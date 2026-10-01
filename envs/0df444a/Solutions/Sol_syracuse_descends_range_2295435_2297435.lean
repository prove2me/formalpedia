-- Prove2me | solution 1 for syracuse_descends_range_2295435_2297435
-- status  : ACCEPTED   (prove)
-- author  : @chstdu
-- created : 2026-09-23T17:49:53.99082+00:00
-- url     : https://prove2.me/submissions/048cc459-f1c1-4188-9c58-17a22ed52bea

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

theorem B2582365 : Blo 2295435 2582365 := bbase (se 3 (by rfl) ⟨484193, by rfl⟩ : syracuseStep 2582365 = 968387) (by norm_num)
theorem B3443153 : Blo 2295435 3443153 := bstep (se 2 (by rfl) ⟨1291182, by rfl⟩ : syracuseStep 3443153 = 2582365) B2582365
theorem B2295435 : Blo 2295435 2295435 := bstep (se 1 (by rfl) ⟨1721576, by rfl⟩ : syracuseStep 2295435 = 3443153) B3443153
theorem B7747109 : Blo 2295435 7747109 := bbase (se 4 (by rfl) ⟨726291, by rfl⟩ : syracuseStep 7747109 = 1452583) (by norm_num)
theorem B5164739 : Blo 2295435 5164739 := bstep (se 1 (by rfl) ⟨3873554, by rfl⟩ : syracuseStep 5164739 = 7747109) B7747109
theorem B3443159 : Blo 2295435 3443159 := bstep (se 1 (by rfl) ⟨2582369, by rfl⟩ : syracuseStep 3443159 = 5164739) B5164739
theorem B2295439 : Blo 2295435 2295439 := bstep (se 1 (by rfl) ⟨1721579, by rfl⟩ : syracuseStep 2295439 = 3443159) B3443159
theorem B3443165 : Blo 2295435 3443165 := bbase (se 3 (by rfl) ⟨645593, by rfl⟩ : syracuseStep 3443165 = 1291187) (by norm_num)
theorem B2295443 : Blo 2295435 2295443 := bstep (se 1 (by rfl) ⟨1721582, by rfl⟩ : syracuseStep 2295443 = 3443165) B3443165
theorem B5164757 : Blo 2295435 5164757 := bbase (se 7 (by rfl) ⟨60524, by rfl⟩ : syracuseStep 5164757 = 121049) (by norm_num)
theorem B3443171 : Blo 2295435 3443171 := bstep (se 1 (by rfl) ⟨2582378, by rfl⟩ : syracuseStep 3443171 = 5164757) B5164757
theorem B2295447 : Blo 2295435 2295447 := bstep (se 1 (by rfl) ⟨1721585, by rfl⟩ : syracuseStep 2295447 = 3443171) B3443171
theorem B4653541 : Blo 2295435 4653541 := bbase (se 4 (by rfl) ⟨436269, by rfl⟩ : syracuseStep 4653541 = 872539) (by norm_num)
theorem B6204721 : Blo 2295435 6204721 := bstep (se 2 (by rfl) ⟨2326770, by rfl⟩ : syracuseStep 6204721 = 4653541) B4653541
theorem B8272961 : Blo 2295435 8272961 := bstep (se 2 (by rfl) ⟨3102360, by rfl⟩ : syracuseStep 8272961 = 6204721) B6204721
theorem B5515307 : Blo 2295435 5515307 := bstep (se 1 (by rfl) ⟨4136480, by rfl⟩ : syracuseStep 5515307 = 8272961) B8272961
theorem B3676871 : Blo 2295435 3676871 := bstep (se 1 (by rfl) ⟨2757653, by rfl⟩ : syracuseStep 3676871 = 5515307) B5515307
theorem B9804989 : Blo 2295435 9804989 := bstep (se 3 (by rfl) ⟨1838435, by rfl⟩ : syracuseStep 9804989 = 3676871) B3676871
theorem B6536659 : Blo 2295435 6536659 := bstep (se 1 (by rfl) ⟨4902494, by rfl⟩ : syracuseStep 6536659 = 9804989) B9804989
theorem B8715545 : Blo 2295435 8715545 := bstep (se 2 (by rfl) ⟨3268329, by rfl⟩ : syracuseStep 8715545 = 6536659) B6536659
theorem B5810363 : Blo 2295435 5810363 := bstep (se 1 (by rfl) ⟨4357772, by rfl⟩ : syracuseStep 5810363 = 8715545) B8715545
theorem B3873575 : Blo 2295435 3873575 := bstep (se 1 (by rfl) ⟨2905181, by rfl⟩ : syracuseStep 3873575 = 5810363) B5810363
theorem B2582383 : Blo 2295435 2582383 := bstep (se 1 (by rfl) ⟨1936787, by rfl⟩ : syracuseStep 2582383 = 3873575) B3873575
theorem B3443177 : Blo 2295435 3443177 := bstep (se 2 (by rfl) ⟨1291191, by rfl⟩ : syracuseStep 3443177 = 2582383) B2582383
theorem B2295451 : Blo 2295435 2295451 := bstep (se 1 (by rfl) ⟨1721588, by rfl⟩ : syracuseStep 2295451 = 3443177) B3443177
theorem B3102365 : Blo 2295435 3102365 := bbase (se 3 (by rfl) ⟨581693, by rfl⟩ : syracuseStep 3102365 = 1163387) (by norm_num)
theorem B8272973 : Blo 2295435 8272973 := bstep (se 3 (by rfl) ⟨1551182, by rfl⟩ : syracuseStep 8272973 = 3102365) B3102365
theorem B22061261 : Blo 2295435 22061261 := bstep (se 3 (by rfl) ⟨4136486, by rfl⟩ : syracuseStep 22061261 = 8272973) B8272973
theorem B14707507 : Blo 2295435 14707507 := bstep (se 1 (by rfl) ⟨11030630, by rfl⟩ : syracuseStep 14707507 = 22061261) B22061261
theorem B19610009 : Blo 2295435 19610009 := bstep (se 2 (by rfl) ⟨7353753, by rfl⟩ : syracuseStep 19610009 = 14707507) B14707507
theorem B13073339 : Blo 2295435 13073339 := bstep (se 1 (by rfl) ⟨9805004, by rfl⟩ : syracuseStep 13073339 = 19610009) B19610009
theorem B8715559 : Blo 2295435 8715559 := bstep (se 1 (by rfl) ⟨6536669, by rfl⟩ : syracuseStep 8715559 = 13073339) B13073339
theorem B11620745 : Blo 2295435 11620745 := bstep (se 2 (by rfl) ⟨4357779, by rfl⟩ : syracuseStep 11620745 = 8715559) B8715559
theorem B7747163 : Blo 2295435 7747163 := bstep (se 1 (by rfl) ⟨5810372, by rfl⟩ : syracuseStep 7747163 = 11620745) B11620745
theorem B5164775 : Blo 2295435 5164775 := bstep (se 1 (by rfl) ⟨3873581, by rfl⟩ : syracuseStep 5164775 = 7747163) B7747163
theorem B3443183 : Blo 2295435 3443183 := bstep (se 1 (by rfl) ⟨2582387, by rfl⟩ : syracuseStep 3443183 = 5164775) B5164775
theorem B2295455 : Blo 2295435 2295455 := bstep (se 1 (by rfl) ⟨1721591, by rfl⟩ : syracuseStep 2295455 = 3443183) B3443183
theorem B3443189 : Blo 2295435 3443189 := bbase (se 5 (by rfl) ⟨161399, by rfl⟩ : syracuseStep 3443189 = 322799) (by norm_num)
theorem B2295459 : Blo 2295435 2295459 := bstep (se 1 (by rfl) ⟨1721594, by rfl⟩ : syracuseStep 2295459 = 3443189) B3443189
theorem B6536693 : Blo 2295435 6536693 := bbase (se 5 (by rfl) ⟨306407, by rfl⟩ : syracuseStep 6536693 = 612815) (by norm_num)
theorem B4357795 : Blo 2295435 4357795 := bstep (se 1 (by rfl) ⟨3268346, by rfl⟩ : syracuseStep 4357795 = 6536693) B6536693
theorem B5810393 : Blo 2295435 5810393 := bstep (se 2 (by rfl) ⟨2178897, by rfl⟩ : syracuseStep 5810393 = 4357795) B4357795
theorem B3873595 : Blo 2295435 3873595 := bstep (se 1 (by rfl) ⟨2905196, by rfl⟩ : syracuseStep 3873595 = 5810393) B5810393
theorem B5164793 : Blo 2295435 5164793 := bstep (se 2 (by rfl) ⟨1936797, by rfl⟩ : syracuseStep 5164793 = 3873595) B3873595
theorem B3443195 : Blo 2295435 3443195 := bstep (se 1 (by rfl) ⟨2582396, by rfl⟩ : syracuseStep 3443195 = 5164793) B5164793
theorem B2295463 : Blo 2295435 2295463 := bstep (se 1 (by rfl) ⟨1721597, by rfl⟩ : syracuseStep 2295463 = 3443195) B3443195
theorem B2582401 : Blo 2295435 2582401 := bbase (se 2 (by rfl) ⟨968400, by rfl⟩ : syracuseStep 2582401 = 1936801) (by norm_num)
theorem B3443201 : Blo 2295435 3443201 := bstep (se 2 (by rfl) ⟨1291200, by rfl⟩ : syracuseStep 3443201 = 2582401) B2582401
theorem B2295467 : Blo 2295435 2295467 := bstep (se 1 (by rfl) ⟨1721600, by rfl⟩ : syracuseStep 2295467 = 3443201) B3443201
theorem B5810413 : Blo 2295435 5810413 := bbase (se 3 (by rfl) ⟨1089452, by rfl⟩ : syracuseStep 5810413 = 2178905) (by norm_num)
theorem B7747217 : Blo 2295435 7747217 := bstep (se 2 (by rfl) ⟨2905206, by rfl⟩ : syracuseStep 7747217 = 5810413) B5810413
theorem B5164811 : Blo 2295435 5164811 := bstep (se 1 (by rfl) ⟨3873608, by rfl⟩ : syracuseStep 5164811 = 7747217) B7747217
theorem B3443207 : Blo 2295435 3443207 := bstep (se 1 (by rfl) ⟨2582405, by rfl⟩ : syracuseStep 3443207 = 5164811) B5164811
theorem B2295471 : Blo 2295435 2295471 := bstep (se 1 (by rfl) ⟨1721603, by rfl⟩ : syracuseStep 2295471 = 3443207) B3443207
theorem B3443213 : Blo 2295435 3443213 := bbase (se 3 (by rfl) ⟨645602, by rfl⟩ : syracuseStep 3443213 = 1291205) (by norm_num)
theorem B2295475 : Blo 2295435 2295475 := bstep (se 1 (by rfl) ⟨1721606, by rfl⟩ : syracuseStep 2295475 = 3443213) B3443213
theorem B5164829 : Blo 2295435 5164829 := bbase (se 3 (by rfl) ⟨968405, by rfl⟩ : syracuseStep 5164829 = 1936811) (by norm_num)
theorem B3443219 : Blo 2295435 3443219 := bstep (se 1 (by rfl) ⟨2582414, by rfl⟩ : syracuseStep 3443219 = 5164829) B5164829
theorem B2295479 : Blo 2295435 2295479 := bstep (se 1 (by rfl) ⟨1721609, by rfl⟩ : syracuseStep 2295479 = 3443219) B3443219
theorem B3873629 : Blo 2295435 3873629 := bbase (se 3 (by rfl) ⟨726305, by rfl⟩ : syracuseStep 3873629 = 1452611) (by norm_num)
theorem B2582419 : Blo 2295435 2582419 := bstep (se 1 (by rfl) ⟨1936814, by rfl⟩ : syracuseStep 2582419 = 3873629) B3873629
theorem B3443225 : Blo 2295435 3443225 := bstep (se 2 (by rfl) ⟨1291209, by rfl⟩ : syracuseStep 3443225 = 2582419) B2582419
theorem B2295483 : Blo 2295435 2295483 := bstep (se 1 (by rfl) ⟨1721612, by rfl⟩ : syracuseStep 2295483 = 3443225) B3443225
theorem B9805141 : Blo 2295435 9805141 := bbase (se 11 (by rfl) ⟨7181, by rfl⟩ : syracuseStep 9805141 = 14363) (by norm_num)
theorem B13073521 : Blo 2295435 13073521 := bstep (se 2 (by rfl) ⟨4902570, by rfl⟩ : syracuseStep 13073521 = 9805141) B9805141
theorem B17431361 : Blo 2295435 17431361 := bstep (se 2 (by rfl) ⟨6536760, by rfl⟩ : syracuseStep 17431361 = 13073521) B13073521
theorem B11620907 : Blo 2295435 11620907 := bstep (se 1 (by rfl) ⟨8715680, by rfl⟩ : syracuseStep 11620907 = 17431361) B17431361
theorem B7747271 : Blo 2295435 7747271 := bstep (se 1 (by rfl) ⟨5810453, by rfl⟩ : syracuseStep 7747271 = 11620907) B11620907
theorem B5164847 : Blo 2295435 5164847 := bstep (se 1 (by rfl) ⟨3873635, by rfl⟩ : syracuseStep 5164847 = 7747271) B7747271
theorem B3443231 : Blo 2295435 3443231 := bstep (se 1 (by rfl) ⟨2582423, by rfl⟩ : syracuseStep 3443231 = 5164847) B5164847
theorem B2295487 : Blo 2295435 2295487 := bstep (se 1 (by rfl) ⟨1721615, by rfl⟩ : syracuseStep 2295487 = 3443231) B3443231
theorem B3443237 : Blo 2295435 3443237 := bbase (se 4 (by rfl) ⟨322803, by rfl⟩ : syracuseStep 3443237 = 645607) (by norm_num)
theorem B2295491 : Blo 2295435 2295491 := bstep (se 1 (by rfl) ⟨1721618, by rfl⟩ : syracuseStep 2295491 = 3443237) B3443237
theorem B2905237 : Blo 2295435 2905237 := bbase (se 6 (by rfl) ⟨68091, by rfl⟩ : syracuseStep 2905237 = 136183) (by norm_num)
theorem B3873649 : Blo 2295435 3873649 := bstep (se 2 (by rfl) ⟨1452618, by rfl⟩ : syracuseStep 3873649 = 2905237) B2905237
theorem B5164865 : Blo 2295435 5164865 := bstep (se 2 (by rfl) ⟨1936824, by rfl⟩ : syracuseStep 5164865 = 3873649) B3873649
theorem B3443243 : Blo 2295435 3443243 := bstep (se 1 (by rfl) ⟨2582432, by rfl⟩ : syracuseStep 3443243 = 5164865) B5164865
theorem B2295495 : Blo 2295435 2295495 := bstep (se 1 (by rfl) ⟨1721621, by rfl⟩ : syracuseStep 2295495 = 3443243) B3443243
theorem B2582437 : Blo 2295435 2582437 := bbase (se 4 (by rfl) ⟨242103, by rfl⟩ : syracuseStep 2582437 = 484207) (by norm_num)
theorem B3443249 : Blo 2295435 3443249 := bstep (se 2 (by rfl) ⟨1291218, by rfl⟩ : syracuseStep 3443249 = 2582437) B2582437
theorem B2295499 : Blo 2295435 2295499 := bstep (se 1 (by rfl) ⟨1721624, by rfl⟩ : syracuseStep 2295499 = 3443249) B3443249
theorem B2358569 : Blo 2295435 2358569 := bbase (se 2 (by rfl) ⟨884463, by rfl⟩ : syracuseStep 2358569 = 1768927) (by norm_num)
theorem B6289517 : Blo 2295435 6289517 := bstep (se 3 (by rfl) ⟨1179284, by rfl⟩ : syracuseStep 6289517 = 2358569) B2358569
theorem B4193011 : Blo 2295435 4193011 := bstep (se 1 (by rfl) ⟨3144758, by rfl⟩ : syracuseStep 4193011 = 6289517) B6289517
theorem B22362725 : Blo 2295435 22362725 := bstep (se 4 (by rfl) ⟨2096505, by rfl⟩ : syracuseStep 22362725 = 4193011) B4193011
theorem B14908483 : Blo 2295435 14908483 := bstep (se 1 (by rfl) ⟨11181362, by rfl⟩ : syracuseStep 14908483 = 22362725) B22362725
theorem B19877977 : Blo 2295435 19877977 := bstep (se 2 (by rfl) ⟨7454241, by rfl⟩ : syracuseStep 19877977 = 14908483) B14908483
theorem B26503969 : Blo 2295435 26503969 := bstep (se 2 (by rfl) ⟨9938988, by rfl⟩ : syracuseStep 26503969 = 19877977) B19877977
theorem B35338625 : Blo 2295435 35338625 := bstep (se 2 (by rfl) ⟨13251984, by rfl⟩ : syracuseStep 35338625 = 26503969) B26503969
theorem B23559083 : Blo 2295435 23559083 := bstep (se 1 (by rfl) ⟨17669312, by rfl⟩ : syracuseStep 23559083 = 35338625) B35338625
theorem B15706055 : Blo 2295435 15706055 := bstep (se 1 (by rfl) ⟨11779541, by rfl⟩ : syracuseStep 15706055 = 23559083) B23559083
theorem B10470703 : Blo 2295435 10470703 := bstep (se 1 (by rfl) ⟨7853027, by rfl⟩ : syracuseStep 10470703 = 15706055) B15706055
theorem B13960937 : Blo 2295435 13960937 := bstep (se 2 (by rfl) ⟨5235351, by rfl⟩ : syracuseStep 13960937 = 10470703) B10470703
theorem B37229165 : Blo 2295435 37229165 := bstep (se 3 (by rfl) ⟨6980468, by rfl⟩ : syracuseStep 37229165 = 13960937) B13960937
theorem B24819443 : Blo 2295435 24819443 := bstep (se 1 (by rfl) ⟨18614582, by rfl⟩ : syracuseStep 24819443 = 37229165) B37229165
theorem B16546295 : Blo 2295435 16546295 := bstep (se 1 (by rfl) ⟨12409721, by rfl⟩ : syracuseStep 16546295 = 24819443) B24819443
theorem B11030863 : Blo 2295435 11030863 := bstep (se 1 (by rfl) ⟨8273147, by rfl⟩ : syracuseStep 11030863 = 16546295) B16546295
theorem B14707817 : Blo 2295435 14707817 := bstep (se 2 (by rfl) ⟨5515431, by rfl⟩ : syracuseStep 14707817 = 11030863) B11030863
theorem B9805211 : Blo 2295435 9805211 := bstep (se 1 (by rfl) ⟨7353908, by rfl⟩ : syracuseStep 9805211 = 14707817) B14707817
theorem B6536807 : Blo 2295435 6536807 := bstep (se 1 (by rfl) ⟨4902605, by rfl⟩ : syracuseStep 6536807 = 9805211) B9805211
theorem B4357871 : Blo 2295435 4357871 := bstep (se 1 (by rfl) ⟨3268403, by rfl⟩ : syracuseStep 4357871 = 6536807) B6536807
theorem B2905247 : Blo 2295435 2905247 := bstep (se 1 (by rfl) ⟨2178935, by rfl⟩ : syracuseStep 2905247 = 4357871) B4357871
theorem B7747325 : Blo 2295435 7747325 := bstep (se 3 (by rfl) ⟨1452623, by rfl⟩ : syracuseStep 7747325 = 2905247) B2905247
theorem B5164883 : Blo 2295435 5164883 := bstep (se 1 (by rfl) ⟨3873662, by rfl⟩ : syracuseStep 5164883 = 7747325) B7747325
theorem B3443255 : Blo 2295435 3443255 := bstep (se 1 (by rfl) ⟨2582441, by rfl⟩ : syracuseStep 3443255 = 5164883) B5164883
theorem B2295503 : Blo 2295435 2295503 := bstep (se 1 (by rfl) ⟨1721627, by rfl⟩ : syracuseStep 2295503 = 3443255) B3443255
theorem B3443261 : Blo 2295435 3443261 := bbase (se 3 (by rfl) ⟨645611, by rfl⟩ : syracuseStep 3443261 = 1291223) (by norm_num)
theorem B2295507 : Blo 2295435 2295507 := bstep (se 1 (by rfl) ⟨1721630, by rfl⟩ : syracuseStep 2295507 = 3443261) B3443261
theorem B5164901 : Blo 2295435 5164901 := bbase (se 4 (by rfl) ⟨484209, by rfl⟩ : syracuseStep 5164901 = 968419) (by norm_num)
theorem B3443267 : Blo 2295435 3443267 := bstep (se 1 (by rfl) ⟨2582450, by rfl⟩ : syracuseStep 3443267 = 5164901) B5164901
theorem B2295511 : Blo 2295435 2295511 := bstep (se 1 (by rfl) ⟨1721633, by rfl⟩ : syracuseStep 2295511 = 3443267) B3443267
theorem B5810525 : Blo 2295435 5810525 := bbase (se 3 (by rfl) ⟨1089473, by rfl⟩ : syracuseStep 5810525 = 2178947) (by norm_num)
theorem B3873683 : Blo 2295435 3873683 := bstep (se 1 (by rfl) ⟨2905262, by rfl⟩ : syracuseStep 3873683 = 5810525) B5810525
theorem B2582455 : Blo 2295435 2582455 := bstep (se 1 (by rfl) ⟨1936841, by rfl⟩ : syracuseStep 2582455 = 3873683) B3873683
theorem B3443273 : Blo 2295435 3443273 := bstep (se 2 (by rfl) ⟨1291227, by rfl⟩ : syracuseStep 3443273 = 2582455) B2582455
theorem B2295515 : Blo 2295435 2295515 := bstep (se 1 (by rfl) ⟨1721636, by rfl⟩ : syracuseStep 2295515 = 3443273) B3443273
theorem B4357901 : Blo 2295435 4357901 := bbase (se 3 (by rfl) ⟨817106, by rfl⟩ : syracuseStep 4357901 = 1634213) (by norm_num)
theorem B11621069 : Blo 2295435 11621069 := bstep (se 3 (by rfl) ⟨2178950, by rfl⟩ : syracuseStep 11621069 = 4357901) B4357901
theorem B7747379 : Blo 2295435 7747379 := bstep (se 1 (by rfl) ⟨5810534, by rfl⟩ : syracuseStep 7747379 = 11621069) B11621069
theorem B5164919 : Blo 2295435 5164919 := bstep (se 1 (by rfl) ⟨3873689, by rfl⟩ : syracuseStep 5164919 = 7747379) B7747379
theorem B3443279 : Blo 2295435 3443279 := bstep (se 1 (by rfl) ⟨2582459, by rfl⟩ : syracuseStep 3443279 = 5164919) B5164919
theorem B2295519 : Blo 2295435 2295519 := bstep (se 1 (by rfl) ⟨1721639, by rfl⟩ : syracuseStep 2295519 = 3443279) B3443279
theorem B3443285 : Blo 2295435 3443285 := bbase (se 8 (by rfl) ⟨20175, by rfl⟩ : syracuseStep 3443285 = 40351) (by norm_num)
theorem B2295523 : Blo 2295435 2295523 := bstep (se 1 (by rfl) ⟨1721642, by rfl⟩ : syracuseStep 2295523 = 3443285) B3443285
theorem B9563093 : Blo 2295435 9563093 := bbase (se 7 (by rfl) ⟨112067, by rfl⟩ : syracuseStep 9563093 = 224135) (by norm_num)
theorem B6375395 : Blo 2295435 6375395 := bstep (se 1 (by rfl) ⟨4781546, by rfl⟩ : syracuseStep 6375395 = 9563093) B9563093
theorem B17001053 : Blo 2295435 17001053 := bstep (se 3 (by rfl) ⟨3187697, by rfl⟩ : syracuseStep 17001053 = 6375395) B6375395
theorem B11334035 : Blo 2295435 11334035 := bstep (se 1 (by rfl) ⟨8500526, by rfl⟩ : syracuseStep 11334035 = 17001053) B17001053
theorem B7556023 : Blo 2295435 7556023 := bstep (se 1 (by rfl) ⟨5667017, by rfl⟩ : syracuseStep 7556023 = 11334035) B11334035
theorem B40298789 : Blo 2295435 40298789 := bstep (se 4 (by rfl) ⟨3778011, by rfl⟩ : syracuseStep 40298789 = 7556023) B7556023
theorem B26865859 : Blo 2295435 26865859 := bstep (se 1 (by rfl) ⟨20149394, by rfl⟩ : syracuseStep 26865859 = 40298789) B40298789
theorem B35821145 : Blo 2295435 35821145 := bstep (se 2 (by rfl) ⟨13432929, by rfl⟩ : syracuseStep 35821145 = 26865859) B26865859
theorem B23880763 : Blo 2295435 23880763 := bstep (se 1 (by rfl) ⟨17910572, by rfl⟩ : syracuseStep 23880763 = 35821145) B35821145
theorem B127364069 : Blo 2295435 127364069 := bstep (se 4 (by rfl) ⟨11940381, by rfl⟩ : syracuseStep 127364069 = 23880763) B23880763
theorem B84909379 : Blo 2295435 84909379 := bstep (se 1 (by rfl) ⟨63682034, by rfl⟩ : syracuseStep 84909379 = 127364069) B127364069
theorem B113212505 : Blo 2295435 113212505 := bstep (se 2 (by rfl) ⟨42454689, by rfl⟩ : syracuseStep 113212505 = 84909379) B84909379
theorem B75475003 : Blo 2295435 75475003 := bstep (se 1 (by rfl) ⟨56606252, by rfl⟩ : syracuseStep 75475003 = 113212505) B113212505
theorem B100633337 : Blo 2295435 100633337 := bstep (se 2 (by rfl) ⟨37737501, by rfl⟩ : syracuseStep 100633337 = 75475003) B75475003
theorem B67088891 : Blo 2295435 67088891 := bstep (se 1 (by rfl) ⟨50316668, by rfl⟩ : syracuseStep 67088891 = 100633337) B100633337
theorem B44725927 : Blo 2295435 44725927 := bstep (se 1 (by rfl) ⟨33544445, by rfl⟩ : syracuseStep 44725927 = 67088891) B67088891
theorem B59634569 : Blo 2295435 59634569 := bstep (se 2 (by rfl) ⟨22362963, by rfl⟩ : syracuseStep 59634569 = 44725927) B44725927
theorem B39756379 : Blo 2295435 39756379 := bstep (se 1 (by rfl) ⟨29817284, by rfl⟩ : syracuseStep 39756379 = 59634569) B59634569
theorem B53008505 : Blo 2295435 53008505 := bstep (se 2 (by rfl) ⟨19878189, by rfl⟩ : syracuseStep 53008505 = 39756379) B39756379
theorem B35339003 : Blo 2295435 35339003 := bstep (se 1 (by rfl) ⟨26504252, by rfl⟩ : syracuseStep 35339003 = 53008505) B53008505
theorem B23559335 : Blo 2295435 23559335 := bstep (se 1 (by rfl) ⟨17669501, by rfl⟩ : syracuseStep 23559335 = 35339003) B35339003
theorem B15706223 : Blo 2295435 15706223 := bstep (se 1 (by rfl) ⟨11779667, by rfl⟩ : syracuseStep 15706223 = 23559335) B23559335
theorem B10470815 : Blo 2295435 10470815 := bstep (se 1 (by rfl) ⟨7853111, by rfl⟩ : syracuseStep 10470815 = 15706223) B15706223
theorem B6980543 : Blo 2295435 6980543 := bstep (se 1 (by rfl) ⟨5235407, by rfl⟩ : syracuseStep 6980543 = 10470815) B10470815
theorem B4653695 : Blo 2295435 4653695 := bstep (se 1 (by rfl) ⟨3490271, by rfl⟩ : syracuseStep 4653695 = 6980543) B6980543
theorem B3102463 : Blo 2295435 3102463 := bstep (se 1 (by rfl) ⟨2326847, by rfl⟩ : syracuseStep 3102463 = 4653695) B4653695
theorem B4136617 : Blo 2295435 4136617 := bstep (se 2 (by rfl) ⟨1551231, by rfl⟩ : syracuseStep 4136617 = 3102463) B3102463
theorem B5515489 : Blo 2295435 5515489 := bstep (se 2 (by rfl) ⟨2068308, by rfl⟩ : syracuseStep 5515489 = 4136617) B4136617
theorem B7353985 : Blo 2295435 7353985 := bstep (se 2 (by rfl) ⟨2757744, by rfl⟩ : syracuseStep 7353985 = 5515489) B5515489
theorem B9805313 : Blo 2295435 9805313 := bstep (se 2 (by rfl) ⟨3676992, by rfl⟩ : syracuseStep 9805313 = 7353985) B7353985
theorem B6536875 : Blo 2295435 6536875 := bstep (se 1 (by rfl) ⟨4902656, by rfl⟩ : syracuseStep 6536875 = 9805313) B9805313
theorem B8715833 : Blo 2295435 8715833 := bstep (se 2 (by rfl) ⟨3268437, by rfl⟩ : syracuseStep 8715833 = 6536875) B6536875
theorem B5810555 : Blo 2295435 5810555 := bstep (se 1 (by rfl) ⟨4357916, by rfl⟩ : syracuseStep 5810555 = 8715833) B8715833
theorem B3873703 : Blo 2295435 3873703 := bstep (se 1 (by rfl) ⟨2905277, by rfl⟩ : syracuseStep 3873703 = 5810555) B5810555
theorem B5164937 : Blo 2295435 5164937 := bstep (se 2 (by rfl) ⟨1936851, by rfl⟩ : syracuseStep 5164937 = 3873703) B3873703
theorem B3443291 : Blo 2295435 3443291 := bstep (se 1 (by rfl) ⟨2582468, by rfl⟩ : syracuseStep 3443291 = 5164937) B5164937
theorem B2295527 : Blo 2295435 2295527 := bstep (se 1 (by rfl) ⟨1721645, by rfl⟩ : syracuseStep 2295527 = 3443291) B3443291
theorem B2582473 : Blo 2295435 2582473 := bbase (se 2 (by rfl) ⟨968427, by rfl⟩ : syracuseStep 2582473 = 1936855) (by norm_num)
theorem B3443297 : Blo 2295435 3443297 := bstep (se 2 (by rfl) ⟨1291236, by rfl⟩ : syracuseStep 3443297 = 2582473) B2582473
theorem B2295531 : Blo 2295435 2295531 := bstep (se 1 (by rfl) ⟨1721648, by rfl⟩ : syracuseStep 2295531 = 3443297) B3443297
theorem B3677005 : Blo 2295435 3677005 := bbase (se 3 (by rfl) ⟨689438, by rfl⟩ : syracuseStep 3677005 = 1378877) (by norm_num)
theorem B19610693 : Blo 2295435 19610693 := bstep (se 4 (by rfl) ⟨1838502, by rfl⟩ : syracuseStep 19610693 = 3677005) B3677005
theorem B13073795 : Blo 2295435 13073795 := bstep (se 1 (by rfl) ⟨9805346, by rfl⟩ : syracuseStep 13073795 = 19610693) B19610693
theorem B8715863 : Blo 2295435 8715863 := bstep (se 1 (by rfl) ⟨6536897, by rfl⟩ : syracuseStep 8715863 = 13073795) B13073795
theorem B5810575 : Blo 2295435 5810575 := bstep (se 1 (by rfl) ⟨4357931, by rfl⟩ : syracuseStep 5810575 = 8715863) B8715863
theorem B7747433 : Blo 2295435 7747433 := bstep (se 2 (by rfl) ⟨2905287, by rfl⟩ : syracuseStep 7747433 = 5810575) B5810575
theorem B5164955 : Blo 2295435 5164955 := bstep (se 1 (by rfl) ⟨3873716, by rfl⟩ : syracuseStep 5164955 = 7747433) B7747433
theorem B3443303 : Blo 2295435 3443303 := bstep (se 1 (by rfl) ⟨2582477, by rfl⟩ : syracuseStep 3443303 = 5164955) B5164955
theorem B2295535 : Blo 2295435 2295535 := bstep (se 1 (by rfl) ⟨1721651, by rfl⟩ : syracuseStep 2295535 = 3443303) B3443303
theorem B3443309 : Blo 2295435 3443309 := bbase (se 3 (by rfl) ⟨645620, by rfl⟩ : syracuseStep 3443309 = 1291241) (by norm_num)
theorem B2295539 : Blo 2295435 2295539 := bstep (se 1 (by rfl) ⟨1721654, by rfl⟩ : syracuseStep 2295539 = 3443309) B3443309
theorem B5164973 : Blo 2295435 5164973 := bbase (se 3 (by rfl) ⟨968432, by rfl⟩ : syracuseStep 5164973 = 1936865) (by norm_num)
theorem B3443315 : Blo 2295435 3443315 := bstep (se 1 (by rfl) ⟨2582486, by rfl⟩ : syracuseStep 3443315 = 5164973) B5164973
theorem B2295543 : Blo 2295435 2295543 := bstep (se 1 (by rfl) ⟨1721657, by rfl⟩ : syracuseStep 2295543 = 3443315) B3443315
theorem B6536933 : Blo 2295435 6536933 := bbase (se 4 (by rfl) ⟨612837, by rfl⟩ : syracuseStep 6536933 = 1225675) (by norm_num)
theorem B4357955 : Blo 2295435 4357955 := bstep (se 1 (by rfl) ⟨3268466, by rfl⟩ : syracuseStep 4357955 = 6536933) B6536933
theorem B2905303 : Blo 2295435 2905303 := bstep (se 1 (by rfl) ⟨2178977, by rfl⟩ : syracuseStep 2905303 = 4357955) B4357955
theorem B3873737 : Blo 2295435 3873737 := bstep (se 2 (by rfl) ⟨1452651, by rfl⟩ : syracuseStep 3873737 = 2905303) B2905303
theorem B2582491 : Blo 2295435 2582491 := bstep (se 1 (by rfl) ⟨1936868, by rfl⟩ : syracuseStep 2582491 = 3873737) B3873737
theorem B3443321 : Blo 2295435 3443321 := bstep (se 2 (by rfl) ⟨1291245, by rfl⟩ : syracuseStep 3443321 = 2582491) B2582491
theorem B2295547 : Blo 2295435 2295547 := bstep (se 1 (by rfl) ⟨1721660, by rfl⟩ : syracuseStep 2295547 = 3443321) B3443321
theorem B5235461 : Blo 2295435 5235461 := bbase (se 4 (by rfl) ⟨490824, by rfl⟩ : syracuseStep 5235461 = 981649) (by norm_num)
theorem B3490307 : Blo 2295435 3490307 := bstep (se 1 (by rfl) ⟨2617730, by rfl⟩ : syracuseStep 3490307 = 5235461) B5235461
theorem B2326871 : Blo 2295435 2326871 := bstep (se 1 (by rfl) ⟨1745153, by rfl⟩ : syracuseStep 2326871 = 3490307) B3490307
theorem B6204989 : Blo 2295435 6204989 := bstep (se 3 (by rfl) ⟨1163435, by rfl⟩ : syracuseStep 6204989 = 2326871) B2326871
theorem B16546637 : Blo 2295435 16546637 := bstep (se 3 (by rfl) ⟨3102494, by rfl⟩ : syracuseStep 16546637 = 6204989) B6204989
theorem B44124365 : Blo 2295435 44124365 := bstep (se 3 (by rfl) ⟨8273318, by rfl⟩ : syracuseStep 44124365 = 16546637) B16546637
theorem B29416243 : Blo 2295435 29416243 := bstep (se 1 (by rfl) ⟨22062182, by rfl⟩ : syracuseStep 29416243 = 44124365) B44124365
theorem B39221657 : Blo 2295435 39221657 := bstep (se 2 (by rfl) ⟨14708121, by rfl⟩ : syracuseStep 39221657 = 29416243) B29416243
theorem B26147771 : Blo 2295435 26147771 := bstep (se 1 (by rfl) ⟨19610828, by rfl⟩ : syracuseStep 26147771 = 39221657) B39221657
theorem B17431847 : Blo 2295435 17431847 := bstep (se 1 (by rfl) ⟨13073885, by rfl⟩ : syracuseStep 17431847 = 26147771) B26147771
theorem B11621231 : Blo 2295435 11621231 := bstep (se 1 (by rfl) ⟨8715923, by rfl⟩ : syracuseStep 11621231 = 17431847) B17431847
theorem B7747487 : Blo 2295435 7747487 := bstep (se 1 (by rfl) ⟨5810615, by rfl⟩ : syracuseStep 7747487 = 11621231) B11621231
theorem B5164991 : Blo 2295435 5164991 := bstep (se 1 (by rfl) ⟨3873743, by rfl⟩ : syracuseStep 5164991 = 7747487) B7747487
theorem B3443327 : Blo 2295435 3443327 := bstep (se 1 (by rfl) ⟨2582495, by rfl⟩ : syracuseStep 3443327 = 5164991) B5164991
theorem B2295551 : Blo 2295435 2295551 := bstep (se 1 (by rfl) ⟨1721663, by rfl⟩ : syracuseStep 2295551 = 3443327) B3443327
theorem B3443333 : Blo 2295435 3443333 := bbase (se 4 (by rfl) ⟨322812, by rfl⟩ : syracuseStep 3443333 = 645625) (by norm_num)
theorem B2295555 : Blo 2295435 2295555 := bstep (se 1 (by rfl) ⟨1721666, by rfl⟩ : syracuseStep 2295555 = 3443333) B3443333
theorem B3873757 : Blo 2295435 3873757 := bbase (se 3 (by rfl) ⟨726329, by rfl⟩ : syracuseStep 3873757 = 1452659) (by norm_num)
theorem B5165009 : Blo 2295435 5165009 := bstep (se 2 (by rfl) ⟨1936878, by rfl⟩ : syracuseStep 5165009 = 3873757) B3873757
theorem B3443339 : Blo 2295435 3443339 := bstep (se 1 (by rfl) ⟨2582504, by rfl⟩ : syracuseStep 3443339 = 5165009) B5165009
theorem B2295559 : Blo 2295435 2295559 := bstep (se 1 (by rfl) ⟨1721669, by rfl⟩ : syracuseStep 2295559 = 3443339) B3443339
theorem B2582509 : Blo 2295435 2582509 := bbase (se 3 (by rfl) ⟨484220, by rfl⟩ : syracuseStep 2582509 = 968441) (by norm_num)
theorem B3443345 : Blo 2295435 3443345 := bstep (se 2 (by rfl) ⟨1291254, by rfl⟩ : syracuseStep 3443345 = 2582509) B2582509
theorem B2295563 : Blo 2295435 2295563 := bstep (se 1 (by rfl) ⟨1721672, by rfl⟩ : syracuseStep 2295563 = 3443345) B3443345
theorem B7747541 : Blo 2295435 7747541 := bbase (se 7 (by rfl) ⟨90791, by rfl⟩ : syracuseStep 7747541 = 181583) (by norm_num)
theorem B5165027 : Blo 2295435 5165027 := bstep (se 1 (by rfl) ⟨3873770, by rfl⟩ : syracuseStep 5165027 = 7747541) B7747541
theorem B3443351 : Blo 2295435 3443351 := bstep (se 1 (by rfl) ⟨2582513, by rfl⟩ : syracuseStep 3443351 = 5165027) B5165027
theorem B2295567 : Blo 2295435 2295567 := bstep (se 1 (by rfl) ⟨1721675, by rfl⟩ : syracuseStep 2295567 = 3443351) B3443351
theorem B3443357 : Blo 2295435 3443357 := bbase (se 3 (by rfl) ⟨645629, by rfl⟩ : syracuseStep 3443357 = 1291259) (by norm_num)
theorem B2295571 : Blo 2295435 2295571 := bstep (se 1 (by rfl) ⟨1721678, by rfl⟩ : syracuseStep 2295571 = 3443357) B3443357
theorem B5165045 : Blo 2295435 5165045 := bbase (se 5 (by rfl) ⟨242111, by rfl⟩ : syracuseStep 5165045 = 484223) (by norm_num)
theorem B3443363 : Blo 2295435 3443363 := bstep (se 1 (by rfl) ⟨2582522, by rfl⟩ : syracuseStep 3443363 = 5165045) B5165045
theorem B2295575 : Blo 2295435 2295575 := bstep (se 1 (by rfl) ⟨1721681, by rfl⟩ : syracuseStep 2295575 = 3443363) B3443363
theorem B81699029 : Blo 2295435 81699029 := bbase (se 7 (by rfl) ⟨957410, by rfl⟩ : syracuseStep 81699029 = 1914821) (by norm_num)
theorem B54466019 : Blo 2295435 54466019 := bstep (se 1 (by rfl) ⟨40849514, by rfl⟩ : syracuseStep 54466019 = 81699029) B81699029
theorem B36310679 : Blo 2295435 36310679 := bstep (se 1 (by rfl) ⟨27233009, by rfl⟩ : syracuseStep 36310679 = 54466019) B54466019
theorem B24207119 : Blo 2295435 24207119 := bstep (se 1 (by rfl) ⟨18155339, by rfl⟩ : syracuseStep 24207119 = 36310679) B36310679
theorem B16138079 : Blo 2295435 16138079 := bstep (se 1 (by rfl) ⟨12103559, by rfl⟩ : syracuseStep 16138079 = 24207119) B24207119
theorem B10758719 : Blo 2295435 10758719 := bstep (se 1 (by rfl) ⟨8069039, by rfl⟩ : syracuseStep 10758719 = 16138079) B16138079
theorem B7172479 : Blo 2295435 7172479 := bstep (se 1 (by rfl) ⟨5379359, by rfl⟩ : syracuseStep 7172479 = 10758719) B10758719
theorem B38253221 : Blo 2295435 38253221 := bstep (se 4 (by rfl) ⟨3586239, by rfl⟩ : syracuseStep 38253221 = 7172479) B7172479
theorem B25502147 : Blo 2295435 25502147 := bstep (se 1 (by rfl) ⟨19126610, by rfl⟩ : syracuseStep 25502147 = 38253221) B38253221
theorem B17001431 : Blo 2295435 17001431 := bstep (se 1 (by rfl) ⟨12751073, by rfl⟩ : syracuseStep 17001431 = 25502147) B25502147
theorem B11334287 : Blo 2295435 11334287 := bstep (se 1 (by rfl) ⟨8500715, by rfl⟩ : syracuseStep 11334287 = 17001431) B17001431
theorem B30224765 : Blo 2295435 30224765 := bstep (se 3 (by rfl) ⟨5667143, by rfl⟩ : syracuseStep 30224765 = 11334287) B11334287
theorem B20149843 : Blo 2295435 20149843 := bstep (se 1 (by rfl) ⟨15112382, by rfl⟩ : syracuseStep 20149843 = 30224765) B30224765
theorem B26866457 : Blo 2295435 26866457 := bstep (se 2 (by rfl) ⟨10074921, by rfl⟩ : syracuseStep 26866457 = 20149843) B20149843
theorem B17910971 : Blo 2295435 17910971 := bstep (se 1 (by rfl) ⟨13433228, by rfl⟩ : syracuseStep 17910971 = 26866457) B26866457
theorem B11940647 : Blo 2295435 11940647 := bstep (se 1 (by rfl) ⟨8955485, by rfl⟩ : syracuseStep 11940647 = 17910971) B17910971
theorem B127366901 : Blo 2295435 127366901 := bstep (se 5 (by rfl) ⟨5970323, by rfl⟩ : syracuseStep 127366901 = 11940647) B11940647
theorem B84911267 : Blo 2295435 84911267 := bstep (se 1 (by rfl) ⟨63683450, by rfl⟩ : syracuseStep 84911267 = 127366901) B127366901
theorem B56607511 : Blo 2295435 56607511 := bstep (se 1 (by rfl) ⟨42455633, by rfl⟩ : syracuseStep 56607511 = 84911267) B84911267
theorem B75476681 : Blo 2295435 75476681 := bstep (se 2 (by rfl) ⟨28303755, by rfl⟩ : syracuseStep 75476681 = 56607511) B56607511
theorem B50317787 : Blo 2295435 50317787 := bstep (se 1 (by rfl) ⟨37738340, by rfl⟩ : syracuseStep 50317787 = 75476681) B75476681
theorem B33545191 : Blo 2295435 33545191 := bstep (se 1 (by rfl) ⟨25158893, by rfl⟩ : syracuseStep 33545191 = 50317787) B50317787
theorem B44726921 : Blo 2295435 44726921 := bstep (se 2 (by rfl) ⟨16772595, by rfl⟩ : syracuseStep 44726921 = 33545191) B33545191
theorem B29817947 : Blo 2295435 29817947 := bstep (se 1 (by rfl) ⟨22363460, by rfl⟩ : syracuseStep 29817947 = 44726921) B44726921
theorem B79514525 : Blo 2295435 79514525 := bstep (se 3 (by rfl) ⟨14908973, by rfl⟩ : syracuseStep 79514525 = 29817947) B29817947
theorem B53009683 : Blo 2295435 53009683 := bstep (se 1 (by rfl) ⟨39757262, by rfl⟩ : syracuseStep 53009683 = 79514525) B79514525
theorem B282718309 : Blo 2295435 282718309 := bstep (se 4 (by rfl) ⟨26504841, by rfl⟩ : syracuseStep 282718309 = 53009683) B53009683
theorem B376957745 : Blo 2295435 376957745 := bstep (se 2 (by rfl) ⟨141359154, by rfl⟩ : syracuseStep 376957745 = 282718309) B282718309
theorem B251305163 : Blo 2295435 251305163 := bstep (se 1 (by rfl) ⟨188478872, by rfl⟩ : syracuseStep 251305163 = 376957745) B376957745
theorem B167536775 : Blo 2295435 167536775 := bstep (se 1 (by rfl) ⟨125652581, by rfl⟩ : syracuseStep 167536775 = 251305163) B251305163
theorem B111691183 : Blo 2295435 111691183 := bstep (se 1 (by rfl) ⟨83768387, by rfl⟩ : syracuseStep 111691183 = 167536775) B167536775
theorem B148921577 : Blo 2295435 148921577 := bstep (se 2 (by rfl) ⟨55845591, by rfl⟩ : syracuseStep 148921577 = 111691183) B111691183
theorem B99281051 : Blo 2295435 99281051 := bstep (se 1 (by rfl) ⟨74460788, by rfl⟩ : syracuseStep 99281051 = 148921577) B148921577
theorem B66187367 : Blo 2295435 66187367 := bstep (se 1 (by rfl) ⟨49640525, by rfl⟩ : syracuseStep 66187367 = 99281051) B99281051
theorem B44124911 : Blo 2295435 44124911 := bstep (se 1 (by rfl) ⟨33093683, by rfl⟩ : syracuseStep 44124911 = 66187367) B66187367
theorem B29416607 : Blo 2295435 29416607 := bstep (se 1 (by rfl) ⟨22062455, by rfl⟩ : syracuseStep 29416607 = 44124911) B44124911
theorem B19611071 : Blo 2295435 19611071 := bstep (se 1 (by rfl) ⟨14708303, by rfl⟩ : syracuseStep 19611071 = 29416607) B29416607
theorem B13074047 : Blo 2295435 13074047 := bstep (se 1 (by rfl) ⟨9805535, by rfl⟩ : syracuseStep 13074047 = 19611071) B19611071
theorem B8716031 : Blo 2295435 8716031 := bstep (se 1 (by rfl) ⟨6537023, by rfl⟩ : syracuseStep 8716031 = 13074047) B13074047
theorem B5810687 : Blo 2295435 5810687 := bstep (se 1 (by rfl) ⟨4358015, by rfl⟩ : syracuseStep 5810687 = 8716031) B8716031
theorem B3873791 : Blo 2295435 3873791 := bstep (se 1 (by rfl) ⟨2905343, by rfl⟩ : syracuseStep 3873791 = 5810687) B5810687
theorem B2582527 : Blo 2295435 2582527 := bstep (se 1 (by rfl) ⟨1936895, by rfl⟩ : syracuseStep 2582527 = 3873791) B3873791
theorem B3443369 : Blo 2295435 3443369 := bstep (se 2 (by rfl) ⟨1291263, by rfl⟩ : syracuseStep 3443369 = 2582527) B2582527
theorem B2295579 : Blo 2295435 2295579 := bstep (se 1 (by rfl) ⟨1721684, by rfl⟩ : syracuseStep 2295579 = 3443369) B3443369
theorem B3268517 : Blo 2295435 3268517 := bbase (se 4 (by rfl) ⟨306423, by rfl⟩ : syracuseStep 3268517 = 612847) (by norm_num)
theorem B8716045 : Blo 2295435 8716045 := bstep (se 3 (by rfl) ⟨1634258, by rfl⟩ : syracuseStep 8716045 = 3268517) B3268517
theorem B11621393 : Blo 2295435 11621393 := bstep (se 2 (by rfl) ⟨4358022, by rfl⟩ : syracuseStep 11621393 = 8716045) B8716045
theorem B7747595 : Blo 2295435 7747595 := bstep (se 1 (by rfl) ⟨5810696, by rfl⟩ : syracuseStep 7747595 = 11621393) B11621393
theorem B5165063 : Blo 2295435 5165063 := bstep (se 1 (by rfl) ⟨3873797, by rfl⟩ : syracuseStep 5165063 = 7747595) B7747595
theorem B3443375 : Blo 2295435 3443375 := bstep (se 1 (by rfl) ⟨2582531, by rfl⟩ : syracuseStep 3443375 = 5165063) B5165063
theorem B2295583 : Blo 2295435 2295583 := bstep (se 1 (by rfl) ⟨1721687, by rfl⟩ : syracuseStep 2295583 = 3443375) B3443375
theorem B3443381 : Blo 2295435 3443381 := bbase (se 5 (by rfl) ⟨161408, by rfl⟩ : syracuseStep 3443381 = 322817) (by norm_num)
theorem B2295587 : Blo 2295435 2295587 := bstep (se 1 (by rfl) ⟨1721690, by rfl⟩ : syracuseStep 2295587 = 3443381) B3443381
theorem B5810717 : Blo 2295435 5810717 := bbase (se 3 (by rfl) ⟨1089509, by rfl⟩ : syracuseStep 5810717 = 2179019) (by norm_num)
theorem B3873811 : Blo 2295435 3873811 := bstep (se 1 (by rfl) ⟨2905358, by rfl⟩ : syracuseStep 3873811 = 5810717) B5810717
theorem B5165081 : Blo 2295435 5165081 := bstep (se 2 (by rfl) ⟨1936905, by rfl⟩ : syracuseStep 5165081 = 3873811) B3873811
theorem B3443387 : Blo 2295435 3443387 := bstep (se 1 (by rfl) ⟨2582540, by rfl⟩ : syracuseStep 3443387 = 5165081) B5165081
theorem B2295591 : Blo 2295435 2295591 := bstep (se 1 (by rfl) ⟨1721693, by rfl⟩ : syracuseStep 2295591 = 3443387) B3443387
theorem B2582545 : Blo 2295435 2582545 := bbase (se 2 (by rfl) ⟨968454, by rfl⟩ : syracuseStep 2582545 = 1936909) (by norm_num)
theorem B3443393 : Blo 2295435 3443393 := bstep (se 2 (by rfl) ⟨1291272, by rfl⟩ : syracuseStep 3443393 = 2582545) B2582545
theorem B2295595 : Blo 2295435 2295595 := bstep (se 1 (by rfl) ⟨1721696, by rfl⟩ : syracuseStep 2295595 = 3443393) B3443393
theorem B4358053 : Blo 2295435 4358053 := bbase (se 4 (by rfl) ⟨408567, by rfl⟩ : syracuseStep 4358053 = 817135) (by norm_num)
theorem B5810737 : Blo 2295435 5810737 := bstep (se 2 (by rfl) ⟨2179026, by rfl⟩ : syracuseStep 5810737 = 4358053) B4358053
theorem B7747649 : Blo 2295435 7747649 := bstep (se 2 (by rfl) ⟨2905368, by rfl⟩ : syracuseStep 7747649 = 5810737) B5810737
theorem B5165099 : Blo 2295435 5165099 := bstep (se 1 (by rfl) ⟨3873824, by rfl⟩ : syracuseStep 5165099 = 7747649) B7747649
theorem B3443399 : Blo 2295435 3443399 := bstep (se 1 (by rfl) ⟨2582549, by rfl⟩ : syracuseStep 3443399 = 5165099) B5165099
theorem B2295599 : Blo 2295435 2295599 := bstep (se 1 (by rfl) ⟨1721699, by rfl⟩ : syracuseStep 2295599 = 3443399) B3443399
theorem B3443405 : Blo 2295435 3443405 := bbase (se 3 (by rfl) ⟨645638, by rfl⟩ : syracuseStep 3443405 = 1291277) (by norm_num)
theorem B2295603 : Blo 2295435 2295603 := bstep (se 1 (by rfl) ⟨1721702, by rfl⟩ : syracuseStep 2295603 = 3443405) B3443405
theorem B5165117 : Blo 2295435 5165117 := bbase (se 3 (by rfl) ⟨968459, by rfl⟩ : syracuseStep 5165117 = 1936919) (by norm_num)
theorem B3443411 : Blo 2295435 3443411 := bstep (se 1 (by rfl) ⟨2582558, by rfl⟩ : syracuseStep 3443411 = 5165117) B5165117
theorem B2295607 : Blo 2295435 2295607 := bstep (se 1 (by rfl) ⟨1721705, by rfl⟩ : syracuseStep 2295607 = 3443411) B3443411
theorem B3873845 : Blo 2295435 3873845 := bbase (se 5 (by rfl) ⟨181586, by rfl⟩ : syracuseStep 3873845 = 363173) (by norm_num)
theorem B2582563 : Blo 2295435 2582563 := bstep (se 1 (by rfl) ⟨1936922, by rfl⟩ : syracuseStep 2582563 = 3873845) B3873845
theorem B3443417 : Blo 2295435 3443417 := bstep (se 2 (by rfl) ⟨1291281, by rfl⟩ : syracuseStep 3443417 = 2582563) B2582563
theorem B2295611 : Blo 2295435 2295611 := bstep (se 1 (by rfl) ⟨1721708, by rfl⟩ : syracuseStep 2295611 = 3443417) B3443417
theorem B6537125 : Blo 2295435 6537125 := bbase (se 4 (by rfl) ⟨612855, by rfl⟩ : syracuseStep 6537125 = 1225711) (by norm_num)
theorem B17432333 : Blo 2295435 17432333 := bstep (se 3 (by rfl) ⟨3268562, by rfl⟩ : syracuseStep 17432333 = 6537125) B6537125
theorem B11621555 : Blo 2295435 11621555 := bstep (se 1 (by rfl) ⟨8716166, by rfl⟩ : syracuseStep 11621555 = 17432333) B17432333
theorem B7747703 : Blo 2295435 7747703 := bstep (se 1 (by rfl) ⟨5810777, by rfl⟩ : syracuseStep 7747703 = 11621555) B11621555
theorem B5165135 : Blo 2295435 5165135 := bstep (se 1 (by rfl) ⟨3873851, by rfl⟩ : syracuseStep 5165135 = 7747703) B7747703
theorem B3443423 : Blo 2295435 3443423 := bstep (se 1 (by rfl) ⟨2582567, by rfl⟩ : syracuseStep 3443423 = 5165135) B5165135
theorem B2295615 : Blo 2295435 2295615 := bstep (se 1 (by rfl) ⟨1721711, by rfl⟩ : syracuseStep 2295615 = 3443423) B3443423
theorem B3443429 : Blo 2295435 3443429 := bbase (se 4 (by rfl) ⟨322821, by rfl⟩ : syracuseStep 3443429 = 645643) (by norm_num)
theorem B2295619 : Blo 2295435 2295619 := bstep (se 1 (by rfl) ⟨1721714, by rfl⟩ : syracuseStep 2295619 = 3443429) B3443429
theorem B9307781 : Blo 2295435 9307781 := bbase (se 4 (by rfl) ⟨872604, by rfl⟩ : syracuseStep 9307781 = 1745209) (by norm_num)
theorem B6205187 : Blo 2295435 6205187 := bstep (se 1 (by rfl) ⟨4653890, by rfl⟩ : syracuseStep 6205187 = 9307781) B9307781
theorem B4136791 : Blo 2295435 4136791 := bstep (se 1 (by rfl) ⟨3102593, by rfl⟩ : syracuseStep 4136791 = 6205187) B6205187
theorem B5515721 : Blo 2295435 5515721 := bstep (se 2 (by rfl) ⟨2068395, by rfl⟩ : syracuseStep 5515721 = 4136791) B4136791
theorem B3677147 : Blo 2295435 3677147 := bstep (se 1 (by rfl) ⟨2757860, by rfl⟩ : syracuseStep 3677147 = 5515721) B5515721
theorem B2451431 : Blo 2295435 2451431 := bstep (se 1 (by rfl) ⟨1838573, by rfl⟩ : syracuseStep 2451431 = 3677147) B3677147
theorem B6537149 : Blo 2295435 6537149 := bstep (se 3 (by rfl) ⟨1225715, by rfl⟩ : syracuseStep 6537149 = 2451431) B2451431
theorem B4358099 : Blo 2295435 4358099 := bstep (se 1 (by rfl) ⟨3268574, by rfl⟩ : syracuseStep 4358099 = 6537149) B6537149
theorem B2905399 : Blo 2295435 2905399 := bstep (se 1 (by rfl) ⟨2179049, by rfl⟩ : syracuseStep 2905399 = 4358099) B4358099
theorem B3873865 : Blo 2295435 3873865 := bstep (se 2 (by rfl) ⟨1452699, by rfl⟩ : syracuseStep 3873865 = 2905399) B2905399
theorem B5165153 : Blo 2295435 5165153 := bstep (se 2 (by rfl) ⟨1936932, by rfl⟩ : syracuseStep 5165153 = 3873865) B3873865
theorem B3443435 : Blo 2295435 3443435 := bstep (se 1 (by rfl) ⟨2582576, by rfl⟩ : syracuseStep 3443435 = 5165153) B5165153
theorem B2295623 : Blo 2295435 2295623 := bstep (se 1 (by rfl) ⟨1721717, by rfl⟩ : syracuseStep 2295623 = 3443435) B3443435
theorem B2582581 : Blo 2295435 2582581 := bbase (se 5 (by rfl) ⟨121058, by rfl⟩ : syracuseStep 2582581 = 242117) (by norm_num)
theorem B3443441 : Blo 2295435 3443441 := bstep (se 2 (by rfl) ⟨1291290, by rfl⟩ : syracuseStep 3443441 = 2582581) B2582581
theorem B2295627 : Blo 2295435 2295627 := bstep (se 1 (by rfl) ⟨1721720, by rfl⟩ : syracuseStep 2295627 = 3443441) B3443441
theorem B2905409 : Blo 2295435 2905409 := bbase (se 2 (by rfl) ⟨1089528, by rfl⟩ : syracuseStep 2905409 = 2179057) (by norm_num)
theorem B7747757 : Blo 2295435 7747757 := bstep (se 3 (by rfl) ⟨1452704, by rfl⟩ : syracuseStep 7747757 = 2905409) B2905409
theorem B5165171 : Blo 2295435 5165171 := bstep (se 1 (by rfl) ⟨3873878, by rfl⟩ : syracuseStep 5165171 = 7747757) B7747757
theorem B3443447 : Blo 2295435 3443447 := bstep (se 1 (by rfl) ⟨2582585, by rfl⟩ : syracuseStep 3443447 = 5165171) B5165171
theorem B2295631 : Blo 2295435 2295631 := bstep (se 1 (by rfl) ⟨1721723, by rfl⟩ : syracuseStep 2295631 = 3443447) B3443447
theorem B3443453 : Blo 2295435 3443453 := bbase (se 3 (by rfl) ⟨645647, by rfl⟩ : syracuseStep 3443453 = 1291295) (by norm_num)
theorem B2295635 : Blo 2295435 2295635 := bstep (se 1 (by rfl) ⟨1721726, by rfl⟩ : syracuseStep 2295635 = 3443453) B3443453
theorem B5165189 : Blo 2295435 5165189 := bbase (se 4 (by rfl) ⟨484236, by rfl⟩ : syracuseStep 5165189 = 968473) (by norm_num)
theorem B3443459 : Blo 2295435 3443459 := bstep (se 1 (by rfl) ⟨2582594, by rfl⟩ : syracuseStep 3443459 = 5165189) B5165189
theorem B2295639 : Blo 2295435 2295639 := bstep (se 1 (by rfl) ⟨1721729, by rfl⟩ : syracuseStep 2295639 = 3443459) B3443459
theorem B5890133 : Blo 2295435 5890133 := bbase (se 8 (by rfl) ⟨34512, by rfl⟩ : syracuseStep 5890133 = 69025) (by norm_num)
theorem B3926755 : Blo 2295435 3926755 := bstep (se 1 (by rfl) ⟨2945066, by rfl⟩ : syracuseStep 3926755 = 5890133) B5890133
theorem B5235673 : Blo 2295435 5235673 := bstep (se 2 (by rfl) ⟨1963377, by rfl⟩ : syracuseStep 5235673 = 3926755) B3926755
theorem B6980897 : Blo 2295435 6980897 := bstep (se 2 (by rfl) ⟨2617836, by rfl⟩ : syracuseStep 6980897 = 5235673) B5235673
theorem B4653931 : Blo 2295435 4653931 := bstep (se 1 (by rfl) ⟨3490448, by rfl⟩ : syracuseStep 4653931 = 6980897) B6980897
theorem B6205241 : Blo 2295435 6205241 := bstep (se 2 (by rfl) ⟨2326965, by rfl⟩ : syracuseStep 6205241 = 4653931) B4653931
theorem B4136827 : Blo 2295435 4136827 := bstep (se 1 (by rfl) ⟨3102620, by rfl⟩ : syracuseStep 4136827 = 6205241) B6205241
theorem B5515769 : Blo 2295435 5515769 := bstep (se 2 (by rfl) ⟨2068413, by rfl⟩ : syracuseStep 5515769 = 4136827) B4136827
theorem B3677179 : Blo 2295435 3677179 := bstep (se 1 (by rfl) ⟨2757884, by rfl⟩ : syracuseStep 3677179 = 5515769) B5515769
theorem B4902905 : Blo 2295435 4902905 := bstep (se 2 (by rfl) ⟨1838589, by rfl⟩ : syracuseStep 4902905 = 3677179) B3677179
theorem B3268603 : Blo 2295435 3268603 := bstep (se 1 (by rfl) ⟨2451452, by rfl⟩ : syracuseStep 3268603 = 4902905) B4902905
theorem B4358137 : Blo 2295435 4358137 := bstep (se 2 (by rfl) ⟨1634301, by rfl⟩ : syracuseStep 4358137 = 3268603) B3268603
theorem B5810849 : Blo 2295435 5810849 := bstep (se 2 (by rfl) ⟨2179068, by rfl⟩ : syracuseStep 5810849 = 4358137) B4358137
theorem B3873899 : Blo 2295435 3873899 := bstep (se 1 (by rfl) ⟨2905424, by rfl⟩ : syracuseStep 3873899 = 5810849) B5810849
theorem B2582599 : Blo 2295435 2582599 := bstep (se 1 (by rfl) ⟨1936949, by rfl⟩ : syracuseStep 2582599 = 3873899) B3873899
theorem B3443465 : Blo 2295435 3443465 := bstep (se 2 (by rfl) ⟨1291299, by rfl⟩ : syracuseStep 3443465 = 2582599) B2582599
theorem B2295643 : Blo 2295435 2295643 := bstep (se 1 (by rfl) ⟨1721732, by rfl⟩ : syracuseStep 2295643 = 3443465) B3443465
theorem B11621717 : Blo 2295435 11621717 := bbase (se 18 (by rfl) ⟨66, by rfl⟩ : syracuseStep 11621717 = 133) (by norm_num)
theorem B7747811 : Blo 2295435 7747811 := bstep (se 1 (by rfl) ⟨5810858, by rfl⟩ : syracuseStep 7747811 = 11621717) B11621717
theorem B5165207 : Blo 2295435 5165207 := bstep (se 1 (by rfl) ⟨3873905, by rfl⟩ : syracuseStep 5165207 = 7747811) B7747811
theorem B3443471 : Blo 2295435 3443471 := bstep (se 1 (by rfl) ⟨2582603, by rfl⟩ : syracuseStep 3443471 = 5165207) B5165207
theorem B2295647 : Blo 2295435 2295647 := bstep (se 1 (by rfl) ⟨1721735, by rfl⟩ : syracuseStep 2295647 = 3443471) B3443471
theorem B3443477 : Blo 2295435 3443477 := bbase (se 6 (by rfl) ⟨80706, by rfl⟩ : syracuseStep 3443477 = 161413) (by norm_num)
theorem B2295651 : Blo 2295435 2295651 := bstep (se 1 (by rfl) ⟨1721738, by rfl⟩ : syracuseStep 2295651 = 3443477) B3443477
theorem B8500997 : Blo 2295435 8500997 := bbase (se 4 (by rfl) ⟨796968, by rfl⟩ : syracuseStep 8500997 = 1593937) (by norm_num)
theorem B22669325 : Blo 2295435 22669325 := bstep (se 3 (by rfl) ⟨4250498, by rfl⟩ : syracuseStep 22669325 = 8500997) B8500997
theorem B15112883 : Blo 2295435 15112883 := bstep (se 1 (by rfl) ⟨11334662, by rfl⟩ : syracuseStep 15112883 = 22669325) B22669325
theorem B10075255 : Blo 2295435 10075255 := bstep (se 1 (by rfl) ⟨7556441, by rfl⟩ : syracuseStep 10075255 = 15112883) B15112883
theorem B53734693 : Blo 2295435 53734693 := bstep (se 4 (by rfl) ⟨5037627, by rfl⟩ : syracuseStep 53734693 = 10075255) B10075255
theorem B71646257 : Blo 2295435 71646257 := bstep (se 2 (by rfl) ⟨26867346, by rfl⟩ : syracuseStep 71646257 = 53734693) B53734693
theorem B47764171 : Blo 2295435 47764171 := bstep (se 1 (by rfl) ⟨35823128, by rfl⟩ : syracuseStep 47764171 = 71646257) B71646257
theorem B63685561 : Blo 2295435 63685561 := bstep (se 2 (by rfl) ⟨23882085, by rfl⟩ : syracuseStep 63685561 = 47764171) B47764171
theorem B84914081 : Blo 2295435 84914081 := bstep (se 2 (by rfl) ⟨31842780, by rfl⟩ : syracuseStep 84914081 = 63685561) B63685561
theorem B56609387 : Blo 2295435 56609387 := bstep (se 1 (by rfl) ⟨42457040, by rfl⟩ : syracuseStep 56609387 = 84914081) B84914081
theorem B37739591 : Blo 2295435 37739591 := bstep (se 1 (by rfl) ⟨28304693, by rfl⟩ : syracuseStep 37739591 = 56609387) B56609387
theorem B25159727 : Blo 2295435 25159727 := bstep (se 1 (by rfl) ⟨18869795, by rfl⟩ : syracuseStep 25159727 = 37739591) B37739591
theorem B16773151 : Blo 2295435 16773151 := bstep (se 1 (by rfl) ⟨12579863, by rfl⟩ : syracuseStep 16773151 = 25159727) B25159727
theorem B22364201 : Blo 2295435 22364201 := bstep (se 2 (by rfl) ⟨8386575, by rfl⟩ : syracuseStep 22364201 = 16773151) B16773151
theorem B59637869 : Blo 2295435 59637869 := bstep (se 3 (by rfl) ⟨11182100, by rfl⟩ : syracuseStep 59637869 = 22364201) B22364201
theorem B39758579 : Blo 2295435 39758579 := bstep (se 1 (by rfl) ⟨29818934, by rfl⟩ : syracuseStep 39758579 = 59637869) B59637869
theorem B26505719 : Blo 2295435 26505719 := bstep (se 1 (by rfl) ⟨19879289, by rfl⟩ : syracuseStep 26505719 = 39758579) B39758579
theorem B17670479 : Blo 2295435 17670479 := bstep (se 1 (by rfl) ⟨13252859, by rfl⟩ : syracuseStep 17670479 = 26505719) B26505719
theorem B47121277 : Blo 2295435 47121277 := bstep (se 3 (by rfl) ⟨8835239, by rfl⟩ : syracuseStep 47121277 = 17670479) B17670479
theorem B62828369 : Blo 2295435 62828369 := bstep (se 2 (by rfl) ⟨23560638, by rfl⟩ : syracuseStep 62828369 = 47121277) B47121277
theorem B41885579 : Blo 2295435 41885579 := bstep (se 1 (by rfl) ⟨31414184, by rfl⟩ : syracuseStep 41885579 = 62828369) B62828369
theorem B27923719 : Blo 2295435 27923719 := bstep (se 1 (by rfl) ⟨20942789, by rfl⟩ : syracuseStep 27923719 = 41885579) B41885579
theorem B37231625 : Blo 2295435 37231625 := bstep (se 2 (by rfl) ⟨13961859, by rfl⟩ : syracuseStep 37231625 = 27923719) B27923719
theorem B24821083 : Blo 2295435 24821083 := bstep (se 1 (by rfl) ⟨18615812, by rfl⟩ : syracuseStep 24821083 = 37231625) B37231625
theorem B33094777 : Blo 2295435 33094777 := bstep (se 2 (by rfl) ⟨12410541, by rfl⟩ : syracuseStep 33094777 = 24821083) B24821083
theorem B44126369 : Blo 2295435 44126369 := bstep (se 2 (by rfl) ⟨16547388, by rfl⟩ : syracuseStep 44126369 = 33094777) B33094777
theorem B29417579 : Blo 2295435 29417579 := bstep (se 1 (by rfl) ⟨22063184, by rfl⟩ : syracuseStep 29417579 = 44126369) B44126369
theorem B19611719 : Blo 2295435 19611719 := bstep (se 1 (by rfl) ⟨14708789, by rfl⟩ : syracuseStep 19611719 = 29417579) B29417579
theorem B13074479 : Blo 2295435 13074479 := bstep (se 1 (by rfl) ⟨9805859, by rfl⟩ : syracuseStep 13074479 = 19611719) B19611719
theorem B8716319 : Blo 2295435 8716319 := bstep (se 1 (by rfl) ⟨6537239, by rfl⟩ : syracuseStep 8716319 = 13074479) B13074479
theorem B5810879 : Blo 2295435 5810879 := bstep (se 1 (by rfl) ⟨4358159, by rfl⟩ : syracuseStep 5810879 = 8716319) B8716319
theorem B3873919 : Blo 2295435 3873919 := bstep (se 1 (by rfl) ⟨2905439, by rfl⟩ : syracuseStep 3873919 = 5810879) B5810879
theorem B5165225 : Blo 2295435 5165225 := bstep (se 2 (by rfl) ⟨1936959, by rfl⟩ : syracuseStep 5165225 = 3873919) B3873919
theorem B3443483 : Blo 2295435 3443483 := bstep (se 1 (by rfl) ⟨2582612, by rfl⟩ : syracuseStep 3443483 = 5165225) B5165225
theorem B2295655 : Blo 2295435 2295655 := bstep (se 1 (by rfl) ⟨1721741, by rfl⟩ : syracuseStep 2295655 = 3443483) B3443483
theorem B2582617 : Blo 2295435 2582617 := bbase (se 2 (by rfl) ⟨968481, by rfl⟩ : syracuseStep 2582617 = 1936963) (by norm_num)
theorem B3443489 : Blo 2295435 3443489 := bstep (se 2 (by rfl) ⟨1291308, by rfl⟩ : syracuseStep 3443489 = 2582617) B2582617
theorem B2295659 : Blo 2295435 2295659 := bstep (se 1 (by rfl) ⟨1721744, by rfl⟩ : syracuseStep 2295659 = 3443489) B3443489
theorem B7354421 : Blo 2295435 7354421 := bbase (se 5 (by rfl) ⟨344738, by rfl⟩ : syracuseStep 7354421 = 689477) (by norm_num)
theorem B4902947 : Blo 2295435 4902947 := bstep (se 1 (by rfl) ⟨3677210, by rfl⟩ : syracuseStep 4902947 = 7354421) B7354421
theorem B3268631 : Blo 2295435 3268631 := bstep (se 1 (by rfl) ⟨2451473, by rfl⟩ : syracuseStep 3268631 = 4902947) B4902947
theorem B8716349 : Blo 2295435 8716349 := bstep (se 3 (by rfl) ⟨1634315, by rfl⟩ : syracuseStep 8716349 = 3268631) B3268631
theorem B5810899 : Blo 2295435 5810899 := bstep (se 1 (by rfl) ⟨4358174, by rfl⟩ : syracuseStep 5810899 = 8716349) B8716349
theorem B7747865 : Blo 2295435 7747865 := bstep (se 2 (by rfl) ⟨2905449, by rfl⟩ : syracuseStep 7747865 = 5810899) B5810899
theorem B5165243 : Blo 2295435 5165243 := bstep (se 1 (by rfl) ⟨3873932, by rfl⟩ : syracuseStep 5165243 = 7747865) B7747865
theorem B3443495 : Blo 2295435 3443495 := bstep (se 1 (by rfl) ⟨2582621, by rfl⟩ : syracuseStep 3443495 = 5165243) B5165243
theorem B2295663 : Blo 2295435 2295663 := bstep (se 1 (by rfl) ⟨1721747, by rfl⟩ : syracuseStep 2295663 = 3443495) B3443495
theorem B3443501 : Blo 2295435 3443501 := bbase (se 3 (by rfl) ⟨645656, by rfl⟩ : syracuseStep 3443501 = 1291313) (by norm_num)
theorem B2295667 : Blo 2295435 2295667 := bstep (se 1 (by rfl) ⟨1721750, by rfl⟩ : syracuseStep 2295667 = 3443501) B3443501
theorem B5165261 : Blo 2295435 5165261 := bbase (se 3 (by rfl) ⟨968486, by rfl⟩ : syracuseStep 5165261 = 1936973) (by norm_num)
theorem B3443507 : Blo 2295435 3443507 := bstep (se 1 (by rfl) ⟨2582630, by rfl⟩ : syracuseStep 3443507 = 5165261) B5165261
theorem B2295671 : Blo 2295435 2295671 := bstep (se 1 (by rfl) ⟨1721753, by rfl⟩ : syracuseStep 2295671 = 3443507) B3443507
theorem B2905465 : Blo 2295435 2905465 := bbase (se 2 (by rfl) ⟨1089549, by rfl⟩ : syracuseStep 2905465 = 2179099) (by norm_num)
theorem B3873953 : Blo 2295435 3873953 := bstep (se 2 (by rfl) ⟨1452732, by rfl⟩ : syracuseStep 3873953 = 2905465) B2905465
theorem B2582635 : Blo 2295435 2582635 := bstep (se 1 (by rfl) ⟨1936976, by rfl⟩ : syracuseStep 2582635 = 3873953) B3873953
theorem B3443513 : Blo 2295435 3443513 := bstep (se 2 (by rfl) ⟨1291317, by rfl⟩ : syracuseStep 3443513 = 2582635) B2582635
theorem B2295675 : Blo 2295435 2295675 := bstep (se 1 (by rfl) ⟨1721756, by rfl⟩ : syracuseStep 2295675 = 3443513) B3443513
theorem B23560885 : Blo 2295435 23560885 := bbase (se 5 (by rfl) ⟨1104416, by rfl⟩ : syracuseStep 23560885 = 2208833) (by norm_num)
theorem B31414513 : Blo 2295435 31414513 := bstep (se 2 (by rfl) ⟨11780442, by rfl⟩ : syracuseStep 31414513 = 23560885) B23560885
theorem B41886017 : Blo 2295435 41886017 := bstep (se 2 (by rfl) ⟨15707256, by rfl⟩ : syracuseStep 41886017 = 31414513) B31414513
theorem B27924011 : Blo 2295435 27924011 := bstep (se 1 (by rfl) ⟨20943008, by rfl⟩ : syracuseStep 27924011 = 41886017) B41886017
theorem B18616007 : Blo 2295435 18616007 := bstep (se 1 (by rfl) ⟨13962005, by rfl⟩ : syracuseStep 18616007 = 27924011) B27924011
theorem B12410671 : Blo 2295435 12410671 := bstep (se 1 (by rfl) ⟨9308003, by rfl⟩ : syracuseStep 12410671 = 18616007) B18616007
theorem B16547561 : Blo 2295435 16547561 := bstep (se 2 (by rfl) ⟨6205335, by rfl⟩ : syracuseStep 16547561 = 12410671) B12410671
theorem B11031707 : Blo 2295435 11031707 := bstep (se 1 (by rfl) ⟨8273780, by rfl⟩ : syracuseStep 11031707 = 16547561) B16547561
theorem B7354471 : Blo 2295435 7354471 := bstep (se 1 (by rfl) ⟨5515853, by rfl⟩ : syracuseStep 7354471 = 11031707) B11031707
theorem B9805961 : Blo 2295435 9805961 := bstep (se 2 (by rfl) ⟨3677235, by rfl⟩ : syracuseStep 9805961 = 7354471) B7354471
theorem B26149229 : Blo 2295435 26149229 := bstep (se 3 (by rfl) ⟨4902980, by rfl⟩ : syracuseStep 26149229 = 9805961) B9805961
theorem B17432819 : Blo 2295435 17432819 := bstep (se 1 (by rfl) ⟨13074614, by rfl⟩ : syracuseStep 17432819 = 26149229) B26149229
theorem B11621879 : Blo 2295435 11621879 := bstep (se 1 (by rfl) ⟨8716409, by rfl⟩ : syracuseStep 11621879 = 17432819) B17432819
theorem B7747919 : Blo 2295435 7747919 := bstep (se 1 (by rfl) ⟨5810939, by rfl⟩ : syracuseStep 7747919 = 11621879) B11621879
theorem B5165279 : Blo 2295435 5165279 := bstep (se 1 (by rfl) ⟨3873959, by rfl⟩ : syracuseStep 5165279 = 7747919) B7747919
theorem B3443519 : Blo 2295435 3443519 := bstep (se 1 (by rfl) ⟨2582639, by rfl⟩ : syracuseStep 3443519 = 5165279) B5165279
theorem B2295679 : Blo 2295435 2295679 := bstep (se 1 (by rfl) ⟨1721759, by rfl⟩ : syracuseStep 2295679 = 3443519) B3443519
theorem B3443525 : Blo 2295435 3443525 := bbase (se 4 (by rfl) ⟨322830, by rfl⟩ : syracuseStep 3443525 = 645661) (by norm_num)
theorem B2295683 : Blo 2295435 2295683 := bstep (se 1 (by rfl) ⟨1721762, by rfl⟩ : syracuseStep 2295683 = 3443525) B3443525
theorem B3873973 : Blo 2295435 3873973 := bbase (se 5 (by rfl) ⟨181592, by rfl⟩ : syracuseStep 3873973 = 363185) (by norm_num)
theorem B5165297 : Blo 2295435 5165297 := bstep (se 2 (by rfl) ⟨1936986, by rfl⟩ : syracuseStep 5165297 = 3873973) B3873973
theorem B3443531 : Blo 2295435 3443531 := bstep (se 1 (by rfl) ⟨2582648, by rfl⟩ : syracuseStep 3443531 = 5165297) B5165297
theorem B2295687 : Blo 2295435 2295687 := bstep (se 1 (by rfl) ⟨1721765, by rfl⟩ : syracuseStep 2295687 = 3443531) B3443531
theorem B2582653 : Blo 2295435 2582653 := bbase (se 3 (by rfl) ⟨484247, by rfl⟩ : syracuseStep 2582653 = 968495) (by norm_num)
theorem B3443537 : Blo 2295435 3443537 := bstep (se 2 (by rfl) ⟨1291326, by rfl⟩ : syracuseStep 3443537 = 2582653) B2582653
theorem B2295691 : Blo 2295435 2295691 := bstep (se 1 (by rfl) ⟨1721768, by rfl⟩ : syracuseStep 2295691 = 3443537) B3443537
theorem B7747973 : Blo 2295435 7747973 := bbase (se 4 (by rfl) ⟨726372, by rfl⟩ : syracuseStep 7747973 = 1452745) (by norm_num)
theorem B5165315 : Blo 2295435 5165315 := bstep (se 1 (by rfl) ⟨3873986, by rfl⟩ : syracuseStep 5165315 = 7747973) B7747973
theorem B3443543 : Blo 2295435 3443543 := bstep (se 1 (by rfl) ⟨2582657, by rfl⟩ : syracuseStep 3443543 = 5165315) B5165315
theorem B2295695 : Blo 2295435 2295695 := bstep (se 1 (by rfl) ⟨1721771, by rfl⟩ : syracuseStep 2295695 = 3443543) B3443543
theorem B3443549 : Blo 2295435 3443549 := bbase (se 3 (by rfl) ⟨645665, by rfl⟩ : syracuseStep 3443549 = 1291331) (by norm_num)
theorem B2295699 : Blo 2295435 2295699 := bstep (se 1 (by rfl) ⟨1721774, by rfl⟩ : syracuseStep 2295699 = 3443549) B3443549
theorem B5165333 : Blo 2295435 5165333 := bbase (se 6 (by rfl) ⟨121062, by rfl⟩ : syracuseStep 5165333 = 242125) (by norm_num)
theorem B3443555 : Blo 2295435 3443555 := bstep (se 1 (by rfl) ⟨2582666, by rfl⟩ : syracuseStep 3443555 = 5165333) B5165333
theorem B2295703 : Blo 2295435 2295703 := bstep (se 1 (by rfl) ⟨1721777, by rfl⟩ : syracuseStep 2295703 = 3443555) B3443555
theorem B8716517 : Blo 2295435 8716517 := bbase (se 4 (by rfl) ⟨817173, by rfl⟩ : syracuseStep 8716517 = 1634347) (by norm_num)
theorem B5811011 : Blo 2295435 5811011 := bstep (se 1 (by rfl) ⟨4358258, by rfl⟩ : syracuseStep 5811011 = 8716517) B8716517
theorem B3874007 : Blo 2295435 3874007 := bstep (se 1 (by rfl) ⟨2905505, by rfl⟩ : syracuseStep 3874007 = 5811011) B5811011
theorem B2582671 : Blo 2295435 2582671 := bstep (se 1 (by rfl) ⟨1937003, by rfl⟩ : syracuseStep 2582671 = 3874007) B3874007
theorem B3443561 : Blo 2295435 3443561 := bstep (se 2 (by rfl) ⟨1291335, by rfl⟩ : syracuseStep 3443561 = 2582671) B2582671
theorem B2295707 : Blo 2295435 2295707 := bstep (se 1 (by rfl) ⟨1721780, by rfl⟩ : syracuseStep 2295707 = 3443561) B3443561
theorem B5591189 : Blo 2295435 5591189 := bbase (se 6 (by rfl) ⟨131043, by rfl⟩ : syracuseStep 5591189 = 262087) (by norm_num)
theorem B3727459 : Blo 2295435 3727459 := bstep (se 1 (by rfl) ⟨2795594, by rfl⟩ : syracuseStep 3727459 = 5591189) B5591189
theorem B4969945 : Blo 2295435 4969945 := bstep (se 2 (by rfl) ⟨1863729, by rfl⟩ : syracuseStep 4969945 = 3727459) B3727459
theorem B6626593 : Blo 2295435 6626593 := bstep (se 2 (by rfl) ⟨2484972, by rfl⟩ : syracuseStep 6626593 = 4969945) B4969945
theorem B35341829 : Blo 2295435 35341829 := bstep (se 4 (by rfl) ⟨3313296, by rfl⟩ : syracuseStep 35341829 = 6626593) B6626593
theorem B23561219 : Blo 2295435 23561219 := bstep (se 1 (by rfl) ⟨17670914, by rfl⟩ : syracuseStep 23561219 = 35341829) B35341829
theorem B15707479 : Blo 2295435 15707479 := bstep (se 1 (by rfl) ⟨11780609, by rfl⟩ : syracuseStep 15707479 = 23561219) B23561219
theorem B20943305 : Blo 2295435 20943305 := bstep (se 2 (by rfl) ⟨7853739, by rfl⟩ : syracuseStep 20943305 = 15707479) B15707479
theorem B13962203 : Blo 2295435 13962203 := bstep (se 1 (by rfl) ⟨10471652, by rfl⟩ : syracuseStep 13962203 = 20943305) B20943305
theorem B9308135 : Blo 2295435 9308135 := bstep (se 1 (by rfl) ⟨6981101, by rfl⟩ : syracuseStep 9308135 = 13962203) B13962203
theorem B6205423 : Blo 2295435 6205423 := bstep (se 1 (by rfl) ⟨4654067, by rfl⟩ : syracuseStep 6205423 = 9308135) B9308135
theorem B8273897 : Blo 2295435 8273897 := bstep (se 2 (by rfl) ⟨3102711, by rfl⟩ : syracuseStep 8273897 = 6205423) B6205423
theorem B5515931 : Blo 2295435 5515931 := bstep (se 1 (by rfl) ⟨4136948, by rfl⟩ : syracuseStep 5515931 = 8273897) B8273897
theorem B3677287 : Blo 2295435 3677287 := bstep (se 1 (by rfl) ⟨2757965, by rfl⟩ : syracuseStep 3677287 = 5515931) B5515931
theorem B4903049 : Blo 2295435 4903049 := bstep (se 2 (by rfl) ⟨1838643, by rfl⟩ : syracuseStep 4903049 = 3677287) B3677287
theorem B13074797 : Blo 2295435 13074797 := bstep (se 3 (by rfl) ⟨2451524, by rfl⟩ : syracuseStep 13074797 = 4903049) B4903049
theorem B8716531 : Blo 2295435 8716531 := bstep (se 1 (by rfl) ⟨6537398, by rfl⟩ : syracuseStep 8716531 = 13074797) B13074797
theorem B11622041 : Blo 2295435 11622041 := bstep (se 2 (by rfl) ⟨4358265, by rfl⟩ : syracuseStep 11622041 = 8716531) B8716531
theorem B7748027 : Blo 2295435 7748027 := bstep (se 1 (by rfl) ⟨5811020, by rfl⟩ : syracuseStep 7748027 = 11622041) B11622041
theorem B5165351 : Blo 2295435 5165351 := bstep (se 1 (by rfl) ⟨3874013, by rfl⟩ : syracuseStep 5165351 = 7748027) B7748027
theorem B3443567 : Blo 2295435 3443567 := bstep (se 1 (by rfl) ⟨2582675, by rfl⟩ : syracuseStep 3443567 = 5165351) B5165351
theorem B2295711 : Blo 2295435 2295711 := bstep (se 1 (by rfl) ⟨1721783, by rfl⟩ : syracuseStep 2295711 = 3443567) B3443567
theorem B3443573 : Blo 2295435 3443573 := bbase (se 5 (by rfl) ⟨161417, by rfl⟩ : syracuseStep 3443573 = 322835) (by norm_num)
theorem B2295715 : Blo 2295435 2295715 := bstep (se 1 (by rfl) ⟨1721786, by rfl⟩ : syracuseStep 2295715 = 3443573) B3443573
theorem B5235845 : Blo 2295435 5235845 := bbase (se 4 (by rfl) ⟨490860, by rfl⟩ : syracuseStep 5235845 = 981721) (by norm_num)
theorem B13962253 : Blo 2295435 13962253 := bstep (se 3 (by rfl) ⟨2617922, by rfl⟩ : syracuseStep 13962253 = 5235845) B5235845
theorem B18616337 : Blo 2295435 18616337 := bstep (se 2 (by rfl) ⟨6981126, by rfl⟩ : syracuseStep 18616337 = 13962253) B13962253
theorem B12410891 : Blo 2295435 12410891 := bstep (se 1 (by rfl) ⟨9308168, by rfl⟩ : syracuseStep 12410891 = 18616337) B18616337
theorem B8273927 : Blo 2295435 8273927 := bstep (se 1 (by rfl) ⟨6205445, by rfl⟩ : syracuseStep 8273927 = 12410891) B12410891
theorem B5515951 : Blo 2295435 5515951 := bstep (se 1 (by rfl) ⟨4136963, by rfl⟩ : syracuseStep 5515951 = 8273927) B8273927
theorem B7354601 : Blo 2295435 7354601 := bstep (se 2 (by rfl) ⟨2757975, by rfl⟩ : syracuseStep 7354601 = 5515951) B5515951
theorem B4903067 : Blo 2295435 4903067 := bstep (se 1 (by rfl) ⟨3677300, by rfl⟩ : syracuseStep 4903067 = 7354601) B7354601
theorem B3268711 : Blo 2295435 3268711 := bstep (se 1 (by rfl) ⟨2451533, by rfl⟩ : syracuseStep 3268711 = 4903067) B4903067
theorem B4358281 : Blo 2295435 4358281 := bstep (se 2 (by rfl) ⟨1634355, by rfl⟩ : syracuseStep 4358281 = 3268711) B3268711
theorem B5811041 : Blo 2295435 5811041 := bstep (se 2 (by rfl) ⟨2179140, by rfl⟩ : syracuseStep 5811041 = 4358281) B4358281
theorem B3874027 : Blo 2295435 3874027 := bstep (se 1 (by rfl) ⟨2905520, by rfl⟩ : syracuseStep 3874027 = 5811041) B5811041
theorem B5165369 : Blo 2295435 5165369 := bstep (se 2 (by rfl) ⟨1937013, by rfl⟩ : syracuseStep 5165369 = 3874027) B3874027
theorem B3443579 : Blo 2295435 3443579 := bstep (se 1 (by rfl) ⟨2582684, by rfl⟩ : syracuseStep 3443579 = 5165369) B5165369
theorem B2295719 : Blo 2295435 2295719 := bstep (se 1 (by rfl) ⟨1721789, by rfl⟩ : syracuseStep 2295719 = 3443579) B3443579
theorem B2582689 : Blo 2295435 2582689 := bbase (se 2 (by rfl) ⟨968508, by rfl⟩ : syracuseStep 2582689 = 1937017) (by norm_num)
theorem B3443585 : Blo 2295435 3443585 := bstep (se 2 (by rfl) ⟨1291344, by rfl⟩ : syracuseStep 3443585 = 2582689) B2582689
theorem B2295723 : Blo 2295435 2295723 := bstep (se 1 (by rfl) ⟨1721792, by rfl⟩ : syracuseStep 2295723 = 3443585) B3443585
theorem B5811061 : Blo 2295435 5811061 := bbase (se 5 (by rfl) ⟨272393, by rfl⟩ : syracuseStep 5811061 = 544787) (by norm_num)
theorem B7748081 : Blo 2295435 7748081 := bstep (se 2 (by rfl) ⟨2905530, by rfl⟩ : syracuseStep 7748081 = 5811061) B5811061
theorem B5165387 : Blo 2295435 5165387 := bstep (se 1 (by rfl) ⟨3874040, by rfl⟩ : syracuseStep 5165387 = 7748081) B7748081
theorem B3443591 : Blo 2295435 3443591 := bstep (se 1 (by rfl) ⟨2582693, by rfl⟩ : syracuseStep 3443591 = 5165387) B5165387
theorem B2295727 : Blo 2295435 2295727 := bstep (se 1 (by rfl) ⟨1721795, by rfl⟩ : syracuseStep 2295727 = 3443591) B3443591
theorem B3443597 : Blo 2295435 3443597 := bbase (se 3 (by rfl) ⟨645674, by rfl⟩ : syracuseStep 3443597 = 1291349) (by norm_num)
theorem B2295731 : Blo 2295435 2295731 := bstep (se 1 (by rfl) ⟨1721798, by rfl⟩ : syracuseStep 2295731 = 3443597) B3443597
theorem B5165405 : Blo 2295435 5165405 := bbase (se 3 (by rfl) ⟨968513, by rfl⟩ : syracuseStep 5165405 = 1937027) (by norm_num)
theorem B3443603 : Blo 2295435 3443603 := bstep (se 1 (by rfl) ⟨2582702, by rfl⟩ : syracuseStep 3443603 = 5165405) B5165405
theorem B2295735 : Blo 2295435 2295735 := bstep (se 1 (by rfl) ⟨1721801, by rfl⟩ : syracuseStep 2295735 = 3443603) B3443603
theorem B3874061 : Blo 2295435 3874061 := bbase (se 3 (by rfl) ⟨726386, by rfl⟩ : syracuseStep 3874061 = 1452773) (by norm_num)
theorem B2582707 : Blo 2295435 2582707 := bstep (se 1 (by rfl) ⟨1937030, by rfl⟩ : syracuseStep 2582707 = 3874061) B3874061
theorem B3443609 : Blo 2295435 3443609 := bstep (se 2 (by rfl) ⟨1291353, by rfl⟩ : syracuseStep 3443609 = 2582707) B2582707
theorem B2295739 : Blo 2295435 2295739 := bstep (se 1 (by rfl) ⟨1721804, by rfl⟩ : syracuseStep 2295739 = 3443609) B3443609
theorem B19612469 : Blo 2295435 19612469 := bbase (se 5 (by rfl) ⟨919334, by rfl⟩ : syracuseStep 19612469 = 1838669) (by norm_num)
theorem B13074979 : Blo 2295435 13074979 := bstep (se 1 (by rfl) ⟨9806234, by rfl⟩ : syracuseStep 13074979 = 19612469) B19612469
theorem B17433305 : Blo 2295435 17433305 := bstep (se 2 (by rfl) ⟨6537489, by rfl⟩ : syracuseStep 17433305 = 13074979) B13074979
theorem B11622203 : Blo 2295435 11622203 := bstep (se 1 (by rfl) ⟨8716652, by rfl⟩ : syracuseStep 11622203 = 17433305) B17433305
theorem B7748135 : Blo 2295435 7748135 := bstep (se 1 (by rfl) ⟨5811101, by rfl⟩ : syracuseStep 7748135 = 11622203) B11622203
theorem B5165423 : Blo 2295435 5165423 := bstep (se 1 (by rfl) ⟨3874067, by rfl⟩ : syracuseStep 5165423 = 7748135) B7748135
theorem B3443615 : Blo 2295435 3443615 := bstep (se 1 (by rfl) ⟨2582711, by rfl⟩ : syracuseStep 3443615 = 5165423) B5165423
theorem B2295743 : Blo 2295435 2295743 := bstep (se 1 (by rfl) ⟨1721807, by rfl⟩ : syracuseStep 2295743 = 3443615) B3443615
theorem B3443621 : Blo 2295435 3443621 := bbase (se 4 (by rfl) ⟨322839, by rfl⟩ : syracuseStep 3443621 = 645679) (by norm_num)
theorem B2295747 : Blo 2295435 2295747 := bstep (se 1 (by rfl) ⟨1721810, by rfl⟩ : syracuseStep 2295747 = 3443621) B3443621
theorem B2905561 : Blo 2295435 2905561 := bbase (se 2 (by rfl) ⟨1089585, by rfl⟩ : syracuseStep 2905561 = 2179171) (by norm_num)
theorem B3874081 : Blo 2295435 3874081 := bstep (se 2 (by rfl) ⟨1452780, by rfl⟩ : syracuseStep 3874081 = 2905561) B2905561
theorem B5165441 : Blo 2295435 5165441 := bstep (se 2 (by rfl) ⟨1937040, by rfl⟩ : syracuseStep 5165441 = 3874081) B3874081
theorem B3443627 : Blo 2295435 3443627 := bstep (se 1 (by rfl) ⟨2582720, by rfl⟩ : syracuseStep 3443627 = 5165441) B5165441
theorem B2295751 : Blo 2295435 2295751 := bstep (se 1 (by rfl) ⟨1721813, by rfl⟩ : syracuseStep 2295751 = 3443627) B3443627
theorem B2582725 : Blo 2295435 2582725 := bbase (se 4 (by rfl) ⟨242130, by rfl⟩ : syracuseStep 2582725 = 484261) (by norm_num)
theorem B3443633 : Blo 2295435 3443633 := bstep (se 2 (by rfl) ⟨1291362, by rfl⟩ : syracuseStep 3443633 = 2582725) B2582725
theorem B2295755 : Blo 2295435 2295755 := bstep (se 1 (by rfl) ⟨1721816, by rfl⟩ : syracuseStep 2295755 = 3443633) B3443633
theorem B4358357 : Blo 2295435 4358357 := bbase (se 7 (by rfl) ⟨51074, by rfl⟩ : syracuseStep 4358357 = 102149) (by norm_num)
theorem B2905571 : Blo 2295435 2905571 := bstep (se 1 (by rfl) ⟨2179178, by rfl⟩ : syracuseStep 2905571 = 4358357) B4358357
theorem B7748189 : Blo 2295435 7748189 := bstep (se 3 (by rfl) ⟨1452785, by rfl⟩ : syracuseStep 7748189 = 2905571) B2905571
theorem B5165459 : Blo 2295435 5165459 := bstep (se 1 (by rfl) ⟨3874094, by rfl⟩ : syracuseStep 5165459 = 7748189) B7748189
theorem B3443639 : Blo 2295435 3443639 := bstep (se 1 (by rfl) ⟨2582729, by rfl⟩ : syracuseStep 3443639 = 5165459) B5165459
theorem B2295759 : Blo 2295435 2295759 := bstep (se 1 (by rfl) ⟨1721819, by rfl⟩ : syracuseStep 2295759 = 3443639) B3443639
theorem B3443645 : Blo 2295435 3443645 := bbase (se 3 (by rfl) ⟨645683, by rfl⟩ : syracuseStep 3443645 = 1291367) (by norm_num)
theorem B2295763 : Blo 2295435 2295763 := bstep (se 1 (by rfl) ⟨1721822, by rfl⟩ : syracuseStep 2295763 = 3443645) B3443645
theorem B5165477 : Blo 2295435 5165477 := bbase (se 4 (by rfl) ⟨484263, by rfl⟩ : syracuseStep 5165477 = 968527) (by norm_num)
theorem B3443651 : Blo 2295435 3443651 := bstep (se 1 (by rfl) ⟨2582738, by rfl⟩ : syracuseStep 3443651 = 5165477) B5165477
theorem B2295767 : Blo 2295435 2295767 := bstep (se 1 (by rfl) ⟨1721825, by rfl⟩ : syracuseStep 2295767 = 3443651) B3443651
theorem B5811173 : Blo 2295435 5811173 := bbase (se 4 (by rfl) ⟨544797, by rfl⟩ : syracuseStep 5811173 = 1089595) (by norm_num)
theorem B3874115 : Blo 2295435 3874115 := bstep (se 1 (by rfl) ⟨2905586, by rfl⟩ : syracuseStep 3874115 = 5811173) B5811173
theorem B2582743 : Blo 2295435 2582743 := bstep (se 1 (by rfl) ⟨1937057, by rfl⟩ : syracuseStep 2582743 = 3874115) B3874115
theorem B3443657 : Blo 2295435 3443657 := bstep (se 2 (by rfl) ⟨1291371, by rfl⟩ : syracuseStep 3443657 = 2582743) B2582743
theorem B2295771 : Blo 2295435 2295771 := bstep (se 1 (by rfl) ⟨1721828, by rfl⟩ : syracuseStep 2295771 = 3443657) B3443657
theorem B2451593 : Blo 2295435 2451593 := bbase (se 2 (by rfl) ⟨919347, by rfl⟩ : syracuseStep 2451593 = 1838695) (by norm_num)
theorem B6537581 : Blo 2295435 6537581 := bstep (se 3 (by rfl) ⟨1225796, by rfl⟩ : syracuseStep 6537581 = 2451593) B2451593
theorem B4358387 : Blo 2295435 4358387 := bstep (se 1 (by rfl) ⟨3268790, by rfl⟩ : syracuseStep 4358387 = 6537581) B6537581
theorem B11622365 : Blo 2295435 11622365 := bstep (se 3 (by rfl) ⟨2179193, by rfl⟩ : syracuseStep 11622365 = 4358387) B4358387
theorem B7748243 : Blo 2295435 7748243 := bstep (se 1 (by rfl) ⟨5811182, by rfl⟩ : syracuseStep 7748243 = 11622365) B11622365
theorem B5165495 : Blo 2295435 5165495 := bstep (se 1 (by rfl) ⟨3874121, by rfl⟩ : syracuseStep 5165495 = 7748243) B7748243
theorem B3443663 : Blo 2295435 3443663 := bstep (se 1 (by rfl) ⟨2582747, by rfl⟩ : syracuseStep 3443663 = 5165495) B5165495
theorem B2295775 : Blo 2295435 2295775 := bstep (se 1 (by rfl) ⟨1721831, by rfl⟩ : syracuseStep 2295775 = 3443663) B3443663
theorem B3443669 : Blo 2295435 3443669 := bbase (se 7 (by rfl) ⟨40355, by rfl⟩ : syracuseStep 3443669 = 80711) (by norm_num)
theorem B2295779 : Blo 2295435 2295779 := bstep (se 1 (by rfl) ⟨1721834, by rfl⟩ : syracuseStep 2295779 = 3443669) B3443669
theorem B8716805 : Blo 2295435 8716805 := bbase (se 4 (by rfl) ⟨817200, by rfl⟩ : syracuseStep 8716805 = 1634401) (by norm_num)
theorem B5811203 : Blo 2295435 5811203 := bstep (se 1 (by rfl) ⟨4358402, by rfl⟩ : syracuseStep 5811203 = 8716805) B8716805
theorem B3874135 : Blo 2295435 3874135 := bstep (se 1 (by rfl) ⟨2905601, by rfl⟩ : syracuseStep 3874135 = 5811203) B5811203
theorem B5165513 : Blo 2295435 5165513 := bstep (se 2 (by rfl) ⟨1937067, by rfl⟩ : syracuseStep 5165513 = 3874135) B3874135
theorem B3443675 : Blo 2295435 3443675 := bstep (se 1 (by rfl) ⟨2582756, by rfl⟩ : syracuseStep 3443675 = 5165513) B5165513
theorem B2295783 : Blo 2295435 2295783 := bstep (se 1 (by rfl) ⟨1721837, by rfl⟩ : syracuseStep 2295783 = 3443675) B3443675
theorem B2582761 : Blo 2295435 2582761 := bbase (se 2 (by rfl) ⟨968535, by rfl⟩ : syracuseStep 2582761 = 1937071) (by norm_num)
theorem B3443681 : Blo 2295435 3443681 := bstep (se 2 (by rfl) ⟨1291380, by rfl⟩ : syracuseStep 3443681 = 2582761) B2582761
theorem B2295787 : Blo 2295435 2295787 := bstep (se 1 (by rfl) ⟨1721840, by rfl⟩ : syracuseStep 2295787 = 3443681) B3443681
theorem B13075253 : Blo 2295435 13075253 := bbase (se 5 (by rfl) ⟨612902, by rfl⟩ : syracuseStep 13075253 = 1225805) (by norm_num)
theorem B8716835 : Blo 2295435 8716835 := bstep (se 1 (by rfl) ⟨6537626, by rfl⟩ : syracuseStep 8716835 = 13075253) B13075253
theorem B5811223 : Blo 2295435 5811223 := bstep (se 1 (by rfl) ⟨4358417, by rfl⟩ : syracuseStep 5811223 = 8716835) B8716835
theorem B7748297 : Blo 2295435 7748297 := bstep (se 2 (by rfl) ⟨2905611, by rfl⟩ : syracuseStep 7748297 = 5811223) B5811223
theorem B5165531 : Blo 2295435 5165531 := bstep (se 1 (by rfl) ⟨3874148, by rfl⟩ : syracuseStep 5165531 = 7748297) B7748297
theorem B3443687 : Blo 2295435 3443687 := bstep (se 1 (by rfl) ⟨2582765, by rfl⟩ : syracuseStep 3443687 = 5165531) B5165531
theorem B2295791 : Blo 2295435 2295791 := bstep (se 1 (by rfl) ⟨1721843, by rfl⟩ : syracuseStep 2295791 = 3443687) B3443687
theorem B3443693 : Blo 2295435 3443693 := bbase (se 3 (by rfl) ⟨645692, by rfl⟩ : syracuseStep 3443693 = 1291385) (by norm_num)
theorem B2295795 : Blo 2295435 2295795 := bstep (se 1 (by rfl) ⟨1721846, by rfl⟩ : syracuseStep 2295795 = 3443693) B3443693
theorem B5165549 : Blo 2295435 5165549 := bbase (se 3 (by rfl) ⟨968540, by rfl⟩ : syracuseStep 5165549 = 1937081) (by norm_num)
theorem B3443699 : Blo 2295435 3443699 := bstep (se 1 (by rfl) ⟨2582774, by rfl⟩ : syracuseStep 3443699 = 5165549) B5165549
theorem B2295799 : Blo 2295435 2295799 := bstep (se 1 (by rfl) ⟨1721849, by rfl⟩ : syracuseStep 2295799 = 3443699) B3443699
theorem B2485073 : Blo 2295435 2485073 := bbase (se 2 (by rfl) ⟨931902, by rfl⟩ : syracuseStep 2485073 = 1863805) (by norm_num)
theorem B6626861 : Blo 2295435 6626861 := bstep (se 3 (by rfl) ⟨1242536, by rfl⟩ : syracuseStep 6626861 = 2485073) B2485073
theorem B4417907 : Blo 2295435 4417907 := bstep (se 1 (by rfl) ⟨3313430, by rfl⟩ : syracuseStep 4417907 = 6626861) B6626861
theorem B11781085 : Blo 2295435 11781085 := bstep (se 3 (by rfl) ⟨2208953, by rfl⟩ : syracuseStep 11781085 = 4417907) B4417907
theorem B15708113 : Blo 2295435 15708113 := bstep (se 2 (by rfl) ⟨5890542, by rfl⟩ : syracuseStep 15708113 = 11781085) B11781085
theorem B10472075 : Blo 2295435 10472075 := bstep (se 1 (by rfl) ⟨7854056, by rfl⟩ : syracuseStep 10472075 = 15708113) B15708113
theorem B6981383 : Blo 2295435 6981383 := bstep (se 1 (by rfl) ⟨5236037, by rfl⟩ : syracuseStep 6981383 = 10472075) B10472075
theorem B4654255 : Blo 2295435 4654255 := bstep (se 1 (by rfl) ⟨3490691, by rfl⟩ : syracuseStep 4654255 = 6981383) B6981383
theorem B6205673 : Blo 2295435 6205673 := bstep (se 2 (by rfl) ⟨2327127, by rfl⟩ : syracuseStep 6205673 = 4654255) B4654255
theorem B16548461 : Blo 2295435 16548461 := bstep (se 3 (by rfl) ⟨3102836, by rfl⟩ : syracuseStep 16548461 = 6205673) B6205673
theorem B11032307 : Blo 2295435 11032307 := bstep (se 1 (by rfl) ⟨8274230, by rfl⟩ : syracuseStep 11032307 = 16548461) B16548461
theorem B7354871 : Blo 2295435 7354871 := bstep (se 1 (by rfl) ⟨5516153, by rfl⟩ : syracuseStep 7354871 = 11032307) B11032307
theorem B4903247 : Blo 2295435 4903247 := bstep (se 1 (by rfl) ⟨3677435, by rfl⟩ : syracuseStep 4903247 = 7354871) B7354871
theorem B3268831 : Blo 2295435 3268831 := bstep (se 1 (by rfl) ⟨2451623, by rfl⟩ : syracuseStep 3268831 = 4903247) B4903247
theorem B4358441 : Blo 2295435 4358441 := bstep (se 2 (by rfl) ⟨1634415, by rfl⟩ : syracuseStep 4358441 = 3268831) B3268831
theorem B2905627 : Blo 2295435 2905627 := bstep (se 1 (by rfl) ⟨2179220, by rfl⟩ : syracuseStep 2905627 = 4358441) B4358441
theorem B3874169 : Blo 2295435 3874169 := bstep (se 2 (by rfl) ⟨1452813, by rfl⟩ : syracuseStep 3874169 = 2905627) B2905627
theorem B2582779 : Blo 2295435 2582779 := bstep (se 1 (by rfl) ⟨1937084, by rfl⟩ : syracuseStep 2582779 = 3874169) B3874169
theorem B3443705 : Blo 2295435 3443705 := bstep (se 2 (by rfl) ⟨1291389, by rfl⟩ : syracuseStep 3443705 = 2582779) B2582779
theorem B2295803 : Blo 2295435 2295803 := bstep (se 1 (by rfl) ⟨1721852, by rfl⟩ : syracuseStep 2295803 = 3443705) B3443705
theorem B23562197 : Blo 2295435 23562197 := bbase (se 7 (by rfl) ⟨276119, by rfl⟩ : syracuseStep 23562197 = 552239) (by norm_num)
theorem B15708131 : Blo 2295435 15708131 := bstep (se 1 (by rfl) ⟨11781098, by rfl⟩ : syracuseStep 15708131 = 23562197) B23562197
theorem B10472087 : Blo 2295435 10472087 := bstep (se 1 (by rfl) ⟨7854065, by rfl⟩ : syracuseStep 10472087 = 15708131) B15708131
theorem B6981391 : Blo 2295435 6981391 := bstep (se 1 (by rfl) ⟨5236043, by rfl⟩ : syracuseStep 6981391 = 10472087) B10472087
theorem B37234085 : Blo 2295435 37234085 := bstep (se 4 (by rfl) ⟨3490695, by rfl⟩ : syracuseStep 37234085 = 6981391) B6981391
theorem B99290893 : Blo 2295435 99290893 := bstep (se 3 (by rfl) ⟨18617042, by rfl⟩ : syracuseStep 99290893 = 37234085) B37234085
theorem B132387857 : Blo 2295435 132387857 := bstep (se 2 (by rfl) ⟨49645446, by rfl⟩ : syracuseStep 132387857 = 99290893) B99290893
theorem B88258571 : Blo 2295435 88258571 := bstep (se 1 (by rfl) ⟨66193928, by rfl⟩ : syracuseStep 88258571 = 132387857) B132387857
theorem B58839047 : Blo 2295435 58839047 := bstep (se 1 (by rfl) ⟨44129285, by rfl⟩ : syracuseStep 58839047 = 88258571) B88258571
theorem B39226031 : Blo 2295435 39226031 := bstep (se 1 (by rfl) ⟨29419523, by rfl⟩ : syracuseStep 39226031 = 58839047) B58839047
theorem B26150687 : Blo 2295435 26150687 := bstep (se 1 (by rfl) ⟨19613015, by rfl⟩ : syracuseStep 26150687 = 39226031) B39226031
theorem B17433791 : Blo 2295435 17433791 := bstep (se 1 (by rfl) ⟨13075343, by rfl⟩ : syracuseStep 17433791 = 26150687) B26150687
theorem B11622527 : Blo 2295435 11622527 := bstep (se 1 (by rfl) ⟨8716895, by rfl⟩ : syracuseStep 11622527 = 17433791) B17433791
theorem B7748351 : Blo 2295435 7748351 := bstep (se 1 (by rfl) ⟨5811263, by rfl⟩ : syracuseStep 7748351 = 11622527) B11622527
theorem B5165567 : Blo 2295435 5165567 := bstep (se 1 (by rfl) ⟨3874175, by rfl⟩ : syracuseStep 5165567 = 7748351) B7748351
theorem B3443711 : Blo 2295435 3443711 := bstep (se 1 (by rfl) ⟨2582783, by rfl⟩ : syracuseStep 3443711 = 5165567) B5165567
theorem B2295807 : Blo 2295435 2295807 := bstep (se 1 (by rfl) ⟨1721855, by rfl⟩ : syracuseStep 2295807 = 3443711) B3443711
theorem B3443717 : Blo 2295435 3443717 := bbase (se 4 (by rfl) ⟨322848, by rfl⟩ : syracuseStep 3443717 = 645697) (by norm_num)
theorem B2295811 : Blo 2295435 2295811 := bstep (se 1 (by rfl) ⟨1721858, by rfl⟩ : syracuseStep 2295811 = 3443717) B3443717
theorem B3874189 : Blo 2295435 3874189 := bbase (se 3 (by rfl) ⟨726410, by rfl⟩ : syracuseStep 3874189 = 1452821) (by norm_num)
theorem B5165585 : Blo 2295435 5165585 := bstep (se 2 (by rfl) ⟨1937094, by rfl⟩ : syracuseStep 5165585 = 3874189) B3874189
theorem B3443723 : Blo 2295435 3443723 := bstep (se 1 (by rfl) ⟨2582792, by rfl⟩ : syracuseStep 3443723 = 5165585) B5165585
theorem B2295815 : Blo 2295435 2295815 := bstep (se 1 (by rfl) ⟨1721861, by rfl⟩ : syracuseStep 2295815 = 3443723) B3443723
theorem B2582797 : Blo 2295435 2582797 := bbase (se 3 (by rfl) ⟨484274, by rfl⟩ : syracuseStep 2582797 = 968549) (by norm_num)
theorem B3443729 : Blo 2295435 3443729 := bstep (se 2 (by rfl) ⟨1291398, by rfl⟩ : syracuseStep 3443729 = 2582797) B2582797
theorem B2295819 : Blo 2295435 2295819 := bstep (se 1 (by rfl) ⟨1721864, by rfl⟩ : syracuseStep 2295819 = 3443729) B3443729
theorem B7748405 : Blo 2295435 7748405 := bbase (se 5 (by rfl) ⟨363206, by rfl⟩ : syracuseStep 7748405 = 726413) (by norm_num)
theorem B5165603 : Blo 2295435 5165603 := bstep (se 1 (by rfl) ⟨3874202, by rfl⟩ : syracuseStep 5165603 = 7748405) B7748405
theorem B3443735 : Blo 2295435 3443735 := bstep (se 1 (by rfl) ⟨2582801, by rfl⟩ : syracuseStep 3443735 = 5165603) B5165603
theorem B2295823 : Blo 2295435 2295823 := bstep (se 1 (by rfl) ⟨1721867, by rfl⟩ : syracuseStep 2295823 = 3443735) B3443735
theorem B3443741 : Blo 2295435 3443741 := bbase (se 3 (by rfl) ⟨645701, by rfl⟩ : syracuseStep 3443741 = 1291403) (by norm_num)
theorem B2295827 : Blo 2295435 2295827 := bstep (se 1 (by rfl) ⟨1721870, by rfl⟩ : syracuseStep 2295827 = 3443741) B3443741
theorem B5165621 : Blo 2295435 5165621 := bbase (se 5 (by rfl) ⟨242138, by rfl⟩ : syracuseStep 5165621 = 484277) (by norm_num)
theorem B3443747 : Blo 2295435 3443747 := bstep (se 1 (by rfl) ⟨2582810, by rfl⟩ : syracuseStep 3443747 = 5165621) B5165621
theorem B2295831 : Blo 2295435 2295831 := bstep (se 1 (by rfl) ⟨1721873, by rfl⟩ : syracuseStep 2295831 = 3443747) B3443747
theorem B9806629 : Blo 2295435 9806629 := bbase (se 4 (by rfl) ⟨919371, by rfl⟩ : syracuseStep 9806629 = 1838743) (by norm_num)
theorem B13075505 : Blo 2295435 13075505 := bstep (se 2 (by rfl) ⟨4903314, by rfl⟩ : syracuseStep 13075505 = 9806629) B9806629
theorem B8717003 : Blo 2295435 8717003 := bstep (se 1 (by rfl) ⟨6537752, by rfl⟩ : syracuseStep 8717003 = 13075505) B13075505
theorem B5811335 : Blo 2295435 5811335 := bstep (se 1 (by rfl) ⟨4358501, by rfl⟩ : syracuseStep 5811335 = 8717003) B8717003
theorem B3874223 : Blo 2295435 3874223 := bstep (se 1 (by rfl) ⟨2905667, by rfl⟩ : syracuseStep 3874223 = 5811335) B5811335
theorem B2582815 : Blo 2295435 2582815 := bstep (se 1 (by rfl) ⟨1937111, by rfl⟩ : syracuseStep 2582815 = 3874223) B3874223
theorem B3443753 : Blo 2295435 3443753 := bstep (se 2 (by rfl) ⟨1291407, by rfl⟩ : syracuseStep 3443753 = 2582815) B2582815
theorem B2295835 : Blo 2295435 2295835 := bstep (se 1 (by rfl) ⟨1721876, by rfl⟩ : syracuseStep 2295835 = 3443753) B3443753
theorem B9806645 : Blo 2295435 9806645 := bbase (se 5 (by rfl) ⟨459686, by rfl⟩ : syracuseStep 9806645 = 919373) (by norm_num)
theorem B6537763 : Blo 2295435 6537763 := bstep (se 1 (by rfl) ⟨4903322, by rfl⟩ : syracuseStep 6537763 = 9806645) B9806645
theorem B8717017 : Blo 2295435 8717017 := bstep (se 2 (by rfl) ⟨3268881, by rfl⟩ : syracuseStep 8717017 = 6537763) B6537763
theorem B11622689 : Blo 2295435 11622689 := bstep (se 2 (by rfl) ⟨4358508, by rfl⟩ : syracuseStep 11622689 = 8717017) B8717017
theorem B7748459 : Blo 2295435 7748459 := bstep (se 1 (by rfl) ⟨5811344, by rfl⟩ : syracuseStep 7748459 = 11622689) B11622689
theorem B5165639 : Blo 2295435 5165639 := bstep (se 1 (by rfl) ⟨3874229, by rfl⟩ : syracuseStep 5165639 = 7748459) B7748459
theorem B3443759 : Blo 2295435 3443759 := bstep (se 1 (by rfl) ⟨2582819, by rfl⟩ : syracuseStep 3443759 = 5165639) B5165639
theorem B2295839 : Blo 2295435 2295839 := bstep (se 1 (by rfl) ⟨1721879, by rfl⟩ : syracuseStep 2295839 = 3443759) B3443759
theorem B3443765 : Blo 2295435 3443765 := bbase (se 5 (by rfl) ⟨161426, by rfl⟩ : syracuseStep 3443765 = 322853) (by norm_num)
theorem B2295843 : Blo 2295435 2295843 := bstep (se 1 (by rfl) ⟨1721882, by rfl⟩ : syracuseStep 2295843 = 3443765) B3443765
theorem B5811365 : Blo 2295435 5811365 := bbase (se 4 (by rfl) ⟨544815, by rfl⟩ : syracuseStep 5811365 = 1089631) (by norm_num)
theorem B3874243 : Blo 2295435 3874243 := bstep (se 1 (by rfl) ⟨2905682, by rfl⟩ : syracuseStep 3874243 = 5811365) B5811365
theorem B5165657 : Blo 2295435 5165657 := bstep (se 2 (by rfl) ⟨1937121, by rfl⟩ : syracuseStep 5165657 = 3874243) B3874243
theorem B3443771 : Blo 2295435 3443771 := bstep (se 1 (by rfl) ⟨2582828, by rfl⟩ : syracuseStep 3443771 = 5165657) B5165657
theorem B2295847 : Blo 2295435 2295847 := bstep (se 1 (by rfl) ⟨1721885, by rfl⟩ : syracuseStep 2295847 = 3443771) B3443771
theorem B2582833 : Blo 2295435 2582833 := bbase (se 2 (by rfl) ⟨968562, by rfl⟩ : syracuseStep 2582833 = 1937125) (by norm_num)
theorem B3443777 : Blo 2295435 3443777 := bstep (se 2 (by rfl) ⟨1291416, by rfl⟩ : syracuseStep 3443777 = 2582833) B2582833
theorem B2295851 : Blo 2295435 2295851 := bstep (se 1 (by rfl) ⟨1721888, by rfl⟩ : syracuseStep 2295851 = 3443777) B3443777
theorem B4903357 : Blo 2295435 4903357 := bbase (se 3 (by rfl) ⟨919379, by rfl⟩ : syracuseStep 4903357 = 1838759) (by norm_num)
theorem B6537809 : Blo 2295435 6537809 := bstep (se 2 (by rfl) ⟨2451678, by rfl⟩ : syracuseStep 6537809 = 4903357) B4903357
theorem B4358539 : Blo 2295435 4358539 := bstep (se 1 (by rfl) ⟨3268904, by rfl⟩ : syracuseStep 4358539 = 6537809) B6537809
theorem B5811385 : Blo 2295435 5811385 := bstep (se 2 (by rfl) ⟨2179269, by rfl⟩ : syracuseStep 5811385 = 4358539) B4358539
theorem B7748513 : Blo 2295435 7748513 := bstep (se 2 (by rfl) ⟨2905692, by rfl⟩ : syracuseStep 7748513 = 5811385) B5811385
theorem B5165675 : Blo 2295435 5165675 := bstep (se 1 (by rfl) ⟨3874256, by rfl⟩ : syracuseStep 5165675 = 7748513) B7748513
theorem B3443783 : Blo 2295435 3443783 := bstep (se 1 (by rfl) ⟨2582837, by rfl⟩ : syracuseStep 3443783 = 5165675) B5165675
theorem B2295855 : Blo 2295435 2295855 := bstep (se 1 (by rfl) ⟨1721891, by rfl⟩ : syracuseStep 2295855 = 3443783) B3443783
theorem B3443789 : Blo 2295435 3443789 := bbase (se 3 (by rfl) ⟨645710, by rfl⟩ : syracuseStep 3443789 = 1291421) (by norm_num)
theorem B2295859 : Blo 2295435 2295859 := bstep (se 1 (by rfl) ⟨1721894, by rfl⟩ : syracuseStep 2295859 = 3443789) B3443789
theorem B5165693 : Blo 2295435 5165693 := bbase (se 3 (by rfl) ⟨968567, by rfl⟩ : syracuseStep 5165693 = 1937135) (by norm_num)
theorem B3443795 : Blo 2295435 3443795 := bstep (se 1 (by rfl) ⟨2582846, by rfl⟩ : syracuseStep 3443795 = 5165693) B5165693
theorem B2295863 : Blo 2295435 2295863 := bstep (se 1 (by rfl) ⟨1721897, by rfl⟩ : syracuseStep 2295863 = 3443795) B3443795
theorem B3874277 : Blo 2295435 3874277 := bbase (se 4 (by rfl) ⟨363213, by rfl⟩ : syracuseStep 3874277 = 726427) (by norm_num)
theorem B2582851 : Blo 2295435 2582851 := bstep (se 1 (by rfl) ⟨1937138, by rfl⟩ : syracuseStep 2582851 = 3874277) B3874277
theorem B3443801 : Blo 2295435 3443801 := bstep (se 2 (by rfl) ⟨1291425, by rfl⟩ : syracuseStep 3443801 = 2582851) B2582851
theorem B2295867 : Blo 2295435 2295867 := bstep (se 1 (by rfl) ⟨1721900, by rfl⟩ : syracuseStep 2295867 = 3443801) B3443801
theorem B3538421 : Blo 2295435 3538421 := bbase (se 5 (by rfl) ⟨165863, by rfl⟩ : syracuseStep 3538421 = 331727) (by norm_num)
theorem B2358947 : Blo 2295435 2358947 := bstep (se 1 (by rfl) ⟨1769210, by rfl⟩ : syracuseStep 2358947 = 3538421) B3538421
theorem B6290525 : Blo 2295435 6290525 := bstep (se 3 (by rfl) ⟨1179473, by rfl⟩ : syracuseStep 6290525 = 2358947) B2358947
theorem B4193683 : Blo 2295435 4193683 := bstep (se 1 (by rfl) ⟨3145262, by rfl⟩ : syracuseStep 4193683 = 6290525) B6290525
theorem B22366309 : Blo 2295435 22366309 := bstep (se 4 (by rfl) ⟨2096841, by rfl⟩ : syracuseStep 22366309 = 4193683) B4193683
theorem B29821745 : Blo 2295435 29821745 := bstep (se 2 (by rfl) ⟨11183154, by rfl⟩ : syracuseStep 29821745 = 22366309) B22366309
theorem B19881163 : Blo 2295435 19881163 := bstep (se 1 (by rfl) ⟨14910872, by rfl⟩ : syracuseStep 19881163 = 29821745) B29821745
theorem B26508217 : Blo 2295435 26508217 := bstep (se 2 (by rfl) ⟨9940581, by rfl⟩ : syracuseStep 26508217 = 19881163) B19881163
theorem B35344289 : Blo 2295435 35344289 := bstep (se 2 (by rfl) ⟨13254108, by rfl⟩ : syracuseStep 35344289 = 26508217) B26508217
theorem B23562859 : Blo 2295435 23562859 := bstep (se 1 (by rfl) ⟨17672144, by rfl⟩ : syracuseStep 23562859 = 35344289) B35344289
theorem B31417145 : Blo 2295435 31417145 := bstep (se 2 (by rfl) ⟨11781429, by rfl⟩ : syracuseStep 31417145 = 23562859) B23562859
theorem B20944763 : Blo 2295435 20944763 := bstep (se 1 (by rfl) ⟨15708572, by rfl⟩ : syracuseStep 20944763 = 31417145) B31417145
theorem B13963175 : Blo 2295435 13963175 := bstep (se 1 (by rfl) ⟨10472381, by rfl⟩ : syracuseStep 13963175 = 20944763) B20944763
theorem B9308783 : Blo 2295435 9308783 := bstep (se 1 (by rfl) ⟨6981587, by rfl⟩ : syracuseStep 9308783 = 13963175) B13963175
theorem B24823421 : Blo 2295435 24823421 := bstep (se 3 (by rfl) ⟨4654391, by rfl⟩ : syracuseStep 24823421 = 9308783) B9308783
theorem B16548947 : Blo 2295435 16548947 := bstep (se 1 (by rfl) ⟨12411710, by rfl⟩ : syracuseStep 16548947 = 24823421) B24823421
theorem B11032631 : Blo 2295435 11032631 := bstep (se 1 (by rfl) ⟨8274473, by rfl⟩ : syracuseStep 11032631 = 16548947) B16548947
theorem B7355087 : Blo 2295435 7355087 := bstep (se 1 (by rfl) ⟨5516315, by rfl⟩ : syracuseStep 7355087 = 11032631) B11032631
theorem B4903391 : Blo 2295435 4903391 := bstep (se 1 (by rfl) ⟨3677543, by rfl⟩ : syracuseStep 4903391 = 7355087) B7355087
theorem B3268927 : Blo 2295435 3268927 := bstep (se 1 (by rfl) ⟨2451695, by rfl⟩ : syracuseStep 3268927 = 4903391) B4903391
theorem B17434277 : Blo 2295435 17434277 := bstep (se 4 (by rfl) ⟨1634463, by rfl⟩ : syracuseStep 17434277 = 3268927) B3268927
theorem B11622851 : Blo 2295435 11622851 := bstep (se 1 (by rfl) ⟨8717138, by rfl⟩ : syracuseStep 11622851 = 17434277) B17434277
theorem B7748567 : Blo 2295435 7748567 := bstep (se 1 (by rfl) ⟨5811425, by rfl⟩ : syracuseStep 7748567 = 11622851) B11622851
theorem B5165711 : Blo 2295435 5165711 := bstep (se 1 (by rfl) ⟨3874283, by rfl⟩ : syracuseStep 5165711 = 7748567) B7748567
theorem B3443807 : Blo 2295435 3443807 := bstep (se 1 (by rfl) ⟨2582855, by rfl⟩ : syracuseStep 3443807 = 5165711) B5165711
theorem B2295871 : Blo 2295435 2295871 := bstep (se 1 (by rfl) ⟨1721903, by rfl⟩ : syracuseStep 2295871 = 3443807) B3443807
theorem B3443813 : Blo 2295435 3443813 := bbase (se 4 (by rfl) ⟨322857, by rfl⟩ : syracuseStep 3443813 = 645715) (by norm_num)
theorem B2295875 : Blo 2295435 2295875 := bstep (se 1 (by rfl) ⟨1721906, by rfl⟩ : syracuseStep 2295875 = 3443813) B3443813
theorem B3677557 : Blo 2295435 3677557 := bbase (se 5 (by rfl) ⟨172385, by rfl⟩ : syracuseStep 3677557 = 344771) (by norm_num)
theorem B4903409 : Blo 2295435 4903409 := bstep (se 2 (by rfl) ⟨1838778, by rfl⟩ : syracuseStep 4903409 = 3677557) B3677557
theorem B3268939 : Blo 2295435 3268939 := bstep (se 1 (by rfl) ⟨2451704, by rfl⟩ : syracuseStep 3268939 = 4903409) B4903409
theorem B4358585 : Blo 2295435 4358585 := bstep (se 2 (by rfl) ⟨1634469, by rfl⟩ : syracuseStep 4358585 = 3268939) B3268939
theorem B2905723 : Blo 2295435 2905723 := bstep (se 1 (by rfl) ⟨2179292, by rfl⟩ : syracuseStep 2905723 = 4358585) B4358585
theorem B3874297 : Blo 2295435 3874297 := bstep (se 2 (by rfl) ⟨1452861, by rfl⟩ : syracuseStep 3874297 = 2905723) B2905723
theorem B5165729 : Blo 2295435 5165729 := bstep (se 2 (by rfl) ⟨1937148, by rfl⟩ : syracuseStep 5165729 = 3874297) B3874297
theorem B3443819 : Blo 2295435 3443819 := bstep (se 1 (by rfl) ⟨2582864, by rfl⟩ : syracuseStep 3443819 = 5165729) B5165729
theorem B2295879 : Blo 2295435 2295879 := bstep (se 1 (by rfl) ⟨1721909, by rfl⟩ : syracuseStep 2295879 = 3443819) B3443819
theorem B2582869 : Blo 2295435 2582869 := bbase (se 10 (by rfl) ⟨3783, by rfl⟩ : syracuseStep 2582869 = 7567) (by norm_num)
theorem B3443825 : Blo 2295435 3443825 := bstep (se 2 (by rfl) ⟨1291434, by rfl⟩ : syracuseStep 3443825 = 2582869) B2582869
theorem B2295883 : Blo 2295435 2295883 := bstep (se 1 (by rfl) ⟨1721912, by rfl⟩ : syracuseStep 2295883 = 3443825) B3443825
theorem B2905733 : Blo 2295435 2905733 := bbase (se 4 (by rfl) ⟨272412, by rfl⟩ : syracuseStep 2905733 = 544825) (by norm_num)
theorem B7748621 : Blo 2295435 7748621 := bstep (se 3 (by rfl) ⟨1452866, by rfl⟩ : syracuseStep 7748621 = 2905733) B2905733
theorem B5165747 : Blo 2295435 5165747 := bstep (se 1 (by rfl) ⟨3874310, by rfl⟩ : syracuseStep 5165747 = 7748621) B7748621
theorem B3443831 : Blo 2295435 3443831 := bstep (se 1 (by rfl) ⟨2582873, by rfl⟩ : syracuseStep 3443831 = 5165747) B5165747
theorem B2295887 : Blo 2295435 2295887 := bstep (se 1 (by rfl) ⟨1721915, by rfl⟩ : syracuseStep 2295887 = 3443831) B3443831
theorem B3443837 : Blo 2295435 3443837 := bbase (se 3 (by rfl) ⟨645719, by rfl⟩ : syracuseStep 3443837 = 1291439) (by norm_num)
theorem B2295891 : Blo 2295435 2295891 := bstep (se 1 (by rfl) ⟨1721918, by rfl⟩ : syracuseStep 2295891 = 3443837) B3443837
theorem B5165765 : Blo 2295435 5165765 := bbase (se 4 (by rfl) ⟨484290, by rfl⟩ : syracuseStep 5165765 = 968581) (by norm_num)
theorem B3443843 : Blo 2295435 3443843 := bstep (se 1 (by rfl) ⟨2582882, by rfl⟩ : syracuseStep 3443843 = 5165765) B5165765
theorem B2295895 : Blo 2295435 2295895 := bstep (se 1 (by rfl) ⟨1721921, by rfl⟩ : syracuseStep 2295895 = 3443843) B3443843
theorem B3980773 : Blo 2295435 3980773 := bbase (se 4 (by rfl) ⟨373197, by rfl⟩ : syracuseStep 3980773 = 746395) (by norm_num)
theorem B5307697 : Blo 2295435 5307697 := bstep (se 2 (by rfl) ⟨1990386, by rfl⟩ : syracuseStep 5307697 = 3980773) B3980773
theorem B7076929 : Blo 2295435 7076929 := bstep (se 2 (by rfl) ⟨2653848, by rfl⟩ : syracuseStep 7076929 = 5307697) B5307697
theorem B9435905 : Blo 2295435 9435905 := bstep (se 2 (by rfl) ⟨3538464, by rfl⟩ : syracuseStep 9435905 = 7076929) B7076929
theorem B6290603 : Blo 2295435 6290603 := bstep (se 1 (by rfl) ⟨4717952, by rfl⟩ : syracuseStep 6290603 = 9435905) B9435905
theorem B4193735 : Blo 2295435 4193735 := bstep (se 1 (by rfl) ⟨3145301, by rfl⟩ : syracuseStep 4193735 = 6290603) B6290603
theorem B11183293 : Blo 2295435 11183293 := bstep (se 3 (by rfl) ⟨2096867, by rfl⟩ : syracuseStep 11183293 = 4193735) B4193735
theorem B14911057 : Blo 2295435 14911057 := bstep (se 2 (by rfl) ⟨5591646, by rfl⟩ : syracuseStep 14911057 = 11183293) B11183293
theorem B19881409 : Blo 2295435 19881409 := bstep (se 2 (by rfl) ⟨7455528, by rfl⟩ : syracuseStep 19881409 = 14911057) B14911057
theorem B26508545 : Blo 2295435 26508545 := bstep (se 2 (by rfl) ⟨9940704, by rfl⟩ : syracuseStep 26508545 = 19881409) B19881409
theorem B17672363 : Blo 2295435 17672363 := bstep (se 1 (by rfl) ⟨13254272, by rfl⟩ : syracuseStep 17672363 = 26508545) B26508545
theorem B11781575 : Blo 2295435 11781575 := bstep (se 1 (by rfl) ⟨8836181, by rfl⟩ : syracuseStep 11781575 = 17672363) B17672363
theorem B7854383 : Blo 2295435 7854383 := bstep (se 1 (by rfl) ⟨5890787, by rfl⟩ : syracuseStep 7854383 = 11781575) B11781575
theorem B5236255 : Blo 2295435 5236255 := bstep (se 1 (by rfl) ⟨3927191, by rfl⟩ : syracuseStep 5236255 = 7854383) B7854383
theorem B27926693 : Blo 2295435 27926693 := bstep (se 4 (by rfl) ⟨2618127, by rfl⟩ : syracuseStep 27926693 = 5236255) B5236255
theorem B18617795 : Blo 2295435 18617795 := bstep (se 1 (by rfl) ⟨13963346, by rfl⟩ : syracuseStep 18617795 = 27926693) B27926693
theorem B12411863 : Blo 2295435 12411863 := bstep (se 1 (by rfl) ⟨9308897, by rfl⟩ : syracuseStep 12411863 = 18617795) B18617795
theorem B8274575 : Blo 2295435 8274575 := bstep (se 1 (by rfl) ⟨6205931, by rfl⟩ : syracuseStep 8274575 = 12411863) B12411863
theorem B22065533 : Blo 2295435 22065533 := bstep (se 3 (by rfl) ⟨4137287, by rfl⟩ : syracuseStep 22065533 = 8274575) B8274575
theorem B14710355 : Blo 2295435 14710355 := bstep (se 1 (by rfl) ⟨11032766, by rfl⟩ : syracuseStep 14710355 = 22065533) B22065533
theorem B9806903 : Blo 2295435 9806903 := bstep (se 1 (by rfl) ⟨7355177, by rfl⟩ : syracuseStep 9806903 = 14710355) B14710355
theorem B6537935 : Blo 2295435 6537935 := bstep (se 1 (by rfl) ⟨4903451, by rfl⟩ : syracuseStep 6537935 = 9806903) B9806903
theorem B4358623 : Blo 2295435 4358623 := bstep (se 1 (by rfl) ⟨3268967, by rfl⟩ : syracuseStep 4358623 = 6537935) B6537935
theorem B5811497 : Blo 2295435 5811497 := bstep (se 2 (by rfl) ⟨2179311, by rfl⟩ : syracuseStep 5811497 = 4358623) B4358623
theorem B3874331 : Blo 2295435 3874331 := bstep (se 1 (by rfl) ⟨2905748, by rfl⟩ : syracuseStep 3874331 = 5811497) B5811497
theorem B2582887 : Blo 2295435 2582887 := bstep (se 1 (by rfl) ⟨1937165, by rfl⟩ : syracuseStep 2582887 = 3874331) B3874331
theorem B3443849 : Blo 2295435 3443849 := bstep (se 2 (by rfl) ⟨1291443, by rfl⟩ : syracuseStep 3443849 = 2582887) B2582887
theorem B2295899 : Blo 2295435 2295899 := bstep (se 1 (by rfl) ⟨1721924, by rfl⟩ : syracuseStep 2295899 = 3443849) B3443849
theorem B11623013 : Blo 2295435 11623013 := bbase (se 4 (by rfl) ⟨1089657, by rfl⟩ : syracuseStep 11623013 = 2179315) (by norm_num)
theorem B7748675 : Blo 2295435 7748675 := bstep (se 1 (by rfl) ⟨5811506, by rfl⟩ : syracuseStep 7748675 = 11623013) B11623013
theorem B5165783 : Blo 2295435 5165783 := bstep (se 1 (by rfl) ⟨3874337, by rfl⟩ : syracuseStep 5165783 = 7748675) B7748675
theorem B3443855 : Blo 2295435 3443855 := bstep (se 1 (by rfl) ⟨2582891, by rfl⟩ : syracuseStep 3443855 = 5165783) B5165783
theorem B2295903 : Blo 2295435 2295903 := bstep (se 1 (by rfl) ⟨1721927, by rfl⟩ : syracuseStep 2295903 = 3443855) B3443855
theorem B3443861 : Blo 2295435 3443861 := bbase (se 6 (by rfl) ⟨80715, by rfl⟩ : syracuseStep 3443861 = 161431) (by norm_num)
theorem B2295907 : Blo 2295435 2295907 := bstep (se 1 (by rfl) ⟨1721930, by rfl⟩ : syracuseStep 2295907 = 3443861) B3443861
theorem B2618141 : Blo 2295435 2618141 := bbase (se 3 (by rfl) ⟨490901, by rfl⟩ : syracuseStep 2618141 = 981803) (by norm_num)
theorem B6981709 : Blo 2295435 6981709 := bstep (se 3 (by rfl) ⟨1309070, by rfl⟩ : syracuseStep 6981709 = 2618141) B2618141
theorem B9308945 : Blo 2295435 9308945 := bstep (se 2 (by rfl) ⟨3490854, by rfl⟩ : syracuseStep 9308945 = 6981709) B6981709
theorem B24823853 : Blo 2295435 24823853 := bstep (se 3 (by rfl) ⟨4654472, by rfl⟩ : syracuseStep 24823853 = 9308945) B9308945
theorem B16549235 : Blo 2295435 16549235 := bstep (se 1 (by rfl) ⟨12411926, by rfl⟩ : syracuseStep 16549235 = 24823853) B24823853
theorem B11032823 : Blo 2295435 11032823 := bstep (se 1 (by rfl) ⟨8274617, by rfl⟩ : syracuseStep 11032823 = 16549235) B16549235
theorem B7355215 : Blo 2295435 7355215 := bstep (se 1 (by rfl) ⟨5516411, by rfl⟩ : syracuseStep 7355215 = 11032823) B11032823
theorem B9806953 : Blo 2295435 9806953 := bstep (se 2 (by rfl) ⟨3677607, by rfl⟩ : syracuseStep 9806953 = 7355215) B7355215
theorem B13075937 : Blo 2295435 13075937 := bstep (se 2 (by rfl) ⟨4903476, by rfl⟩ : syracuseStep 13075937 = 9806953) B9806953
theorem B8717291 : Blo 2295435 8717291 := bstep (se 1 (by rfl) ⟨6537968, by rfl⟩ : syracuseStep 8717291 = 13075937) B13075937
theorem B5811527 : Blo 2295435 5811527 := bstep (se 1 (by rfl) ⟨4358645, by rfl⟩ : syracuseStep 5811527 = 8717291) B8717291
theorem B3874351 : Blo 2295435 3874351 := bstep (se 1 (by rfl) ⟨2905763, by rfl⟩ : syracuseStep 3874351 = 5811527) B5811527
theorem B5165801 : Blo 2295435 5165801 := bstep (se 2 (by rfl) ⟨1937175, by rfl⟩ : syracuseStep 5165801 = 3874351) B3874351
theorem B3443867 : Blo 2295435 3443867 := bstep (se 1 (by rfl) ⟨2582900, by rfl⟩ : syracuseStep 3443867 = 5165801) B5165801
theorem B2295911 : Blo 2295435 2295911 := bstep (se 1 (by rfl) ⟨1721933, by rfl⟩ : syracuseStep 2295911 = 3443867) B3443867
theorem B2582905 : Blo 2295435 2582905 := bbase (se 2 (by rfl) ⟨968589, by rfl⟩ : syracuseStep 2582905 = 1937179) (by norm_num)
theorem B3443873 : Blo 2295435 3443873 := bstep (se 2 (by rfl) ⟨1291452, by rfl⟩ : syracuseStep 3443873 = 2582905) B2582905
theorem B2295915 : Blo 2295435 2295915 := bstep (se 1 (by rfl) ⟨1721936, by rfl⟩ : syracuseStep 2295915 = 3443873) B3443873
theorem B5236301 : Blo 2295435 5236301 := bbase (se 3 (by rfl) ⟨981806, by rfl⟩ : syracuseStep 5236301 = 1963613) (by norm_num)
theorem B3490867 : Blo 2295435 3490867 := bstep (se 1 (by rfl) ⟨2618150, by rfl⟩ : syracuseStep 3490867 = 5236301) B5236301
theorem B4654489 : Blo 2295435 4654489 := bstep (se 2 (by rfl) ⟨1745433, by rfl⟩ : syracuseStep 4654489 = 3490867) B3490867
theorem B6205985 : Blo 2295435 6205985 := bstep (se 2 (by rfl) ⟨2327244, by rfl⟩ : syracuseStep 6205985 = 4654489) B4654489
theorem B4137323 : Blo 2295435 4137323 := bstep (se 1 (by rfl) ⟨3102992, by rfl⟩ : syracuseStep 4137323 = 6205985) B6205985
theorem B11032861 : Blo 2295435 11032861 := bstep (se 3 (by rfl) ⟨2068661, by rfl⟩ : syracuseStep 11032861 = 4137323) B4137323
theorem B14710481 : Blo 2295435 14710481 := bstep (se 2 (by rfl) ⟨5516430, by rfl⟩ : syracuseStep 14710481 = 11032861) B11032861
theorem B9806987 : Blo 2295435 9806987 := bstep (se 1 (by rfl) ⟨7355240, by rfl⟩ : syracuseStep 9806987 = 14710481) B14710481
theorem B6537991 : Blo 2295435 6537991 := bstep (se 1 (by rfl) ⟨4903493, by rfl⟩ : syracuseStep 6537991 = 9806987) B9806987
theorem B8717321 : Blo 2295435 8717321 := bstep (se 2 (by rfl) ⟨3268995, by rfl⟩ : syracuseStep 8717321 = 6537991) B6537991
theorem B5811547 : Blo 2295435 5811547 := bstep (se 1 (by rfl) ⟨4358660, by rfl⟩ : syracuseStep 5811547 = 8717321) B8717321
theorem B7748729 : Blo 2295435 7748729 := bstep (se 2 (by rfl) ⟨2905773, by rfl⟩ : syracuseStep 7748729 = 5811547) B5811547
theorem B5165819 : Blo 2295435 5165819 := bstep (se 1 (by rfl) ⟨3874364, by rfl⟩ : syracuseStep 5165819 = 7748729) B7748729
theorem B3443879 : Blo 2295435 3443879 := bstep (se 1 (by rfl) ⟨2582909, by rfl⟩ : syracuseStep 3443879 = 5165819) B5165819
theorem B2295919 : Blo 2295435 2295919 := bstep (se 1 (by rfl) ⟨1721939, by rfl⟩ : syracuseStep 2295919 = 3443879) B3443879
theorem B3443885 : Blo 2295435 3443885 := bbase (se 3 (by rfl) ⟨645728, by rfl⟩ : syracuseStep 3443885 = 1291457) (by norm_num)
theorem B2295923 : Blo 2295435 2295923 := bstep (se 1 (by rfl) ⟨1721942, by rfl⟩ : syracuseStep 2295923 = 3443885) B3443885
theorem B5165837 : Blo 2295435 5165837 := bbase (se 3 (by rfl) ⟨968594, by rfl⟩ : syracuseStep 5165837 = 1937189) (by norm_num)
theorem B3443891 : Blo 2295435 3443891 := bstep (se 1 (by rfl) ⟨2582918, by rfl⟩ : syracuseStep 3443891 = 5165837) B5165837
theorem B2295927 : Blo 2295435 2295927 := bstep (se 1 (by rfl) ⟨1721945, by rfl⟩ : syracuseStep 2295927 = 3443891) B3443891
theorem B2905789 : Blo 2295435 2905789 := bbase (se 3 (by rfl) ⟨544835, by rfl⟩ : syracuseStep 2905789 = 1089671) (by norm_num)
theorem B3874385 : Blo 2295435 3874385 := bstep (se 2 (by rfl) ⟨1452894, by rfl⟩ : syracuseStep 3874385 = 2905789) B2905789
theorem B2582923 : Blo 2295435 2582923 := bstep (se 1 (by rfl) ⟨1937192, by rfl⟩ : syracuseStep 2582923 = 3874385) B3874385
theorem B3443897 : Blo 2295435 3443897 := bstep (se 2 (by rfl) ⟨1291461, by rfl⟩ : syracuseStep 3443897 = 2582923) B2582923
theorem B2295931 : Blo 2295435 2295931 := bstep (se 1 (by rfl) ⟨1721948, by rfl⟩ : syracuseStep 2295931 = 3443897) B3443897
theorem B27927125 : Blo 2295435 27927125 := bbase (se 8 (by rfl) ⟨163635, by rfl⟩ : syracuseStep 27927125 = 327271) (by norm_num)
theorem B18618083 : Blo 2295435 18618083 := bstep (se 1 (by rfl) ⟨13963562, by rfl⟩ : syracuseStep 18618083 = 27927125) B27927125
theorem B12412055 : Blo 2295435 12412055 := bstep (se 1 (by rfl) ⟨9309041, by rfl⟩ : syracuseStep 12412055 = 18618083) B18618083
theorem B8274703 : Blo 2295435 8274703 := bstep (se 1 (by rfl) ⟨6206027, by rfl⟩ : syracuseStep 8274703 = 12412055) B12412055
theorem B11032937 : Blo 2295435 11032937 := bstep (se 2 (by rfl) ⟨4137351, by rfl⟩ : syracuseStep 11032937 = 8274703) B8274703
theorem B7355291 : Blo 2295435 7355291 := bstep (se 1 (by rfl) ⟨5516468, by rfl⟩ : syracuseStep 7355291 = 11032937) B11032937
theorem B19614109 : Blo 2295435 19614109 := bstep (se 3 (by rfl) ⟨3677645, by rfl⟩ : syracuseStep 19614109 = 7355291) B7355291
theorem B26152145 : Blo 2295435 26152145 := bstep (se 2 (by rfl) ⟨9807054, by rfl⟩ : syracuseStep 26152145 = 19614109) B19614109
theorem B17434763 : Blo 2295435 17434763 := bstep (se 1 (by rfl) ⟨13076072, by rfl⟩ : syracuseStep 17434763 = 26152145) B26152145
theorem B11623175 : Blo 2295435 11623175 := bstep (se 1 (by rfl) ⟨8717381, by rfl⟩ : syracuseStep 11623175 = 17434763) B17434763
theorem B7748783 : Blo 2295435 7748783 := bstep (se 1 (by rfl) ⟨5811587, by rfl⟩ : syracuseStep 7748783 = 11623175) B11623175
theorem B5165855 : Blo 2295435 5165855 := bstep (se 1 (by rfl) ⟨3874391, by rfl⟩ : syracuseStep 5165855 = 7748783) B7748783
theorem B3443903 : Blo 2295435 3443903 := bstep (se 1 (by rfl) ⟨2582927, by rfl⟩ : syracuseStep 3443903 = 5165855) B5165855
theorem B2295935 : Blo 2295435 2295935 := bstep (se 1 (by rfl) ⟨1721951, by rfl⟩ : syracuseStep 2295935 = 3443903) B3443903
theorem B3443909 : Blo 2295435 3443909 := bbase (se 4 (by rfl) ⟨322866, by rfl⟩ : syracuseStep 3443909 = 645733) (by norm_num)
theorem B2295939 : Blo 2295435 2295939 := bstep (se 1 (by rfl) ⟨1721954, by rfl⟩ : syracuseStep 2295939 = 3443909) B3443909
theorem B3874405 : Blo 2295435 3874405 := bbase (se 4 (by rfl) ⟨363225, by rfl⟩ : syracuseStep 3874405 = 726451) (by norm_num)
theorem B5165873 : Blo 2295435 5165873 := bstep (se 2 (by rfl) ⟨1937202, by rfl⟩ : syracuseStep 5165873 = 3874405) B3874405
theorem B3443915 : Blo 2295435 3443915 := bstep (se 1 (by rfl) ⟨2582936, by rfl⟩ : syracuseStep 3443915 = 5165873) B5165873
theorem B2295943 : Blo 2295435 2295943 := bstep (se 1 (by rfl) ⟨1721957, by rfl⟩ : syracuseStep 2295943 = 3443915) B3443915
theorem B2582941 : Blo 2295435 2582941 := bbase (se 3 (by rfl) ⟨484301, by rfl⟩ : syracuseStep 2582941 = 968603) (by norm_num)
theorem B3443921 : Blo 2295435 3443921 := bstep (se 2 (by rfl) ⟨1291470, by rfl⟩ : syracuseStep 3443921 = 2582941) B2582941
theorem B2295947 : Blo 2295435 2295947 := bstep (se 1 (by rfl) ⟨1721960, by rfl⟩ : syracuseStep 2295947 = 3443921) B3443921
theorem B7748837 : Blo 2295435 7748837 := bbase (se 4 (by rfl) ⟨726453, by rfl⟩ : syracuseStep 7748837 = 1452907) (by norm_num)
theorem B5165891 : Blo 2295435 5165891 := bstep (se 1 (by rfl) ⟨3874418, by rfl⟩ : syracuseStep 5165891 = 7748837) B7748837
theorem B3443927 : Blo 2295435 3443927 := bstep (se 1 (by rfl) ⟨2582945, by rfl⟩ : syracuseStep 3443927 = 5165891) B5165891
theorem B2295951 : Blo 2295435 2295951 := bstep (se 1 (by rfl) ⟨1721963, by rfl⟩ : syracuseStep 2295951 = 3443927) B3443927
theorem B3443933 : Blo 2295435 3443933 := bbase (se 3 (by rfl) ⟨645737, by rfl⟩ : syracuseStep 3443933 = 1291475) (by norm_num)
theorem B2295955 : Blo 2295435 2295955 := bstep (se 1 (by rfl) ⟨1721966, by rfl⟩ : syracuseStep 2295955 = 3443933) B3443933
theorem B5165909 : Blo 2295435 5165909 := bbase (se 9 (by rfl) ⟨15134, by rfl⟩ : syracuseStep 5165909 = 30269) (by norm_num)
theorem B3443939 : Blo 2295435 3443939 := bstep (se 1 (by rfl) ⟨2582954, by rfl⟩ : syracuseStep 3443939 = 5165909) B5165909
theorem B2295959 : Blo 2295435 2295959 := bstep (se 1 (by rfl) ⟨1721969, by rfl⟩ : syracuseStep 2295959 = 3443939) B3443939
theorem B6538117 : Blo 2295435 6538117 := bbase (se 4 (by rfl) ⟨612948, by rfl⟩ : syracuseStep 6538117 = 1225897) (by norm_num)
theorem B8717489 : Blo 2295435 8717489 := bstep (se 2 (by rfl) ⟨3269058, by rfl⟩ : syracuseStep 8717489 = 6538117) B6538117
theorem B5811659 : Blo 2295435 5811659 := bstep (se 1 (by rfl) ⟨4358744, by rfl⟩ : syracuseStep 5811659 = 8717489) B8717489
theorem B3874439 : Blo 2295435 3874439 := bstep (se 1 (by rfl) ⟨2905829, by rfl⟩ : syracuseStep 3874439 = 5811659) B5811659
theorem B2582959 : Blo 2295435 2582959 := bstep (se 1 (by rfl) ⟨1937219, by rfl⟩ : syracuseStep 2582959 = 3874439) B3874439
theorem B3443945 : Blo 2295435 3443945 := bstep (se 2 (by rfl) ⟨1291479, by rfl⟩ : syracuseStep 3443945 = 2582959) B2582959
theorem B2295963 : Blo 2295435 2295963 := bstep (se 1 (by rfl) ⟨1721972, by rfl⟩ : syracuseStep 2295963 = 3443945) B3443945
theorem B4418221 : Blo 2295435 4418221 := bbase (se 3 (by rfl) ⟨828416, by rfl⟩ : syracuseStep 4418221 = 1656833) (by norm_num)
theorem B5890961 : Blo 2295435 5890961 := bstep (se 2 (by rfl) ⟨2209110, by rfl⟩ : syracuseStep 5890961 = 4418221) B4418221
theorem B3927307 : Blo 2295435 3927307 := bstep (se 1 (by rfl) ⟨2945480, by rfl⟩ : syracuseStep 3927307 = 5890961) B5890961
theorem B5236409 : Blo 2295435 5236409 := bstep (se 2 (by rfl) ⟨1963653, by rfl⟩ : syracuseStep 5236409 = 3927307) B3927307
theorem B3490939 : Blo 2295435 3490939 := bstep (se 1 (by rfl) ⟨2618204, by rfl⟩ : syracuseStep 3490939 = 5236409) B5236409
theorem B18618341 : Blo 2295435 18618341 := bstep (se 4 (by rfl) ⟨1745469, by rfl⟩ : syracuseStep 18618341 = 3490939) B3490939
theorem B49648909 : Blo 2295435 49648909 := bstep (se 3 (by rfl) ⟨9309170, by rfl⟩ : syracuseStep 49648909 = 18618341) B18618341
theorem B66198545 : Blo 2295435 66198545 := bstep (se 2 (by rfl) ⟨24824454, by rfl⟩ : syracuseStep 66198545 = 49648909) B49648909
theorem B44132363 : Blo 2295435 44132363 := bstep (se 1 (by rfl) ⟨33099272, by rfl⟩ : syracuseStep 44132363 = 66198545) B66198545
theorem B29421575 : Blo 2295435 29421575 := bstep (se 1 (by rfl) ⟨22066181, by rfl⟩ : syracuseStep 29421575 = 44132363) B44132363
theorem B19614383 : Blo 2295435 19614383 := bstep (se 1 (by rfl) ⟨14710787, by rfl⟩ : syracuseStep 19614383 = 29421575) B29421575
theorem B13076255 : Blo 2295435 13076255 := bstep (se 1 (by rfl) ⟨9807191, by rfl⟩ : syracuseStep 13076255 = 19614383) B19614383
theorem B8717503 : Blo 2295435 8717503 := bstep (se 1 (by rfl) ⟨6538127, by rfl⟩ : syracuseStep 8717503 = 13076255) B13076255
theorem B11623337 : Blo 2295435 11623337 := bstep (se 2 (by rfl) ⟨4358751, by rfl⟩ : syracuseStep 11623337 = 8717503) B8717503
theorem B7748891 : Blo 2295435 7748891 := bstep (se 1 (by rfl) ⟨5811668, by rfl⟩ : syracuseStep 7748891 = 11623337) B11623337
theorem B5165927 : Blo 2295435 5165927 := bstep (se 1 (by rfl) ⟨3874445, by rfl⟩ : syracuseStep 5165927 = 7748891) B7748891
theorem B3443951 : Blo 2295435 3443951 := bstep (se 1 (by rfl) ⟨2582963, by rfl⟩ : syracuseStep 3443951 = 5165927) B5165927
theorem B2295967 : Blo 2295435 2295967 := bstep (se 1 (by rfl) ⟨1721975, by rfl⟩ : syracuseStep 2295967 = 3443951) B3443951
theorem B3443957 : Blo 2295435 3443957 := bbase (se 5 (by rfl) ⟨161435, by rfl⟩ : syracuseStep 3443957 = 322871) (by norm_num)
theorem B2295971 : Blo 2295435 2295971 := bstep (se 1 (by rfl) ⟨1721978, by rfl⟩ : syracuseStep 2295971 = 3443957) B3443957
theorem B9309205 : Blo 2295435 9309205 := bbase (se 6 (by rfl) ⟨218184, by rfl⟩ : syracuseStep 9309205 = 436369) (by norm_num)
theorem B12412273 : Blo 2295435 12412273 := bstep (se 2 (by rfl) ⟨4654602, by rfl⟩ : syracuseStep 12412273 = 9309205) B9309205
theorem B16549697 : Blo 2295435 16549697 := bstep (se 2 (by rfl) ⟨6206136, by rfl⟩ : syracuseStep 16549697 = 12412273) B12412273
theorem B11033131 : Blo 2295435 11033131 := bstep (se 1 (by rfl) ⟨8274848, by rfl⟩ : syracuseStep 11033131 = 16549697) B16549697
theorem B14710841 : Blo 2295435 14710841 := bstep (se 2 (by rfl) ⟨5516565, by rfl⟩ : syracuseStep 14710841 = 11033131) B11033131
theorem B9807227 : Blo 2295435 9807227 := bstep (se 1 (by rfl) ⟨7355420, by rfl⟩ : syracuseStep 9807227 = 14710841) B14710841
theorem B6538151 : Blo 2295435 6538151 := bstep (se 1 (by rfl) ⟨4903613, by rfl⟩ : syracuseStep 6538151 = 9807227) B9807227
theorem B4358767 : Blo 2295435 4358767 := bstep (se 1 (by rfl) ⟨3269075, by rfl⟩ : syracuseStep 4358767 = 6538151) B6538151
theorem B5811689 : Blo 2295435 5811689 := bstep (se 2 (by rfl) ⟨2179383, by rfl⟩ : syracuseStep 5811689 = 4358767) B4358767
theorem B3874459 : Blo 2295435 3874459 := bstep (se 1 (by rfl) ⟨2905844, by rfl⟩ : syracuseStep 3874459 = 5811689) B5811689
theorem B5165945 : Blo 2295435 5165945 := bstep (se 2 (by rfl) ⟨1937229, by rfl⟩ : syracuseStep 5165945 = 3874459) B3874459
theorem B3443963 : Blo 2295435 3443963 := bstep (se 1 (by rfl) ⟨2582972, by rfl⟩ : syracuseStep 3443963 = 5165945) B5165945
theorem B2295975 : Blo 2295435 2295975 := bstep (se 1 (by rfl) ⟨1721981, by rfl⟩ : syracuseStep 2295975 = 3443963) B3443963
theorem B2582977 : Blo 2295435 2582977 := bbase (se 2 (by rfl) ⟨968616, by rfl⟩ : syracuseStep 2582977 = 1937233) (by norm_num)
theorem B3443969 : Blo 2295435 3443969 := bstep (se 2 (by rfl) ⟨1291488, by rfl⟩ : syracuseStep 3443969 = 2582977) B2582977
theorem B2295979 : Blo 2295435 2295979 := bstep (se 1 (by rfl) ⟨1721984, by rfl⟩ : syracuseStep 2295979 = 3443969) B3443969
theorem B5811709 : Blo 2295435 5811709 := bbase (se 3 (by rfl) ⟨1089695, by rfl⟩ : syracuseStep 5811709 = 2179391) (by norm_num)
theorem B7748945 : Blo 2295435 7748945 := bstep (se 2 (by rfl) ⟨2905854, by rfl⟩ : syracuseStep 7748945 = 5811709) B5811709
theorem B5165963 : Blo 2295435 5165963 := bstep (se 1 (by rfl) ⟨3874472, by rfl⟩ : syracuseStep 5165963 = 7748945) B7748945
theorem B3443975 : Blo 2295435 3443975 := bstep (se 1 (by rfl) ⟨2582981, by rfl⟩ : syracuseStep 3443975 = 5165963) B5165963
theorem B2295983 : Blo 2295435 2295983 := bstep (se 1 (by rfl) ⟨1721987, by rfl⟩ : syracuseStep 2295983 = 3443975) B3443975
theorem B3443981 : Blo 2295435 3443981 := bbase (se 3 (by rfl) ⟨645746, by rfl⟩ : syracuseStep 3443981 = 1291493) (by norm_num)
theorem B2295987 : Blo 2295435 2295987 := bstep (se 1 (by rfl) ⟨1721990, by rfl⟩ : syracuseStep 2295987 = 3443981) B3443981
theorem B5165981 : Blo 2295435 5165981 := bbase (se 3 (by rfl) ⟨968621, by rfl⟩ : syracuseStep 5165981 = 1937243) (by norm_num)
theorem B3443987 : Blo 2295435 3443987 := bstep (se 1 (by rfl) ⟨2582990, by rfl⟩ : syracuseStep 3443987 = 5165981) B5165981
theorem B2295991 : Blo 2295435 2295991 := bstep (se 1 (by rfl) ⟨1721993, by rfl⟩ : syracuseStep 2295991 = 3443987) B3443987
theorem B3874493 : Blo 2295435 3874493 := bbase (se 3 (by rfl) ⟨726467, by rfl⟩ : syracuseStep 3874493 = 1452935) (by norm_num)
theorem B2582995 : Blo 2295435 2582995 := bstep (se 1 (by rfl) ⟨1937246, by rfl⟩ : syracuseStep 2582995 = 3874493) B3874493
theorem B3443993 : Blo 2295435 3443993 := bstep (se 2 (by rfl) ⟨1291497, by rfl⟩ : syracuseStep 3443993 = 2582995) B2582995
theorem B2295995 : Blo 2295435 2295995 := bstep (se 1 (by rfl) ⟨1721996, by rfl⟩ : syracuseStep 2295995 = 3443993) B3443993
theorem B13076437 : Blo 2295435 13076437 := bbase (se 7 (by rfl) ⟨153239, by rfl⟩ : syracuseStep 13076437 = 306479) (by norm_num)
theorem B17435249 : Blo 2295435 17435249 := bstep (se 2 (by rfl) ⟨6538218, by rfl⟩ : syracuseStep 17435249 = 13076437) B13076437
theorem B11623499 : Blo 2295435 11623499 := bstep (se 1 (by rfl) ⟨8717624, by rfl⟩ : syracuseStep 11623499 = 17435249) B17435249
theorem B7748999 : Blo 2295435 7748999 := bstep (se 1 (by rfl) ⟨5811749, by rfl⟩ : syracuseStep 7748999 = 11623499) B11623499
theorem B5165999 : Blo 2295435 5165999 := bstep (se 1 (by rfl) ⟨3874499, by rfl⟩ : syracuseStep 5165999 = 7748999) B7748999
theorem B3443999 : Blo 2295435 3443999 := bstep (se 1 (by rfl) ⟨2582999, by rfl⟩ : syracuseStep 3443999 = 5165999) B5165999
theorem B2295999 : Blo 2295435 2295999 := bstep (se 1 (by rfl) ⟨1721999, by rfl⟩ : syracuseStep 2295999 = 3443999) B3443999
theorem B3444005 : Blo 2295435 3444005 := bbase (se 4 (by rfl) ⟨322875, by rfl⟩ : syracuseStep 3444005 = 645751) (by norm_num)
theorem B2296003 : Blo 2295435 2296003 := bstep (se 1 (by rfl) ⟨1722002, by rfl⟩ : syracuseStep 2296003 = 3444005) B3444005
theorem B2905885 : Blo 2295435 2905885 := bbase (se 3 (by rfl) ⟨544853, by rfl⟩ : syracuseStep 2905885 = 1089707) (by norm_num)
theorem B3874513 : Blo 2295435 3874513 := bstep (se 2 (by rfl) ⟨1452942, by rfl⟩ : syracuseStep 3874513 = 2905885) B2905885
theorem B5166017 : Blo 2295435 5166017 := bstep (se 2 (by rfl) ⟨1937256, by rfl⟩ : syracuseStep 5166017 = 3874513) B3874513
theorem B3444011 : Blo 2295435 3444011 := bstep (se 1 (by rfl) ⟨2583008, by rfl⟩ : syracuseStep 3444011 = 5166017) B5166017
theorem B2296007 : Blo 2295435 2296007 := bstep (se 1 (by rfl) ⟨1722005, by rfl⟩ : syracuseStep 2296007 = 3444011) B3444011
theorem B2583013 : Blo 2295435 2583013 := bbase (se 4 (by rfl) ⟨242157, by rfl⟩ : syracuseStep 2583013 = 484315) (by norm_num)
theorem B3444017 : Blo 2295435 3444017 := bstep (se 2 (by rfl) ⟨1291506, by rfl⟩ : syracuseStep 3444017 = 2583013) B2583013
theorem B2296011 : Blo 2295435 2296011 := bstep (se 1 (by rfl) ⟨1722008, by rfl⟩ : syracuseStep 2296011 = 3444017) B3444017
theorem B4654685 : Blo 2295435 4654685 := bbase (se 3 (by rfl) ⟨872753, by rfl⟩ : syracuseStep 4654685 = 1745507) (by norm_num)
theorem B3103123 : Blo 2295435 3103123 := bstep (se 1 (by rfl) ⟨2327342, by rfl⟩ : syracuseStep 3103123 = 4654685) B4654685
theorem B4137497 : Blo 2295435 4137497 := bstep (se 2 (by rfl) ⟨1551561, by rfl⟩ : syracuseStep 4137497 = 3103123) B3103123
theorem B2758331 : Blo 2295435 2758331 := bstep (se 1 (by rfl) ⟨2068748, by rfl⟩ : syracuseStep 2758331 = 4137497) B4137497
theorem B7355549 : Blo 2295435 7355549 := bstep (se 3 (by rfl) ⟨1379165, by rfl⟩ : syracuseStep 7355549 = 2758331) B2758331
theorem B4903699 : Blo 2295435 4903699 := bstep (se 1 (by rfl) ⟨3677774, by rfl⟩ : syracuseStep 4903699 = 7355549) B7355549
theorem B6538265 : Blo 2295435 6538265 := bstep (se 2 (by rfl) ⟨2451849, by rfl⟩ : syracuseStep 6538265 = 4903699) B4903699
theorem B4358843 : Blo 2295435 4358843 := bstep (se 1 (by rfl) ⟨3269132, by rfl⟩ : syracuseStep 4358843 = 6538265) B6538265
theorem B2905895 : Blo 2295435 2905895 := bstep (se 1 (by rfl) ⟨2179421, by rfl⟩ : syracuseStep 2905895 = 4358843) B4358843
theorem B7749053 : Blo 2295435 7749053 := bstep (se 3 (by rfl) ⟨1452947, by rfl⟩ : syracuseStep 7749053 = 2905895) B2905895
theorem B5166035 : Blo 2295435 5166035 := bstep (se 1 (by rfl) ⟨3874526, by rfl⟩ : syracuseStep 5166035 = 7749053) B7749053
theorem B3444023 : Blo 2295435 3444023 := bstep (se 1 (by rfl) ⟨2583017, by rfl⟩ : syracuseStep 3444023 = 5166035) B5166035
theorem B2296015 : Blo 2295435 2296015 := bstep (se 1 (by rfl) ⟨1722011, by rfl⟩ : syracuseStep 2296015 = 3444023) B3444023
theorem B3444029 : Blo 2295435 3444029 := bbase (se 3 (by rfl) ⟨645755, by rfl⟩ : syracuseStep 3444029 = 1291511) (by norm_num)
theorem B2296019 : Blo 2295435 2296019 := bstep (se 1 (by rfl) ⟨1722014, by rfl⟩ : syracuseStep 2296019 = 3444029) B3444029
theorem B5166053 : Blo 2295435 5166053 := bbase (se 4 (by rfl) ⟨484317, by rfl⟩ : syracuseStep 5166053 = 968635) (by norm_num)
theorem B3444035 : Blo 2295435 3444035 := bstep (se 1 (by rfl) ⟨2583026, by rfl⟩ : syracuseStep 3444035 = 5166053) B5166053
theorem B2296023 : Blo 2295435 2296023 := bstep (se 1 (by rfl) ⟨1722017, by rfl⟩ : syracuseStep 2296023 = 3444035) B3444035
theorem B5811821 : Blo 2295435 5811821 := bbase (se 3 (by rfl) ⟨1089716, by rfl⟩ : syracuseStep 5811821 = 2179433) (by norm_num)
theorem B3874547 : Blo 2295435 3874547 := bstep (se 1 (by rfl) ⟨2905910, by rfl⟩ : syracuseStep 3874547 = 5811821) B5811821
theorem B2583031 : Blo 2295435 2583031 := bstep (se 1 (by rfl) ⟨1937273, by rfl⟩ : syracuseStep 2583031 = 3874547) B3874547
theorem B3444041 : Blo 2295435 3444041 := bstep (se 2 (by rfl) ⟨1291515, by rfl⟩ : syracuseStep 3444041 = 2583031) B2583031
theorem B2296027 : Blo 2295435 2296027 := bstep (se 1 (by rfl) ⟨1722020, by rfl⟩ : syracuseStep 2296027 = 3444041) B3444041
theorem B4903733 : Blo 2295435 4903733 := bbase (se 5 (by rfl) ⟨229862, by rfl⟩ : syracuseStep 4903733 = 459725) (by norm_num)
theorem B3269155 : Blo 2295435 3269155 := bstep (se 1 (by rfl) ⟨2451866, by rfl⟩ : syracuseStep 3269155 = 4903733) B4903733
theorem B4358873 : Blo 2295435 4358873 := bstep (se 2 (by rfl) ⟨1634577, by rfl⟩ : syracuseStep 4358873 = 3269155) B3269155
theorem B11623661 : Blo 2295435 11623661 := bstep (se 3 (by rfl) ⟨2179436, by rfl⟩ : syracuseStep 11623661 = 4358873) B4358873
theorem B7749107 : Blo 2295435 7749107 := bstep (se 1 (by rfl) ⟨5811830, by rfl⟩ : syracuseStep 7749107 = 11623661) B11623661
theorem B5166071 : Blo 2295435 5166071 := bstep (se 1 (by rfl) ⟨3874553, by rfl⟩ : syracuseStep 5166071 = 7749107) B7749107
theorem B3444047 : Blo 2295435 3444047 := bstep (se 1 (by rfl) ⟨2583035, by rfl⟩ : syracuseStep 3444047 = 5166071) B5166071
theorem B2296031 : Blo 2295435 2296031 := bstep (se 1 (by rfl) ⟨1722023, by rfl⟩ : syracuseStep 2296031 = 3444047) B3444047
theorem B3444053 : Blo 2295435 3444053 := bbase (se 11 (by rfl) ⟨2522, by rfl⟩ : syracuseStep 3444053 = 5045) (by norm_num)
theorem B2296035 : Blo 2295435 2296035 := bstep (se 1 (by rfl) ⟨1722026, by rfl⟩ : syracuseStep 2296035 = 3444053) B3444053
theorem B3677813 : Blo 2295435 3677813 := bbase (se 5 (by rfl) ⟨172397, by rfl⟩ : syracuseStep 3677813 = 344795) (by norm_num)
theorem B2451875 : Blo 2295435 2451875 := bstep (se 1 (by rfl) ⟨1838906, by rfl⟩ : syracuseStep 2451875 = 3677813) B3677813
theorem B6538333 : Blo 2295435 6538333 := bstep (se 3 (by rfl) ⟨1225937, by rfl⟩ : syracuseStep 6538333 = 2451875) B2451875
theorem B8717777 : Blo 2295435 8717777 := bstep (se 2 (by rfl) ⟨3269166, by rfl⟩ : syracuseStep 8717777 = 6538333) B6538333
theorem B5811851 : Blo 2295435 5811851 := bstep (se 1 (by rfl) ⟨4358888, by rfl⟩ : syracuseStep 5811851 = 8717777) B8717777
theorem B3874567 : Blo 2295435 3874567 := bstep (se 1 (by rfl) ⟨2905925, by rfl⟩ : syracuseStep 3874567 = 5811851) B5811851
theorem B5166089 : Blo 2295435 5166089 := bstep (se 2 (by rfl) ⟨1937283, by rfl⟩ : syracuseStep 5166089 = 3874567) B3874567
theorem B3444059 : Blo 2295435 3444059 := bstep (se 1 (by rfl) ⟨2583044, by rfl⟩ : syracuseStep 3444059 = 5166089) B5166089
theorem B2296039 : Blo 2295435 2296039 := bstep (se 1 (by rfl) ⟨1722029, by rfl⟩ : syracuseStep 2296039 = 3444059) B3444059
theorem B2583049 : Blo 2295435 2583049 := bbase (se 2 (by rfl) ⟨968643, by rfl⟩ : syracuseStep 2583049 = 1937287) (by norm_num)
theorem B3444065 : Blo 2295435 3444065 := bstep (se 2 (by rfl) ⟨1291524, by rfl⟩ : syracuseStep 3444065 = 2583049) B2583049
theorem B2296043 : Blo 2295435 2296043 := bstep (se 1 (by rfl) ⟨1722032, by rfl⟩ : syracuseStep 2296043 = 3444065) B3444065
theorem B2519245 : Blo 2295435 2519245 := bbase (se 3 (by rfl) ⟨472358, by rfl⟩ : syracuseStep 2519245 = 944717) (by norm_num)
theorem B3358993 : Blo 2295435 3358993 := bstep (se 2 (by rfl) ⟨1259622, by rfl⟩ : syracuseStep 3358993 = 2519245) B2519245
theorem B4478657 : Blo 2295435 4478657 := bstep (se 2 (by rfl) ⟨1679496, by rfl⟩ : syracuseStep 4478657 = 3358993) B3358993
theorem B11943085 : Blo 2295435 11943085 := bstep (se 3 (by rfl) ⟨2239328, by rfl⟩ : syracuseStep 11943085 = 4478657) B4478657
theorem B15924113 : Blo 2295435 15924113 := bstep (se 2 (by rfl) ⟨5971542, by rfl⟩ : syracuseStep 15924113 = 11943085) B11943085
theorem B10616075 : Blo 2295435 10616075 := bstep (se 1 (by rfl) ⟨7962056, by rfl⟩ : syracuseStep 10616075 = 15924113) B15924113
theorem B7077383 : Blo 2295435 7077383 := bstep (se 1 (by rfl) ⟨5308037, by rfl⟩ : syracuseStep 7077383 = 10616075) B10616075
theorem B4718255 : Blo 2295435 4718255 := bstep (se 1 (by rfl) ⟨3538691, by rfl⟩ : syracuseStep 4718255 = 7077383) B7077383
theorem B12582013 : Blo 2295435 12582013 := bstep (se 3 (by rfl) ⟨2359127, by rfl⟩ : syracuseStep 12582013 = 4718255) B4718255
theorem B16776017 : Blo 2295435 16776017 := bstep (se 2 (by rfl) ⟨6291006, by rfl⟩ : syracuseStep 16776017 = 12582013) B12582013
theorem B11184011 : Blo 2295435 11184011 := bstep (se 1 (by rfl) ⟨8388008, by rfl⟩ : syracuseStep 11184011 = 16776017) B16776017
theorem B7456007 : Blo 2295435 7456007 := bstep (se 1 (by rfl) ⟨5592005, by rfl⟩ : syracuseStep 7456007 = 11184011) B11184011
theorem B19882685 : Blo 2295435 19882685 := bstep (se 3 (by rfl) ⟨3728003, by rfl⟩ : syracuseStep 19882685 = 7456007) B7456007
theorem B13255123 : Blo 2295435 13255123 := bstep (se 1 (by rfl) ⟨9941342, by rfl⟩ : syracuseStep 13255123 = 19882685) B19882685
theorem B17673497 : Blo 2295435 17673497 := bstep (se 2 (by rfl) ⟨6627561, by rfl⟩ : syracuseStep 17673497 = 13255123) B13255123
theorem B11782331 : Blo 2295435 11782331 := bstep (se 1 (by rfl) ⟨8836748, by rfl⟩ : syracuseStep 11782331 = 17673497) B17673497
theorem B7854887 : Blo 2295435 7854887 := bstep (se 1 (by rfl) ⟨5891165, by rfl⟩ : syracuseStep 7854887 = 11782331) B11782331
theorem B20946365 : Blo 2295435 20946365 := bstep (se 3 (by rfl) ⟨3927443, by rfl⟩ : syracuseStep 20946365 = 7854887) B7854887
theorem B13964243 : Blo 2295435 13964243 := bstep (se 1 (by rfl) ⟨10473182, by rfl⟩ : syracuseStep 13964243 = 20946365) B20946365
theorem B37237981 : Blo 2295435 37237981 := bstep (se 3 (by rfl) ⟨6982121, by rfl⟩ : syracuseStep 37237981 = 13964243) B13964243
theorem B49650641 : Blo 2295435 49650641 := bstep (se 2 (by rfl) ⟨18618990, by rfl⟩ : syracuseStep 49650641 = 37237981) B37237981
theorem B33100427 : Blo 2295435 33100427 := bstep (se 1 (by rfl) ⟨24825320, by rfl⟩ : syracuseStep 33100427 = 49650641) B49650641
theorem B22066951 : Blo 2295435 22066951 := bstep (se 1 (by rfl) ⟨16550213, by rfl⟩ : syracuseStep 22066951 = 33100427) B33100427
theorem B29422601 : Blo 2295435 29422601 := bstep (se 2 (by rfl) ⟨11033475, by rfl⟩ : syracuseStep 29422601 = 22066951) B22066951
theorem B19615067 : Blo 2295435 19615067 := bstep (se 1 (by rfl) ⟨14711300, by rfl⟩ : syracuseStep 19615067 = 29422601) B29422601
theorem B13076711 : Blo 2295435 13076711 := bstep (se 1 (by rfl) ⟨9807533, by rfl⟩ : syracuseStep 13076711 = 19615067) B19615067
theorem B8717807 : Blo 2295435 8717807 := bstep (se 1 (by rfl) ⟨6538355, by rfl⟩ : syracuseStep 8717807 = 13076711) B13076711
theorem B5811871 : Blo 2295435 5811871 := bstep (se 1 (by rfl) ⟨4358903, by rfl⟩ : syracuseStep 5811871 = 8717807) B8717807
theorem B7749161 : Blo 2295435 7749161 := bstep (se 2 (by rfl) ⟨2905935, by rfl⟩ : syracuseStep 7749161 = 5811871) B5811871
theorem B5166107 : Blo 2295435 5166107 := bstep (se 1 (by rfl) ⟨3874580, by rfl⟩ : syracuseStep 5166107 = 7749161) B7749161
theorem B3444071 : Blo 2295435 3444071 := bstep (se 1 (by rfl) ⟨2583053, by rfl⟩ : syracuseStep 3444071 = 5166107) B5166107
theorem B2296047 : Blo 2295435 2296047 := bstep (se 1 (by rfl) ⟨1722035, by rfl⟩ : syracuseStep 2296047 = 3444071) B3444071
theorem B3444077 : Blo 2295435 3444077 := bbase (se 3 (by rfl) ⟨645764, by rfl⟩ : syracuseStep 3444077 = 1291529) (by norm_num)
theorem B2296051 : Blo 2295435 2296051 := bstep (se 1 (by rfl) ⟨1722038, by rfl⟩ : syracuseStep 2296051 = 3444077) B3444077
theorem B5166125 : Blo 2295435 5166125 := bbase (se 3 (by rfl) ⟨968648, by rfl⟩ : syracuseStep 5166125 = 1937297) (by norm_num)
theorem B3444083 : Blo 2295435 3444083 := bstep (se 1 (by rfl) ⟨2583062, by rfl⟩ : syracuseStep 3444083 = 5166125) B5166125
theorem B2296055 : Blo 2295435 2296055 := bstep (se 1 (by rfl) ⟨1722041, by rfl⟩ : syracuseStep 2296055 = 3444083) B3444083
theorem B14711381 : Blo 2295435 14711381 := bbase (se 8 (by rfl) ⟨86199, by rfl⟩ : syracuseStep 14711381 = 172399) (by norm_num)
theorem B9807587 : Blo 2295435 9807587 := bstep (se 1 (by rfl) ⟨7355690, by rfl⟩ : syracuseStep 9807587 = 14711381) B14711381
theorem B6538391 : Blo 2295435 6538391 := bstep (se 1 (by rfl) ⟨4903793, by rfl⟩ : syracuseStep 6538391 = 9807587) B9807587
theorem B4358927 : Blo 2295435 4358927 := bstep (se 1 (by rfl) ⟨3269195, by rfl⟩ : syracuseStep 4358927 = 6538391) B6538391
theorem B2905951 : Blo 2295435 2905951 := bstep (se 1 (by rfl) ⟨2179463, by rfl⟩ : syracuseStep 2905951 = 4358927) B4358927
theorem B3874601 : Blo 2295435 3874601 := bstep (se 2 (by rfl) ⟨1452975, by rfl⟩ : syracuseStep 3874601 = 2905951) B2905951
theorem B2583067 : Blo 2295435 2583067 := bstep (se 1 (by rfl) ⟨1937300, by rfl⟩ : syracuseStep 2583067 = 3874601) B3874601
theorem B3444089 : Blo 2295435 3444089 := bstep (se 2 (by rfl) ⟨1291533, by rfl⟩ : syracuseStep 3444089 = 2583067) B2583067
theorem B2296059 : Blo 2295435 2296059 := bstep (se 1 (by rfl) ⟨1722044, by rfl⟩ : syracuseStep 2296059 = 3444089) B3444089
theorem B7355701 : Blo 2295435 7355701 := bbase (se 5 (by rfl) ⟨344798, by rfl⟩ : syracuseStep 7355701 = 689597) (by norm_num)
theorem B39230405 : Blo 2295435 39230405 := bstep (se 4 (by rfl) ⟨3677850, by rfl⟩ : syracuseStep 39230405 = 7355701) B7355701
theorem B26153603 : Blo 2295435 26153603 := bstep (se 1 (by rfl) ⟨19615202, by rfl⟩ : syracuseStep 26153603 = 39230405) B39230405
theorem B17435735 : Blo 2295435 17435735 := bstep (se 1 (by rfl) ⟨13076801, by rfl⟩ : syracuseStep 17435735 = 26153603) B26153603
theorem B11623823 : Blo 2295435 11623823 := bstep (se 1 (by rfl) ⟨8717867, by rfl⟩ : syracuseStep 11623823 = 17435735) B17435735
theorem B7749215 : Blo 2295435 7749215 := bstep (se 1 (by rfl) ⟨5811911, by rfl⟩ : syracuseStep 7749215 = 11623823) B11623823
theorem B5166143 : Blo 2295435 5166143 := bstep (se 1 (by rfl) ⟨3874607, by rfl⟩ : syracuseStep 5166143 = 7749215) B7749215
theorem B3444095 : Blo 2295435 3444095 := bstep (se 1 (by rfl) ⟨2583071, by rfl⟩ : syracuseStep 3444095 = 5166143) B5166143
theorem B2296063 : Blo 2295435 2296063 := bstep (se 1 (by rfl) ⟨1722047, by rfl⟩ : syracuseStep 2296063 = 3444095) B3444095
theorem B3444101 : Blo 2295435 3444101 := bbase (se 4 (by rfl) ⟨322884, by rfl⟩ : syracuseStep 3444101 = 645769) (by norm_num)
theorem B2296067 : Blo 2295435 2296067 := bstep (se 1 (by rfl) ⟨1722050, by rfl⟩ : syracuseStep 2296067 = 3444101) B3444101
theorem B3874621 : Blo 2295435 3874621 := bbase (se 3 (by rfl) ⟨726491, by rfl⟩ : syracuseStep 3874621 = 1452983) (by norm_num)
theorem B5166161 : Blo 2295435 5166161 := bstep (se 2 (by rfl) ⟨1937310, by rfl⟩ : syracuseStep 5166161 = 3874621) B3874621
theorem B3444107 : Blo 2295435 3444107 := bstep (se 1 (by rfl) ⟨2583080, by rfl⟩ : syracuseStep 3444107 = 5166161) B5166161
theorem B2296071 : Blo 2295435 2296071 := bstep (se 1 (by rfl) ⟨1722053, by rfl⟩ : syracuseStep 2296071 = 3444107) B3444107
theorem B2583085 : Blo 2295435 2583085 := bbase (se 3 (by rfl) ⟨484328, by rfl⟩ : syracuseStep 2583085 = 968657) (by norm_num)
theorem B3444113 : Blo 2295435 3444113 := bstep (se 2 (by rfl) ⟨1291542, by rfl⟩ : syracuseStep 3444113 = 2583085) B2583085
theorem B2296075 : Blo 2295435 2296075 := bstep (se 1 (by rfl) ⟨1722056, by rfl⟩ : syracuseStep 2296075 = 3444113) B3444113
theorem B7749269 : Blo 2295435 7749269 := bbase (se 6 (by rfl) ⟨181623, by rfl⟩ : syracuseStep 7749269 = 363247) (by norm_num)
theorem B5166179 : Blo 2295435 5166179 := bstep (se 1 (by rfl) ⟨3874634, by rfl⟩ : syracuseStep 5166179 = 7749269) B7749269
theorem B3444119 : Blo 2295435 3444119 := bstep (se 1 (by rfl) ⟨2583089, by rfl⟩ : syracuseStep 3444119 = 5166179) B5166179
theorem B2296079 : Blo 2295435 2296079 := bstep (se 1 (by rfl) ⟨1722059, by rfl⟩ : syracuseStep 2296079 = 3444119) B3444119
theorem B3444125 : Blo 2295435 3444125 := bbase (se 3 (by rfl) ⟨645773, by rfl⟩ : syracuseStep 3444125 = 1291547) (by norm_num)
theorem B2296083 : Blo 2295435 2296083 := bstep (se 1 (by rfl) ⟨1722062, by rfl⟩ : syracuseStep 2296083 = 3444125) B3444125
theorem B5166197 : Blo 2295435 5166197 := bbase (se 5 (by rfl) ⟨242165, by rfl⟩ : syracuseStep 5166197 = 484331) (by norm_num)
theorem B3444131 : Blo 2295435 3444131 := bstep (se 1 (by rfl) ⟨2583098, by rfl⟩ : syracuseStep 3444131 = 5166197) B5166197
theorem B2296087 : Blo 2295435 2296087 := bstep (se 1 (by rfl) ⟨1722065, by rfl⟩ : syracuseStep 2296087 = 3444131) B3444131
theorem B19615445 : Blo 2295435 19615445 := bbase (se 7 (by rfl) ⟨229868, by rfl⟩ : syracuseStep 19615445 = 459737) (by norm_num)
theorem B13076963 : Blo 2295435 13076963 := bstep (se 1 (by rfl) ⟨9807722, by rfl⟩ : syracuseStep 13076963 = 19615445) B19615445
theorem B8717975 : Blo 2295435 8717975 := bstep (se 1 (by rfl) ⟨6538481, by rfl⟩ : syracuseStep 8717975 = 13076963) B13076963
theorem B5811983 : Blo 2295435 5811983 := bstep (se 1 (by rfl) ⟨4358987, by rfl⟩ : syracuseStep 5811983 = 8717975) B8717975
theorem B3874655 : Blo 2295435 3874655 := bstep (se 1 (by rfl) ⟨2905991, by rfl⟩ : syracuseStep 3874655 = 5811983) B5811983
theorem B2583103 : Blo 2295435 2583103 := bstep (se 1 (by rfl) ⟨1937327, by rfl⟩ : syracuseStep 2583103 = 3874655) B3874655
theorem B3444137 : Blo 2295435 3444137 := bstep (se 2 (by rfl) ⟨1291551, by rfl⟩ : syracuseStep 3444137 = 2583103) B2583103
theorem B2296091 : Blo 2295435 2296091 := bstep (se 1 (by rfl) ⟨1722068, by rfl⟩ : syracuseStep 2296091 = 3444137) B3444137
theorem B8717989 : Blo 2295435 8717989 := bbase (se 4 (by rfl) ⟨817311, by rfl⟩ : syracuseStep 8717989 = 1634623) (by norm_num)
theorem B11623985 : Blo 2295435 11623985 := bstep (se 2 (by rfl) ⟨4358994, by rfl⟩ : syracuseStep 11623985 = 8717989) B8717989
theorem B7749323 : Blo 2295435 7749323 := bstep (se 1 (by rfl) ⟨5811992, by rfl⟩ : syracuseStep 7749323 = 11623985) B11623985
theorem B5166215 : Blo 2295435 5166215 := bstep (se 1 (by rfl) ⟨3874661, by rfl⟩ : syracuseStep 5166215 = 7749323) B7749323
theorem B3444143 : Blo 2295435 3444143 := bstep (se 1 (by rfl) ⟨2583107, by rfl⟩ : syracuseStep 3444143 = 5166215) B5166215
theorem B2296095 : Blo 2295435 2296095 := bstep (se 1 (by rfl) ⟨1722071, by rfl⟩ : syracuseStep 2296095 = 3444143) B3444143
theorem B3444149 : Blo 2295435 3444149 := bbase (se 5 (by rfl) ⟨161444, by rfl⟩ : syracuseStep 3444149 = 322889) (by norm_num)
theorem B2296099 : Blo 2295435 2296099 := bstep (se 1 (by rfl) ⟨1722074, by rfl⟩ : syracuseStep 2296099 = 3444149) B3444149
theorem B5812013 : Blo 2295435 5812013 := bbase (se 3 (by rfl) ⟨1089752, by rfl⟩ : syracuseStep 5812013 = 2179505) (by norm_num)
theorem B3874675 : Blo 2295435 3874675 := bstep (se 1 (by rfl) ⟨2906006, by rfl⟩ : syracuseStep 3874675 = 5812013) B5812013
theorem B5166233 : Blo 2295435 5166233 := bstep (se 2 (by rfl) ⟨1937337, by rfl⟩ : syracuseStep 5166233 = 3874675) B3874675
theorem B3444155 : Blo 2295435 3444155 := bstep (se 1 (by rfl) ⟨2583116, by rfl⟩ : syracuseStep 3444155 = 5166233) B5166233
theorem B2296103 : Blo 2295435 2296103 := bstep (se 1 (by rfl) ⟨1722077, by rfl⟩ : syracuseStep 2296103 = 3444155) B3444155
theorem B2583121 : Blo 2295435 2583121 := bbase (se 2 (by rfl) ⟨968670, by rfl⟩ : syracuseStep 2583121 = 1937341) (by norm_num)
theorem B3444161 : Blo 2295435 3444161 := bstep (se 2 (by rfl) ⟨1291560, by rfl⟩ : syracuseStep 3444161 = 2583121) B2583121
theorem B2296107 : Blo 2295435 2296107 := bstep (se 1 (by rfl) ⟨1722080, by rfl⟩ : syracuseStep 2296107 = 3444161) B3444161
theorem B3269269 : Blo 2295435 3269269 := bbase (se 6 (by rfl) ⟨76623, by rfl⟩ : syracuseStep 3269269 = 153247) (by norm_num)
theorem B4359025 : Blo 2295435 4359025 := bstep (se 2 (by rfl) ⟨1634634, by rfl⟩ : syracuseStep 4359025 = 3269269) B3269269
theorem B5812033 : Blo 2295435 5812033 := bstep (se 2 (by rfl) ⟨2179512, by rfl⟩ : syracuseStep 5812033 = 4359025) B4359025
theorem B7749377 : Blo 2295435 7749377 := bstep (se 2 (by rfl) ⟨2906016, by rfl⟩ : syracuseStep 7749377 = 5812033) B5812033
theorem B5166251 : Blo 2295435 5166251 := bstep (se 1 (by rfl) ⟨3874688, by rfl⟩ : syracuseStep 5166251 = 7749377) B7749377
theorem B3444167 : Blo 2295435 3444167 := bstep (se 1 (by rfl) ⟨2583125, by rfl⟩ : syracuseStep 3444167 = 5166251) B5166251
theorem B2296111 : Blo 2295435 2296111 := bstep (se 1 (by rfl) ⟨1722083, by rfl⟩ : syracuseStep 2296111 = 3444167) B3444167
theorem B3444173 : Blo 2295435 3444173 := bbase (se 3 (by rfl) ⟨645782, by rfl⟩ : syracuseStep 3444173 = 1291565) (by norm_num)
theorem B2296115 : Blo 2295435 2296115 := bstep (se 1 (by rfl) ⟨1722086, by rfl⟩ : syracuseStep 2296115 = 3444173) B3444173
theorem B5166269 : Blo 2295435 5166269 := bbase (se 3 (by rfl) ⟨968675, by rfl⟩ : syracuseStep 5166269 = 1937351) (by norm_num)
theorem B3444179 : Blo 2295435 3444179 := bstep (se 1 (by rfl) ⟨2583134, by rfl⟩ : syracuseStep 3444179 = 5166269) B5166269
theorem B2296119 : Blo 2295435 2296119 := bstep (se 1 (by rfl) ⟨1722089, by rfl⟩ : syracuseStep 2296119 = 3444179) B3444179
theorem B3874709 : Blo 2295435 3874709 := bbase (se 6 (by rfl) ⟨90813, by rfl⟩ : syracuseStep 3874709 = 181627) (by norm_num)
theorem B2583139 : Blo 2295435 2583139 := bstep (se 1 (by rfl) ⟨1937354, by rfl⟩ : syracuseStep 2583139 = 3874709) B3874709
theorem B3444185 : Blo 2295435 3444185 := bstep (se 2 (by rfl) ⟨1291569, by rfl⟩ : syracuseStep 3444185 = 2583139) B2583139
theorem B2296123 : Blo 2295435 2296123 := bstep (se 1 (by rfl) ⟨1722092, by rfl⟩ : syracuseStep 2296123 = 3444185) B3444185
theorem B2758465 : Blo 2295435 2758465 := bbase (se 2 (by rfl) ⟨1034424, by rfl⟩ : syracuseStep 2758465 = 2068849) (by norm_num)
theorem B14711813 : Blo 2295435 14711813 := bstep (se 4 (by rfl) ⟨1379232, by rfl⟩ : syracuseStep 14711813 = 2758465) B2758465
theorem B9807875 : Blo 2295435 9807875 := bstep (se 1 (by rfl) ⟨7355906, by rfl⟩ : syracuseStep 9807875 = 14711813) B14711813
theorem B6538583 : Blo 2295435 6538583 := bstep (se 1 (by rfl) ⟨4903937, by rfl⟩ : syracuseStep 6538583 = 9807875) B9807875
theorem B17436221 : Blo 2295435 17436221 := bstep (se 3 (by rfl) ⟨3269291, by rfl⟩ : syracuseStep 17436221 = 6538583) B6538583
theorem B11624147 : Blo 2295435 11624147 := bstep (se 1 (by rfl) ⟨8718110, by rfl⟩ : syracuseStep 11624147 = 17436221) B17436221
theorem B7749431 : Blo 2295435 7749431 := bstep (se 1 (by rfl) ⟨5812073, by rfl⟩ : syracuseStep 7749431 = 11624147) B11624147
theorem B5166287 : Blo 2295435 5166287 := bstep (se 1 (by rfl) ⟨3874715, by rfl⟩ : syracuseStep 5166287 = 7749431) B7749431
theorem B3444191 : Blo 2295435 3444191 := bstep (se 1 (by rfl) ⟨2583143, by rfl⟩ : syracuseStep 3444191 = 5166287) B5166287
theorem B2296127 : Blo 2295435 2296127 := bstep (se 1 (by rfl) ⟨1722095, by rfl⟩ : syracuseStep 2296127 = 3444191) B3444191
theorem B3444197 : Blo 2295435 3444197 := bbase (se 4 (by rfl) ⟨322893, by rfl⟩ : syracuseStep 3444197 = 645787) (by norm_num)
theorem B2296131 : Blo 2295435 2296131 := bstep (se 1 (by rfl) ⟨1722098, by rfl⟩ : syracuseStep 2296131 = 3444197) B3444197
theorem B3313909 : Blo 2295435 3313909 := bbase (se 5 (by rfl) ⟨155339, by rfl⟩ : syracuseStep 3313909 = 310679) (by norm_num)
theorem B4418545 : Blo 2295435 4418545 := bstep (se 2 (by rfl) ⟨1656954, by rfl⟩ : syracuseStep 4418545 = 3313909) B3313909
theorem B5891393 : Blo 2295435 5891393 := bstep (se 2 (by rfl) ⟨2209272, by rfl⟩ : syracuseStep 5891393 = 4418545) B4418545
theorem B15710381 : Blo 2295435 15710381 := bstep (se 3 (by rfl) ⟨2945696, by rfl⟩ : syracuseStep 15710381 = 5891393) B5891393
theorem B10473587 : Blo 2295435 10473587 := bstep (se 1 (by rfl) ⟨7855190, by rfl⟩ : syracuseStep 10473587 = 15710381) B15710381
theorem B6982391 : Blo 2295435 6982391 := bstep (se 1 (by rfl) ⟨5236793, by rfl⟩ : syracuseStep 6982391 = 10473587) B10473587
theorem B4654927 : Blo 2295435 4654927 := bstep (se 1 (by rfl) ⟨3491195, by rfl⟩ : syracuseStep 4654927 = 6982391) B6982391
theorem B24826277 : Blo 2295435 24826277 := bstep (se 4 (by rfl) ⟨2327463, by rfl⟩ : syracuseStep 24826277 = 4654927) B4654927
theorem B16550851 : Blo 2295435 16550851 := bstep (se 1 (by rfl) ⟨12413138, by rfl⟩ : syracuseStep 16550851 = 24826277) B24826277
theorem B22067801 : Blo 2295435 22067801 := bstep (se 2 (by rfl) ⟨8275425, by rfl⟩ : syracuseStep 22067801 = 16550851) B16550851
theorem B14711867 : Blo 2295435 14711867 := bstep (se 1 (by rfl) ⟨11033900, by rfl⟩ : syracuseStep 14711867 = 22067801) B22067801
theorem B9807911 : Blo 2295435 9807911 := bstep (se 1 (by rfl) ⟨7355933, by rfl⟩ : syracuseStep 9807911 = 14711867) B14711867
theorem B6538607 : Blo 2295435 6538607 := bstep (se 1 (by rfl) ⟨4903955, by rfl⟩ : syracuseStep 6538607 = 9807911) B9807911
theorem B4359071 : Blo 2295435 4359071 := bstep (se 1 (by rfl) ⟨3269303, by rfl⟩ : syracuseStep 4359071 = 6538607) B6538607
theorem B2906047 : Blo 2295435 2906047 := bstep (se 1 (by rfl) ⟨2179535, by rfl⟩ : syracuseStep 2906047 = 4359071) B4359071
theorem B3874729 : Blo 2295435 3874729 := bstep (se 2 (by rfl) ⟨1453023, by rfl⟩ : syracuseStep 3874729 = 2906047) B2906047
theorem B5166305 : Blo 2295435 5166305 := bstep (se 2 (by rfl) ⟨1937364, by rfl⟩ : syracuseStep 5166305 = 3874729) B3874729
theorem B3444203 : Blo 2295435 3444203 := bstep (se 1 (by rfl) ⟨2583152, by rfl⟩ : syracuseStep 3444203 = 5166305) B5166305
theorem B2296135 : Blo 2295435 2296135 := bstep (se 1 (by rfl) ⟨1722101, by rfl⟩ : syracuseStep 2296135 = 3444203) B3444203
theorem B2583157 : Blo 2295435 2583157 := bbase (se 5 (by rfl) ⟨121085, by rfl⟩ : syracuseStep 2583157 = 242171) (by norm_num)
theorem B3444209 : Blo 2295435 3444209 := bstep (se 2 (by rfl) ⟨1291578, by rfl⟩ : syracuseStep 3444209 = 2583157) B2583157
theorem B2296139 : Blo 2295435 2296139 := bstep (se 1 (by rfl) ⟨1722104, by rfl⟩ : syracuseStep 2296139 = 3444209) B3444209
theorem B2906057 : Blo 2295435 2906057 := bbase (se 2 (by rfl) ⟨1089771, by rfl⟩ : syracuseStep 2906057 = 2179543) (by norm_num)
theorem B7749485 : Blo 2295435 7749485 := bstep (se 3 (by rfl) ⟨1453028, by rfl⟩ : syracuseStep 7749485 = 2906057) B2906057
theorem B5166323 : Blo 2295435 5166323 := bstep (se 1 (by rfl) ⟨3874742, by rfl⟩ : syracuseStep 5166323 = 7749485) B7749485
theorem B3444215 : Blo 2295435 3444215 := bstep (se 1 (by rfl) ⟨2583161, by rfl⟩ : syracuseStep 3444215 = 5166323) B5166323
theorem B2296143 : Blo 2295435 2296143 := bstep (se 1 (by rfl) ⟨1722107, by rfl⟩ : syracuseStep 2296143 = 3444215) B3444215
theorem B3444221 : Blo 2295435 3444221 := bbase (se 3 (by rfl) ⟨645791, by rfl⟩ : syracuseStep 3444221 = 1291583) (by norm_num)
theorem B2296147 : Blo 2295435 2296147 := bstep (se 1 (by rfl) ⟨1722110, by rfl⟩ : syracuseStep 2296147 = 3444221) B3444221
theorem B5166341 : Blo 2295435 5166341 := bbase (se 4 (by rfl) ⟨484344, by rfl⟩ : syracuseStep 5166341 = 968689) (by norm_num)
theorem B3444227 : Blo 2295435 3444227 := bstep (se 1 (by rfl) ⟨2583170, by rfl⟩ : syracuseStep 3444227 = 5166341) B5166341
theorem B2296151 : Blo 2295435 2296151 := bstep (se 1 (by rfl) ⟨1722113, by rfl⟩ : syracuseStep 2296151 = 3444227) B3444227
theorem B4359109 : Blo 2295435 4359109 := bbase (se 4 (by rfl) ⟨408666, by rfl⟩ : syracuseStep 4359109 = 817333) (by norm_num)
theorem B5812145 : Blo 2295435 5812145 := bstep (se 2 (by rfl) ⟨2179554, by rfl⟩ : syracuseStep 5812145 = 4359109) B4359109
theorem B3874763 : Blo 2295435 3874763 := bstep (se 1 (by rfl) ⟨2906072, by rfl⟩ : syracuseStep 3874763 = 5812145) B5812145
theorem B2583175 : Blo 2295435 2583175 := bstep (se 1 (by rfl) ⟨1937381, by rfl⟩ : syracuseStep 2583175 = 3874763) B3874763
theorem B3444233 : Blo 2295435 3444233 := bstep (se 2 (by rfl) ⟨1291587, by rfl⟩ : syracuseStep 3444233 = 2583175) B2583175
theorem B2296155 : Blo 2295435 2296155 := bstep (se 1 (by rfl) ⟨1722116, by rfl⟩ : syracuseStep 2296155 = 3444233) B3444233
theorem B11624309 : Blo 2295435 11624309 := bbase (se 5 (by rfl) ⟨544889, by rfl⟩ : syracuseStep 11624309 = 1089779) (by norm_num)
theorem B7749539 : Blo 2295435 7749539 := bstep (se 1 (by rfl) ⟨5812154, by rfl⟩ : syracuseStep 7749539 = 11624309) B11624309
theorem B5166359 : Blo 2295435 5166359 := bstep (se 1 (by rfl) ⟨3874769, by rfl⟩ : syracuseStep 5166359 = 7749539) B7749539
theorem B3444239 : Blo 2295435 3444239 := bstep (se 1 (by rfl) ⟨2583179, by rfl⟩ : syracuseStep 3444239 = 5166359) B5166359
theorem B2296159 : Blo 2295435 2296159 := bstep (se 1 (by rfl) ⟨1722119, by rfl⟩ : syracuseStep 2296159 = 3444239) B3444239
theorem B3444245 : Blo 2295435 3444245 := bbase (se 6 (by rfl) ⟨80724, by rfl⟩ : syracuseStep 3444245 = 161449) (by norm_num)
theorem B2296163 : Blo 2295435 2296163 := bstep (se 1 (by rfl) ⟨1722122, by rfl⟩ : syracuseStep 2296163 = 3444245) B3444245
theorem B11034053 : Blo 2295435 11034053 := bbase (se 4 (by rfl) ⟨1034442, by rfl⟩ : syracuseStep 11034053 = 2068885) (by norm_num)
theorem B7356035 : Blo 2295435 7356035 := bstep (se 1 (by rfl) ⟨5517026, by rfl⟩ : syracuseStep 7356035 = 11034053) B11034053
theorem B19616093 : Blo 2295435 19616093 := bstep (se 3 (by rfl) ⟨3678017, by rfl⟩ : syracuseStep 19616093 = 7356035) B7356035
theorem B13077395 : Blo 2295435 13077395 := bstep (se 1 (by rfl) ⟨9808046, by rfl⟩ : syracuseStep 13077395 = 19616093) B19616093
theorem B8718263 : Blo 2295435 8718263 := bstep (se 1 (by rfl) ⟨6538697, by rfl⟩ : syracuseStep 8718263 = 13077395) B13077395
theorem B5812175 : Blo 2295435 5812175 := bstep (se 1 (by rfl) ⟨4359131, by rfl⟩ : syracuseStep 5812175 = 8718263) B8718263
theorem B3874783 : Blo 2295435 3874783 := bstep (se 1 (by rfl) ⟨2906087, by rfl⟩ : syracuseStep 3874783 = 5812175) B5812175
theorem B5166377 : Blo 2295435 5166377 := bstep (se 2 (by rfl) ⟨1937391, by rfl⟩ : syracuseStep 5166377 = 3874783) B3874783
theorem B3444251 : Blo 2295435 3444251 := bstep (se 1 (by rfl) ⟨2583188, by rfl⟩ : syracuseStep 3444251 = 5166377) B5166377
theorem B2296167 : Blo 2295435 2296167 := bstep (se 1 (by rfl) ⟨1722125, by rfl⟩ : syracuseStep 2296167 = 3444251) B3444251
theorem B2583193 : Blo 2295435 2583193 := bbase (se 2 (by rfl) ⟨968697, by rfl⟩ : syracuseStep 2583193 = 1937395) (by norm_num)
theorem B3444257 : Blo 2295435 3444257 := bstep (se 2 (by rfl) ⟨1291596, by rfl⟩ : syracuseStep 3444257 = 2583193) B2583193
theorem B2296171 : Blo 2295435 2296171 := bstep (se 1 (by rfl) ⟨1722128, by rfl⟩ : syracuseStep 2296171 = 3444257) B3444257
theorem B8718293 : Blo 2295435 8718293 := bbase (se 7 (by rfl) ⟨102167, by rfl⟩ : syracuseStep 8718293 = 204335) (by norm_num)
theorem B5812195 : Blo 2295435 5812195 := bstep (se 1 (by rfl) ⟨4359146, by rfl⟩ : syracuseStep 5812195 = 8718293) B8718293
theorem B7749593 : Blo 2295435 7749593 := bstep (se 2 (by rfl) ⟨2906097, by rfl⟩ : syracuseStep 7749593 = 5812195) B5812195
theorem B5166395 : Blo 2295435 5166395 := bstep (se 1 (by rfl) ⟨3874796, by rfl⟩ : syracuseStep 5166395 = 7749593) B7749593
theorem B3444263 : Blo 2295435 3444263 := bstep (se 1 (by rfl) ⟨2583197, by rfl⟩ : syracuseStep 3444263 = 5166395) B5166395
theorem B2296175 : Blo 2295435 2296175 := bstep (se 1 (by rfl) ⟨1722131, by rfl⟩ : syracuseStep 2296175 = 3444263) B3444263
theorem B3444269 : Blo 2295435 3444269 := bbase (se 3 (by rfl) ⟨645800, by rfl⟩ : syracuseStep 3444269 = 1291601) (by norm_num)
theorem B2296179 : Blo 2295435 2296179 := bstep (se 1 (by rfl) ⟨1722134, by rfl⟩ : syracuseStep 2296179 = 3444269) B3444269
theorem B5166413 : Blo 2295435 5166413 := bbase (se 3 (by rfl) ⟨968702, by rfl⟩ : syracuseStep 5166413 = 1937405) (by norm_num)
theorem B3444275 : Blo 2295435 3444275 := bstep (se 1 (by rfl) ⟨2583206, by rfl⟩ : syracuseStep 3444275 = 5166413) B5166413
theorem B2296183 : Blo 2295435 2296183 := bstep (se 1 (by rfl) ⟨1722137, by rfl⟩ : syracuseStep 2296183 = 3444275) B3444275
theorem B2906113 : Blo 2295435 2906113 := bbase (se 2 (by rfl) ⟨1089792, by rfl⟩ : syracuseStep 2906113 = 2179585) (by norm_num)
theorem B3874817 : Blo 2295435 3874817 := bstep (se 2 (by rfl) ⟨1453056, by rfl⟩ : syracuseStep 3874817 = 2906113) B2906113
theorem B2583211 : Blo 2295435 2583211 := bstep (se 1 (by rfl) ⟨1937408, by rfl⟩ : syracuseStep 2583211 = 3874817) B3874817
theorem B3444281 : Blo 2295435 3444281 := bstep (se 2 (by rfl) ⟨1291605, by rfl⟩ : syracuseStep 3444281 = 2583211) B2583211
theorem B2296187 : Blo 2295435 2296187 := bstep (se 1 (by rfl) ⟨1722140, by rfl⟩ : syracuseStep 2296187 = 3444281) B3444281
theorem B2452037 : Blo 2295435 2452037 := bbase (se 4 (by rfl) ⟨229878, by rfl⟩ : syracuseStep 2452037 = 459757) (by norm_num)
theorem B26155061 : Blo 2295435 26155061 := bstep (se 5 (by rfl) ⟨1226018, by rfl⟩ : syracuseStep 26155061 = 2452037) B2452037
theorem B17436707 : Blo 2295435 17436707 := bstep (se 1 (by rfl) ⟨13077530, by rfl⟩ : syracuseStep 17436707 = 26155061) B26155061
theorem B11624471 : Blo 2295435 11624471 := bstep (se 1 (by rfl) ⟨8718353, by rfl⟩ : syracuseStep 11624471 = 17436707) B17436707
theorem B7749647 : Blo 2295435 7749647 := bstep (se 1 (by rfl) ⟨5812235, by rfl⟩ : syracuseStep 7749647 = 11624471) B11624471
theorem B5166431 : Blo 2295435 5166431 := bstep (se 1 (by rfl) ⟨3874823, by rfl⟩ : syracuseStep 5166431 = 7749647) B7749647
theorem B3444287 : Blo 2295435 3444287 := bstep (se 1 (by rfl) ⟨2583215, by rfl⟩ : syracuseStep 3444287 = 5166431) B5166431
theorem B2296191 : Blo 2295435 2296191 := bstep (se 1 (by rfl) ⟨1722143, by rfl⟩ : syracuseStep 2296191 = 3444287) B3444287
theorem B3444293 : Blo 2295435 3444293 := bbase (se 4 (by rfl) ⟨322902, by rfl⟩ : syracuseStep 3444293 = 645805) (by norm_num)
theorem B2296195 : Blo 2295435 2296195 := bstep (se 1 (by rfl) ⟨1722146, by rfl⟩ : syracuseStep 2296195 = 3444293) B3444293
theorem B3874837 : Blo 2295435 3874837 := bbase (se 6 (by rfl) ⟨90816, by rfl⟩ : syracuseStep 3874837 = 181633) (by norm_num)
theorem B5166449 : Blo 2295435 5166449 := bstep (se 2 (by rfl) ⟨1937418, by rfl⟩ : syracuseStep 5166449 = 3874837) B3874837
theorem B3444299 : Blo 2295435 3444299 := bstep (se 1 (by rfl) ⟨2583224, by rfl⟩ : syracuseStep 3444299 = 5166449) B5166449
theorem B2296199 : Blo 2295435 2296199 := bstep (se 1 (by rfl) ⟨1722149, by rfl⟩ : syracuseStep 2296199 = 3444299) B3444299
theorem B2583229 : Blo 2295435 2583229 := bbase (se 3 (by rfl) ⟨484355, by rfl⟩ : syracuseStep 2583229 = 968711) (by norm_num)
theorem B3444305 : Blo 2295435 3444305 := bstep (se 2 (by rfl) ⟨1291614, by rfl⟩ : syracuseStep 3444305 = 2583229) B2583229
theorem B2296203 : Blo 2295435 2296203 := bstep (se 1 (by rfl) ⟨1722152, by rfl⟩ : syracuseStep 2296203 = 3444305) B3444305
theorem B7749701 : Blo 2295435 7749701 := bbase (se 4 (by rfl) ⟨726534, by rfl⟩ : syracuseStep 7749701 = 1453069) (by norm_num)
theorem B5166467 : Blo 2295435 5166467 := bstep (se 1 (by rfl) ⟨3874850, by rfl⟩ : syracuseStep 5166467 = 7749701) B7749701
theorem B3444311 : Blo 2295435 3444311 := bstep (se 1 (by rfl) ⟨2583233, by rfl⟩ : syracuseStep 3444311 = 5166467) B5166467
theorem B2296207 : Blo 2295435 2296207 := bstep (se 1 (by rfl) ⟨1722155, by rfl⟩ : syracuseStep 2296207 = 3444311) B3444311
theorem B3444317 : Blo 2295435 3444317 := bbase (se 3 (by rfl) ⟨645809, by rfl⟩ : syracuseStep 3444317 = 1291619) (by norm_num)
theorem B2296211 : Blo 2295435 2296211 := bstep (se 1 (by rfl) ⟨1722158, by rfl⟩ : syracuseStep 2296211 = 3444317) B3444317
theorem B5166485 : Blo 2295435 5166485 := bbase (se 6 (by rfl) ⟨121089, by rfl⟩ : syracuseStep 5166485 = 242179) (by norm_num)
theorem B3444323 : Blo 2295435 3444323 := bstep (se 1 (by rfl) ⟨2583242, by rfl⟩ : syracuseStep 3444323 = 5166485) B5166485
theorem B2296215 : Blo 2295435 2296215 := bstep (se 1 (by rfl) ⟨1722161, by rfl⟩ : syracuseStep 2296215 = 3444323) B3444323
theorem B2327549 : Blo 2295435 2327549 := bbase (se 3 (by rfl) ⟨436415, by rfl⟩ : syracuseStep 2327549 = 872831) (by norm_num)
theorem B6206797 : Blo 2295435 6206797 := bstep (se 3 (by rfl) ⟨1163774, by rfl⟩ : syracuseStep 6206797 = 2327549) B2327549
theorem B8275729 : Blo 2295435 8275729 := bstep (se 2 (by rfl) ⟨3103398, by rfl⟩ : syracuseStep 8275729 = 6206797) B6206797
theorem B11034305 : Blo 2295435 11034305 := bstep (se 2 (by rfl) ⟨4137864, by rfl⟩ : syracuseStep 11034305 = 8275729) B8275729
theorem B7356203 : Blo 2295435 7356203 := bstep (se 1 (by rfl) ⟨5517152, by rfl⟩ : syracuseStep 7356203 = 11034305) B11034305
theorem B4904135 : Blo 2295435 4904135 := bstep (se 1 (by rfl) ⟨3678101, by rfl⟩ : syracuseStep 4904135 = 7356203) B7356203
theorem B3269423 : Blo 2295435 3269423 := bstep (se 1 (by rfl) ⟨2452067, by rfl⟩ : syracuseStep 3269423 = 4904135) B4904135
theorem B8718461 : Blo 2295435 8718461 := bstep (se 3 (by rfl) ⟨1634711, by rfl⟩ : syracuseStep 8718461 = 3269423) B3269423
theorem B5812307 : Blo 2295435 5812307 := bstep (se 1 (by rfl) ⟨4359230, by rfl⟩ : syracuseStep 5812307 = 8718461) B8718461
theorem B3874871 : Blo 2295435 3874871 := bstep (se 1 (by rfl) ⟨2906153, by rfl⟩ : syracuseStep 3874871 = 5812307) B5812307
theorem B2583247 : Blo 2295435 2583247 := bstep (se 1 (by rfl) ⟨1937435, by rfl⟩ : syracuseStep 2583247 = 3874871) B3874871
theorem B3444329 : Blo 2295435 3444329 := bstep (se 2 (by rfl) ⟨1291623, by rfl⟩ : syracuseStep 3444329 = 2583247) B2583247
theorem B2296219 : Blo 2295435 2296219 := bstep (se 1 (by rfl) ⟨1722164, by rfl⟩ : syracuseStep 2296219 = 3444329) B3444329
theorem B2618497 : Blo 2295435 2618497 := bbase (se 2 (by rfl) ⟨981936, by rfl⟩ : syracuseStep 2618497 = 1963873) (by norm_num)
theorem B13965317 : Blo 2295435 13965317 := bstep (se 4 (by rfl) ⟨1309248, by rfl⟩ : syracuseStep 13965317 = 2618497) B2618497
theorem B9310211 : Blo 2295435 9310211 := bstep (se 1 (by rfl) ⟨6982658, by rfl⟩ : syracuseStep 9310211 = 13965317) B13965317
theorem B6206807 : Blo 2295435 6206807 := bstep (se 1 (by rfl) ⟨4655105, by rfl⟩ : syracuseStep 6206807 = 9310211) B9310211
theorem B4137871 : Blo 2295435 4137871 := bstep (se 1 (by rfl) ⟨3103403, by rfl⟩ : syracuseStep 4137871 = 6206807) B6206807
theorem B5517161 : Blo 2295435 5517161 := bstep (se 2 (by rfl) ⟨2068935, by rfl⟩ : syracuseStep 5517161 = 4137871) B4137871
theorem B3678107 : Blo 2295435 3678107 := bstep (se 1 (by rfl) ⟨2758580, by rfl⟩ : syracuseStep 3678107 = 5517161) B5517161
theorem B9808285 : Blo 2295435 9808285 := bstep (se 3 (by rfl) ⟨1839053, by rfl⟩ : syracuseStep 9808285 = 3678107) B3678107
theorem B13077713 : Blo 2295435 13077713 := bstep (se 2 (by rfl) ⟨4904142, by rfl⟩ : syracuseStep 13077713 = 9808285) B9808285
theorem B8718475 : Blo 2295435 8718475 := bstep (se 1 (by rfl) ⟨6538856, by rfl⟩ : syracuseStep 8718475 = 13077713) B13077713
theorem B11624633 : Blo 2295435 11624633 := bstep (se 2 (by rfl) ⟨4359237, by rfl⟩ : syracuseStep 11624633 = 8718475) B8718475
theorem B7749755 : Blo 2295435 7749755 := bstep (se 1 (by rfl) ⟨5812316, by rfl⟩ : syracuseStep 7749755 = 11624633) B11624633
theorem B5166503 : Blo 2295435 5166503 := bstep (se 1 (by rfl) ⟨3874877, by rfl⟩ : syracuseStep 5166503 = 7749755) B7749755
theorem B3444335 : Blo 2295435 3444335 := bstep (se 1 (by rfl) ⟨2583251, by rfl⟩ : syracuseStep 3444335 = 5166503) B5166503
theorem B2296223 : Blo 2295435 2296223 := bstep (se 1 (by rfl) ⟨1722167, by rfl⟩ : syracuseStep 2296223 = 3444335) B3444335
theorem B3444341 : Blo 2295435 3444341 := bbase (se 5 (by rfl) ⟨161453, by rfl⟩ : syracuseStep 3444341 = 322907) (by norm_num)
theorem B2296227 : Blo 2295435 2296227 := bstep (se 1 (by rfl) ⟨1722170, by rfl⟩ : syracuseStep 2296227 = 3444341) B3444341
theorem B4359253 : Blo 2295435 4359253 := bbase (se 8 (by rfl) ⟨25542, by rfl⟩ : syracuseStep 4359253 = 51085) (by norm_num)
theorem B5812337 : Blo 2295435 5812337 := bstep (se 2 (by rfl) ⟨2179626, by rfl⟩ : syracuseStep 5812337 = 4359253) B4359253
theorem B3874891 : Blo 2295435 3874891 := bstep (se 1 (by rfl) ⟨2906168, by rfl⟩ : syracuseStep 3874891 = 5812337) B5812337
theorem B5166521 : Blo 2295435 5166521 := bstep (se 2 (by rfl) ⟨1937445, by rfl⟩ : syracuseStep 5166521 = 3874891) B3874891
theorem B3444347 : Blo 2295435 3444347 := bstep (se 1 (by rfl) ⟨2583260, by rfl⟩ : syracuseStep 3444347 = 5166521) B5166521
theorem B2296231 : Blo 2295435 2296231 := bstep (se 1 (by rfl) ⟨1722173, by rfl⟩ : syracuseStep 2296231 = 3444347) B3444347
theorem B2583265 : Blo 2295435 2583265 := bbase (se 2 (by rfl) ⟨968724, by rfl⟩ : syracuseStep 2583265 = 1937449) (by norm_num)
theorem B3444353 : Blo 2295435 3444353 := bstep (se 2 (by rfl) ⟨1291632, by rfl⟩ : syracuseStep 3444353 = 2583265) B2583265
theorem B2296235 : Blo 2295435 2296235 := bstep (se 1 (by rfl) ⟨1722176, by rfl⟩ : syracuseStep 2296235 = 3444353) B3444353
theorem B5812357 : Blo 2295435 5812357 := bbase (se 4 (by rfl) ⟨544908, by rfl⟩ : syracuseStep 5812357 = 1089817) (by norm_num)
theorem B7749809 : Blo 2295435 7749809 := bstep (se 2 (by rfl) ⟨2906178, by rfl⟩ : syracuseStep 7749809 = 5812357) B5812357
theorem B5166539 : Blo 2295435 5166539 := bstep (se 1 (by rfl) ⟨3874904, by rfl⟩ : syracuseStep 5166539 = 7749809) B7749809
theorem B3444359 : Blo 2295435 3444359 := bstep (se 1 (by rfl) ⟨2583269, by rfl⟩ : syracuseStep 3444359 = 5166539) B5166539
theorem B2296239 : Blo 2295435 2296239 := bstep (se 1 (by rfl) ⟨1722179, by rfl⟩ : syracuseStep 2296239 = 3444359) B3444359
theorem B3444365 : Blo 2295435 3444365 := bbase (se 3 (by rfl) ⟨645818, by rfl⟩ : syracuseStep 3444365 = 1291637) (by norm_num)
theorem B2296243 : Blo 2295435 2296243 := bstep (se 1 (by rfl) ⟨1722182, by rfl⟩ : syracuseStep 2296243 = 3444365) B3444365
theorem B5166557 : Blo 2295435 5166557 := bbase (se 3 (by rfl) ⟨968729, by rfl⟩ : syracuseStep 5166557 = 1937459) (by norm_num)
theorem B3444371 : Blo 2295435 3444371 := bstep (se 1 (by rfl) ⟨2583278, by rfl⟩ : syracuseStep 3444371 = 5166557) B5166557
theorem B2296247 : Blo 2295435 2296247 := bstep (se 1 (by rfl) ⟨1722185, by rfl⟩ : syracuseStep 2296247 = 3444371) B3444371
theorem B3874925 : Blo 2295435 3874925 := bbase (se 3 (by rfl) ⟨726548, by rfl⟩ : syracuseStep 3874925 = 1453097) (by norm_num)
theorem B2583283 : Blo 2295435 2583283 := bstep (se 1 (by rfl) ⟨1937462, by rfl⟩ : syracuseStep 2583283 = 3874925) B3874925
theorem B3444377 : Blo 2295435 3444377 := bstep (se 2 (by rfl) ⟨1291641, by rfl⟩ : syracuseStep 3444377 = 2583283) B2583283
theorem B2296251 : Blo 2295435 2296251 := bstep (se 1 (by rfl) ⟨1722188, by rfl⟩ : syracuseStep 2296251 = 3444377) B3444377
theorem B22068949 : Blo 2295435 22068949 := bbase (se 7 (by rfl) ⟨258620, by rfl⟩ : syracuseStep 22068949 = 517241) (by norm_num)
theorem B29425265 : Blo 2295435 29425265 := bstep (se 2 (by rfl) ⟨11034474, by rfl⟩ : syracuseStep 29425265 = 22068949) B22068949
theorem B19616843 : Blo 2295435 19616843 := bstep (se 1 (by rfl) ⟨14712632, by rfl⟩ : syracuseStep 19616843 = 29425265) B29425265
theorem B13077895 : Blo 2295435 13077895 := bstep (se 1 (by rfl) ⟨9808421, by rfl⟩ : syracuseStep 13077895 = 19616843) B19616843
theorem B17437193 : Blo 2295435 17437193 := bstep (se 2 (by rfl) ⟨6538947, by rfl⟩ : syracuseStep 17437193 = 13077895) B13077895
theorem B11624795 : Blo 2295435 11624795 := bstep (se 1 (by rfl) ⟨8718596, by rfl⟩ : syracuseStep 11624795 = 17437193) B17437193
theorem B7749863 : Blo 2295435 7749863 := bstep (se 1 (by rfl) ⟨5812397, by rfl⟩ : syracuseStep 7749863 = 11624795) B11624795
theorem B5166575 : Blo 2295435 5166575 := bstep (se 1 (by rfl) ⟨3874931, by rfl⟩ : syracuseStep 5166575 = 7749863) B7749863
theorem B3444383 : Blo 2295435 3444383 := bstep (se 1 (by rfl) ⟨2583287, by rfl⟩ : syracuseStep 3444383 = 5166575) B5166575
theorem B2296255 : Blo 2295435 2296255 := bstep (se 1 (by rfl) ⟨1722191, by rfl⟩ : syracuseStep 2296255 = 3444383) B3444383
theorem B3444389 : Blo 2295435 3444389 := bbase (se 4 (by rfl) ⟨322911, by rfl⟩ : syracuseStep 3444389 = 645823) (by norm_num)
theorem B2296259 : Blo 2295435 2296259 := bstep (se 1 (by rfl) ⟨1722194, by rfl⟩ : syracuseStep 2296259 = 3444389) B3444389
theorem B2906209 : Blo 2295435 2906209 := bbase (se 2 (by rfl) ⟨1089828, by rfl⟩ : syracuseStep 2906209 = 2179657) (by norm_num)
theorem B3874945 : Blo 2295435 3874945 := bstep (se 2 (by rfl) ⟨1453104, by rfl⟩ : syracuseStep 3874945 = 2906209) B2906209
theorem B5166593 : Blo 2295435 5166593 := bstep (se 2 (by rfl) ⟨1937472, by rfl⟩ : syracuseStep 5166593 = 3874945) B3874945
theorem B3444395 : Blo 2295435 3444395 := bstep (se 1 (by rfl) ⟨2583296, by rfl⟩ : syracuseStep 3444395 = 5166593) B5166593
theorem B2296263 : Blo 2295435 2296263 := bstep (se 1 (by rfl) ⟨1722197, by rfl⟩ : syracuseStep 2296263 = 3444395) B3444395
theorem B2583301 : Blo 2295435 2583301 := bbase (se 4 (by rfl) ⟨242184, by rfl⟩ : syracuseStep 2583301 = 484369) (by norm_num)
theorem B3444401 : Blo 2295435 3444401 := bstep (se 2 (by rfl) ⟨1291650, by rfl⟩ : syracuseStep 3444401 = 2583301) B2583301
theorem B2296267 : Blo 2295435 2296267 := bstep (se 1 (by rfl) ⟨1722200, by rfl⟩ : syracuseStep 2296267 = 3444401) B3444401
theorem B15711317 : Blo 2295435 15711317 := bbase (se 8 (by rfl) ⟨92058, by rfl⟩ : syracuseStep 15711317 = 184117) (by norm_num)
theorem B10474211 : Blo 2295435 10474211 := bstep (se 1 (by rfl) ⟨7855658, by rfl⟩ : syracuseStep 10474211 = 15711317) B15711317
theorem B6982807 : Blo 2295435 6982807 := bstep (se 1 (by rfl) ⟨5237105, by rfl⟩ : syracuseStep 6982807 = 10474211) B10474211
theorem B9310409 : Blo 2295435 9310409 := bstep (se 2 (by rfl) ⟨3491403, by rfl⟩ : syracuseStep 9310409 = 6982807) B6982807
theorem B6206939 : Blo 2295435 6206939 := bstep (se 1 (by rfl) ⟨4655204, by rfl⟩ : syracuseStep 6206939 = 9310409) B9310409
theorem B4137959 : Blo 2295435 4137959 := bstep (se 1 (by rfl) ⟨3103469, by rfl⟩ : syracuseStep 4137959 = 6206939) B6206939
theorem B2758639 : Blo 2295435 2758639 := bstep (se 1 (by rfl) ⟨2068979, by rfl⟩ : syracuseStep 2758639 = 4137959) B4137959
theorem B3678185 : Blo 2295435 3678185 := bstep (se 2 (by rfl) ⟨1379319, by rfl⟩ : syracuseStep 3678185 = 2758639) B2758639
theorem B2452123 : Blo 2295435 2452123 := bstep (se 1 (by rfl) ⟨1839092, by rfl⟩ : syracuseStep 2452123 = 3678185) B3678185
theorem B3269497 : Blo 2295435 3269497 := bstep (se 2 (by rfl) ⟨1226061, by rfl⟩ : syracuseStep 3269497 = 2452123) B2452123
theorem B4359329 : Blo 2295435 4359329 := bstep (se 2 (by rfl) ⟨1634748, by rfl⟩ : syracuseStep 4359329 = 3269497) B3269497
theorem B2906219 : Blo 2295435 2906219 := bstep (se 1 (by rfl) ⟨2179664, by rfl⟩ : syracuseStep 2906219 = 4359329) B4359329
theorem B7749917 : Blo 2295435 7749917 := bstep (se 3 (by rfl) ⟨1453109, by rfl⟩ : syracuseStep 7749917 = 2906219) B2906219
theorem B5166611 : Blo 2295435 5166611 := bstep (se 1 (by rfl) ⟨3874958, by rfl⟩ : syracuseStep 5166611 = 7749917) B7749917
theorem B3444407 : Blo 2295435 3444407 := bstep (se 1 (by rfl) ⟨2583305, by rfl⟩ : syracuseStep 3444407 = 5166611) B5166611
theorem B2296271 : Blo 2295435 2296271 := bstep (se 1 (by rfl) ⟨1722203, by rfl⟩ : syracuseStep 2296271 = 3444407) B3444407
theorem B3444413 : Blo 2295435 3444413 := bbase (se 3 (by rfl) ⟨645827, by rfl⟩ : syracuseStep 3444413 = 1291655) (by norm_num)
theorem B2296275 : Blo 2295435 2296275 := bstep (se 1 (by rfl) ⟨1722206, by rfl⟩ : syracuseStep 2296275 = 3444413) B3444413
theorem B5166629 : Blo 2295435 5166629 := bbase (se 4 (by rfl) ⟨484371, by rfl⟩ : syracuseStep 5166629 = 968743) (by norm_num)
theorem B3444419 : Blo 2295435 3444419 := bstep (se 1 (by rfl) ⟨2583314, by rfl⟩ : syracuseStep 3444419 = 5166629) B5166629
theorem B2296279 : Blo 2295435 2296279 := bstep (se 1 (by rfl) ⟨1722209, by rfl⟩ : syracuseStep 2296279 = 3444419) B3444419
theorem B5812469 : Blo 2295435 5812469 := bbase (se 5 (by rfl) ⟨272459, by rfl⟩ : syracuseStep 5812469 = 544919) (by norm_num)
theorem B3874979 : Blo 2295435 3874979 := bstep (se 1 (by rfl) ⟨2906234, by rfl⟩ : syracuseStep 3874979 = 5812469) B5812469
theorem B2583319 : Blo 2295435 2583319 := bstep (se 1 (by rfl) ⟨1937489, by rfl⟩ : syracuseStep 2583319 = 3874979) B3874979
theorem B3444425 : Blo 2295435 3444425 := bstep (se 2 (by rfl) ⟨1291659, by rfl⟩ : syracuseStep 3444425 = 2583319) B2583319
theorem B2296283 : Blo 2295435 2296283 := bstep (se 1 (by rfl) ⟨1722212, by rfl⟩ : syracuseStep 2296283 = 3444425) B3444425
theorem B9310469 : Blo 2295435 9310469 := bbase (se 4 (by rfl) ⟨872856, by rfl⟩ : syracuseStep 9310469 = 1745713) (by norm_num)
theorem B24827917 : Blo 2295435 24827917 := bstep (se 3 (by rfl) ⟨4655234, by rfl⟩ : syracuseStep 24827917 = 9310469) B9310469
theorem B33103889 : Blo 2295435 33103889 := bstep (se 2 (by rfl) ⟨12413958, by rfl⟩ : syracuseStep 33103889 = 24827917) B24827917
theorem B22069259 : Blo 2295435 22069259 := bstep (se 1 (by rfl) ⟨16551944, by rfl⟩ : syracuseStep 22069259 = 33103889) B33103889
theorem B14712839 : Blo 2295435 14712839 := bstep (se 1 (by rfl) ⟨11034629, by rfl⟩ : syracuseStep 14712839 = 22069259) B22069259
theorem B9808559 : Blo 2295435 9808559 := bstep (se 1 (by rfl) ⟨7356419, by rfl⟩ : syracuseStep 9808559 = 14712839) B14712839
theorem B6539039 : Blo 2295435 6539039 := bstep (se 1 (by rfl) ⟨4904279, by rfl⟩ : syracuseStep 6539039 = 9808559) B9808559
theorem B4359359 : Blo 2295435 4359359 := bstep (se 1 (by rfl) ⟨3269519, by rfl⟩ : syracuseStep 4359359 = 6539039) B6539039
theorem B11624957 : Blo 2295435 11624957 := bstep (se 3 (by rfl) ⟨2179679, by rfl⟩ : syracuseStep 11624957 = 4359359) B4359359
theorem B7749971 : Blo 2295435 7749971 := bstep (se 1 (by rfl) ⟨5812478, by rfl⟩ : syracuseStep 7749971 = 11624957) B11624957
theorem B5166647 : Blo 2295435 5166647 := bstep (se 1 (by rfl) ⟨3874985, by rfl⟩ : syracuseStep 5166647 = 7749971) B7749971
theorem B3444431 : Blo 2295435 3444431 := bstep (se 1 (by rfl) ⟨2583323, by rfl⟩ : syracuseStep 3444431 = 5166647) B5166647
theorem B2296287 : Blo 2295435 2296287 := bstep (se 1 (by rfl) ⟨1722215, by rfl⟩ : syracuseStep 2296287 = 3444431) B3444431
theorem B3444437 : Blo 2295435 3444437 := bbase (se 7 (by rfl) ⟨40364, by rfl⟩ : syracuseStep 3444437 = 80729) (by norm_num)
theorem B2296291 : Blo 2295435 2296291 := bstep (se 1 (by rfl) ⟨1722218, by rfl⟩ : syracuseStep 2296291 = 3444437) B3444437
theorem B12414005 : Blo 2295435 12414005 := bbase (se 5 (by rfl) ⟨581906, by rfl⟩ : syracuseStep 12414005 = 1163813) (by norm_num)
theorem B8276003 : Blo 2295435 8276003 := bstep (se 1 (by rfl) ⟨6207002, by rfl⟩ : syracuseStep 8276003 = 12414005) B12414005
theorem B5517335 : Blo 2295435 5517335 := bstep (se 1 (by rfl) ⟨4138001, by rfl⟩ : syracuseStep 5517335 = 8276003) B8276003
theorem B3678223 : Blo 2295435 3678223 := bstep (se 1 (by rfl) ⟨2758667, by rfl⟩ : syracuseStep 3678223 = 5517335) B5517335
theorem B4904297 : Blo 2295435 4904297 := bstep (se 2 (by rfl) ⟨1839111, by rfl⟩ : syracuseStep 4904297 = 3678223) B3678223
theorem B3269531 : Blo 2295435 3269531 := bstep (se 1 (by rfl) ⟨2452148, by rfl⟩ : syracuseStep 3269531 = 4904297) B4904297
theorem B8718749 : Blo 2295435 8718749 := bstep (se 3 (by rfl) ⟨1634765, by rfl⟩ : syracuseStep 8718749 = 3269531) B3269531
theorem B5812499 : Blo 2295435 5812499 := bstep (se 1 (by rfl) ⟨4359374, by rfl⟩ : syracuseStep 5812499 = 8718749) B8718749
theorem B3874999 : Blo 2295435 3874999 := bstep (se 1 (by rfl) ⟨2906249, by rfl⟩ : syracuseStep 3874999 = 5812499) B5812499
theorem B5166665 : Blo 2295435 5166665 := bstep (se 2 (by rfl) ⟨1937499, by rfl⟩ : syracuseStep 5166665 = 3874999) B3874999
theorem B3444443 : Blo 2295435 3444443 := bstep (se 1 (by rfl) ⟨2583332, by rfl⟩ : syracuseStep 3444443 = 5166665) B5166665
theorem B2296295 : Blo 2295435 2296295 := bstep (se 1 (by rfl) ⟨1722221, by rfl⟩ : syracuseStep 2296295 = 3444443) B3444443
theorem B2583337 : Blo 2295435 2583337 := bbase (se 2 (by rfl) ⟨968751, by rfl⟩ : syracuseStep 2583337 = 1937503) (by norm_num)
theorem B3444449 : Blo 2295435 3444449 := bstep (se 2 (by rfl) ⟨1291668, by rfl⟩ : syracuseStep 3444449 = 2583337) B2583337
theorem B2296299 : Blo 2295435 2296299 := bstep (se 1 (by rfl) ⟨1722224, by rfl⟩ : syracuseStep 2296299 = 3444449) B3444449
theorem B22675733 : Blo 2295435 22675733 := bbase (se 6 (by rfl) ⟨531462, by rfl⟩ : syracuseStep 22675733 = 1062925) (by norm_num)
theorem B15117155 : Blo 2295435 15117155 := bstep (se 1 (by rfl) ⟨11337866, by rfl⟩ : syracuseStep 15117155 = 22675733) B22675733
theorem B10078103 : Blo 2295435 10078103 := bstep (se 1 (by rfl) ⟨7558577, by rfl⟩ : syracuseStep 10078103 = 15117155) B15117155
theorem B6718735 : Blo 2295435 6718735 := bstep (se 1 (by rfl) ⟨5039051, by rfl⟩ : syracuseStep 6718735 = 10078103) B10078103
theorem B8958313 : Blo 2295435 8958313 := bstep (se 2 (by rfl) ⟨3359367, by rfl⟩ : syracuseStep 8958313 = 6718735) B6718735
theorem B11944417 : Blo 2295435 11944417 := bstep (se 2 (by rfl) ⟨4479156, by rfl⟩ : syracuseStep 11944417 = 8958313) B8958313
theorem B15925889 : Blo 2295435 15925889 := bstep (se 2 (by rfl) ⟨5972208, by rfl⟩ : syracuseStep 15925889 = 11944417) B11944417
theorem B10617259 : Blo 2295435 10617259 := bstep (se 1 (by rfl) ⟨7962944, by rfl⟩ : syracuseStep 10617259 = 15925889) B15925889
theorem B14156345 : Blo 2295435 14156345 := bstep (se 2 (by rfl) ⟨5308629, by rfl⟩ : syracuseStep 14156345 = 10617259) B10617259
theorem B9437563 : Blo 2295435 9437563 := bstep (se 1 (by rfl) ⟨7078172, by rfl⟩ : syracuseStep 9437563 = 14156345) B14156345
theorem B50333669 : Blo 2295435 50333669 := bstep (se 4 (by rfl) ⟨4718781, by rfl⟩ : syracuseStep 50333669 = 9437563) B9437563
theorem B33555779 : Blo 2295435 33555779 := bstep (se 1 (by rfl) ⟨25166834, by rfl⟩ : syracuseStep 33555779 = 50333669) B50333669
theorem B22370519 : Blo 2295435 22370519 := bstep (se 1 (by rfl) ⟨16777889, by rfl⟩ : syracuseStep 22370519 = 33555779) B33555779
theorem B59654717 : Blo 2295435 59654717 := bstep (se 3 (by rfl) ⟨11185259, by rfl⟩ : syracuseStep 59654717 = 22370519) B22370519
theorem B39769811 : Blo 2295435 39769811 := bstep (se 1 (by rfl) ⟨29827358, by rfl⟩ : syracuseStep 39769811 = 59654717) B59654717
theorem B26513207 : Blo 2295435 26513207 := bstep (se 1 (by rfl) ⟨19884905, by rfl⟩ : syracuseStep 26513207 = 39769811) B39769811
theorem B17675471 : Blo 2295435 17675471 := bstep (se 1 (by rfl) ⟨13256603, by rfl⟩ : syracuseStep 17675471 = 26513207) B26513207
theorem B11783647 : Blo 2295435 11783647 := bstep (se 1 (by rfl) ⟨8837735, by rfl⟩ : syracuseStep 11783647 = 17675471) B17675471
theorem B15711529 : Blo 2295435 15711529 := bstep (se 2 (by rfl) ⟨5891823, by rfl⟩ : syracuseStep 15711529 = 11783647) B11783647
theorem B20948705 : Blo 2295435 20948705 := bstep (se 2 (by rfl) ⟨7855764, by rfl⟩ : syracuseStep 20948705 = 15711529) B15711529
theorem B13965803 : Blo 2295435 13965803 := bstep (se 1 (by rfl) ⟨10474352, by rfl⟩ : syracuseStep 13965803 = 20948705) B20948705
theorem B9310535 : Blo 2295435 9310535 := bstep (se 1 (by rfl) ⟨6982901, by rfl⟩ : syracuseStep 9310535 = 13965803) B13965803
theorem B6207023 : Blo 2295435 6207023 := bstep (se 1 (by rfl) ⟨4655267, by rfl⟩ : syracuseStep 6207023 = 9310535) B9310535
theorem B4138015 : Blo 2295435 4138015 := bstep (se 1 (by rfl) ⟨3103511, by rfl⟩ : syracuseStep 4138015 = 6207023) B6207023
theorem B5517353 : Blo 2295435 5517353 := bstep (se 2 (by rfl) ⟨2069007, by rfl⟩ : syracuseStep 5517353 = 4138015) B4138015
theorem B14712941 : Blo 2295435 14712941 := bstep (se 3 (by rfl) ⟨2758676, by rfl⟩ : syracuseStep 14712941 = 5517353) B5517353
theorem B9808627 : Blo 2295435 9808627 := bstep (se 1 (by rfl) ⟨7356470, by rfl⟩ : syracuseStep 9808627 = 14712941) B14712941
theorem B13078169 : Blo 2295435 13078169 := bstep (se 2 (by rfl) ⟨4904313, by rfl⟩ : syracuseStep 13078169 = 9808627) B9808627
theorem B8718779 : Blo 2295435 8718779 := bstep (se 1 (by rfl) ⟨6539084, by rfl⟩ : syracuseStep 8718779 = 13078169) B13078169
theorem B5812519 : Blo 2295435 5812519 := bstep (se 1 (by rfl) ⟨4359389, by rfl⟩ : syracuseStep 5812519 = 8718779) B8718779
theorem B7750025 : Blo 2295435 7750025 := bstep (se 2 (by rfl) ⟨2906259, by rfl⟩ : syracuseStep 7750025 = 5812519) B5812519
theorem B5166683 : Blo 2295435 5166683 := bstep (se 1 (by rfl) ⟨3875012, by rfl⟩ : syracuseStep 5166683 = 7750025) B7750025
theorem B3444455 : Blo 2295435 3444455 := bstep (se 1 (by rfl) ⟨2583341, by rfl⟩ : syracuseStep 3444455 = 5166683) B5166683
theorem B2296303 : Blo 2295435 2296303 := bstep (se 1 (by rfl) ⟨1722227, by rfl⟩ : syracuseStep 2296303 = 3444455) B3444455
theorem B3444461 : Blo 2295435 3444461 := bbase (se 3 (by rfl) ⟨645836, by rfl⟩ : syracuseStep 3444461 = 1291673) (by norm_num)
theorem B2296307 : Blo 2295435 2296307 := bstep (se 1 (by rfl) ⟨1722230, by rfl⟩ : syracuseStep 2296307 = 3444461) B3444461
theorem B5166701 : Blo 2295435 5166701 := bbase (se 3 (by rfl) ⟨968756, by rfl⟩ : syracuseStep 5166701 = 1937513) (by norm_num)
theorem B3444467 : Blo 2295435 3444467 := bstep (se 1 (by rfl) ⟨2583350, by rfl⟩ : syracuseStep 3444467 = 5166701) B5166701
theorem B2296311 : Blo 2295435 2296311 := bstep (se 1 (by rfl) ⟨1722233, by rfl⟩ : syracuseStep 2296311 = 3444467) B3444467
theorem B4359413 : Blo 2295435 4359413 := bbase (se 5 (by rfl) ⟨204347, by rfl⟩ : syracuseStep 4359413 = 408695) (by norm_num)
theorem B2906275 : Blo 2295435 2906275 := bstep (se 1 (by rfl) ⟨2179706, by rfl⟩ : syracuseStep 2906275 = 4359413) B4359413
theorem B3875033 : Blo 2295435 3875033 := bstep (se 2 (by rfl) ⟨1453137, by rfl⟩ : syracuseStep 3875033 = 2906275) B2906275
theorem B2583355 : Blo 2295435 2583355 := bstep (se 1 (by rfl) ⟨1937516, by rfl⟩ : syracuseStep 2583355 = 3875033) B3875033
theorem B3444473 : Blo 2295435 3444473 := bstep (se 2 (by rfl) ⟨1291677, by rfl⟩ : syracuseStep 3444473 = 2583355) B2583355
theorem B2296315 : Blo 2295435 2296315 := bstep (se 1 (by rfl) ⟨1722236, by rfl⟩ : syracuseStep 2296315 = 3444473) B3444473
theorem B37242389 : Blo 2295435 37242389 := bbase (se 6 (by rfl) ⟨872868, by rfl⟩ : syracuseStep 37242389 = 1745737) (by norm_num)
theorem B99313037 : Blo 2295435 99313037 := bstep (se 3 (by rfl) ⟨18621194, by rfl⟩ : syracuseStep 99313037 = 37242389) B37242389
theorem B66208691 : Blo 2295435 66208691 := bstep (se 1 (by rfl) ⟨49656518, by rfl⟩ : syracuseStep 66208691 = 99313037) B99313037
theorem B44139127 : Blo 2295435 44139127 := bstep (se 1 (by rfl) ⟨33104345, by rfl⟩ : syracuseStep 44139127 = 66208691) B66208691
theorem B58852169 : Blo 2295435 58852169 := bstep (se 2 (by rfl) ⟨22069563, by rfl⟩ : syracuseStep 58852169 = 44139127) B44139127
theorem B39234779 : Blo 2295435 39234779 := bstep (se 1 (by rfl) ⟨29426084, by rfl⟩ : syracuseStep 39234779 = 58852169) B58852169
theorem B26156519 : Blo 2295435 26156519 := bstep (se 1 (by rfl) ⟨19617389, by rfl⟩ : syracuseStep 26156519 = 39234779) B39234779
theorem B17437679 : Blo 2295435 17437679 := bstep (se 1 (by rfl) ⟨13078259, by rfl⟩ : syracuseStep 17437679 = 26156519) B26156519
theorem B11625119 : Blo 2295435 11625119 := bstep (se 1 (by rfl) ⟨8718839, by rfl⟩ : syracuseStep 11625119 = 17437679) B17437679
theorem B7750079 : Blo 2295435 7750079 := bstep (se 1 (by rfl) ⟨5812559, by rfl⟩ : syracuseStep 7750079 = 11625119) B11625119
theorem B5166719 : Blo 2295435 5166719 := bstep (se 1 (by rfl) ⟨3875039, by rfl⟩ : syracuseStep 5166719 = 7750079) B7750079
theorem B3444479 : Blo 2295435 3444479 := bstep (se 1 (by rfl) ⟨2583359, by rfl⟩ : syracuseStep 3444479 = 5166719) B5166719
theorem B2296319 : Blo 2295435 2296319 := bstep (se 1 (by rfl) ⟨1722239, by rfl⟩ : syracuseStep 2296319 = 3444479) B3444479
theorem B3444485 : Blo 2295435 3444485 := bbase (se 4 (by rfl) ⟨322920, by rfl⟩ : syracuseStep 3444485 = 645841) (by norm_num)
theorem B2296323 : Blo 2295435 2296323 := bstep (se 1 (by rfl) ⟨1722242, by rfl⟩ : syracuseStep 2296323 = 3444485) B3444485
theorem B3875053 : Blo 2295435 3875053 := bbase (se 3 (by rfl) ⟨726572, by rfl⟩ : syracuseStep 3875053 = 1453145) (by norm_num)
theorem B5166737 : Blo 2295435 5166737 := bstep (se 2 (by rfl) ⟨1937526, by rfl⟩ : syracuseStep 5166737 = 3875053) B3875053
theorem B3444491 : Blo 2295435 3444491 := bstep (se 1 (by rfl) ⟨2583368, by rfl⟩ : syracuseStep 3444491 = 5166737) B5166737
theorem B2296327 : Blo 2295435 2296327 := bstep (se 1 (by rfl) ⟨1722245, by rfl⟩ : syracuseStep 2296327 = 3444491) B3444491
theorem B2583373 : Blo 2295435 2583373 := bbase (se 3 (by rfl) ⟨484382, by rfl⟩ : syracuseStep 2583373 = 968765) (by norm_num)
theorem B3444497 : Blo 2295435 3444497 := bstep (se 2 (by rfl) ⟨1291686, by rfl⟩ : syracuseStep 3444497 = 2583373) B2583373
theorem B2296331 : Blo 2295435 2296331 := bstep (se 1 (by rfl) ⟨1722248, by rfl⟩ : syracuseStep 2296331 = 3444497) B3444497
theorem B7750133 : Blo 2295435 7750133 := bbase (se 5 (by rfl) ⟨363287, by rfl⟩ : syracuseStep 7750133 = 726575) (by norm_num)
theorem B5166755 : Blo 2295435 5166755 := bstep (se 1 (by rfl) ⟨3875066, by rfl⟩ : syracuseStep 5166755 = 7750133) B7750133
theorem B3444503 : Blo 2295435 3444503 := bstep (se 1 (by rfl) ⟨2583377, by rfl⟩ : syracuseStep 3444503 = 5166755) B5166755
theorem B2296335 : Blo 2295435 2296335 := bstep (se 1 (by rfl) ⟨1722251, by rfl⟩ : syracuseStep 2296335 = 3444503) B3444503
theorem B3444509 : Blo 2295435 3444509 := bbase (se 3 (by rfl) ⟨645845, by rfl⟩ : syracuseStep 3444509 = 1291691) (by norm_num)
theorem B2296339 : Blo 2295435 2296339 := bstep (se 1 (by rfl) ⟨1722254, by rfl⟩ : syracuseStep 2296339 = 3444509) B3444509
theorem B5166773 : Blo 2295435 5166773 := bbase (se 5 (by rfl) ⟨242192, by rfl⟩ : syracuseStep 5166773 = 484385) (by norm_num)
theorem B3444515 : Blo 2295435 3444515 := bstep (se 1 (by rfl) ⟨2583386, by rfl⟩ : syracuseStep 3444515 = 5166773) B5166773
theorem B2296343 : Blo 2295435 2296343 := bstep (se 1 (by rfl) ⟨1722257, by rfl⟩ : syracuseStep 2296343 = 3444515) B3444515
theorem B13078421 : Blo 2295435 13078421 := bbase (se 6 (by rfl) ⟨306525, by rfl⟩ : syracuseStep 13078421 = 613051) (by norm_num)
theorem B8718947 : Blo 2295435 8718947 := bstep (se 1 (by rfl) ⟨6539210, by rfl⟩ : syracuseStep 8718947 = 13078421) B13078421
theorem B5812631 : Blo 2295435 5812631 := bstep (se 1 (by rfl) ⟨4359473, by rfl⟩ : syracuseStep 5812631 = 8718947) B8718947
theorem B3875087 : Blo 2295435 3875087 := bstep (se 1 (by rfl) ⟨2906315, by rfl⟩ : syracuseStep 3875087 = 5812631) B5812631
theorem B2583391 : Blo 2295435 2583391 := bstep (se 1 (by rfl) ⟨1937543, by rfl⟩ : syracuseStep 2583391 = 3875087) B3875087
theorem B3444521 : Blo 2295435 3444521 := bstep (se 2 (by rfl) ⟨1291695, by rfl⟩ : syracuseStep 3444521 = 2583391) B2583391
theorem B2296347 : Blo 2295435 2296347 := bstep (se 1 (by rfl) ⟨1722260, by rfl⟩ : syracuseStep 2296347 = 3444521) B3444521
theorem B6539221 : Blo 2295435 6539221 := bbase (se 7 (by rfl) ⟨76631, by rfl⟩ : syracuseStep 6539221 = 153263) (by norm_num)
theorem B8718961 : Blo 2295435 8718961 := bstep (se 2 (by rfl) ⟨3269610, by rfl⟩ : syracuseStep 8718961 = 6539221) B6539221
theorem B11625281 : Blo 2295435 11625281 := bstep (se 2 (by rfl) ⟨4359480, by rfl⟩ : syracuseStep 11625281 = 8718961) B8718961
theorem B7750187 : Blo 2295435 7750187 := bstep (se 1 (by rfl) ⟨5812640, by rfl⟩ : syracuseStep 7750187 = 11625281) B11625281
theorem B5166791 : Blo 2295435 5166791 := bstep (se 1 (by rfl) ⟨3875093, by rfl⟩ : syracuseStep 5166791 = 7750187) B7750187
theorem B3444527 : Blo 2295435 3444527 := bstep (se 1 (by rfl) ⟨2583395, by rfl⟩ : syracuseStep 3444527 = 5166791) B5166791
theorem B2296351 : Blo 2295435 2296351 := bstep (se 1 (by rfl) ⟨1722263, by rfl⟩ : syracuseStep 2296351 = 3444527) B3444527
theorem B3444533 : Blo 2295435 3444533 := bbase (se 5 (by rfl) ⟨161462, by rfl⟩ : syracuseStep 3444533 = 322925) (by norm_num)
theorem B2296355 : Blo 2295435 2296355 := bstep (se 1 (by rfl) ⟨1722266, by rfl⟩ : syracuseStep 2296355 = 3444533) B3444533
theorem B5812661 : Blo 2295435 5812661 := bbase (se 5 (by rfl) ⟨272468, by rfl⟩ : syracuseStep 5812661 = 544937) (by norm_num)
theorem B3875107 : Blo 2295435 3875107 := bstep (se 1 (by rfl) ⟨2906330, by rfl⟩ : syracuseStep 3875107 = 5812661) B5812661
theorem B5166809 : Blo 2295435 5166809 := bstep (se 2 (by rfl) ⟨1937553, by rfl⟩ : syracuseStep 5166809 = 3875107) B3875107
theorem B3444539 : Blo 2295435 3444539 := bstep (se 1 (by rfl) ⟨2583404, by rfl⟩ : syracuseStep 3444539 = 5166809) B5166809
theorem B2296359 : Blo 2295435 2296359 := bstep (se 1 (by rfl) ⟨1722269, by rfl⟩ : syracuseStep 2296359 = 3444539) B3444539
theorem B2583409 : Blo 2295435 2583409 := bbase (se 2 (by rfl) ⟨968778, by rfl⟩ : syracuseStep 2583409 = 1937557) (by norm_num)
theorem B3444545 : Blo 2295435 3444545 := bstep (se 2 (by rfl) ⟨1291704, by rfl⟩ : syracuseStep 3444545 = 2583409) B2583409
theorem B2296363 : Blo 2295435 2296363 := bstep (se 1 (by rfl) ⟨1722272, by rfl⟩ : syracuseStep 2296363 = 3444545) B3444545
theorem B9808901 : Blo 2295435 9808901 := bbase (se 4 (by rfl) ⟨919584, by rfl⟩ : syracuseStep 9808901 = 1839169) (by norm_num)
theorem B6539267 : Blo 2295435 6539267 := bstep (se 1 (by rfl) ⟨4904450, by rfl⟩ : syracuseStep 6539267 = 9808901) B9808901
theorem B4359511 : Blo 2295435 4359511 := bstep (se 1 (by rfl) ⟨3269633, by rfl⟩ : syracuseStep 4359511 = 6539267) B6539267
theorem B5812681 : Blo 2295435 5812681 := bstep (se 2 (by rfl) ⟨2179755, by rfl⟩ : syracuseStep 5812681 = 4359511) B4359511
theorem B7750241 : Blo 2295435 7750241 := bstep (se 2 (by rfl) ⟨2906340, by rfl⟩ : syracuseStep 7750241 = 5812681) B5812681
theorem B5166827 : Blo 2295435 5166827 := bstep (se 1 (by rfl) ⟨3875120, by rfl⟩ : syracuseStep 5166827 = 7750241) B7750241
theorem B3444551 : Blo 2295435 3444551 := bstep (se 1 (by rfl) ⟨2583413, by rfl⟩ : syracuseStep 3444551 = 5166827) B5166827
theorem B2296367 : Blo 2295435 2296367 := bstep (se 1 (by rfl) ⟨1722275, by rfl⟩ : syracuseStep 2296367 = 3444551) B3444551
theorem B3444557 : Blo 2295435 3444557 := bbase (se 3 (by rfl) ⟨645854, by rfl⟩ : syracuseStep 3444557 = 1291709) (by norm_num)
theorem B2296371 : Blo 2295435 2296371 := bstep (se 1 (by rfl) ⟨1722278, by rfl⟩ : syracuseStep 2296371 = 3444557) B3444557
theorem B5166845 : Blo 2295435 5166845 := bbase (se 3 (by rfl) ⟨968783, by rfl⟩ : syracuseStep 5166845 = 1937567) (by norm_num)
theorem B3444563 : Blo 2295435 3444563 := bstep (se 1 (by rfl) ⟨2583422, by rfl⟩ : syracuseStep 3444563 = 5166845) B5166845
theorem B2296375 : Blo 2295435 2296375 := bstep (se 1 (by rfl) ⟨1722281, by rfl⟩ : syracuseStep 2296375 = 3444563) B3444563
theorem B3875141 : Blo 2295435 3875141 := bbase (se 4 (by rfl) ⟨363294, by rfl⟩ : syracuseStep 3875141 = 726589) (by norm_num)
theorem B2583427 : Blo 2295435 2583427 := bstep (se 1 (by rfl) ⟨1937570, by rfl⟩ : syracuseStep 2583427 = 3875141) B3875141
theorem B3444569 : Blo 2295435 3444569 := bstep (se 2 (by rfl) ⟨1291713, by rfl⟩ : syracuseStep 3444569 = 2583427) B2583427
theorem B2296379 : Blo 2295435 2296379 := bstep (se 1 (by rfl) ⟨1722284, by rfl⟩ : syracuseStep 2296379 = 3444569) B3444569
theorem B17438165 : Blo 2295435 17438165 := bbase (se 7 (by rfl) ⟨204353, by rfl⟩ : syracuseStep 17438165 = 408707) (by norm_num)
theorem B11625443 : Blo 2295435 11625443 := bstep (se 1 (by rfl) ⟨8719082, by rfl⟩ : syracuseStep 11625443 = 17438165) B17438165
theorem B7750295 : Blo 2295435 7750295 := bstep (se 1 (by rfl) ⟨5812721, by rfl⟩ : syracuseStep 7750295 = 11625443) B11625443
theorem B5166863 : Blo 2295435 5166863 := bstep (se 1 (by rfl) ⟨3875147, by rfl⟩ : syracuseStep 5166863 = 7750295) B7750295
theorem B3444575 : Blo 2295435 3444575 := bstep (se 1 (by rfl) ⟨2583431, by rfl⟩ : syracuseStep 3444575 = 5166863) B5166863
theorem B2296383 : Blo 2295435 2296383 := bstep (se 1 (by rfl) ⟨1722287, by rfl⟩ : syracuseStep 2296383 = 3444575) B3444575
theorem B3444581 : Blo 2295435 3444581 := bbase (se 4 (by rfl) ⟨322929, by rfl⟩ : syracuseStep 3444581 = 645859) (by norm_num)
theorem B2296387 : Blo 2295435 2296387 := bstep (se 1 (by rfl) ⟨1722290, by rfl⟩ : syracuseStep 2296387 = 3444581) B3444581
theorem B4359557 : Blo 2295435 4359557 := bbase (se 4 (by rfl) ⟨408708, by rfl⟩ : syracuseStep 4359557 = 817417) (by norm_num)
theorem B2906371 : Blo 2295435 2906371 := bstep (se 1 (by rfl) ⟨2179778, by rfl⟩ : syracuseStep 2906371 = 4359557) B4359557
theorem B3875161 : Blo 2295435 3875161 := bstep (se 2 (by rfl) ⟨1453185, by rfl⟩ : syracuseStep 3875161 = 2906371) B2906371
theorem B5166881 : Blo 2295435 5166881 := bstep (se 2 (by rfl) ⟨1937580, by rfl⟩ : syracuseStep 5166881 = 3875161) B3875161
theorem B3444587 : Blo 2295435 3444587 := bstep (se 1 (by rfl) ⟨2583440, by rfl⟩ : syracuseStep 3444587 = 5166881) B5166881
theorem B2296391 : Blo 2295435 2296391 := bstep (se 1 (by rfl) ⟨1722293, by rfl⟩ : syracuseStep 2296391 = 3444587) B3444587
theorem B2583445 : Blo 2295435 2583445 := bbase (se 6 (by rfl) ⟨60549, by rfl⟩ : syracuseStep 2583445 = 121099) (by norm_num)
theorem B3444593 : Blo 2295435 3444593 := bstep (se 2 (by rfl) ⟨1291722, by rfl⟩ : syracuseStep 3444593 = 2583445) B2583445
theorem B2296395 : Blo 2295435 2296395 := bstep (se 1 (by rfl) ⟨1722296, by rfl⟩ : syracuseStep 2296395 = 3444593) B3444593
theorem B2906381 : Blo 2295435 2906381 := bbase (se 3 (by rfl) ⟨544946, by rfl⟩ : syracuseStep 2906381 = 1089893) (by norm_num)
theorem B7750349 : Blo 2295435 7750349 := bstep (se 3 (by rfl) ⟨1453190, by rfl⟩ : syracuseStep 7750349 = 2906381) B2906381
theorem B5166899 : Blo 2295435 5166899 := bstep (se 1 (by rfl) ⟨3875174, by rfl⟩ : syracuseStep 5166899 = 7750349) B7750349
theorem B3444599 : Blo 2295435 3444599 := bstep (se 1 (by rfl) ⟨2583449, by rfl⟩ : syracuseStep 3444599 = 5166899) B5166899
theorem B2296399 : Blo 2295435 2296399 := bstep (se 1 (by rfl) ⟨1722299, by rfl⟩ : syracuseStep 2296399 = 3444599) B3444599
theorem B3444605 : Blo 2295435 3444605 := bbase (se 3 (by rfl) ⟨645863, by rfl⟩ : syracuseStep 3444605 = 1291727) (by norm_num)
theorem B2296403 : Blo 2295435 2296403 := bstep (se 1 (by rfl) ⟨1722302, by rfl⟩ : syracuseStep 2296403 = 3444605) B3444605
theorem B5166917 : Blo 2295435 5166917 := bbase (se 4 (by rfl) ⟨484398, by rfl⟩ : syracuseStep 5166917 = 968797) (by norm_num)
theorem B3444611 : Blo 2295435 3444611 := bstep (se 1 (by rfl) ⟨2583458, by rfl⟩ : syracuseStep 3444611 = 5166917) B5166917
theorem B2296407 : Blo 2295435 2296407 := bstep (se 1 (by rfl) ⟨1722305, by rfl⟩ : syracuseStep 2296407 = 3444611) B3444611
theorem B6207317 : Blo 2295435 6207317 := bbase (se 9 (by rfl) ⟨18185, by rfl⟩ : syracuseStep 6207317 = 36371) (by norm_num)
theorem B4138211 : Blo 2295435 4138211 := bstep (se 1 (by rfl) ⟨3103658, by rfl⟩ : syracuseStep 4138211 = 6207317) B6207317
theorem B2758807 : Blo 2295435 2758807 := bstep (se 1 (by rfl) ⟨2069105, by rfl⟩ : syracuseStep 2758807 = 4138211) B4138211
theorem B3678409 : Blo 2295435 3678409 := bstep (se 2 (by rfl) ⟨1379403, by rfl⟩ : syracuseStep 3678409 = 2758807) B2758807
theorem B4904545 : Blo 2295435 4904545 := bstep (se 2 (by rfl) ⟨1839204, by rfl⟩ : syracuseStep 4904545 = 3678409) B3678409
theorem B6539393 : Blo 2295435 6539393 := bstep (se 2 (by rfl) ⟨2452272, by rfl⟩ : syracuseStep 6539393 = 4904545) B4904545
theorem B4359595 : Blo 2295435 4359595 := bstep (se 1 (by rfl) ⟨3269696, by rfl⟩ : syracuseStep 4359595 = 6539393) B6539393
theorem B5812793 : Blo 2295435 5812793 := bstep (se 2 (by rfl) ⟨2179797, by rfl⟩ : syracuseStep 5812793 = 4359595) B4359595
theorem B3875195 : Blo 2295435 3875195 := bstep (se 1 (by rfl) ⟨2906396, by rfl⟩ : syracuseStep 3875195 = 5812793) B5812793
theorem B2583463 : Blo 2295435 2583463 := bstep (se 1 (by rfl) ⟨1937597, by rfl⟩ : syracuseStep 2583463 = 3875195) B3875195
theorem B3444617 : Blo 2295435 3444617 := bstep (se 2 (by rfl) ⟨1291731, by rfl⟩ : syracuseStep 3444617 = 2583463) B2583463
theorem B2296411 : Blo 2295435 2296411 := bstep (se 1 (by rfl) ⟨1722308, by rfl⟩ : syracuseStep 2296411 = 3444617) B3444617
theorem B11625605 : Blo 2295435 11625605 := bbase (se 4 (by rfl) ⟨1089900, by rfl⟩ : syracuseStep 11625605 = 2179801) (by norm_num)
theorem B7750403 : Blo 2295435 7750403 := bstep (se 1 (by rfl) ⟨5812802, by rfl⟩ : syracuseStep 7750403 = 11625605) B11625605
theorem B5166935 : Blo 2295435 5166935 := bstep (se 1 (by rfl) ⟨3875201, by rfl⟩ : syracuseStep 5166935 = 7750403) B7750403
theorem B3444623 : Blo 2295435 3444623 := bstep (se 1 (by rfl) ⟨2583467, by rfl⟩ : syracuseStep 3444623 = 5166935) B5166935
theorem B2296415 : Blo 2295435 2296415 := bstep (se 1 (by rfl) ⟨1722311, by rfl⟩ : syracuseStep 2296415 = 3444623) B3444623
theorem B3444629 : Blo 2295435 3444629 := bbase (se 6 (by rfl) ⟨80733, by rfl⟩ : syracuseStep 3444629 = 161467) (by norm_num)
theorem B2296419 : Blo 2295435 2296419 := bstep (se 1 (by rfl) ⟨1722314, by rfl⟩ : syracuseStep 2296419 = 3444629) B3444629
theorem B2452285 : Blo 2295435 2452285 := bbase (se 3 (by rfl) ⟨459803, by rfl⟩ : syracuseStep 2452285 = 919607) (by norm_num)
theorem B13078853 : Blo 2295435 13078853 := bstep (se 4 (by rfl) ⟨1226142, by rfl⟩ : syracuseStep 13078853 = 2452285) B2452285
theorem B8719235 : Blo 2295435 8719235 := bstep (se 1 (by rfl) ⟨6539426, by rfl⟩ : syracuseStep 8719235 = 13078853) B13078853
theorem B5812823 : Blo 2295435 5812823 := bstep (se 1 (by rfl) ⟨4359617, by rfl⟩ : syracuseStep 5812823 = 8719235) B8719235
theorem B3875215 : Blo 2295435 3875215 := bstep (se 1 (by rfl) ⟨2906411, by rfl⟩ : syracuseStep 3875215 = 5812823) B5812823
theorem B5166953 : Blo 2295435 5166953 := bstep (se 2 (by rfl) ⟨1937607, by rfl⟩ : syracuseStep 5166953 = 3875215) B3875215
theorem B3444635 : Blo 2295435 3444635 := bstep (se 1 (by rfl) ⟨2583476, by rfl⟩ : syracuseStep 3444635 = 5166953) B5166953
theorem B2296423 : Blo 2295435 2296423 := bstep (se 1 (by rfl) ⟨1722317, by rfl⟩ : syracuseStep 2296423 = 3444635) B3444635
theorem B2583481 : Blo 2295435 2583481 := bbase (se 2 (by rfl) ⟨968805, by rfl⟩ : syracuseStep 2583481 = 1937611) (by norm_num)
theorem B3444641 : Blo 2295435 3444641 := bstep (se 2 (by rfl) ⟨1291740, by rfl⟩ : syracuseStep 3444641 = 2583481) B2583481
theorem B2296427 : Blo 2295435 2296427 := bstep (se 1 (by rfl) ⟨1722320, by rfl⟩ : syracuseStep 2296427 = 3444641) B3444641
theorem B5517661 : Blo 2295435 5517661 := bbase (se 3 (by rfl) ⟨1034561, by rfl⟩ : syracuseStep 5517661 = 2069123) (by norm_num)
theorem B7356881 : Blo 2295435 7356881 := bstep (se 2 (by rfl) ⟨2758830, by rfl⟩ : syracuseStep 7356881 = 5517661) B5517661
theorem B4904587 : Blo 2295435 4904587 := bstep (se 1 (by rfl) ⟨3678440, by rfl⟩ : syracuseStep 4904587 = 7356881) B7356881
theorem B6539449 : Blo 2295435 6539449 := bstep (se 2 (by rfl) ⟨2452293, by rfl⟩ : syracuseStep 6539449 = 4904587) B4904587
theorem B8719265 : Blo 2295435 8719265 := bstep (se 2 (by rfl) ⟨3269724, by rfl⟩ : syracuseStep 8719265 = 6539449) B6539449
theorem B5812843 : Blo 2295435 5812843 := bstep (se 1 (by rfl) ⟨4359632, by rfl⟩ : syracuseStep 5812843 = 8719265) B8719265
theorem B7750457 : Blo 2295435 7750457 := bstep (se 2 (by rfl) ⟨2906421, by rfl⟩ : syracuseStep 7750457 = 5812843) B5812843
theorem B5166971 : Blo 2295435 5166971 := bstep (se 1 (by rfl) ⟨3875228, by rfl⟩ : syracuseStep 5166971 = 7750457) B7750457
theorem B3444647 : Blo 2295435 3444647 := bstep (se 1 (by rfl) ⟨2583485, by rfl⟩ : syracuseStep 3444647 = 5166971) B5166971
theorem B2296431 : Blo 2295435 2296431 := bstep (se 1 (by rfl) ⟨1722323, by rfl⟩ : syracuseStep 2296431 = 3444647) B3444647
theorem B3444653 : Blo 2295435 3444653 := bbase (se 3 (by rfl) ⟨645872, by rfl⟩ : syracuseStep 3444653 = 1291745) (by norm_num)
theorem B2296435 : Blo 2295435 2296435 := bstep (se 1 (by rfl) ⟨1722326, by rfl⟩ : syracuseStep 2296435 = 3444653) B3444653
theorem B5166989 : Blo 2295435 5166989 := bbase (se 3 (by rfl) ⟨968810, by rfl⟩ : syracuseStep 5166989 = 1937621) (by norm_num)
theorem B3444659 : Blo 2295435 3444659 := bstep (se 1 (by rfl) ⟨2583494, by rfl⟩ : syracuseStep 3444659 = 5166989) B5166989
theorem B2296439 : Blo 2295435 2296439 := bstep (se 1 (by rfl) ⟨1722329, by rfl⟩ : syracuseStep 2296439 = 3444659) B3444659
theorem B2906437 : Blo 2295435 2906437 := bbase (se 4 (by rfl) ⟨272478, by rfl⟩ : syracuseStep 2906437 = 544957) (by norm_num)
theorem B3875249 : Blo 2295435 3875249 := bstep (se 2 (by rfl) ⟨1453218, by rfl⟩ : syracuseStep 3875249 = 2906437) B2906437
theorem B2583499 : Blo 2295435 2583499 := bstep (se 1 (by rfl) ⟨1937624, by rfl⟩ : syracuseStep 2583499 = 3875249) B3875249
theorem B3444665 : Blo 2295435 3444665 := bstep (se 2 (by rfl) ⟨1291749, by rfl⟩ : syracuseStep 3444665 = 2583499) B2583499
theorem B2296443 : Blo 2295435 2296443 := bstep (se 1 (by rfl) ⟨1722332, by rfl⟩ : syracuseStep 2296443 = 3444665) B3444665
theorem B11035397 : Blo 2295435 11035397 := bbase (se 4 (by rfl) ⟨1034568, by rfl⟩ : syracuseStep 11035397 = 2069137) (by norm_num)
theorem B29427725 : Blo 2295435 29427725 := bstep (se 3 (by rfl) ⟨5517698, by rfl⟩ : syracuseStep 29427725 = 11035397) B11035397
theorem B19618483 : Blo 2295435 19618483 := bstep (se 1 (by rfl) ⟨14713862, by rfl⟩ : syracuseStep 19618483 = 29427725) B29427725
theorem B26157977 : Blo 2295435 26157977 := bstep (se 2 (by rfl) ⟨9809241, by rfl⟩ : syracuseStep 26157977 = 19618483) B19618483
theorem B17438651 : Blo 2295435 17438651 := bstep (se 1 (by rfl) ⟨13078988, by rfl⟩ : syracuseStep 17438651 = 26157977) B26157977
theorem B11625767 : Blo 2295435 11625767 := bstep (se 1 (by rfl) ⟨8719325, by rfl⟩ : syracuseStep 11625767 = 17438651) B17438651
theorem B7750511 : Blo 2295435 7750511 := bstep (se 1 (by rfl) ⟨5812883, by rfl⟩ : syracuseStep 7750511 = 11625767) B11625767
theorem B5167007 : Blo 2295435 5167007 := bstep (se 1 (by rfl) ⟨3875255, by rfl⟩ : syracuseStep 5167007 = 7750511) B7750511
theorem B3444671 : Blo 2295435 3444671 := bstep (se 1 (by rfl) ⟨2583503, by rfl⟩ : syracuseStep 3444671 = 5167007) B5167007
theorem B2296447 : Blo 2295435 2296447 := bstep (se 1 (by rfl) ⟨1722335, by rfl⟩ : syracuseStep 2296447 = 3444671) B3444671
theorem B3444677 : Blo 2295435 3444677 := bbase (se 4 (by rfl) ⟨322938, by rfl⟩ : syracuseStep 3444677 = 645877) (by norm_num)
theorem B2296451 : Blo 2295435 2296451 := bstep (se 1 (by rfl) ⟨1722338, by rfl⟩ : syracuseStep 2296451 = 3444677) B3444677
theorem B3875269 : Blo 2295435 3875269 := bbase (se 4 (by rfl) ⟨363306, by rfl⟩ : syracuseStep 3875269 = 726613) (by norm_num)
theorem B5167025 : Blo 2295435 5167025 := bstep (se 2 (by rfl) ⟨1937634, by rfl⟩ : syracuseStep 5167025 = 3875269) B3875269
theorem B3444683 : Blo 2295435 3444683 := bstep (se 1 (by rfl) ⟨2583512, by rfl⟩ : syracuseStep 3444683 = 5167025) B5167025
theorem B2296455 : Blo 2295435 2296455 := bstep (se 1 (by rfl) ⟨1722341, by rfl⟩ : syracuseStep 2296455 = 3444683) B3444683
theorem B2583517 : Blo 2295435 2583517 := bbase (se 3 (by rfl) ⟨484409, by rfl⟩ : syracuseStep 2583517 = 968819) (by norm_num)
theorem B3444689 : Blo 2295435 3444689 := bstep (se 2 (by rfl) ⟨1291758, by rfl⟩ : syracuseStep 3444689 = 2583517) B2583517
theorem B2296459 : Blo 2295435 2296459 := bstep (se 1 (by rfl) ⟨1722344, by rfl⟩ : syracuseStep 2296459 = 3444689) B3444689
theorem B7750565 : Blo 2295435 7750565 := bbase (se 4 (by rfl) ⟨726615, by rfl⟩ : syracuseStep 7750565 = 1453231) (by norm_num)
theorem B5167043 : Blo 2295435 5167043 := bstep (se 1 (by rfl) ⟨3875282, by rfl⟩ : syracuseStep 5167043 = 7750565) B7750565
theorem B3444695 : Blo 2295435 3444695 := bstep (se 1 (by rfl) ⟨2583521, by rfl⟩ : syracuseStep 3444695 = 5167043) B5167043
theorem B2296463 : Blo 2295435 2296463 := bstep (se 1 (by rfl) ⟨1722347, by rfl⟩ : syracuseStep 2296463 = 3444695) B3444695
theorem B3444701 : Blo 2295435 3444701 := bbase (se 3 (by rfl) ⟨645881, by rfl⟩ : syracuseStep 3444701 = 1291763) (by norm_num)
theorem B2296467 : Blo 2295435 2296467 := bstep (se 1 (by rfl) ⟨1722350, by rfl⟩ : syracuseStep 2296467 = 3444701) B3444701
theorem B5167061 : Blo 2295435 5167061 := bbase (se 7 (by rfl) ⟨60551, by rfl⟩ : syracuseStep 5167061 = 121103) (by norm_num)
theorem B3444707 : Blo 2295435 3444707 := bstep (se 1 (by rfl) ⟨2583530, by rfl⟩ : syracuseStep 3444707 = 5167061) B5167061
theorem B2296471 : Blo 2295435 2296471 := bstep (se 1 (by rfl) ⟨1722353, by rfl⟩ : syracuseStep 2296471 = 3444707) B3444707
theorem B2946133 : Blo 2295435 2946133 := bbase (se 8 (by rfl) ⟨17262, by rfl⟩ : syracuseStep 2946133 = 34525) (by norm_num)
theorem B3928177 : Blo 2295435 3928177 := bstep (se 2 (by rfl) ⟨1473066, by rfl⟩ : syracuseStep 3928177 = 2946133) B2946133
theorem B5237569 : Blo 2295435 5237569 := bstep (se 2 (by rfl) ⟨1964088, by rfl⟩ : syracuseStep 5237569 = 3928177) B3928177
theorem B6983425 : Blo 2295435 6983425 := bstep (se 2 (by rfl) ⟨2618784, by rfl⟩ : syracuseStep 6983425 = 5237569) B5237569
theorem B9311233 : Blo 2295435 9311233 := bstep (se 2 (by rfl) ⟨3491712, by rfl⟩ : syracuseStep 9311233 = 6983425) B6983425
theorem B12414977 : Blo 2295435 12414977 := bstep (se 2 (by rfl) ⟨4655616, by rfl⟩ : syracuseStep 12414977 = 9311233) B9311233
theorem B8276651 : Blo 2295435 8276651 := bstep (se 1 (by rfl) ⟨6207488, by rfl⟩ : syracuseStep 8276651 = 12414977) B12414977
theorem B5517767 : Blo 2295435 5517767 := bstep (se 1 (by rfl) ⟨4138325, by rfl⟩ : syracuseStep 5517767 = 8276651) B8276651
theorem B14714045 : Blo 2295435 14714045 := bstep (se 3 (by rfl) ⟨2758883, by rfl⟩ : syracuseStep 14714045 = 5517767) B5517767
theorem B9809363 : Blo 2295435 9809363 := bstep (se 1 (by rfl) ⟨7357022, by rfl⟩ : syracuseStep 9809363 = 14714045) B14714045
theorem B6539575 : Blo 2295435 6539575 := bstep (se 1 (by rfl) ⟨4904681, by rfl⟩ : syracuseStep 6539575 = 9809363) B9809363
theorem B8719433 : Blo 2295435 8719433 := bstep (se 2 (by rfl) ⟨3269787, by rfl⟩ : syracuseStep 8719433 = 6539575) B6539575
theorem B5812955 : Blo 2295435 5812955 := bstep (se 1 (by rfl) ⟨4359716, by rfl⟩ : syracuseStep 5812955 = 8719433) B8719433
theorem B3875303 : Blo 2295435 3875303 := bstep (se 1 (by rfl) ⟨2906477, by rfl⟩ : syracuseStep 3875303 = 5812955) B5812955
theorem B2583535 : Blo 2295435 2583535 := bstep (se 1 (by rfl) ⟨1937651, by rfl⟩ : syracuseStep 2583535 = 3875303) B3875303
theorem B3444713 : Blo 2295435 3444713 := bstep (se 2 (by rfl) ⟨1291767, by rfl⟩ : syracuseStep 3444713 = 2583535) B2583535
theorem B2296475 : Blo 2295435 2296475 := bstep (se 1 (by rfl) ⟨1722356, by rfl⟩ : syracuseStep 2296475 = 3444713) B3444713
theorem B3678517 : Blo 2295435 3678517 := bbase (se 5 (by rfl) ⟨172430, by rfl⟩ : syracuseStep 3678517 = 344861) (by norm_num)
theorem B19618757 : Blo 2295435 19618757 := bstep (se 4 (by rfl) ⟨1839258, by rfl⟩ : syracuseStep 19618757 = 3678517) B3678517
theorem B13079171 : Blo 2295435 13079171 := bstep (se 1 (by rfl) ⟨9809378, by rfl⟩ : syracuseStep 13079171 = 19618757) B19618757
theorem B8719447 : Blo 2295435 8719447 := bstep (se 1 (by rfl) ⟨6539585, by rfl⟩ : syracuseStep 8719447 = 13079171) B13079171
theorem B11625929 : Blo 2295435 11625929 := bstep (se 2 (by rfl) ⟨4359723, by rfl⟩ : syracuseStep 11625929 = 8719447) B8719447
theorem B7750619 : Blo 2295435 7750619 := bstep (se 1 (by rfl) ⟨5812964, by rfl⟩ : syracuseStep 7750619 = 11625929) B11625929
theorem B5167079 : Blo 2295435 5167079 := bstep (se 1 (by rfl) ⟨3875309, by rfl⟩ : syracuseStep 5167079 = 7750619) B7750619
theorem B3444719 : Blo 2295435 3444719 := bstep (se 1 (by rfl) ⟨2583539, by rfl⟩ : syracuseStep 3444719 = 5167079) B5167079
theorem B2296479 : Blo 2295435 2296479 := bstep (se 1 (by rfl) ⟨1722359, by rfl⟩ : syracuseStep 2296479 = 3444719) B3444719
theorem B3444725 : Blo 2295435 3444725 := bbase (se 5 (by rfl) ⟨161471, by rfl⟩ : syracuseStep 3444725 = 322943) (by norm_num)
theorem B2296483 : Blo 2295435 2296483 := bstep (se 1 (by rfl) ⟨1722362, by rfl⟩ : syracuseStep 2296483 = 3444725) B3444725
theorem B7357061 : Blo 2295435 7357061 := bbase (se 4 (by rfl) ⟨689724, by rfl⟩ : syracuseStep 7357061 = 1379449) (by norm_num)
theorem B4904707 : Blo 2295435 4904707 := bstep (se 1 (by rfl) ⟨3678530, by rfl⟩ : syracuseStep 4904707 = 7357061) B7357061
theorem B6539609 : Blo 2295435 6539609 := bstep (se 2 (by rfl) ⟨2452353, by rfl⟩ : syracuseStep 6539609 = 4904707) B4904707
theorem B4359739 : Blo 2295435 4359739 := bstep (se 1 (by rfl) ⟨3269804, by rfl⟩ : syracuseStep 4359739 = 6539609) B6539609
theorem B5812985 : Blo 2295435 5812985 := bstep (se 2 (by rfl) ⟨2179869, by rfl⟩ : syracuseStep 5812985 = 4359739) B4359739
theorem B3875323 : Blo 2295435 3875323 := bstep (se 1 (by rfl) ⟨2906492, by rfl⟩ : syracuseStep 3875323 = 5812985) B5812985
theorem B5167097 : Blo 2295435 5167097 := bstep (se 2 (by rfl) ⟨1937661, by rfl⟩ : syracuseStep 5167097 = 3875323) B3875323
theorem B3444731 : Blo 2295435 3444731 := bstep (se 1 (by rfl) ⟨2583548, by rfl⟩ : syracuseStep 3444731 = 5167097) B5167097
theorem B2296487 : Blo 2295435 2296487 := bstep (se 1 (by rfl) ⟨1722365, by rfl⟩ : syracuseStep 2296487 = 3444731) B3444731
theorem B2583553 : Blo 2295435 2583553 := bbase (se 2 (by rfl) ⟨968832, by rfl⟩ : syracuseStep 2583553 = 1937665) (by norm_num)
theorem B3444737 : Blo 2295435 3444737 := bstep (se 2 (by rfl) ⟨1291776, by rfl⟩ : syracuseStep 3444737 = 2583553) B2583553
theorem B2296491 : Blo 2295435 2296491 := bstep (se 1 (by rfl) ⟨1722368, by rfl⟩ : syracuseStep 2296491 = 3444737) B3444737
theorem B5813005 : Blo 2295435 5813005 := bbase (se 3 (by rfl) ⟨1089938, by rfl⟩ : syracuseStep 5813005 = 2179877) (by norm_num)
theorem B7750673 : Blo 2295435 7750673 := bstep (se 2 (by rfl) ⟨2906502, by rfl⟩ : syracuseStep 7750673 = 5813005) B5813005
theorem B5167115 : Blo 2295435 5167115 := bstep (se 1 (by rfl) ⟨3875336, by rfl⟩ : syracuseStep 5167115 = 7750673) B7750673
theorem B3444743 : Blo 2295435 3444743 := bstep (se 1 (by rfl) ⟨2583557, by rfl⟩ : syracuseStep 3444743 = 5167115) B5167115
theorem B2296495 : Blo 2295435 2296495 := bstep (se 1 (by rfl) ⟨1722371, by rfl⟩ : syracuseStep 2296495 = 3444743) B3444743
theorem B3444749 : Blo 2295435 3444749 := bbase (se 3 (by rfl) ⟨645890, by rfl⟩ : syracuseStep 3444749 = 1291781) (by norm_num)
theorem B2296499 : Blo 2295435 2296499 := bstep (se 1 (by rfl) ⟨1722374, by rfl⟩ : syracuseStep 2296499 = 3444749) B3444749
theorem B5167133 : Blo 2295435 5167133 := bbase (se 3 (by rfl) ⟨968837, by rfl⟩ : syracuseStep 5167133 = 1937675) (by norm_num)
theorem B3444755 : Blo 2295435 3444755 := bstep (se 1 (by rfl) ⟨2583566, by rfl⟩ : syracuseStep 3444755 = 5167133) B5167133
theorem B2296503 : Blo 2295435 2296503 := bstep (se 1 (by rfl) ⟨1722377, by rfl⟩ : syracuseStep 2296503 = 3444755) B3444755
theorem B3875357 : Blo 2295435 3875357 := bbase (se 3 (by rfl) ⟨726629, by rfl⟩ : syracuseStep 3875357 = 1453259) (by norm_num)
theorem B2583571 : Blo 2295435 2583571 := bstep (se 1 (by rfl) ⟨1937678, by rfl⟩ : syracuseStep 2583571 = 3875357) B3875357
theorem B3444761 : Blo 2295435 3444761 := bstep (se 2 (by rfl) ⟨1291785, by rfl⟩ : syracuseStep 3444761 = 2583571) B2583571
theorem B2296507 : Blo 2295435 2296507 := bstep (se 1 (by rfl) ⟨1722380, by rfl⟩ : syracuseStep 2296507 = 3444761) B3444761
theorem B2618825 : Blo 2295435 2618825 := bbase (se 2 (by rfl) ⟨982059, by rfl⟩ : syracuseStep 2618825 = 1964119) (by norm_num)
theorem B6983533 : Blo 2295435 6983533 := bstep (se 3 (by rfl) ⟨1309412, by rfl⟩ : syracuseStep 6983533 = 2618825) B2618825
theorem B9311377 : Blo 2295435 9311377 := bstep (se 2 (by rfl) ⟨3491766, by rfl⟩ : syracuseStep 9311377 = 6983533) B6983533
theorem B12415169 : Blo 2295435 12415169 := bstep (se 2 (by rfl) ⟨4655688, by rfl⟩ : syracuseStep 12415169 = 9311377) B9311377
theorem B8276779 : Blo 2295435 8276779 := bstep (se 1 (by rfl) ⟨6207584, by rfl⟩ : syracuseStep 8276779 = 12415169) B12415169
theorem B11035705 : Blo 2295435 11035705 := bstep (se 2 (by rfl) ⟨4138389, by rfl⟩ : syracuseStep 11035705 = 8276779) B8276779
theorem B14714273 : Blo 2295435 14714273 := bstep (se 2 (by rfl) ⟨5517852, by rfl⟩ : syracuseStep 14714273 = 11035705) B11035705
theorem B9809515 : Blo 2295435 9809515 := bstep (se 1 (by rfl) ⟨7357136, by rfl⟩ : syracuseStep 9809515 = 14714273) B14714273
theorem B13079353 : Blo 2295435 13079353 := bstep (se 2 (by rfl) ⟨4904757, by rfl⟩ : syracuseStep 13079353 = 9809515) B9809515
theorem B17439137 : Blo 2295435 17439137 := bstep (se 2 (by rfl) ⟨6539676, by rfl⟩ : syracuseStep 17439137 = 13079353) B13079353
theorem B11626091 : Blo 2295435 11626091 := bstep (se 1 (by rfl) ⟨8719568, by rfl⟩ : syracuseStep 11626091 = 17439137) B17439137
theorem B7750727 : Blo 2295435 7750727 := bstep (se 1 (by rfl) ⟨5813045, by rfl⟩ : syracuseStep 7750727 = 11626091) B11626091
theorem B5167151 : Blo 2295435 5167151 := bstep (se 1 (by rfl) ⟨3875363, by rfl⟩ : syracuseStep 5167151 = 7750727) B7750727
theorem B3444767 : Blo 2295435 3444767 := bstep (se 1 (by rfl) ⟨2583575, by rfl⟩ : syracuseStep 3444767 = 5167151) B5167151
theorem B2296511 : Blo 2295435 2296511 := bstep (se 1 (by rfl) ⟨1722383, by rfl⟩ : syracuseStep 2296511 = 3444767) B3444767
theorem B3444773 : Blo 2295435 3444773 := bbase (se 4 (by rfl) ⟨322947, by rfl⟩ : syracuseStep 3444773 = 645895) (by norm_num)
theorem B2296515 : Blo 2295435 2296515 := bstep (se 1 (by rfl) ⟨1722386, by rfl⟩ : syracuseStep 2296515 = 3444773) B3444773
theorem B2906533 : Blo 2295435 2906533 := bbase (se 4 (by rfl) ⟨272487, by rfl⟩ : syracuseStep 2906533 = 544975) (by norm_num)
theorem B3875377 : Blo 2295435 3875377 := bstep (se 2 (by rfl) ⟨1453266, by rfl⟩ : syracuseStep 3875377 = 2906533) B2906533
theorem B5167169 : Blo 2295435 5167169 := bstep (se 2 (by rfl) ⟨1937688, by rfl⟩ : syracuseStep 5167169 = 3875377) B3875377
theorem B3444779 : Blo 2295435 3444779 := bstep (se 1 (by rfl) ⟨2583584, by rfl⟩ : syracuseStep 3444779 = 5167169) B5167169
theorem B2296519 : Blo 2295435 2296519 := bstep (se 1 (by rfl) ⟨1722389, by rfl⟩ : syracuseStep 2296519 = 3444779) B3444779
theorem B2583589 : Blo 2295435 2583589 := bbase (se 4 (by rfl) ⟨242211, by rfl⟩ : syracuseStep 2583589 = 484423) (by norm_num)
theorem B3444785 : Blo 2295435 3444785 := bstep (se 2 (by rfl) ⟨1291794, by rfl⟩ : syracuseStep 3444785 = 2583589) B2583589
theorem B2296523 : Blo 2295435 2296523 := bstep (se 1 (by rfl) ⟨1722392, by rfl⟩ : syracuseStep 2296523 = 3444785) B3444785
theorem B7357189 : Blo 2295435 7357189 := bbase (se 4 (by rfl) ⟨689736, by rfl⟩ : syracuseStep 7357189 = 1379473) (by norm_num)
theorem B9809585 : Blo 2295435 9809585 := bstep (se 2 (by rfl) ⟨3678594, by rfl⟩ : syracuseStep 9809585 = 7357189) B7357189
theorem B6539723 : Blo 2295435 6539723 := bstep (se 1 (by rfl) ⟨4904792, by rfl⟩ : syracuseStep 6539723 = 9809585) B9809585
theorem B4359815 : Blo 2295435 4359815 := bstep (se 1 (by rfl) ⟨3269861, by rfl⟩ : syracuseStep 4359815 = 6539723) B6539723
theorem B2906543 : Blo 2295435 2906543 := bstep (se 1 (by rfl) ⟨2179907, by rfl⟩ : syracuseStep 2906543 = 4359815) B4359815
theorem B7750781 : Blo 2295435 7750781 := bstep (se 3 (by rfl) ⟨1453271, by rfl⟩ : syracuseStep 7750781 = 2906543) B2906543
theorem B5167187 : Blo 2295435 5167187 := bstep (se 1 (by rfl) ⟨3875390, by rfl⟩ : syracuseStep 5167187 = 7750781) B7750781
theorem B3444791 : Blo 2295435 3444791 := bstep (se 1 (by rfl) ⟨2583593, by rfl⟩ : syracuseStep 3444791 = 5167187) B5167187
theorem B2296527 : Blo 2295435 2296527 := bstep (se 1 (by rfl) ⟨1722395, by rfl⟩ : syracuseStep 2296527 = 3444791) B3444791
theorem B3444797 : Blo 2295435 3444797 := bbase (se 3 (by rfl) ⟨645899, by rfl⟩ : syracuseStep 3444797 = 1291799) (by norm_num)
theorem B2296531 : Blo 2295435 2296531 := bstep (se 1 (by rfl) ⟨1722398, by rfl⟩ : syracuseStep 2296531 = 3444797) B3444797
theorem B5167205 : Blo 2295435 5167205 := bbase (se 4 (by rfl) ⟨484425, by rfl⟩ : syracuseStep 5167205 = 968851) (by norm_num)
theorem B3444803 : Blo 2295435 3444803 := bstep (se 1 (by rfl) ⟨2583602, by rfl⟩ : syracuseStep 3444803 = 5167205) B5167205
theorem B2296535 : Blo 2295435 2296535 := bstep (se 1 (by rfl) ⟨1722401, by rfl⟩ : syracuseStep 2296535 = 3444803) B3444803
theorem B5813117 : Blo 2295435 5813117 := bbase (se 3 (by rfl) ⟨1089959, by rfl⟩ : syracuseStep 5813117 = 2179919) (by norm_num)
theorem B3875411 : Blo 2295435 3875411 := bstep (se 1 (by rfl) ⟨2906558, by rfl⟩ : syracuseStep 3875411 = 5813117) B5813117
theorem B2583607 : Blo 2295435 2583607 := bstep (se 1 (by rfl) ⟨1937705, by rfl⟩ : syracuseStep 2583607 = 3875411) B3875411
theorem B3444809 : Blo 2295435 3444809 := bstep (se 2 (by rfl) ⟨1291803, by rfl⟩ : syracuseStep 3444809 = 2583607) B2583607
theorem B2296539 : Blo 2295435 2296539 := bstep (se 1 (by rfl) ⟨1722404, by rfl⟩ : syracuseStep 2296539 = 3444809) B3444809
theorem B4359845 : Blo 2295435 4359845 := bbase (se 4 (by rfl) ⟨408735, by rfl⟩ : syracuseStep 4359845 = 817471) (by norm_num)
theorem B11626253 : Blo 2295435 11626253 := bstep (se 3 (by rfl) ⟨2179922, by rfl⟩ : syracuseStep 11626253 = 4359845) B4359845
theorem B7750835 : Blo 2295435 7750835 := bstep (se 1 (by rfl) ⟨5813126, by rfl⟩ : syracuseStep 7750835 = 11626253) B11626253
theorem B5167223 : Blo 2295435 5167223 := bstep (se 1 (by rfl) ⟨3875417, by rfl⟩ : syracuseStep 5167223 = 7750835) B7750835
theorem B3444815 : Blo 2295435 3444815 := bstep (se 1 (by rfl) ⟨2583611, by rfl⟩ : syracuseStep 3444815 = 5167223) B5167223
theorem B2296543 : Blo 2295435 2296543 := bstep (se 1 (by rfl) ⟨1722407, by rfl⟩ : syracuseStep 2296543 = 3444815) B3444815
theorem B3444821 : Blo 2295435 3444821 := bbase (se 8 (by rfl) ⟨20184, by rfl⟩ : syracuseStep 3444821 = 40369) (by norm_num)
theorem B2296547 : Blo 2295435 2296547 := bstep (se 1 (by rfl) ⟨1722410, by rfl⟩ : syracuseStep 2296547 = 3444821) B3444821
theorem B22071797 : Blo 2295435 22071797 := bbase (se 5 (by rfl) ⟨1034615, by rfl⟩ : syracuseStep 22071797 = 2069231) (by norm_num)
theorem B14714531 : Blo 2295435 14714531 := bstep (se 1 (by rfl) ⟨11035898, by rfl⟩ : syracuseStep 14714531 = 22071797) B22071797
theorem B9809687 : Blo 2295435 9809687 := bstep (se 1 (by rfl) ⟨7357265, by rfl⟩ : syracuseStep 9809687 = 14714531) B14714531
theorem B6539791 : Blo 2295435 6539791 := bstep (se 1 (by rfl) ⟨4904843, by rfl⟩ : syracuseStep 6539791 = 9809687) B9809687
theorem B8719721 : Blo 2295435 8719721 := bstep (se 2 (by rfl) ⟨3269895, by rfl⟩ : syracuseStep 8719721 = 6539791) B6539791
theorem B5813147 : Blo 2295435 5813147 := bstep (se 1 (by rfl) ⟨4359860, by rfl⟩ : syracuseStep 5813147 = 8719721) B8719721
theorem B3875431 : Blo 2295435 3875431 := bstep (se 1 (by rfl) ⟨2906573, by rfl⟩ : syracuseStep 3875431 = 5813147) B5813147
theorem B5167241 : Blo 2295435 5167241 := bstep (se 2 (by rfl) ⟨1937715, by rfl⟩ : syracuseStep 5167241 = 3875431) B3875431
theorem B3444827 : Blo 2295435 3444827 := bstep (se 1 (by rfl) ⟨2583620, by rfl⟩ : syracuseStep 3444827 = 5167241) B5167241
theorem B2296551 : Blo 2295435 2296551 := bstep (se 1 (by rfl) ⟨1722413, by rfl⟩ : syracuseStep 2296551 = 3444827) B3444827
theorem B2583625 : Blo 2295435 2583625 := bbase (se 2 (by rfl) ⟨968859, by rfl⟩ : syracuseStep 2583625 = 1937719) (by norm_num)
theorem B3444833 : Blo 2295435 3444833 := bstep (se 2 (by rfl) ⟨1291812, by rfl⟩ : syracuseStep 3444833 = 2583625) B2583625
theorem B2296555 : Blo 2295435 2296555 := bstep (se 1 (by rfl) ⟨1722416, by rfl⟩ : syracuseStep 2296555 = 3444833) B3444833
theorem B14714581 : Blo 2295435 14714581 := bbase (se 7 (by rfl) ⟨172436, by rfl⟩ : syracuseStep 14714581 = 344873) (by norm_num)
theorem B19619441 : Blo 2295435 19619441 := bstep (se 2 (by rfl) ⟨7357290, by rfl⟩ : syracuseStep 19619441 = 14714581) B14714581
theorem B13079627 : Blo 2295435 13079627 := bstep (se 1 (by rfl) ⟨9809720, by rfl⟩ : syracuseStep 13079627 = 19619441) B19619441
theorem B8719751 : Blo 2295435 8719751 := bstep (se 1 (by rfl) ⟨6539813, by rfl⟩ : syracuseStep 8719751 = 13079627) B13079627
theorem B5813167 : Blo 2295435 5813167 := bstep (se 1 (by rfl) ⟨4359875, by rfl⟩ : syracuseStep 5813167 = 8719751) B8719751
theorem B7750889 : Blo 2295435 7750889 := bstep (se 2 (by rfl) ⟨2906583, by rfl⟩ : syracuseStep 7750889 = 5813167) B5813167
theorem B5167259 : Blo 2295435 5167259 := bstep (se 1 (by rfl) ⟨3875444, by rfl⟩ : syracuseStep 5167259 = 7750889) B7750889
theorem B3444839 : Blo 2295435 3444839 := bstep (se 1 (by rfl) ⟨2583629, by rfl⟩ : syracuseStep 3444839 = 5167259) B5167259
theorem B2296559 : Blo 2295435 2296559 := bstep (se 1 (by rfl) ⟨1722419, by rfl⟩ : syracuseStep 2296559 = 3444839) B3444839
theorem B3444845 : Blo 2295435 3444845 := bbase (se 3 (by rfl) ⟨645908, by rfl⟩ : syracuseStep 3444845 = 1291817) (by norm_num)
theorem B2296563 : Blo 2295435 2296563 := bstep (se 1 (by rfl) ⟨1722422, by rfl⟩ : syracuseStep 2296563 = 3444845) B3444845
theorem B5167277 : Blo 2295435 5167277 := bbase (se 3 (by rfl) ⟨968864, by rfl⟩ : syracuseStep 5167277 = 1937729) (by norm_num)
theorem B3444851 : Blo 2295435 3444851 := bstep (se 1 (by rfl) ⟨2583638, by rfl⟩ : syracuseStep 3444851 = 5167277) B5167277
theorem B2296567 : Blo 2295435 2296567 := bstep (se 1 (by rfl) ⟨1722425, by rfl⟩ : syracuseStep 2296567 = 3444851) B3444851
theorem B6207749 : Blo 2295435 6207749 := bbase (se 4 (by rfl) ⟨581976, by rfl⟩ : syracuseStep 6207749 = 1163953) (by norm_num)
theorem B4138499 : Blo 2295435 4138499 := bstep (se 1 (by rfl) ⟨3103874, by rfl⟩ : syracuseStep 4138499 = 6207749) B6207749
theorem B11035997 : Blo 2295435 11035997 := bstep (se 3 (by rfl) ⟨2069249, by rfl⟩ : syracuseStep 11035997 = 4138499) B4138499
theorem B7357331 : Blo 2295435 7357331 := bstep (se 1 (by rfl) ⟨5517998, by rfl⟩ : syracuseStep 7357331 = 11035997) B11035997
theorem B4904887 : Blo 2295435 4904887 := bstep (se 1 (by rfl) ⟨3678665, by rfl⟩ : syracuseStep 4904887 = 7357331) B7357331
theorem B6539849 : Blo 2295435 6539849 := bstep (se 2 (by rfl) ⟨2452443, by rfl⟩ : syracuseStep 6539849 = 4904887) B4904887
theorem B4359899 : Blo 2295435 4359899 := bstep (se 1 (by rfl) ⟨3269924, by rfl⟩ : syracuseStep 4359899 = 6539849) B6539849
theorem B2906599 : Blo 2295435 2906599 := bstep (se 1 (by rfl) ⟨2179949, by rfl⟩ : syracuseStep 2906599 = 4359899) B4359899
theorem B3875465 : Blo 2295435 3875465 := bstep (se 2 (by rfl) ⟨1453299, by rfl⟩ : syracuseStep 3875465 = 2906599) B2906599
theorem B2583643 : Blo 2295435 2583643 := bstep (se 1 (by rfl) ⟨1937732, by rfl⟩ : syracuseStep 2583643 = 3875465) B3875465
theorem B3444857 : Blo 2295435 3444857 := bstep (se 2 (by rfl) ⟨1291821, by rfl⟩ : syracuseStep 3444857 = 2583643) B2583643
theorem B2296571 : Blo 2295435 2296571 := bstep (se 1 (by rfl) ⟨1722428, by rfl⟩ : syracuseStep 2296571 = 3444857) B3444857
theorem B5237797 : Blo 2295435 5237797 := bbase (se 4 (by rfl) ⟨491043, by rfl⟩ : syracuseStep 5237797 = 982087) (by norm_num)
theorem B6983729 : Blo 2295435 6983729 := bstep (se 2 (by rfl) ⟨2618898, by rfl⟩ : syracuseStep 6983729 = 5237797) B5237797
theorem B4655819 : Blo 2295435 4655819 := bstep (se 1 (by rfl) ⟨3491864, by rfl⟩ : syracuseStep 4655819 = 6983729) B6983729
theorem B3103879 : Blo 2295435 3103879 := bstep (se 1 (by rfl) ⟨2327909, by rfl⟩ : syracuseStep 3103879 = 4655819) B4655819
theorem B4138505 : Blo 2295435 4138505 := bstep (se 2 (by rfl) ⟨1551939, by rfl⟩ : syracuseStep 4138505 = 3103879) B3103879
theorem B2759003 : Blo 2295435 2759003 := bstep (se 1 (by rfl) ⟨2069252, by rfl⟩ : syracuseStep 2759003 = 4138505) B4138505
theorem B29429365 : Blo 2295435 29429365 := bstep (se 5 (by rfl) ⟨1379501, by rfl⟩ : syracuseStep 29429365 = 2759003) B2759003
theorem B39239153 : Blo 2295435 39239153 := bstep (se 2 (by rfl) ⟨14714682, by rfl⟩ : syracuseStep 39239153 = 29429365) B29429365
theorem B26159435 : Blo 2295435 26159435 := bstep (se 1 (by rfl) ⟨19619576, by rfl⟩ : syracuseStep 26159435 = 39239153) B39239153
theorem B17439623 : Blo 2295435 17439623 := bstep (se 1 (by rfl) ⟨13079717, by rfl⟩ : syracuseStep 17439623 = 26159435) B26159435
theorem B11626415 : Blo 2295435 11626415 := bstep (se 1 (by rfl) ⟨8719811, by rfl⟩ : syracuseStep 11626415 = 17439623) B17439623
theorem B7750943 : Blo 2295435 7750943 := bstep (se 1 (by rfl) ⟨5813207, by rfl⟩ : syracuseStep 7750943 = 11626415) B11626415
theorem B5167295 : Blo 2295435 5167295 := bstep (se 1 (by rfl) ⟨3875471, by rfl⟩ : syracuseStep 5167295 = 7750943) B7750943
theorem B3444863 : Blo 2295435 3444863 := bstep (se 1 (by rfl) ⟨2583647, by rfl⟩ : syracuseStep 3444863 = 5167295) B5167295
theorem B2296575 : Blo 2295435 2296575 := bstep (se 1 (by rfl) ⟨1722431, by rfl⟩ : syracuseStep 2296575 = 3444863) B3444863
theorem B3444869 : Blo 2295435 3444869 := bbase (se 4 (by rfl) ⟨322956, by rfl⟩ : syracuseStep 3444869 = 645913) (by norm_num)
theorem B2296579 : Blo 2295435 2296579 := bstep (se 1 (by rfl) ⟨1722434, by rfl⟩ : syracuseStep 2296579 = 3444869) B3444869
theorem B3875485 : Blo 2295435 3875485 := bbase (se 3 (by rfl) ⟨726653, by rfl⟩ : syracuseStep 3875485 = 1453307) (by norm_num)
theorem B5167313 : Blo 2295435 5167313 := bstep (se 2 (by rfl) ⟨1937742, by rfl⟩ : syracuseStep 5167313 = 3875485) B3875485
theorem B3444875 : Blo 2295435 3444875 := bstep (se 1 (by rfl) ⟨2583656, by rfl⟩ : syracuseStep 3444875 = 5167313) B5167313
theorem B2296583 : Blo 2295435 2296583 := bstep (se 1 (by rfl) ⟨1722437, by rfl⟩ : syracuseStep 2296583 = 3444875) B3444875
theorem B2583661 : Blo 2295435 2583661 := bbase (se 3 (by rfl) ⟨484436, by rfl⟩ : syracuseStep 2583661 = 968873) (by norm_num)
theorem B3444881 : Blo 2295435 3444881 := bstep (se 2 (by rfl) ⟨1291830, by rfl⟩ : syracuseStep 3444881 = 2583661) B2583661
theorem B2296587 : Blo 2295435 2296587 := bstep (se 1 (by rfl) ⟨1722440, by rfl⟩ : syracuseStep 2296587 = 3444881) B3444881
theorem B7750997 : Blo 2295435 7750997 := bbase (se 12 (by rfl) ⟨2838, by rfl⟩ : syracuseStep 7750997 = 5677) (by norm_num)
theorem B5167331 : Blo 2295435 5167331 := bstep (se 1 (by rfl) ⟨3875498, by rfl⟩ : syracuseStep 5167331 = 7750997) B7750997
theorem B3444887 : Blo 2295435 3444887 := bstep (se 1 (by rfl) ⟨2583665, by rfl⟩ : syracuseStep 3444887 = 5167331) B5167331
theorem B2296591 : Blo 2295435 2296591 := bstep (se 1 (by rfl) ⟨1722443, by rfl⟩ : syracuseStep 2296591 = 3444887) B3444887
theorem B3444893 : Blo 2295435 3444893 := bbase (se 3 (by rfl) ⟨645917, by rfl⟩ : syracuseStep 3444893 = 1291835) (by norm_num)
theorem B2296595 : Blo 2295435 2296595 := bstep (se 1 (by rfl) ⟨1722446, by rfl⟩ : syracuseStep 2296595 = 3444893) B3444893
theorem B5167349 : Blo 2295435 5167349 := bbase (se 5 (by rfl) ⟨242219, by rfl⟩ : syracuseStep 5167349 = 484439) (by norm_num)
theorem B3444899 : Blo 2295435 3444899 := bstep (se 1 (by rfl) ⟨2583674, by rfl⟩ : syracuseStep 3444899 = 5167349) B5167349
theorem B2296599 : Blo 2295435 2296599 := bstep (se 1 (by rfl) ⟨1722449, by rfl⟩ : syracuseStep 2296599 = 3444899) B3444899
theorem B18877589 : Blo 2295435 18877589 := bbase (se 6 (by rfl) ⟨442443, by rfl⟩ : syracuseStep 18877589 = 884887) (by norm_num)
theorem B12585059 : Blo 2295435 12585059 := bstep (se 1 (by rfl) ⟨9438794, by rfl⟩ : syracuseStep 12585059 = 18877589) B18877589
theorem B8390039 : Blo 2295435 8390039 := bstep (se 1 (by rfl) ⟨6292529, by rfl⟩ : syracuseStep 8390039 = 12585059) B12585059
theorem B89493749 : Blo 2295435 89493749 := bstep (se 5 (by rfl) ⟨4195019, by rfl⟩ : syracuseStep 89493749 = 8390039) B8390039
theorem B59662499 : Blo 2295435 59662499 := bstep (se 1 (by rfl) ⟨44746874, by rfl⟩ : syracuseStep 59662499 = 89493749) B89493749
theorem B159099997 : Blo 2295435 159099997 := bstep (se 3 (by rfl) ⟨29831249, by rfl⟩ : syracuseStep 159099997 = 59662499) B59662499
theorem B212133329 : Blo 2295435 212133329 := bstep (se 2 (by rfl) ⟨79549998, by rfl⟩ : syracuseStep 212133329 = 159099997) B159099997
theorem B141422219 : Blo 2295435 141422219 := bstep (se 1 (by rfl) ⟨106066664, by rfl⟩ : syracuseStep 141422219 = 212133329) B212133329
theorem B94281479 : Blo 2295435 94281479 := bstep (se 1 (by rfl) ⟨70711109, by rfl⟩ : syracuseStep 94281479 = 141422219) B141422219
theorem B62854319 : Blo 2295435 62854319 := bstep (se 1 (by rfl) ⟨47140739, by rfl⟩ : syracuseStep 62854319 = 94281479) B94281479
theorem B41902879 : Blo 2295435 41902879 := bstep (se 1 (by rfl) ⟨31427159, by rfl⟩ : syracuseStep 41902879 = 62854319) B62854319
theorem B55870505 : Blo 2295435 55870505 := bstep (se 2 (by rfl) ⟨20951439, by rfl⟩ : syracuseStep 55870505 = 41902879) B41902879
theorem B37247003 : Blo 2295435 37247003 := bstep (se 1 (by rfl) ⟨27935252, by rfl⟩ : syracuseStep 37247003 = 55870505) B55870505
theorem B24831335 : Blo 2295435 24831335 := bstep (se 1 (by rfl) ⟨18623501, by rfl⟩ : syracuseStep 24831335 = 37247003) B37247003
theorem B16554223 : Blo 2295435 16554223 := bstep (se 1 (by rfl) ⟨12415667, by rfl⟩ : syracuseStep 16554223 = 24831335) B24831335
theorem B22072297 : Blo 2295435 22072297 := bstep (se 2 (by rfl) ⟨8277111, by rfl⟩ : syracuseStep 22072297 = 16554223) B16554223
theorem B29429729 : Blo 2295435 29429729 := bstep (se 2 (by rfl) ⟨11036148, by rfl⟩ : syracuseStep 29429729 = 22072297) B22072297
theorem B19619819 : Blo 2295435 19619819 := bstep (se 1 (by rfl) ⟨14714864, by rfl⟩ : syracuseStep 19619819 = 29429729) B29429729
theorem B13079879 : Blo 2295435 13079879 := bstep (se 1 (by rfl) ⟨9809909, by rfl⟩ : syracuseStep 13079879 = 19619819) B19619819
theorem B8719919 : Blo 2295435 8719919 := bstep (se 1 (by rfl) ⟨6539939, by rfl⟩ : syracuseStep 8719919 = 13079879) B13079879
theorem B5813279 : Blo 2295435 5813279 := bstep (se 1 (by rfl) ⟨4359959, by rfl⟩ : syracuseStep 5813279 = 8719919) B8719919
theorem B3875519 : Blo 2295435 3875519 := bstep (se 1 (by rfl) ⟨2906639, by rfl⟩ : syracuseStep 3875519 = 5813279) B5813279
theorem B2583679 : Blo 2295435 2583679 := bstep (se 1 (by rfl) ⟨1937759, by rfl⟩ : syracuseStep 2583679 = 3875519) B3875519
theorem B3444905 : Blo 2295435 3444905 := bstep (se 2 (by rfl) ⟨1291839, by rfl⟩ : syracuseStep 3444905 = 2583679) B2583679
theorem B2296603 : Blo 2295435 2296603 := bstep (se 1 (by rfl) ⟨1722452, by rfl⟩ : syracuseStep 2296603 = 3444905) B3444905
theorem B7357445 : Blo 2295435 7357445 := bbase (se 4 (by rfl) ⟨689760, by rfl⟩ : syracuseStep 7357445 = 1379521) (by norm_num)
theorem B4904963 : Blo 2295435 4904963 := bstep (se 1 (by rfl) ⟨3678722, by rfl⟩ : syracuseStep 4904963 = 7357445) B7357445
theorem B3269975 : Blo 2295435 3269975 := bstep (se 1 (by rfl) ⟨2452481, by rfl⟩ : syracuseStep 3269975 = 4904963) B4904963
theorem B8719933 : Blo 2295435 8719933 := bstep (se 3 (by rfl) ⟨1634987, by rfl⟩ : syracuseStep 8719933 = 3269975) B3269975
theorem B11626577 : Blo 2295435 11626577 := bstep (se 2 (by rfl) ⟨4359966, by rfl⟩ : syracuseStep 11626577 = 8719933) B8719933
theorem B7751051 : Blo 2295435 7751051 := bstep (se 1 (by rfl) ⟨5813288, by rfl⟩ : syracuseStep 7751051 = 11626577) B11626577
theorem B5167367 : Blo 2295435 5167367 := bstep (se 1 (by rfl) ⟨3875525, by rfl⟩ : syracuseStep 5167367 = 7751051) B7751051
theorem B3444911 : Blo 2295435 3444911 := bstep (se 1 (by rfl) ⟨2583683, by rfl⟩ : syracuseStep 3444911 = 5167367) B5167367
theorem B2296607 : Blo 2295435 2296607 := bstep (se 1 (by rfl) ⟨1722455, by rfl⟩ : syracuseStep 2296607 = 3444911) B3444911
theorem B3444917 : Blo 2295435 3444917 := bbase (se 5 (by rfl) ⟨161480, by rfl⟩ : syracuseStep 3444917 = 322961) (by norm_num)
theorem B2296611 : Blo 2295435 2296611 := bstep (se 1 (by rfl) ⟨1722458, by rfl⟩ : syracuseStep 2296611 = 3444917) B3444917
theorem B5813309 : Blo 2295435 5813309 := bbase (se 3 (by rfl) ⟨1089995, by rfl⟩ : syracuseStep 5813309 = 2179991) (by norm_num)
theorem B3875539 : Blo 2295435 3875539 := bstep (se 1 (by rfl) ⟨2906654, by rfl⟩ : syracuseStep 3875539 = 5813309) B5813309
theorem B5167385 : Blo 2295435 5167385 := bstep (se 2 (by rfl) ⟨1937769, by rfl⟩ : syracuseStep 5167385 = 3875539) B3875539
theorem B3444923 : Blo 2295435 3444923 := bstep (se 1 (by rfl) ⟨2583692, by rfl⟩ : syracuseStep 3444923 = 5167385) B5167385
theorem B2296615 : Blo 2295435 2296615 := bstep (se 1 (by rfl) ⟨1722461, by rfl⟩ : syracuseStep 2296615 = 3444923) B3444923
theorem B2583697 : Blo 2295435 2583697 := bbase (se 2 (by rfl) ⟨968886, by rfl⟩ : syracuseStep 2583697 = 1937773) (by norm_num)
theorem B3444929 : Blo 2295435 3444929 := bstep (se 2 (by rfl) ⟨1291848, by rfl⟩ : syracuseStep 3444929 = 2583697) B2583697
theorem B2296619 : Blo 2295435 2296619 := bstep (se 1 (by rfl) ⟨1722464, by rfl⟩ : syracuseStep 2296619 = 3444929) B3444929
theorem B4359997 : Blo 2295435 4359997 := bbase (se 3 (by rfl) ⟨817499, by rfl⟩ : syracuseStep 4359997 = 1634999) (by norm_num)
theorem B5813329 : Blo 2295435 5813329 := bstep (se 2 (by rfl) ⟨2179998, by rfl⟩ : syracuseStep 5813329 = 4359997) B4359997
theorem B7751105 : Blo 2295435 7751105 := bstep (se 2 (by rfl) ⟨2906664, by rfl⟩ : syracuseStep 7751105 = 5813329) B5813329
theorem B5167403 : Blo 2295435 5167403 := bstep (se 1 (by rfl) ⟨3875552, by rfl⟩ : syracuseStep 5167403 = 7751105) B7751105
theorem B3444935 : Blo 2295435 3444935 := bstep (se 1 (by rfl) ⟨2583701, by rfl⟩ : syracuseStep 3444935 = 5167403) B5167403
theorem B2296623 : Blo 2295435 2296623 := bstep (se 1 (by rfl) ⟨1722467, by rfl⟩ : syracuseStep 2296623 = 3444935) B3444935
theorem B3444941 : Blo 2295435 3444941 := bbase (se 3 (by rfl) ⟨645926, by rfl⟩ : syracuseStep 3444941 = 1291853) (by norm_num)
theorem B2296627 : Blo 2295435 2296627 := bstep (se 1 (by rfl) ⟨1722470, by rfl⟩ : syracuseStep 2296627 = 3444941) B3444941
theorem B5167421 : Blo 2295435 5167421 := bbase (se 3 (by rfl) ⟨968891, by rfl⟩ : syracuseStep 5167421 = 1937783) (by norm_num)
theorem B3444947 : Blo 2295435 3444947 := bstep (se 1 (by rfl) ⟨2583710, by rfl⟩ : syracuseStep 3444947 = 5167421) B5167421
theorem B2296631 : Blo 2295435 2296631 := bstep (se 1 (by rfl) ⟨1722473, by rfl⟩ : syracuseStep 2296631 = 3444947) B3444947
theorem B3875573 : Blo 2295435 3875573 := bbase (se 5 (by rfl) ⟨181667, by rfl⟩ : syracuseStep 3875573 = 363335) (by norm_num)
theorem B2583715 : Blo 2295435 2583715 := bstep (se 1 (by rfl) ⟨1937786, by rfl⟩ : syracuseStep 2583715 = 3875573) B3875573
theorem B3444953 : Blo 2295435 3444953 := bstep (se 2 (by rfl) ⟨1291857, by rfl⟩ : syracuseStep 3444953 = 2583715) B2583715
theorem B2296635 : Blo 2295435 2296635 := bstep (se 1 (by rfl) ⟨1722476, by rfl⟩ : syracuseStep 2296635 = 3444953) B3444953
theorem B2796725 : Blo 2295435 2796725 := bbase (se 5 (by rfl) ⟨131096, by rfl⟩ : syracuseStep 2796725 = 262193) (by norm_num)
theorem B7457933 : Blo 2295435 7457933 := bstep (se 3 (by rfl) ⟨1398362, by rfl⟩ : syracuseStep 7457933 = 2796725) B2796725
theorem B4971955 : Blo 2295435 4971955 := bstep (se 1 (by rfl) ⟨3728966, by rfl⟩ : syracuseStep 4971955 = 7457933) B7457933
theorem B6629273 : Blo 2295435 6629273 := bstep (se 2 (by rfl) ⟨2485977, by rfl⟩ : syracuseStep 6629273 = 4971955) B4971955
theorem B4419515 : Blo 2295435 4419515 := bstep (se 1 (by rfl) ⟨3314636, by rfl⟩ : syracuseStep 4419515 = 6629273) B6629273
theorem B2946343 : Blo 2295435 2946343 := bstep (se 1 (by rfl) ⟨2209757, by rfl⟩ : syracuseStep 2946343 = 4419515) B4419515
theorem B3928457 : Blo 2295435 3928457 := bstep (se 2 (by rfl) ⟨1473171, by rfl⟩ : syracuseStep 3928457 = 2946343) B2946343
theorem B10475885 : Blo 2295435 10475885 := bstep (se 3 (by rfl) ⟨1964228, by rfl⟩ : syracuseStep 10475885 = 3928457) B3928457
theorem B6983923 : Blo 2295435 6983923 := bstep (se 1 (by rfl) ⟨5237942, by rfl⟩ : syracuseStep 6983923 = 10475885) B10475885
theorem B9311897 : Blo 2295435 9311897 := bstep (se 2 (by rfl) ⟨3491961, by rfl⟩ : syracuseStep 9311897 = 6983923) B6983923
theorem B6207931 : Blo 2295435 6207931 := bstep (se 1 (by rfl) ⟨4655948, by rfl⟩ : syracuseStep 6207931 = 9311897) B9311897
theorem B8277241 : Blo 2295435 8277241 := bstep (se 2 (by rfl) ⟨3103965, by rfl⟩ : syracuseStep 8277241 = 6207931) B6207931
theorem B11036321 : Blo 2295435 11036321 := bstep (se 2 (by rfl) ⟨4138620, by rfl⟩ : syracuseStep 11036321 = 8277241) B8277241
theorem B7357547 : Blo 2295435 7357547 := bstep (se 1 (by rfl) ⟨5518160, by rfl⟩ : syracuseStep 7357547 = 11036321) B11036321
theorem B4905031 : Blo 2295435 4905031 := bstep (se 1 (by rfl) ⟨3678773, by rfl⟩ : syracuseStep 4905031 = 7357547) B7357547
theorem B6540041 : Blo 2295435 6540041 := bstep (se 2 (by rfl) ⟨2452515, by rfl⟩ : syracuseStep 6540041 = 4905031) B4905031
theorem B17440109 : Blo 2295435 17440109 := bstep (se 3 (by rfl) ⟨3270020, by rfl⟩ : syracuseStep 17440109 = 6540041) B6540041
theorem B11626739 : Blo 2295435 11626739 := bstep (se 1 (by rfl) ⟨8720054, by rfl⟩ : syracuseStep 11626739 = 17440109) B17440109
theorem B7751159 : Blo 2295435 7751159 := bstep (se 1 (by rfl) ⟨5813369, by rfl⟩ : syracuseStep 7751159 = 11626739) B11626739
theorem B5167439 : Blo 2295435 5167439 := bstep (se 1 (by rfl) ⟨3875579, by rfl⟩ : syracuseStep 5167439 = 7751159) B7751159
theorem B3444959 : Blo 2295435 3444959 := bstep (se 1 (by rfl) ⟨2583719, by rfl⟩ : syracuseStep 3444959 = 5167439) B5167439
theorem B2296639 : Blo 2295435 2296639 := bstep (se 1 (by rfl) ⟨1722479, by rfl⟩ : syracuseStep 2296639 = 3444959) B3444959
theorem B3444965 : Blo 2295435 3444965 := bbase (se 4 (by rfl) ⟨322965, by rfl⟩ : syracuseStep 3444965 = 645931) (by norm_num)
theorem B2296643 : Blo 2295435 2296643 := bstep (se 1 (by rfl) ⟨1722482, by rfl⟩ : syracuseStep 2296643 = 3444965) B3444965
theorem B5518181 : Blo 2295435 5518181 := bbase (se 4 (by rfl) ⟨517329, by rfl⟩ : syracuseStep 5518181 = 1034659) (by norm_num)
theorem B3678787 : Blo 2295435 3678787 := bstep (se 1 (by rfl) ⟨2759090, by rfl⟩ : syracuseStep 3678787 = 5518181) B5518181
theorem B4905049 : Blo 2295435 4905049 := bstep (se 2 (by rfl) ⟨1839393, by rfl⟩ : syracuseStep 4905049 = 3678787) B3678787
theorem B6540065 : Blo 2295435 6540065 := bstep (se 2 (by rfl) ⟨2452524, by rfl⟩ : syracuseStep 6540065 = 4905049) B4905049
theorem B4360043 : Blo 2295435 4360043 := bstep (se 1 (by rfl) ⟨3270032, by rfl⟩ : syracuseStep 4360043 = 6540065) B6540065
theorem B2906695 : Blo 2295435 2906695 := bstep (se 1 (by rfl) ⟨2180021, by rfl⟩ : syracuseStep 2906695 = 4360043) B4360043
theorem B3875593 : Blo 2295435 3875593 := bstep (se 2 (by rfl) ⟨1453347, by rfl⟩ : syracuseStep 3875593 = 2906695) B2906695
theorem B5167457 : Blo 2295435 5167457 := bstep (se 2 (by rfl) ⟨1937796, by rfl⟩ : syracuseStep 5167457 = 3875593) B3875593
theorem B3444971 : Blo 2295435 3444971 := bstep (se 1 (by rfl) ⟨2583728, by rfl⟩ : syracuseStep 3444971 = 5167457) B5167457
theorem B2296647 : Blo 2295435 2296647 := bstep (se 1 (by rfl) ⟨1722485, by rfl⟩ : syracuseStep 2296647 = 3444971) B3444971
theorem B2583733 : Blo 2295435 2583733 := bbase (se 5 (by rfl) ⟨121112, by rfl⟩ : syracuseStep 2583733 = 242225) (by norm_num)
theorem B3444977 : Blo 2295435 3444977 := bstep (se 2 (by rfl) ⟨1291866, by rfl⟩ : syracuseStep 3444977 = 2583733) B2583733
theorem B2296651 : Blo 2295435 2296651 := bstep (se 1 (by rfl) ⟨1722488, by rfl⟩ : syracuseStep 2296651 = 3444977) B3444977
theorem B2906705 : Blo 2295435 2906705 := bbase (se 2 (by rfl) ⟨1090014, by rfl⟩ : syracuseStep 2906705 = 2180029) (by norm_num)
theorem B7751213 : Blo 2295435 7751213 := bstep (se 3 (by rfl) ⟨1453352, by rfl⟩ : syracuseStep 7751213 = 2906705) B2906705
theorem B5167475 : Blo 2295435 5167475 := bstep (se 1 (by rfl) ⟨3875606, by rfl⟩ : syracuseStep 5167475 = 7751213) B7751213
theorem B3444983 : Blo 2295435 3444983 := bstep (se 1 (by rfl) ⟨2583737, by rfl⟩ : syracuseStep 3444983 = 5167475) B5167475
theorem B2296655 : Blo 2295435 2296655 := bstep (se 1 (by rfl) ⟨1722491, by rfl⟩ : syracuseStep 2296655 = 3444983) B3444983
theorem B3444989 : Blo 2295435 3444989 := bbase (se 3 (by rfl) ⟨645935, by rfl⟩ : syracuseStep 3444989 = 1291871) (by norm_num)
theorem B2296659 : Blo 2295435 2296659 := bstep (se 1 (by rfl) ⟨1722494, by rfl⟩ : syracuseStep 2296659 = 3444989) B3444989
theorem B5167493 : Blo 2295435 5167493 := bbase (se 4 (by rfl) ⟨484452, by rfl⟩ : syracuseStep 5167493 = 968905) (by norm_num)
theorem B3444995 : Blo 2295435 3444995 := bstep (se 1 (by rfl) ⟨2583746, by rfl⟩ : syracuseStep 3444995 = 5167493) B5167493
theorem B2296663 : Blo 2295435 2296663 := bstep (se 1 (by rfl) ⟨1722497, by rfl⟩ : syracuseStep 2296663 = 3444995) B3444995
theorem B3270061 : Blo 2295435 3270061 := bbase (se 3 (by rfl) ⟨613136, by rfl⟩ : syracuseStep 3270061 = 1226273) (by norm_num)
theorem B4360081 : Blo 2295435 4360081 := bstep (se 2 (by rfl) ⟨1635030, by rfl⟩ : syracuseStep 4360081 = 3270061) B3270061
theorem B5813441 : Blo 2295435 5813441 := bstep (se 2 (by rfl) ⟨2180040, by rfl⟩ : syracuseStep 5813441 = 4360081) B4360081
theorem B3875627 : Blo 2295435 3875627 := bstep (se 1 (by rfl) ⟨2906720, by rfl⟩ : syracuseStep 3875627 = 5813441) B5813441
theorem B2583751 : Blo 2295435 2583751 := bstep (se 1 (by rfl) ⟨1937813, by rfl⟩ : syracuseStep 2583751 = 3875627) B3875627
theorem B3445001 : Blo 2295435 3445001 := bstep (se 2 (by rfl) ⟨1291875, by rfl⟩ : syracuseStep 3445001 = 2583751) B2583751
theorem B2296667 : Blo 2295435 2296667 := bstep (se 1 (by rfl) ⟨1722500, by rfl⟩ : syracuseStep 2296667 = 3445001) B3445001
theorem B11626901 : Blo 2295435 11626901 := bbase (se 6 (by rfl) ⟨272505, by rfl⟩ : syracuseStep 11626901 = 545011) (by norm_num)
theorem B7751267 : Blo 2295435 7751267 := bstep (se 1 (by rfl) ⟨5813450, by rfl⟩ : syracuseStep 7751267 = 11626901) B11626901
theorem B5167511 : Blo 2295435 5167511 := bstep (se 1 (by rfl) ⟨3875633, by rfl⟩ : syracuseStep 5167511 = 7751267) B7751267
theorem B3445007 : Blo 2295435 3445007 := bstep (se 1 (by rfl) ⟨2583755, by rfl⟩ : syracuseStep 3445007 = 5167511) B5167511
theorem B2296671 : Blo 2295435 2296671 := bstep (se 1 (by rfl) ⟨1722503, by rfl⟩ : syracuseStep 2296671 = 3445007) B3445007
theorem B3445013 : Blo 2295435 3445013 := bbase (se 6 (by rfl) ⟨80742, by rfl⟩ : syracuseStep 3445013 = 161485) (by norm_num)
theorem B2296675 : Blo 2295435 2296675 := bstep (se 1 (by rfl) ⟨1722506, by rfl⟩ : syracuseStep 2296675 = 3445013) B3445013
theorem B15714101 : Blo 2295435 15714101 := bbase (se 5 (by rfl) ⟨736598, by rfl⟩ : syracuseStep 15714101 = 1473197) (by norm_num)
theorem B10476067 : Blo 2295435 10476067 := bstep (se 1 (by rfl) ⟨7857050, by rfl⟩ : syracuseStep 10476067 = 15714101) B15714101
theorem B13968089 : Blo 2295435 13968089 := bstep (se 2 (by rfl) ⟨5238033, by rfl⟩ : syracuseStep 13968089 = 10476067) B10476067
theorem B9312059 : Blo 2295435 9312059 := bstep (se 1 (by rfl) ⟨6984044, by rfl⟩ : syracuseStep 9312059 = 13968089) B13968089
theorem B6208039 : Blo 2295435 6208039 := bstep (se 1 (by rfl) ⟨4656029, by rfl⟩ : syracuseStep 6208039 = 9312059) B9312059
theorem B8277385 : Blo 2295435 8277385 := bstep (se 2 (by rfl) ⟨3104019, by rfl⟩ : syracuseStep 8277385 = 6208039) B6208039
theorem B11036513 : Blo 2295435 11036513 := bstep (se 2 (by rfl) ⟨4138692, by rfl⟩ : syracuseStep 11036513 = 8277385) B8277385
theorem B29430701 : Blo 2295435 29430701 := bstep (se 3 (by rfl) ⟨5518256, by rfl⟩ : syracuseStep 29430701 = 11036513) B11036513
theorem B19620467 : Blo 2295435 19620467 := bstep (se 1 (by rfl) ⟨14715350, by rfl⟩ : syracuseStep 19620467 = 29430701) B29430701
theorem B13080311 : Blo 2295435 13080311 := bstep (se 1 (by rfl) ⟨9810233, by rfl⟩ : syracuseStep 13080311 = 19620467) B19620467
theorem B8720207 : Blo 2295435 8720207 := bstep (se 1 (by rfl) ⟨6540155, by rfl⟩ : syracuseStep 8720207 = 13080311) B13080311
theorem B5813471 : Blo 2295435 5813471 := bstep (se 1 (by rfl) ⟨4360103, by rfl⟩ : syracuseStep 5813471 = 8720207) B8720207
theorem B3875647 : Blo 2295435 3875647 := bstep (se 1 (by rfl) ⟨2906735, by rfl⟩ : syracuseStep 3875647 = 5813471) B5813471
theorem B5167529 : Blo 2295435 5167529 := bstep (se 2 (by rfl) ⟨1937823, by rfl⟩ : syracuseStep 5167529 = 3875647) B3875647
theorem B3445019 : Blo 2295435 3445019 := bstep (se 1 (by rfl) ⟨2583764, by rfl⟩ : syracuseStep 3445019 = 5167529) B5167529
theorem B2296679 : Blo 2295435 2296679 := bstep (se 1 (by rfl) ⟨1722509, by rfl⟩ : syracuseStep 2296679 = 3445019) B3445019
theorem B2583769 : Blo 2295435 2583769 := bbase (se 2 (by rfl) ⟨968913, by rfl⟩ : syracuseStep 2583769 = 1937827) (by norm_num)
theorem B3445025 : Blo 2295435 3445025 := bstep (se 2 (by rfl) ⟨1291884, by rfl⟩ : syracuseStep 3445025 = 2583769) B2583769
theorem B2296683 : Blo 2295435 2296683 := bstep (se 1 (by rfl) ⟨1722512, by rfl⟩ : syracuseStep 2296683 = 3445025) B3445025
theorem B5518277 : Blo 2295435 5518277 := bbase (se 4 (by rfl) ⟨517338, by rfl⟩ : syracuseStep 5518277 = 1034677) (by norm_num)
theorem B3678851 : Blo 2295435 3678851 := bstep (se 1 (by rfl) ⟨2759138, by rfl⟩ : syracuseStep 3678851 = 5518277) B5518277
theorem B2452567 : Blo 2295435 2452567 := bstep (se 1 (by rfl) ⟨1839425, by rfl⟩ : syracuseStep 2452567 = 3678851) B3678851
theorem B3270089 : Blo 2295435 3270089 := bstep (se 2 (by rfl) ⟨1226283, by rfl⟩ : syracuseStep 3270089 = 2452567) B2452567
theorem B8720237 : Blo 2295435 8720237 := bstep (se 3 (by rfl) ⟨1635044, by rfl⟩ : syracuseStep 8720237 = 3270089) B3270089
theorem B5813491 : Blo 2295435 5813491 := bstep (se 1 (by rfl) ⟨4360118, by rfl⟩ : syracuseStep 5813491 = 8720237) B8720237
theorem B7751321 : Blo 2295435 7751321 := bstep (se 2 (by rfl) ⟨2906745, by rfl⟩ : syracuseStep 7751321 = 5813491) B5813491
theorem B5167547 : Blo 2295435 5167547 := bstep (se 1 (by rfl) ⟨3875660, by rfl⟩ : syracuseStep 5167547 = 7751321) B7751321
theorem B3445031 : Blo 2295435 3445031 := bstep (se 1 (by rfl) ⟨2583773, by rfl⟩ : syracuseStep 3445031 = 5167547) B5167547
theorem B2296687 : Blo 2295435 2296687 := bstep (se 1 (by rfl) ⟨1722515, by rfl⟩ : syracuseStep 2296687 = 3445031) B3445031
theorem B3445037 : Blo 2295435 3445037 := bbase (se 3 (by rfl) ⟨645944, by rfl⟩ : syracuseStep 3445037 = 1291889) (by norm_num)
theorem B2296691 : Blo 2295435 2296691 := bstep (se 1 (by rfl) ⟨1722518, by rfl⟩ : syracuseStep 2296691 = 3445037) B3445037
theorem B5167565 : Blo 2295435 5167565 := bbase (se 3 (by rfl) ⟨968918, by rfl⟩ : syracuseStep 5167565 = 1937837) (by norm_num)
theorem B3445043 : Blo 2295435 3445043 := bstep (se 1 (by rfl) ⟨2583782, by rfl⟩ : syracuseStep 3445043 = 5167565) B5167565
theorem B2296695 : Blo 2295435 2296695 := bstep (se 1 (by rfl) ⟨1722521, by rfl⟩ : syracuseStep 2296695 = 3445043) B3445043
theorem B2906761 : Blo 2295435 2906761 := bbase (se 2 (by rfl) ⟨1090035, by rfl⟩ : syracuseStep 2906761 = 2180071) (by norm_num)
theorem B3875681 : Blo 2295435 3875681 := bstep (se 2 (by rfl) ⟨1453380, by rfl⟩ : syracuseStep 3875681 = 2906761) B2906761
theorem B2583787 : Blo 2295435 2583787 := bstep (se 1 (by rfl) ⟨1937840, by rfl⟩ : syracuseStep 2583787 = 3875681) B3875681
theorem B3445049 : Blo 2295435 3445049 := bstep (se 2 (by rfl) ⟨1291893, by rfl⟩ : syracuseStep 3445049 = 2583787) B2583787
theorem B2296699 : Blo 2295435 2296699 := bstep (se 1 (by rfl) ⟨1722524, by rfl⟩ : syracuseStep 2296699 = 3445049) B3445049
theorem B2554345 : Blo 2295435 2554345 := bbase (se 2 (by rfl) ⟨957879, by rfl⟩ : syracuseStep 2554345 = 1915759) (by norm_num)
theorem B13623173 : Blo 2295435 13623173 := bstep (se 4 (by rfl) ⟨1277172, by rfl⟩ : syracuseStep 13623173 = 2554345) B2554345
theorem B9082115 : Blo 2295435 9082115 := bstep (se 1 (by rfl) ⟨6811586, by rfl⟩ : syracuseStep 9082115 = 13623173) B13623173
theorem B6054743 : Blo 2295435 6054743 := bstep (se 1 (by rfl) ⟨4541057, by rfl⟩ : syracuseStep 6054743 = 9082115) B9082115
theorem B16145981 : Blo 2295435 16145981 := bstep (se 3 (by rfl) ⟨3027371, by rfl⟩ : syracuseStep 16145981 = 6054743) B6054743
theorem B10763987 : Blo 2295435 10763987 := bstep (se 1 (by rfl) ⟨8072990, by rfl⟩ : syracuseStep 10763987 = 16145981) B16145981
theorem B28703965 : Blo 2295435 28703965 := bstep (se 3 (by rfl) ⟨5381993, by rfl⟩ : syracuseStep 28703965 = 10763987) B10763987
theorem B38271953 : Blo 2295435 38271953 := bstep (se 2 (by rfl) ⟨14351982, by rfl⟩ : syracuseStep 38271953 = 28703965) B28703965
theorem B102058541 : Blo 2295435 102058541 := bstep (se 3 (by rfl) ⟨19135976, by rfl⟩ : syracuseStep 102058541 = 38271953) B38271953
theorem B68039027 : Blo 2295435 68039027 := bstep (se 1 (by rfl) ⟨51029270, by rfl⟩ : syracuseStep 68039027 = 102058541) B102058541
theorem B45359351 : Blo 2295435 45359351 := bstep (se 1 (by rfl) ⟨34019513, by rfl⟩ : syracuseStep 45359351 = 68039027) B68039027
theorem B30239567 : Blo 2295435 30239567 := bstep (se 1 (by rfl) ⟨22679675, by rfl⟩ : syracuseStep 30239567 = 45359351) B45359351
theorem B20159711 : Blo 2295435 20159711 := bstep (se 1 (by rfl) ⟨15119783, by rfl⟩ : syracuseStep 20159711 = 30239567) B30239567
theorem B13439807 : Blo 2295435 13439807 := bstep (se 1 (by rfl) ⟨10079855, by rfl⟩ : syracuseStep 13439807 = 20159711) B20159711
theorem B8959871 : Blo 2295435 8959871 := bstep (se 1 (by rfl) ⟨6719903, by rfl⟩ : syracuseStep 8959871 = 13439807) B13439807
theorem B5973247 : Blo 2295435 5973247 := bstep (se 1 (by rfl) ⟨4479935, by rfl⟩ : syracuseStep 5973247 = 8959871) B8959871
theorem B7964329 : Blo 2295435 7964329 := bstep (se 2 (by rfl) ⟨2986623, by rfl⟩ : syracuseStep 7964329 = 5973247) B5973247
theorem B10619105 : Blo 2295435 10619105 := bstep (se 2 (by rfl) ⟨3982164, by rfl⟩ : syracuseStep 10619105 = 7964329) B7964329
theorem B28317613 : Blo 2295435 28317613 := bstep (se 3 (by rfl) ⟨5309552, by rfl⟩ : syracuseStep 28317613 = 10619105) B10619105
theorem B37756817 : Blo 2295435 37756817 := bstep (se 2 (by rfl) ⟨14158806, by rfl⟩ : syracuseStep 37756817 = 28317613) B28317613
theorem B25171211 : Blo 2295435 25171211 := bstep (se 1 (by rfl) ⟨18878408, by rfl⟩ : syracuseStep 25171211 = 37756817) B37756817
theorem B16780807 : Blo 2295435 16780807 := bstep (se 1 (by rfl) ⟨12585605, by rfl⟩ : syracuseStep 16780807 = 25171211) B25171211
theorem B22374409 : Blo 2295435 22374409 := bstep (se 2 (by rfl) ⟨8390403, by rfl⟩ : syracuseStep 22374409 = 16780807) B16780807
theorem B29832545 : Blo 2295435 29832545 := bstep (se 2 (by rfl) ⟨11187204, by rfl⟩ : syracuseStep 29832545 = 22374409) B22374409
theorem B19888363 : Blo 2295435 19888363 := bstep (se 1 (by rfl) ⟨14916272, by rfl⟩ : syracuseStep 19888363 = 29832545) B29832545
theorem B26517817 : Blo 2295435 26517817 := bstep (se 2 (by rfl) ⟨9944181, by rfl⟩ : syracuseStep 26517817 = 19888363) B19888363
theorem B35357089 : Blo 2295435 35357089 := bstep (se 2 (by rfl) ⟨13258908, by rfl⟩ : syracuseStep 35357089 = 26517817) B26517817
theorem B47142785 : Blo 2295435 47142785 := bstep (se 2 (by rfl) ⟨17678544, by rfl⟩ : syracuseStep 47142785 = 35357089) B35357089
theorem B31428523 : Blo 2295435 31428523 := bstep (se 1 (by rfl) ⟨23571392, by rfl⟩ : syracuseStep 31428523 = 47142785) B47142785
theorem B41904697 : Blo 2295435 41904697 := bstep (se 2 (by rfl) ⟨15714261, by rfl⟩ : syracuseStep 41904697 = 31428523) B31428523
theorem B55872929 : Blo 2295435 55872929 := bstep (se 2 (by rfl) ⟨20952348, by rfl⟩ : syracuseStep 55872929 = 41904697) B41904697
theorem B37248619 : Blo 2295435 37248619 := bstep (se 1 (by rfl) ⟨27936464, by rfl⟩ : syracuseStep 37248619 = 55872929) B55872929
theorem B49664825 : Blo 2295435 49664825 := bstep (se 2 (by rfl) ⟨18624309, by rfl⟩ : syracuseStep 49664825 = 37248619) B37248619
theorem B33109883 : Blo 2295435 33109883 := bstep (se 1 (by rfl) ⟨24832412, by rfl⟩ : syracuseStep 33109883 = 49664825) B49664825
theorem B22073255 : Blo 2295435 22073255 := bstep (se 1 (by rfl) ⟨16554941, by rfl⟩ : syracuseStep 22073255 = 33109883) B33109883
theorem B14715503 : Blo 2295435 14715503 := bstep (se 1 (by rfl) ⟨11036627, by rfl⟩ : syracuseStep 14715503 = 22073255) B22073255
theorem B9810335 : Blo 2295435 9810335 := bstep (se 1 (by rfl) ⟨7357751, by rfl⟩ : syracuseStep 9810335 = 14715503) B14715503
theorem B26160893 : Blo 2295435 26160893 := bstep (se 3 (by rfl) ⟨4905167, by rfl⟩ : syracuseStep 26160893 = 9810335) B9810335
theorem B17440595 : Blo 2295435 17440595 := bstep (se 1 (by rfl) ⟨13080446, by rfl⟩ : syracuseStep 17440595 = 26160893) B26160893
theorem B11627063 : Blo 2295435 11627063 := bstep (se 1 (by rfl) ⟨8720297, by rfl⟩ : syracuseStep 11627063 = 17440595) B17440595
theorem B7751375 : Blo 2295435 7751375 := bstep (se 1 (by rfl) ⟨5813531, by rfl⟩ : syracuseStep 7751375 = 11627063) B11627063
theorem B5167583 : Blo 2295435 5167583 := bstep (se 1 (by rfl) ⟨3875687, by rfl⟩ : syracuseStep 5167583 = 7751375) B7751375
theorem B3445055 : Blo 2295435 3445055 := bstep (se 1 (by rfl) ⟨2583791, by rfl⟩ : syracuseStep 3445055 = 5167583) B5167583
theorem B2296703 : Blo 2295435 2296703 := bstep (se 1 (by rfl) ⟨1722527, by rfl⟩ : syracuseStep 2296703 = 3445055) B3445055
theorem B3445061 : Blo 2295435 3445061 := bbase (se 4 (by rfl) ⟨322974, by rfl⟩ : syracuseStep 3445061 = 645949) (by norm_num)
theorem B2296707 : Blo 2295435 2296707 := bstep (se 1 (by rfl) ⟨1722530, by rfl⟩ : syracuseStep 2296707 = 3445061) B3445061
theorem B3875701 : Blo 2295435 3875701 := bbase (se 5 (by rfl) ⟨181673, by rfl⟩ : syracuseStep 3875701 = 363347) (by norm_num)
theorem B5167601 : Blo 2295435 5167601 := bstep (se 2 (by rfl) ⟨1937850, by rfl⟩ : syracuseStep 5167601 = 3875701) B3875701
theorem B3445067 : Blo 2295435 3445067 := bstep (se 1 (by rfl) ⟨2583800, by rfl⟩ : syracuseStep 3445067 = 5167601) B5167601
theorem B2296711 : Blo 2295435 2296711 := bstep (se 1 (by rfl) ⟨1722533, by rfl⟩ : syracuseStep 2296711 = 3445067) B3445067
theorem B2583805 : Blo 2295435 2583805 := bbase (se 3 (by rfl) ⟨484463, by rfl⟩ : syracuseStep 2583805 = 968927) (by norm_num)
theorem B3445073 : Blo 2295435 3445073 := bstep (se 2 (by rfl) ⟨1291902, by rfl⟩ : syracuseStep 3445073 = 2583805) B2583805
theorem B2296715 : Blo 2295435 2296715 := bstep (se 1 (by rfl) ⟨1722536, by rfl⟩ : syracuseStep 2296715 = 3445073) B3445073
theorem B7751429 : Blo 2295435 7751429 := bbase (se 4 (by rfl) ⟨726696, by rfl⟩ : syracuseStep 7751429 = 1453393) (by norm_num)
theorem B5167619 : Blo 2295435 5167619 := bstep (se 1 (by rfl) ⟨3875714, by rfl⟩ : syracuseStep 5167619 = 7751429) B7751429
theorem B3445079 : Blo 2295435 3445079 := bstep (se 1 (by rfl) ⟨2583809, by rfl⟩ : syracuseStep 3445079 = 5167619) B5167619
theorem B2296719 : Blo 2295435 2296719 := bstep (se 1 (by rfl) ⟨1722539, by rfl⟩ : syracuseStep 2296719 = 3445079) B3445079
theorem B3445085 : Blo 2295435 3445085 := bbase (se 3 (by rfl) ⟨645953, by rfl⟩ : syracuseStep 3445085 = 1291907) (by norm_num)
theorem B2296723 : Blo 2295435 2296723 := bstep (se 1 (by rfl) ⟨1722542, by rfl⟩ : syracuseStep 2296723 = 3445085) B3445085
theorem B5167637 : Blo 2295435 5167637 := bbase (se 6 (by rfl) ⟨121116, by rfl⟩ : syracuseStep 5167637 = 242233) (by norm_num)
theorem B3445091 : Blo 2295435 3445091 := bstep (se 1 (by rfl) ⟨2583818, by rfl⟩ : syracuseStep 3445091 = 5167637) B5167637
theorem B2296727 : Blo 2295435 2296727 := bstep (se 1 (by rfl) ⟨1722545, by rfl⟩ : syracuseStep 2296727 = 3445091) B3445091
theorem B8720405 : Blo 2295435 8720405 := bbase (se 6 (by rfl) ⟨204384, by rfl⟩ : syracuseStep 8720405 = 408769) (by norm_num)
theorem B5813603 : Blo 2295435 5813603 := bstep (se 1 (by rfl) ⟨4360202, by rfl⟩ : syracuseStep 5813603 = 8720405) B8720405
theorem B3875735 : Blo 2295435 3875735 := bstep (se 1 (by rfl) ⟨2906801, by rfl⟩ : syracuseStep 3875735 = 5813603) B5813603
theorem B2583823 : Blo 2295435 2583823 := bstep (se 1 (by rfl) ⟨1937867, by rfl⟩ : syracuseStep 2583823 = 3875735) B3875735
theorem B3445097 : Blo 2295435 3445097 := bstep (se 2 (by rfl) ⟨1291911, by rfl⟩ : syracuseStep 3445097 = 2583823) B2583823
theorem B2296731 : Blo 2295435 2296731 := bstep (se 1 (by rfl) ⟨1722548, by rfl⟩ : syracuseStep 2296731 = 3445097) B3445097
theorem B13080629 : Blo 2295435 13080629 := bbase (se 5 (by rfl) ⟨613154, by rfl⟩ : syracuseStep 13080629 = 1226309) (by norm_num)
theorem B8720419 : Blo 2295435 8720419 := bstep (se 1 (by rfl) ⟨6540314, by rfl⟩ : syracuseStep 8720419 = 13080629) B13080629
theorem B11627225 : Blo 2295435 11627225 := bstep (se 2 (by rfl) ⟨4360209, by rfl⟩ : syracuseStep 11627225 = 8720419) B8720419
theorem B7751483 : Blo 2295435 7751483 := bstep (se 1 (by rfl) ⟨5813612, by rfl⟩ : syracuseStep 7751483 = 11627225) B11627225
theorem B5167655 : Blo 2295435 5167655 := bstep (se 1 (by rfl) ⟨3875741, by rfl⟩ : syracuseStep 5167655 = 7751483) B7751483
theorem B3445103 : Blo 2295435 3445103 := bstep (se 1 (by rfl) ⟨2583827, by rfl⟩ : syracuseStep 3445103 = 5167655) B5167655
theorem B2296735 : Blo 2295435 2296735 := bstep (se 1 (by rfl) ⟨1722551, by rfl⟩ : syracuseStep 2296735 = 3445103) B3445103
theorem B3445109 : Blo 2295435 3445109 := bbase (se 5 (by rfl) ⟨161489, by rfl⟩ : syracuseStep 3445109 = 322979) (by norm_num)
theorem B2296739 : Blo 2295435 2296739 := bstep (se 1 (by rfl) ⟨1722554, by rfl⟩ : syracuseStep 2296739 = 3445109) B3445109
theorem B3678941 : Blo 2295435 3678941 := bbase (se 3 (by rfl) ⟨689801, by rfl⟩ : syracuseStep 3678941 = 1379603) (by norm_num)
theorem B2452627 : Blo 2295435 2452627 := bstep (se 1 (by rfl) ⟨1839470, by rfl⟩ : syracuseStep 2452627 = 3678941) B3678941
theorem B3270169 : Blo 2295435 3270169 := bstep (se 2 (by rfl) ⟨1226313, by rfl⟩ : syracuseStep 3270169 = 2452627) B2452627
theorem B4360225 : Blo 2295435 4360225 := bstep (se 2 (by rfl) ⟨1635084, by rfl⟩ : syracuseStep 4360225 = 3270169) B3270169
theorem B5813633 : Blo 2295435 5813633 := bstep (se 2 (by rfl) ⟨2180112, by rfl⟩ : syracuseStep 5813633 = 4360225) B4360225
theorem B3875755 : Blo 2295435 3875755 := bstep (se 1 (by rfl) ⟨2906816, by rfl⟩ : syracuseStep 3875755 = 5813633) B5813633
theorem B5167673 : Blo 2295435 5167673 := bstep (se 2 (by rfl) ⟨1937877, by rfl⟩ : syracuseStep 5167673 = 3875755) B3875755
theorem B3445115 : Blo 2295435 3445115 := bstep (se 1 (by rfl) ⟨2583836, by rfl⟩ : syracuseStep 3445115 = 5167673) B5167673
theorem B2296743 : Blo 2295435 2296743 := bstep (se 1 (by rfl) ⟨1722557, by rfl⟩ : syracuseStep 2296743 = 3445115) B3445115
theorem B2583841 : Blo 2295435 2583841 := bbase (se 2 (by rfl) ⟨968940, by rfl⟩ : syracuseStep 2583841 = 1937881) (by norm_num)
theorem B3445121 : Blo 2295435 3445121 := bstep (se 2 (by rfl) ⟨1291920, by rfl⟩ : syracuseStep 3445121 = 2583841) B2583841
theorem B2296747 : Blo 2295435 2296747 := bstep (se 1 (by rfl) ⟨1722560, by rfl⟩ : syracuseStep 2296747 = 3445121) B3445121
theorem B5813653 : Blo 2295435 5813653 := bbase (se 6 (by rfl) ⟨136257, by rfl⟩ : syracuseStep 5813653 = 272515) (by norm_num)
theorem B7751537 : Blo 2295435 7751537 := bstep (se 2 (by rfl) ⟨2906826, by rfl⟩ : syracuseStep 7751537 = 5813653) B5813653
theorem B5167691 : Blo 2295435 5167691 := bstep (se 1 (by rfl) ⟨3875768, by rfl⟩ : syracuseStep 5167691 = 7751537) B7751537
theorem B3445127 : Blo 2295435 3445127 := bstep (se 1 (by rfl) ⟨2583845, by rfl⟩ : syracuseStep 3445127 = 5167691) B5167691
theorem B2296751 : Blo 2295435 2296751 := bstep (se 1 (by rfl) ⟨1722563, by rfl⟩ : syracuseStep 2296751 = 3445127) B3445127
theorem B3445133 : Blo 2295435 3445133 := bbase (se 3 (by rfl) ⟨645962, by rfl⟩ : syracuseStep 3445133 = 1291925) (by norm_num)
theorem B2296755 : Blo 2295435 2296755 := bstep (se 1 (by rfl) ⟨1722566, by rfl⟩ : syracuseStep 2296755 = 3445133) B3445133
theorem B5167709 : Blo 2295435 5167709 := bbase (se 3 (by rfl) ⟨968945, by rfl⟩ : syracuseStep 5167709 = 1937891) (by norm_num)
theorem B3445139 : Blo 2295435 3445139 := bstep (se 1 (by rfl) ⟨2583854, by rfl⟩ : syracuseStep 3445139 = 5167709) B5167709
theorem B2296759 : Blo 2295435 2296759 := bstep (se 1 (by rfl) ⟨1722569, by rfl⟩ : syracuseStep 2296759 = 3445139) B3445139
theorem B3875789 : Blo 2295435 3875789 := bbase (se 3 (by rfl) ⟨726710, by rfl⟩ : syracuseStep 3875789 = 1453421) (by norm_num)
theorem B2583859 : Blo 2295435 2583859 := bstep (se 1 (by rfl) ⟨1937894, by rfl⟩ : syracuseStep 2583859 = 3875789) B3875789
theorem B3445145 : Blo 2295435 3445145 := bstep (se 2 (by rfl) ⟨1291929, by rfl⟩ : syracuseStep 3445145 = 2583859) B2583859
theorem B2296763 : Blo 2295435 2296763 := bstep (se 1 (by rfl) ⟨1722572, by rfl⟩ : syracuseStep 2296763 = 3445145) B3445145
theorem B5893013 : Blo 2295435 5893013 := bbase (se 6 (by rfl) ⟨138117, by rfl⟩ : syracuseStep 5893013 = 276235) (by norm_num)
theorem B15714701 : Blo 2295435 15714701 := bstep (se 3 (by rfl) ⟨2946506, by rfl⟩ : syracuseStep 15714701 = 5893013) B5893013
theorem B10476467 : Blo 2295435 10476467 := bstep (se 1 (by rfl) ⟨7857350, by rfl⟩ : syracuseStep 10476467 = 15714701) B15714701
theorem B6984311 : Blo 2295435 6984311 := bstep (se 1 (by rfl) ⟨5238233, by rfl⟩ : syracuseStep 6984311 = 10476467) B10476467
theorem B18624829 : Blo 2295435 18624829 := bstep (se 3 (by rfl) ⟨3492155, by rfl⟩ : syracuseStep 18624829 = 6984311) B6984311
theorem B24833105 : Blo 2295435 24833105 := bstep (se 2 (by rfl) ⟨9312414, by rfl⟩ : syracuseStep 24833105 = 18624829) B18624829
theorem B16555403 : Blo 2295435 16555403 := bstep (se 1 (by rfl) ⟨12416552, by rfl⟩ : syracuseStep 16555403 = 24833105) B24833105
theorem B11036935 : Blo 2295435 11036935 := bstep (se 1 (by rfl) ⟨8277701, by rfl⟩ : syracuseStep 11036935 = 16555403) B16555403
theorem B14715913 : Blo 2295435 14715913 := bstep (se 2 (by rfl) ⟨5518467, by rfl⟩ : syracuseStep 14715913 = 11036935) B11036935
theorem B19621217 : Blo 2295435 19621217 := bstep (se 2 (by rfl) ⟨7357956, by rfl⟩ : syracuseStep 19621217 = 14715913) B14715913
theorem B13080811 : Blo 2295435 13080811 := bstep (se 1 (by rfl) ⟨9810608, by rfl⟩ : syracuseStep 13080811 = 19621217) B19621217
theorem B17441081 : Blo 2295435 17441081 := bstep (se 2 (by rfl) ⟨6540405, by rfl⟩ : syracuseStep 17441081 = 13080811) B13080811
theorem B11627387 : Blo 2295435 11627387 := bstep (se 1 (by rfl) ⟨8720540, by rfl⟩ : syracuseStep 11627387 = 17441081) B17441081
theorem B7751591 : Blo 2295435 7751591 := bstep (se 1 (by rfl) ⟨5813693, by rfl⟩ : syracuseStep 7751591 = 11627387) B11627387
theorem B5167727 : Blo 2295435 5167727 := bstep (se 1 (by rfl) ⟨3875795, by rfl⟩ : syracuseStep 5167727 = 7751591) B7751591
theorem B3445151 : Blo 2295435 3445151 := bstep (se 1 (by rfl) ⟨2583863, by rfl⟩ : syracuseStep 3445151 = 5167727) B5167727
theorem B2296767 : Blo 2295435 2296767 := bstep (se 1 (by rfl) ⟨1722575, by rfl⟩ : syracuseStep 2296767 = 3445151) B3445151
theorem B3445157 : Blo 2295435 3445157 := bbase (se 4 (by rfl) ⟨322983, by rfl⟩ : syracuseStep 3445157 = 645967) (by norm_num)
theorem B2296771 : Blo 2295435 2296771 := bstep (se 1 (by rfl) ⟨1722578, by rfl⟩ : syracuseStep 2296771 = 3445157) B3445157
theorem B2906857 : Blo 2295435 2906857 := bbase (se 2 (by rfl) ⟨1090071, by rfl⟩ : syracuseStep 2906857 = 2180143) (by norm_num)
theorem B3875809 : Blo 2295435 3875809 := bstep (se 2 (by rfl) ⟨1453428, by rfl⟩ : syracuseStep 3875809 = 2906857) B2906857
theorem B5167745 : Blo 2295435 5167745 := bstep (se 2 (by rfl) ⟨1937904, by rfl⟩ : syracuseStep 5167745 = 3875809) B3875809
theorem B3445163 : Blo 2295435 3445163 := bstep (se 1 (by rfl) ⟨2583872, by rfl⟩ : syracuseStep 3445163 = 5167745) B5167745
theorem B2296775 : Blo 2295435 2296775 := bstep (se 1 (by rfl) ⟨1722581, by rfl⟩ : syracuseStep 2296775 = 3445163) B3445163
theorem B2583877 : Blo 2295435 2583877 := bbase (se 4 (by rfl) ⟨242238, by rfl⟩ : syracuseStep 2583877 = 484477) (by norm_num)
theorem B3445169 : Blo 2295435 3445169 := bstep (se 2 (by rfl) ⟨1291938, by rfl⟩ : syracuseStep 3445169 = 2583877) B2583877
theorem B2296779 : Blo 2295435 2296779 := bstep (se 1 (by rfl) ⟨1722584, by rfl⟩ : syracuseStep 2296779 = 3445169) B3445169
theorem B4360301 : Blo 2295435 4360301 := bbase (se 3 (by rfl) ⟨817556, by rfl⟩ : syracuseStep 4360301 = 1635113) (by norm_num)
theorem B2906867 : Blo 2295435 2906867 := bstep (se 1 (by rfl) ⟨2180150, by rfl⟩ : syracuseStep 2906867 = 4360301) B4360301
theorem B7751645 : Blo 2295435 7751645 := bstep (se 3 (by rfl) ⟨1453433, by rfl⟩ : syracuseStep 7751645 = 2906867) B2906867
theorem B5167763 : Blo 2295435 5167763 := bstep (se 1 (by rfl) ⟨3875822, by rfl⟩ : syracuseStep 5167763 = 7751645) B7751645
theorem B3445175 : Blo 2295435 3445175 := bstep (se 1 (by rfl) ⟨2583881, by rfl⟩ : syracuseStep 3445175 = 5167763) B5167763
theorem B2296783 : Blo 2295435 2296783 := bstep (se 1 (by rfl) ⟨1722587, by rfl⟩ : syracuseStep 2296783 = 3445175) B3445175
theorem B3445181 : Blo 2295435 3445181 := bbase (se 3 (by rfl) ⟨645971, by rfl⟩ : syracuseStep 3445181 = 1291943) (by norm_num)
theorem B2296787 : Blo 2295435 2296787 := bstep (se 1 (by rfl) ⟨1722590, by rfl⟩ : syracuseStep 2296787 = 3445181) B3445181
theorem B5167781 : Blo 2295435 5167781 := bbase (se 4 (by rfl) ⟨484479, by rfl⟩ : syracuseStep 5167781 = 968959) (by norm_num)
theorem B3445187 : Blo 2295435 3445187 := bstep (se 1 (by rfl) ⟨2583890, by rfl⟩ : syracuseStep 3445187 = 5167781) B5167781
theorem B2296791 : Blo 2295435 2296791 := bstep (se 1 (by rfl) ⟨1722593, by rfl⟩ : syracuseStep 2296791 = 3445187) B3445187
theorem B5813765 : Blo 2295435 5813765 := bbase (se 4 (by rfl) ⟨545040, by rfl⟩ : syracuseStep 5813765 = 1090081) (by norm_num)
theorem B3875843 : Blo 2295435 3875843 := bstep (se 1 (by rfl) ⟨2906882, by rfl⟩ : syracuseStep 3875843 = 5813765) B5813765
theorem B2583895 : Blo 2295435 2583895 := bstep (se 1 (by rfl) ⟨1937921, by rfl⟩ : syracuseStep 2583895 = 3875843) B3875843
theorem B3445193 : Blo 2295435 3445193 := bstep (se 2 (by rfl) ⟨1291947, by rfl⟩ : syracuseStep 3445193 = 2583895) B2583895
theorem B2296795 : Blo 2295435 2296795 := bstep (se 1 (by rfl) ⟨1722596, by rfl⟩ : syracuseStep 2296795 = 3445193) B3445193
theorem B4905373 : Blo 2295435 4905373 := bbase (se 3 (by rfl) ⟨919757, by rfl⟩ : syracuseStep 4905373 = 1839515) (by norm_num)
theorem B6540497 : Blo 2295435 6540497 := bstep (se 2 (by rfl) ⟨2452686, by rfl⟩ : syracuseStep 6540497 = 4905373) B4905373
theorem B4360331 : Blo 2295435 4360331 := bstep (se 1 (by rfl) ⟨3270248, by rfl⟩ : syracuseStep 4360331 = 6540497) B6540497
theorem B11627549 : Blo 2295435 11627549 := bstep (se 3 (by rfl) ⟨2180165, by rfl⟩ : syracuseStep 11627549 = 4360331) B4360331
theorem B7751699 : Blo 2295435 7751699 := bstep (se 1 (by rfl) ⟨5813774, by rfl⟩ : syracuseStep 7751699 = 11627549) B11627549
theorem B5167799 : Blo 2295435 5167799 := bstep (se 1 (by rfl) ⟨3875849, by rfl⟩ : syracuseStep 5167799 = 7751699) B7751699
theorem B3445199 : Blo 2295435 3445199 := bstep (se 1 (by rfl) ⟨2583899, by rfl⟩ : syracuseStep 3445199 = 5167799) B5167799
theorem B2296799 : Blo 2295435 2296799 := bstep (se 1 (by rfl) ⟨1722599, by rfl⟩ : syracuseStep 2296799 = 3445199) B3445199
theorem B3445205 : Blo 2295435 3445205 := bbase (se 7 (by rfl) ⟨40373, by rfl⟩ : syracuseStep 3445205 = 80747) (by norm_num)
theorem B2296803 : Blo 2295435 2296803 := bstep (se 1 (by rfl) ⟨1722602, by rfl⟩ : syracuseStep 2296803 = 3445205) B3445205
theorem B8720693 : Blo 2295435 8720693 := bbase (se 5 (by rfl) ⟨408782, by rfl⟩ : syracuseStep 8720693 = 817565) (by norm_num)
theorem B5813795 : Blo 2295435 5813795 := bstep (se 1 (by rfl) ⟨4360346, by rfl⟩ : syracuseStep 5813795 = 8720693) B8720693
theorem B3875863 : Blo 2295435 3875863 := bstep (se 1 (by rfl) ⟨2906897, by rfl⟩ : syracuseStep 3875863 = 5813795) B5813795
theorem B5167817 : Blo 2295435 5167817 := bstep (se 2 (by rfl) ⟨1937931, by rfl⟩ : syracuseStep 5167817 = 3875863) B3875863
theorem B3445211 : Blo 2295435 3445211 := bstep (se 1 (by rfl) ⟨2583908, by rfl⟩ : syracuseStep 3445211 = 5167817) B5167817
theorem B2296807 : Blo 2295435 2296807 := bstep (se 1 (by rfl) ⟨1722605, by rfl⟩ : syracuseStep 2296807 = 3445211) B3445211
theorem B2583913 : Blo 2295435 2583913 := bbase (se 2 (by rfl) ⟨968967, by rfl⟩ : syracuseStep 2583913 = 1937935) (by norm_num)
theorem B3445217 : Blo 2295435 3445217 := bstep (se 2 (by rfl) ⟨1291956, by rfl⟩ : syracuseStep 3445217 = 2583913) B2583913
theorem B2296811 : Blo 2295435 2296811 := bstep (se 1 (by rfl) ⟨1722608, by rfl⟩ : syracuseStep 2296811 = 3445217) B3445217
theorem B5593877 : Blo 2295435 5593877 := bbase (se 6 (by rfl) ⟨131106, by rfl⟩ : syracuseStep 5593877 = 262213) (by norm_num)
theorem B3729251 : Blo 2295435 3729251 := bstep (se 1 (by rfl) ⟨2796938, by rfl⟩ : syracuseStep 3729251 = 5593877) B5593877
theorem B2486167 : Blo 2295435 2486167 := bstep (se 1 (by rfl) ⟨1864625, by rfl⟩ : syracuseStep 2486167 = 3729251) B3729251
theorem B13259557 : Blo 2295435 13259557 := bstep (se 4 (by rfl) ⟨1243083, by rfl⟩ : syracuseStep 13259557 = 2486167) B2486167
theorem B70717637 : Blo 2295435 70717637 := bstep (se 4 (by rfl) ⟨6629778, by rfl⟩ : syracuseStep 70717637 = 13259557) B13259557
theorem B47145091 : Blo 2295435 47145091 := bstep (se 1 (by rfl) ⟨35358818, by rfl⟩ : syracuseStep 47145091 = 70717637) B70717637
theorem B62860121 : Blo 2295435 62860121 := bstep (se 2 (by rfl) ⟨23572545, by rfl⟩ : syracuseStep 62860121 = 47145091) B47145091
theorem B41906747 : Blo 2295435 41906747 := bstep (se 1 (by rfl) ⟨31430060, by rfl⟩ : syracuseStep 41906747 = 62860121) B62860121
theorem B27937831 : Blo 2295435 27937831 := bstep (se 1 (by rfl) ⟨20953373, by rfl⟩ : syracuseStep 27937831 = 41906747) B41906747
theorem B37250441 : Blo 2295435 37250441 := bstep (se 2 (by rfl) ⟨13968915, by rfl⟩ : syracuseStep 37250441 = 27937831) B27937831
theorem B24833627 : Blo 2295435 24833627 := bstep (se 1 (by rfl) ⟨18625220, by rfl⟩ : syracuseStep 24833627 = 37250441) B37250441
theorem B16555751 : Blo 2295435 16555751 := bstep (se 1 (by rfl) ⟨12416813, by rfl⟩ : syracuseStep 16555751 = 24833627) B24833627
theorem B11037167 : Blo 2295435 11037167 := bstep (se 1 (by rfl) ⟨8277875, by rfl⟩ : syracuseStep 11037167 = 16555751) B16555751
theorem B7358111 : Blo 2295435 7358111 := bstep (se 1 (by rfl) ⟨5518583, by rfl⟩ : syracuseStep 7358111 = 11037167) B11037167
theorem B4905407 : Blo 2295435 4905407 := bstep (se 1 (by rfl) ⟨3679055, by rfl⟩ : syracuseStep 4905407 = 7358111) B7358111
theorem B13081085 : Blo 2295435 13081085 := bstep (se 3 (by rfl) ⟨2452703, by rfl⟩ : syracuseStep 13081085 = 4905407) B4905407
theorem B8720723 : Blo 2295435 8720723 := bstep (se 1 (by rfl) ⟨6540542, by rfl⟩ : syracuseStep 8720723 = 13081085) B13081085
theorem B5813815 : Blo 2295435 5813815 := bstep (se 1 (by rfl) ⟨4360361, by rfl⟩ : syracuseStep 5813815 = 8720723) B8720723
theorem B7751753 : Blo 2295435 7751753 := bstep (se 2 (by rfl) ⟨2906907, by rfl⟩ : syracuseStep 7751753 = 5813815) B5813815
theorem B5167835 : Blo 2295435 5167835 := bstep (se 1 (by rfl) ⟨3875876, by rfl⟩ : syracuseStep 5167835 = 7751753) B7751753
theorem B3445223 : Blo 2295435 3445223 := bstep (se 1 (by rfl) ⟨2583917, by rfl⟩ : syracuseStep 3445223 = 5167835) B5167835
theorem B2296815 : Blo 2295435 2296815 := bstep (se 1 (by rfl) ⟨1722611, by rfl⟩ : syracuseStep 2296815 = 3445223) B3445223
theorem B3445229 : Blo 2295435 3445229 := bbase (se 3 (by rfl) ⟨645980, by rfl⟩ : syracuseStep 3445229 = 1291961) (by norm_num)
theorem B2296819 : Blo 2295435 2296819 := bstep (se 1 (by rfl) ⟨1722614, by rfl⟩ : syracuseStep 2296819 = 3445229) B3445229
theorem B5167853 : Blo 2295435 5167853 := bbase (se 3 (by rfl) ⟨968972, by rfl⟩ : syracuseStep 5167853 = 1937945) (by norm_num)
theorem B3445235 : Blo 2295435 3445235 := bstep (se 1 (by rfl) ⟨2583926, by rfl⟩ : syracuseStep 3445235 = 5167853) B5167853
theorem B2296823 : Blo 2295435 2296823 := bstep (se 1 (by rfl) ⟨1722617, by rfl⟩ : syracuseStep 2296823 = 3445235) B3445235
theorem B2452717 : Blo 2295435 2452717 := bbase (se 3 (by rfl) ⟨459884, by rfl⟩ : syracuseStep 2452717 = 919769) (by norm_num)
theorem B3270289 : Blo 2295435 3270289 := bstep (se 2 (by rfl) ⟨1226358, by rfl⟩ : syracuseStep 3270289 = 2452717) B2452717
theorem B4360385 : Blo 2295435 4360385 := bstep (se 2 (by rfl) ⟨1635144, by rfl⟩ : syracuseStep 4360385 = 3270289) B3270289
theorem B2906923 : Blo 2295435 2906923 := bstep (se 1 (by rfl) ⟨2180192, by rfl⟩ : syracuseStep 2906923 = 4360385) B4360385
theorem B3875897 : Blo 2295435 3875897 := bstep (se 2 (by rfl) ⟨1453461, by rfl⟩ : syracuseStep 3875897 = 2906923) B2906923
theorem B2583931 : Blo 2295435 2583931 := bstep (se 1 (by rfl) ⟨1937948, by rfl⟩ : syracuseStep 2583931 = 3875897) B3875897
theorem B3445241 : Blo 2295435 3445241 := bstep (se 2 (by rfl) ⟨1291965, by rfl⟩ : syracuseStep 3445241 = 2583931) B2583931
theorem B2296827 : Blo 2295435 2296827 := bstep (se 1 (by rfl) ⟨1722620, by rfl⟩ : syracuseStep 2296827 = 3445241) B3445241
theorem B3729277 : Blo 2295435 3729277 := bbase (se 3 (by rfl) ⟨699239, by rfl⟩ : syracuseStep 3729277 = 1398479) (by norm_num)
theorem B4972369 : Blo 2295435 4972369 := bstep (se 2 (by rfl) ⟨1864638, by rfl⟩ : syracuseStep 4972369 = 3729277) B3729277
theorem B6629825 : Blo 2295435 6629825 := bstep (se 2 (by rfl) ⟨2486184, by rfl⟩ : syracuseStep 6629825 = 4972369) B4972369
theorem B4419883 : Blo 2295435 4419883 := bstep (se 1 (by rfl) ⟨3314912, by rfl⟩ : syracuseStep 4419883 = 6629825) B6629825
theorem B5893177 : Blo 2295435 5893177 := bstep (se 2 (by rfl) ⟨2209941, by rfl⟩ : syracuseStep 5893177 = 4419883) B4419883
theorem B7857569 : Blo 2295435 7857569 := bstep (se 2 (by rfl) ⟨2946588, by rfl⟩ : syracuseStep 7857569 = 5893177) B5893177
theorem B5238379 : Blo 2295435 5238379 := bstep (se 1 (by rfl) ⟨3928784, by rfl⟩ : syracuseStep 5238379 = 7857569) B7857569
theorem B6984505 : Blo 2295435 6984505 := bstep (se 2 (by rfl) ⟨2619189, by rfl⟩ : syracuseStep 6984505 = 5238379) B5238379
theorem B37250693 : Blo 2295435 37250693 := bstep (se 4 (by rfl) ⟨3492252, by rfl⟩ : syracuseStep 37250693 = 6984505) B6984505
theorem B24833795 : Blo 2295435 24833795 := bstep (se 1 (by rfl) ⟨18625346, by rfl⟩ : syracuseStep 24833795 = 37250693) B37250693
theorem B66223453 : Blo 2295435 66223453 := bstep (se 3 (by rfl) ⟨12416897, by rfl⟩ : syracuseStep 66223453 = 24833795) B24833795
theorem B88297937 : Blo 2295435 88297937 := bstep (se 2 (by rfl) ⟨33111726, by rfl⟩ : syracuseStep 88297937 = 66223453) B66223453
theorem B58865291 : Blo 2295435 58865291 := bstep (se 1 (by rfl) ⟨44148968, by rfl⟩ : syracuseStep 58865291 = 88297937) B88297937
theorem B39243527 : Blo 2295435 39243527 := bstep (se 1 (by rfl) ⟨29432645, by rfl⟩ : syracuseStep 39243527 = 58865291) B58865291
theorem B26162351 : Blo 2295435 26162351 := bstep (se 1 (by rfl) ⟨19621763, by rfl⟩ : syracuseStep 26162351 = 39243527) B39243527
theorem B17441567 : Blo 2295435 17441567 := bstep (se 1 (by rfl) ⟨13081175, by rfl⟩ : syracuseStep 17441567 = 26162351) B26162351
theorem B11627711 : Blo 2295435 11627711 := bstep (se 1 (by rfl) ⟨8720783, by rfl⟩ : syracuseStep 11627711 = 17441567) B17441567
theorem B7751807 : Blo 2295435 7751807 := bstep (se 1 (by rfl) ⟨5813855, by rfl⟩ : syracuseStep 7751807 = 11627711) B11627711
theorem B5167871 : Blo 2295435 5167871 := bstep (se 1 (by rfl) ⟨3875903, by rfl⟩ : syracuseStep 5167871 = 7751807) B7751807
theorem B3445247 : Blo 2295435 3445247 := bstep (se 1 (by rfl) ⟨2583935, by rfl⟩ : syracuseStep 3445247 = 5167871) B5167871
theorem B2296831 : Blo 2295435 2296831 := bstep (se 1 (by rfl) ⟨1722623, by rfl⟩ : syracuseStep 2296831 = 3445247) B3445247
theorem B3445253 : Blo 2295435 3445253 := bbase (se 4 (by rfl) ⟨322992, by rfl⟩ : syracuseStep 3445253 = 645985) (by norm_num)
theorem B2296835 : Blo 2295435 2296835 := bstep (se 1 (by rfl) ⟨1722626, by rfl⟩ : syracuseStep 2296835 = 3445253) B3445253
theorem B3875917 : Blo 2295435 3875917 := bbase (se 3 (by rfl) ⟨726734, by rfl⟩ : syracuseStep 3875917 = 1453469) (by norm_num)
theorem B5167889 : Blo 2295435 5167889 := bstep (se 2 (by rfl) ⟨1937958, by rfl⟩ : syracuseStep 5167889 = 3875917) B3875917
theorem B3445259 : Blo 2295435 3445259 := bstep (se 1 (by rfl) ⟨2583944, by rfl⟩ : syracuseStep 3445259 = 5167889) B5167889
theorem B2296839 : Blo 2295435 2296839 := bstep (se 1 (by rfl) ⟨1722629, by rfl⟩ : syracuseStep 2296839 = 3445259) B3445259
theorem B2583949 : Blo 2295435 2583949 := bbase (se 3 (by rfl) ⟨484490, by rfl⟩ : syracuseStep 2583949 = 968981) (by norm_num)
theorem B3445265 : Blo 2295435 3445265 := bstep (se 2 (by rfl) ⟨1291974, by rfl⟩ : syracuseStep 3445265 = 2583949) B2583949
theorem B2296843 : Blo 2295435 2296843 := bstep (se 1 (by rfl) ⟨1722632, by rfl⟩ : syracuseStep 2296843 = 3445265) B3445265
theorem B7751861 : Blo 2295435 7751861 := bbase (se 5 (by rfl) ⟨363368, by rfl⟩ : syracuseStep 7751861 = 726737) (by norm_num)
theorem B5167907 : Blo 2295435 5167907 := bstep (se 1 (by rfl) ⟨3875930, by rfl⟩ : syracuseStep 5167907 = 7751861) B7751861
theorem B3445271 : Blo 2295435 3445271 := bstep (se 1 (by rfl) ⟨2583953, by rfl⟩ : syracuseStep 3445271 = 5167907) B5167907
theorem B2296847 : Blo 2295435 2296847 := bstep (se 1 (by rfl) ⟨1722635, by rfl⟩ : syracuseStep 2296847 = 3445271) B3445271
theorem B3445277 : Blo 2295435 3445277 := bbase (se 3 (by rfl) ⟨645989, by rfl⟩ : syracuseStep 3445277 = 1291979) (by norm_num)
theorem B2296851 : Blo 2295435 2296851 := bstep (se 1 (by rfl) ⟨1722638, by rfl⟩ : syracuseStep 2296851 = 3445277) B3445277
theorem B5167925 : Blo 2295435 5167925 := bbase (se 5 (by rfl) ⟨242246, by rfl⟩ : syracuseStep 5167925 = 484493) (by norm_num)
theorem B3445283 : Blo 2295435 3445283 := bstep (se 1 (by rfl) ⟨2583962, by rfl⟩ : syracuseStep 3445283 = 5167925) B5167925
theorem B2296855 : Blo 2295435 2296855 := bstep (se 1 (by rfl) ⟨1722641, by rfl⟩ : syracuseStep 2296855 = 3445283) B3445283
theorem B5238445 : Blo 2295435 5238445 := bbase (se 3 (by rfl) ⟨982208, by rfl⟩ : syracuseStep 5238445 = 1964417) (by norm_num)
theorem B6984593 : Blo 2295435 6984593 := bstep (se 2 (by rfl) ⟨2619222, by rfl⟩ : syracuseStep 6984593 = 5238445) B5238445
theorem B4656395 : Blo 2295435 4656395 := bstep (se 1 (by rfl) ⟨3492296, by rfl⟩ : syracuseStep 4656395 = 6984593) B6984593
theorem B3104263 : Blo 2295435 3104263 := bstep (se 1 (by rfl) ⟨2328197, by rfl⟩ : syracuseStep 3104263 = 4656395) B4656395
theorem B16556069 : Blo 2295435 16556069 := bstep (se 4 (by rfl) ⟨1552131, by rfl⟩ : syracuseStep 16556069 = 3104263) B3104263
theorem B11037379 : Blo 2295435 11037379 := bstep (se 1 (by rfl) ⟨8278034, by rfl⟩ : syracuseStep 11037379 = 16556069) B16556069
theorem B14716505 : Blo 2295435 14716505 := bstep (se 2 (by rfl) ⟨5518689, by rfl⟩ : syracuseStep 14716505 = 11037379) B11037379
theorem B9811003 : Blo 2295435 9811003 := bstep (se 1 (by rfl) ⟨7358252, by rfl⟩ : syracuseStep 9811003 = 14716505) B14716505
theorem B13081337 : Blo 2295435 13081337 := bstep (se 2 (by rfl) ⟨4905501, by rfl⟩ : syracuseStep 13081337 = 9811003) B9811003
theorem B8720891 : Blo 2295435 8720891 := bstep (se 1 (by rfl) ⟨6540668, by rfl⟩ : syracuseStep 8720891 = 13081337) B13081337
theorem B5813927 : Blo 2295435 5813927 := bstep (se 1 (by rfl) ⟨4360445, by rfl⟩ : syracuseStep 5813927 = 8720891) B8720891
theorem B3875951 : Blo 2295435 3875951 := bstep (se 1 (by rfl) ⟨2906963, by rfl⟩ : syracuseStep 3875951 = 5813927) B5813927
theorem B2583967 : Blo 2295435 2583967 := bstep (se 1 (by rfl) ⟨1937975, by rfl⟩ : syracuseStep 2583967 = 3875951) B3875951
theorem B3445289 : Blo 2295435 3445289 := bstep (se 2 (by rfl) ⟨1291983, by rfl⟩ : syracuseStep 3445289 = 2583967) B2583967
theorem B2296859 : Blo 2295435 2296859 := bstep (se 1 (by rfl) ⟨1722644, by rfl⟩ : syracuseStep 2296859 = 3445289) B3445289
theorem B11037397 : Blo 2295435 11037397 := bbase (se 7 (by rfl) ⟨129344, by rfl⟩ : syracuseStep 11037397 = 258689) (by norm_num)
theorem B14716529 : Blo 2295435 14716529 := bstep (se 2 (by rfl) ⟨5518698, by rfl⟩ : syracuseStep 14716529 = 11037397) B11037397
theorem B9811019 : Blo 2295435 9811019 := bstep (se 1 (by rfl) ⟨7358264, by rfl⟩ : syracuseStep 9811019 = 14716529) B14716529
theorem B6540679 : Blo 2295435 6540679 := bstep (se 1 (by rfl) ⟨4905509, by rfl⟩ : syracuseStep 6540679 = 9811019) B9811019
theorem B8720905 : Blo 2295435 8720905 := bstep (se 2 (by rfl) ⟨3270339, by rfl⟩ : syracuseStep 8720905 = 6540679) B6540679
theorem B11627873 : Blo 2295435 11627873 := bstep (se 2 (by rfl) ⟨4360452, by rfl⟩ : syracuseStep 11627873 = 8720905) B8720905
theorem B7751915 : Blo 2295435 7751915 := bstep (se 1 (by rfl) ⟨5813936, by rfl⟩ : syracuseStep 7751915 = 11627873) B11627873
theorem B5167943 : Blo 2295435 5167943 := bstep (se 1 (by rfl) ⟨3875957, by rfl⟩ : syracuseStep 5167943 = 7751915) B7751915
theorem B3445295 : Blo 2295435 3445295 := bstep (se 1 (by rfl) ⟨2583971, by rfl⟩ : syracuseStep 3445295 = 5167943) B5167943
theorem B2296863 : Blo 2295435 2296863 := bstep (se 1 (by rfl) ⟨1722647, by rfl⟩ : syracuseStep 2296863 = 3445295) B3445295
theorem B3445301 : Blo 2295435 3445301 := bbase (se 5 (by rfl) ⟨161498, by rfl⟩ : syracuseStep 3445301 = 322997) (by norm_num)
theorem B2296867 : Blo 2295435 2296867 := bstep (se 1 (by rfl) ⟨1722650, by rfl⟩ : syracuseStep 2296867 = 3445301) B3445301
theorem B5813957 : Blo 2295435 5813957 := bbase (se 4 (by rfl) ⟨545058, by rfl⟩ : syracuseStep 5813957 = 1090117) (by norm_num)
theorem B3875971 : Blo 2295435 3875971 := bstep (se 1 (by rfl) ⟨2906978, by rfl⟩ : syracuseStep 3875971 = 5813957) B5813957
theorem B5167961 : Blo 2295435 5167961 := bstep (se 2 (by rfl) ⟨1937985, by rfl⟩ : syracuseStep 5167961 = 3875971) B3875971
theorem B3445307 : Blo 2295435 3445307 := bstep (se 1 (by rfl) ⟨2583980, by rfl⟩ : syracuseStep 3445307 = 5167961) B5167961
theorem B2296871 : Blo 2295435 2296871 := bstep (se 1 (by rfl) ⟨1722653, by rfl⟩ : syracuseStep 2296871 = 3445307) B3445307
theorem B2583985 : Blo 2295435 2583985 := bbase (se 2 (by rfl) ⟨968994, by rfl⟩ : syracuseStep 2583985 = 1937989) (by norm_num)
theorem B3445313 : Blo 2295435 3445313 := bstep (se 2 (by rfl) ⟨1291992, by rfl⟩ : syracuseStep 3445313 = 2583985) B2583985
theorem B2296875 : Blo 2295435 2296875 := bstep (se 1 (by rfl) ⟨1722656, by rfl⟩ : syracuseStep 2296875 = 3445313) B3445313
theorem B6540725 : Blo 2295435 6540725 := bbase (se 5 (by rfl) ⟨306596, by rfl⟩ : syracuseStep 6540725 = 613193) (by norm_num)
theorem B4360483 : Blo 2295435 4360483 := bstep (se 1 (by rfl) ⟨3270362, by rfl⟩ : syracuseStep 4360483 = 6540725) B6540725
theorem B5813977 : Blo 2295435 5813977 := bstep (se 2 (by rfl) ⟨2180241, by rfl⟩ : syracuseStep 5813977 = 4360483) B4360483
theorem B7751969 : Blo 2295435 7751969 := bstep (se 2 (by rfl) ⟨2906988, by rfl⟩ : syracuseStep 7751969 = 5813977) B5813977
theorem B5167979 : Blo 2295435 5167979 := bstep (se 1 (by rfl) ⟨3875984, by rfl⟩ : syracuseStep 5167979 = 7751969) B7751969
theorem B3445319 : Blo 2295435 3445319 := bstep (se 1 (by rfl) ⟨2583989, by rfl⟩ : syracuseStep 3445319 = 5167979) B5167979
theorem B2296879 : Blo 2295435 2296879 := bstep (se 1 (by rfl) ⟨1722659, by rfl⟩ : syracuseStep 2296879 = 3445319) B3445319
theorem B3445325 : Blo 2295435 3445325 := bbase (se 3 (by rfl) ⟨645998, by rfl⟩ : syracuseStep 3445325 = 1291997) (by norm_num)
theorem B2296883 : Blo 2295435 2296883 := bstep (se 1 (by rfl) ⟨1722662, by rfl⟩ : syracuseStep 2296883 = 3445325) B3445325
theorem B5167997 : Blo 2295435 5167997 := bbase (se 3 (by rfl) ⟨968999, by rfl⟩ : syracuseStep 5167997 = 1937999) (by norm_num)
theorem B3445331 : Blo 2295435 3445331 := bstep (se 1 (by rfl) ⟨2583998, by rfl⟩ : syracuseStep 3445331 = 5167997) B5167997
theorem B2296887 : Blo 2295435 2296887 := bstep (se 1 (by rfl) ⟨1722665, by rfl⟩ : syracuseStep 2296887 = 3445331) B3445331
theorem B3876005 : Blo 2295435 3876005 := bbase (se 4 (by rfl) ⟨363375, by rfl⟩ : syracuseStep 3876005 = 726751) (by norm_num)
theorem B2584003 : Blo 2295435 2584003 := bstep (se 1 (by rfl) ⟨1938002, by rfl⟩ : syracuseStep 2584003 = 3876005) B3876005
theorem B3445337 : Blo 2295435 3445337 := bstep (se 2 (by rfl) ⟨1292001, by rfl⟩ : syracuseStep 3445337 = 2584003) B2584003
theorem B2296891 : Blo 2295435 2296891 := bstep (se 1 (by rfl) ⟨1722668, by rfl⟩ : syracuseStep 2296891 = 3445337) B3445337
theorem B2452789 : Blo 2295435 2452789 := bbase (se 5 (by rfl) ⟨114974, by rfl⟩ : syracuseStep 2452789 = 229949) (by norm_num)
theorem B3270385 : Blo 2295435 3270385 := bstep (se 2 (by rfl) ⟨1226394, by rfl⟩ : syracuseStep 3270385 = 2452789) B2452789
theorem B17442053 : Blo 2295435 17442053 := bstep (se 4 (by rfl) ⟨1635192, by rfl⟩ : syracuseStep 17442053 = 3270385) B3270385
theorem B11628035 : Blo 2295435 11628035 := bstep (se 1 (by rfl) ⟨8721026, by rfl⟩ : syracuseStep 11628035 = 17442053) B17442053
theorem B7752023 : Blo 2295435 7752023 := bstep (se 1 (by rfl) ⟨5814017, by rfl⟩ : syracuseStep 7752023 = 11628035) B11628035
theorem B5168015 : Blo 2295435 5168015 := bstep (se 1 (by rfl) ⟨3876011, by rfl⟩ : syracuseStep 5168015 = 7752023) B7752023
theorem B3445343 : Blo 2295435 3445343 := bstep (se 1 (by rfl) ⟨2584007, by rfl⟩ : syracuseStep 3445343 = 5168015) B5168015
theorem B2296895 : Blo 2295435 2296895 := bstep (se 1 (by rfl) ⟨1722671, by rfl⟩ : syracuseStep 2296895 = 3445343) B3445343
theorem B3445349 : Blo 2295435 3445349 := bbase (se 4 (by rfl) ⟨323001, by rfl⟩ : syracuseStep 3445349 = 646003) (by norm_num)
theorem B2296899 : Blo 2295435 2296899 := bstep (se 1 (by rfl) ⟨1722674, by rfl⟩ : syracuseStep 2296899 = 3445349) B3445349
theorem B3270397 : Blo 2295435 3270397 := bbase (se 3 (by rfl) ⟨613199, by rfl⟩ : syracuseStep 3270397 = 1226399) (by norm_num)
theorem B4360529 : Blo 2295435 4360529 := bstep (se 2 (by rfl) ⟨1635198, by rfl⟩ : syracuseStep 4360529 = 3270397) B3270397
theorem B2907019 : Blo 2295435 2907019 := bstep (se 1 (by rfl) ⟨2180264, by rfl⟩ : syracuseStep 2907019 = 4360529) B4360529
theorem B3876025 : Blo 2295435 3876025 := bstep (se 2 (by rfl) ⟨1453509, by rfl⟩ : syracuseStep 3876025 = 2907019) B2907019
theorem B5168033 : Blo 2295435 5168033 := bstep (se 2 (by rfl) ⟨1938012, by rfl⟩ : syracuseStep 5168033 = 3876025) B3876025
theorem B3445355 : Blo 2295435 3445355 := bstep (se 1 (by rfl) ⟨2584016, by rfl⟩ : syracuseStep 3445355 = 5168033) B5168033
theorem B2296903 : Blo 2295435 2296903 := bstep (se 1 (by rfl) ⟨1722677, by rfl⟩ : syracuseStep 2296903 = 3445355) B3445355
theorem B2584021 : Blo 2295435 2584021 := bbase (se 7 (by rfl) ⟨30281, by rfl⟩ : syracuseStep 2584021 = 60563) (by norm_num)
theorem B3445361 : Blo 2295435 3445361 := bstep (se 2 (by rfl) ⟨1292010, by rfl⟩ : syracuseStep 3445361 = 2584021) B2584021
theorem B2296907 : Blo 2295435 2296907 := bstep (se 1 (by rfl) ⟨1722680, by rfl⟩ : syracuseStep 2296907 = 3445361) B3445361
theorem B2907029 : Blo 2295435 2907029 := bbase (se 6 (by rfl) ⟨68133, by rfl⟩ : syracuseStep 2907029 = 136267) (by norm_num)
theorem B7752077 : Blo 2295435 7752077 := bstep (se 3 (by rfl) ⟨1453514, by rfl⟩ : syracuseStep 7752077 = 2907029) B2907029
theorem B5168051 : Blo 2295435 5168051 := bstep (se 1 (by rfl) ⟨3876038, by rfl⟩ : syracuseStep 5168051 = 7752077) B7752077
theorem B3445367 : Blo 2295435 3445367 := bstep (se 1 (by rfl) ⟨2584025, by rfl⟩ : syracuseStep 3445367 = 5168051) B5168051
theorem B2296911 : Blo 2295435 2296911 := bstep (se 1 (by rfl) ⟨1722683, by rfl⟩ : syracuseStep 2296911 = 3445367) B3445367
theorem B3445373 : Blo 2295435 3445373 := bbase (se 3 (by rfl) ⟨646007, by rfl⟩ : syracuseStep 3445373 = 1292015) (by norm_num)
theorem B2296915 : Blo 2295435 2296915 := bstep (se 1 (by rfl) ⟨1722686, by rfl⟩ : syracuseStep 2296915 = 3445373) B3445373
theorem B5168069 : Blo 2295435 5168069 := bbase (se 4 (by rfl) ⟨484506, by rfl⟩ : syracuseStep 5168069 = 969013) (by norm_num)
theorem B3445379 : Blo 2295435 3445379 := bstep (se 1 (by rfl) ⟨2584034, by rfl⟩ : syracuseStep 3445379 = 5168069) B5168069
theorem B2296919 : Blo 2295435 2296919 := bstep (se 1 (by rfl) ⟨1722689, by rfl⟩ : syracuseStep 2296919 = 3445379) B3445379
theorem B3679229 : Blo 2295435 3679229 := bbase (se 3 (by rfl) ⟨689855, by rfl⟩ : syracuseStep 3679229 = 1379711) (by norm_num)
theorem B9811277 : Blo 2295435 9811277 := bstep (se 3 (by rfl) ⟨1839614, by rfl⟩ : syracuseStep 9811277 = 3679229) B3679229
theorem B6540851 : Blo 2295435 6540851 := bstep (se 1 (by rfl) ⟨4905638, by rfl⟩ : syracuseStep 6540851 = 9811277) B9811277
theorem B4360567 : Blo 2295435 4360567 := bstep (se 1 (by rfl) ⟨3270425, by rfl⟩ : syracuseStep 4360567 = 6540851) B6540851
theorem B5814089 : Blo 2295435 5814089 := bstep (se 2 (by rfl) ⟨2180283, by rfl⟩ : syracuseStep 5814089 = 4360567) B4360567
theorem B3876059 : Blo 2295435 3876059 := bstep (se 1 (by rfl) ⟨2907044, by rfl⟩ : syracuseStep 3876059 = 5814089) B5814089
theorem B2584039 : Blo 2295435 2584039 := bstep (se 1 (by rfl) ⟨1938029, by rfl⟩ : syracuseStep 2584039 = 3876059) B3876059
theorem B3445385 : Blo 2295435 3445385 := bstep (se 2 (by rfl) ⟨1292019, by rfl⟩ : syracuseStep 3445385 = 2584039) B2584039
theorem B2296923 : Blo 2295435 2296923 := bstep (se 1 (by rfl) ⟨1722692, by rfl⟩ : syracuseStep 2296923 = 3445385) B3445385
theorem B11628197 : Blo 2295435 11628197 := bbase (se 4 (by rfl) ⟨1090143, by rfl⟩ : syracuseStep 11628197 = 2180287) (by norm_num)
theorem B7752131 : Blo 2295435 7752131 := bstep (se 1 (by rfl) ⟨5814098, by rfl⟩ : syracuseStep 7752131 = 11628197) B11628197
theorem B5168087 : Blo 2295435 5168087 := bstep (se 1 (by rfl) ⟨3876065, by rfl⟩ : syracuseStep 5168087 = 7752131) B7752131
theorem B3445391 : Blo 2295435 3445391 := bstep (se 1 (by rfl) ⟨2584043, by rfl⟩ : syracuseStep 3445391 = 5168087) B5168087
theorem B2296927 : Blo 2295435 2296927 := bstep (se 1 (by rfl) ⟨1722695, by rfl⟩ : syracuseStep 2296927 = 3445391) B3445391
theorem B3445397 : Blo 2295435 3445397 := bbase (se 6 (by rfl) ⟨80751, by rfl⟩ : syracuseStep 3445397 = 161503) (by norm_num)
theorem B2296931 : Blo 2295435 2296931 := bstep (se 1 (by rfl) ⟨1722698, by rfl⟩ : syracuseStep 2296931 = 3445397) B3445397
theorem B31431701 : Blo 2295435 31431701 := bbase (se 6 (by rfl) ⟨736680, by rfl⟩ : syracuseStep 31431701 = 1473361) (by norm_num)
theorem B20954467 : Blo 2295435 20954467 := bstep (se 1 (by rfl) ⟨15715850, by rfl⟩ : syracuseStep 20954467 = 31431701) B31431701
theorem B111757157 : Blo 2295435 111757157 := bstep (se 4 (by rfl) ⟨10477233, by rfl⟩ : syracuseStep 111757157 = 20954467) B20954467
theorem B74504771 : Blo 2295435 74504771 := bstep (se 1 (by rfl) ⟨55878578, by rfl⟩ : syracuseStep 74504771 = 111757157) B111757157
theorem B49669847 : Blo 2295435 49669847 := bstep (se 1 (by rfl) ⟨37252385, by rfl⟩ : syracuseStep 49669847 = 74504771) B74504771
theorem B33113231 : Blo 2295435 33113231 := bstep (se 1 (by rfl) ⟨24834923, by rfl⟩ : syracuseStep 33113231 = 49669847) B49669847
theorem B22075487 : Blo 2295435 22075487 := bstep (se 1 (by rfl) ⟨16556615, by rfl⟩ : syracuseStep 22075487 = 33113231) B33113231
theorem B14716991 : Blo 2295435 14716991 := bstep (se 1 (by rfl) ⟨11037743, by rfl⟩ : syracuseStep 14716991 = 22075487) B22075487
theorem B9811327 : Blo 2295435 9811327 := bstep (se 1 (by rfl) ⟨7358495, by rfl⟩ : syracuseStep 9811327 = 14716991) B14716991
theorem B13081769 : Blo 2295435 13081769 := bstep (se 2 (by rfl) ⟨4905663, by rfl⟩ : syracuseStep 13081769 = 9811327) B9811327
theorem B8721179 : Blo 2295435 8721179 := bstep (se 1 (by rfl) ⟨6540884, by rfl⟩ : syracuseStep 8721179 = 13081769) B13081769
theorem B5814119 : Blo 2295435 5814119 := bstep (se 1 (by rfl) ⟨4360589, by rfl⟩ : syracuseStep 5814119 = 8721179) B8721179
theorem B3876079 : Blo 2295435 3876079 := bstep (se 1 (by rfl) ⟨2907059, by rfl⟩ : syracuseStep 3876079 = 5814119) B5814119
theorem B5168105 : Blo 2295435 5168105 := bstep (se 2 (by rfl) ⟨1938039, by rfl⟩ : syracuseStep 5168105 = 3876079) B3876079
theorem B3445403 : Blo 2295435 3445403 := bstep (se 1 (by rfl) ⟨2584052, by rfl⟩ : syracuseStep 3445403 = 5168105) B5168105
theorem B2296935 : Blo 2295435 2296935 := bstep (se 1 (by rfl) ⟨1722701, by rfl⟩ : syracuseStep 2296935 = 3445403) B3445403
theorem B2584057 : Blo 2295435 2584057 := bbase (se 2 (by rfl) ⟨969021, by rfl⟩ : syracuseStep 2584057 = 1938043) (by norm_num)
theorem B3445409 : Blo 2295435 3445409 := bstep (se 2 (by rfl) ⟨1292028, by rfl⟩ : syracuseStep 3445409 = 2584057) B2584057
theorem B2296939 : Blo 2295435 2296939 := bstep (se 1 (by rfl) ⟨1722704, by rfl⟩ : syracuseStep 2296939 = 3445409) B3445409
theorem B4656565 : Blo 2295435 4656565 := bbase (se 5 (by rfl) ⟨218276, by rfl⟩ : syracuseStep 4656565 = 436553) (by norm_num)
theorem B6208753 : Blo 2295435 6208753 := bstep (se 2 (by rfl) ⟨2328282, by rfl⟩ : syracuseStep 6208753 = 4656565) B4656565
theorem B8278337 : Blo 2295435 8278337 := bstep (se 2 (by rfl) ⟨3104376, by rfl⟩ : syracuseStep 8278337 = 6208753) B6208753
theorem B5518891 : Blo 2295435 5518891 := bstep (se 1 (by rfl) ⟨4139168, by rfl⟩ : syracuseStep 5518891 = 8278337) B8278337
theorem B7358521 : Blo 2295435 7358521 := bstep (se 2 (by rfl) ⟨2759445, by rfl⟩ : syracuseStep 7358521 = 5518891) B5518891
theorem B9811361 : Blo 2295435 9811361 := bstep (se 2 (by rfl) ⟨3679260, by rfl⟩ : syracuseStep 9811361 = 7358521) B7358521
theorem B6540907 : Blo 2295435 6540907 := bstep (se 1 (by rfl) ⟨4905680, by rfl⟩ : syracuseStep 6540907 = 9811361) B9811361
theorem B8721209 : Blo 2295435 8721209 := bstep (se 2 (by rfl) ⟨3270453, by rfl⟩ : syracuseStep 8721209 = 6540907) B6540907
theorem B5814139 : Blo 2295435 5814139 := bstep (se 1 (by rfl) ⟨4360604, by rfl⟩ : syracuseStep 5814139 = 8721209) B8721209
theorem B7752185 : Blo 2295435 7752185 := bstep (se 2 (by rfl) ⟨2907069, by rfl⟩ : syracuseStep 7752185 = 5814139) B5814139
theorem B5168123 : Blo 2295435 5168123 := bstep (se 1 (by rfl) ⟨3876092, by rfl⟩ : syracuseStep 5168123 = 7752185) B7752185
theorem B3445415 : Blo 2295435 3445415 := bstep (se 1 (by rfl) ⟨2584061, by rfl⟩ : syracuseStep 3445415 = 5168123) B5168123
theorem B2296943 : Blo 2295435 2296943 := bstep (se 1 (by rfl) ⟨1722707, by rfl⟩ : syracuseStep 2296943 = 3445415) B3445415
theorem B3445421 : Blo 2295435 3445421 := bbase (se 3 (by rfl) ⟨646016, by rfl⟩ : syracuseStep 3445421 = 1292033) (by norm_num)
theorem B2296947 : Blo 2295435 2296947 := bstep (se 1 (by rfl) ⟨1722710, by rfl⟩ : syracuseStep 2296947 = 3445421) B3445421
theorem B5168141 : Blo 2295435 5168141 := bbase (se 3 (by rfl) ⟨969026, by rfl⟩ : syracuseStep 5168141 = 1938053) (by norm_num)
theorem B3445427 : Blo 2295435 3445427 := bstep (se 1 (by rfl) ⟨2584070, by rfl⟩ : syracuseStep 3445427 = 5168141) B5168141
theorem B2296951 : Blo 2295435 2296951 := bstep (se 1 (by rfl) ⟨1722713, by rfl⟩ : syracuseStep 2296951 = 3445427) B3445427
theorem B2907085 : Blo 2295435 2907085 := bbase (se 3 (by rfl) ⟨545078, by rfl⟩ : syracuseStep 2907085 = 1090157) (by norm_num)
theorem B3876113 : Blo 2295435 3876113 := bstep (se 2 (by rfl) ⟨1453542, by rfl⟩ : syracuseStep 3876113 = 2907085) B2907085
theorem B2584075 : Blo 2295435 2584075 := bstep (se 1 (by rfl) ⟨1938056, by rfl⟩ : syracuseStep 2584075 = 3876113) B3876113
theorem B3445433 : Blo 2295435 3445433 := bstep (se 2 (by rfl) ⟨1292037, by rfl⟩ : syracuseStep 3445433 = 2584075) B2584075
theorem B2296955 : Blo 2295435 2296955 := bstep (se 1 (by rfl) ⟨1722716, by rfl⟩ : syracuseStep 2296955 = 3445433) B3445433
theorem B11188453 : Blo 2295435 11188453 := bbase (se 4 (by rfl) ⟨1048917, by rfl⟩ : syracuseStep 11188453 = 2097835) (by norm_num)
theorem B14917937 : Blo 2295435 14917937 := bstep (se 2 (by rfl) ⟨5594226, by rfl⟩ : syracuseStep 14917937 = 11188453) B11188453
theorem B39781165 : Blo 2295435 39781165 := bstep (se 3 (by rfl) ⟨7458968, by rfl⟩ : syracuseStep 39781165 = 14917937) B14917937
theorem B53041553 : Blo 2295435 53041553 := bstep (se 2 (by rfl) ⟨19890582, by rfl⟩ : syracuseStep 53041553 = 39781165) B39781165
theorem B35361035 : Blo 2295435 35361035 := bstep (se 1 (by rfl) ⟨26520776, by rfl⟩ : syracuseStep 35361035 = 53041553) B53041553
theorem B23574023 : Blo 2295435 23574023 := bstep (se 1 (by rfl) ⟨17680517, by rfl⟩ : syracuseStep 23574023 = 35361035) B35361035
theorem B15716015 : Blo 2295435 15716015 := bstep (se 1 (by rfl) ⟨11787011, by rfl⟩ : syracuseStep 15716015 = 23574023) B23574023
theorem B10477343 : Blo 2295435 10477343 := bstep (se 1 (by rfl) ⟨7858007, by rfl⟩ : syracuseStep 10477343 = 15716015) B15716015
theorem B6984895 : Blo 2295435 6984895 := bstep (se 1 (by rfl) ⟨5238671, by rfl⟩ : syracuseStep 6984895 = 10477343) B10477343
theorem B9313193 : Blo 2295435 9313193 := bstep (se 2 (by rfl) ⟨3492447, by rfl⟩ : syracuseStep 9313193 = 6984895) B6984895
theorem B6208795 : Blo 2295435 6208795 := bstep (se 1 (by rfl) ⟨4656596, by rfl⟩ : syracuseStep 6208795 = 9313193) B9313193
theorem B33113573 : Blo 2295435 33113573 := bstep (se 4 (by rfl) ⟨3104397, by rfl⟩ : syracuseStep 33113573 = 6208795) B6208795
theorem B22075715 : Blo 2295435 22075715 := bstep (se 1 (by rfl) ⟨16556786, by rfl⟩ : syracuseStep 22075715 = 33113573) B33113573
theorem B14717143 : Blo 2295435 14717143 := bstep (se 1 (by rfl) ⟨11037857, by rfl⟩ : syracuseStep 14717143 = 22075715) B22075715
theorem B19622857 : Blo 2295435 19622857 := bstep (se 2 (by rfl) ⟨7358571, by rfl⟩ : syracuseStep 19622857 = 14717143) B14717143
theorem B26163809 : Blo 2295435 26163809 := bstep (se 2 (by rfl) ⟨9811428, by rfl⟩ : syracuseStep 26163809 = 19622857) B19622857
theorem B17442539 : Blo 2295435 17442539 := bstep (se 1 (by rfl) ⟨13081904, by rfl⟩ : syracuseStep 17442539 = 26163809) B26163809
theorem B11628359 : Blo 2295435 11628359 := bstep (se 1 (by rfl) ⟨8721269, by rfl⟩ : syracuseStep 11628359 = 17442539) B17442539
theorem B7752239 : Blo 2295435 7752239 := bstep (se 1 (by rfl) ⟨5814179, by rfl⟩ : syracuseStep 7752239 = 11628359) B11628359
theorem B5168159 : Blo 2295435 5168159 := bstep (se 1 (by rfl) ⟨3876119, by rfl⟩ : syracuseStep 5168159 = 7752239) B7752239
theorem B3445439 : Blo 2295435 3445439 := bstep (se 1 (by rfl) ⟨2584079, by rfl⟩ : syracuseStep 3445439 = 5168159) B5168159
theorem B2296959 : Blo 2295435 2296959 := bstep (se 1 (by rfl) ⟨1722719, by rfl⟩ : syracuseStep 2296959 = 3445439) B3445439
theorem B3445445 : Blo 2295435 3445445 := bbase (se 4 (by rfl) ⟨323010, by rfl⟩ : syracuseStep 3445445 = 646021) (by norm_num)
theorem B2296963 : Blo 2295435 2296963 := bstep (se 1 (by rfl) ⟨1722722, by rfl⟩ : syracuseStep 2296963 = 3445445) B3445445
theorem B3876133 : Blo 2295435 3876133 := bbase (se 4 (by rfl) ⟨363387, by rfl⟩ : syracuseStep 3876133 = 726775) (by norm_num)
theorem B5168177 : Blo 2295435 5168177 := bstep (se 2 (by rfl) ⟨1938066, by rfl⟩ : syracuseStep 5168177 = 3876133) B3876133
theorem B3445451 : Blo 2295435 3445451 := bstep (se 1 (by rfl) ⟨2584088, by rfl⟩ : syracuseStep 3445451 = 5168177) B5168177
theorem B2296967 : Blo 2295435 2296967 := bstep (se 1 (by rfl) ⟨1722725, by rfl⟩ : syracuseStep 2296967 = 3445451) B3445451
theorem B2584093 : Blo 2295435 2584093 := bbase (se 3 (by rfl) ⟨484517, by rfl⟩ : syracuseStep 2584093 = 969035) (by norm_num)
theorem B3445457 : Blo 2295435 3445457 := bstep (se 2 (by rfl) ⟨1292046, by rfl⟩ : syracuseStep 3445457 = 2584093) B2584093
theorem B2296971 : Blo 2295435 2296971 := bstep (se 1 (by rfl) ⟨1722728, by rfl⟩ : syracuseStep 2296971 = 3445457) B3445457
theorem B7752293 : Blo 2295435 7752293 := bbase (se 4 (by rfl) ⟨726777, by rfl⟩ : syracuseStep 7752293 = 1453555) (by norm_num)
theorem B5168195 : Blo 2295435 5168195 := bstep (se 1 (by rfl) ⟨3876146, by rfl⟩ : syracuseStep 5168195 = 7752293) B7752293
theorem B3445463 : Blo 2295435 3445463 := bstep (se 1 (by rfl) ⟨2584097, by rfl⟩ : syracuseStep 3445463 = 5168195) B5168195
theorem B2296975 : Blo 2295435 2296975 := bstep (se 1 (by rfl) ⟨1722731, by rfl⟩ : syracuseStep 2296975 = 3445463) B3445463
theorem B3445469 : Blo 2295435 3445469 := bbase (se 3 (by rfl) ⟨646025, by rfl⟩ : syracuseStep 3445469 = 1292051) (by norm_num)
theorem B2296979 : Blo 2295435 2296979 := bstep (se 1 (by rfl) ⟨1722734, by rfl⟩ : syracuseStep 2296979 = 3445469) B3445469
theorem B5168213 : Blo 2295435 5168213 := bbase (se 8 (by rfl) ⟨30282, by rfl⟩ : syracuseStep 5168213 = 60565) (by norm_num)
theorem B3445475 : Blo 2295435 3445475 := bstep (se 1 (by rfl) ⟨2584106, by rfl⟩ : syracuseStep 3445475 = 5168213) B5168213
theorem B2296983 : Blo 2295435 2296983 := bstep (se 1 (by rfl) ⟨1722737, by rfl⟩ : syracuseStep 2296983 = 3445475) B3445475
theorem B3929053 : Blo 2295435 3929053 := bbase (se 3 (by rfl) ⟨736697, by rfl⟩ : syracuseStep 3929053 = 1473395) (by norm_num)
theorem B5238737 : Blo 2295435 5238737 := bstep (se 2 (by rfl) ⟨1964526, by rfl⟩ : syracuseStep 5238737 = 3929053) B3929053
theorem B3492491 : Blo 2295435 3492491 := bstep (se 1 (by rfl) ⟨2619368, by rfl⟩ : syracuseStep 3492491 = 5238737) B5238737
theorem B9313309 : Blo 2295435 9313309 := bstep (se 3 (by rfl) ⟨1746245, by rfl⟩ : syracuseStep 9313309 = 3492491) B3492491
theorem B12417745 : Blo 2295435 12417745 := bstep (se 2 (by rfl) ⟨4656654, by rfl⟩ : syracuseStep 12417745 = 9313309) B9313309
theorem B16556993 : Blo 2295435 16556993 := bstep (se 2 (by rfl) ⟨6208872, by rfl⟩ : syracuseStep 16556993 = 12417745) B12417745
theorem B11037995 : Blo 2295435 11037995 := bstep (se 1 (by rfl) ⟨8278496, by rfl⟩ : syracuseStep 11037995 = 16556993) B16556993
theorem B7358663 : Blo 2295435 7358663 := bstep (se 1 (by rfl) ⟨5518997, by rfl⟩ : syracuseStep 7358663 = 11037995) B11037995
theorem B4905775 : Blo 2295435 4905775 := bstep (se 1 (by rfl) ⟨3679331, by rfl⟩ : syracuseStep 4905775 = 7358663) B7358663
theorem B6541033 : Blo 2295435 6541033 := bstep (se 2 (by rfl) ⟨2452887, by rfl⟩ : syracuseStep 6541033 = 4905775) B4905775
theorem B8721377 : Blo 2295435 8721377 := bstep (se 2 (by rfl) ⟨3270516, by rfl⟩ : syracuseStep 8721377 = 6541033) B6541033
theorem B5814251 : Blo 2295435 5814251 := bstep (se 1 (by rfl) ⟨4360688, by rfl⟩ : syracuseStep 5814251 = 8721377) B8721377
theorem B3876167 : Blo 2295435 3876167 := bstep (se 1 (by rfl) ⟨2907125, by rfl⟩ : syracuseStep 3876167 = 5814251) B5814251
theorem B2584111 : Blo 2295435 2584111 := bstep (se 1 (by rfl) ⟨1938083, by rfl⟩ : syracuseStep 2584111 = 3876167) B3876167
theorem B3445481 : Blo 2295435 3445481 := bstep (se 2 (by rfl) ⟨1292055, by rfl⟩ : syracuseStep 3445481 = 2584111) B2584111
theorem B2296987 : Blo 2295435 2296987 := bstep (se 1 (by rfl) ⟨1722740, by rfl⟩ : syracuseStep 2296987 = 3445481) B3445481
theorem B18626645 : Blo 2295435 18626645 := bbase (se 8 (by rfl) ⟨109140, by rfl⟩ : syracuseStep 18626645 = 218281) (by norm_num)
theorem B49671053 : Blo 2295435 49671053 := bstep (se 3 (by rfl) ⟨9313322, by rfl⟩ : syracuseStep 49671053 = 18626645) B18626645
theorem B33114035 : Blo 2295435 33114035 := bstep (se 1 (by rfl) ⟨24835526, by rfl⟩ : syracuseStep 33114035 = 49671053) B49671053
theorem B22076023 : Blo 2295435 22076023 := bstep (se 1 (by rfl) ⟨16557017, by rfl⟩ : syracuseStep 22076023 = 33114035) B33114035
theorem B29434697 : Blo 2295435 29434697 := bstep (se 2 (by rfl) ⟨11038011, by rfl⟩ : syracuseStep 29434697 = 22076023) B22076023
theorem B19623131 : Blo 2295435 19623131 := bstep (se 1 (by rfl) ⟨14717348, by rfl⟩ : syracuseStep 19623131 = 29434697) B29434697
theorem B13082087 : Blo 2295435 13082087 := bstep (se 1 (by rfl) ⟨9811565, by rfl⟩ : syracuseStep 13082087 = 19623131) B19623131
theorem B8721391 : Blo 2295435 8721391 := bstep (se 1 (by rfl) ⟨6541043, by rfl⟩ : syracuseStep 8721391 = 13082087) B13082087
theorem B11628521 : Blo 2295435 11628521 := bstep (se 2 (by rfl) ⟨4360695, by rfl⟩ : syracuseStep 11628521 = 8721391) B8721391
theorem B7752347 : Blo 2295435 7752347 := bstep (se 1 (by rfl) ⟨5814260, by rfl⟩ : syracuseStep 7752347 = 11628521) B11628521
theorem B5168231 : Blo 2295435 5168231 := bstep (se 1 (by rfl) ⟨3876173, by rfl⟩ : syracuseStep 5168231 = 7752347) B7752347
theorem B3445487 : Blo 2295435 3445487 := bstep (se 1 (by rfl) ⟨2584115, by rfl⟩ : syracuseStep 3445487 = 5168231) B5168231
theorem B2296991 : Blo 2295435 2296991 := bstep (se 1 (by rfl) ⟨1722743, by rfl⟩ : syracuseStep 2296991 = 3445487) B3445487
theorem B3445493 : Blo 2295435 3445493 := bbase (se 5 (by rfl) ⟨161507, by rfl⟩ : syracuseStep 3445493 = 323015) (by norm_num)
theorem B2296995 : Blo 2295435 2296995 := bstep (se 1 (by rfl) ⟨1722746, by rfl⟩ : syracuseStep 2296995 = 3445493) B3445493
theorem B2759513 : Blo 2295435 2759513 := bbase (se 2 (by rfl) ⟨1034817, by rfl⟩ : syracuseStep 2759513 = 2069635) (by norm_num)
theorem B7358701 : Blo 2295435 7358701 := bstep (se 3 (by rfl) ⟨1379756, by rfl⟩ : syracuseStep 7358701 = 2759513) B2759513
theorem B9811601 : Blo 2295435 9811601 := bstep (se 2 (by rfl) ⟨3679350, by rfl⟩ : syracuseStep 9811601 = 7358701) B7358701
theorem B6541067 : Blo 2295435 6541067 := bstep (se 1 (by rfl) ⟨4905800, by rfl⟩ : syracuseStep 6541067 = 9811601) B9811601
theorem B4360711 : Blo 2295435 4360711 := bstep (se 1 (by rfl) ⟨3270533, by rfl⟩ : syracuseStep 4360711 = 6541067) B6541067
theorem B5814281 : Blo 2295435 5814281 := bstep (se 2 (by rfl) ⟨2180355, by rfl⟩ : syracuseStep 5814281 = 4360711) B4360711
theorem B3876187 : Blo 2295435 3876187 := bstep (se 1 (by rfl) ⟨2907140, by rfl⟩ : syracuseStep 3876187 = 5814281) B5814281
theorem B5168249 : Blo 2295435 5168249 := bstep (se 2 (by rfl) ⟨1938093, by rfl⟩ : syracuseStep 5168249 = 3876187) B3876187
theorem B3445499 : Blo 2295435 3445499 := bstep (se 1 (by rfl) ⟨2584124, by rfl⟩ : syracuseStep 3445499 = 5168249) B5168249
theorem B2296999 : Blo 2295435 2296999 := bstep (se 1 (by rfl) ⟨1722749, by rfl⟩ : syracuseStep 2296999 = 3445499) B3445499
theorem B2584129 : Blo 2295435 2584129 := bbase (se 2 (by rfl) ⟨969048, by rfl⟩ : syracuseStep 2584129 = 1938097) (by norm_num)
theorem B3445505 : Blo 2295435 3445505 := bstep (se 2 (by rfl) ⟨1292064, by rfl⟩ : syracuseStep 3445505 = 2584129) B2584129
theorem B2297003 : Blo 2295435 2297003 := bstep (se 1 (by rfl) ⟨1722752, by rfl⟩ : syracuseStep 2297003 = 3445505) B3445505
theorem B5814301 : Blo 2295435 5814301 := bbase (se 3 (by rfl) ⟨1090181, by rfl⟩ : syracuseStep 5814301 = 2180363) (by norm_num)
theorem B7752401 : Blo 2295435 7752401 := bstep (se 2 (by rfl) ⟨2907150, by rfl⟩ : syracuseStep 7752401 = 5814301) B5814301
theorem B5168267 : Blo 2295435 5168267 := bstep (se 1 (by rfl) ⟨3876200, by rfl⟩ : syracuseStep 5168267 = 7752401) B7752401
theorem B3445511 : Blo 2295435 3445511 := bstep (se 1 (by rfl) ⟨2584133, by rfl⟩ : syracuseStep 3445511 = 5168267) B5168267
theorem B2297007 : Blo 2295435 2297007 := bstep (se 1 (by rfl) ⟨1722755, by rfl⟩ : syracuseStep 2297007 = 3445511) B3445511
theorem B3445517 : Blo 2295435 3445517 := bbase (se 3 (by rfl) ⟨646034, by rfl⟩ : syracuseStep 3445517 = 1292069) (by norm_num)
theorem B2297011 : Blo 2295435 2297011 := bstep (se 1 (by rfl) ⟨1722758, by rfl⟩ : syracuseStep 2297011 = 3445517) B3445517
theorem B5168285 : Blo 2295435 5168285 := bbase (se 3 (by rfl) ⟨969053, by rfl⟩ : syracuseStep 5168285 = 1938107) (by norm_num)
theorem B3445523 : Blo 2295435 3445523 := bstep (se 1 (by rfl) ⟨2584142, by rfl⟩ : syracuseStep 3445523 = 5168285) B5168285
theorem B2297015 : Blo 2295435 2297015 := bstep (se 1 (by rfl) ⟨1722761, by rfl⟩ : syracuseStep 2297015 = 3445523) B3445523
theorem B3876221 : Blo 2295435 3876221 := bbase (se 3 (by rfl) ⟨726791, by rfl⟩ : syracuseStep 3876221 = 1453583) (by norm_num)
theorem B2584147 : Blo 2295435 2584147 := bstep (se 1 (by rfl) ⟨1938110, by rfl⟩ : syracuseStep 2584147 = 3876221) B3876221
theorem B3445529 : Blo 2295435 3445529 := bstep (se 2 (by rfl) ⟨1292073, by rfl⟩ : syracuseStep 3445529 = 2584147) B2584147
theorem B2297019 : Blo 2295435 2297019 := bstep (se 1 (by rfl) ⟨1722764, by rfl⟩ : syracuseStep 2297019 = 3445529) B3445529
theorem B10477637 : Blo 2295435 10477637 := bbase (se 4 (by rfl) ⟨982278, by rfl⟩ : syracuseStep 10477637 = 1964557) (by norm_num)
theorem B6985091 : Blo 2295435 6985091 := bstep (se 1 (by rfl) ⟨5238818, by rfl⟩ : syracuseStep 6985091 = 10477637) B10477637
theorem B4656727 : Blo 2295435 4656727 := bstep (se 1 (by rfl) ⟨3492545, by rfl⟩ : syracuseStep 4656727 = 6985091) B6985091
theorem B6208969 : Blo 2295435 6208969 := bstep (se 2 (by rfl) ⟨2328363, by rfl⟩ : syracuseStep 6208969 = 4656727) B4656727
theorem B8278625 : Blo 2295435 8278625 := bstep (se 2 (by rfl) ⟨3104484, by rfl⟩ : syracuseStep 8278625 = 6208969) B6208969
theorem B5519083 : Blo 2295435 5519083 := bstep (se 1 (by rfl) ⟨4139312, by rfl⟩ : syracuseStep 5519083 = 8278625) B8278625
theorem B7358777 : Blo 2295435 7358777 := bstep (se 2 (by rfl) ⟨2759541, by rfl⟩ : syracuseStep 7358777 = 5519083) B5519083
theorem B4905851 : Blo 2295435 4905851 := bstep (se 1 (by rfl) ⟨3679388, by rfl⟩ : syracuseStep 4905851 = 7358777) B7358777
theorem B13082269 : Blo 2295435 13082269 := bstep (se 3 (by rfl) ⟨2452925, by rfl⟩ : syracuseStep 13082269 = 4905851) B4905851
theorem B17443025 : Blo 2295435 17443025 := bstep (se 2 (by rfl) ⟨6541134, by rfl⟩ : syracuseStep 17443025 = 13082269) B13082269
theorem B11628683 : Blo 2295435 11628683 := bstep (se 1 (by rfl) ⟨8721512, by rfl⟩ : syracuseStep 11628683 = 17443025) B17443025
theorem B7752455 : Blo 2295435 7752455 := bstep (se 1 (by rfl) ⟨5814341, by rfl⟩ : syracuseStep 7752455 = 11628683) B11628683
theorem B5168303 : Blo 2295435 5168303 := bstep (se 1 (by rfl) ⟨3876227, by rfl⟩ : syracuseStep 5168303 = 7752455) B7752455
theorem B3445535 : Blo 2295435 3445535 := bstep (se 1 (by rfl) ⟨2584151, by rfl⟩ : syracuseStep 3445535 = 5168303) B5168303
theorem B2297023 : Blo 2295435 2297023 := bstep (se 1 (by rfl) ⟨1722767, by rfl⟩ : syracuseStep 2297023 = 3445535) B3445535
theorem B3445541 : Blo 2295435 3445541 := bbase (se 4 (by rfl) ⟨323019, by rfl⟩ : syracuseStep 3445541 = 646039) (by norm_num)
theorem B2297027 : Blo 2295435 2297027 := bstep (se 1 (by rfl) ⟨1722770, by rfl⟩ : syracuseStep 2297027 = 3445541) B3445541
theorem B2907181 : Blo 2295435 2907181 := bbase (se 3 (by rfl) ⟨545096, by rfl⟩ : syracuseStep 2907181 = 1090193) (by norm_num)
theorem B3876241 : Blo 2295435 3876241 := bstep (se 2 (by rfl) ⟨1453590, by rfl⟩ : syracuseStep 3876241 = 2907181) B2907181
theorem B5168321 : Blo 2295435 5168321 := bstep (se 2 (by rfl) ⟨1938120, by rfl⟩ : syracuseStep 5168321 = 3876241) B3876241
theorem B3445547 : Blo 2295435 3445547 := bstep (se 1 (by rfl) ⟨2584160, by rfl⟩ : syracuseStep 3445547 = 5168321) B5168321
theorem B2297031 : Blo 2295435 2297031 := bstep (se 1 (by rfl) ⟨1722773, by rfl⟩ : syracuseStep 2297031 = 3445547) B3445547
theorem B2584165 : Blo 2295435 2584165 := bbase (se 4 (by rfl) ⟨242265, by rfl⟩ : syracuseStep 2584165 = 484531) (by norm_num)
theorem B3445553 : Blo 2295435 3445553 := bstep (se 2 (by rfl) ⟨1292082, by rfl⟩ : syracuseStep 3445553 = 2584165) B2584165
theorem B2297035 : Blo 2295435 2297035 := bstep (se 1 (by rfl) ⟨1722776, by rfl⟩ : syracuseStep 2297035 = 3445553) B3445553
theorem B11188853 : Blo 2295435 11188853 := bbase (se 5 (by rfl) ⟨524477, by rfl⟩ : syracuseStep 11188853 = 1048955) (by norm_num)
theorem B7459235 : Blo 2295435 7459235 := bstep (se 1 (by rfl) ⟨5594426, by rfl⟩ : syracuseStep 7459235 = 11188853) B11188853
theorem B4972823 : Blo 2295435 4972823 := bstep (se 1 (by rfl) ⟨3729617, by rfl⟩ : syracuseStep 4972823 = 7459235) B7459235
theorem B3315215 : Blo 2295435 3315215 := bstep (se 1 (by rfl) ⟨2486411, by rfl⟩ : syracuseStep 3315215 = 4972823) B4972823
theorem B8840573 : Blo 2295435 8840573 := bstep (se 3 (by rfl) ⟨1657607, by rfl⟩ : syracuseStep 8840573 = 3315215) B3315215
theorem B5893715 : Blo 2295435 5893715 := bstep (se 1 (by rfl) ⟨4420286, by rfl⟩ : syracuseStep 5893715 = 8840573) B8840573
theorem B3929143 : Blo 2295435 3929143 := bstep (se 1 (by rfl) ⟨2946857, by rfl⟩ : syracuseStep 3929143 = 5893715) B5893715
theorem B5238857 : Blo 2295435 5238857 := bstep (se 2 (by rfl) ⟨1964571, by rfl⟩ : syracuseStep 5238857 = 3929143) B3929143
theorem B3492571 : Blo 2295435 3492571 := bstep (se 1 (by rfl) ⟨2619428, by rfl⟩ : syracuseStep 3492571 = 5238857) B5238857
theorem B4656761 : Blo 2295435 4656761 := bstep (se 2 (by rfl) ⟨1746285, by rfl⟩ : syracuseStep 4656761 = 3492571) B3492571
theorem B3104507 : Blo 2295435 3104507 := bstep (se 1 (by rfl) ⟨2328380, by rfl⟩ : syracuseStep 3104507 = 4656761) B4656761
theorem B8278685 : Blo 2295435 8278685 := bstep (se 3 (by rfl) ⟨1552253, by rfl⟩ : syracuseStep 8278685 = 3104507) B3104507
theorem B5519123 : Blo 2295435 5519123 := bstep (se 1 (by rfl) ⟨4139342, by rfl⟩ : syracuseStep 5519123 = 8278685) B8278685
theorem B3679415 : Blo 2295435 3679415 := bstep (se 1 (by rfl) ⟨2759561, by rfl⟩ : syracuseStep 3679415 = 5519123) B5519123
theorem B2452943 : Blo 2295435 2452943 := bstep (se 1 (by rfl) ⟨1839707, by rfl⟩ : syracuseStep 2452943 = 3679415) B3679415
theorem B6541181 : Blo 2295435 6541181 := bstep (se 3 (by rfl) ⟨1226471, by rfl⟩ : syracuseStep 6541181 = 2452943) B2452943
theorem B4360787 : Blo 2295435 4360787 := bstep (se 1 (by rfl) ⟨3270590, by rfl⟩ : syracuseStep 4360787 = 6541181) B6541181
theorem B2907191 : Blo 2295435 2907191 := bstep (se 1 (by rfl) ⟨2180393, by rfl⟩ : syracuseStep 2907191 = 4360787) B4360787
theorem B7752509 : Blo 2295435 7752509 := bstep (se 3 (by rfl) ⟨1453595, by rfl⟩ : syracuseStep 7752509 = 2907191) B2907191
theorem B5168339 : Blo 2295435 5168339 := bstep (se 1 (by rfl) ⟨3876254, by rfl⟩ : syracuseStep 5168339 = 7752509) B7752509
theorem B3445559 : Blo 2295435 3445559 := bstep (se 1 (by rfl) ⟨2584169, by rfl⟩ : syracuseStep 3445559 = 5168339) B5168339
theorem B2297039 : Blo 2295435 2297039 := bstep (se 1 (by rfl) ⟨1722779, by rfl⟩ : syracuseStep 2297039 = 3445559) B3445559
theorem B3445565 : Blo 2295435 3445565 := bbase (se 3 (by rfl) ⟨646043, by rfl⟩ : syracuseStep 3445565 = 1292087) (by norm_num)
theorem B2297043 : Blo 2295435 2297043 := bstep (se 1 (by rfl) ⟨1722782, by rfl⟩ : syracuseStep 2297043 = 3445565) B3445565
theorem B5168357 : Blo 2295435 5168357 := bbase (se 4 (by rfl) ⟨484533, by rfl⟩ : syracuseStep 5168357 = 969067) (by norm_num)
theorem B3445571 : Blo 2295435 3445571 := bstep (se 1 (by rfl) ⟨2584178, by rfl⟩ : syracuseStep 3445571 = 5168357) B5168357
theorem B2297047 : Blo 2295435 2297047 := bstep (se 1 (by rfl) ⟨1722785, by rfl⟩ : syracuseStep 2297047 = 3445571) B3445571
theorem B5814413 : Blo 2295435 5814413 := bbase (se 3 (by rfl) ⟨1090202, by rfl⟩ : syracuseStep 5814413 = 2180405) (by norm_num)
theorem B3876275 : Blo 2295435 3876275 := bstep (se 1 (by rfl) ⟨2907206, by rfl⟩ : syracuseStep 3876275 = 5814413) B5814413
theorem B2584183 : Blo 2295435 2584183 := bstep (se 1 (by rfl) ⟨1938137, by rfl⟩ : syracuseStep 2584183 = 3876275) B3876275
theorem B3445577 : Blo 2295435 3445577 := bstep (se 2 (by rfl) ⟨1292091, by rfl⟩ : syracuseStep 3445577 = 2584183) B2584183
theorem B2297051 : Blo 2295435 2297051 := bstep (se 1 (by rfl) ⟨1722788, by rfl⟩ : syracuseStep 2297051 = 3445577) B3445577
theorem B3270613 : Blo 2295435 3270613 := bbase (se 7 (by rfl) ⟨38327, by rfl⟩ : syracuseStep 3270613 = 76655) (by norm_num)
theorem B4360817 : Blo 2295435 4360817 := bstep (se 2 (by rfl) ⟨1635306, by rfl⟩ : syracuseStep 4360817 = 3270613) B3270613
theorem B11628845 : Blo 2295435 11628845 := bstep (se 3 (by rfl) ⟨2180408, by rfl⟩ : syracuseStep 11628845 = 4360817) B4360817
theorem B7752563 : Blo 2295435 7752563 := bstep (se 1 (by rfl) ⟨5814422, by rfl⟩ : syracuseStep 7752563 = 11628845) B11628845
theorem B5168375 : Blo 2295435 5168375 := bstep (se 1 (by rfl) ⟨3876281, by rfl⟩ : syracuseStep 5168375 = 7752563) B7752563
theorem B3445583 : Blo 2295435 3445583 := bstep (se 1 (by rfl) ⟨2584187, by rfl⟩ : syracuseStep 3445583 = 5168375) B5168375
theorem B2297055 : Blo 2295435 2297055 := bstep (se 1 (by rfl) ⟨1722791, by rfl⟩ : syracuseStep 2297055 = 3445583) B3445583
theorem B3445589 : Blo 2295435 3445589 := bbase (se 9 (by rfl) ⟨10094, by rfl⟩ : syracuseStep 3445589 = 20189) (by norm_num)
theorem B2297059 : Blo 2295435 2297059 := bstep (se 1 (by rfl) ⟨1722794, by rfl⟩ : syracuseStep 2297059 = 3445589) B3445589
theorem B3679453 : Blo 2295435 3679453 := bbase (se 3 (by rfl) ⟨689897, by rfl⟩ : syracuseStep 3679453 = 1379795) (by norm_num)
theorem B4905937 : Blo 2295435 4905937 := bstep (se 2 (by rfl) ⟨1839726, by rfl⟩ : syracuseStep 4905937 = 3679453) B3679453
theorem B6541249 : Blo 2295435 6541249 := bstep (se 2 (by rfl) ⟨2452968, by rfl⟩ : syracuseStep 6541249 = 4905937) B4905937
theorem B8721665 : Blo 2295435 8721665 := bstep (se 2 (by rfl) ⟨3270624, by rfl⟩ : syracuseStep 8721665 = 6541249) B6541249
theorem B5814443 : Blo 2295435 5814443 := bstep (se 1 (by rfl) ⟨4360832, by rfl⟩ : syracuseStep 5814443 = 8721665) B8721665
theorem B3876295 : Blo 2295435 3876295 := bstep (se 1 (by rfl) ⟨2907221, by rfl⟩ : syracuseStep 3876295 = 5814443) B5814443
theorem B5168393 : Blo 2295435 5168393 := bstep (se 2 (by rfl) ⟨1938147, by rfl⟩ : syracuseStep 5168393 = 3876295) B3876295
theorem B3445595 : Blo 2295435 3445595 := bstep (se 1 (by rfl) ⟨2584196, by rfl⟩ : syracuseStep 3445595 = 5168393) B5168393
theorem B2297063 : Blo 2295435 2297063 := bstep (se 1 (by rfl) ⟨1722797, by rfl⟩ : syracuseStep 2297063 = 3445595) B3445595
theorem B2584201 : Blo 2295435 2584201 := bbase (se 2 (by rfl) ⟨969075, by rfl⟩ : syracuseStep 2584201 = 1938151) (by norm_num)
theorem B3445601 : Blo 2295435 3445601 := bstep (se 2 (by rfl) ⟨1292100, by rfl⟩ : syracuseStep 3445601 = 2584201) B2584201
theorem B2297067 : Blo 2295435 2297067 := bstep (se 1 (by rfl) ⟨1722800, by rfl⟩ : syracuseStep 2297067 = 3445601) B3445601
theorem B3104549 : Blo 2295435 3104549 := bbase (se 4 (by rfl) ⟨291051, by rfl⟩ : syracuseStep 3104549 = 582103) (by norm_num)
theorem B33115189 : Blo 2295435 33115189 := bstep (se 5 (by rfl) ⟨1552274, by rfl⟩ : syracuseStep 33115189 = 3104549) B3104549
theorem B44153585 : Blo 2295435 44153585 := bstep (se 2 (by rfl) ⟨16557594, by rfl⟩ : syracuseStep 44153585 = 33115189) B33115189
theorem B29435723 : Blo 2295435 29435723 := bstep (se 1 (by rfl) ⟨22076792, by rfl⟩ : syracuseStep 29435723 = 44153585) B44153585
theorem B19623815 : Blo 2295435 19623815 := bstep (se 1 (by rfl) ⟨14717861, by rfl⟩ : syracuseStep 19623815 = 29435723) B29435723
theorem B13082543 : Blo 2295435 13082543 := bstep (se 1 (by rfl) ⟨9811907, by rfl⟩ : syracuseStep 13082543 = 19623815) B19623815
theorem B8721695 : Blo 2295435 8721695 := bstep (se 1 (by rfl) ⟨6541271, by rfl⟩ : syracuseStep 8721695 = 13082543) B13082543
theorem B5814463 : Blo 2295435 5814463 := bstep (se 1 (by rfl) ⟨4360847, by rfl⟩ : syracuseStep 5814463 = 8721695) B8721695
theorem B7752617 : Blo 2295435 7752617 := bstep (se 2 (by rfl) ⟨2907231, by rfl⟩ : syracuseStep 7752617 = 5814463) B5814463
theorem B5168411 : Blo 2295435 5168411 := bstep (se 1 (by rfl) ⟨3876308, by rfl⟩ : syracuseStep 5168411 = 7752617) B7752617
theorem B3445607 : Blo 2295435 3445607 := bstep (se 1 (by rfl) ⟨2584205, by rfl⟩ : syracuseStep 3445607 = 5168411) B5168411
theorem B2297071 : Blo 2295435 2297071 := bstep (se 1 (by rfl) ⟨1722803, by rfl⟩ : syracuseStep 2297071 = 3445607) B3445607
theorem B3445613 : Blo 2295435 3445613 := bbase (se 3 (by rfl) ⟨646052, by rfl⟩ : syracuseStep 3445613 = 1292105) (by norm_num)
theorem B2297075 : Blo 2295435 2297075 := bstep (se 1 (by rfl) ⟨1722806, by rfl⟩ : syracuseStep 2297075 = 3445613) B3445613
theorem B5168429 : Blo 2295435 5168429 := bbase (se 3 (by rfl) ⟨969080, by rfl⟩ : syracuseStep 5168429 = 1938161) (by norm_num)
theorem B3445619 : Blo 2295435 3445619 := bstep (se 1 (by rfl) ⟨2584214, by rfl⟩ : syracuseStep 3445619 = 5168429) B5168429
theorem B2297079 : Blo 2295435 2297079 := bstep (se 1 (by rfl) ⟨1722809, by rfl⟩ : syracuseStep 2297079 = 3445619) B3445619
theorem B13970549 : Blo 2295435 13970549 := bbase (se 5 (by rfl) ⟨654869, by rfl⟩ : syracuseStep 13970549 = 1309739) (by norm_num)
theorem B9313699 : Blo 2295435 9313699 := bstep (se 1 (by rfl) ⟨6985274, by rfl⟩ : syracuseStep 9313699 = 13970549) B13970549
theorem B12418265 : Blo 2295435 12418265 := bstep (se 2 (by rfl) ⟨4656849, by rfl⟩ : syracuseStep 12418265 = 9313699) B9313699
theorem B8278843 : Blo 2295435 8278843 := bstep (se 1 (by rfl) ⟨6209132, by rfl⟩ : syracuseStep 8278843 = 12418265) B12418265
theorem B11038457 : Blo 2295435 11038457 := bstep (se 2 (by rfl) ⟨4139421, by rfl⟩ : syracuseStep 11038457 = 8278843) B8278843
theorem B7358971 : Blo 2295435 7358971 := bstep (se 1 (by rfl) ⟨5519228, by rfl⟩ : syracuseStep 7358971 = 11038457) B11038457
theorem B9811961 : Blo 2295435 9811961 := bstep (se 2 (by rfl) ⟨3679485, by rfl⟩ : syracuseStep 9811961 = 7358971) B7358971
theorem B6541307 : Blo 2295435 6541307 := bstep (se 1 (by rfl) ⟨4905980, by rfl⟩ : syracuseStep 6541307 = 9811961) B9811961
theorem B4360871 : Blo 2295435 4360871 := bstep (se 1 (by rfl) ⟨3270653, by rfl⟩ : syracuseStep 4360871 = 6541307) B6541307
theorem B2907247 : Blo 2295435 2907247 := bstep (se 1 (by rfl) ⟨2180435, by rfl⟩ : syracuseStep 2907247 = 4360871) B4360871
theorem B3876329 : Blo 2295435 3876329 := bstep (se 2 (by rfl) ⟨1453623, by rfl⟩ : syracuseStep 3876329 = 2907247) B2907247
theorem B2584219 : Blo 2295435 2584219 := bstep (se 1 (by rfl) ⟨1938164, by rfl⟩ : syracuseStep 2584219 = 3876329) B3876329
theorem B3445625 : Blo 2295435 3445625 := bstep (se 2 (by rfl) ⟨1292109, by rfl⟩ : syracuseStep 3445625 = 2584219) B2584219
theorem B2297083 : Blo 2295435 2297083 := bstep (se 1 (by rfl) ⟨1722812, by rfl⟩ : syracuseStep 2297083 = 3445625) B3445625
theorem B6209141 : Blo 2295435 6209141 := bbase (se 5 (by rfl) ⟨291053, by rfl⟩ : syracuseStep 6209141 = 582107) (by norm_num)
theorem B16557709 : Blo 2295435 16557709 := bstep (se 3 (by rfl) ⟨3104570, by rfl⟩ : syracuseStep 16557709 = 6209141) B6209141
theorem B22076945 : Blo 2295435 22076945 := bstep (se 2 (by rfl) ⟨8278854, by rfl⟩ : syracuseStep 22076945 = 16557709) B16557709
theorem B14717963 : Blo 2295435 14717963 := bstep (se 1 (by rfl) ⟨11038472, by rfl⟩ : syracuseStep 14717963 = 22076945) B22076945
theorem B39247901 : Blo 2295435 39247901 := bstep (se 3 (by rfl) ⟨7358981, by rfl⟩ : syracuseStep 39247901 = 14717963) B14717963
theorem B26165267 : Blo 2295435 26165267 := bstep (se 1 (by rfl) ⟨19623950, by rfl⟩ : syracuseStep 26165267 = 39247901) B39247901
theorem B17443511 : Blo 2295435 17443511 := bstep (se 1 (by rfl) ⟨13082633, by rfl⟩ : syracuseStep 17443511 = 26165267) B26165267
theorem B11629007 : Blo 2295435 11629007 := bstep (se 1 (by rfl) ⟨8721755, by rfl⟩ : syracuseStep 11629007 = 17443511) B17443511
theorem B7752671 : Blo 2295435 7752671 := bstep (se 1 (by rfl) ⟨5814503, by rfl⟩ : syracuseStep 7752671 = 11629007) B11629007
theorem B5168447 : Blo 2295435 5168447 := bstep (se 1 (by rfl) ⟨3876335, by rfl⟩ : syracuseStep 5168447 = 7752671) B7752671
theorem B3445631 : Blo 2295435 3445631 := bstep (se 1 (by rfl) ⟨2584223, by rfl⟩ : syracuseStep 3445631 = 5168447) B5168447
theorem B2297087 : Blo 2295435 2297087 := bstep (se 1 (by rfl) ⟨1722815, by rfl⟩ : syracuseStep 2297087 = 3445631) B3445631
theorem B3445637 : Blo 2295435 3445637 := bbase (se 4 (by rfl) ⟨323028, by rfl⟩ : syracuseStep 3445637 = 646057) (by norm_num)
theorem B2297091 : Blo 2295435 2297091 := bstep (se 1 (by rfl) ⟨1722818, by rfl⟩ : syracuseStep 2297091 = 3445637) B3445637
theorem B3876349 : Blo 2295435 3876349 := bbase (se 3 (by rfl) ⟨726815, by rfl⟩ : syracuseStep 3876349 = 1453631) (by norm_num)
theorem B5168465 : Blo 2295435 5168465 := bstep (se 2 (by rfl) ⟨1938174, by rfl⟩ : syracuseStep 5168465 = 3876349) B3876349
theorem B3445643 : Blo 2295435 3445643 := bstep (se 1 (by rfl) ⟨2584232, by rfl⟩ : syracuseStep 3445643 = 5168465) B5168465
theorem B2297095 : Blo 2295435 2297095 := bstep (se 1 (by rfl) ⟨1722821, by rfl⟩ : syracuseStep 2297095 = 3445643) B3445643
theorem B2584237 : Blo 2295435 2584237 := bbase (se 3 (by rfl) ⟨484544, by rfl⟩ : syracuseStep 2584237 = 969089) (by norm_num)
theorem B3445649 : Blo 2295435 3445649 := bstep (se 2 (by rfl) ⟨1292118, by rfl⟩ : syracuseStep 3445649 = 2584237) B2584237
theorem B2297099 : Blo 2295435 2297099 := bstep (se 1 (by rfl) ⟨1722824, by rfl⟩ : syracuseStep 2297099 = 3445649) B3445649
theorem B7752725 : Blo 2295435 7752725 := bbase (se 6 (by rfl) ⟨181704, by rfl⟩ : syracuseStep 7752725 = 363409) (by norm_num)
theorem B5168483 : Blo 2295435 5168483 := bstep (se 1 (by rfl) ⟨3876362, by rfl⟩ : syracuseStep 5168483 = 7752725) B7752725
theorem B3445655 : Blo 2295435 3445655 := bstep (se 1 (by rfl) ⟨2584241, by rfl⟩ : syracuseStep 3445655 = 5168483) B5168483
theorem B2297103 : Blo 2295435 2297103 := bstep (se 1 (by rfl) ⟨1722827, by rfl⟩ : syracuseStep 2297103 = 3445655) B3445655
theorem B3445661 : Blo 2295435 3445661 := bbase (se 3 (by rfl) ⟨646061, by rfl⟩ : syracuseStep 3445661 = 1292123) (by norm_num)
theorem B2297107 : Blo 2295435 2297107 := bstep (se 1 (by rfl) ⟨1722830, by rfl⟩ : syracuseStep 2297107 = 3445661) B3445661
theorem B5168501 : Blo 2295435 5168501 := bbase (se 5 (by rfl) ⟨242273, by rfl⟩ : syracuseStep 5168501 = 484547) (by norm_num)
theorem B3445667 : Blo 2295435 3445667 := bstep (se 1 (by rfl) ⟨2584250, by rfl⟩ : syracuseStep 3445667 = 5168501) B5168501
theorem B2297111 : Blo 2295435 2297111 := bstep (se 1 (by rfl) ⟨1722833, by rfl⟩ : syracuseStep 2297111 = 3445667) B3445667
theorem B2328457 : Blo 2295435 2328457 := bbase (se 2 (by rfl) ⟨873171, by rfl⟩ : syracuseStep 2328457 = 1746343) (by norm_num)
theorem B3104609 : Blo 2295435 3104609 := bstep (se 2 (by rfl) ⟨1164228, by rfl⟩ : syracuseStep 3104609 = 2328457) B2328457
theorem B8278957 : Blo 2295435 8278957 := bstep (se 3 (by rfl) ⟨1552304, by rfl⟩ : syracuseStep 8278957 = 3104609) B3104609
theorem B11038609 : Blo 2295435 11038609 := bstep (se 2 (by rfl) ⟨4139478, by rfl⟩ : syracuseStep 11038609 = 8278957) B8278957
theorem B14718145 : Blo 2295435 14718145 := bstep (se 2 (by rfl) ⟨5519304, by rfl⟩ : syracuseStep 14718145 = 11038609) B11038609
theorem B19624193 : Blo 2295435 19624193 := bstep (se 2 (by rfl) ⟨7359072, by rfl⟩ : syracuseStep 19624193 = 14718145) B14718145
theorem B13082795 : Blo 2295435 13082795 := bstep (se 1 (by rfl) ⟨9812096, by rfl⟩ : syracuseStep 13082795 = 19624193) B19624193
theorem B8721863 : Blo 2295435 8721863 := bstep (se 1 (by rfl) ⟨6541397, by rfl⟩ : syracuseStep 8721863 = 13082795) B13082795
theorem B5814575 : Blo 2295435 5814575 := bstep (se 1 (by rfl) ⟨4360931, by rfl⟩ : syracuseStep 5814575 = 8721863) B8721863
theorem B3876383 : Blo 2295435 3876383 := bstep (se 1 (by rfl) ⟨2907287, by rfl⟩ : syracuseStep 3876383 = 5814575) B5814575
theorem B2584255 : Blo 2295435 2584255 := bstep (se 1 (by rfl) ⟨1938191, by rfl⟩ : syracuseStep 2584255 = 3876383) B3876383
theorem B3445673 : Blo 2295435 3445673 := bstep (se 2 (by rfl) ⟨1292127, by rfl⟩ : syracuseStep 3445673 = 2584255) B2584255
theorem B2297115 : Blo 2295435 2297115 := bstep (se 1 (by rfl) ⟨1722836, by rfl⟩ : syracuseStep 2297115 = 3445673) B3445673
theorem B8721877 : Blo 2295435 8721877 := bbase (se 7 (by rfl) ⟨102209, by rfl⟩ : syracuseStep 8721877 = 204419) (by norm_num)
theorem B11629169 : Blo 2295435 11629169 := bstep (se 2 (by rfl) ⟨4360938, by rfl⟩ : syracuseStep 11629169 = 8721877) B8721877
theorem B7752779 : Blo 2295435 7752779 := bstep (se 1 (by rfl) ⟨5814584, by rfl⟩ : syracuseStep 7752779 = 11629169) B11629169
theorem B5168519 : Blo 2295435 5168519 := bstep (se 1 (by rfl) ⟨3876389, by rfl⟩ : syracuseStep 5168519 = 7752779) B7752779
theorem B3445679 : Blo 2295435 3445679 := bstep (se 1 (by rfl) ⟨2584259, by rfl⟩ : syracuseStep 3445679 = 5168519) B5168519
theorem B2297119 : Blo 2295435 2297119 := bstep (se 1 (by rfl) ⟨1722839, by rfl⟩ : syracuseStep 2297119 = 3445679) B3445679
theorem B3445685 : Blo 2295435 3445685 := bbase (se 5 (by rfl) ⟨161516, by rfl⟩ : syracuseStep 3445685 = 323033) (by norm_num)
theorem B2297123 : Blo 2295435 2297123 := bstep (se 1 (by rfl) ⟨1722842, by rfl⟩ : syracuseStep 2297123 = 3445685) B3445685
theorem B5814605 : Blo 2295435 5814605 := bbase (se 3 (by rfl) ⟨1090238, by rfl⟩ : syracuseStep 5814605 = 2180477) (by norm_num)
theorem B3876403 : Blo 2295435 3876403 := bstep (se 1 (by rfl) ⟨2907302, by rfl⟩ : syracuseStep 3876403 = 5814605) B5814605
theorem B5168537 : Blo 2295435 5168537 := bstep (se 2 (by rfl) ⟨1938201, by rfl⟩ : syracuseStep 5168537 = 3876403) B3876403
theorem B3445691 : Blo 2295435 3445691 := bstep (se 1 (by rfl) ⟨2584268, by rfl⟩ : syracuseStep 3445691 = 5168537) B5168537
theorem B2297127 : Blo 2295435 2297127 := bstep (se 1 (by rfl) ⟨1722845, by rfl⟩ : syracuseStep 2297127 = 3445691) B3445691
theorem B2584273 : Blo 2295435 2584273 := bbase (se 2 (by rfl) ⟨969102, by rfl⟩ : syracuseStep 2584273 = 1938205) (by norm_num)
theorem B3445697 : Blo 2295435 3445697 := bstep (se 2 (by rfl) ⟨1292136, by rfl⟩ : syracuseStep 3445697 = 2584273) B2584273
theorem B2297131 : Blo 2295435 2297131 := bstep (se 1 (by rfl) ⟨1722848, by rfl⟩ : syracuseStep 2297131 = 3445697) B3445697
theorem B7858613 : Blo 2295435 7858613 := bbase (se 5 (by rfl) ⟨368372, by rfl⟩ : syracuseStep 7858613 = 736745) (by norm_num)
theorem B5239075 : Blo 2295435 5239075 := bstep (se 1 (by rfl) ⟨3929306, by rfl⟩ : syracuseStep 5239075 = 7858613) B7858613
theorem B6985433 : Blo 2295435 6985433 := bstep (se 2 (by rfl) ⟨2619537, by rfl⟩ : syracuseStep 6985433 = 5239075) B5239075
theorem B4656955 : Blo 2295435 4656955 := bstep (se 1 (by rfl) ⟨3492716, by rfl⟩ : syracuseStep 4656955 = 6985433) B6985433
theorem B6209273 : Blo 2295435 6209273 := bstep (se 2 (by rfl) ⟨2328477, by rfl⟩ : syracuseStep 6209273 = 4656955) B4656955
theorem B4139515 : Blo 2295435 4139515 := bstep (se 1 (by rfl) ⟨3104636, by rfl⟩ : syracuseStep 4139515 = 6209273) B6209273
theorem B5519353 : Blo 2295435 5519353 := bstep (se 2 (by rfl) ⟨2069757, by rfl⟩ : syracuseStep 5519353 = 4139515) B4139515
theorem B7359137 : Blo 2295435 7359137 := bstep (se 2 (by rfl) ⟨2759676, by rfl⟩ : syracuseStep 7359137 = 5519353) B5519353
theorem B4906091 : Blo 2295435 4906091 := bstep (se 1 (by rfl) ⟨3679568, by rfl⟩ : syracuseStep 4906091 = 7359137) B7359137
theorem B3270727 : Blo 2295435 3270727 := bstep (se 1 (by rfl) ⟨2453045, by rfl⟩ : syracuseStep 3270727 = 4906091) B4906091
theorem B4360969 : Blo 2295435 4360969 := bstep (se 2 (by rfl) ⟨1635363, by rfl⟩ : syracuseStep 4360969 = 3270727) B3270727
theorem B5814625 : Blo 2295435 5814625 := bstep (se 2 (by rfl) ⟨2180484, by rfl⟩ : syracuseStep 5814625 = 4360969) B4360969
theorem B7752833 : Blo 2295435 7752833 := bstep (se 2 (by rfl) ⟨2907312, by rfl⟩ : syracuseStep 7752833 = 5814625) B5814625
theorem B5168555 : Blo 2295435 5168555 := bstep (se 1 (by rfl) ⟨3876416, by rfl⟩ : syracuseStep 5168555 = 7752833) B7752833
theorem B3445703 : Blo 2295435 3445703 := bstep (se 1 (by rfl) ⟨2584277, by rfl⟩ : syracuseStep 3445703 = 5168555) B5168555
theorem B2297135 : Blo 2295435 2297135 := bstep (se 1 (by rfl) ⟨1722851, by rfl⟩ : syracuseStep 2297135 = 3445703) B3445703
theorem B3445709 : Blo 2295435 3445709 := bbase (se 3 (by rfl) ⟨646070, by rfl⟩ : syracuseStep 3445709 = 1292141) (by norm_num)
theorem B2297139 : Blo 2295435 2297139 := bstep (se 1 (by rfl) ⟨1722854, by rfl⟩ : syracuseStep 2297139 = 3445709) B3445709
theorem B5168573 : Blo 2295435 5168573 := bbase (se 3 (by rfl) ⟨969107, by rfl⟩ : syracuseStep 5168573 = 1938215) (by norm_num)
theorem B3445715 : Blo 2295435 3445715 := bstep (se 1 (by rfl) ⟨2584286, by rfl⟩ : syracuseStep 3445715 = 5168573) B5168573
theorem B2297143 : Blo 2295435 2297143 := bstep (se 1 (by rfl) ⟨1722857, by rfl⟩ : syracuseStep 2297143 = 3445715) B3445715
theorem B3876437 : Blo 2295435 3876437 := bbase (se 8 (by rfl) ⟨22713, by rfl⟩ : syracuseStep 3876437 = 45427) (by norm_num)
theorem B2584291 : Blo 2295435 2584291 := bstep (se 1 (by rfl) ⟨1938218, by rfl⟩ : syracuseStep 2584291 = 3876437) B3876437
theorem B3445721 : Blo 2295435 3445721 := bstep (se 2 (by rfl) ⟨1292145, by rfl⟩ : syracuseStep 3445721 = 2584291) B2584291
theorem B2297147 : Blo 2295435 2297147 := bstep (se 1 (by rfl) ⟨1722860, by rfl⟩ : syracuseStep 2297147 = 3445721) B3445721
theorem B9313973 : Blo 2295435 9313973 := bbase (se 5 (by rfl) ⟨436592, by rfl⟩ : syracuseStep 9313973 = 873185) (by norm_num)
theorem B6209315 : Blo 2295435 6209315 := bstep (se 1 (by rfl) ⟨4656986, by rfl⟩ : syracuseStep 6209315 = 9313973) B9313973
theorem B4139543 : Blo 2295435 4139543 := bstep (se 1 (by rfl) ⟨3104657, by rfl⟩ : syracuseStep 4139543 = 6209315) B6209315
theorem B11038781 : Blo 2295435 11038781 := bstep (se 3 (by rfl) ⟨2069771, by rfl⟩ : syracuseStep 11038781 = 4139543) B4139543
theorem B7359187 : Blo 2295435 7359187 := bstep (se 1 (by rfl) ⟨5519390, by rfl⟩ : syracuseStep 7359187 = 11038781) B11038781
theorem B9812249 : Blo 2295435 9812249 := bstep (se 2 (by rfl) ⟨3679593, by rfl⟩ : syracuseStep 9812249 = 7359187) B7359187
theorem B6541499 : Blo 2295435 6541499 := bstep (se 1 (by rfl) ⟨4906124, by rfl⟩ : syracuseStep 6541499 = 9812249) B9812249
theorem B17443997 : Blo 2295435 17443997 := bstep (se 3 (by rfl) ⟨3270749, by rfl⟩ : syracuseStep 17443997 = 6541499) B6541499
theorem B11629331 : Blo 2295435 11629331 := bstep (se 1 (by rfl) ⟨8721998, by rfl⟩ : syracuseStep 11629331 = 17443997) B17443997
theorem B7752887 : Blo 2295435 7752887 := bstep (se 1 (by rfl) ⟨5814665, by rfl⟩ : syracuseStep 7752887 = 11629331) B11629331
theorem B5168591 : Blo 2295435 5168591 := bstep (se 1 (by rfl) ⟨3876443, by rfl⟩ : syracuseStep 5168591 = 7752887) B7752887
theorem B3445727 : Blo 2295435 3445727 := bstep (se 1 (by rfl) ⟨2584295, by rfl⟩ : syracuseStep 3445727 = 5168591) B5168591
theorem B2297151 : Blo 2295435 2297151 := bstep (se 1 (by rfl) ⟨1722863, by rfl⟩ : syracuseStep 2297151 = 3445727) B3445727
theorem B3445733 : Blo 2295435 3445733 := bbase (se 4 (by rfl) ⟨323037, by rfl⟩ : syracuseStep 3445733 = 646075) (by norm_num)
theorem B2297155 : Blo 2295435 2297155 := bstep (se 1 (by rfl) ⟨1722866, by rfl⟩ : syracuseStep 2297155 = 3445733) B3445733
theorem B3104669 : Blo 2295435 3104669 := bbase (se 3 (by rfl) ⟨582125, by rfl⟩ : syracuseStep 3104669 = 1164251) (by norm_num)
theorem B8279117 : Blo 2295435 8279117 := bstep (se 3 (by rfl) ⟨1552334, by rfl⟩ : syracuseStep 8279117 = 3104669) B3104669
theorem B5519411 : Blo 2295435 5519411 := bstep (se 1 (by rfl) ⟨4139558, by rfl⟩ : syracuseStep 5519411 = 8279117) B8279117
theorem B3679607 : Blo 2295435 3679607 := bstep (se 1 (by rfl) ⟨2759705, by rfl⟩ : syracuseStep 3679607 = 5519411) B5519411
theorem B9812285 : Blo 2295435 9812285 := bstep (se 3 (by rfl) ⟨1839803, by rfl⟩ : syracuseStep 9812285 = 3679607) B3679607
theorem B6541523 : Blo 2295435 6541523 := bstep (se 1 (by rfl) ⟨4906142, by rfl⟩ : syracuseStep 6541523 = 9812285) B9812285
theorem B4361015 : Blo 2295435 4361015 := bstep (se 1 (by rfl) ⟨3270761, by rfl⟩ : syracuseStep 4361015 = 6541523) B6541523
theorem B2907343 : Blo 2295435 2907343 := bstep (se 1 (by rfl) ⟨2180507, by rfl⟩ : syracuseStep 2907343 = 4361015) B4361015
theorem B3876457 : Blo 2295435 3876457 := bstep (se 2 (by rfl) ⟨1453671, by rfl⟩ : syracuseStep 3876457 = 2907343) B2907343
theorem B5168609 : Blo 2295435 5168609 := bstep (se 2 (by rfl) ⟨1938228, by rfl⟩ : syracuseStep 5168609 = 3876457) B3876457
theorem B3445739 : Blo 2295435 3445739 := bstep (se 1 (by rfl) ⟨2584304, by rfl⟩ : syracuseStep 3445739 = 5168609) B5168609
theorem B2297159 : Blo 2295435 2297159 := bstep (se 1 (by rfl) ⟨1722869, by rfl⟩ : syracuseStep 2297159 = 3445739) B3445739
theorem B2584309 : Blo 2295435 2584309 := bbase (se 5 (by rfl) ⟨121139, by rfl⟩ : syracuseStep 2584309 = 242279) (by norm_num)
theorem B3445745 : Blo 2295435 3445745 := bstep (se 2 (by rfl) ⟨1292154, by rfl⟩ : syracuseStep 3445745 = 2584309) B2584309
theorem B2297163 : Blo 2295435 2297163 := bstep (se 1 (by rfl) ⟨1722872, by rfl⟩ : syracuseStep 2297163 = 3445745) B3445745
theorem B2907353 : Blo 2295435 2907353 := bbase (se 2 (by rfl) ⟨1090257, by rfl⟩ : syracuseStep 2907353 = 2180515) (by norm_num)
theorem B7752941 : Blo 2295435 7752941 := bstep (se 3 (by rfl) ⟨1453676, by rfl⟩ : syracuseStep 7752941 = 2907353) B2907353
theorem B5168627 : Blo 2295435 5168627 := bstep (se 1 (by rfl) ⟨3876470, by rfl⟩ : syracuseStep 5168627 = 7752941) B7752941
theorem B3445751 : Blo 2295435 3445751 := bstep (se 1 (by rfl) ⟨2584313, by rfl⟩ : syracuseStep 3445751 = 5168627) B5168627
theorem B2297167 : Blo 2295435 2297167 := bstep (se 1 (by rfl) ⟨1722875, by rfl⟩ : syracuseStep 2297167 = 3445751) B3445751
theorem B3445757 : Blo 2295435 3445757 := bbase (se 3 (by rfl) ⟨646079, by rfl⟩ : syracuseStep 3445757 = 1292159) (by norm_num)
theorem B2297171 : Blo 2295435 2297171 := bstep (se 1 (by rfl) ⟨1722878, by rfl⟩ : syracuseStep 2297171 = 3445757) B3445757
theorem B5168645 : Blo 2295435 5168645 := bbase (se 4 (by rfl) ⟨484560, by rfl⟩ : syracuseStep 5168645 = 969121) (by norm_num)
theorem B3445763 : Blo 2295435 3445763 := bstep (se 1 (by rfl) ⟨2584322, by rfl⟩ : syracuseStep 3445763 = 5168645) B5168645
theorem B2297175 : Blo 2295435 2297175 := bstep (se 1 (by rfl) ⟨1722881, by rfl⟩ : syracuseStep 2297175 = 3445763) B3445763
theorem B4361053 : Blo 2295435 4361053 := bbase (se 3 (by rfl) ⟨817697, by rfl⟩ : syracuseStep 4361053 = 1635395) (by norm_num)
theorem B5814737 : Blo 2295435 5814737 := bstep (se 2 (by rfl) ⟨2180526, by rfl⟩ : syracuseStep 5814737 = 4361053) B4361053
theorem B3876491 : Blo 2295435 3876491 := bstep (se 1 (by rfl) ⟨2907368, by rfl⟩ : syracuseStep 3876491 = 5814737) B5814737
theorem B2584327 : Blo 2295435 2584327 := bstep (se 1 (by rfl) ⟨1938245, by rfl⟩ : syracuseStep 2584327 = 3876491) B3876491
theorem B3445769 : Blo 2295435 3445769 := bstep (se 2 (by rfl) ⟨1292163, by rfl⟩ : syracuseStep 3445769 = 2584327) B2584327
theorem B2297179 : Blo 2295435 2297179 := bstep (se 1 (by rfl) ⟨1722884, by rfl⟩ : syracuseStep 2297179 = 3445769) B3445769
theorem B11629493 : Blo 2295435 11629493 := bbase (se 5 (by rfl) ⟨545132, by rfl⟩ : syracuseStep 11629493 = 1090265) (by norm_num)
theorem B7752995 : Blo 2295435 7752995 := bstep (se 1 (by rfl) ⟨5814746, by rfl⟩ : syracuseStep 7752995 = 11629493) B11629493
theorem B5168663 : Blo 2295435 5168663 := bstep (se 1 (by rfl) ⟨3876497, by rfl⟩ : syracuseStep 5168663 = 7752995) B7752995
theorem B3445775 : Blo 2295435 3445775 := bstep (se 1 (by rfl) ⟨2584331, by rfl⟩ : syracuseStep 3445775 = 5168663) B5168663
theorem B2297183 : Blo 2295435 2297183 := bstep (se 1 (by rfl) ⟨1722887, by rfl⟩ : syracuseStep 2297183 = 3445775) B3445775
theorem B3445781 : Blo 2295435 3445781 := bbase (se 6 (by rfl) ⟨80760, by rfl⟩ : syracuseStep 3445781 = 161521) (by norm_num)
theorem B2297187 : Blo 2295435 2297187 := bstep (se 1 (by rfl) ⟨1722890, by rfl⟩ : syracuseStep 2297187 = 3445781) B3445781
theorem B5894101 : Blo 2295435 5894101 := bbase (se 7 (by rfl) ⟨69071, by rfl⟩ : syracuseStep 5894101 = 138143) (by norm_num)
theorem B7858801 : Blo 2295435 7858801 := bstep (se 2 (by rfl) ⟨2947050, by rfl⟩ : syracuseStep 7858801 = 5894101) B5894101
theorem B41913605 : Blo 2295435 41913605 := bstep (se 4 (by rfl) ⟨3929400, by rfl⟩ : syracuseStep 41913605 = 7858801) B7858801
theorem B27942403 : Blo 2295435 27942403 := bstep (se 1 (by rfl) ⟨20956802, by rfl⟩ : syracuseStep 27942403 = 41913605) B41913605
theorem B37256537 : Blo 2295435 37256537 := bstep (se 2 (by rfl) ⟨13971201, by rfl⟩ : syracuseStep 37256537 = 27942403) B27942403
theorem B24837691 : Blo 2295435 24837691 := bstep (se 1 (by rfl) ⟨18628268, by rfl⟩ : syracuseStep 24837691 = 37256537) B37256537
theorem B33116921 : Blo 2295435 33116921 := bstep (se 2 (by rfl) ⟨12418845, by rfl⟩ : syracuseStep 33116921 = 24837691) B24837691
theorem B22077947 : Blo 2295435 22077947 := bstep (se 1 (by rfl) ⟨16558460, by rfl⟩ : syracuseStep 22077947 = 33116921) B33116921
theorem B14718631 : Blo 2295435 14718631 := bstep (se 1 (by rfl) ⟨11038973, by rfl⟩ : syracuseStep 14718631 = 22077947) B22077947
theorem B19624841 : Blo 2295435 19624841 := bstep (se 2 (by rfl) ⟨7359315, by rfl⟩ : syracuseStep 19624841 = 14718631) B14718631
theorem B13083227 : Blo 2295435 13083227 := bstep (se 1 (by rfl) ⟨9812420, by rfl⟩ : syracuseStep 13083227 = 19624841) B19624841
theorem B8722151 : Blo 2295435 8722151 := bstep (se 1 (by rfl) ⟨6541613, by rfl⟩ : syracuseStep 8722151 = 13083227) B13083227
theorem B5814767 : Blo 2295435 5814767 := bstep (se 1 (by rfl) ⟨4361075, by rfl⟩ : syracuseStep 5814767 = 8722151) B8722151
theorem B3876511 : Blo 2295435 3876511 := bstep (se 1 (by rfl) ⟨2907383, by rfl⟩ : syracuseStep 3876511 = 5814767) B5814767
theorem B5168681 : Blo 2295435 5168681 := bstep (se 2 (by rfl) ⟨1938255, by rfl⟩ : syracuseStep 5168681 = 3876511) B3876511
theorem B3445787 : Blo 2295435 3445787 := bstep (se 1 (by rfl) ⟨2584340, by rfl⟩ : syracuseStep 3445787 = 5168681) B5168681
theorem B2297191 : Blo 2295435 2297191 := bstep (se 1 (by rfl) ⟨1722893, by rfl⟩ : syracuseStep 2297191 = 3445787) B3445787
theorem B2584345 : Blo 2295435 2584345 := bbase (se 2 (by rfl) ⟨969129, by rfl⟩ : syracuseStep 2584345 = 1938259) (by norm_num)
theorem B3445793 : Blo 2295435 3445793 := bstep (se 2 (by rfl) ⟨1292172, by rfl⟩ : syracuseStep 3445793 = 2584345) B2584345
theorem B2297195 : Blo 2295435 2297195 := bstep (se 1 (by rfl) ⟨1722896, by rfl⟩ : syracuseStep 2297195 = 3445793) B3445793
theorem B8722181 : Blo 2295435 8722181 := bbase (se 4 (by rfl) ⟨817704, by rfl⟩ : syracuseStep 8722181 = 1635409) (by norm_num)
theorem B5814787 : Blo 2295435 5814787 := bstep (se 1 (by rfl) ⟨4361090, by rfl⟩ : syracuseStep 5814787 = 8722181) B8722181
theorem B7753049 : Blo 2295435 7753049 := bstep (se 2 (by rfl) ⟨2907393, by rfl⟩ : syracuseStep 7753049 = 5814787) B5814787
theorem B5168699 : Blo 2295435 5168699 := bstep (se 1 (by rfl) ⟨3876524, by rfl⟩ : syracuseStep 5168699 = 7753049) B7753049
theorem B3445799 : Blo 2295435 3445799 := bstep (se 1 (by rfl) ⟨2584349, by rfl⟩ : syracuseStep 3445799 = 5168699) B5168699
theorem B2297199 : Blo 2295435 2297199 := bstep (se 1 (by rfl) ⟨1722899, by rfl⟩ : syracuseStep 2297199 = 3445799) B3445799
theorem B3445805 : Blo 2295435 3445805 := bbase (se 3 (by rfl) ⟨646088, by rfl⟩ : syracuseStep 3445805 = 1292177) (by norm_num)
theorem B2297203 : Blo 2295435 2297203 := bstep (se 1 (by rfl) ⟨1722902, by rfl⟩ : syracuseStep 2297203 = 3445805) B3445805
theorem B5168717 : Blo 2295435 5168717 := bbase (se 3 (by rfl) ⟨969134, by rfl⟩ : syracuseStep 5168717 = 1938269) (by norm_num)
theorem B3445811 : Blo 2295435 3445811 := bstep (se 1 (by rfl) ⟨2584358, by rfl⟩ : syracuseStep 3445811 = 5168717) B5168717
theorem B2297207 : Blo 2295435 2297207 := bstep (se 1 (by rfl) ⟨1722905, by rfl⟩ : syracuseStep 2297207 = 3445811) B3445811
theorem B2907409 : Blo 2295435 2907409 := bbase (se 2 (by rfl) ⟨1090278, by rfl⟩ : syracuseStep 2907409 = 2180557) (by norm_num)
theorem B3876545 : Blo 2295435 3876545 := bstep (se 2 (by rfl) ⟨1453704, by rfl⟩ : syracuseStep 3876545 = 2907409) B2907409
theorem B2584363 : Blo 2295435 2584363 := bstep (se 1 (by rfl) ⟨1938272, by rfl⟩ : syracuseStep 2584363 = 3876545) B3876545
theorem B3445817 : Blo 2295435 3445817 := bstep (se 2 (by rfl) ⟨1292181, by rfl⟩ : syracuseStep 3445817 = 2584363) B2584363
theorem B2297211 : Blo 2295435 2297211 := bstep (se 1 (by rfl) ⟨1722908, by rfl⟩ : syracuseStep 2297211 = 3445817) B3445817
theorem B4906261 : Blo 2295435 4906261 := bbase (se 6 (by rfl) ⟨114990, by rfl⟩ : syracuseStep 4906261 = 229981) (by norm_num)
theorem B26166725 : Blo 2295435 26166725 := bstep (se 4 (by rfl) ⟨2453130, by rfl⟩ : syracuseStep 26166725 = 4906261) B4906261
theorem B17444483 : Blo 2295435 17444483 := bstep (se 1 (by rfl) ⟨13083362, by rfl⟩ : syracuseStep 17444483 = 26166725) B26166725
theorem B11629655 : Blo 2295435 11629655 := bstep (se 1 (by rfl) ⟨8722241, by rfl⟩ : syracuseStep 11629655 = 17444483) B17444483
theorem B7753103 : Blo 2295435 7753103 := bstep (se 1 (by rfl) ⟨5814827, by rfl⟩ : syracuseStep 7753103 = 11629655) B11629655
theorem B5168735 : Blo 2295435 5168735 := bstep (se 1 (by rfl) ⟨3876551, by rfl⟩ : syracuseStep 5168735 = 7753103) B7753103
theorem B3445823 : Blo 2295435 3445823 := bstep (se 1 (by rfl) ⟨2584367, by rfl⟩ : syracuseStep 3445823 = 5168735) B5168735
theorem B2297215 : Blo 2295435 2297215 := bstep (se 1 (by rfl) ⟨1722911, by rfl⟩ : syracuseStep 2297215 = 3445823) B3445823
theorem B3445829 : Blo 2295435 3445829 := bbase (se 4 (by rfl) ⟨323046, by rfl⟩ : syracuseStep 3445829 = 646093) (by norm_num)
theorem B2297219 : Blo 2295435 2297219 := bstep (se 1 (by rfl) ⟨1722914, by rfl⟩ : syracuseStep 2297219 = 3445829) B3445829
theorem B3876565 : Blo 2295435 3876565 := bbase (se 7 (by rfl) ⟨45428, by rfl⟩ : syracuseStep 3876565 = 90857) (by norm_num)
theorem B5168753 : Blo 2295435 5168753 := bstep (se 2 (by rfl) ⟨1938282, by rfl⟩ : syracuseStep 5168753 = 3876565) B3876565
theorem B3445835 : Blo 2295435 3445835 := bstep (se 1 (by rfl) ⟨2584376, by rfl⟩ : syracuseStep 3445835 = 5168753) B5168753
theorem B2297223 : Blo 2295435 2297223 := bstep (se 1 (by rfl) ⟨1722917, by rfl⟩ : syracuseStep 2297223 = 3445835) B3445835
theorem B2584381 : Blo 2295435 2584381 := bbase (se 3 (by rfl) ⟨484571, by rfl⟩ : syracuseStep 2584381 = 969143) (by norm_num)
theorem B3445841 : Blo 2295435 3445841 := bstep (se 2 (by rfl) ⟨1292190, by rfl⟩ : syracuseStep 3445841 = 2584381) B2584381
theorem B2297227 : Blo 2295435 2297227 := bstep (se 1 (by rfl) ⟨1722920, by rfl⟩ : syracuseStep 2297227 = 3445841) B3445841
theorem B7753157 : Blo 2295435 7753157 := bbase (se 4 (by rfl) ⟨726858, by rfl⟩ : syracuseStep 7753157 = 1453717) (by norm_num)
theorem B5168771 : Blo 2295435 5168771 := bstep (se 1 (by rfl) ⟨3876578, by rfl⟩ : syracuseStep 5168771 = 7753157) B7753157
theorem B3445847 : Blo 2295435 3445847 := bstep (se 1 (by rfl) ⟨2584385, by rfl⟩ : syracuseStep 3445847 = 5168771) B5168771
theorem B2297231 : Blo 2295435 2297231 := bstep (se 1 (by rfl) ⟨1722923, by rfl⟩ : syracuseStep 2297231 = 3445847) B3445847
theorem B3445853 : Blo 2295435 3445853 := bbase (se 3 (by rfl) ⟨646097, by rfl⟩ : syracuseStep 3445853 = 1292195) (by norm_num)
theorem B2297235 : Blo 2295435 2297235 := bstep (se 1 (by rfl) ⟨1722926, by rfl⟩ : syracuseStep 2297235 = 3445853) B3445853
theorem B5168789 : Blo 2295435 5168789 := bbase (se 6 (by rfl) ⟨121143, by rfl⟩ : syracuseStep 5168789 = 242287) (by norm_num)
theorem B3445859 : Blo 2295435 3445859 := bstep (se 1 (by rfl) ⟨2584394, by rfl⟩ : syracuseStep 3445859 = 5168789) B5168789
theorem B2297239 : Blo 2295435 2297239 := bstep (se 1 (by rfl) ⟨1722929, by rfl⟩ : syracuseStep 2297239 = 3445859) B3445859
theorem B2453161 : Blo 2295435 2453161 := bbase (se 2 (by rfl) ⟨919935, by rfl⟩ : syracuseStep 2453161 = 1839871) (by norm_num)
theorem B3270881 : Blo 2295435 3270881 := bstep (se 2 (by rfl) ⟨1226580, by rfl⟩ : syracuseStep 3270881 = 2453161) B2453161
theorem B8722349 : Blo 2295435 8722349 := bstep (se 3 (by rfl) ⟨1635440, by rfl⟩ : syracuseStep 8722349 = 3270881) B3270881
theorem B5814899 : Blo 2295435 5814899 := bstep (se 1 (by rfl) ⟨4361174, by rfl⟩ : syracuseStep 5814899 = 8722349) B8722349
theorem B3876599 : Blo 2295435 3876599 := bstep (se 1 (by rfl) ⟨2907449, by rfl⟩ : syracuseStep 3876599 = 5814899) B5814899
theorem B2584399 : Blo 2295435 2584399 := bstep (se 1 (by rfl) ⟨1938299, by rfl⟩ : syracuseStep 2584399 = 3876599) B3876599
theorem B3445865 : Blo 2295435 3445865 := bstep (se 2 (by rfl) ⟨1292199, by rfl⟩ : syracuseStep 3445865 = 2584399) B2584399
theorem B2297243 : Blo 2295435 2297243 := bstep (se 1 (by rfl) ⟨1722932, by rfl⟩ : syracuseStep 2297243 = 3445865) B3445865
theorem B5519621 : Blo 2295435 5519621 := bbase (se 4 (by rfl) ⟨517464, by rfl⟩ : syracuseStep 5519621 = 1034929) (by norm_num)
theorem B14718989 : Blo 2295435 14718989 := bstep (se 3 (by rfl) ⟨2759810, by rfl⟩ : syracuseStep 14718989 = 5519621) B5519621
theorem B9812659 : Blo 2295435 9812659 := bstep (se 1 (by rfl) ⟨7359494, by rfl⟩ : syracuseStep 9812659 = 14718989) B14718989
theorem B13083545 : Blo 2295435 13083545 := bstep (se 2 (by rfl) ⟨4906329, by rfl⟩ : syracuseStep 13083545 = 9812659) B9812659
theorem B8722363 : Blo 2295435 8722363 := bstep (se 1 (by rfl) ⟨6541772, by rfl⟩ : syracuseStep 8722363 = 13083545) B13083545
theorem B11629817 : Blo 2295435 11629817 := bstep (se 2 (by rfl) ⟨4361181, by rfl⟩ : syracuseStep 11629817 = 8722363) B8722363
theorem B7753211 : Blo 2295435 7753211 := bstep (se 1 (by rfl) ⟨5814908, by rfl⟩ : syracuseStep 7753211 = 11629817) B11629817
theorem B5168807 : Blo 2295435 5168807 := bstep (se 1 (by rfl) ⟨3876605, by rfl⟩ : syracuseStep 5168807 = 7753211) B7753211
theorem B3445871 : Blo 2295435 3445871 := bstep (se 1 (by rfl) ⟨2584403, by rfl⟩ : syracuseStep 3445871 = 5168807) B5168807
theorem B2297247 : Blo 2295435 2297247 := bstep (se 1 (by rfl) ⟨1722935, by rfl⟩ : syracuseStep 2297247 = 3445871) B3445871
theorem B3445877 : Blo 2295435 3445877 := bbase (se 5 (by rfl) ⟨161525, by rfl⟩ : syracuseStep 3445877 = 323051) (by norm_num)
theorem B2297251 : Blo 2295435 2297251 := bstep (se 1 (by rfl) ⟨1722938, by rfl⟩ : syracuseStep 2297251 = 3445877) B3445877
theorem B4361197 : Blo 2295435 4361197 := bbase (se 3 (by rfl) ⟨817724, by rfl⟩ : syracuseStep 4361197 = 1635449) (by norm_num)
theorem B5814929 : Blo 2295435 5814929 := bstep (se 2 (by rfl) ⟨2180598, by rfl⟩ : syracuseStep 5814929 = 4361197) B4361197
theorem B3876619 : Blo 2295435 3876619 := bstep (se 1 (by rfl) ⟨2907464, by rfl⟩ : syracuseStep 3876619 = 5814929) B5814929
theorem B5168825 : Blo 2295435 5168825 := bstep (se 2 (by rfl) ⟨1938309, by rfl⟩ : syracuseStep 5168825 = 3876619) B3876619
theorem B3445883 : Blo 2295435 3445883 := bstep (se 1 (by rfl) ⟨2584412, by rfl⟩ : syracuseStep 3445883 = 5168825) B5168825
theorem B2297255 : Blo 2295435 2297255 := bstep (se 1 (by rfl) ⟨1722941, by rfl⟩ : syracuseStep 2297255 = 3445883) B3445883
theorem B2584417 : Blo 2295435 2584417 := bbase (se 2 (by rfl) ⟨969156, by rfl⟩ : syracuseStep 2584417 = 1938313) (by norm_num)
theorem B3445889 : Blo 2295435 3445889 := bstep (se 2 (by rfl) ⟨1292208, by rfl⟩ : syracuseStep 3445889 = 2584417) B2584417
theorem B2297259 : Blo 2295435 2297259 := bstep (se 1 (by rfl) ⟨1722944, by rfl⟩ : syracuseStep 2297259 = 3445889) B3445889
theorem B5814949 : Blo 2295435 5814949 := bbase (se 4 (by rfl) ⟨545151, by rfl⟩ : syracuseStep 5814949 = 1090303) (by norm_num)
theorem B7753265 : Blo 2295435 7753265 := bstep (se 2 (by rfl) ⟨2907474, by rfl⟩ : syracuseStep 7753265 = 5814949) B5814949
theorem B5168843 : Blo 2295435 5168843 := bstep (se 1 (by rfl) ⟨3876632, by rfl⟩ : syracuseStep 5168843 = 7753265) B7753265
theorem B3445895 : Blo 2295435 3445895 := bstep (se 1 (by rfl) ⟨2584421, by rfl⟩ : syracuseStep 3445895 = 5168843) B5168843
theorem B2297263 : Blo 2295435 2297263 := bstep (se 1 (by rfl) ⟨1722947, by rfl⟩ : syracuseStep 2297263 = 3445895) B3445895
theorem B3445901 : Blo 2295435 3445901 := bbase (se 3 (by rfl) ⟨646106, by rfl⟩ : syracuseStep 3445901 = 1292213) (by norm_num)
theorem B2297267 : Blo 2295435 2297267 := bstep (se 1 (by rfl) ⟨1722950, by rfl⟩ : syracuseStep 2297267 = 3445901) B3445901
theorem B5168861 : Blo 2295435 5168861 := bbase (se 3 (by rfl) ⟨969161, by rfl⟩ : syracuseStep 5168861 = 1938323) (by norm_num)
theorem B3445907 : Blo 2295435 3445907 := bstep (se 1 (by rfl) ⟨2584430, by rfl⟩ : syracuseStep 3445907 = 5168861) B5168861
theorem B2297271 : Blo 2295435 2297271 := bstep (se 1 (by rfl) ⟨1722953, by rfl⟩ : syracuseStep 2297271 = 3445907) B3445907
theorem B3876653 : Blo 2295435 3876653 := bbase (se 3 (by rfl) ⟨726872, by rfl⟩ : syracuseStep 3876653 = 1453745) (by norm_num)
theorem B2584435 : Blo 2295435 2584435 := bstep (se 1 (by rfl) ⟨1938326, by rfl⟩ : syracuseStep 2584435 = 3876653) B3876653
theorem B3445913 : Blo 2295435 3445913 := bstep (se 2 (by rfl) ⟨1292217, by rfl⟩ : syracuseStep 3445913 = 2584435) B2584435
theorem B2297275 : Blo 2295435 2297275 := bstep (se 1 (by rfl) ⟨1722956, by rfl⟩ : syracuseStep 2297275 = 3445913) B3445913
theorem B16559093 : Blo 2295435 16559093 := bbase (se 5 (by rfl) ⟨776207, by rfl⟩ : syracuseStep 16559093 = 1552415) (by norm_num)
theorem B44157581 : Blo 2295435 44157581 := bstep (se 3 (by rfl) ⟨8279546, by rfl⟩ : syracuseStep 44157581 = 16559093) B16559093
theorem B29438387 : Blo 2295435 29438387 := bstep (se 1 (by rfl) ⟨22078790, by rfl⟩ : syracuseStep 29438387 = 44157581) B44157581
theorem B19625591 : Blo 2295435 19625591 := bstep (se 1 (by rfl) ⟨14719193, by rfl⟩ : syracuseStep 19625591 = 29438387) B29438387
theorem B13083727 : Blo 2295435 13083727 := bstep (se 1 (by rfl) ⟨9812795, by rfl⟩ : syracuseStep 13083727 = 19625591) B19625591
theorem B17444969 : Blo 2295435 17444969 := bstep (se 2 (by rfl) ⟨6541863, by rfl⟩ : syracuseStep 17444969 = 13083727) B13083727
theorem B11629979 : Blo 2295435 11629979 := bstep (se 1 (by rfl) ⟨8722484, by rfl⟩ : syracuseStep 11629979 = 17444969) B17444969
theorem B7753319 : Blo 2295435 7753319 := bstep (se 1 (by rfl) ⟨5814989, by rfl⟩ : syracuseStep 7753319 = 11629979) B11629979
theorem B5168879 : Blo 2295435 5168879 := bstep (se 1 (by rfl) ⟨3876659, by rfl⟩ : syracuseStep 5168879 = 7753319) B7753319
theorem B3445919 : Blo 2295435 3445919 := bstep (se 1 (by rfl) ⟨2584439, by rfl⟩ : syracuseStep 3445919 = 5168879) B5168879
theorem B2297279 : Blo 2295435 2297279 := bstep (se 1 (by rfl) ⟨1722959, by rfl⟩ : syracuseStep 2297279 = 3445919) B3445919
theorem B3445925 : Blo 2295435 3445925 := bbase (se 4 (by rfl) ⟨323055, by rfl⟩ : syracuseStep 3445925 = 646111) (by norm_num)
theorem B2297283 : Blo 2295435 2297283 := bstep (se 1 (by rfl) ⟨1722962, by rfl⟩ : syracuseStep 2297283 = 3445925) B3445925
theorem B2907505 : Blo 2295435 2907505 := bbase (se 2 (by rfl) ⟨1090314, by rfl⟩ : syracuseStep 2907505 = 2180629) (by norm_num)
theorem B3876673 : Blo 2295435 3876673 := bstep (se 2 (by rfl) ⟨1453752, by rfl⟩ : syracuseStep 3876673 = 2907505) B2907505
theorem B5168897 : Blo 2295435 5168897 := bstep (se 2 (by rfl) ⟨1938336, by rfl⟩ : syracuseStep 5168897 = 3876673) B3876673
theorem B3445931 : Blo 2295435 3445931 := bstep (se 1 (by rfl) ⟨2584448, by rfl⟩ : syracuseStep 3445931 = 5168897) B5168897
theorem B2297287 : Blo 2295435 2297287 := bstep (se 1 (by rfl) ⟨1722965, by rfl⟩ : syracuseStep 2297287 = 3445931) B3445931
theorem B2584453 : Blo 2295435 2584453 := bbase (se 4 (by rfl) ⟨242292, by rfl⟩ : syracuseStep 2584453 = 484585) (by norm_num)
theorem B3445937 : Blo 2295435 3445937 := bstep (se 2 (by rfl) ⟨1292226, by rfl⟩ : syracuseStep 3445937 = 2584453) B2584453
theorem B2297291 : Blo 2295435 2297291 := bstep (se 1 (by rfl) ⟨1722968, by rfl⟩ : syracuseStep 2297291 = 3445937) B3445937
theorem B2759869 : Blo 2295435 2759869 := bbase (se 3 (by rfl) ⟨517475, by rfl⟩ : syracuseStep 2759869 = 1034951) (by norm_num)
theorem B3679825 : Blo 2295435 3679825 := bstep (se 2 (by rfl) ⟨1379934, by rfl⟩ : syracuseStep 3679825 = 2759869) B2759869
theorem B4906433 : Blo 2295435 4906433 := bstep (se 2 (by rfl) ⟨1839912, by rfl⟩ : syracuseStep 4906433 = 3679825) B3679825
theorem B3270955 : Blo 2295435 3270955 := bstep (se 1 (by rfl) ⟨2453216, by rfl⟩ : syracuseStep 3270955 = 4906433) B4906433
theorem B4361273 : Blo 2295435 4361273 := bstep (se 2 (by rfl) ⟨1635477, by rfl⟩ : syracuseStep 4361273 = 3270955) B3270955
theorem B2907515 : Blo 2295435 2907515 := bstep (se 1 (by rfl) ⟨2180636, by rfl⟩ : syracuseStep 2907515 = 4361273) B4361273
theorem B7753373 : Blo 2295435 7753373 := bstep (se 3 (by rfl) ⟨1453757, by rfl⟩ : syracuseStep 7753373 = 2907515) B2907515
theorem B5168915 : Blo 2295435 5168915 := bstep (se 1 (by rfl) ⟨3876686, by rfl⟩ : syracuseStep 5168915 = 7753373) B7753373
theorem B3445943 : Blo 2295435 3445943 := bstep (se 1 (by rfl) ⟨2584457, by rfl⟩ : syracuseStep 3445943 = 5168915) B5168915
theorem B2297295 : Blo 2295435 2297295 := bstep (se 1 (by rfl) ⟨1722971, by rfl⟩ : syracuseStep 2297295 = 3445943) B3445943
theorem B3445949 : Blo 2295435 3445949 := bbase (se 3 (by rfl) ⟨646115, by rfl⟩ : syracuseStep 3445949 = 1292231) (by norm_num)
theorem B2297299 : Blo 2295435 2297299 := bstep (se 1 (by rfl) ⟨1722974, by rfl⟩ : syracuseStep 2297299 = 3445949) B3445949
theorem B5168933 : Blo 2295435 5168933 := bbase (se 4 (by rfl) ⟨484587, by rfl⟩ : syracuseStep 5168933 = 969175) (by norm_num)
theorem B3445955 : Blo 2295435 3445955 := bstep (se 1 (by rfl) ⟨2584466, by rfl⟩ : syracuseStep 3445955 = 5168933) B5168933
theorem B2297303 : Blo 2295435 2297303 := bstep (se 1 (by rfl) ⟨1722977, by rfl⟩ : syracuseStep 2297303 = 3445955) B3445955
theorem B5815061 : Blo 2295435 5815061 := bbase (se 6 (by rfl) ⟨136290, by rfl⟩ : syracuseStep 5815061 = 272581) (by norm_num)
theorem B3876707 : Blo 2295435 3876707 := bstep (se 1 (by rfl) ⟨2907530, by rfl⟩ : syracuseStep 3876707 = 5815061) B5815061
theorem B2584471 : Blo 2295435 2584471 := bstep (se 1 (by rfl) ⟨1938353, by rfl⟩ : syracuseStep 2584471 = 3876707) B3876707
theorem B3445961 : Blo 2295435 3445961 := bstep (se 2 (by rfl) ⟨1292235, by rfl⟩ : syracuseStep 3445961 = 2584471) B2584471
theorem B2297307 : Blo 2295435 2297307 := bstep (se 1 (by rfl) ⟨1722980, by rfl⟩ : syracuseStep 2297307 = 3445961) B3445961
theorem B9812933 : Blo 2295435 9812933 := bbase (se 4 (by rfl) ⟨919962, by rfl⟩ : syracuseStep 9812933 = 1839925) (by norm_num)
theorem B6541955 : Blo 2295435 6541955 := bstep (se 1 (by rfl) ⟨4906466, by rfl⟩ : syracuseStep 6541955 = 9812933) B9812933
theorem B4361303 : Blo 2295435 4361303 := bstep (se 1 (by rfl) ⟨3270977, by rfl⟩ : syracuseStep 4361303 = 6541955) B6541955
theorem B11630141 : Blo 2295435 11630141 := bstep (se 3 (by rfl) ⟨2180651, by rfl⟩ : syracuseStep 11630141 = 4361303) B4361303
theorem B7753427 : Blo 2295435 7753427 := bstep (se 1 (by rfl) ⟨5815070, by rfl⟩ : syracuseStep 7753427 = 11630141) B11630141
theorem B5168951 : Blo 2295435 5168951 := bstep (se 1 (by rfl) ⟨3876713, by rfl⟩ : syracuseStep 5168951 = 7753427) B7753427
theorem B3445967 : Blo 2295435 3445967 := bstep (se 1 (by rfl) ⟨2584475, by rfl⟩ : syracuseStep 3445967 = 5168951) B5168951
theorem B2297311 : Blo 2295435 2297311 := bstep (se 1 (by rfl) ⟨1722983, by rfl⟩ : syracuseStep 2297311 = 3445967) B3445967
theorem B3445973 : Blo 2295435 3445973 := bbase (se 7 (by rfl) ⟨40382, by rfl⟩ : syracuseStep 3445973 = 80765) (by norm_num)
theorem B2297315 : Blo 2295435 2297315 := bstep (se 1 (by rfl) ⟨1722986, by rfl⟩ : syracuseStep 2297315 = 3445973) B3445973
theorem B3270989 : Blo 2295435 3270989 := bbase (se 3 (by rfl) ⟨613310, by rfl⟩ : syracuseStep 3270989 = 1226621) (by norm_num)
theorem B8722637 : Blo 2295435 8722637 := bstep (se 3 (by rfl) ⟨1635494, by rfl⟩ : syracuseStep 8722637 = 3270989) B3270989
theorem B5815091 : Blo 2295435 5815091 := bstep (se 1 (by rfl) ⟨4361318, by rfl⟩ : syracuseStep 5815091 = 8722637) B8722637
theorem B3876727 : Blo 2295435 3876727 := bstep (se 1 (by rfl) ⟨2907545, by rfl⟩ : syracuseStep 3876727 = 5815091) B5815091
theorem B5168969 : Blo 2295435 5168969 := bstep (se 2 (by rfl) ⟨1938363, by rfl⟩ : syracuseStep 5168969 = 3876727) B3876727
theorem B3445979 : Blo 2295435 3445979 := bstep (se 1 (by rfl) ⟨2584484, by rfl⟩ : syracuseStep 3445979 = 5168969) B5168969
theorem B2297319 : Blo 2295435 2297319 := bstep (se 1 (by rfl) ⟨1722989, by rfl⟩ : syracuseStep 2297319 = 3445979) B3445979
theorem B2584489 : Blo 2295435 2584489 := bbase (se 2 (by rfl) ⟨969183, by rfl⟩ : syracuseStep 2584489 = 1938367) (by norm_num)
theorem B3445985 : Blo 2295435 3445985 := bstep (se 2 (by rfl) ⟨1292244, by rfl⟩ : syracuseStep 3445985 = 2584489) B2584489
theorem B2297323 : Blo 2295435 2297323 := bstep (se 1 (by rfl) ⟨1722992, by rfl⟩ : syracuseStep 2297323 = 3445985) B3445985
theorem B7460165 : Blo 2295435 7460165 := bbase (se 4 (by rfl) ⟨699390, by rfl⟩ : syracuseStep 7460165 = 1398781) (by norm_num)
theorem B4973443 : Blo 2295435 4973443 := bstep (se 1 (by rfl) ⟨3730082, by rfl⟩ : syracuseStep 4973443 = 7460165) B7460165
theorem B26525029 : Blo 2295435 26525029 := bstep (se 4 (by rfl) ⟨2486721, by rfl⟩ : syracuseStep 26525029 = 4973443) B4973443
theorem B35366705 : Blo 2295435 35366705 := bstep (se 2 (by rfl) ⟨13262514, by rfl⟩ : syracuseStep 35366705 = 26525029) B26525029
theorem B23577803 : Blo 2295435 23577803 := bstep (se 1 (by rfl) ⟨17683352, by rfl⟩ : syracuseStep 23577803 = 35366705) B35366705
theorem B15718535 : Blo 2295435 15718535 := bstep (se 1 (by rfl) ⟨11788901, by rfl⟩ : syracuseStep 15718535 = 23577803) B23577803
theorem B10479023 : Blo 2295435 10479023 := bstep (se 1 (by rfl) ⟨7859267, by rfl⟩ : syracuseStep 10479023 = 15718535) B15718535
theorem B6986015 : Blo 2295435 6986015 := bstep (se 1 (by rfl) ⟨5239511, by rfl⟩ : syracuseStep 6986015 = 10479023) B10479023
theorem B4657343 : Blo 2295435 4657343 := bstep (se 1 (by rfl) ⟨3493007, by rfl⟩ : syracuseStep 4657343 = 6986015) B6986015
theorem B12419581 : Blo 2295435 12419581 := bstep (se 3 (by rfl) ⟨2328671, by rfl⟩ : syracuseStep 12419581 = 4657343) B4657343
theorem B16559441 : Blo 2295435 16559441 := bstep (se 2 (by rfl) ⟨6209790, by rfl⟩ : syracuseStep 16559441 = 12419581) B12419581
theorem B11039627 : Blo 2295435 11039627 := bstep (se 1 (by rfl) ⟨8279720, by rfl⟩ : syracuseStep 11039627 = 16559441) B16559441
theorem B7359751 : Blo 2295435 7359751 := bstep (se 1 (by rfl) ⟨5519813, by rfl⟩ : syracuseStep 7359751 = 11039627) B11039627
theorem B9813001 : Blo 2295435 9813001 := bstep (se 2 (by rfl) ⟨3679875, by rfl⟩ : syracuseStep 9813001 = 7359751) B7359751
theorem B13084001 : Blo 2295435 13084001 := bstep (se 2 (by rfl) ⟨4906500, by rfl⟩ : syracuseStep 13084001 = 9813001) B9813001
theorem B8722667 : Blo 2295435 8722667 := bstep (se 1 (by rfl) ⟨6542000, by rfl⟩ : syracuseStep 8722667 = 13084001) B13084001
theorem B5815111 : Blo 2295435 5815111 := bstep (se 1 (by rfl) ⟨4361333, by rfl⟩ : syracuseStep 5815111 = 8722667) B8722667
theorem B7753481 : Blo 2295435 7753481 := bstep (se 2 (by rfl) ⟨2907555, by rfl⟩ : syracuseStep 7753481 = 5815111) B5815111
theorem B5168987 : Blo 2295435 5168987 := bstep (se 1 (by rfl) ⟨3876740, by rfl⟩ : syracuseStep 5168987 = 7753481) B7753481
theorem B3445991 : Blo 2295435 3445991 := bstep (se 1 (by rfl) ⟨2584493, by rfl⟩ : syracuseStep 3445991 = 5168987) B5168987
theorem B2297327 : Blo 2295435 2297327 := bstep (se 1 (by rfl) ⟨1722995, by rfl⟩ : syracuseStep 2297327 = 3445991) B3445991
theorem B3445997 : Blo 2295435 3445997 := bbase (se 3 (by rfl) ⟨646124, by rfl⟩ : syracuseStep 3445997 = 1292249) (by norm_num)
theorem B2297331 : Blo 2295435 2297331 := bstep (se 1 (by rfl) ⟨1722998, by rfl⟩ : syracuseStep 2297331 = 3445997) B3445997
theorem B5169005 : Blo 2295435 5169005 := bbase (se 3 (by rfl) ⟨969188, by rfl⟩ : syracuseStep 5169005 = 1938377) (by norm_num)
theorem B3446003 : Blo 2295435 3446003 := bstep (se 1 (by rfl) ⟨2584502, by rfl⟩ : syracuseStep 3446003 = 5169005) B5169005
theorem B2297335 : Blo 2295435 2297335 := bstep (se 1 (by rfl) ⟨1723001, by rfl⟩ : syracuseStep 2297335 = 3446003) B3446003
theorem B4361357 : Blo 2295435 4361357 := bbase (se 3 (by rfl) ⟨817754, by rfl⟩ : syracuseStep 4361357 = 1635509) (by norm_num)
theorem B2907571 : Blo 2295435 2907571 := bstep (se 1 (by rfl) ⟨2180678, by rfl⟩ : syracuseStep 2907571 = 4361357) B4361357
theorem B3876761 : Blo 2295435 3876761 := bstep (se 2 (by rfl) ⟨1453785, by rfl⟩ : syracuseStep 3876761 = 2907571) B2907571
theorem B2584507 : Blo 2295435 2584507 := bstep (se 1 (by rfl) ⟨1938380, by rfl⟩ : syracuseStep 2584507 = 3876761) B3876761
theorem B3446009 : Blo 2295435 3446009 := bstep (se 2 (by rfl) ⟨1292253, by rfl⟩ : syracuseStep 3446009 = 2584507) B2584507
theorem B2297339 : Blo 2295435 2297339 := bstep (se 1 (by rfl) ⟨1723004, by rfl⟩ : syracuseStep 2297339 = 3446009) B3446009
theorem B11190325 : Blo 2295435 11190325 := bbase (se 5 (by rfl) ⟨524546, by rfl⟩ : syracuseStep 11190325 = 1049093) (by norm_num)
theorem B14920433 : Blo 2295435 14920433 := bstep (se 2 (by rfl) ⟨5595162, by rfl⟩ : syracuseStep 14920433 = 11190325) B11190325
theorem B9946955 : Blo 2295435 9946955 := bstep (se 1 (by rfl) ⟨7460216, by rfl⟩ : syracuseStep 9946955 = 14920433) B14920433
theorem B6631303 : Blo 2295435 6631303 := bstep (se 1 (by rfl) ⟨4973477, by rfl⟩ : syracuseStep 6631303 = 9946955) B9946955
theorem B8841737 : Blo 2295435 8841737 := bstep (se 2 (by rfl) ⟨3315651, by rfl⟩ : syracuseStep 8841737 = 6631303) B6631303
theorem B23577965 : Blo 2295435 23577965 := bstep (se 3 (by rfl) ⟨4420868, by rfl⟩ : syracuseStep 23577965 = 8841737) B8841737
theorem B15718643 : Blo 2295435 15718643 := bstep (se 1 (by rfl) ⟨11788982, by rfl⟩ : syracuseStep 15718643 = 23577965) B23577965
theorem B10479095 : Blo 2295435 10479095 := bstep (se 1 (by rfl) ⟨7859321, by rfl⟩ : syracuseStep 10479095 = 15718643) B15718643
theorem B6986063 : Blo 2295435 6986063 := bstep (se 1 (by rfl) ⟨5239547, by rfl⟩ : syracuseStep 6986063 = 10479095) B10479095
theorem B4657375 : Blo 2295435 4657375 := bstep (se 1 (by rfl) ⟨3493031, by rfl⟩ : syracuseStep 4657375 = 6986063) B6986063
theorem B6209833 : Blo 2295435 6209833 := bstep (se 2 (by rfl) ⟨2328687, by rfl⟩ : syracuseStep 6209833 = 4657375) B4657375
theorem B8279777 : Blo 2295435 8279777 := bstep (se 2 (by rfl) ⟨3104916, by rfl⟩ : syracuseStep 8279777 = 6209833) B6209833
theorem B22079405 : Blo 2295435 22079405 := bstep (se 3 (by rfl) ⟨4139888, by rfl⟩ : syracuseStep 22079405 = 8279777) B8279777
theorem B58878413 : Blo 2295435 58878413 := bstep (se 3 (by rfl) ⟨11039702, by rfl⟩ : syracuseStep 58878413 = 22079405) B22079405
theorem B39252275 : Blo 2295435 39252275 := bstep (se 1 (by rfl) ⟨29439206, by rfl⟩ : syracuseStep 39252275 = 58878413) B58878413
theorem B26168183 : Blo 2295435 26168183 := bstep (se 1 (by rfl) ⟨19626137, by rfl⟩ : syracuseStep 26168183 = 39252275) B39252275
theorem B17445455 : Blo 2295435 17445455 := bstep (se 1 (by rfl) ⟨13084091, by rfl⟩ : syracuseStep 17445455 = 26168183) B26168183
theorem B11630303 : Blo 2295435 11630303 := bstep (se 1 (by rfl) ⟨8722727, by rfl⟩ : syracuseStep 11630303 = 17445455) B17445455
theorem B7753535 : Blo 2295435 7753535 := bstep (se 1 (by rfl) ⟨5815151, by rfl⟩ : syracuseStep 7753535 = 11630303) B11630303
theorem B5169023 : Blo 2295435 5169023 := bstep (se 1 (by rfl) ⟨3876767, by rfl⟩ : syracuseStep 5169023 = 7753535) B7753535
theorem B3446015 : Blo 2295435 3446015 := bstep (se 1 (by rfl) ⟨2584511, by rfl⟩ : syracuseStep 3446015 = 5169023) B5169023
theorem B2297343 : Blo 2295435 2297343 := bstep (se 1 (by rfl) ⟨1723007, by rfl⟩ : syracuseStep 2297343 = 3446015) B3446015
theorem B3446021 : Blo 2295435 3446021 := bbase (se 4 (by rfl) ⟨323064, by rfl⟩ : syracuseStep 3446021 = 646129) (by norm_num)
theorem B2297347 : Blo 2295435 2297347 := bstep (se 1 (by rfl) ⟨1723010, by rfl⟩ : syracuseStep 2297347 = 3446021) B3446021
theorem B3876781 : Blo 2295435 3876781 := bbase (se 3 (by rfl) ⟨726896, by rfl⟩ : syracuseStep 3876781 = 1453793) (by norm_num)
theorem B5169041 : Blo 2295435 5169041 := bstep (se 2 (by rfl) ⟨1938390, by rfl⟩ : syracuseStep 5169041 = 3876781) B3876781
theorem B3446027 : Blo 2295435 3446027 := bstep (se 1 (by rfl) ⟨2584520, by rfl⟩ : syracuseStep 3446027 = 5169041) B5169041
theorem B2297351 : Blo 2295435 2297351 := bstep (se 1 (by rfl) ⟨1723013, by rfl⟩ : syracuseStep 2297351 = 3446027) B3446027
theorem B2584525 : Blo 2295435 2584525 := bbase (se 3 (by rfl) ⟨484598, by rfl⟩ : syracuseStep 2584525 = 969197) (by norm_num)
theorem B3446033 : Blo 2295435 3446033 := bstep (se 2 (by rfl) ⟨1292262, by rfl⟩ : syracuseStep 3446033 = 2584525) B2584525
theorem B2297355 : Blo 2295435 2297355 := bstep (se 1 (by rfl) ⟨1723016, by rfl⟩ : syracuseStep 2297355 = 3446033) B3446033
theorem B7753589 : Blo 2295435 7753589 := bbase (se 5 (by rfl) ⟨363449, by rfl⟩ : syracuseStep 7753589 = 726899) (by norm_num)
theorem B5169059 : Blo 2295435 5169059 := bstep (se 1 (by rfl) ⟨3876794, by rfl⟩ : syracuseStep 5169059 = 7753589) B7753589
theorem B3446039 : Blo 2295435 3446039 := bstep (se 1 (by rfl) ⟨2584529, by rfl⟩ : syracuseStep 3446039 = 5169059) B5169059
theorem B2297359 : Blo 2295435 2297359 := bstep (se 1 (by rfl) ⟨1723019, by rfl⟩ : syracuseStep 2297359 = 3446039) B3446039
theorem B3446045 : Blo 2295435 3446045 := bbase (se 3 (by rfl) ⟨646133, by rfl⟩ : syracuseStep 3446045 = 1292267) (by norm_num)
theorem B2297363 : Blo 2295435 2297363 := bstep (se 1 (by rfl) ⟨1723022, by rfl⟩ : syracuseStep 2297363 = 3446045) B3446045
theorem B5169077 : Blo 2295435 5169077 := bbase (se 5 (by rfl) ⟨242300, by rfl⟩ : syracuseStep 5169077 = 484601) (by norm_num)
theorem B3446051 : Blo 2295435 3446051 := bstep (se 1 (by rfl) ⟨2584538, by rfl⟩ : syracuseStep 3446051 = 5169077) B5169077
theorem B2297367 : Blo 2295435 2297367 := bstep (se 1 (by rfl) ⟨1723025, by rfl⟩ : syracuseStep 2297367 = 3446051) B3446051
theorem B7359893 : Blo 2295435 7359893 := bbase (se 6 (by rfl) ⟨172497, by rfl⟩ : syracuseStep 7359893 = 344995) (by norm_num)
theorem B4906595 : Blo 2295435 4906595 := bstep (se 1 (by rfl) ⟨3679946, by rfl⟩ : syracuseStep 4906595 = 7359893) B7359893
theorem B13084253 : Blo 2295435 13084253 := bstep (se 3 (by rfl) ⟨2453297, by rfl⟩ : syracuseStep 13084253 = 4906595) B4906595
theorem B8722835 : Blo 2295435 8722835 := bstep (se 1 (by rfl) ⟨6542126, by rfl⟩ : syracuseStep 8722835 = 13084253) B13084253
theorem B5815223 : Blo 2295435 5815223 := bstep (se 1 (by rfl) ⟨4361417, by rfl⟩ : syracuseStep 5815223 = 8722835) B8722835
theorem B3876815 : Blo 2295435 3876815 := bstep (se 1 (by rfl) ⟨2907611, by rfl⟩ : syracuseStep 3876815 = 5815223) B5815223
theorem B2584543 : Blo 2295435 2584543 := bstep (se 1 (by rfl) ⟨1938407, by rfl⟩ : syracuseStep 2584543 = 3876815) B3876815
theorem B3446057 : Blo 2295435 3446057 := bstep (se 2 (by rfl) ⟨1292271, by rfl⟩ : syracuseStep 3446057 = 2584543) B2584543
theorem B2297371 : Blo 2295435 2297371 := bstep (se 1 (by rfl) ⟨1723028, by rfl⟩ : syracuseStep 2297371 = 3446057) B3446057
theorem B3929717 : Blo 2295435 3929717 := bbase (se 5 (by rfl) ⟨184205, by rfl⟩ : syracuseStep 3929717 = 368411) (by norm_num)
theorem B2619811 : Blo 2295435 2619811 := bstep (se 1 (by rfl) ⟨1964858, by rfl⟩ : syracuseStep 2619811 = 3929717) B3929717
theorem B3493081 : Blo 2295435 3493081 := bstep (se 2 (by rfl) ⟨1309905, by rfl⟩ : syracuseStep 3493081 = 2619811) B2619811
theorem B4657441 : Blo 2295435 4657441 := bstep (se 2 (by rfl) ⟨1746540, by rfl⟩ : syracuseStep 4657441 = 3493081) B3493081
theorem B6209921 : Blo 2295435 6209921 := bstep (se 2 (by rfl) ⟨2328720, by rfl⟩ : syracuseStep 6209921 = 4657441) B4657441
theorem B4139947 : Blo 2295435 4139947 := bstep (se 1 (by rfl) ⟨3104960, by rfl⟩ : syracuseStep 4139947 = 6209921) B6209921
theorem B5519929 : Blo 2295435 5519929 := bstep (se 2 (by rfl) ⟨2069973, by rfl⟩ : syracuseStep 5519929 = 4139947) B4139947
theorem B7359905 : Blo 2295435 7359905 := bstep (se 2 (by rfl) ⟨2759964, by rfl⟩ : syracuseStep 7359905 = 5519929) B5519929
theorem B4906603 : Blo 2295435 4906603 := bstep (se 1 (by rfl) ⟨3679952, by rfl⟩ : syracuseStep 4906603 = 7359905) B7359905
theorem B6542137 : Blo 2295435 6542137 := bstep (se 2 (by rfl) ⟨2453301, by rfl⟩ : syracuseStep 6542137 = 4906603) B4906603
theorem B8722849 : Blo 2295435 8722849 := bstep (se 2 (by rfl) ⟨3271068, by rfl⟩ : syracuseStep 8722849 = 6542137) B6542137
theorem B11630465 : Blo 2295435 11630465 := bstep (se 2 (by rfl) ⟨4361424, by rfl⟩ : syracuseStep 11630465 = 8722849) B8722849
theorem B7753643 : Blo 2295435 7753643 := bstep (se 1 (by rfl) ⟨5815232, by rfl⟩ : syracuseStep 7753643 = 11630465) B11630465
theorem B5169095 : Blo 2295435 5169095 := bstep (se 1 (by rfl) ⟨3876821, by rfl⟩ : syracuseStep 5169095 = 7753643) B7753643
theorem B3446063 : Blo 2295435 3446063 := bstep (se 1 (by rfl) ⟨2584547, by rfl⟩ : syracuseStep 3446063 = 5169095) B5169095
theorem B2297375 : Blo 2295435 2297375 := bstep (se 1 (by rfl) ⟨1723031, by rfl⟩ : syracuseStep 2297375 = 3446063) B3446063
theorem B3446069 : Blo 2295435 3446069 := bbase (se 5 (by rfl) ⟨161534, by rfl⟩ : syracuseStep 3446069 = 323069) (by norm_num)
theorem B2297379 : Blo 2295435 2297379 := bstep (se 1 (by rfl) ⟨1723034, by rfl⟩ : syracuseStep 2297379 = 3446069) B3446069
theorem B5815253 : Blo 2295435 5815253 := bbase (se 7 (by rfl) ⟨68147, by rfl⟩ : syracuseStep 5815253 = 136295) (by norm_num)
theorem B3876835 : Blo 2295435 3876835 := bstep (se 1 (by rfl) ⟨2907626, by rfl⟩ : syracuseStep 3876835 = 5815253) B5815253
theorem B5169113 : Blo 2295435 5169113 := bstep (se 2 (by rfl) ⟨1938417, by rfl⟩ : syracuseStep 5169113 = 3876835) B3876835
theorem B3446075 : Blo 2295435 3446075 := bstep (se 1 (by rfl) ⟨2584556, by rfl⟩ : syracuseStep 3446075 = 5169113) B5169113
theorem B2297383 : Blo 2295435 2297383 := bstep (se 1 (by rfl) ⟨1723037, by rfl⟩ : syracuseStep 2297383 = 3446075) B3446075
theorem B2584561 : Blo 2295435 2584561 := bbase (se 2 (by rfl) ⟨969210, by rfl⟩ : syracuseStep 2584561 = 1938421) (by norm_num)
theorem B3446081 : Blo 2295435 3446081 := bstep (se 2 (by rfl) ⟨1292280, by rfl⟩ : syracuseStep 3446081 = 2584561) B2584561
theorem B2297387 : Blo 2295435 2297387 := bstep (se 1 (by rfl) ⟨1723040, by rfl⟩ : syracuseStep 2297387 = 3446081) B3446081
theorem B4973581 : Blo 2295435 4973581 := bbase (se 3 (by rfl) ⟨932546, by rfl⟩ : syracuseStep 4973581 = 1865093) (by norm_num)
theorem B26525765 : Blo 2295435 26525765 := bstep (se 4 (by rfl) ⟨2486790, by rfl⟩ : syracuseStep 26525765 = 4973581) B4973581
theorem B17683843 : Blo 2295435 17683843 := bstep (se 1 (by rfl) ⟨13262882, by rfl⟩ : syracuseStep 17683843 = 26525765) B26525765
theorem B23578457 : Blo 2295435 23578457 := bstep (se 2 (by rfl) ⟨8841921, by rfl⟩ : syracuseStep 23578457 = 17683843) B17683843
theorem B62875885 : Blo 2295435 62875885 := bstep (se 3 (by rfl) ⟨11789228, by rfl⟩ : syracuseStep 62875885 = 23578457) B23578457
theorem B83834513 : Blo 2295435 83834513 := bstep (se 2 (by rfl) ⟨31437942, by rfl⟩ : syracuseStep 83834513 = 62875885) B62875885
theorem B55889675 : Blo 2295435 55889675 := bstep (se 1 (by rfl) ⟨41917256, by rfl⟩ : syracuseStep 55889675 = 83834513) B83834513
theorem B37259783 : Blo 2295435 37259783 := bstep (se 1 (by rfl) ⟨27944837, by rfl⟩ : syracuseStep 37259783 = 55889675) B55889675
theorem B24839855 : Blo 2295435 24839855 := bstep (se 1 (by rfl) ⟨18629891, by rfl⟩ : syracuseStep 24839855 = 37259783) B37259783
theorem B16559903 : Blo 2295435 16559903 := bstep (se 1 (by rfl) ⟨12419927, by rfl⟩ : syracuseStep 16559903 = 24839855) B24839855
theorem B11039935 : Blo 2295435 11039935 := bstep (se 1 (by rfl) ⟨8279951, by rfl⟩ : syracuseStep 11039935 = 16559903) B16559903
theorem B14719913 : Blo 2295435 14719913 := bstep (se 2 (by rfl) ⟨5519967, by rfl⟩ : syracuseStep 14719913 = 11039935) B11039935
theorem B9813275 : Blo 2295435 9813275 := bstep (se 1 (by rfl) ⟨7359956, by rfl⟩ : syracuseStep 9813275 = 14719913) B14719913
theorem B6542183 : Blo 2295435 6542183 := bstep (se 1 (by rfl) ⟨4906637, by rfl⟩ : syracuseStep 6542183 = 9813275) B9813275
theorem B4361455 : Blo 2295435 4361455 := bstep (se 1 (by rfl) ⟨3271091, by rfl⟩ : syracuseStep 4361455 = 6542183) B6542183
theorem B5815273 : Blo 2295435 5815273 := bstep (se 2 (by rfl) ⟨2180727, by rfl⟩ : syracuseStep 5815273 = 4361455) B4361455
theorem B7753697 : Blo 2295435 7753697 := bstep (se 2 (by rfl) ⟨2907636, by rfl⟩ : syracuseStep 7753697 = 5815273) B5815273
theorem B5169131 : Blo 2295435 5169131 := bstep (se 1 (by rfl) ⟨3876848, by rfl⟩ : syracuseStep 5169131 = 7753697) B7753697
theorem B3446087 : Blo 2295435 3446087 := bstep (se 1 (by rfl) ⟨2584565, by rfl⟩ : syracuseStep 3446087 = 5169131) B5169131
theorem B2297391 : Blo 2295435 2297391 := bstep (se 1 (by rfl) ⟨1723043, by rfl⟩ : syracuseStep 2297391 = 3446087) B3446087
theorem B3446093 : Blo 2295435 3446093 := bbase (se 3 (by rfl) ⟨646142, by rfl⟩ : syracuseStep 3446093 = 1292285) (by norm_num)
theorem B2297395 : Blo 2295435 2297395 := bstep (se 1 (by rfl) ⟨1723046, by rfl⟩ : syracuseStep 2297395 = 3446093) B3446093
theorem B5169149 : Blo 2295435 5169149 := bbase (se 3 (by rfl) ⟨969215, by rfl⟩ : syracuseStep 5169149 = 1938431) (by norm_num)
theorem B3446099 : Blo 2295435 3446099 := bstep (se 1 (by rfl) ⟨2584574, by rfl⟩ : syracuseStep 3446099 = 5169149) B5169149
theorem B2297399 : Blo 2295435 2297399 := bstep (se 1 (by rfl) ⟨1723049, by rfl⟩ : syracuseStep 2297399 = 3446099) B3446099
theorem B3876869 : Blo 2295435 3876869 := bbase (se 4 (by rfl) ⟨363456, by rfl⟩ : syracuseStep 3876869 = 726913) (by norm_num)
theorem B2584579 : Blo 2295435 2584579 := bstep (se 1 (by rfl) ⟨1938434, by rfl⟩ : syracuseStep 2584579 = 3876869) B3876869
theorem B3446105 : Blo 2295435 3446105 := bstep (se 2 (by rfl) ⟨1292289, by rfl⟩ : syracuseStep 3446105 = 2584579) B2584579
theorem B2297403 : Blo 2295435 2297403 := bstep (se 1 (by rfl) ⟨1723052, by rfl⟩ : syracuseStep 2297403 = 3446105) B3446105
theorem B17445941 : Blo 2295435 17445941 := bbase (se 5 (by rfl) ⟨817778, by rfl⟩ : syracuseStep 17445941 = 1635557) (by norm_num)
theorem B11630627 : Blo 2295435 11630627 := bstep (se 1 (by rfl) ⟨8722970, by rfl⟩ : syracuseStep 11630627 = 17445941) B17445941
theorem B7753751 : Blo 2295435 7753751 := bstep (se 1 (by rfl) ⟨5815313, by rfl⟩ : syracuseStep 7753751 = 11630627) B11630627
theorem B5169167 : Blo 2295435 5169167 := bstep (se 1 (by rfl) ⟨3876875, by rfl⟩ : syracuseStep 5169167 = 7753751) B7753751
theorem B3446111 : Blo 2295435 3446111 := bstep (se 1 (by rfl) ⟨2584583, by rfl⟩ : syracuseStep 3446111 = 5169167) B5169167
theorem B2297407 : Blo 2295435 2297407 := bstep (se 1 (by rfl) ⟨1723055, by rfl⟩ : syracuseStep 2297407 = 3446111) B3446111
theorem B3446117 : Blo 2295435 3446117 := bbase (se 4 (by rfl) ⟨323073, by rfl⟩ : syracuseStep 3446117 = 646147) (by norm_num)
theorem B2297411 : Blo 2295435 2297411 := bstep (se 1 (by rfl) ⟨1723058, by rfl⟩ : syracuseStep 2297411 = 3446117) B3446117
theorem B4361501 : Blo 2295435 4361501 := bbase (se 3 (by rfl) ⟨817781, by rfl⟩ : syracuseStep 4361501 = 1635563) (by norm_num)
theorem B2907667 : Blo 2295435 2907667 := bstep (se 1 (by rfl) ⟨2180750, by rfl⟩ : syracuseStep 2907667 = 4361501) B4361501
theorem B3876889 : Blo 2295435 3876889 := bstep (se 2 (by rfl) ⟨1453833, by rfl⟩ : syracuseStep 3876889 = 2907667) B2907667
theorem B5169185 : Blo 2295435 5169185 := bstep (se 2 (by rfl) ⟨1938444, by rfl⟩ : syracuseStep 5169185 = 3876889) B3876889
theorem B3446123 : Blo 2295435 3446123 := bstep (se 1 (by rfl) ⟨2584592, by rfl⟩ : syracuseStep 3446123 = 5169185) B5169185
theorem B2297415 : Blo 2295435 2297415 := bstep (se 1 (by rfl) ⟨1723061, by rfl⟩ : syracuseStep 2297415 = 3446123) B3446123
theorem B2584597 : Blo 2295435 2584597 := bbase (se 6 (by rfl) ⟨60576, by rfl⟩ : syracuseStep 2584597 = 121153) (by norm_num)
theorem B3446129 : Blo 2295435 3446129 := bstep (se 2 (by rfl) ⟨1292298, by rfl⟩ : syracuseStep 3446129 = 2584597) B2584597
theorem B2297419 : Blo 2295435 2297419 := bstep (se 1 (by rfl) ⟨1723064, by rfl⟩ : syracuseStep 2297419 = 3446129) B3446129
theorem B2907677 : Blo 2295435 2907677 := bbase (se 3 (by rfl) ⟨545189, by rfl⟩ : syracuseStep 2907677 = 1090379) (by norm_num)
theorem B7753805 : Blo 2295435 7753805 := bstep (se 3 (by rfl) ⟨1453838, by rfl⟩ : syracuseStep 7753805 = 2907677) B2907677
theorem B5169203 : Blo 2295435 5169203 := bstep (se 1 (by rfl) ⟨3876902, by rfl⟩ : syracuseStep 5169203 = 7753805) B7753805
theorem B3446135 : Blo 2295435 3446135 := bstep (se 1 (by rfl) ⟨2584601, by rfl⟩ : syracuseStep 3446135 = 5169203) B5169203
theorem B2297423 : Blo 2295435 2297423 := bstep (se 1 (by rfl) ⟨1723067, by rfl⟩ : syracuseStep 2297423 = 3446135) B3446135
theorem B3446141 : Blo 2295435 3446141 := bbase (se 3 (by rfl) ⟨646151, by rfl⟩ : syracuseStep 3446141 = 1292303) (by norm_num)
theorem B2297427 : Blo 2295435 2297427 := bstep (se 1 (by rfl) ⟨1723070, by rfl⟩ : syracuseStep 2297427 = 3446141) B3446141
theorem B5169221 : Blo 2295435 5169221 := bbase (se 4 (by rfl) ⟨484614, by rfl⟩ : syracuseStep 5169221 = 969229) (by norm_num)
theorem B3446147 : Blo 2295435 3446147 := bstep (se 1 (by rfl) ⟨2584610, by rfl⟩ : syracuseStep 3446147 = 5169221) B5169221
theorem B2297431 : Blo 2295435 2297431 := bstep (se 1 (by rfl) ⟨1723073, by rfl⟩ : syracuseStep 2297431 = 3446147) B3446147
theorem B6542309 : Blo 2295435 6542309 := bbase (se 4 (by rfl) ⟨613341, by rfl⟩ : syracuseStep 6542309 = 1226683) (by norm_num)
theorem B4361539 : Blo 2295435 4361539 := bstep (se 1 (by rfl) ⟨3271154, by rfl⟩ : syracuseStep 4361539 = 6542309) B6542309
theorem B5815385 : Blo 2295435 5815385 := bstep (se 2 (by rfl) ⟨2180769, by rfl⟩ : syracuseStep 5815385 = 4361539) B4361539
theorem B3876923 : Blo 2295435 3876923 := bstep (se 1 (by rfl) ⟨2907692, by rfl⟩ : syracuseStep 3876923 = 5815385) B5815385
theorem B2584615 : Blo 2295435 2584615 := bstep (se 1 (by rfl) ⟨1938461, by rfl⟩ : syracuseStep 2584615 = 3876923) B3876923
theorem B3446153 : Blo 2295435 3446153 := bstep (se 2 (by rfl) ⟨1292307, by rfl⟩ : syracuseStep 3446153 = 2584615) B2584615
theorem B2297435 : Blo 2295435 2297435 := bstep (se 1 (by rfl) ⟨1723076, by rfl⟩ : syracuseStep 2297435 = 3446153) B3446153
theorem C0 (j : ℕ) (h1 : 573858 ≤ j) (h2 : j ≤ 574358) : Blo 2295435 (4 * j + 3) := by
  interval_cases j
  · exact B2295435
  · exact B2295439
  · exact B2295443
  · exact B2295447
  · exact B2295451
  · exact B2295455
  · exact B2295459
  · exact B2295463
  · exact B2295467
  · exact B2295471
  · exact B2295475
  · exact B2295479
  · exact B2295483
  · exact B2295487
  · exact B2295491
  · exact B2295495
  · exact B2295499
  · exact B2295503
  · exact B2295507
  · exact B2295511
  · exact B2295515
  · exact B2295519
  · exact B2295523
  · exact B2295527
  · exact B2295531
  · exact B2295535
  · exact B2295539
  · exact B2295543
  · exact B2295547
  · exact B2295551
  · exact B2295555
  · exact B2295559
  · exact B2295563
  · exact B2295567
  · exact B2295571
  · exact B2295575
  · exact B2295579
  · exact B2295583
  · exact B2295587
  · exact B2295591
  · exact B2295595
  · exact B2295599
  · exact B2295603
  · exact B2295607
  · exact B2295611
  · exact B2295615
  · exact B2295619
  · exact B2295623
  · exact B2295627
  · exact B2295631
  · exact B2295635
  · exact B2295639
  · exact B2295643
  · exact B2295647
  · exact B2295651
  · exact B2295655
  · exact B2295659
  · exact B2295663
  · exact B2295667
  · exact B2295671
  · exact B2295675
  · exact B2295679
  · exact B2295683
  · exact B2295687
  · exact B2295691
  · exact B2295695
  · exact B2295699
  · exact B2295703
  · exact B2295707
  · exact B2295711
  · exact B2295715
  · exact B2295719
  · exact B2295723
  · exact B2295727
  · exact B2295731
  · exact B2295735
  · exact B2295739
  · exact B2295743
  · exact B2295747
  · exact B2295751
  · exact B2295755
  · exact B2295759
  · exact B2295763
  · exact B2295767
  · exact B2295771
  · exact B2295775
  · exact B2295779
  · exact B2295783
  · exact B2295787
  · exact B2295791
  · exact B2295795
  · exact B2295799
  · exact B2295803
  · exact B2295807
  · exact B2295811
  · exact B2295815
  · exact B2295819
  · exact B2295823
  · exact B2295827
  · exact B2295831
  · exact B2295835
  · exact B2295839
  · exact B2295843
  · exact B2295847
  · exact B2295851
  · exact B2295855
  · exact B2295859
  · exact B2295863
  · exact B2295867
  · exact B2295871
  · exact B2295875
  · exact B2295879
  · exact B2295883
  · exact B2295887
  · exact B2295891
  · exact B2295895
  · exact B2295899
  · exact B2295903
  · exact B2295907
  · exact B2295911
  · exact B2295915
  · exact B2295919
  · exact B2295923
  · exact B2295927
  · exact B2295931
  · exact B2295935
  · exact B2295939
  · exact B2295943
  · exact B2295947
  · exact B2295951
  · exact B2295955
  · exact B2295959
  · exact B2295963
  · exact B2295967
  · exact B2295971
  · exact B2295975
  · exact B2295979
  · exact B2295983
  · exact B2295987
  · exact B2295991
  · exact B2295995
  · exact B2295999
  · exact B2296003
  · exact B2296007
  · exact B2296011
  · exact B2296015
  · exact B2296019
  · exact B2296023
  · exact B2296027
  · exact B2296031
  · exact B2296035
  · exact B2296039
  · exact B2296043
  · exact B2296047
  · exact B2296051
  · exact B2296055
  · exact B2296059
  · exact B2296063
  · exact B2296067
  · exact B2296071
  · exact B2296075
  · exact B2296079
  · exact B2296083
  · exact B2296087
  · exact B2296091
  · exact B2296095
  · exact B2296099
  · exact B2296103
  · exact B2296107
  · exact B2296111
  · exact B2296115
  · exact B2296119
  · exact B2296123
  · exact B2296127
  · exact B2296131
  · exact B2296135
  · exact B2296139
  · exact B2296143
  · exact B2296147
  · exact B2296151
  · exact B2296155
  · exact B2296159
  · exact B2296163
  · exact B2296167
  · exact B2296171
  · exact B2296175
  · exact B2296179
  · exact B2296183
  · exact B2296187
  · exact B2296191
  · exact B2296195
  · exact B2296199
  · exact B2296203
  · exact B2296207
  · exact B2296211
  · exact B2296215
  · exact B2296219
  · exact B2296223
  · exact B2296227
  · exact B2296231
  · exact B2296235
  · exact B2296239
  · exact B2296243
  · exact B2296247
  · exact B2296251
  · exact B2296255
  · exact B2296259
  · exact B2296263
  · exact B2296267
  · exact B2296271
  · exact B2296275
  · exact B2296279
  · exact B2296283
  · exact B2296287
  · exact B2296291
  · exact B2296295
  · exact B2296299
  · exact B2296303
  · exact B2296307
  · exact B2296311
  · exact B2296315
  · exact B2296319
  · exact B2296323
  · exact B2296327
  · exact B2296331
  · exact B2296335
  · exact B2296339
  · exact B2296343
  · exact B2296347
  · exact B2296351
  · exact B2296355
  · exact B2296359
  · exact B2296363
  · exact B2296367
  · exact B2296371
  · exact B2296375
  · exact B2296379
  · exact B2296383
  · exact B2296387
  · exact B2296391
  · exact B2296395
  · exact B2296399
  · exact B2296403
  · exact B2296407
  · exact B2296411
  · exact B2296415
  · exact B2296419
  · exact B2296423
  · exact B2296427
  · exact B2296431
  · exact B2296435
  · exact B2296439
  · exact B2296443
  · exact B2296447
  · exact B2296451
  · exact B2296455
  · exact B2296459
  · exact B2296463
  · exact B2296467
  · exact B2296471
  · exact B2296475
  · exact B2296479
  · exact B2296483
  · exact B2296487
  · exact B2296491
  · exact B2296495
  · exact B2296499
  · exact B2296503
  · exact B2296507
  · exact B2296511
  · exact B2296515
  · exact B2296519
  · exact B2296523
  · exact B2296527
  · exact B2296531
  · exact B2296535
  · exact B2296539
  · exact B2296543
  · exact B2296547
  · exact B2296551
  · exact B2296555
  · exact B2296559
  · exact B2296563
  · exact B2296567
  · exact B2296571
  · exact B2296575
  · exact B2296579
  · exact B2296583
  · exact B2296587
  · exact B2296591
  · exact B2296595
  · exact B2296599
  · exact B2296603
  · exact B2296607
  · exact B2296611
  · exact B2296615
  · exact B2296619
  · exact B2296623
  · exact B2296627
  · exact B2296631
  · exact B2296635
  · exact B2296639
  · exact B2296643
  · exact B2296647
  · exact B2296651
  · exact B2296655
  · exact B2296659
  · exact B2296663
  · exact B2296667
  · exact B2296671
  · exact B2296675
  · exact B2296679
  · exact B2296683
  · exact B2296687
  · exact B2296691
  · exact B2296695
  · exact B2296699
  · exact B2296703
  · exact B2296707
  · exact B2296711
  · exact B2296715
  · exact B2296719
  · exact B2296723
  · exact B2296727
  · exact B2296731
  · exact B2296735
  · exact B2296739
  · exact B2296743
  · exact B2296747
  · exact B2296751
  · exact B2296755
  · exact B2296759
  · exact B2296763
  · exact B2296767
  · exact B2296771
  · exact B2296775
  · exact B2296779
  · exact B2296783
  · exact B2296787
  · exact B2296791
  · exact B2296795
  · exact B2296799
  · exact B2296803
  · exact B2296807
  · exact B2296811
  · exact B2296815
  · exact B2296819
  · exact B2296823
  · exact B2296827
  · exact B2296831
  · exact B2296835
  · exact B2296839
  · exact B2296843
  · exact B2296847
  · exact B2296851
  · exact B2296855
  · exact B2296859
  · exact B2296863
  · exact B2296867
  · exact B2296871
  · exact B2296875
  · exact B2296879
  · exact B2296883
  · exact B2296887
  · exact B2296891
  · exact B2296895
  · exact B2296899
  · exact B2296903
  · exact B2296907
  · exact B2296911
  · exact B2296915
  · exact B2296919
  · exact B2296923
  · exact B2296927
  · exact B2296931
  · exact B2296935
  · exact B2296939
  · exact B2296943
  · exact B2296947
  · exact B2296951
  · exact B2296955
  · exact B2296959
  · exact B2296963
  · exact B2296967
  · exact B2296971
  · exact B2296975
  · exact B2296979
  · exact B2296983
  · exact B2296987
  · exact B2296991
  · exact B2296995
  · exact B2296999
  · exact B2297003
  · exact B2297007
  · exact B2297011
  · exact B2297015
  · exact B2297019
  · exact B2297023
  · exact B2297027
  · exact B2297031
  · exact B2297035
  · exact B2297039
  · exact B2297043
  · exact B2297047
  · exact B2297051
  · exact B2297055
  · exact B2297059
  · exact B2297063
  · exact B2297067
  · exact B2297071
  · exact B2297075
  · exact B2297079
  · exact B2297083
  · exact B2297087
  · exact B2297091
  · exact B2297095
  · exact B2297099
  · exact B2297103
  · exact B2297107
  · exact B2297111
  · exact B2297115
  · exact B2297119
  · exact B2297123
  · exact B2297127
  · exact B2297131
  · exact B2297135
  · exact B2297139
  · exact B2297143
  · exact B2297147
  · exact B2297151
  · exact B2297155
  · exact B2297159
  · exact B2297163
  · exact B2297167
  · exact B2297171
  · exact B2297175
  · exact B2297179
  · exact B2297183
  · exact B2297187
  · exact B2297191
  · exact B2297195
  · exact B2297199
  · exact B2297203
  · exact B2297207
  · exact B2297211
  · exact B2297215
  · exact B2297219
  · exact B2297223
  · exact B2297227
  · exact B2297231
  · exact B2297235
  · exact B2297239
  · exact B2297243
  · exact B2297247
  · exact B2297251
  · exact B2297255
  · exact B2297259
  · exact B2297263
  · exact B2297267
  · exact B2297271
  · exact B2297275
  · exact B2297279
  · exact B2297283
  · exact B2297287
  · exact B2297291
  · exact B2297295
  · exact B2297299
  · exact B2297303
  · exact B2297307
  · exact B2297311
  · exact B2297315
  · exact B2297319
  · exact B2297323
  · exact B2297327
  · exact B2297331
  · exact B2297335
  · exact B2297339
  · exact B2297343
  · exact B2297347
  · exact B2297351
  · exact B2297355
  · exact B2297359
  · exact B2297363
  · exact B2297367
  · exact B2297371
  · exact B2297375
  · exact B2297379
  · exact B2297383
  · exact B2297387
  · exact B2297391
  · exact B2297395
  · exact B2297399
  · exact B2297403
  · exact B2297407
  · exact B2297411
  · exact B2297415
  · exact B2297419
  · exact B2297423
  · exact B2297427
  · exact B2297431
  · exact B2297435
theorem solution (m : ℕ) (hlo : 2295435 ≤ m) (hhi : m ≤ 2297435) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 573858 ≤ j := by omega
    have hj2 : j ≤ 574358 := by omega
    have hb : Blo 2295435 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
