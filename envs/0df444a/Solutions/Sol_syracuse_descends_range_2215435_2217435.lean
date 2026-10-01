-- Prove2me | solution 1 for syracuse_descends_range_2215435_2217435
-- status  : ACCEPTED   (prove)
-- author  : @chstdu
-- created : 2026-09-23T17:18:34.160543+00:00
-- url     : https://prove2.me/submissions/462e1f43-f2ed-43bf-942a-c2a5dcebeb65

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

theorem B2492365 : Blo 2215435 2492365 := bbase (se 3 (by rfl) ⟨467318, by rfl⟩ : syracuseStep 2492365 = 934637) (by norm_num)
theorem B3323153 : Blo 2215435 3323153 := bstep (se 2 (by rfl) ⟨1246182, by rfl⟩ : syracuseStep 3323153 = 2492365) B2492365
theorem B2215435 : Blo 2215435 2215435 := bstep (se 1 (by rfl) ⟨1661576, by rfl⟩ : syracuseStep 2215435 = 3323153) B3323153
theorem B7477109 : Blo 2215435 7477109 := bbase (se 5 (by rfl) ⟨350489, by rfl⟩ : syracuseStep 7477109 = 700979) (by norm_num)
theorem B4984739 : Blo 2215435 4984739 := bstep (se 1 (by rfl) ⟨3738554, by rfl⟩ : syracuseStep 4984739 = 7477109) B7477109
theorem B3323159 : Blo 2215435 3323159 := bstep (se 1 (by rfl) ⟨2492369, by rfl⟩ : syracuseStep 3323159 = 4984739) B4984739
theorem B2215439 : Blo 2215435 2215439 := bstep (se 1 (by rfl) ⟨1661579, by rfl⟩ : syracuseStep 2215439 = 3323159) B3323159
theorem B3323165 : Blo 2215435 3323165 := bbase (se 3 (by rfl) ⟨623093, by rfl⟩ : syracuseStep 3323165 = 1246187) (by norm_num)
theorem B2215443 : Blo 2215435 2215443 := bstep (se 1 (by rfl) ⟨1661582, by rfl⟩ : syracuseStep 2215443 = 3323165) B3323165
theorem B4984757 : Blo 2215435 4984757 := bbase (se 5 (by rfl) ⟨233660, by rfl⟩ : syracuseStep 4984757 = 467321) (by norm_num)
theorem B3323171 : Blo 2215435 3323171 := bstep (se 1 (by rfl) ⟨2492378, by rfl⟩ : syracuseStep 3323171 = 4984757) B4984757
theorem B2215447 : Blo 2215435 2215447 := bstep (se 1 (by rfl) ⟨1661585, by rfl⟩ : syracuseStep 2215447 = 3323171) B3323171
theorem B2661545 : Blo 2215435 2661545 := bbase (se 2 (by rfl) ⟨998079, by rfl⟩ : syracuseStep 2661545 = 1996159) (by norm_num)
theorem B7097453 : Blo 2215435 7097453 := bstep (se 3 (by rfl) ⟨1330772, by rfl⟩ : syracuseStep 7097453 = 2661545) B2661545
theorem B4731635 : Blo 2215435 4731635 := bstep (se 1 (by rfl) ⟨3548726, by rfl⟩ : syracuseStep 4731635 = 7097453) B7097453
theorem B12617693 : Blo 2215435 12617693 := bstep (se 3 (by rfl) ⟨2365817, by rfl⟩ : syracuseStep 12617693 = 4731635) B4731635
theorem B8411795 : Blo 2215435 8411795 := bstep (se 1 (by rfl) ⟨6308846, by rfl⟩ : syracuseStep 8411795 = 12617693) B12617693
theorem B5607863 : Blo 2215435 5607863 := bstep (se 1 (by rfl) ⟨4205897, by rfl⟩ : syracuseStep 5607863 = 8411795) B8411795
theorem B3738575 : Blo 2215435 3738575 := bstep (se 1 (by rfl) ⟨2803931, by rfl⟩ : syracuseStep 3738575 = 5607863) B5607863
theorem B2492383 : Blo 2215435 2492383 := bstep (se 1 (by rfl) ⟨1869287, by rfl⟩ : syracuseStep 2492383 = 3738575) B3738575
theorem B3323177 : Blo 2215435 3323177 := bstep (se 2 (by rfl) ⟨1246191, by rfl⟩ : syracuseStep 3323177 = 2492383) B2492383
theorem B2215451 : Blo 2215435 2215451 := bstep (se 1 (by rfl) ⟨1661588, by rfl⟩ : syracuseStep 2215451 = 3323177) B3323177
theorem B10105573 : Blo 2215435 10105573 := bbase (se 4 (by rfl) ⟨947397, by rfl⟩ : syracuseStep 10105573 = 1894795) (by norm_num)
theorem B13474097 : Blo 2215435 13474097 := bstep (se 2 (by rfl) ⟨5052786, by rfl⟩ : syracuseStep 13474097 = 10105573) B10105573
theorem B8982731 : Blo 2215435 8982731 := bstep (se 1 (by rfl) ⟨6737048, by rfl⟩ : syracuseStep 8982731 = 13474097) B13474097
theorem B5988487 : Blo 2215435 5988487 := bstep (se 1 (by rfl) ⟨4491365, by rfl⟩ : syracuseStep 5988487 = 8982731) B8982731
theorem B7984649 : Blo 2215435 7984649 := bstep (se 2 (by rfl) ⟨2994243, by rfl⟩ : syracuseStep 7984649 = 5988487) B5988487
theorem B5323099 : Blo 2215435 5323099 := bstep (se 1 (by rfl) ⟨3992324, by rfl⟩ : syracuseStep 5323099 = 7984649) B7984649
theorem B7097465 : Blo 2215435 7097465 := bstep (se 2 (by rfl) ⟨2661549, by rfl⟩ : syracuseStep 7097465 = 5323099) B5323099
theorem B4731643 : Blo 2215435 4731643 := bstep (se 1 (by rfl) ⟨3548732, by rfl⟩ : syracuseStep 4731643 = 7097465) B7097465
theorem B6308857 : Blo 2215435 6308857 := bstep (se 2 (by rfl) ⟨2365821, by rfl⟩ : syracuseStep 6308857 = 4731643) B4731643
theorem B8411809 : Blo 2215435 8411809 := bstep (se 2 (by rfl) ⟨3154428, by rfl⟩ : syracuseStep 8411809 = 6308857) B6308857
theorem B11215745 : Blo 2215435 11215745 := bstep (se 2 (by rfl) ⟨4205904, by rfl⟩ : syracuseStep 11215745 = 8411809) B8411809
theorem B7477163 : Blo 2215435 7477163 := bstep (se 1 (by rfl) ⟨5607872, by rfl⟩ : syracuseStep 7477163 = 11215745) B11215745
theorem B4984775 : Blo 2215435 4984775 := bstep (se 1 (by rfl) ⟨3738581, by rfl⟩ : syracuseStep 4984775 = 7477163) B7477163
theorem B3323183 : Blo 2215435 3323183 := bstep (se 1 (by rfl) ⟨2492387, by rfl⟩ : syracuseStep 3323183 = 4984775) B4984775
theorem B2215455 : Blo 2215435 2215455 := bstep (se 1 (by rfl) ⟨1661591, by rfl⟩ : syracuseStep 2215455 = 3323183) B3323183
theorem B3323189 : Blo 2215435 3323189 := bbase (se 5 (by rfl) ⟨155774, by rfl⟩ : syracuseStep 3323189 = 311549) (by norm_num)
theorem B2215459 : Blo 2215435 2215459 := bstep (se 1 (by rfl) ⟨1661594, by rfl⟩ : syracuseStep 2215459 = 3323189) B3323189
theorem B5607893 : Blo 2215435 5607893 := bbase (se 7 (by rfl) ⟨65717, by rfl⟩ : syracuseStep 5607893 = 131435) (by norm_num)
theorem B3738595 : Blo 2215435 3738595 := bstep (se 1 (by rfl) ⟨2803946, by rfl⟩ : syracuseStep 3738595 = 5607893) B5607893
theorem B4984793 : Blo 2215435 4984793 := bstep (se 2 (by rfl) ⟨1869297, by rfl⟩ : syracuseStep 4984793 = 3738595) B3738595
theorem B3323195 : Blo 2215435 3323195 := bstep (se 1 (by rfl) ⟨2492396, by rfl⟩ : syracuseStep 3323195 = 4984793) B4984793
theorem B2215463 : Blo 2215435 2215463 := bstep (se 1 (by rfl) ⟨1661597, by rfl⟩ : syracuseStep 2215463 = 3323195) B3323195
theorem B2492401 : Blo 2215435 2492401 := bbase (se 2 (by rfl) ⟨934650, by rfl⟩ : syracuseStep 2492401 = 1869301) (by norm_num)
theorem B3323201 : Blo 2215435 3323201 := bstep (se 2 (by rfl) ⟨1246200, by rfl⟩ : syracuseStep 3323201 = 2492401) B2492401
theorem B2215467 : Blo 2215435 2215467 := bstep (se 1 (by rfl) ⟨1661600, by rfl⟩ : syracuseStep 2215467 = 3323201) B3323201
theorem B3368549 : Blo 2215435 3368549 := bbase (se 4 (by rfl) ⟨315801, by rfl⟩ : syracuseStep 3368549 = 631603) (by norm_num)
theorem B2245699 : Blo 2215435 2245699 := bstep (se 1 (by rfl) ⟨1684274, by rfl⟩ : syracuseStep 2245699 = 3368549) B3368549
theorem B2994265 : Blo 2215435 2994265 := bstep (se 2 (by rfl) ⟨1122849, by rfl⟩ : syracuseStep 2994265 = 2245699) B2245699
theorem B15969413 : Blo 2215435 15969413 := bstep (se 4 (by rfl) ⟨1497132, by rfl⟩ : syracuseStep 15969413 = 2994265) B2994265
theorem B10646275 : Blo 2215435 10646275 := bstep (se 1 (by rfl) ⟨7984706, by rfl⟩ : syracuseStep 10646275 = 15969413) B15969413
theorem B14195033 : Blo 2215435 14195033 := bstep (se 2 (by rfl) ⟨5323137, by rfl⟩ : syracuseStep 14195033 = 10646275) B10646275
theorem B9463355 : Blo 2215435 9463355 := bstep (se 1 (by rfl) ⟨7097516, by rfl⟩ : syracuseStep 9463355 = 14195033) B14195033
theorem B6308903 : Blo 2215435 6308903 := bstep (se 1 (by rfl) ⟨4731677, by rfl⟩ : syracuseStep 6308903 = 9463355) B9463355
theorem B4205935 : Blo 2215435 4205935 := bstep (se 1 (by rfl) ⟨3154451, by rfl⟩ : syracuseStep 4205935 = 6308903) B6308903
theorem B5607913 : Blo 2215435 5607913 := bstep (se 2 (by rfl) ⟨2102967, by rfl⟩ : syracuseStep 5607913 = 4205935) B4205935
theorem B7477217 : Blo 2215435 7477217 := bstep (se 2 (by rfl) ⟨2803956, by rfl⟩ : syracuseStep 7477217 = 5607913) B5607913
theorem B4984811 : Blo 2215435 4984811 := bstep (se 1 (by rfl) ⟨3738608, by rfl⟩ : syracuseStep 4984811 = 7477217) B7477217
theorem B3323207 : Blo 2215435 3323207 := bstep (se 1 (by rfl) ⟨2492405, by rfl⟩ : syracuseStep 3323207 = 4984811) B4984811
theorem B2215471 : Blo 2215435 2215471 := bstep (se 1 (by rfl) ⟨1661603, by rfl⟩ : syracuseStep 2215471 = 3323207) B3323207
theorem B3323213 : Blo 2215435 3323213 := bbase (se 3 (by rfl) ⟨623102, by rfl⟩ : syracuseStep 3323213 = 1246205) (by norm_num)
theorem B2215475 : Blo 2215435 2215475 := bstep (se 1 (by rfl) ⟨1661606, by rfl⟩ : syracuseStep 2215475 = 3323213) B3323213
theorem B4984829 : Blo 2215435 4984829 := bbase (se 3 (by rfl) ⟨934655, by rfl⟩ : syracuseStep 4984829 = 1869311) (by norm_num)
theorem B3323219 : Blo 2215435 3323219 := bstep (se 1 (by rfl) ⟨2492414, by rfl⟩ : syracuseStep 3323219 = 4984829) B4984829
theorem B2215479 : Blo 2215435 2215479 := bstep (se 1 (by rfl) ⟨1661609, by rfl⟩ : syracuseStep 2215479 = 3323219) B3323219
theorem B3738629 : Blo 2215435 3738629 := bbase (se 4 (by rfl) ⟨350496, by rfl⟩ : syracuseStep 3738629 = 700993) (by norm_num)
theorem B2492419 : Blo 2215435 2492419 := bstep (se 1 (by rfl) ⟨1869314, by rfl⟩ : syracuseStep 2492419 = 3738629) B3738629
theorem B3323225 : Blo 2215435 3323225 := bstep (se 2 (by rfl) ⟨1246209, by rfl⟩ : syracuseStep 3323225 = 2492419) B2492419
theorem B2215483 : Blo 2215435 2215483 := bstep (se 1 (by rfl) ⟨1661612, by rfl⟩ : syracuseStep 2215483 = 3323225) B3323225
theorem B16823861 : Blo 2215435 16823861 := bbase (se 5 (by rfl) ⟨788618, by rfl⟩ : syracuseStep 16823861 = 1577237) (by norm_num)
theorem B11215907 : Blo 2215435 11215907 := bstep (se 1 (by rfl) ⟨8411930, by rfl⟩ : syracuseStep 11215907 = 16823861) B16823861
theorem B7477271 : Blo 2215435 7477271 := bstep (se 1 (by rfl) ⟨5607953, by rfl⟩ : syracuseStep 7477271 = 11215907) B11215907
theorem B4984847 : Blo 2215435 4984847 := bstep (se 1 (by rfl) ⟨3738635, by rfl⟩ : syracuseStep 4984847 = 7477271) B7477271
theorem B3323231 : Blo 2215435 3323231 := bstep (se 1 (by rfl) ⟨2492423, by rfl⟩ : syracuseStep 3323231 = 4984847) B4984847
theorem B2215487 : Blo 2215435 2215487 := bstep (se 1 (by rfl) ⟨1661615, by rfl⟩ : syracuseStep 2215487 = 3323231) B3323231
theorem B3323237 : Blo 2215435 3323237 := bbase (se 4 (by rfl) ⟨311553, by rfl⟩ : syracuseStep 3323237 = 623107) (by norm_num)
theorem B2215491 : Blo 2215435 2215491 := bstep (se 1 (by rfl) ⟨1661618, by rfl⟩ : syracuseStep 2215491 = 3323237) B3323237
theorem B4205981 : Blo 2215435 4205981 := bbase (se 3 (by rfl) ⟨788621, by rfl⟩ : syracuseStep 4205981 = 1577243) (by norm_num)
theorem B2803987 : Blo 2215435 2803987 := bstep (se 1 (by rfl) ⟨2102990, by rfl⟩ : syracuseStep 2803987 = 4205981) B4205981
theorem B3738649 : Blo 2215435 3738649 := bstep (se 2 (by rfl) ⟨1401993, by rfl⟩ : syracuseStep 3738649 = 2803987) B2803987
theorem B4984865 : Blo 2215435 4984865 := bstep (se 2 (by rfl) ⟨1869324, by rfl⟩ : syracuseStep 4984865 = 3738649) B3738649
theorem B3323243 : Blo 2215435 3323243 := bstep (se 1 (by rfl) ⟨2492432, by rfl⟩ : syracuseStep 3323243 = 4984865) B4984865
theorem B2215495 : Blo 2215435 2215495 := bstep (se 1 (by rfl) ⟨1661621, by rfl⟩ : syracuseStep 2215495 = 3323243) B3323243
theorem B2492437 : Blo 2215435 2492437 := bbase (se 6 (by rfl) ⟨58416, by rfl⟩ : syracuseStep 2492437 = 116833) (by norm_num)
theorem B3323249 : Blo 2215435 3323249 := bstep (se 2 (by rfl) ⟨1246218, by rfl⟩ : syracuseStep 3323249 = 2492437) B2492437
theorem B2215499 : Blo 2215435 2215499 := bstep (se 1 (by rfl) ⟨1661624, by rfl⟩ : syracuseStep 2215499 = 3323249) B3323249
theorem B2803997 : Blo 2215435 2803997 := bbase (se 3 (by rfl) ⟨525749, by rfl⟩ : syracuseStep 2803997 = 1051499) (by norm_num)
theorem B7477325 : Blo 2215435 7477325 := bstep (se 3 (by rfl) ⟨1401998, by rfl⟩ : syracuseStep 7477325 = 2803997) B2803997
theorem B4984883 : Blo 2215435 4984883 := bstep (se 1 (by rfl) ⟨3738662, by rfl⟩ : syracuseStep 4984883 = 7477325) B7477325
theorem B3323255 : Blo 2215435 3323255 := bstep (se 1 (by rfl) ⟨2492441, by rfl⟩ : syracuseStep 3323255 = 4984883) B4984883
theorem B2215503 : Blo 2215435 2215503 := bstep (se 1 (by rfl) ⟨1661627, by rfl⟩ : syracuseStep 2215503 = 3323255) B3323255
theorem B3323261 : Blo 2215435 3323261 := bbase (se 3 (by rfl) ⟨623111, by rfl⟩ : syracuseStep 3323261 = 1246223) (by norm_num)
theorem B2215507 : Blo 2215435 2215507 := bstep (se 1 (by rfl) ⟨1661630, by rfl⟩ : syracuseStep 2215507 = 3323261) B3323261
theorem B4984901 : Blo 2215435 4984901 := bbase (se 4 (by rfl) ⟨467334, by rfl⟩ : syracuseStep 4984901 = 934669) (by norm_num)
theorem B3323267 : Blo 2215435 3323267 := bstep (se 1 (by rfl) ⟨2492450, by rfl⟩ : syracuseStep 3323267 = 4984901) B4984901
theorem B2215511 : Blo 2215435 2215511 := bstep (se 1 (by rfl) ⟨1661633, by rfl⟩ : syracuseStep 2215511 = 3323267) B3323267
theorem B6309029 : Blo 2215435 6309029 := bbase (se 4 (by rfl) ⟨591471, by rfl⟩ : syracuseStep 6309029 = 1182943) (by norm_num)
theorem B4206019 : Blo 2215435 4206019 := bstep (se 1 (by rfl) ⟨3154514, by rfl⟩ : syracuseStep 4206019 = 6309029) B6309029
theorem B5608025 : Blo 2215435 5608025 := bstep (se 2 (by rfl) ⟨2103009, by rfl⟩ : syracuseStep 5608025 = 4206019) B4206019
theorem B3738683 : Blo 2215435 3738683 := bstep (se 1 (by rfl) ⟨2804012, by rfl⟩ : syracuseStep 3738683 = 5608025) B5608025
theorem B2492455 : Blo 2215435 2492455 := bstep (se 1 (by rfl) ⟨1869341, by rfl⟩ : syracuseStep 2492455 = 3738683) B3738683
theorem B3323273 : Blo 2215435 3323273 := bstep (se 2 (by rfl) ⟨1246227, by rfl⟩ : syracuseStep 3323273 = 2492455) B2492455
theorem B2215515 : Blo 2215435 2215515 := bstep (se 1 (by rfl) ⟨1661636, by rfl⟩ : syracuseStep 2215515 = 3323273) B3323273
theorem B11216069 : Blo 2215435 11216069 := bbase (se 4 (by rfl) ⟨1051506, by rfl⟩ : syracuseStep 11216069 = 2103013) (by norm_num)
theorem B7477379 : Blo 2215435 7477379 := bstep (se 1 (by rfl) ⟨5608034, by rfl⟩ : syracuseStep 7477379 = 11216069) B11216069
theorem B4984919 : Blo 2215435 4984919 := bstep (se 1 (by rfl) ⟨3738689, by rfl⟩ : syracuseStep 4984919 = 7477379) B7477379
theorem B3323279 : Blo 2215435 3323279 := bstep (se 1 (by rfl) ⟨2492459, by rfl⟩ : syracuseStep 3323279 = 4984919) B4984919
theorem B2215519 : Blo 2215435 2215519 := bstep (se 1 (by rfl) ⟨1661639, by rfl⟩ : syracuseStep 2215519 = 3323279) B3323279
theorem B3323285 : Blo 2215435 3323285 := bbase (se 6 (by rfl) ⟨77889, by rfl⟩ : syracuseStep 3323285 = 155779) (by norm_num)
theorem B2215523 : Blo 2215435 2215523 := bstep (se 1 (by rfl) ⟨1661642, by rfl⟩ : syracuseStep 2215523 = 3323285) B3323285
theorem B4731797 : Blo 2215435 4731797 := bbase (se 6 (by rfl) ⟨110901, by rfl⟩ : syracuseStep 4731797 = 221803) (by norm_num)
theorem B12618125 : Blo 2215435 12618125 := bstep (se 3 (by rfl) ⟨2365898, by rfl⟩ : syracuseStep 12618125 = 4731797) B4731797
theorem B8412083 : Blo 2215435 8412083 := bstep (se 1 (by rfl) ⟨6309062, by rfl⟩ : syracuseStep 8412083 = 12618125) B12618125
theorem B5608055 : Blo 2215435 5608055 := bstep (se 1 (by rfl) ⟨4206041, by rfl⟩ : syracuseStep 5608055 = 8412083) B8412083
theorem B3738703 : Blo 2215435 3738703 := bstep (se 1 (by rfl) ⟨2804027, by rfl⟩ : syracuseStep 3738703 = 5608055) B5608055
theorem B4984937 : Blo 2215435 4984937 := bstep (se 2 (by rfl) ⟨1869351, by rfl⟩ : syracuseStep 4984937 = 3738703) B3738703
theorem B3323291 : Blo 2215435 3323291 := bstep (se 1 (by rfl) ⟨2492468, by rfl⟩ : syracuseStep 3323291 = 4984937) B4984937
theorem B2215527 : Blo 2215435 2215527 := bstep (se 1 (by rfl) ⟨1661645, by rfl⟩ : syracuseStep 2215527 = 3323291) B3323291
theorem B2492473 : Blo 2215435 2492473 := bbase (se 2 (by rfl) ⟨934677, by rfl⟩ : syracuseStep 2492473 = 1869355) (by norm_num)
theorem B3323297 : Blo 2215435 3323297 := bstep (se 2 (by rfl) ⟨1246236, by rfl⟩ : syracuseStep 3323297 = 2492473) B2492473
theorem B2215531 : Blo 2215435 2215531 := bstep (se 1 (by rfl) ⟨1661648, by rfl⟩ : syracuseStep 2215531 = 3323297) B3323297
theorem B3548861 : Blo 2215435 3548861 := bbase (se 3 (by rfl) ⟨665411, by rfl⟩ : syracuseStep 3548861 = 1330823) (by norm_num)
theorem B2365907 : Blo 2215435 2365907 := bstep (se 1 (by rfl) ⟨1774430, by rfl⟩ : syracuseStep 2365907 = 3548861) B3548861
theorem B6309085 : Blo 2215435 6309085 := bstep (se 3 (by rfl) ⟨1182953, by rfl⟩ : syracuseStep 6309085 = 2365907) B2365907
theorem B8412113 : Blo 2215435 8412113 := bstep (se 2 (by rfl) ⟨3154542, by rfl⟩ : syracuseStep 8412113 = 6309085) B6309085
theorem B5608075 : Blo 2215435 5608075 := bstep (se 1 (by rfl) ⟨4206056, by rfl⟩ : syracuseStep 5608075 = 8412113) B8412113
theorem B7477433 : Blo 2215435 7477433 := bstep (se 2 (by rfl) ⟨2804037, by rfl⟩ : syracuseStep 7477433 = 5608075) B5608075
theorem B4984955 : Blo 2215435 4984955 := bstep (se 1 (by rfl) ⟨3738716, by rfl⟩ : syracuseStep 4984955 = 7477433) B7477433
theorem B3323303 : Blo 2215435 3323303 := bstep (se 1 (by rfl) ⟨2492477, by rfl⟩ : syracuseStep 3323303 = 4984955) B4984955
theorem B2215535 : Blo 2215435 2215535 := bstep (se 1 (by rfl) ⟨1661651, by rfl⟩ : syracuseStep 2215535 = 3323303) B3323303
theorem B3323309 : Blo 2215435 3323309 := bbase (se 3 (by rfl) ⟨623120, by rfl⟩ : syracuseStep 3323309 = 1246241) (by norm_num)
theorem B2215539 : Blo 2215435 2215539 := bstep (se 1 (by rfl) ⟨1661654, by rfl⟩ : syracuseStep 2215539 = 3323309) B3323309
theorem B4984973 : Blo 2215435 4984973 := bbase (se 3 (by rfl) ⟨934682, by rfl⟩ : syracuseStep 4984973 = 1869365) (by norm_num)
theorem B3323315 : Blo 2215435 3323315 := bstep (se 1 (by rfl) ⟨2492486, by rfl⟩ : syracuseStep 3323315 = 4984973) B4984973
theorem B2215543 : Blo 2215435 2215543 := bstep (se 1 (by rfl) ⟨1661657, by rfl⟩ : syracuseStep 2215543 = 3323315) B3323315
theorem B2804053 : Blo 2215435 2804053 := bbase (se 10 (by rfl) ⟨4107, by rfl⟩ : syracuseStep 2804053 = 8215) (by norm_num)
theorem B3738737 : Blo 2215435 3738737 := bstep (se 2 (by rfl) ⟨1402026, by rfl⟩ : syracuseStep 3738737 = 2804053) B2804053
theorem B2492491 : Blo 2215435 2492491 := bstep (se 1 (by rfl) ⟨1869368, by rfl⟩ : syracuseStep 2492491 = 3738737) B3738737
theorem B3323321 : Blo 2215435 3323321 := bstep (se 2 (by rfl) ⟨1246245, by rfl⟩ : syracuseStep 3323321 = 2492491) B2492491
theorem B2215547 : Blo 2215435 2215547 := bstep (se 1 (by rfl) ⟨1661660, by rfl⟩ : syracuseStep 2215547 = 3323321) B3323321
theorem B5395957 : Blo 2215435 5395957 := bbase (se 5 (by rfl) ⟨252935, by rfl⟩ : syracuseStep 5395957 = 505871) (by norm_num)
theorem B28778437 : Blo 2215435 28778437 := bstep (se 4 (by rfl) ⟨2697978, by rfl⟩ : syracuseStep 28778437 = 5395957) B5395957
theorem B38371249 : Blo 2215435 38371249 := bstep (se 2 (by rfl) ⟨14389218, by rfl⟩ : syracuseStep 38371249 = 28778437) B28778437
theorem B51161665 : Blo 2215435 51161665 := bstep (se 2 (by rfl) ⟨19185624, by rfl⟩ : syracuseStep 51161665 = 38371249) B38371249
theorem B68215553 : Blo 2215435 68215553 := bstep (se 2 (by rfl) ⟨25580832, by rfl⟩ : syracuseStep 68215553 = 51161665) B51161665
theorem B45477035 : Blo 2215435 45477035 := bstep (se 1 (by rfl) ⟨34107776, by rfl⟩ : syracuseStep 45477035 = 68215553) B68215553
theorem B30318023 : Blo 2215435 30318023 := bstep (se 1 (by rfl) ⟨22738517, by rfl⟩ : syracuseStep 30318023 = 45477035) B45477035
theorem B20212015 : Blo 2215435 20212015 := bstep (se 1 (by rfl) ⟨15159011, by rfl⟩ : syracuseStep 20212015 = 30318023) B30318023
theorem B26949353 : Blo 2215435 26949353 := bstep (se 2 (by rfl) ⟨10106007, by rfl⟩ : syracuseStep 26949353 = 20212015) B20212015
theorem B71864941 : Blo 2215435 71864941 := bstep (se 3 (by rfl) ⟨13474676, by rfl⟩ : syracuseStep 71864941 = 26949353) B26949353
theorem B95819921 : Blo 2215435 95819921 := bstep (se 2 (by rfl) ⟨35932470, by rfl⟩ : syracuseStep 95819921 = 71864941) B71864941
theorem B63879947 : Blo 2215435 63879947 := bstep (se 1 (by rfl) ⟨47909960, by rfl⟩ : syracuseStep 63879947 = 95819921) B95819921
theorem B42586631 : Blo 2215435 42586631 := bstep (se 1 (by rfl) ⟨31939973, by rfl⟩ : syracuseStep 42586631 = 63879947) B63879947
theorem B28391087 : Blo 2215435 28391087 := bstep (se 1 (by rfl) ⟨21293315, by rfl⟩ : syracuseStep 28391087 = 42586631) B42586631
theorem B18927391 : Blo 2215435 18927391 := bstep (se 1 (by rfl) ⟨14195543, by rfl⟩ : syracuseStep 18927391 = 28391087) B28391087
theorem B25236521 : Blo 2215435 25236521 := bstep (se 2 (by rfl) ⟨9463695, by rfl⟩ : syracuseStep 25236521 = 18927391) B18927391
theorem B16824347 : Blo 2215435 16824347 := bstep (se 1 (by rfl) ⟨12618260, by rfl⟩ : syracuseStep 16824347 = 25236521) B25236521
theorem B11216231 : Blo 2215435 11216231 := bstep (se 1 (by rfl) ⟨8412173, by rfl⟩ : syracuseStep 11216231 = 16824347) B16824347
theorem B7477487 : Blo 2215435 7477487 := bstep (se 1 (by rfl) ⟨5608115, by rfl⟩ : syracuseStep 7477487 = 11216231) B11216231
theorem B4984991 : Blo 2215435 4984991 := bstep (se 1 (by rfl) ⟨3738743, by rfl⟩ : syracuseStep 4984991 = 7477487) B7477487
theorem B3323327 : Blo 2215435 3323327 := bstep (se 1 (by rfl) ⟨2492495, by rfl⟩ : syracuseStep 3323327 = 4984991) B4984991
theorem B2215551 : Blo 2215435 2215551 := bstep (se 1 (by rfl) ⟨1661663, by rfl⟩ : syracuseStep 2215551 = 3323327) B3323327
theorem B3323333 : Blo 2215435 3323333 := bbase (se 4 (by rfl) ⟨311562, by rfl⟩ : syracuseStep 3323333 = 623125) (by norm_num)
theorem B2215555 : Blo 2215435 2215555 := bstep (se 1 (by rfl) ⟨1661666, by rfl⟩ : syracuseStep 2215555 = 3323333) B3323333
theorem B3738757 : Blo 2215435 3738757 := bbase (se 4 (by rfl) ⟨350508, by rfl⟩ : syracuseStep 3738757 = 701017) (by norm_num)
theorem B4985009 : Blo 2215435 4985009 := bstep (se 2 (by rfl) ⟨1869378, by rfl⟩ : syracuseStep 4985009 = 3738757) B3738757
theorem B3323339 : Blo 2215435 3323339 := bstep (se 1 (by rfl) ⟨2492504, by rfl⟩ : syracuseStep 3323339 = 4985009) B4985009
theorem B2215559 : Blo 2215435 2215559 := bstep (se 1 (by rfl) ⟨1661669, by rfl⟩ : syracuseStep 2215559 = 3323339) B3323339
theorem B2492509 : Blo 2215435 2492509 := bbase (se 3 (by rfl) ⟨467345, by rfl⟩ : syracuseStep 2492509 = 934691) (by norm_num)
theorem B3323345 : Blo 2215435 3323345 := bstep (se 2 (by rfl) ⟨1246254, by rfl⟩ : syracuseStep 3323345 = 2492509) B2492509
theorem B2215563 : Blo 2215435 2215563 := bstep (se 1 (by rfl) ⟨1661672, by rfl⟩ : syracuseStep 2215563 = 3323345) B3323345
theorem B7477541 : Blo 2215435 7477541 := bbase (se 4 (by rfl) ⟨701019, by rfl⟩ : syracuseStep 7477541 = 1402039) (by norm_num)
theorem B4985027 : Blo 2215435 4985027 := bstep (se 1 (by rfl) ⟨3738770, by rfl⟩ : syracuseStep 4985027 = 7477541) B7477541
theorem B3323351 : Blo 2215435 3323351 := bstep (se 1 (by rfl) ⟨2492513, by rfl⟩ : syracuseStep 3323351 = 4985027) B4985027
theorem B2215567 : Blo 2215435 2215567 := bstep (se 1 (by rfl) ⟨1661675, by rfl⟩ : syracuseStep 2215567 = 3323351) B3323351
theorem B3323357 : Blo 2215435 3323357 := bbase (se 3 (by rfl) ⟨623129, by rfl⟩ : syracuseStep 3323357 = 1246259) (by norm_num)
theorem B2215571 : Blo 2215435 2215571 := bstep (se 1 (by rfl) ⟨1661678, by rfl⟩ : syracuseStep 2215571 = 3323357) B3323357
theorem B4985045 : Blo 2215435 4985045 := bbase (se 7 (by rfl) ⟨58418, by rfl⟩ : syracuseStep 4985045 = 116837) (by norm_num)
theorem B3323363 : Blo 2215435 3323363 := bstep (se 1 (by rfl) ⟨2492522, by rfl⟩ : syracuseStep 3323363 = 4985045) B4985045
theorem B2215575 : Blo 2215435 2215575 := bstep (se 1 (by rfl) ⟨1661681, by rfl⟩ : syracuseStep 2215575 = 3323363) B3323363
theorem B5469653 : Blo 2215435 5469653 := bbase (se 7 (by rfl) ⟨64097, by rfl⟩ : syracuseStep 5469653 = 128195) (by norm_num)
theorem B14585741 : Blo 2215435 14585741 := bstep (se 3 (by rfl) ⟨2734826, by rfl⟩ : syracuseStep 14585741 = 5469653) B5469653
theorem B9723827 : Blo 2215435 9723827 := bstep (se 1 (by rfl) ⟨7292870, by rfl⟩ : syracuseStep 9723827 = 14585741) B14585741
theorem B6482551 : Blo 2215435 6482551 := bstep (se 1 (by rfl) ⟨4861913, by rfl⟩ : syracuseStep 6482551 = 9723827) B9723827
theorem B8643401 : Blo 2215435 8643401 := bstep (se 2 (by rfl) ⟨3241275, by rfl⟩ : syracuseStep 8643401 = 6482551) B6482551
theorem B5762267 : Blo 2215435 5762267 := bstep (se 1 (by rfl) ⟨4321700, by rfl⟩ : syracuseStep 5762267 = 8643401) B8643401
theorem B3841511 : Blo 2215435 3841511 := bstep (se 1 (by rfl) ⟨2881133, by rfl⟩ : syracuseStep 3841511 = 5762267) B5762267
theorem B10244029 : Blo 2215435 10244029 := bstep (se 3 (by rfl) ⟨1920755, by rfl⟩ : syracuseStep 10244029 = 3841511) B3841511
theorem B13658705 : Blo 2215435 13658705 := bstep (se 2 (by rfl) ⟨5122014, by rfl⟩ : syracuseStep 13658705 = 10244029) B10244029
theorem B9105803 : Blo 2215435 9105803 := bstep (se 1 (by rfl) ⟨6829352, by rfl⟩ : syracuseStep 9105803 = 13658705) B13658705
theorem B6070535 : Blo 2215435 6070535 := bstep (se 1 (by rfl) ⟨4552901, by rfl⟩ : syracuseStep 6070535 = 9105803) B9105803
theorem B4047023 : Blo 2215435 4047023 := bstep (se 1 (by rfl) ⟨3035267, by rfl⟩ : syracuseStep 4047023 = 6070535) B6070535
theorem B10792061 : Blo 2215435 10792061 := bstep (se 3 (by rfl) ⟨2023511, by rfl⟩ : syracuseStep 10792061 = 4047023) B4047023
theorem B7194707 : Blo 2215435 7194707 := bstep (se 1 (by rfl) ⟨5396030, by rfl⟩ : syracuseStep 7194707 = 10792061) B10792061
theorem B4796471 : Blo 2215435 4796471 := bstep (se 1 (by rfl) ⟨3597353, by rfl⟩ : syracuseStep 4796471 = 7194707) B7194707
theorem B3197647 : Blo 2215435 3197647 := bstep (se 1 (by rfl) ⟨2398235, by rfl⟩ : syracuseStep 3197647 = 4796471) B4796471
theorem B4263529 : Blo 2215435 4263529 := bstep (se 2 (by rfl) ⟨1598823, by rfl⟩ : syracuseStep 4263529 = 3197647) B3197647
theorem B5684705 : Blo 2215435 5684705 := bstep (se 2 (by rfl) ⟨2131764, by rfl⟩ : syracuseStep 5684705 = 4263529) B4263529
theorem B3789803 : Blo 2215435 3789803 := bstep (se 1 (by rfl) ⟨2842352, by rfl⟩ : syracuseStep 3789803 = 5684705) B5684705
theorem B2526535 : Blo 2215435 2526535 := bstep (se 1 (by rfl) ⟨1894901, by rfl⟩ : syracuseStep 2526535 = 3789803) B3789803
theorem B3368713 : Blo 2215435 3368713 := bstep (se 2 (by rfl) ⟨1263267, by rfl⟩ : syracuseStep 3368713 = 2526535) B2526535
theorem B4491617 : Blo 2215435 4491617 := bstep (se 2 (by rfl) ⟨1684356, by rfl⟩ : syracuseStep 4491617 = 3368713) B3368713
theorem B11977645 : Blo 2215435 11977645 := bstep (se 3 (by rfl) ⟨2245808, by rfl⟩ : syracuseStep 11977645 = 4491617) B4491617
theorem B15970193 : Blo 2215435 15970193 := bstep (se 2 (by rfl) ⟨5988822, by rfl⟩ : syracuseStep 15970193 = 11977645) B11977645
theorem B10646795 : Blo 2215435 10646795 := bstep (se 1 (by rfl) ⟨7985096, by rfl⟩ : syracuseStep 10646795 = 15970193) B15970193
theorem B7097863 : Blo 2215435 7097863 := bstep (se 1 (by rfl) ⟨5323397, by rfl⟩ : syracuseStep 7097863 = 10646795) B10646795
theorem B9463817 : Blo 2215435 9463817 := bstep (se 2 (by rfl) ⟨3548931, by rfl⟩ : syracuseStep 9463817 = 7097863) B7097863
theorem B6309211 : Blo 2215435 6309211 := bstep (se 1 (by rfl) ⟨4731908, by rfl⟩ : syracuseStep 6309211 = 9463817) B9463817
theorem B8412281 : Blo 2215435 8412281 := bstep (se 2 (by rfl) ⟨3154605, by rfl⟩ : syracuseStep 8412281 = 6309211) B6309211
theorem B5608187 : Blo 2215435 5608187 := bstep (se 1 (by rfl) ⟨4206140, by rfl⟩ : syracuseStep 5608187 = 8412281) B8412281
theorem B3738791 : Blo 2215435 3738791 := bstep (se 1 (by rfl) ⟨2804093, by rfl⟩ : syracuseStep 3738791 = 5608187) B5608187
theorem B2492527 : Blo 2215435 2492527 := bstep (se 1 (by rfl) ⟨1869395, by rfl⟩ : syracuseStep 2492527 = 3738791) B3738791
theorem B3323369 : Blo 2215435 3323369 := bstep (se 2 (by rfl) ⟨1246263, by rfl⟩ : syracuseStep 3323369 = 2492527) B2492527
theorem B2215579 : Blo 2215435 2215579 := bstep (se 1 (by rfl) ⟨1661684, by rfl⟩ : syracuseStep 2215579 = 3323369) B3323369
theorem B11369429 : Blo 2215435 11369429 := bbase (se 7 (by rfl) ⟨133235, by rfl⟩ : syracuseStep 11369429 = 266471) (by norm_num)
theorem B7579619 : Blo 2215435 7579619 := bstep (se 1 (by rfl) ⟨5684714, by rfl⟩ : syracuseStep 7579619 = 11369429) B11369429
theorem B5053079 : Blo 2215435 5053079 := bstep (se 1 (by rfl) ⟨3789809, by rfl⟩ : syracuseStep 5053079 = 7579619) B7579619
theorem B3368719 : Blo 2215435 3368719 := bstep (se 1 (by rfl) ⟨2526539, by rfl⟩ : syracuseStep 3368719 = 5053079) B5053079
theorem B4491625 : Blo 2215435 4491625 := bstep (se 2 (by rfl) ⟨1684359, by rfl⟩ : syracuseStep 4491625 = 3368719) B3368719
theorem B5988833 : Blo 2215435 5988833 := bstep (se 2 (by rfl) ⟨2245812, by rfl⟩ : syracuseStep 5988833 = 4491625) B4491625
theorem B3992555 : Blo 2215435 3992555 := bstep (se 1 (by rfl) ⟨2994416, by rfl⟩ : syracuseStep 3992555 = 5988833) B5988833
theorem B2661703 : Blo 2215435 2661703 := bstep (se 1 (by rfl) ⟨1996277, by rfl⟩ : syracuseStep 2661703 = 3992555) B3992555
theorem B14195749 : Blo 2215435 14195749 := bstep (se 4 (by rfl) ⟨1330851, by rfl⟩ : syracuseStep 14195749 = 2661703) B2661703
theorem B18927665 : Blo 2215435 18927665 := bstep (se 2 (by rfl) ⟨7097874, by rfl⟩ : syracuseStep 18927665 = 14195749) B14195749
theorem B12618443 : Blo 2215435 12618443 := bstep (se 1 (by rfl) ⟨9463832, by rfl⟩ : syracuseStep 12618443 = 18927665) B18927665
theorem B8412295 : Blo 2215435 8412295 := bstep (se 1 (by rfl) ⟨6309221, by rfl⟩ : syracuseStep 8412295 = 12618443) B12618443
theorem B11216393 : Blo 2215435 11216393 := bstep (se 2 (by rfl) ⟨4206147, by rfl⟩ : syracuseStep 11216393 = 8412295) B8412295
theorem B7477595 : Blo 2215435 7477595 := bstep (se 1 (by rfl) ⟨5608196, by rfl⟩ : syracuseStep 7477595 = 11216393) B11216393
theorem B4985063 : Blo 2215435 4985063 := bstep (se 1 (by rfl) ⟨3738797, by rfl⟩ : syracuseStep 4985063 = 7477595) B7477595
theorem B3323375 : Blo 2215435 3323375 := bstep (se 1 (by rfl) ⟨2492531, by rfl⟩ : syracuseStep 3323375 = 4985063) B4985063
theorem B2215583 : Blo 2215435 2215583 := bstep (se 1 (by rfl) ⟨1661687, by rfl⟩ : syracuseStep 2215583 = 3323375) B3323375
theorem B3323381 : Blo 2215435 3323381 := bbase (se 5 (by rfl) ⟨155783, by rfl⟩ : syracuseStep 3323381 = 311567) (by norm_num)
theorem B2215587 : Blo 2215435 2215587 := bstep (se 1 (by rfl) ⟨1661690, by rfl⟩ : syracuseStep 2215587 = 3323381) B3323381
theorem B7985141 : Blo 2215435 7985141 := bbase (se 5 (by rfl) ⟨374303, by rfl⟩ : syracuseStep 7985141 = 748607) (by norm_num)
theorem B5323427 : Blo 2215435 5323427 := bstep (se 1 (by rfl) ⟨3992570, by rfl⟩ : syracuseStep 5323427 = 7985141) B7985141
theorem B3548951 : Blo 2215435 3548951 := bstep (se 1 (by rfl) ⟨2661713, by rfl⟩ : syracuseStep 3548951 = 5323427) B5323427
theorem B2365967 : Blo 2215435 2365967 := bstep (se 1 (by rfl) ⟨1774475, by rfl⟩ : syracuseStep 2365967 = 3548951) B3548951
theorem B6309245 : Blo 2215435 6309245 := bstep (se 3 (by rfl) ⟨1182983, by rfl⟩ : syracuseStep 6309245 = 2365967) B2365967
theorem B4206163 : Blo 2215435 4206163 := bstep (se 1 (by rfl) ⟨3154622, by rfl⟩ : syracuseStep 4206163 = 6309245) B6309245
theorem B5608217 : Blo 2215435 5608217 := bstep (se 2 (by rfl) ⟨2103081, by rfl⟩ : syracuseStep 5608217 = 4206163) B4206163
theorem B3738811 : Blo 2215435 3738811 := bstep (se 1 (by rfl) ⟨2804108, by rfl⟩ : syracuseStep 3738811 = 5608217) B5608217
theorem B4985081 : Blo 2215435 4985081 := bstep (se 2 (by rfl) ⟨1869405, by rfl⟩ : syracuseStep 4985081 = 3738811) B3738811
theorem B3323387 : Blo 2215435 3323387 := bstep (se 1 (by rfl) ⟨2492540, by rfl⟩ : syracuseStep 3323387 = 4985081) B4985081
theorem B2215591 : Blo 2215435 2215591 := bstep (se 1 (by rfl) ⟨1661693, by rfl⟩ : syracuseStep 2215591 = 3323387) B3323387
theorem B2492545 : Blo 2215435 2492545 := bbase (se 2 (by rfl) ⟨934704, by rfl⟩ : syracuseStep 2492545 = 1869409) (by norm_num)
theorem B3323393 : Blo 2215435 3323393 := bstep (se 2 (by rfl) ⟨1246272, by rfl⟩ : syracuseStep 3323393 = 2492545) B2492545
theorem B2215595 : Blo 2215435 2215595 := bstep (se 1 (by rfl) ⟨1661696, by rfl⟩ : syracuseStep 2215595 = 3323393) B3323393
theorem B5608237 : Blo 2215435 5608237 := bbase (se 3 (by rfl) ⟨1051544, by rfl⟩ : syracuseStep 5608237 = 2103089) (by norm_num)
theorem B7477649 : Blo 2215435 7477649 := bstep (se 2 (by rfl) ⟨2804118, by rfl⟩ : syracuseStep 7477649 = 5608237) B5608237
theorem B4985099 : Blo 2215435 4985099 := bstep (se 1 (by rfl) ⟨3738824, by rfl⟩ : syracuseStep 4985099 = 7477649) B7477649
theorem B3323399 : Blo 2215435 3323399 := bstep (se 1 (by rfl) ⟨2492549, by rfl⟩ : syracuseStep 3323399 = 4985099) B4985099
theorem B2215599 : Blo 2215435 2215599 := bstep (se 1 (by rfl) ⟨1661699, by rfl⟩ : syracuseStep 2215599 = 3323399) B3323399
theorem B3323405 : Blo 2215435 3323405 := bbase (se 3 (by rfl) ⟨623138, by rfl⟩ : syracuseStep 3323405 = 1246277) (by norm_num)
theorem B2215603 : Blo 2215435 2215603 := bstep (se 1 (by rfl) ⟨1661702, by rfl⟩ : syracuseStep 2215603 = 3323405) B3323405
theorem B4985117 : Blo 2215435 4985117 := bbase (se 3 (by rfl) ⟨934709, by rfl⟩ : syracuseStep 4985117 = 1869419) (by norm_num)
theorem B3323411 : Blo 2215435 3323411 := bstep (se 1 (by rfl) ⟨2492558, by rfl⟩ : syracuseStep 3323411 = 4985117) B4985117
theorem B2215607 : Blo 2215435 2215607 := bstep (se 1 (by rfl) ⟨1661705, by rfl⟩ : syracuseStep 2215607 = 3323411) B3323411
theorem B3738845 : Blo 2215435 3738845 := bbase (se 3 (by rfl) ⟨701033, by rfl⟩ : syracuseStep 3738845 = 1402067) (by norm_num)
theorem B2492563 : Blo 2215435 2492563 := bstep (se 1 (by rfl) ⟨1869422, by rfl⟩ : syracuseStep 2492563 = 3738845) B3738845
theorem B3323417 : Blo 2215435 3323417 := bstep (se 2 (by rfl) ⟨1246281, by rfl⟩ : syracuseStep 3323417 = 2492563) B2492563
theorem B2215611 : Blo 2215435 2215611 := bstep (se 1 (by rfl) ⟨1661708, by rfl⟩ : syracuseStep 2215611 = 3323417) B3323417
theorem B9593093 : Blo 2215435 9593093 := bbase (se 4 (by rfl) ⟨899352, by rfl⟩ : syracuseStep 9593093 = 1798705) (by norm_num)
theorem B25581581 : Blo 2215435 25581581 := bstep (se 3 (by rfl) ⟨4796546, by rfl⟩ : syracuseStep 25581581 = 9593093) B9593093
theorem B17054387 : Blo 2215435 17054387 := bstep (se 1 (by rfl) ⟨12790790, by rfl⟩ : syracuseStep 17054387 = 25581581) B25581581
theorem B11369591 : Blo 2215435 11369591 := bstep (se 1 (by rfl) ⟨8527193, by rfl⟩ : syracuseStep 11369591 = 17054387) B17054387
theorem B7579727 : Blo 2215435 7579727 := bstep (se 1 (by rfl) ⟨5684795, by rfl⟩ : syracuseStep 7579727 = 11369591) B11369591
theorem B5053151 : Blo 2215435 5053151 := bstep (se 1 (by rfl) ⟨3789863, by rfl⟩ : syracuseStep 5053151 = 7579727) B7579727
theorem B13475069 : Blo 2215435 13475069 := bstep (se 3 (by rfl) ⟨2526575, by rfl⟩ : syracuseStep 13475069 = 5053151) B5053151
theorem B8983379 : Blo 2215435 8983379 := bstep (se 1 (by rfl) ⟨6737534, by rfl⟩ : syracuseStep 8983379 = 13475069) B13475069
theorem B5988919 : Blo 2215435 5988919 := bstep (se 1 (by rfl) ⟨4491689, by rfl⟩ : syracuseStep 5988919 = 8983379) B8983379
theorem B7985225 : Blo 2215435 7985225 := bstep (se 2 (by rfl) ⟨2994459, by rfl⟩ : syracuseStep 7985225 = 5988919) B5988919
theorem B5323483 : Blo 2215435 5323483 := bstep (se 1 (by rfl) ⟨3992612, by rfl⟩ : syracuseStep 5323483 = 7985225) B7985225
theorem B7097977 : Blo 2215435 7097977 := bstep (se 2 (by rfl) ⟨2661741, by rfl⟩ : syracuseStep 7097977 = 5323483) B5323483
theorem B9463969 : Blo 2215435 9463969 := bstep (se 2 (by rfl) ⟨3548988, by rfl⟩ : syracuseStep 9463969 = 7097977) B7097977
theorem B12618625 : Blo 2215435 12618625 := bstep (se 2 (by rfl) ⟨4731984, by rfl⟩ : syracuseStep 12618625 = 9463969) B9463969
theorem B16824833 : Blo 2215435 16824833 := bstep (se 2 (by rfl) ⟨6309312, by rfl⟩ : syracuseStep 16824833 = 12618625) B12618625
theorem B11216555 : Blo 2215435 11216555 := bstep (se 1 (by rfl) ⟨8412416, by rfl⟩ : syracuseStep 11216555 = 16824833) B16824833
theorem B7477703 : Blo 2215435 7477703 := bstep (se 1 (by rfl) ⟨5608277, by rfl⟩ : syracuseStep 7477703 = 11216555) B11216555
theorem B4985135 : Blo 2215435 4985135 := bstep (se 1 (by rfl) ⟨3738851, by rfl⟩ : syracuseStep 4985135 = 7477703) B7477703
theorem B3323423 : Blo 2215435 3323423 := bstep (se 1 (by rfl) ⟨2492567, by rfl⟩ : syracuseStep 3323423 = 4985135) B4985135
theorem B2215615 : Blo 2215435 2215615 := bstep (se 1 (by rfl) ⟨1661711, by rfl⟩ : syracuseStep 2215615 = 3323423) B3323423
theorem B3323429 : Blo 2215435 3323429 := bbase (se 4 (by rfl) ⟨311571, by rfl⟩ : syracuseStep 3323429 = 623143) (by norm_num)
theorem B2215619 : Blo 2215435 2215619 := bstep (se 1 (by rfl) ⟨1661714, by rfl⟩ : syracuseStep 2215619 = 3323429) B3323429
theorem B2804149 : Blo 2215435 2804149 := bbase (se 5 (by rfl) ⟨131444, by rfl⟩ : syracuseStep 2804149 = 262889) (by norm_num)
theorem B3738865 : Blo 2215435 3738865 := bstep (se 2 (by rfl) ⟨1402074, by rfl⟩ : syracuseStep 3738865 = 2804149) B2804149
theorem B4985153 : Blo 2215435 4985153 := bstep (se 2 (by rfl) ⟨1869432, by rfl⟩ : syracuseStep 4985153 = 3738865) B3738865
theorem B3323435 : Blo 2215435 3323435 := bstep (se 1 (by rfl) ⟨2492576, by rfl⟩ : syracuseStep 3323435 = 4985153) B4985153
theorem B2215623 : Blo 2215435 2215623 := bstep (se 1 (by rfl) ⟨1661717, by rfl⟩ : syracuseStep 2215623 = 3323435) B3323435
theorem B2492581 : Blo 2215435 2492581 := bbase (se 4 (by rfl) ⟨233679, by rfl⟩ : syracuseStep 2492581 = 467359) (by norm_num)
theorem B3323441 : Blo 2215435 3323441 := bstep (se 2 (by rfl) ⟨1246290, by rfl⟩ : syracuseStep 3323441 = 2492581) B2492581
theorem B2215627 : Blo 2215435 2215627 := bstep (se 1 (by rfl) ⟨1661720, by rfl⟩ : syracuseStep 2215627 = 3323441) B3323441
theorem B4796581 : Blo 2215435 4796581 := bbase (se 4 (by rfl) ⟨449679, by rfl⟩ : syracuseStep 4796581 = 899359) (by norm_num)
theorem B6395441 : Blo 2215435 6395441 := bstep (se 2 (by rfl) ⟨2398290, by rfl⟩ : syracuseStep 6395441 = 4796581) B4796581
theorem B17054509 : Blo 2215435 17054509 := bstep (se 3 (by rfl) ⟨3197720, by rfl⟩ : syracuseStep 17054509 = 6395441) B6395441
theorem B22739345 : Blo 2215435 22739345 := bstep (se 2 (by rfl) ⟨8527254, by rfl⟩ : syracuseStep 22739345 = 17054509) B17054509
theorem B15159563 : Blo 2215435 15159563 := bstep (se 1 (by rfl) ⟨11369672, by rfl⟩ : syracuseStep 15159563 = 22739345) B22739345
theorem B10106375 : Blo 2215435 10106375 := bstep (se 1 (by rfl) ⟨7579781, by rfl⟩ : syracuseStep 10106375 = 15159563) B15159563
theorem B26950333 : Blo 2215435 26950333 := bstep (se 3 (by rfl) ⟨5053187, by rfl⟩ : syracuseStep 26950333 = 10106375) B10106375
theorem B35933777 : Blo 2215435 35933777 := bstep (se 2 (by rfl) ⟨13475166, by rfl⟩ : syracuseStep 35933777 = 26950333) B26950333
theorem B23955851 : Blo 2215435 23955851 := bstep (se 1 (by rfl) ⟨17966888, by rfl⟩ : syracuseStep 23955851 = 35933777) B35933777
theorem B15970567 : Blo 2215435 15970567 := bstep (se 1 (by rfl) ⟨11977925, by rfl⟩ : syracuseStep 15970567 = 23955851) B23955851
theorem B21294089 : Blo 2215435 21294089 := bstep (se 2 (by rfl) ⟨7985283, by rfl⟩ : syracuseStep 21294089 = 15970567) B15970567
theorem B14196059 : Blo 2215435 14196059 := bstep (se 1 (by rfl) ⟨10647044, by rfl⟩ : syracuseStep 14196059 = 21294089) B21294089
theorem B9464039 : Blo 2215435 9464039 := bstep (se 1 (by rfl) ⟨7098029, by rfl⟩ : syracuseStep 9464039 = 14196059) B14196059
theorem B6309359 : Blo 2215435 6309359 := bstep (se 1 (by rfl) ⟨4732019, by rfl⟩ : syracuseStep 6309359 = 9464039) B9464039
theorem B4206239 : Blo 2215435 4206239 := bstep (se 1 (by rfl) ⟨3154679, by rfl⟩ : syracuseStep 4206239 = 6309359) B6309359
theorem B2804159 : Blo 2215435 2804159 := bstep (se 1 (by rfl) ⟨2103119, by rfl⟩ : syracuseStep 2804159 = 4206239) B4206239
theorem B7477757 : Blo 2215435 7477757 := bstep (se 3 (by rfl) ⟨1402079, by rfl⟩ : syracuseStep 7477757 = 2804159) B2804159
theorem B4985171 : Blo 2215435 4985171 := bstep (se 1 (by rfl) ⟨3738878, by rfl⟩ : syracuseStep 4985171 = 7477757) B7477757
theorem B3323447 : Blo 2215435 3323447 := bstep (se 1 (by rfl) ⟨2492585, by rfl⟩ : syracuseStep 3323447 = 4985171) B4985171
theorem B2215631 : Blo 2215435 2215631 := bstep (se 1 (by rfl) ⟨1661723, by rfl⟩ : syracuseStep 2215631 = 3323447) B3323447
theorem B3323453 : Blo 2215435 3323453 := bbase (se 3 (by rfl) ⟨623147, by rfl⟩ : syracuseStep 3323453 = 1246295) (by norm_num)
theorem B2215635 : Blo 2215435 2215635 := bstep (se 1 (by rfl) ⟨1661726, by rfl⟩ : syracuseStep 2215635 = 3323453) B3323453
theorem B4985189 : Blo 2215435 4985189 := bbase (se 4 (by rfl) ⟨467361, by rfl⟩ : syracuseStep 4985189 = 934723) (by norm_num)
theorem B3323459 : Blo 2215435 3323459 := bstep (se 1 (by rfl) ⟨2492594, by rfl⟩ : syracuseStep 3323459 = 4985189) B4985189
theorem B2215639 : Blo 2215435 2215639 := bstep (se 1 (by rfl) ⟨1661729, by rfl⟩ : syracuseStep 2215639 = 3323459) B3323459
theorem B5608349 : Blo 2215435 5608349 := bbase (se 3 (by rfl) ⟨1051565, by rfl⟩ : syracuseStep 5608349 = 2103131) (by norm_num)
theorem B3738899 : Blo 2215435 3738899 := bstep (se 1 (by rfl) ⟨2804174, by rfl⟩ : syracuseStep 3738899 = 5608349) B5608349
theorem B2492599 : Blo 2215435 2492599 := bstep (se 1 (by rfl) ⟨1869449, by rfl⟩ : syracuseStep 2492599 = 3738899) B3738899
theorem B3323465 : Blo 2215435 3323465 := bstep (se 2 (by rfl) ⟨1246299, by rfl⟩ : syracuseStep 3323465 = 2492599) B2492599
theorem B2215643 : Blo 2215435 2215643 := bstep (se 1 (by rfl) ⟨1661732, by rfl⟩ : syracuseStep 2215643 = 3323465) B3323465
theorem B4206269 : Blo 2215435 4206269 := bbase (se 3 (by rfl) ⟨788675, by rfl⟩ : syracuseStep 4206269 = 1577351) (by norm_num)
theorem B11216717 : Blo 2215435 11216717 := bstep (se 3 (by rfl) ⟨2103134, by rfl⟩ : syracuseStep 11216717 = 4206269) B4206269
theorem B7477811 : Blo 2215435 7477811 := bstep (se 1 (by rfl) ⟨5608358, by rfl⟩ : syracuseStep 7477811 = 11216717) B11216717
theorem B4985207 : Blo 2215435 4985207 := bstep (se 1 (by rfl) ⟨3738905, by rfl⟩ : syracuseStep 4985207 = 7477811) B7477811
theorem B3323471 : Blo 2215435 3323471 := bstep (se 1 (by rfl) ⟨2492603, by rfl⟩ : syracuseStep 3323471 = 4985207) B4985207
theorem B2215647 : Blo 2215435 2215647 := bstep (se 1 (by rfl) ⟨1661735, by rfl⟩ : syracuseStep 2215647 = 3323471) B3323471
theorem B3323477 : Blo 2215435 3323477 := bbase (se 8 (by rfl) ⟨19473, by rfl⟩ : syracuseStep 3323477 = 38947) (by norm_num)
theorem B2215651 : Blo 2215435 2215651 := bstep (se 1 (by rfl) ⟨1661738, by rfl⟩ : syracuseStep 2215651 = 3323477) B3323477
theorem B3549053 : Blo 2215435 3549053 := bbase (se 3 (by rfl) ⟨665447, by rfl⟩ : syracuseStep 3549053 = 1330895) (by norm_num)
theorem B9464141 : Blo 2215435 9464141 := bstep (se 3 (by rfl) ⟨1774526, by rfl⟩ : syracuseStep 9464141 = 3549053) B3549053
theorem B6309427 : Blo 2215435 6309427 := bstep (se 1 (by rfl) ⟨4732070, by rfl⟩ : syracuseStep 6309427 = 9464141) B9464141
theorem B8412569 : Blo 2215435 8412569 := bstep (se 2 (by rfl) ⟨3154713, by rfl⟩ : syracuseStep 8412569 = 6309427) B6309427
theorem B5608379 : Blo 2215435 5608379 := bstep (se 1 (by rfl) ⟨4206284, by rfl⟩ : syracuseStep 5608379 = 8412569) B8412569
theorem B3738919 : Blo 2215435 3738919 := bstep (se 1 (by rfl) ⟨2804189, by rfl⟩ : syracuseStep 3738919 = 5608379) B5608379
theorem B4985225 : Blo 2215435 4985225 := bstep (se 2 (by rfl) ⟨1869459, by rfl⟩ : syracuseStep 4985225 = 3738919) B3738919
theorem B3323483 : Blo 2215435 3323483 := bstep (se 1 (by rfl) ⟨2492612, by rfl⟩ : syracuseStep 3323483 = 4985225) B4985225
theorem B2215655 : Blo 2215435 2215655 := bstep (se 1 (by rfl) ⟨1661741, by rfl⟩ : syracuseStep 2215655 = 3323483) B3323483
theorem B2492617 : Blo 2215435 2492617 := bbase (se 2 (by rfl) ⟨934731, by rfl⟩ : syracuseStep 2492617 = 1869463) (by norm_num)
theorem B3323489 : Blo 2215435 3323489 := bstep (se 2 (by rfl) ⟨1246308, by rfl⟩ : syracuseStep 3323489 = 2492617) B2492617
theorem B2215659 : Blo 2215435 2215659 := bstep (se 1 (by rfl) ⟨1661744, by rfl⟩ : syracuseStep 2215659 = 3323489) B3323489
theorem B5053261 : Blo 2215435 5053261 := bbase (se 3 (by rfl) ⟨947486, by rfl⟩ : syracuseStep 5053261 = 1894973) (by norm_num)
theorem B6737681 : Blo 2215435 6737681 := bstep (se 2 (by rfl) ⟨2526630, by rfl⟩ : syracuseStep 6737681 = 5053261) B5053261
theorem B4491787 : Blo 2215435 4491787 := bstep (se 1 (by rfl) ⟨3368840, by rfl⟩ : syracuseStep 4491787 = 6737681) B6737681
theorem B5989049 : Blo 2215435 5989049 := bstep (se 2 (by rfl) ⟨2245893, by rfl⟩ : syracuseStep 5989049 = 4491787) B4491787
theorem B3992699 : Blo 2215435 3992699 := bstep (se 1 (by rfl) ⟨2994524, by rfl⟩ : syracuseStep 3992699 = 5989049) B5989049
theorem B10647197 : Blo 2215435 10647197 := bstep (se 3 (by rfl) ⟨1996349, by rfl⟩ : syracuseStep 10647197 = 3992699) B3992699
theorem B7098131 : Blo 2215435 7098131 := bstep (se 1 (by rfl) ⟨5323598, by rfl⟩ : syracuseStep 7098131 = 10647197) B10647197
theorem B18928349 : Blo 2215435 18928349 := bstep (se 3 (by rfl) ⟨3549065, by rfl⟩ : syracuseStep 18928349 = 7098131) B7098131
theorem B12618899 : Blo 2215435 12618899 := bstep (se 1 (by rfl) ⟨9464174, by rfl⟩ : syracuseStep 12618899 = 18928349) B18928349
theorem B8412599 : Blo 2215435 8412599 := bstep (se 1 (by rfl) ⟨6309449, by rfl⟩ : syracuseStep 8412599 = 12618899) B12618899
theorem B5608399 : Blo 2215435 5608399 := bstep (se 1 (by rfl) ⟨4206299, by rfl⟩ : syracuseStep 5608399 = 8412599) B8412599
theorem B7477865 : Blo 2215435 7477865 := bstep (se 2 (by rfl) ⟨2804199, by rfl⟩ : syracuseStep 7477865 = 5608399) B5608399
theorem B4985243 : Blo 2215435 4985243 := bstep (se 1 (by rfl) ⟨3738932, by rfl⟩ : syracuseStep 4985243 = 7477865) B7477865
theorem B3323495 : Blo 2215435 3323495 := bstep (se 1 (by rfl) ⟨2492621, by rfl⟩ : syracuseStep 3323495 = 4985243) B4985243
theorem B2215663 : Blo 2215435 2215663 := bstep (se 1 (by rfl) ⟨1661747, by rfl⟩ : syracuseStep 2215663 = 3323495) B3323495
theorem B3323501 : Blo 2215435 3323501 := bbase (se 3 (by rfl) ⟨623156, by rfl⟩ : syracuseStep 3323501 = 1246313) (by norm_num)
theorem B2215667 : Blo 2215435 2215667 := bstep (se 1 (by rfl) ⟨1661750, by rfl⟩ : syracuseStep 2215667 = 3323501) B3323501
theorem B4985261 : Blo 2215435 4985261 := bbase (se 3 (by rfl) ⟨934736, by rfl⟩ : syracuseStep 4985261 = 1869473) (by norm_num)
theorem B3323507 : Blo 2215435 3323507 := bstep (se 1 (by rfl) ⟨2492630, by rfl⟩ : syracuseStep 3323507 = 4985261) B4985261
theorem B2215671 : Blo 2215435 2215671 := bstep (se 1 (by rfl) ⟨1661753, by rfl⟩ : syracuseStep 2215671 = 3323507) B3323507
theorem B2366057 : Blo 2215435 2366057 := bbase (se 2 (by rfl) ⟨887271, by rfl⟩ : syracuseStep 2366057 = 1774543) (by norm_num)
theorem B6309485 : Blo 2215435 6309485 := bstep (se 3 (by rfl) ⟨1183028, by rfl⟩ : syracuseStep 6309485 = 2366057) B2366057
theorem B4206323 : Blo 2215435 4206323 := bstep (se 1 (by rfl) ⟨3154742, by rfl⟩ : syracuseStep 4206323 = 6309485) B6309485
theorem B2804215 : Blo 2215435 2804215 := bstep (se 1 (by rfl) ⟨2103161, by rfl⟩ : syracuseStep 2804215 = 4206323) B4206323
theorem B3738953 : Blo 2215435 3738953 := bstep (se 2 (by rfl) ⟨1402107, by rfl⟩ : syracuseStep 3738953 = 2804215) B2804215
theorem B2492635 : Blo 2215435 2492635 := bstep (se 1 (by rfl) ⟨1869476, by rfl⟩ : syracuseStep 2492635 = 3738953) B3738953
theorem B3323513 : Blo 2215435 3323513 := bstep (se 2 (by rfl) ⟨1246317, by rfl⟩ : syracuseStep 3323513 = 2492635) B2492635
theorem B2215675 : Blo 2215435 2215675 := bstep (se 1 (by rfl) ⟨1661756, by rfl⟩ : syracuseStep 2215675 = 3323513) B3323513
theorem B8983637 : Blo 2215435 8983637 := bbase (se 8 (by rfl) ⟨52638, by rfl⟩ : syracuseStep 8983637 = 105277) (by norm_num)
theorem B5989091 : Blo 2215435 5989091 := bstep (se 1 (by rfl) ⟨4491818, by rfl⟩ : syracuseStep 5989091 = 8983637) B8983637
theorem B63883637 : Blo 2215435 63883637 := bstep (se 5 (by rfl) ⟨2994545, by rfl⟩ : syracuseStep 63883637 = 5989091) B5989091
theorem B42589091 : Blo 2215435 42589091 := bstep (se 1 (by rfl) ⟨31941818, by rfl⟩ : syracuseStep 42589091 = 63883637) B63883637
theorem B28392727 : Blo 2215435 28392727 := bstep (se 1 (by rfl) ⟨21294545, by rfl⟩ : syracuseStep 28392727 = 42589091) B42589091
theorem B37856969 : Blo 2215435 37856969 := bstep (se 2 (by rfl) ⟨14196363, by rfl⟩ : syracuseStep 37856969 = 28392727) B28392727
theorem B25237979 : Blo 2215435 25237979 := bstep (se 1 (by rfl) ⟨18928484, by rfl⟩ : syracuseStep 25237979 = 37856969) B37856969
theorem B16825319 : Blo 2215435 16825319 := bstep (se 1 (by rfl) ⟨12618989, by rfl⟩ : syracuseStep 16825319 = 25237979) B25237979
theorem B11216879 : Blo 2215435 11216879 := bstep (se 1 (by rfl) ⟨8412659, by rfl⟩ : syracuseStep 11216879 = 16825319) B16825319
theorem B7477919 : Blo 2215435 7477919 := bstep (se 1 (by rfl) ⟨5608439, by rfl⟩ : syracuseStep 7477919 = 11216879) B11216879
theorem B4985279 : Blo 2215435 4985279 := bstep (se 1 (by rfl) ⟨3738959, by rfl⟩ : syracuseStep 4985279 = 7477919) B7477919
theorem B3323519 : Blo 2215435 3323519 := bstep (se 1 (by rfl) ⟨2492639, by rfl⟩ : syracuseStep 3323519 = 4985279) B4985279
theorem B2215679 : Blo 2215435 2215679 := bstep (se 1 (by rfl) ⟨1661759, by rfl⟩ : syracuseStep 2215679 = 3323519) B3323519
theorem B3323525 : Blo 2215435 3323525 := bbase (se 4 (by rfl) ⟨311580, by rfl⟩ : syracuseStep 3323525 = 623161) (by norm_num)
theorem B2215683 : Blo 2215435 2215683 := bstep (se 1 (by rfl) ⟨1661762, by rfl⟩ : syracuseStep 2215683 = 3323525) B3323525
theorem B3738973 : Blo 2215435 3738973 := bbase (se 3 (by rfl) ⟨701057, by rfl⟩ : syracuseStep 3738973 = 1402115) (by norm_num)
theorem B4985297 : Blo 2215435 4985297 := bstep (se 2 (by rfl) ⟨1869486, by rfl⟩ : syracuseStep 4985297 = 3738973) B3738973
theorem B3323531 : Blo 2215435 3323531 := bstep (se 1 (by rfl) ⟨2492648, by rfl⟩ : syracuseStep 3323531 = 4985297) B4985297
theorem B2215687 : Blo 2215435 2215687 := bstep (se 1 (by rfl) ⟨1661765, by rfl⟩ : syracuseStep 2215687 = 3323531) B3323531
theorem B2492653 : Blo 2215435 2492653 := bbase (se 3 (by rfl) ⟨467372, by rfl⟩ : syracuseStep 2492653 = 934745) (by norm_num)
theorem B3323537 : Blo 2215435 3323537 := bstep (se 2 (by rfl) ⟨1246326, by rfl⟩ : syracuseStep 3323537 = 2492653) B2492653
theorem B2215691 : Blo 2215435 2215691 := bstep (se 1 (by rfl) ⟨1661768, by rfl⟩ : syracuseStep 2215691 = 3323537) B3323537
theorem B7477973 : Blo 2215435 7477973 := bbase (se 7 (by rfl) ⟨87632, by rfl⟩ : syracuseStep 7477973 = 175265) (by norm_num)
theorem B4985315 : Blo 2215435 4985315 := bstep (se 1 (by rfl) ⟨3738986, by rfl⟩ : syracuseStep 4985315 = 7477973) B7477973
theorem B3323543 : Blo 2215435 3323543 := bstep (se 1 (by rfl) ⟨2492657, by rfl⟩ : syracuseStep 3323543 = 4985315) B4985315
theorem B2215695 : Blo 2215435 2215695 := bstep (se 1 (by rfl) ⟨1661771, by rfl⟩ : syracuseStep 2215695 = 3323543) B3323543
theorem B3323549 : Blo 2215435 3323549 := bbase (se 3 (by rfl) ⟨623165, by rfl⟩ : syracuseStep 3323549 = 1246331) (by norm_num)
theorem B2215699 : Blo 2215435 2215699 := bstep (se 1 (by rfl) ⟨1661774, by rfl⟩ : syracuseStep 2215699 = 3323549) B3323549
theorem B4985333 : Blo 2215435 4985333 := bbase (se 5 (by rfl) ⟨233687, by rfl⟩ : syracuseStep 4985333 = 467375) (by norm_num)
theorem B3323555 : Blo 2215435 3323555 := bstep (se 1 (by rfl) ⟨2492666, by rfl⟩ : syracuseStep 3323555 = 4985333) B4985333
theorem B2215703 : Blo 2215435 2215703 := bstep (se 1 (by rfl) ⟨1661777, by rfl⟩ : syracuseStep 2215703 = 3323555) B3323555
theorem B7985557 : Blo 2215435 7985557 := bbase (se 6 (by rfl) ⟨187161, by rfl⟩ : syracuseStep 7985557 = 374323) (by norm_num)
theorem B42589637 : Blo 2215435 42589637 := bstep (se 4 (by rfl) ⟨3992778, by rfl⟩ : syracuseStep 42589637 = 7985557) B7985557
theorem B28393091 : Blo 2215435 28393091 := bstep (se 1 (by rfl) ⟨21294818, by rfl⟩ : syracuseStep 28393091 = 42589637) B42589637
theorem B18928727 : Blo 2215435 18928727 := bstep (se 1 (by rfl) ⟨14196545, by rfl⟩ : syracuseStep 18928727 = 28393091) B28393091
theorem B12619151 : Blo 2215435 12619151 := bstep (se 1 (by rfl) ⟨9464363, by rfl⟩ : syracuseStep 12619151 = 18928727) B18928727
theorem B8412767 : Blo 2215435 8412767 := bstep (se 1 (by rfl) ⟨6309575, by rfl⟩ : syracuseStep 8412767 = 12619151) B12619151
theorem B5608511 : Blo 2215435 5608511 := bstep (se 1 (by rfl) ⟨4206383, by rfl⟩ : syracuseStep 5608511 = 8412767) B8412767
theorem B3739007 : Blo 2215435 3739007 := bstep (se 1 (by rfl) ⟨2804255, by rfl⟩ : syracuseStep 3739007 = 5608511) B5608511
theorem B2492671 : Blo 2215435 2492671 := bstep (se 1 (by rfl) ⟨1869503, by rfl⟩ : syracuseStep 2492671 = 3739007) B3739007
theorem B3323561 : Blo 2215435 3323561 := bstep (se 2 (by rfl) ⟨1246335, by rfl⟩ : syracuseStep 3323561 = 2492671) B2492671
theorem B2215707 : Blo 2215435 2215707 := bstep (se 1 (by rfl) ⟨1661780, by rfl⟩ : syracuseStep 2215707 = 3323561) B3323561
theorem B7985573 : Blo 2215435 7985573 := bbase (se 4 (by rfl) ⟨748647, by rfl⟩ : syracuseStep 7985573 = 1497295) (by norm_num)
theorem B5323715 : Blo 2215435 5323715 := bstep (se 1 (by rfl) ⟨3992786, by rfl⟩ : syracuseStep 5323715 = 7985573) B7985573
theorem B3549143 : Blo 2215435 3549143 := bstep (se 1 (by rfl) ⟨2661857, by rfl⟩ : syracuseStep 3549143 = 5323715) B5323715
theorem B2366095 : Blo 2215435 2366095 := bstep (se 1 (by rfl) ⟨1774571, by rfl⟩ : syracuseStep 2366095 = 3549143) B3549143
theorem B3154793 : Blo 2215435 3154793 := bstep (se 2 (by rfl) ⟨1183047, by rfl⟩ : syracuseStep 3154793 = 2366095) B2366095
theorem B8412781 : Blo 2215435 8412781 := bstep (se 3 (by rfl) ⟨1577396, by rfl⟩ : syracuseStep 8412781 = 3154793) B3154793
theorem B11217041 : Blo 2215435 11217041 := bstep (se 2 (by rfl) ⟨4206390, by rfl⟩ : syracuseStep 11217041 = 8412781) B8412781
theorem B7478027 : Blo 2215435 7478027 := bstep (se 1 (by rfl) ⟨5608520, by rfl⟩ : syracuseStep 7478027 = 11217041) B11217041
theorem B4985351 : Blo 2215435 4985351 := bstep (se 1 (by rfl) ⟨3739013, by rfl⟩ : syracuseStep 4985351 = 7478027) B7478027
theorem B3323567 : Blo 2215435 3323567 := bstep (se 1 (by rfl) ⟨2492675, by rfl⟩ : syracuseStep 3323567 = 4985351) B4985351
theorem B2215711 : Blo 2215435 2215711 := bstep (se 1 (by rfl) ⟨1661783, by rfl⟩ : syracuseStep 2215711 = 3323567) B3323567
theorem B3323573 : Blo 2215435 3323573 := bbase (se 5 (by rfl) ⟨155792, by rfl⟩ : syracuseStep 3323573 = 311585) (by norm_num)
theorem B2215715 : Blo 2215435 2215715 := bstep (se 1 (by rfl) ⟨1661786, by rfl⟩ : syracuseStep 2215715 = 3323573) B3323573
theorem B5608541 : Blo 2215435 5608541 := bbase (se 3 (by rfl) ⟨1051601, by rfl⟩ : syracuseStep 5608541 = 2103203) (by norm_num)
theorem B3739027 : Blo 2215435 3739027 := bstep (se 1 (by rfl) ⟨2804270, by rfl⟩ : syracuseStep 3739027 = 5608541) B5608541
theorem B4985369 : Blo 2215435 4985369 := bstep (se 2 (by rfl) ⟨1869513, by rfl⟩ : syracuseStep 4985369 = 3739027) B3739027
theorem B3323579 : Blo 2215435 3323579 := bstep (se 1 (by rfl) ⟨2492684, by rfl⟩ : syracuseStep 3323579 = 4985369) B4985369
theorem B2215719 : Blo 2215435 2215719 := bstep (se 1 (by rfl) ⟨1661789, by rfl⟩ : syracuseStep 2215719 = 3323579) B3323579
theorem B2492689 : Blo 2215435 2492689 := bbase (se 2 (by rfl) ⟨934758, by rfl⟩ : syracuseStep 2492689 = 1869517) (by norm_num)
theorem B3323585 : Blo 2215435 3323585 := bstep (se 2 (by rfl) ⟨1246344, by rfl⟩ : syracuseStep 3323585 = 2492689) B2492689
theorem B2215723 : Blo 2215435 2215723 := bstep (se 1 (by rfl) ⟨1661792, by rfl⟩ : syracuseStep 2215723 = 3323585) B3323585
theorem B4206421 : Blo 2215435 4206421 := bbase (se 9 (by rfl) ⟨12323, by rfl⟩ : syracuseStep 4206421 = 24647) (by norm_num)
theorem B5608561 : Blo 2215435 5608561 := bstep (se 2 (by rfl) ⟨2103210, by rfl⟩ : syracuseStep 5608561 = 4206421) B4206421
theorem B7478081 : Blo 2215435 7478081 := bstep (se 2 (by rfl) ⟨2804280, by rfl⟩ : syracuseStep 7478081 = 5608561) B5608561
theorem B4985387 : Blo 2215435 4985387 := bstep (se 1 (by rfl) ⟨3739040, by rfl⟩ : syracuseStep 4985387 = 7478081) B7478081
theorem B3323591 : Blo 2215435 3323591 := bstep (se 1 (by rfl) ⟨2492693, by rfl⟩ : syracuseStep 3323591 = 4985387) B4985387
theorem B2215727 : Blo 2215435 2215727 := bstep (se 1 (by rfl) ⟨1661795, by rfl⟩ : syracuseStep 2215727 = 3323591) B3323591
theorem B3323597 : Blo 2215435 3323597 := bbase (se 3 (by rfl) ⟨623174, by rfl⟩ : syracuseStep 3323597 = 1246349) (by norm_num)
theorem B2215731 : Blo 2215435 2215731 := bstep (se 1 (by rfl) ⟨1661798, by rfl⟩ : syracuseStep 2215731 = 3323597) B3323597
theorem B4985405 : Blo 2215435 4985405 := bbase (se 3 (by rfl) ⟨934763, by rfl⟩ : syracuseStep 4985405 = 1869527) (by norm_num)
theorem B3323603 : Blo 2215435 3323603 := bstep (se 1 (by rfl) ⟨2492702, by rfl⟩ : syracuseStep 3323603 = 4985405) B4985405
theorem B2215735 : Blo 2215435 2215735 := bstep (se 1 (by rfl) ⟨1661801, by rfl⟩ : syracuseStep 2215735 = 3323603) B3323603
theorem B3739061 : Blo 2215435 3739061 := bbase (se 5 (by rfl) ⟨175268, by rfl⟩ : syracuseStep 3739061 = 350537) (by norm_num)
theorem B2492707 : Blo 2215435 2492707 := bstep (se 1 (by rfl) ⟨1869530, by rfl⟩ : syracuseStep 2492707 = 3739061) B3739061
theorem B3323609 : Blo 2215435 3323609 := bstep (se 2 (by rfl) ⟨1246353, by rfl⟩ : syracuseStep 3323609 = 2492707) B2492707
theorem B2215739 : Blo 2215435 2215739 := bstep (se 1 (by rfl) ⟨1661804, by rfl⟩ : syracuseStep 2215739 = 3323609) B3323609
theorem B2366129 : Blo 2215435 2366129 := bbase (se 2 (by rfl) ⟨887298, by rfl⟩ : syracuseStep 2366129 = 1774597) (by norm_num)
theorem B6309677 : Blo 2215435 6309677 := bstep (se 3 (by rfl) ⟨1183064, by rfl⟩ : syracuseStep 6309677 = 2366129) B2366129
theorem B16825805 : Blo 2215435 16825805 := bstep (se 3 (by rfl) ⟨3154838, by rfl⟩ : syracuseStep 16825805 = 6309677) B6309677
theorem B11217203 : Blo 2215435 11217203 := bstep (se 1 (by rfl) ⟨8412902, by rfl⟩ : syracuseStep 11217203 = 16825805) B16825805
theorem B7478135 : Blo 2215435 7478135 := bstep (se 1 (by rfl) ⟨5608601, by rfl⟩ : syracuseStep 7478135 = 11217203) B11217203
theorem B4985423 : Blo 2215435 4985423 := bstep (se 1 (by rfl) ⟨3739067, by rfl⟩ : syracuseStep 4985423 = 7478135) B7478135
theorem B3323615 : Blo 2215435 3323615 := bstep (se 1 (by rfl) ⟨2492711, by rfl⟩ : syracuseStep 3323615 = 4985423) B4985423
theorem B2215743 : Blo 2215435 2215743 := bstep (se 1 (by rfl) ⟨1661807, by rfl⟩ : syracuseStep 2215743 = 3323615) B3323615
theorem B3323621 : Blo 2215435 3323621 := bbase (se 4 (by rfl) ⟨311589, by rfl⟩ : syracuseStep 3323621 = 623179) (by norm_num)
theorem B2215747 : Blo 2215435 2215747 := bstep (se 1 (by rfl) ⟨1661810, by rfl⟩ : syracuseStep 2215747 = 3323621) B3323621
theorem B6309701 : Blo 2215435 6309701 := bbase (se 4 (by rfl) ⟨591534, by rfl⟩ : syracuseStep 6309701 = 1183069) (by norm_num)
theorem B4206467 : Blo 2215435 4206467 := bstep (se 1 (by rfl) ⟨3154850, by rfl⟩ : syracuseStep 4206467 = 6309701) B6309701
theorem B2804311 : Blo 2215435 2804311 := bstep (se 1 (by rfl) ⟨2103233, by rfl⟩ : syracuseStep 2804311 = 4206467) B4206467
theorem B3739081 : Blo 2215435 3739081 := bstep (se 2 (by rfl) ⟨1402155, by rfl⟩ : syracuseStep 3739081 = 2804311) B2804311
theorem B4985441 : Blo 2215435 4985441 := bstep (se 2 (by rfl) ⟨1869540, by rfl⟩ : syracuseStep 4985441 = 3739081) B3739081
theorem B3323627 : Blo 2215435 3323627 := bstep (se 1 (by rfl) ⟨2492720, by rfl⟩ : syracuseStep 3323627 = 4985441) B4985441
theorem B2215751 : Blo 2215435 2215751 := bstep (se 1 (by rfl) ⟨1661813, by rfl⟩ : syracuseStep 2215751 = 3323627) B3323627
theorem B2492725 : Blo 2215435 2492725 := bbase (se 5 (by rfl) ⟨116846, by rfl⟩ : syracuseStep 2492725 = 233693) (by norm_num)
theorem B3323633 : Blo 2215435 3323633 := bstep (se 2 (by rfl) ⟨1246362, by rfl⟩ : syracuseStep 3323633 = 2492725) B2492725
theorem B2215755 : Blo 2215435 2215755 := bstep (se 1 (by rfl) ⟨1661816, by rfl⟩ : syracuseStep 2215755 = 3323633) B3323633
theorem B2804321 : Blo 2215435 2804321 := bbase (se 2 (by rfl) ⟨1051620, by rfl⟩ : syracuseStep 2804321 = 2103241) (by norm_num)
theorem B7478189 : Blo 2215435 7478189 := bstep (se 3 (by rfl) ⟨1402160, by rfl⟩ : syracuseStep 7478189 = 2804321) B2804321
theorem B4985459 : Blo 2215435 4985459 := bstep (se 1 (by rfl) ⟨3739094, by rfl⟩ : syracuseStep 4985459 = 7478189) B7478189
theorem B3323639 : Blo 2215435 3323639 := bstep (se 1 (by rfl) ⟨2492729, by rfl⟩ : syracuseStep 3323639 = 4985459) B4985459
theorem B2215759 : Blo 2215435 2215759 := bstep (se 1 (by rfl) ⟨1661819, by rfl⟩ : syracuseStep 2215759 = 3323639) B3323639
theorem B3323645 : Blo 2215435 3323645 := bbase (se 3 (by rfl) ⟨623183, by rfl⟩ : syracuseStep 3323645 = 1246367) (by norm_num)
theorem B2215763 : Blo 2215435 2215763 := bstep (se 1 (by rfl) ⟨1661822, by rfl⟩ : syracuseStep 2215763 = 3323645) B3323645
theorem B4985477 : Blo 2215435 4985477 := bbase (se 4 (by rfl) ⟨467388, by rfl⟩ : syracuseStep 4985477 = 934777) (by norm_num)
theorem B3323651 : Blo 2215435 3323651 := bstep (se 1 (by rfl) ⟨2492738, by rfl⟩ : syracuseStep 3323651 = 4985477) B4985477
theorem B2215767 : Blo 2215435 2215767 := bstep (se 1 (by rfl) ⟨1661825, by rfl⟩ : syracuseStep 2215767 = 3323651) B3323651
theorem B4796885 : Blo 2215435 4796885 := bbase (se 7 (by rfl) ⟨56213, by rfl⟩ : syracuseStep 4796885 = 112427) (by norm_num)
theorem B3197923 : Blo 2215435 3197923 := bstep (se 1 (by rfl) ⟨2398442, by rfl⟩ : syracuseStep 3197923 = 4796885) B4796885
theorem B68222357 : Blo 2215435 68222357 := bstep (se 6 (by rfl) ⟨1598961, by rfl⟩ : syracuseStep 68222357 = 3197923) B3197923
theorem B45481571 : Blo 2215435 45481571 := bstep (se 1 (by rfl) ⟨34111178, by rfl⟩ : syracuseStep 45481571 = 68222357) B68222357
theorem B30321047 : Blo 2215435 30321047 := bstep (se 1 (by rfl) ⟨22740785, by rfl⟩ : syracuseStep 30321047 = 45481571) B45481571
theorem B20214031 : Blo 2215435 20214031 := bstep (se 1 (by rfl) ⟨15160523, by rfl⟩ : syracuseStep 20214031 = 30321047) B30321047
theorem B26952041 : Blo 2215435 26952041 := bstep (se 2 (by rfl) ⟨10107015, by rfl⟩ : syracuseStep 26952041 = 20214031) B20214031
theorem B17968027 : Blo 2215435 17968027 := bstep (se 1 (by rfl) ⟨13476020, by rfl⟩ : syracuseStep 17968027 = 26952041) B26952041
theorem B23957369 : Blo 2215435 23957369 := bstep (se 2 (by rfl) ⟨8984013, by rfl⟩ : syracuseStep 23957369 = 17968027) B17968027
theorem B15971579 : Blo 2215435 15971579 := bstep (se 1 (by rfl) ⟨11978684, by rfl⟩ : syracuseStep 15971579 = 23957369) B23957369
theorem B10647719 : Blo 2215435 10647719 := bstep (se 1 (by rfl) ⟨7985789, by rfl⟩ : syracuseStep 10647719 = 15971579) B15971579
theorem B7098479 : Blo 2215435 7098479 := bstep (se 1 (by rfl) ⟨5323859, by rfl⟩ : syracuseStep 7098479 = 10647719) B10647719
theorem B4732319 : Blo 2215435 4732319 := bstep (se 1 (by rfl) ⟨3549239, by rfl⟩ : syracuseStep 4732319 = 7098479) B7098479
theorem B3154879 : Blo 2215435 3154879 := bstep (se 1 (by rfl) ⟨2366159, by rfl⟩ : syracuseStep 3154879 = 4732319) B4732319
theorem B4206505 : Blo 2215435 4206505 := bstep (se 2 (by rfl) ⟨1577439, by rfl⟩ : syracuseStep 4206505 = 3154879) B3154879
theorem B5608673 : Blo 2215435 5608673 := bstep (se 2 (by rfl) ⟨2103252, by rfl⟩ : syracuseStep 5608673 = 4206505) B4206505
theorem B3739115 : Blo 2215435 3739115 := bstep (se 1 (by rfl) ⟨2804336, by rfl⟩ : syracuseStep 3739115 = 5608673) B5608673
theorem B2492743 : Blo 2215435 2492743 := bstep (se 1 (by rfl) ⟨1869557, by rfl⟩ : syracuseStep 2492743 = 3739115) B3739115
theorem B3323657 : Blo 2215435 3323657 := bstep (se 2 (by rfl) ⟨1246371, by rfl⟩ : syracuseStep 3323657 = 2492743) B2492743
theorem B2215771 : Blo 2215435 2215771 := bstep (se 1 (by rfl) ⟨1661828, by rfl⟩ : syracuseStep 2215771 = 3323657) B3323657
theorem B11217365 : Blo 2215435 11217365 := bbase (se 7 (by rfl) ⟨131453, by rfl⟩ : syracuseStep 11217365 = 262907) (by norm_num)
theorem B7478243 : Blo 2215435 7478243 := bstep (se 1 (by rfl) ⟨5608682, by rfl⟩ : syracuseStep 7478243 = 11217365) B11217365
theorem B4985495 : Blo 2215435 4985495 := bstep (se 1 (by rfl) ⟨3739121, by rfl⟩ : syracuseStep 4985495 = 7478243) B7478243
theorem B3323663 : Blo 2215435 3323663 := bstep (se 1 (by rfl) ⟨2492747, by rfl⟩ : syracuseStep 3323663 = 4985495) B4985495
theorem B2215775 : Blo 2215435 2215775 := bstep (se 1 (by rfl) ⟨1661831, by rfl⟩ : syracuseStep 2215775 = 3323663) B3323663
theorem B3323669 : Blo 2215435 3323669 := bbase (se 6 (by rfl) ⟨77898, by rfl⟩ : syracuseStep 3323669 = 155797) (by norm_num)
theorem B2215779 : Blo 2215435 2215779 := bstep (se 1 (by rfl) ⟨1661834, by rfl⟩ : syracuseStep 2215779 = 3323669) B3323669
theorem B4553317 : Blo 2215435 4553317 := bbase (se 4 (by rfl) ⟨426873, by rfl⟩ : syracuseStep 4553317 = 853747) (by norm_num)
theorem B24284357 : Blo 2215435 24284357 := bstep (se 4 (by rfl) ⟨2276658, by rfl⟩ : syracuseStep 24284357 = 4553317) B4553317
theorem B16189571 : Blo 2215435 16189571 := bstep (se 1 (by rfl) ⟨12142178, by rfl⟩ : syracuseStep 16189571 = 24284357) B24284357
theorem B10793047 : Blo 2215435 10793047 := bstep (se 1 (by rfl) ⟨8094785, by rfl⟩ : syracuseStep 10793047 = 16189571) B16189571
theorem B14390729 : Blo 2215435 14390729 := bstep (se 2 (by rfl) ⟨5396523, by rfl⟩ : syracuseStep 14390729 = 10793047) B10793047
theorem B9593819 : Blo 2215435 9593819 := bstep (se 1 (by rfl) ⟨7195364, by rfl⟩ : syracuseStep 9593819 = 14390729) B14390729
theorem B6395879 : Blo 2215435 6395879 := bstep (se 1 (by rfl) ⟨4796909, by rfl⟩ : syracuseStep 6395879 = 9593819) B9593819
theorem B17055677 : Blo 2215435 17055677 := bstep (se 3 (by rfl) ⟨3197939, by rfl⟩ : syracuseStep 17055677 = 6395879) B6395879
theorem B11370451 : Blo 2215435 11370451 := bstep (se 1 (by rfl) ⟨8527838, by rfl⟩ : syracuseStep 11370451 = 17055677) B17055677
theorem B15160601 : Blo 2215435 15160601 := bstep (se 2 (by rfl) ⟨5685225, by rfl⟩ : syracuseStep 15160601 = 11370451) B11370451
theorem B10107067 : Blo 2215435 10107067 := bstep (se 1 (by rfl) ⟨7580300, by rfl⟩ : syracuseStep 10107067 = 15160601) B15160601
theorem B13476089 : Blo 2215435 13476089 := bstep (se 2 (by rfl) ⟨5053533, by rfl⟩ : syracuseStep 13476089 = 10107067) B10107067
theorem B35936237 : Blo 2215435 35936237 := bstep (se 3 (by rfl) ⟨6738044, by rfl⟩ : syracuseStep 35936237 = 13476089) B13476089
theorem B95829965 : Blo 2215435 95829965 := bstep (se 3 (by rfl) ⟨17968118, by rfl⟩ : syracuseStep 95829965 = 35936237) B35936237
theorem B63886643 : Blo 2215435 63886643 := bstep (se 1 (by rfl) ⟨47914982, by rfl⟩ : syracuseStep 63886643 = 95829965) B95829965
theorem B42591095 : Blo 2215435 42591095 := bstep (se 1 (by rfl) ⟨31943321, by rfl⟩ : syracuseStep 42591095 = 63886643) B63886643
theorem B28394063 : Blo 2215435 28394063 := bstep (se 1 (by rfl) ⟨21295547, by rfl⟩ : syracuseStep 28394063 = 42591095) B42591095
theorem B18929375 : Blo 2215435 18929375 := bstep (se 1 (by rfl) ⟨14197031, by rfl⟩ : syracuseStep 18929375 = 28394063) B28394063
theorem B12619583 : Blo 2215435 12619583 := bstep (se 1 (by rfl) ⟨9464687, by rfl⟩ : syracuseStep 12619583 = 18929375) B18929375
theorem B8413055 : Blo 2215435 8413055 := bstep (se 1 (by rfl) ⟨6309791, by rfl⟩ : syracuseStep 8413055 = 12619583) B12619583
theorem B5608703 : Blo 2215435 5608703 := bstep (se 1 (by rfl) ⟨4206527, by rfl⟩ : syracuseStep 5608703 = 8413055) B8413055
theorem B3739135 : Blo 2215435 3739135 := bstep (se 1 (by rfl) ⟨2804351, by rfl⟩ : syracuseStep 3739135 = 5608703) B5608703
theorem B4985513 : Blo 2215435 4985513 := bstep (se 2 (by rfl) ⟨1869567, by rfl⟩ : syracuseStep 4985513 = 3739135) B3739135
theorem B3323675 : Blo 2215435 3323675 := bstep (se 1 (by rfl) ⟨2492756, by rfl⟩ : syracuseStep 3323675 = 4985513) B4985513
theorem B2215783 : Blo 2215435 2215783 := bstep (se 1 (by rfl) ⟨1661837, by rfl⟩ : syracuseStep 2215783 = 3323675) B3323675
theorem B2492761 : Blo 2215435 2492761 := bbase (se 2 (by rfl) ⟨934785, by rfl⟩ : syracuseStep 2492761 = 1869571) (by norm_num)
theorem B3323681 : Blo 2215435 3323681 := bstep (se 2 (by rfl) ⟨1246380, by rfl⟩ : syracuseStep 3323681 = 2492761) B2492761
theorem B2215787 : Blo 2215435 2215787 := bstep (se 1 (by rfl) ⟨1661840, by rfl⟩ : syracuseStep 2215787 = 3323681) B3323681
theorem B7985861 : Blo 2215435 7985861 := bbase (se 4 (by rfl) ⟨748674, by rfl⟩ : syracuseStep 7985861 = 1497349) (by norm_num)
theorem B5323907 : Blo 2215435 5323907 := bstep (se 1 (by rfl) ⟨3992930, by rfl⟩ : syracuseStep 5323907 = 7985861) B7985861
theorem B3549271 : Blo 2215435 3549271 := bstep (se 1 (by rfl) ⟨2661953, by rfl⟩ : syracuseStep 3549271 = 5323907) B5323907
theorem B4732361 : Blo 2215435 4732361 := bstep (se 2 (by rfl) ⟨1774635, by rfl⟩ : syracuseStep 4732361 = 3549271) B3549271
theorem B3154907 : Blo 2215435 3154907 := bstep (se 1 (by rfl) ⟨2366180, by rfl⟩ : syracuseStep 3154907 = 4732361) B4732361
theorem B8413085 : Blo 2215435 8413085 := bstep (se 3 (by rfl) ⟨1577453, by rfl⟩ : syracuseStep 8413085 = 3154907) B3154907
theorem B5608723 : Blo 2215435 5608723 := bstep (se 1 (by rfl) ⟨4206542, by rfl⟩ : syracuseStep 5608723 = 8413085) B8413085
theorem B7478297 : Blo 2215435 7478297 := bstep (se 2 (by rfl) ⟨2804361, by rfl⟩ : syracuseStep 7478297 = 5608723) B5608723
theorem B4985531 : Blo 2215435 4985531 := bstep (se 1 (by rfl) ⟨3739148, by rfl⟩ : syracuseStep 4985531 = 7478297) B7478297
theorem B3323687 : Blo 2215435 3323687 := bstep (se 1 (by rfl) ⟨2492765, by rfl⟩ : syracuseStep 3323687 = 4985531) B4985531
theorem B2215791 : Blo 2215435 2215791 := bstep (se 1 (by rfl) ⟨1661843, by rfl⟩ : syracuseStep 2215791 = 3323687) B3323687
theorem B3323693 : Blo 2215435 3323693 := bbase (se 3 (by rfl) ⟨623192, by rfl⟩ : syracuseStep 3323693 = 1246385) (by norm_num)
theorem B2215795 : Blo 2215435 2215795 := bstep (se 1 (by rfl) ⟨1661846, by rfl⟩ : syracuseStep 2215795 = 3323693) B3323693
theorem B4985549 : Blo 2215435 4985549 := bbase (se 3 (by rfl) ⟨934790, by rfl⟩ : syracuseStep 4985549 = 1869581) (by norm_num)
theorem B3323699 : Blo 2215435 3323699 := bstep (se 1 (by rfl) ⟨2492774, by rfl⟩ : syracuseStep 3323699 = 4985549) B4985549
theorem B2215799 : Blo 2215435 2215799 := bstep (se 1 (by rfl) ⟨1661849, by rfl⟩ : syracuseStep 2215799 = 3323699) B3323699
theorem B2804377 : Blo 2215435 2804377 := bbase (se 2 (by rfl) ⟨1051641, by rfl⟩ : syracuseStep 2804377 = 2103283) (by norm_num)
theorem B3739169 : Blo 2215435 3739169 := bstep (se 2 (by rfl) ⟨1402188, by rfl⟩ : syracuseStep 3739169 = 2804377) B2804377
theorem B2492779 : Blo 2215435 2492779 := bstep (se 1 (by rfl) ⟨1869584, by rfl⟩ : syracuseStep 2492779 = 3739169) B3739169
theorem B3323705 : Blo 2215435 3323705 := bstep (se 2 (by rfl) ⟨1246389, by rfl⟩ : syracuseStep 3323705 = 2492779) B2492779
theorem B2215803 : Blo 2215435 2215803 := bstep (se 1 (by rfl) ⟨1661852, by rfl⟩ : syracuseStep 2215803 = 3323705) B3323705
theorem B9464789 : Blo 2215435 9464789 := bbase (se 7 (by rfl) ⟨110915, by rfl⟩ : syracuseStep 9464789 = 221831) (by norm_num)
theorem B25239437 : Blo 2215435 25239437 := bstep (se 3 (by rfl) ⟨4732394, by rfl⟩ : syracuseStep 25239437 = 9464789) B9464789
theorem B16826291 : Blo 2215435 16826291 := bstep (se 1 (by rfl) ⟨12619718, by rfl⟩ : syracuseStep 16826291 = 25239437) B25239437
theorem B11217527 : Blo 2215435 11217527 := bstep (se 1 (by rfl) ⟨8413145, by rfl⟩ : syracuseStep 11217527 = 16826291) B16826291
theorem B7478351 : Blo 2215435 7478351 := bstep (se 1 (by rfl) ⟨5608763, by rfl⟩ : syracuseStep 7478351 = 11217527) B11217527
theorem B4985567 : Blo 2215435 4985567 := bstep (se 1 (by rfl) ⟨3739175, by rfl⟩ : syracuseStep 4985567 = 7478351) B7478351
theorem B3323711 : Blo 2215435 3323711 := bstep (se 1 (by rfl) ⟨2492783, by rfl⟩ : syracuseStep 3323711 = 4985567) B4985567
theorem B2215807 : Blo 2215435 2215807 := bstep (se 1 (by rfl) ⟨1661855, by rfl⟩ : syracuseStep 2215807 = 3323711) B3323711
theorem B3323717 : Blo 2215435 3323717 := bbase (se 4 (by rfl) ⟨311598, by rfl⟩ : syracuseStep 3323717 = 623197) (by norm_num)
theorem B2215811 : Blo 2215435 2215811 := bstep (se 1 (by rfl) ⟨1661858, by rfl⟩ : syracuseStep 2215811 = 3323717) B3323717
theorem B3739189 : Blo 2215435 3739189 := bbase (se 5 (by rfl) ⟨175274, by rfl⟩ : syracuseStep 3739189 = 350549) (by norm_num)
theorem B4985585 : Blo 2215435 4985585 := bstep (se 2 (by rfl) ⟨1869594, by rfl⟩ : syracuseStep 4985585 = 3739189) B3739189
theorem B3323723 : Blo 2215435 3323723 := bstep (se 1 (by rfl) ⟨2492792, by rfl⟩ : syracuseStep 3323723 = 4985585) B4985585
theorem B2215815 : Blo 2215435 2215815 := bstep (se 1 (by rfl) ⟨1661861, by rfl⟩ : syracuseStep 2215815 = 3323723) B3323723
theorem B2492797 : Blo 2215435 2492797 := bbase (se 3 (by rfl) ⟨467399, by rfl⟩ : syracuseStep 2492797 = 934799) (by norm_num)
theorem B3323729 : Blo 2215435 3323729 := bstep (se 2 (by rfl) ⟨1246398, by rfl⟩ : syracuseStep 3323729 = 2492797) B2492797
theorem B2215819 : Blo 2215435 2215819 := bstep (se 1 (by rfl) ⟨1661864, by rfl⟩ : syracuseStep 2215819 = 3323729) B3323729
theorem B7478405 : Blo 2215435 7478405 := bbase (se 4 (by rfl) ⟨701100, by rfl⟩ : syracuseStep 7478405 = 1402201) (by norm_num)
theorem B4985603 : Blo 2215435 4985603 := bstep (se 1 (by rfl) ⟨3739202, by rfl⟩ : syracuseStep 4985603 = 7478405) B7478405
theorem B3323735 : Blo 2215435 3323735 := bstep (se 1 (by rfl) ⟨2492801, by rfl⟩ : syracuseStep 3323735 = 4985603) B4985603
theorem B2215823 : Blo 2215435 2215823 := bstep (se 1 (by rfl) ⟨1661867, by rfl⟩ : syracuseStep 2215823 = 3323735) B3323735
theorem B3323741 : Blo 2215435 3323741 := bbase (se 3 (by rfl) ⟨623201, by rfl⟩ : syracuseStep 3323741 = 1246403) (by norm_num)
theorem B2215827 : Blo 2215435 2215827 := bstep (se 1 (by rfl) ⟨1661870, by rfl⟩ : syracuseStep 2215827 = 3323741) B3323741
theorem B4985621 : Blo 2215435 4985621 := bbase (se 6 (by rfl) ⟨116850, by rfl⟩ : syracuseStep 4985621 = 233701) (by norm_num)
theorem B3323747 : Blo 2215435 3323747 := bstep (se 1 (by rfl) ⟨2492810, by rfl⟩ : syracuseStep 3323747 = 4985621) B4985621
theorem B2215831 : Blo 2215435 2215831 := bstep (se 1 (by rfl) ⟨1661873, by rfl⟩ : syracuseStep 2215831 = 3323747) B3323747
theorem B8413253 : Blo 2215435 8413253 := bbase (se 4 (by rfl) ⟨788742, by rfl⟩ : syracuseStep 8413253 = 1577485) (by norm_num)
theorem B5608835 : Blo 2215435 5608835 := bstep (se 1 (by rfl) ⟨4206626, by rfl⟩ : syracuseStep 5608835 = 8413253) B8413253
theorem B3739223 : Blo 2215435 3739223 := bstep (se 1 (by rfl) ⟨2804417, by rfl⟩ : syracuseStep 3739223 = 5608835) B5608835
theorem B2492815 : Blo 2215435 2492815 := bstep (se 1 (by rfl) ⟨1869611, by rfl⟩ : syracuseStep 2492815 = 3739223) B3739223
theorem B3323753 : Blo 2215435 3323753 := bstep (se 2 (by rfl) ⟨1246407, by rfl⟩ : syracuseStep 3323753 = 2492815) B2492815
theorem B2215835 : Blo 2215435 2215835 := bstep (se 1 (by rfl) ⟨1661876, by rfl⟩ : syracuseStep 2215835 = 3323753) B3323753
theorem B27320597 : Blo 2215435 27320597 := bbase (se 6 (by rfl) ⟨640326, by rfl⟩ : syracuseStep 27320597 = 1280653) (by norm_num)
theorem B18213731 : Blo 2215435 18213731 := bstep (se 1 (by rfl) ⟨13660298, by rfl⟩ : syracuseStep 18213731 = 27320597) B27320597
theorem B12142487 : Blo 2215435 12142487 := bstep (se 1 (by rfl) ⟨9106865, by rfl⟩ : syracuseStep 12142487 = 18213731) B18213731
theorem B8094991 : Blo 2215435 8094991 := bstep (se 1 (by rfl) ⟨6071243, by rfl⟩ : syracuseStep 8094991 = 12142487) B12142487
theorem B10793321 : Blo 2215435 10793321 := bstep (se 2 (by rfl) ⟨4047495, by rfl⟩ : syracuseStep 10793321 = 8094991) B8094991
theorem B7195547 : Blo 2215435 7195547 := bstep (se 1 (by rfl) ⟨5396660, by rfl⟩ : syracuseStep 7195547 = 10793321) B10793321
theorem B4797031 : Blo 2215435 4797031 := bstep (se 1 (by rfl) ⟨3597773, by rfl⟩ : syracuseStep 4797031 = 7195547) B7195547
theorem B6396041 : Blo 2215435 6396041 := bstep (se 2 (by rfl) ⟨2398515, by rfl⟩ : syracuseStep 6396041 = 4797031) B4797031
theorem B17056109 : Blo 2215435 17056109 := bstep (se 3 (by rfl) ⟨3198020, by rfl⟩ : syracuseStep 17056109 = 6396041) B6396041
theorem B45482957 : Blo 2215435 45482957 := bstep (se 3 (by rfl) ⟨8528054, by rfl⟩ : syracuseStep 45482957 = 17056109) B17056109
theorem B30321971 : Blo 2215435 30321971 := bstep (se 1 (by rfl) ⟨22741478, by rfl⟩ : syracuseStep 30321971 = 45482957) B45482957
theorem B20214647 : Blo 2215435 20214647 := bstep (se 1 (by rfl) ⟨15160985, by rfl⟩ : syracuseStep 20214647 = 30321971) B30321971
theorem B13476431 : Blo 2215435 13476431 := bstep (se 1 (by rfl) ⟨10107323, by rfl⟩ : syracuseStep 13476431 = 20214647) B20214647
theorem B8984287 : Blo 2215435 8984287 := bstep (se 1 (by rfl) ⟨6738215, by rfl⟩ : syracuseStep 8984287 = 13476431) B13476431
theorem B11979049 : Blo 2215435 11979049 := bstep (se 2 (by rfl) ⟨4492143, by rfl⟩ : syracuseStep 11979049 = 8984287) B8984287
theorem B15972065 : Blo 2215435 15972065 := bstep (se 2 (by rfl) ⟨5989524, by rfl⟩ : syracuseStep 15972065 = 11979049) B11979049
theorem B10648043 : Blo 2215435 10648043 := bstep (se 1 (by rfl) ⟨7986032, by rfl⟩ : syracuseStep 10648043 = 15972065) B15972065
theorem B7098695 : Blo 2215435 7098695 := bstep (se 1 (by rfl) ⟨5324021, by rfl⟩ : syracuseStep 7098695 = 10648043) B10648043
theorem B4732463 : Blo 2215435 4732463 := bstep (se 1 (by rfl) ⟨3549347, by rfl⟩ : syracuseStep 4732463 = 7098695) B7098695
theorem B12619901 : Blo 2215435 12619901 := bstep (se 3 (by rfl) ⟨2366231, by rfl⟩ : syracuseStep 12619901 = 4732463) B4732463
theorem B8413267 : Blo 2215435 8413267 := bstep (se 1 (by rfl) ⟨6309950, by rfl⟩ : syracuseStep 8413267 = 12619901) B12619901
theorem B11217689 : Blo 2215435 11217689 := bstep (se 2 (by rfl) ⟨4206633, by rfl⟩ : syracuseStep 11217689 = 8413267) B8413267
theorem B7478459 : Blo 2215435 7478459 := bstep (se 1 (by rfl) ⟨5608844, by rfl⟩ : syracuseStep 7478459 = 11217689) B11217689
theorem B4985639 : Blo 2215435 4985639 := bstep (se 1 (by rfl) ⟨3739229, by rfl⟩ : syracuseStep 4985639 = 7478459) B7478459
theorem B3323759 : Blo 2215435 3323759 := bstep (se 1 (by rfl) ⟨2492819, by rfl⟩ : syracuseStep 3323759 = 4985639) B4985639
theorem B2215839 : Blo 2215435 2215839 := bstep (se 1 (by rfl) ⟨1661879, by rfl⟩ : syracuseStep 2215839 = 3323759) B3323759
theorem B3323765 : Blo 2215435 3323765 := bbase (se 5 (by rfl) ⟨155801, by rfl⟩ : syracuseStep 3323765 = 311603) (by norm_num)
theorem B2215843 : Blo 2215435 2215843 := bstep (se 1 (by rfl) ⟨1661882, by rfl⟩ : syracuseStep 2215843 = 3323765) B3323765
theorem B2662021 : Blo 2215435 2662021 := bbase (se 4 (by rfl) ⟨249564, by rfl⟩ : syracuseStep 2662021 = 499129) (by norm_num)
theorem B3549361 : Blo 2215435 3549361 := bstep (se 2 (by rfl) ⟨1331010, by rfl⟩ : syracuseStep 3549361 = 2662021) B2662021
theorem B4732481 : Blo 2215435 4732481 := bstep (se 2 (by rfl) ⟨1774680, by rfl⟩ : syracuseStep 4732481 = 3549361) B3549361
theorem B3154987 : Blo 2215435 3154987 := bstep (se 1 (by rfl) ⟨2366240, by rfl⟩ : syracuseStep 3154987 = 4732481) B4732481
theorem B4206649 : Blo 2215435 4206649 := bstep (se 2 (by rfl) ⟨1577493, by rfl⟩ : syracuseStep 4206649 = 3154987) B3154987
theorem B5608865 : Blo 2215435 5608865 := bstep (se 2 (by rfl) ⟨2103324, by rfl⟩ : syracuseStep 5608865 = 4206649) B4206649
theorem B3739243 : Blo 2215435 3739243 := bstep (se 1 (by rfl) ⟨2804432, by rfl⟩ : syracuseStep 3739243 = 5608865) B5608865
theorem B4985657 : Blo 2215435 4985657 := bstep (se 2 (by rfl) ⟨1869621, by rfl⟩ : syracuseStep 4985657 = 3739243) B3739243
theorem B3323771 : Blo 2215435 3323771 := bstep (se 1 (by rfl) ⟨2492828, by rfl⟩ : syracuseStep 3323771 = 4985657) B4985657
theorem B2215847 : Blo 2215435 2215847 := bstep (se 1 (by rfl) ⟨1661885, by rfl⟩ : syracuseStep 2215847 = 3323771) B3323771
theorem B2492833 : Blo 2215435 2492833 := bbase (se 2 (by rfl) ⟨934812, by rfl⟩ : syracuseStep 2492833 = 1869625) (by norm_num)
theorem B3323777 : Blo 2215435 3323777 := bstep (se 2 (by rfl) ⟨1246416, by rfl⟩ : syracuseStep 3323777 = 2492833) B2492833
theorem B2215851 : Blo 2215435 2215851 := bstep (se 1 (by rfl) ⟨1661888, by rfl⟩ : syracuseStep 2215851 = 3323777) B3323777
theorem B5608885 : Blo 2215435 5608885 := bbase (se 5 (by rfl) ⟨262916, by rfl⟩ : syracuseStep 5608885 = 525833) (by norm_num)
theorem B7478513 : Blo 2215435 7478513 := bstep (se 2 (by rfl) ⟨2804442, by rfl⟩ : syracuseStep 7478513 = 5608885) B5608885
theorem B4985675 : Blo 2215435 4985675 := bstep (se 1 (by rfl) ⟨3739256, by rfl⟩ : syracuseStep 4985675 = 7478513) B7478513
theorem B3323783 : Blo 2215435 3323783 := bstep (se 1 (by rfl) ⟨2492837, by rfl⟩ : syracuseStep 3323783 = 4985675) B4985675
theorem B2215855 : Blo 2215435 2215855 := bstep (se 1 (by rfl) ⟨1661891, by rfl⟩ : syracuseStep 2215855 = 3323783) B3323783
theorem B3323789 : Blo 2215435 3323789 := bbase (se 3 (by rfl) ⟨623210, by rfl⟩ : syracuseStep 3323789 = 1246421) (by norm_num)
theorem B2215859 : Blo 2215435 2215859 := bstep (se 1 (by rfl) ⟨1661894, by rfl⟩ : syracuseStep 2215859 = 3323789) B3323789
theorem B4985693 : Blo 2215435 4985693 := bbase (se 3 (by rfl) ⟨934817, by rfl⟩ : syracuseStep 4985693 = 1869635) (by norm_num)
theorem B3323795 : Blo 2215435 3323795 := bstep (se 1 (by rfl) ⟨2492846, by rfl⟩ : syracuseStep 3323795 = 4985693) B4985693
theorem B2215863 : Blo 2215435 2215863 := bstep (se 1 (by rfl) ⟨1661897, by rfl⟩ : syracuseStep 2215863 = 3323795) B3323795
theorem B3739277 : Blo 2215435 3739277 := bbase (se 3 (by rfl) ⟨701114, by rfl⟩ : syracuseStep 3739277 = 1402229) (by norm_num)
theorem B2492851 : Blo 2215435 2492851 := bstep (se 1 (by rfl) ⟨1869638, by rfl⟩ : syracuseStep 2492851 = 3739277) B3739277
theorem B3323801 : Blo 2215435 3323801 := bstep (se 2 (by rfl) ⟨1246425, by rfl⟩ : syracuseStep 3323801 = 2492851) B2492851
theorem B2215867 : Blo 2215435 2215867 := bstep (se 1 (by rfl) ⟨1661900, by rfl⟩ : syracuseStep 2215867 = 3323801) B3323801
theorem B2662049 : Blo 2215435 2662049 := bbase (se 2 (by rfl) ⟨998268, by rfl⟩ : syracuseStep 2662049 = 1996537) (by norm_num)
theorem B7098797 : Blo 2215435 7098797 := bstep (se 3 (by rfl) ⟨1331024, by rfl⟩ : syracuseStep 7098797 = 2662049) B2662049
theorem B18930125 : Blo 2215435 18930125 := bstep (se 3 (by rfl) ⟨3549398, by rfl⟩ : syracuseStep 18930125 = 7098797) B7098797
theorem B12620083 : Blo 2215435 12620083 := bstep (se 1 (by rfl) ⟨9465062, by rfl⟩ : syracuseStep 12620083 = 18930125) B18930125
theorem B16826777 : Blo 2215435 16826777 := bstep (se 2 (by rfl) ⟨6310041, by rfl⟩ : syracuseStep 16826777 = 12620083) B12620083
theorem B11217851 : Blo 2215435 11217851 := bstep (se 1 (by rfl) ⟨8413388, by rfl⟩ : syracuseStep 11217851 = 16826777) B16826777
theorem B7478567 : Blo 2215435 7478567 := bstep (se 1 (by rfl) ⟨5608925, by rfl⟩ : syracuseStep 7478567 = 11217851) B11217851
theorem B4985711 : Blo 2215435 4985711 := bstep (se 1 (by rfl) ⟨3739283, by rfl⟩ : syracuseStep 4985711 = 7478567) B7478567
theorem B3323807 : Blo 2215435 3323807 := bstep (se 1 (by rfl) ⟨2492855, by rfl⟩ : syracuseStep 3323807 = 4985711) B4985711
theorem B2215871 : Blo 2215435 2215871 := bstep (se 1 (by rfl) ⟨1661903, by rfl⟩ : syracuseStep 2215871 = 3323807) B3323807
theorem B3323813 : Blo 2215435 3323813 := bbase (se 4 (by rfl) ⟨311607, by rfl⟩ : syracuseStep 3323813 = 623215) (by norm_num)
theorem B2215875 : Blo 2215435 2215875 := bstep (se 1 (by rfl) ⟨1661906, by rfl⟩ : syracuseStep 2215875 = 3323813) B3323813
theorem B2804473 : Blo 2215435 2804473 := bbase (se 2 (by rfl) ⟨1051677, by rfl⟩ : syracuseStep 2804473 = 2103355) (by norm_num)
theorem B3739297 : Blo 2215435 3739297 := bstep (se 2 (by rfl) ⟨1402236, by rfl⟩ : syracuseStep 3739297 = 2804473) B2804473
theorem B4985729 : Blo 2215435 4985729 := bstep (se 2 (by rfl) ⟨1869648, by rfl⟩ : syracuseStep 4985729 = 3739297) B3739297
theorem B3323819 : Blo 2215435 3323819 := bstep (se 1 (by rfl) ⟨2492864, by rfl⟩ : syracuseStep 3323819 = 4985729) B4985729
theorem B2215879 : Blo 2215435 2215879 := bstep (se 1 (by rfl) ⟨1661909, by rfl⟩ : syracuseStep 2215879 = 3323819) B3323819
theorem B2492869 : Blo 2215435 2492869 := bbase (se 4 (by rfl) ⟨233706, by rfl⟩ : syracuseStep 2492869 = 467413) (by norm_num)
theorem B3323825 : Blo 2215435 3323825 := bstep (se 2 (by rfl) ⟨1246434, by rfl⟩ : syracuseStep 3323825 = 2492869) B2492869
theorem B2215883 : Blo 2215435 2215883 := bstep (se 1 (by rfl) ⟨1661912, by rfl⟩ : syracuseStep 2215883 = 3323825) B3323825
theorem B4206725 : Blo 2215435 4206725 := bbase (se 4 (by rfl) ⟨394380, by rfl⟩ : syracuseStep 4206725 = 788761) (by norm_num)
theorem B2804483 : Blo 2215435 2804483 := bstep (se 1 (by rfl) ⟨2103362, by rfl⟩ : syracuseStep 2804483 = 4206725) B4206725
theorem B7478621 : Blo 2215435 7478621 := bstep (se 3 (by rfl) ⟨1402241, by rfl⟩ : syracuseStep 7478621 = 2804483) B2804483
theorem B4985747 : Blo 2215435 4985747 := bstep (se 1 (by rfl) ⟨3739310, by rfl⟩ : syracuseStep 4985747 = 7478621) B7478621
theorem B3323831 : Blo 2215435 3323831 := bstep (se 1 (by rfl) ⟨2492873, by rfl⟩ : syracuseStep 3323831 = 4985747) B4985747
theorem B2215887 : Blo 2215435 2215887 := bstep (se 1 (by rfl) ⟨1661915, by rfl⟩ : syracuseStep 2215887 = 3323831) B3323831
theorem B3323837 : Blo 2215435 3323837 := bbase (se 3 (by rfl) ⟨623219, by rfl⟩ : syracuseStep 3323837 = 1246439) (by norm_num)
theorem B2215891 : Blo 2215435 2215891 := bstep (se 1 (by rfl) ⟨1661918, by rfl⟩ : syracuseStep 2215891 = 3323837) B3323837
theorem B4985765 : Blo 2215435 4985765 := bbase (se 4 (by rfl) ⟨467415, by rfl⟩ : syracuseStep 4985765 = 934831) (by norm_num)
theorem B3323843 : Blo 2215435 3323843 := bstep (se 1 (by rfl) ⟨2492882, by rfl⟩ : syracuseStep 3323843 = 4985765) B4985765
theorem B2215895 : Blo 2215435 2215895 := bstep (se 1 (by rfl) ⟨1661921, by rfl⟩ : syracuseStep 2215895 = 3323843) B3323843
theorem B5608997 : Blo 2215435 5608997 := bbase (se 4 (by rfl) ⟨525843, by rfl⟩ : syracuseStep 5608997 = 1051687) (by norm_num)
theorem B3739331 : Blo 2215435 3739331 := bstep (se 1 (by rfl) ⟨2804498, by rfl⟩ : syracuseStep 3739331 = 5608997) B5608997
theorem B2492887 : Blo 2215435 2492887 := bstep (se 1 (by rfl) ⟨1869665, by rfl⟩ : syracuseStep 2492887 = 3739331) B3739331
theorem B3323849 : Blo 2215435 3323849 := bstep (se 2 (by rfl) ⟨1246443, by rfl⟩ : syracuseStep 3323849 = 2492887) B2492887
theorem B2215899 : Blo 2215435 2215899 := bstep (se 1 (by rfl) ⟨1661924, by rfl⟩ : syracuseStep 2215899 = 3323849) B3323849
theorem B6310133 : Blo 2215435 6310133 := bbase (se 5 (by rfl) ⟨295787, by rfl⟩ : syracuseStep 6310133 = 591575) (by norm_num)
theorem B4206755 : Blo 2215435 4206755 := bstep (se 1 (by rfl) ⟨3155066, by rfl⟩ : syracuseStep 4206755 = 6310133) B6310133
theorem B11218013 : Blo 2215435 11218013 := bstep (se 3 (by rfl) ⟨2103377, by rfl⟩ : syracuseStep 11218013 = 4206755) B4206755
theorem B7478675 : Blo 2215435 7478675 := bstep (se 1 (by rfl) ⟨5609006, by rfl⟩ : syracuseStep 7478675 = 11218013) B11218013
theorem B4985783 : Blo 2215435 4985783 := bstep (se 1 (by rfl) ⟨3739337, by rfl⟩ : syracuseStep 4985783 = 7478675) B7478675
theorem B3323855 : Blo 2215435 3323855 := bstep (se 1 (by rfl) ⟨2492891, by rfl⟩ : syracuseStep 3323855 = 4985783) B4985783
theorem B2215903 : Blo 2215435 2215903 := bstep (se 1 (by rfl) ⟨1661927, by rfl⟩ : syracuseStep 2215903 = 3323855) B3323855
theorem B3323861 : Blo 2215435 3323861 := bbase (se 7 (by rfl) ⟨38951, by rfl⟩ : syracuseStep 3323861 = 77903) (by norm_num)
theorem B2215907 : Blo 2215435 2215907 := bstep (se 1 (by rfl) ⟨1661930, by rfl⟩ : syracuseStep 2215907 = 3323861) B3323861
theorem B8413541 : Blo 2215435 8413541 := bbase (se 4 (by rfl) ⟨788769, by rfl⟩ : syracuseStep 8413541 = 1577539) (by norm_num)
theorem B5609027 : Blo 2215435 5609027 := bstep (se 1 (by rfl) ⟨4206770, by rfl⟩ : syracuseStep 5609027 = 8413541) B8413541
theorem B3739351 : Blo 2215435 3739351 := bstep (se 1 (by rfl) ⟨2804513, by rfl⟩ : syracuseStep 3739351 = 5609027) B5609027
theorem B4985801 : Blo 2215435 4985801 := bstep (se 2 (by rfl) ⟨1869675, by rfl⟩ : syracuseStep 4985801 = 3739351) B3739351
theorem B3323867 : Blo 2215435 3323867 := bstep (se 1 (by rfl) ⟨2492900, by rfl⟩ : syracuseStep 3323867 = 4985801) B4985801
theorem B2215911 : Blo 2215435 2215911 := bstep (se 1 (by rfl) ⟨1661933, by rfl⟩ : syracuseStep 2215911 = 3323867) B3323867
theorem B2492905 : Blo 2215435 2492905 := bbase (se 2 (by rfl) ⟨934839, by rfl⟩ : syracuseStep 2492905 = 1869679) (by norm_num)
theorem B3323873 : Blo 2215435 3323873 := bstep (se 2 (by rfl) ⟨1246452, by rfl⟩ : syracuseStep 3323873 = 2492905) B2492905
theorem B2215915 : Blo 2215435 2215915 := bstep (se 1 (by rfl) ⟨1661936, by rfl⟩ : syracuseStep 2215915 = 3323873) B3323873
theorem B2366317 : Blo 2215435 2366317 := bbase (se 3 (by rfl) ⟨443684, by rfl⟩ : syracuseStep 2366317 = 887369) (by norm_num)
theorem B12620357 : Blo 2215435 12620357 := bstep (se 4 (by rfl) ⟨1183158, by rfl⟩ : syracuseStep 12620357 = 2366317) B2366317
theorem B8413571 : Blo 2215435 8413571 := bstep (se 1 (by rfl) ⟨6310178, by rfl⟩ : syracuseStep 8413571 = 12620357) B12620357
theorem B5609047 : Blo 2215435 5609047 := bstep (se 1 (by rfl) ⟨4206785, by rfl⟩ : syracuseStep 5609047 = 8413571) B8413571
theorem B7478729 : Blo 2215435 7478729 := bstep (se 2 (by rfl) ⟨2804523, by rfl⟩ : syracuseStep 7478729 = 5609047) B5609047
theorem B4985819 : Blo 2215435 4985819 := bstep (se 1 (by rfl) ⟨3739364, by rfl⟩ : syracuseStep 4985819 = 7478729) B7478729
theorem B3323879 : Blo 2215435 3323879 := bstep (se 1 (by rfl) ⟨2492909, by rfl⟩ : syracuseStep 3323879 = 4985819) B4985819
theorem B2215919 : Blo 2215435 2215919 := bstep (se 1 (by rfl) ⟨1661939, by rfl⟩ : syracuseStep 2215919 = 3323879) B3323879
theorem B3323885 : Blo 2215435 3323885 := bbase (se 3 (by rfl) ⟨623228, by rfl⟩ : syracuseStep 3323885 = 1246457) (by norm_num)
theorem B2215923 : Blo 2215435 2215923 := bstep (se 1 (by rfl) ⟨1661942, by rfl⟩ : syracuseStep 2215923 = 3323885) B3323885
theorem B4985837 : Blo 2215435 4985837 := bbase (se 3 (by rfl) ⟨934844, by rfl⟩ : syracuseStep 4985837 = 1869689) (by norm_num)
theorem B3323891 : Blo 2215435 3323891 := bstep (se 1 (by rfl) ⟨2492918, by rfl⟩ : syracuseStep 3323891 = 4985837) B4985837
theorem B2215927 : Blo 2215435 2215927 := bstep (se 1 (by rfl) ⟨1661945, by rfl⟩ : syracuseStep 2215927 = 3323891) B3323891
theorem B4732661 : Blo 2215435 4732661 := bbase (se 5 (by rfl) ⟨221843, by rfl⟩ : syracuseStep 4732661 = 443687) (by norm_num)
theorem B3155107 : Blo 2215435 3155107 := bstep (se 1 (by rfl) ⟨2366330, by rfl⟩ : syracuseStep 3155107 = 4732661) B4732661
theorem B4206809 : Blo 2215435 4206809 := bstep (se 2 (by rfl) ⟨1577553, by rfl⟩ : syracuseStep 4206809 = 3155107) B3155107
theorem B2804539 : Blo 2215435 2804539 := bstep (se 1 (by rfl) ⟨2103404, by rfl⟩ : syracuseStep 2804539 = 4206809) B4206809
theorem B3739385 : Blo 2215435 3739385 := bstep (se 2 (by rfl) ⟨1402269, by rfl⟩ : syracuseStep 3739385 = 2804539) B2804539
theorem B2492923 : Blo 2215435 2492923 := bstep (se 1 (by rfl) ⟨1869692, by rfl⟩ : syracuseStep 2492923 = 3739385) B3739385
theorem B3323897 : Blo 2215435 3323897 := bstep (se 2 (by rfl) ⟨1246461, by rfl⟩ : syracuseStep 3323897 = 2492923) B2492923
theorem B2215931 : Blo 2215435 2215931 := bstep (se 1 (by rfl) ⟨1661948, by rfl⟩ : syracuseStep 2215931 = 3323897) B3323897
theorem B19188949 : Blo 2215435 19188949 := bbase (se 7 (by rfl) ⟨224870, by rfl⟩ : syracuseStep 19188949 = 449741) (by norm_num)
theorem B25585265 : Blo 2215435 25585265 := bstep (se 2 (by rfl) ⟨9594474, by rfl⟩ : syracuseStep 25585265 = 19188949) B19188949
theorem B68227373 : Blo 2215435 68227373 := bstep (se 3 (by rfl) ⟨12792632, by rfl⟩ : syracuseStep 68227373 = 25585265) B25585265
theorem B45484915 : Blo 2215435 45484915 := bstep (se 1 (by rfl) ⟨34113686, by rfl⟩ : syracuseStep 45484915 = 68227373) B68227373
theorem B60646553 : Blo 2215435 60646553 := bstep (se 2 (by rfl) ⟨22742457, by rfl⟩ : syracuseStep 60646553 = 45484915) B45484915
theorem B40431035 : Blo 2215435 40431035 := bstep (se 1 (by rfl) ⟨30323276, by rfl⟩ : syracuseStep 40431035 = 60646553) B60646553
theorem B107816093 : Blo 2215435 107816093 := bstep (se 3 (by rfl) ⟨20215517, by rfl⟩ : syracuseStep 107816093 = 40431035) B40431035
theorem B71877395 : Blo 2215435 71877395 := bstep (se 1 (by rfl) ⟨53908046, by rfl⟩ : syracuseStep 71877395 = 107816093) B107816093
theorem B191673053 : Blo 2215435 191673053 := bstep (se 3 (by rfl) ⟨35938697, by rfl⟩ : syracuseStep 191673053 = 71877395) B71877395
theorem B127782035 : Blo 2215435 127782035 := bstep (se 1 (by rfl) ⟨95836526, by rfl⟩ : syracuseStep 127782035 = 191673053) B191673053
theorem B85188023 : Blo 2215435 85188023 := bstep (se 1 (by rfl) ⟨63891017, by rfl⟩ : syracuseStep 85188023 = 127782035) B127782035
theorem B56792015 : Blo 2215435 56792015 := bstep (se 1 (by rfl) ⟨42594011, by rfl⟩ : syracuseStep 56792015 = 85188023) B85188023
theorem B37861343 : Blo 2215435 37861343 := bstep (se 1 (by rfl) ⟨28396007, by rfl⟩ : syracuseStep 37861343 = 56792015) B56792015
theorem B25240895 : Blo 2215435 25240895 := bstep (se 1 (by rfl) ⟨18930671, by rfl⟩ : syracuseStep 25240895 = 37861343) B37861343
theorem B16827263 : Blo 2215435 16827263 := bstep (se 1 (by rfl) ⟨12620447, by rfl⟩ : syracuseStep 16827263 = 25240895) B25240895
theorem B11218175 : Blo 2215435 11218175 := bstep (se 1 (by rfl) ⟨8413631, by rfl⟩ : syracuseStep 11218175 = 16827263) B16827263
theorem B7478783 : Blo 2215435 7478783 := bstep (se 1 (by rfl) ⟨5609087, by rfl⟩ : syracuseStep 7478783 = 11218175) B11218175
theorem B4985855 : Blo 2215435 4985855 := bstep (se 1 (by rfl) ⟨3739391, by rfl⟩ : syracuseStep 4985855 = 7478783) B7478783
theorem B3323903 : Blo 2215435 3323903 := bstep (se 1 (by rfl) ⟨2492927, by rfl⟩ : syracuseStep 3323903 = 4985855) B4985855
theorem B2215935 : Blo 2215435 2215935 := bstep (se 1 (by rfl) ⟨1661951, by rfl⟩ : syracuseStep 2215935 = 3323903) B3323903
theorem B3323909 : Blo 2215435 3323909 := bbase (se 4 (by rfl) ⟨311616, by rfl⟩ : syracuseStep 3323909 = 623233) (by norm_num)
theorem B2215939 : Blo 2215435 2215939 := bstep (se 1 (by rfl) ⟨1661954, by rfl⟩ : syracuseStep 2215939 = 3323909) B3323909
theorem B3739405 : Blo 2215435 3739405 := bbase (se 3 (by rfl) ⟨701138, by rfl⟩ : syracuseStep 3739405 = 1402277) (by norm_num)
theorem B4985873 : Blo 2215435 4985873 := bstep (se 2 (by rfl) ⟨1869702, by rfl⟩ : syracuseStep 4985873 = 3739405) B3739405
theorem B3323915 : Blo 2215435 3323915 := bstep (se 1 (by rfl) ⟨2492936, by rfl⟩ : syracuseStep 3323915 = 4985873) B4985873
theorem B2215943 : Blo 2215435 2215943 := bstep (se 1 (by rfl) ⟨1661957, by rfl⟩ : syracuseStep 2215943 = 3323915) B3323915
theorem B2492941 : Blo 2215435 2492941 := bbase (se 3 (by rfl) ⟨467426, by rfl⟩ : syracuseStep 2492941 = 934853) (by norm_num)
theorem B3323921 : Blo 2215435 3323921 := bstep (se 2 (by rfl) ⟨1246470, by rfl⟩ : syracuseStep 3323921 = 2492941) B2492941
theorem B2215947 : Blo 2215435 2215947 := bstep (se 1 (by rfl) ⟨1661960, by rfl⟩ : syracuseStep 2215947 = 3323921) B3323921
theorem B7478837 : Blo 2215435 7478837 := bbase (se 5 (by rfl) ⟨350570, by rfl⟩ : syracuseStep 7478837 = 701141) (by norm_num)
theorem B4985891 : Blo 2215435 4985891 := bstep (se 1 (by rfl) ⟨3739418, by rfl⟩ : syracuseStep 4985891 = 7478837) B7478837
theorem B3323927 : Blo 2215435 3323927 := bstep (se 1 (by rfl) ⟨2492945, by rfl⟩ : syracuseStep 3323927 = 4985891) B4985891
theorem B2215951 : Blo 2215435 2215951 := bstep (se 1 (by rfl) ⟨1661963, by rfl⟩ : syracuseStep 2215951 = 3323927) B3323927
theorem B3323933 : Blo 2215435 3323933 := bbase (se 3 (by rfl) ⟨623237, by rfl⟩ : syracuseStep 3323933 = 1246475) (by norm_num)
theorem B2215955 : Blo 2215435 2215955 := bstep (se 1 (by rfl) ⟨1661966, by rfl⟩ : syracuseStep 2215955 = 3323933) B3323933
theorem B4985909 : Blo 2215435 4985909 := bbase (se 5 (by rfl) ⟨233714, by rfl⟩ : syracuseStep 4985909 = 467429) (by norm_num)
theorem B3323939 : Blo 2215435 3323939 := bstep (se 1 (by rfl) ⟨2492954, by rfl⟩ : syracuseStep 3323939 = 4985909) B4985909
theorem B2215959 : Blo 2215435 2215959 := bstep (se 1 (by rfl) ⟨1661969, by rfl⟩ : syracuseStep 2215959 = 3323939) B3323939
theorem B7099093 : Blo 2215435 7099093 := bbase (se 7 (by rfl) ⟨83192, by rfl⟩ : syracuseStep 7099093 = 166385) (by norm_num)
theorem B9465457 : Blo 2215435 9465457 := bstep (se 2 (by rfl) ⟨3549546, by rfl⟩ : syracuseStep 9465457 = 7099093) B7099093
theorem B12620609 : Blo 2215435 12620609 := bstep (se 2 (by rfl) ⟨4732728, by rfl⟩ : syracuseStep 12620609 = 9465457) B9465457
theorem B8413739 : Blo 2215435 8413739 := bstep (se 1 (by rfl) ⟨6310304, by rfl⟩ : syracuseStep 8413739 = 12620609) B12620609
theorem B5609159 : Blo 2215435 5609159 := bstep (se 1 (by rfl) ⟨4206869, by rfl⟩ : syracuseStep 5609159 = 8413739) B8413739
theorem B3739439 : Blo 2215435 3739439 := bstep (se 1 (by rfl) ⟨2804579, by rfl⟩ : syracuseStep 3739439 = 5609159) B5609159
theorem B2492959 : Blo 2215435 2492959 := bstep (se 1 (by rfl) ⟨1869719, by rfl⟩ : syracuseStep 2492959 = 3739439) B3739439
theorem B3323945 : Blo 2215435 3323945 := bstep (se 2 (by rfl) ⟨1246479, by rfl⟩ : syracuseStep 3323945 = 2492959) B2492959
theorem B2215963 : Blo 2215435 2215963 := bstep (se 1 (by rfl) ⟨1661972, by rfl⟩ : syracuseStep 2215963 = 3323945) B3323945
theorem B12143189 : Blo 2215435 12143189 := bbase (se 8 (by rfl) ⟨71151, by rfl⟩ : syracuseStep 12143189 = 142303) (by norm_num)
theorem B8095459 : Blo 2215435 8095459 := bstep (se 1 (by rfl) ⟨6071594, by rfl⟩ : syracuseStep 8095459 = 12143189) B12143189
theorem B10793945 : Blo 2215435 10793945 := bstep (se 2 (by rfl) ⟨4047729, by rfl⟩ : syracuseStep 10793945 = 8095459) B8095459
theorem B7195963 : Blo 2215435 7195963 := bstep (se 1 (by rfl) ⟨5396972, by rfl⟩ : syracuseStep 7195963 = 10793945) B10793945
theorem B9594617 : Blo 2215435 9594617 := bstep (se 2 (by rfl) ⟨3597981, by rfl⟩ : syracuseStep 9594617 = 7195963) B7195963
theorem B25585645 : Blo 2215435 25585645 := bstep (se 3 (by rfl) ⟨4797308, by rfl⟩ : syracuseStep 25585645 = 9594617) B9594617
theorem B34114193 : Blo 2215435 34114193 := bstep (se 2 (by rfl) ⟨12792822, by rfl⟩ : syracuseStep 34114193 = 25585645) B25585645
theorem B22742795 : Blo 2215435 22742795 := bstep (se 1 (by rfl) ⟨17057096, by rfl⟩ : syracuseStep 22742795 = 34114193) B34114193
theorem B15161863 : Blo 2215435 15161863 := bstep (se 1 (by rfl) ⟨11371397, by rfl⟩ : syracuseStep 15161863 = 22742795) B22742795
theorem B20215817 : Blo 2215435 20215817 := bstep (se 2 (by rfl) ⟨7580931, by rfl⟩ : syracuseStep 20215817 = 15161863) B15161863
theorem B13477211 : Blo 2215435 13477211 := bstep (se 1 (by rfl) ⟨10107908, by rfl⟩ : syracuseStep 13477211 = 20215817) B20215817
theorem B8984807 : Blo 2215435 8984807 := bstep (se 1 (by rfl) ⟨6738605, by rfl⟩ : syracuseStep 8984807 = 13477211) B13477211
theorem B5989871 : Blo 2215435 5989871 := bstep (se 1 (by rfl) ⟨4492403, by rfl⟩ : syracuseStep 5989871 = 8984807) B8984807
theorem B3993247 : Blo 2215435 3993247 := bstep (se 1 (by rfl) ⟨2994935, by rfl⟩ : syracuseStep 3993247 = 5989871) B5989871
theorem B5324329 : Blo 2215435 5324329 := bstep (se 2 (by rfl) ⟨1996623, by rfl⟩ : syracuseStep 5324329 = 3993247) B3993247
theorem B7099105 : Blo 2215435 7099105 := bstep (se 2 (by rfl) ⟨2662164, by rfl⟩ : syracuseStep 7099105 = 5324329) B5324329
theorem B9465473 : Blo 2215435 9465473 := bstep (se 2 (by rfl) ⟨3549552, by rfl⟩ : syracuseStep 9465473 = 7099105) B7099105
theorem B6310315 : Blo 2215435 6310315 := bstep (se 1 (by rfl) ⟨4732736, by rfl⟩ : syracuseStep 6310315 = 9465473) B9465473
theorem B8413753 : Blo 2215435 8413753 := bstep (se 2 (by rfl) ⟨3155157, by rfl⟩ : syracuseStep 8413753 = 6310315) B6310315
theorem B11218337 : Blo 2215435 11218337 := bstep (se 2 (by rfl) ⟨4206876, by rfl⟩ : syracuseStep 11218337 = 8413753) B8413753
theorem B7478891 : Blo 2215435 7478891 := bstep (se 1 (by rfl) ⟨5609168, by rfl⟩ : syracuseStep 7478891 = 11218337) B11218337
theorem B4985927 : Blo 2215435 4985927 := bstep (se 1 (by rfl) ⟨3739445, by rfl⟩ : syracuseStep 4985927 = 7478891) B7478891
theorem B3323951 : Blo 2215435 3323951 := bstep (se 1 (by rfl) ⟨2492963, by rfl⟩ : syracuseStep 3323951 = 4985927) B4985927
theorem B2215967 : Blo 2215435 2215967 := bstep (se 1 (by rfl) ⟨1661975, by rfl⟩ : syracuseStep 2215967 = 3323951) B3323951
theorem B3323957 : Blo 2215435 3323957 := bbase (se 5 (by rfl) ⟨155810, by rfl⟩ : syracuseStep 3323957 = 311621) (by norm_num)
theorem B2215971 : Blo 2215435 2215971 := bstep (se 1 (by rfl) ⟨1661978, by rfl⟩ : syracuseStep 2215971 = 3323957) B3323957
theorem B5609189 : Blo 2215435 5609189 := bbase (se 4 (by rfl) ⟨525861, by rfl⟩ : syracuseStep 5609189 = 1051723) (by norm_num)
theorem B3739459 : Blo 2215435 3739459 := bstep (se 1 (by rfl) ⟨2804594, by rfl⟩ : syracuseStep 3739459 = 5609189) B5609189
theorem B4985945 : Blo 2215435 4985945 := bstep (se 2 (by rfl) ⟨1869729, by rfl⟩ : syracuseStep 4985945 = 3739459) B3739459
theorem B3323963 : Blo 2215435 3323963 := bstep (se 1 (by rfl) ⟨2492972, by rfl⟩ : syracuseStep 3323963 = 4985945) B4985945
theorem B2215975 : Blo 2215435 2215975 := bstep (se 1 (by rfl) ⟨1661981, by rfl⟩ : syracuseStep 2215975 = 3323963) B3323963
theorem B2492977 : Blo 2215435 2492977 := bbase (se 2 (by rfl) ⟨934866, by rfl⟩ : syracuseStep 2492977 = 1869733) (by norm_num)
theorem B3323969 : Blo 2215435 3323969 := bstep (se 2 (by rfl) ⟨1246488, by rfl⟩ : syracuseStep 3323969 = 2492977) B2492977
theorem B2215979 : Blo 2215435 2215979 := bstep (se 1 (by rfl) ⟨1661984, by rfl⟩ : syracuseStep 2215979 = 3323969) B3323969
theorem B7099157 : Blo 2215435 7099157 := bbase (se 6 (by rfl) ⟨166386, by rfl⟩ : syracuseStep 7099157 = 332773) (by norm_num)
theorem B4732771 : Blo 2215435 4732771 := bstep (se 1 (by rfl) ⟨3549578, by rfl⟩ : syracuseStep 4732771 = 7099157) B7099157
theorem B6310361 : Blo 2215435 6310361 := bstep (se 2 (by rfl) ⟨2366385, by rfl⟩ : syracuseStep 6310361 = 4732771) B4732771
theorem B4206907 : Blo 2215435 4206907 := bstep (se 1 (by rfl) ⟨3155180, by rfl⟩ : syracuseStep 4206907 = 6310361) B6310361
theorem B5609209 : Blo 2215435 5609209 := bstep (se 2 (by rfl) ⟨2103453, by rfl⟩ : syracuseStep 5609209 = 4206907) B4206907
theorem B7478945 : Blo 2215435 7478945 := bstep (se 2 (by rfl) ⟨2804604, by rfl⟩ : syracuseStep 7478945 = 5609209) B5609209
theorem B4985963 : Blo 2215435 4985963 := bstep (se 1 (by rfl) ⟨3739472, by rfl⟩ : syracuseStep 4985963 = 7478945) B7478945
theorem B3323975 : Blo 2215435 3323975 := bstep (se 1 (by rfl) ⟨2492981, by rfl⟩ : syracuseStep 3323975 = 4985963) B4985963
theorem B2215983 : Blo 2215435 2215983 := bstep (se 1 (by rfl) ⟨1661987, by rfl⟩ : syracuseStep 2215983 = 3323975) B3323975
theorem B3323981 : Blo 2215435 3323981 := bbase (se 3 (by rfl) ⟨623246, by rfl⟩ : syracuseStep 3323981 = 1246493) (by norm_num)
theorem B2215987 : Blo 2215435 2215987 := bstep (se 1 (by rfl) ⟨1661990, by rfl⟩ : syracuseStep 2215987 = 3323981) B3323981
theorem B4985981 : Blo 2215435 4985981 := bbase (se 3 (by rfl) ⟨934871, by rfl⟩ : syracuseStep 4985981 = 1869743) (by norm_num)
theorem B3323987 : Blo 2215435 3323987 := bstep (se 1 (by rfl) ⟨2492990, by rfl⟩ : syracuseStep 3323987 = 4985981) B4985981
theorem B2215991 : Blo 2215435 2215991 := bstep (se 1 (by rfl) ⟨1661993, by rfl⟩ : syracuseStep 2215991 = 3323987) B3323987
theorem B3739493 : Blo 2215435 3739493 := bbase (se 4 (by rfl) ⟨350577, by rfl⟩ : syracuseStep 3739493 = 701155) (by norm_num)
theorem B2492995 : Blo 2215435 2492995 := bstep (se 1 (by rfl) ⟨1869746, by rfl⟩ : syracuseStep 2492995 = 3739493) B3739493
theorem B3323993 : Blo 2215435 3323993 := bstep (se 2 (by rfl) ⟨1246497, by rfl⟩ : syracuseStep 3323993 = 2492995) B2492995
theorem B2215995 : Blo 2215435 2215995 := bstep (se 1 (by rfl) ⟨1661996, by rfl⟩ : syracuseStep 2215995 = 3323993) B3323993
theorem B4732805 : Blo 2215435 4732805 := bbase (se 4 (by rfl) ⟨443700, by rfl⟩ : syracuseStep 4732805 = 887401) (by norm_num)
theorem B3155203 : Blo 2215435 3155203 := bstep (se 1 (by rfl) ⟨2366402, by rfl⟩ : syracuseStep 3155203 = 4732805) B4732805
theorem B16827749 : Blo 2215435 16827749 := bstep (se 4 (by rfl) ⟨1577601, by rfl⟩ : syracuseStep 16827749 = 3155203) B3155203
theorem B11218499 : Blo 2215435 11218499 := bstep (se 1 (by rfl) ⟨8413874, by rfl⟩ : syracuseStep 11218499 = 16827749) B16827749
theorem B7478999 : Blo 2215435 7478999 := bstep (se 1 (by rfl) ⟨5609249, by rfl⟩ : syracuseStep 7478999 = 11218499) B11218499
theorem B4985999 : Blo 2215435 4985999 := bstep (se 1 (by rfl) ⟨3739499, by rfl⟩ : syracuseStep 4985999 = 7478999) B7478999
theorem B3323999 : Blo 2215435 3323999 := bstep (se 1 (by rfl) ⟨2492999, by rfl⟩ : syracuseStep 3323999 = 4985999) B4985999
theorem B2215999 : Blo 2215435 2215999 := bstep (se 1 (by rfl) ⟨1661999, by rfl⟩ : syracuseStep 2215999 = 3323999) B3323999
theorem B3324005 : Blo 2215435 3324005 := bbase (se 4 (by rfl) ⟨311625, by rfl⟩ : syracuseStep 3324005 = 623251) (by norm_num)
theorem B2216003 : Blo 2215435 2216003 := bstep (se 1 (by rfl) ⟨1662002, by rfl⟩ : syracuseStep 2216003 = 3324005) B3324005
theorem B10648853 : Blo 2215435 10648853 := bbase (se 6 (by rfl) ⟨249582, by rfl⟩ : syracuseStep 10648853 = 499165) (by norm_num)
theorem B7099235 : Blo 2215435 7099235 := bstep (se 1 (by rfl) ⟨5324426, by rfl⟩ : syracuseStep 7099235 = 10648853) B10648853
theorem B4732823 : Blo 2215435 4732823 := bstep (se 1 (by rfl) ⟨3549617, by rfl⟩ : syracuseStep 4732823 = 7099235) B7099235
theorem B3155215 : Blo 2215435 3155215 := bstep (se 1 (by rfl) ⟨2366411, by rfl⟩ : syracuseStep 3155215 = 4732823) B4732823
theorem B4206953 : Blo 2215435 4206953 := bstep (se 2 (by rfl) ⟨1577607, by rfl⟩ : syracuseStep 4206953 = 3155215) B3155215
theorem B2804635 : Blo 2215435 2804635 := bstep (se 1 (by rfl) ⟨2103476, by rfl⟩ : syracuseStep 2804635 = 4206953) B4206953
theorem B3739513 : Blo 2215435 3739513 := bstep (se 2 (by rfl) ⟨1402317, by rfl⟩ : syracuseStep 3739513 = 2804635) B2804635
theorem B4986017 : Blo 2215435 4986017 := bstep (se 2 (by rfl) ⟨1869756, by rfl⟩ : syracuseStep 4986017 = 3739513) B3739513
theorem B3324011 : Blo 2215435 3324011 := bstep (se 1 (by rfl) ⟨2493008, by rfl⟩ : syracuseStep 3324011 = 4986017) B4986017
theorem B2216007 : Blo 2215435 2216007 := bstep (se 1 (by rfl) ⟨1662005, by rfl⟩ : syracuseStep 2216007 = 3324011) B3324011
theorem B2493013 : Blo 2215435 2493013 := bbase (se 8 (by rfl) ⟨14607, by rfl⟩ : syracuseStep 2493013 = 29215) (by norm_num)
theorem B3324017 : Blo 2215435 3324017 := bstep (se 2 (by rfl) ⟨1246506, by rfl⟩ : syracuseStep 3324017 = 2493013) B2493013
theorem B2216011 : Blo 2215435 2216011 := bstep (se 1 (by rfl) ⟨1662008, by rfl⟩ : syracuseStep 2216011 = 3324017) B3324017
theorem B2804645 : Blo 2215435 2804645 := bbase (se 4 (by rfl) ⟨262935, by rfl⟩ : syracuseStep 2804645 = 525871) (by norm_num)
theorem B7479053 : Blo 2215435 7479053 := bstep (se 3 (by rfl) ⟨1402322, by rfl⟩ : syracuseStep 7479053 = 2804645) B2804645
theorem B4986035 : Blo 2215435 4986035 := bstep (se 1 (by rfl) ⟨3739526, by rfl⟩ : syracuseStep 4986035 = 7479053) B7479053
theorem B3324023 : Blo 2215435 3324023 := bstep (se 1 (by rfl) ⟨2493017, by rfl⟩ : syracuseStep 3324023 = 4986035) B4986035
theorem B2216015 : Blo 2215435 2216015 := bstep (se 1 (by rfl) ⟨1662011, by rfl⟩ : syracuseStep 2216015 = 3324023) B3324023
theorem B3324029 : Blo 2215435 3324029 := bbase (se 3 (by rfl) ⟨623255, by rfl⟩ : syracuseStep 3324029 = 1246511) (by norm_num)
theorem B2216019 : Blo 2215435 2216019 := bstep (se 1 (by rfl) ⟨1662014, by rfl⟩ : syracuseStep 2216019 = 3324029) B3324029
theorem B4986053 : Blo 2215435 4986053 := bbase (se 4 (by rfl) ⟨467442, by rfl⟩ : syracuseStep 4986053 = 934885) (by norm_num)
theorem B3324035 : Blo 2215435 3324035 := bstep (se 1 (by rfl) ⟨2493026, by rfl⟩ : syracuseStep 3324035 = 4986053) B4986053
theorem B2216023 : Blo 2215435 2216023 := bstep (se 1 (by rfl) ⟨1662017, by rfl⟩ : syracuseStep 2216023 = 3324035) B3324035
theorem B2662237 : Blo 2215435 2662237 := bbase (se 3 (by rfl) ⟨499169, by rfl⟩ : syracuseStep 2662237 = 998339) (by norm_num)
theorem B14198597 : Blo 2215435 14198597 := bstep (se 4 (by rfl) ⟨1331118, by rfl⟩ : syracuseStep 14198597 = 2662237) B2662237
theorem B9465731 : Blo 2215435 9465731 := bstep (se 1 (by rfl) ⟨7099298, by rfl⟩ : syracuseStep 9465731 = 14198597) B14198597
theorem B6310487 : Blo 2215435 6310487 := bstep (se 1 (by rfl) ⟨4732865, by rfl⟩ : syracuseStep 6310487 = 9465731) B9465731
theorem B4206991 : Blo 2215435 4206991 := bstep (se 1 (by rfl) ⟨3155243, by rfl⟩ : syracuseStep 4206991 = 6310487) B6310487
theorem B5609321 : Blo 2215435 5609321 := bstep (se 2 (by rfl) ⟨2103495, by rfl⟩ : syracuseStep 5609321 = 4206991) B4206991
theorem B3739547 : Blo 2215435 3739547 := bstep (se 1 (by rfl) ⟨2804660, by rfl⟩ : syracuseStep 3739547 = 5609321) B5609321
theorem B2493031 : Blo 2215435 2493031 := bstep (se 1 (by rfl) ⟨1869773, by rfl⟩ : syracuseStep 2493031 = 3739547) B3739547
theorem B3324041 : Blo 2215435 3324041 := bstep (se 2 (by rfl) ⟨1246515, by rfl⟩ : syracuseStep 3324041 = 2493031) B2493031
theorem B2216027 : Blo 2215435 2216027 := bstep (se 1 (by rfl) ⟨1662020, by rfl⟩ : syracuseStep 2216027 = 3324041) B3324041
theorem B11218661 : Blo 2215435 11218661 := bbase (se 4 (by rfl) ⟨1051749, by rfl⟩ : syracuseStep 11218661 = 2103499) (by norm_num)
theorem B7479107 : Blo 2215435 7479107 := bstep (se 1 (by rfl) ⟨5609330, by rfl⟩ : syracuseStep 7479107 = 11218661) B11218661
theorem B4986071 : Blo 2215435 4986071 := bstep (se 1 (by rfl) ⟨3739553, by rfl⟩ : syracuseStep 4986071 = 7479107) B7479107
theorem B3324047 : Blo 2215435 3324047 := bstep (se 1 (by rfl) ⟨2493035, by rfl⟩ : syracuseStep 3324047 = 4986071) B4986071
theorem B2216031 : Blo 2215435 2216031 := bstep (se 1 (by rfl) ⟨1662023, by rfl⟩ : syracuseStep 2216031 = 3324047) B3324047
theorem B3324053 : Blo 2215435 3324053 := bbase (se 6 (by rfl) ⟨77907, by rfl⟩ : syracuseStep 3324053 = 155815) (by norm_num)
theorem B2216035 : Blo 2215435 2216035 := bstep (se 1 (by rfl) ⟨1662026, by rfl⟩ : syracuseStep 2216035 = 3324053) B3324053
theorem B9465781 : Blo 2215435 9465781 := bbase (se 5 (by rfl) ⟨443708, by rfl⟩ : syracuseStep 9465781 = 887417) (by norm_num)
theorem B12621041 : Blo 2215435 12621041 := bstep (se 2 (by rfl) ⟨4732890, by rfl⟩ : syracuseStep 12621041 = 9465781) B9465781
theorem B8414027 : Blo 2215435 8414027 := bstep (se 1 (by rfl) ⟨6310520, by rfl⟩ : syracuseStep 8414027 = 12621041) B12621041
theorem B5609351 : Blo 2215435 5609351 := bstep (se 1 (by rfl) ⟨4207013, by rfl⟩ : syracuseStep 5609351 = 8414027) B8414027
theorem B3739567 : Blo 2215435 3739567 := bstep (se 1 (by rfl) ⟨2804675, by rfl⟩ : syracuseStep 3739567 = 5609351) B5609351
theorem B4986089 : Blo 2215435 4986089 := bstep (se 2 (by rfl) ⟨1869783, by rfl⟩ : syracuseStep 4986089 = 3739567) B3739567
theorem B3324059 : Blo 2215435 3324059 := bstep (se 1 (by rfl) ⟨2493044, by rfl⟩ : syracuseStep 3324059 = 4986089) B4986089
theorem B2216039 : Blo 2215435 2216039 := bstep (se 1 (by rfl) ⟨1662029, by rfl⟩ : syracuseStep 2216039 = 3324059) B3324059
theorem B2493049 : Blo 2215435 2493049 := bbase (se 2 (by rfl) ⟨934893, by rfl⟩ : syracuseStep 2493049 = 1869787) (by norm_num)
theorem B3324065 : Blo 2215435 3324065 := bstep (se 2 (by rfl) ⟨1246524, by rfl⟩ : syracuseStep 3324065 = 2493049) B2493049
theorem B2216043 : Blo 2215435 2216043 := bstep (se 1 (by rfl) ⟨1662032, by rfl⟩ : syracuseStep 2216043 = 3324065) B3324065
theorem B7581205 : Blo 2215435 7581205 := bbase (se 6 (by rfl) ⟨177684, by rfl⟩ : syracuseStep 7581205 = 355369) (by norm_num)
theorem B10108273 : Blo 2215435 10108273 := bstep (se 2 (by rfl) ⟨3790602, by rfl⟩ : syracuseStep 10108273 = 7581205) B7581205
theorem B13477697 : Blo 2215435 13477697 := bstep (se 2 (by rfl) ⟨5054136, by rfl⟩ : syracuseStep 13477697 = 10108273) B10108273
theorem B8985131 : Blo 2215435 8985131 := bstep (se 1 (by rfl) ⟨6738848, by rfl⟩ : syracuseStep 8985131 = 13477697) B13477697
theorem B5990087 : Blo 2215435 5990087 := bstep (se 1 (by rfl) ⟨4492565, by rfl⟩ : syracuseStep 5990087 = 8985131) B8985131
theorem B3993391 : Blo 2215435 3993391 := bstep (se 1 (by rfl) ⟨2995043, by rfl⟩ : syracuseStep 3993391 = 5990087) B5990087
theorem B21298085 : Blo 2215435 21298085 := bstep (se 4 (by rfl) ⟨1996695, by rfl⟩ : syracuseStep 21298085 = 3993391) B3993391
theorem B14198723 : Blo 2215435 14198723 := bstep (se 1 (by rfl) ⟨10649042, by rfl⟩ : syracuseStep 14198723 = 21298085) B21298085
theorem B9465815 : Blo 2215435 9465815 := bstep (se 1 (by rfl) ⟨7099361, by rfl⟩ : syracuseStep 9465815 = 14198723) B14198723
theorem B6310543 : Blo 2215435 6310543 := bstep (se 1 (by rfl) ⟨4732907, by rfl⟩ : syracuseStep 6310543 = 9465815) B9465815
theorem B8414057 : Blo 2215435 8414057 := bstep (se 2 (by rfl) ⟨3155271, by rfl⟩ : syracuseStep 8414057 = 6310543) B6310543
theorem B5609371 : Blo 2215435 5609371 := bstep (se 1 (by rfl) ⟨4207028, by rfl⟩ : syracuseStep 5609371 = 8414057) B8414057
theorem B7479161 : Blo 2215435 7479161 := bstep (se 2 (by rfl) ⟨2804685, by rfl⟩ : syracuseStep 7479161 = 5609371) B5609371
theorem B4986107 : Blo 2215435 4986107 := bstep (se 1 (by rfl) ⟨3739580, by rfl⟩ : syracuseStep 4986107 = 7479161) B7479161
theorem B3324071 : Blo 2215435 3324071 := bstep (se 1 (by rfl) ⟨2493053, by rfl⟩ : syracuseStep 3324071 = 4986107) B4986107
theorem B2216047 : Blo 2215435 2216047 := bstep (se 1 (by rfl) ⟨1662035, by rfl⟩ : syracuseStep 2216047 = 3324071) B3324071
theorem B3324077 : Blo 2215435 3324077 := bbase (se 3 (by rfl) ⟨623264, by rfl⟩ : syracuseStep 3324077 = 1246529) (by norm_num)
theorem B2216051 : Blo 2215435 2216051 := bstep (se 1 (by rfl) ⟨1662038, by rfl⟩ : syracuseStep 2216051 = 3324077) B3324077
theorem B4986125 : Blo 2215435 4986125 := bbase (se 3 (by rfl) ⟨934898, by rfl⟩ : syracuseStep 4986125 = 1869797) (by norm_num)
theorem B3324083 : Blo 2215435 3324083 := bstep (se 1 (by rfl) ⟨2493062, by rfl⟩ : syracuseStep 3324083 = 4986125) B4986125
theorem B2216055 : Blo 2215435 2216055 := bstep (se 1 (by rfl) ⟨1662041, by rfl⟩ : syracuseStep 2216055 = 3324083) B3324083
theorem B2804701 : Blo 2215435 2804701 := bbase (se 3 (by rfl) ⟨525881, by rfl⟩ : syracuseStep 2804701 = 1051763) (by norm_num)
theorem B3739601 : Blo 2215435 3739601 := bstep (se 2 (by rfl) ⟨1402350, by rfl⟩ : syracuseStep 3739601 = 2804701) B2804701
theorem B2493067 : Blo 2215435 2493067 := bstep (se 1 (by rfl) ⟨1869800, by rfl⟩ : syracuseStep 2493067 = 3739601) B3739601
theorem B3324089 : Blo 2215435 3324089 := bstep (se 2 (by rfl) ⟨1246533, by rfl⟩ : syracuseStep 3324089 = 2493067) B2493067
theorem B2216059 : Blo 2215435 2216059 := bstep (se 1 (by rfl) ⟨1662044, by rfl⟩ : syracuseStep 2216059 = 3324089) B3324089
theorem B18931765 : Blo 2215435 18931765 := bbase (se 5 (by rfl) ⟨887426, by rfl⟩ : syracuseStep 18931765 = 1774853) (by norm_num)
theorem B25242353 : Blo 2215435 25242353 := bstep (se 2 (by rfl) ⟨9465882, by rfl⟩ : syracuseStep 25242353 = 18931765) B18931765
theorem B16828235 : Blo 2215435 16828235 := bstep (se 1 (by rfl) ⟨12621176, by rfl⟩ : syracuseStep 16828235 = 25242353) B25242353
theorem B11218823 : Blo 2215435 11218823 := bstep (se 1 (by rfl) ⟨8414117, by rfl⟩ : syracuseStep 11218823 = 16828235) B16828235
theorem B7479215 : Blo 2215435 7479215 := bstep (se 1 (by rfl) ⟨5609411, by rfl⟩ : syracuseStep 7479215 = 11218823) B11218823
theorem B4986143 : Blo 2215435 4986143 := bstep (se 1 (by rfl) ⟨3739607, by rfl⟩ : syracuseStep 4986143 = 7479215) B7479215
theorem B3324095 : Blo 2215435 3324095 := bstep (se 1 (by rfl) ⟨2493071, by rfl⟩ : syracuseStep 3324095 = 4986143) B4986143
theorem B2216063 : Blo 2215435 2216063 := bstep (se 1 (by rfl) ⟨1662047, by rfl⟩ : syracuseStep 2216063 = 3324095) B3324095
theorem B3324101 : Blo 2215435 3324101 := bbase (se 4 (by rfl) ⟨311634, by rfl⟩ : syracuseStep 3324101 = 623269) (by norm_num)
theorem B2216067 : Blo 2215435 2216067 := bstep (se 1 (by rfl) ⟨1662050, by rfl⟩ : syracuseStep 2216067 = 3324101) B3324101
theorem B3739621 : Blo 2215435 3739621 := bbase (se 4 (by rfl) ⟨350589, by rfl⟩ : syracuseStep 3739621 = 701179) (by norm_num)
theorem B4986161 : Blo 2215435 4986161 := bstep (se 2 (by rfl) ⟨1869810, by rfl⟩ : syracuseStep 4986161 = 3739621) B3739621
theorem B3324107 : Blo 2215435 3324107 := bstep (se 1 (by rfl) ⟨2493080, by rfl⟩ : syracuseStep 3324107 = 4986161) B4986161
theorem B2216071 : Blo 2215435 2216071 := bstep (se 1 (by rfl) ⟨1662053, by rfl⟩ : syracuseStep 2216071 = 3324107) B3324107
theorem B2493085 : Blo 2215435 2493085 := bbase (se 3 (by rfl) ⟨467453, by rfl⟩ : syracuseStep 2493085 = 934907) (by norm_num)
theorem B3324113 : Blo 2215435 3324113 := bstep (se 2 (by rfl) ⟨1246542, by rfl⟩ : syracuseStep 3324113 = 2493085) B2493085
theorem B2216075 : Blo 2215435 2216075 := bstep (se 1 (by rfl) ⟨1662056, by rfl⟩ : syracuseStep 2216075 = 3324113) B3324113
theorem B7479269 : Blo 2215435 7479269 := bbase (se 4 (by rfl) ⟨701181, by rfl⟩ : syracuseStep 7479269 = 1402363) (by norm_num)
theorem B4986179 : Blo 2215435 4986179 := bstep (se 1 (by rfl) ⟨3739634, by rfl⟩ : syracuseStep 4986179 = 7479269) B7479269
theorem B3324119 : Blo 2215435 3324119 := bstep (se 1 (by rfl) ⟨2493089, by rfl⟩ : syracuseStep 3324119 = 4986179) B4986179
theorem B2216079 : Blo 2215435 2216079 := bstep (se 1 (by rfl) ⟨1662059, by rfl⟩ : syracuseStep 2216079 = 3324119) B3324119
theorem B3324125 : Blo 2215435 3324125 := bbase (se 3 (by rfl) ⟨623273, by rfl⟩ : syracuseStep 3324125 = 1246547) (by norm_num)
theorem B2216083 : Blo 2215435 2216083 := bstep (se 1 (by rfl) ⟨1662062, by rfl⟩ : syracuseStep 2216083 = 3324125) B3324125
theorem B4986197 : Blo 2215435 4986197 := bbase (se 14 (by rfl) ⟨456, by rfl⟩ : syracuseStep 4986197 = 913) (by norm_num)
theorem B3324131 : Blo 2215435 3324131 := bstep (se 1 (by rfl) ⟨2493098, by rfl⟩ : syracuseStep 3324131 = 4986197) B4986197
theorem B2216087 : Blo 2215435 2216087 := bstep (se 1 (by rfl) ⟨1662065, by rfl⟩ : syracuseStep 2216087 = 3324131) B3324131
theorem B2366501 : Blo 2215435 2366501 := bbase (se 4 (by rfl) ⟨221859, by rfl⟩ : syracuseStep 2366501 = 443719) (by norm_num)
theorem B6310669 : Blo 2215435 6310669 := bstep (se 3 (by rfl) ⟨1183250, by rfl⟩ : syracuseStep 6310669 = 2366501) B2366501
theorem B8414225 : Blo 2215435 8414225 := bstep (se 2 (by rfl) ⟨3155334, by rfl⟩ : syracuseStep 8414225 = 6310669) B6310669
theorem B5609483 : Blo 2215435 5609483 := bstep (se 1 (by rfl) ⟨4207112, by rfl⟩ : syracuseStep 5609483 = 8414225) B8414225
theorem B3739655 : Blo 2215435 3739655 := bstep (se 1 (by rfl) ⟨2804741, by rfl⟩ : syracuseStep 3739655 = 5609483) B5609483
theorem B2493103 : Blo 2215435 2493103 := bstep (se 1 (by rfl) ⟨1869827, by rfl⟩ : syracuseStep 2493103 = 3739655) B3739655
theorem B3324137 : Blo 2215435 3324137 := bstep (se 2 (by rfl) ⟨1246551, by rfl⟩ : syracuseStep 3324137 = 2493103) B2493103
theorem B2216091 : Blo 2215435 2216091 := bstep (se 1 (by rfl) ⟨1662068, by rfl⟩ : syracuseStep 2216091 = 3324137) B3324137
theorem B8095925 : Blo 2215435 8095925 := bbase (se 5 (by rfl) ⟨379496, by rfl⟩ : syracuseStep 8095925 = 758993) (by norm_num)
theorem B5397283 : Blo 2215435 5397283 := bstep (se 1 (by rfl) ⟨4047962, by rfl⟩ : syracuseStep 5397283 = 8095925) B8095925
theorem B7196377 : Blo 2215435 7196377 := bstep (se 2 (by rfl) ⟨2698641, by rfl⟩ : syracuseStep 7196377 = 5397283) B5397283
theorem B9595169 : Blo 2215435 9595169 := bstep (se 2 (by rfl) ⟨3598188, by rfl⟩ : syracuseStep 9595169 = 7196377) B7196377
theorem B6396779 : Blo 2215435 6396779 := bstep (se 1 (by rfl) ⟨4797584, by rfl⟩ : syracuseStep 6396779 = 9595169) B9595169
theorem B4264519 : Blo 2215435 4264519 := bstep (se 1 (by rfl) ⟨3198389, by rfl⟩ : syracuseStep 4264519 = 6396779) B6396779
theorem B90976405 : Blo 2215435 90976405 := bstep (se 6 (by rfl) ⟨2132259, by rfl⟩ : syracuseStep 90976405 = 4264519) B4264519
theorem B121301873 : Blo 2215435 121301873 := bstep (se 2 (by rfl) ⟨45488202, by rfl⟩ : syracuseStep 121301873 = 90976405) B90976405
theorem B80867915 : Blo 2215435 80867915 := bstep (se 1 (by rfl) ⟨60650936, by rfl⟩ : syracuseStep 80867915 = 121301873) B121301873
theorem B53911943 : Blo 2215435 53911943 := bstep (se 1 (by rfl) ⟨40433957, by rfl⟩ : syracuseStep 53911943 = 80867915) B80867915
theorem B35941295 : Blo 2215435 35941295 := bstep (se 1 (by rfl) ⟨26955971, by rfl⟩ : syracuseStep 35941295 = 53911943) B53911943
theorem B23960863 : Blo 2215435 23960863 := bstep (se 1 (by rfl) ⟨17970647, by rfl⟩ : syracuseStep 23960863 = 35941295) B35941295
theorem B31947817 : Blo 2215435 31947817 := bstep (se 2 (by rfl) ⟨11980431, by rfl⟩ : syracuseStep 31947817 = 23960863) B23960863
theorem B42597089 : Blo 2215435 42597089 := bstep (se 2 (by rfl) ⟨15973908, by rfl⟩ : syracuseStep 42597089 = 31947817) B31947817
theorem B28398059 : Blo 2215435 28398059 := bstep (se 1 (by rfl) ⟨21298544, by rfl⟩ : syracuseStep 28398059 = 42597089) B42597089
theorem B18932039 : Blo 2215435 18932039 := bstep (se 1 (by rfl) ⟨14199029, by rfl⟩ : syracuseStep 18932039 = 28398059) B28398059
theorem B12621359 : Blo 2215435 12621359 := bstep (se 1 (by rfl) ⟨9466019, by rfl⟩ : syracuseStep 12621359 = 18932039) B18932039
theorem B8414239 : Blo 2215435 8414239 := bstep (se 1 (by rfl) ⟨6310679, by rfl⟩ : syracuseStep 8414239 = 12621359) B12621359
theorem B11218985 : Blo 2215435 11218985 := bstep (se 2 (by rfl) ⟨4207119, by rfl⟩ : syracuseStep 11218985 = 8414239) B8414239
theorem B7479323 : Blo 2215435 7479323 := bstep (se 1 (by rfl) ⟨5609492, by rfl⟩ : syracuseStep 7479323 = 11218985) B11218985
theorem B4986215 : Blo 2215435 4986215 := bstep (se 1 (by rfl) ⟨3739661, by rfl⟩ : syracuseStep 4986215 = 7479323) B7479323
theorem B3324143 : Blo 2215435 3324143 := bstep (se 1 (by rfl) ⟨2493107, by rfl⟩ : syracuseStep 3324143 = 4986215) B4986215
theorem B2216095 : Blo 2215435 2216095 := bstep (se 1 (by rfl) ⟨1662071, by rfl⟩ : syracuseStep 2216095 = 3324143) B3324143
theorem B3324149 : Blo 2215435 3324149 := bbase (se 5 (by rfl) ⟨155819, by rfl⟩ : syracuseStep 3324149 = 311639) (by norm_num)
theorem B2216099 : Blo 2215435 2216099 := bstep (se 1 (by rfl) ⟨1662074, by rfl⟩ : syracuseStep 2216099 = 3324149) B3324149
theorem B7581397 : Blo 2215435 7581397 := bbase (se 7 (by rfl) ⟨88844, by rfl⟩ : syracuseStep 7581397 = 177689) (by norm_num)
theorem B10108529 : Blo 2215435 10108529 := bstep (se 2 (by rfl) ⟨3790698, by rfl⟩ : syracuseStep 10108529 = 7581397) B7581397
theorem B6739019 : Blo 2215435 6739019 := bstep (se 1 (by rfl) ⟨5054264, by rfl⟩ : syracuseStep 6739019 = 10108529) B10108529
theorem B4492679 : Blo 2215435 4492679 := bstep (se 1 (by rfl) ⟨3369509, by rfl⟩ : syracuseStep 4492679 = 6739019) B6739019
theorem B11980477 : Blo 2215435 11980477 := bstep (se 3 (by rfl) ⟨2246339, by rfl⟩ : syracuseStep 11980477 = 4492679) B4492679
theorem B15973969 : Blo 2215435 15973969 := bstep (se 2 (by rfl) ⟨5990238, by rfl⟩ : syracuseStep 15973969 = 11980477) B11980477
theorem B21298625 : Blo 2215435 21298625 := bstep (se 2 (by rfl) ⟨7986984, by rfl⟩ : syracuseStep 21298625 = 15973969) B15973969
theorem B14199083 : Blo 2215435 14199083 := bstep (se 1 (by rfl) ⟨10649312, by rfl⟩ : syracuseStep 14199083 = 21298625) B21298625
theorem B9466055 : Blo 2215435 9466055 := bstep (se 1 (by rfl) ⟨7099541, by rfl⟩ : syracuseStep 9466055 = 14199083) B14199083
theorem B6310703 : Blo 2215435 6310703 := bstep (se 1 (by rfl) ⟨4733027, by rfl⟩ : syracuseStep 6310703 = 9466055) B9466055
theorem B4207135 : Blo 2215435 4207135 := bstep (se 1 (by rfl) ⟨3155351, by rfl⟩ : syracuseStep 4207135 = 6310703) B6310703
theorem B5609513 : Blo 2215435 5609513 := bstep (se 2 (by rfl) ⟨2103567, by rfl⟩ : syracuseStep 5609513 = 4207135) B4207135
theorem B3739675 : Blo 2215435 3739675 := bstep (se 1 (by rfl) ⟨2804756, by rfl⟩ : syracuseStep 3739675 = 5609513) B5609513
theorem B4986233 : Blo 2215435 4986233 := bstep (se 2 (by rfl) ⟨1869837, by rfl⟩ : syracuseStep 4986233 = 3739675) B3739675
theorem B3324155 : Blo 2215435 3324155 := bstep (se 1 (by rfl) ⟨2493116, by rfl⟩ : syracuseStep 3324155 = 4986233) B4986233
theorem B2216103 : Blo 2215435 2216103 := bstep (se 1 (by rfl) ⟨1662077, by rfl⟩ : syracuseStep 2216103 = 3324155) B3324155
theorem B2493121 : Blo 2215435 2493121 := bbase (se 2 (by rfl) ⟨934920, by rfl⟩ : syracuseStep 2493121 = 1869841) (by norm_num)
theorem B3324161 : Blo 2215435 3324161 := bstep (se 2 (by rfl) ⟨1246560, by rfl⟩ : syracuseStep 3324161 = 2493121) B2493121
theorem B2216107 : Blo 2215435 2216107 := bstep (se 1 (by rfl) ⟨1662080, by rfl⟩ : syracuseStep 2216107 = 3324161) B3324161
theorem B5609533 : Blo 2215435 5609533 := bbase (se 3 (by rfl) ⟨1051787, by rfl⟩ : syracuseStep 5609533 = 2103575) (by norm_num)
theorem B7479377 : Blo 2215435 7479377 := bstep (se 2 (by rfl) ⟨2804766, by rfl⟩ : syracuseStep 7479377 = 5609533) B5609533
theorem B4986251 : Blo 2215435 4986251 := bstep (se 1 (by rfl) ⟨3739688, by rfl⟩ : syracuseStep 4986251 = 7479377) B7479377
theorem B3324167 : Blo 2215435 3324167 := bstep (se 1 (by rfl) ⟨2493125, by rfl⟩ : syracuseStep 3324167 = 4986251) B4986251
theorem B2216111 : Blo 2215435 2216111 := bstep (se 1 (by rfl) ⟨1662083, by rfl⟩ : syracuseStep 2216111 = 3324167) B3324167
theorem B3324173 : Blo 2215435 3324173 := bbase (se 3 (by rfl) ⟨623282, by rfl⟩ : syracuseStep 3324173 = 1246565) (by norm_num)
theorem B2216115 : Blo 2215435 2216115 := bstep (se 1 (by rfl) ⟨1662086, by rfl⟩ : syracuseStep 2216115 = 3324173) B3324173
theorem B4986269 : Blo 2215435 4986269 := bbase (se 3 (by rfl) ⟨934925, by rfl⟩ : syracuseStep 4986269 = 1869851) (by norm_num)
theorem B3324179 : Blo 2215435 3324179 := bstep (se 1 (by rfl) ⟨2493134, by rfl⟩ : syracuseStep 3324179 = 4986269) B4986269
theorem B2216119 : Blo 2215435 2216119 := bstep (se 1 (by rfl) ⟨1662089, by rfl⟩ : syracuseStep 2216119 = 3324179) B3324179
theorem B3739709 : Blo 2215435 3739709 := bbase (se 3 (by rfl) ⟨701195, by rfl⟩ : syracuseStep 3739709 = 1402391) (by norm_num)
theorem B2493139 : Blo 2215435 2493139 := bstep (se 1 (by rfl) ⟨1869854, by rfl⟩ : syracuseStep 2493139 = 3739709) B3739709
theorem B3324185 : Blo 2215435 3324185 := bstep (se 2 (by rfl) ⟨1246569, by rfl⟩ : syracuseStep 3324185 = 2493139) B2493139
theorem B2216123 : Blo 2215435 2216123 := bstep (se 1 (by rfl) ⟨1662092, by rfl⟩ : syracuseStep 2216123 = 3324185) B3324185
theorem B2662357 : Blo 2215435 2662357 := bbase (se 7 (by rfl) ⟨31199, by rfl⟩ : syracuseStep 2662357 = 62399) (by norm_num)
theorem B3549809 : Blo 2215435 3549809 := bstep (se 2 (by rfl) ⟨1331178, by rfl⟩ : syracuseStep 3549809 = 2662357) B2662357
theorem B2366539 : Blo 2215435 2366539 := bstep (se 1 (by rfl) ⟨1774904, by rfl⟩ : syracuseStep 2366539 = 3549809) B3549809
theorem B12621541 : Blo 2215435 12621541 := bstep (se 4 (by rfl) ⟨1183269, by rfl⟩ : syracuseStep 12621541 = 2366539) B2366539
theorem B16828721 : Blo 2215435 16828721 := bstep (se 2 (by rfl) ⟨6310770, by rfl⟩ : syracuseStep 16828721 = 12621541) B12621541
theorem B11219147 : Blo 2215435 11219147 := bstep (se 1 (by rfl) ⟨8414360, by rfl⟩ : syracuseStep 11219147 = 16828721) B16828721
theorem B7479431 : Blo 2215435 7479431 := bstep (se 1 (by rfl) ⟨5609573, by rfl⟩ : syracuseStep 7479431 = 11219147) B11219147
theorem B4986287 : Blo 2215435 4986287 := bstep (se 1 (by rfl) ⟨3739715, by rfl⟩ : syracuseStep 4986287 = 7479431) B7479431
theorem B3324191 : Blo 2215435 3324191 := bstep (se 1 (by rfl) ⟨2493143, by rfl⟩ : syracuseStep 3324191 = 4986287) B4986287
theorem B2216127 : Blo 2215435 2216127 := bstep (se 1 (by rfl) ⟨1662095, by rfl⟩ : syracuseStep 2216127 = 3324191) B3324191
theorem B3324197 : Blo 2215435 3324197 := bbase (se 4 (by rfl) ⟨311643, by rfl⟩ : syracuseStep 3324197 = 623287) (by norm_num)
theorem B2216131 : Blo 2215435 2216131 := bstep (se 1 (by rfl) ⟨1662098, by rfl⟩ : syracuseStep 2216131 = 3324197) B3324197
theorem B2804797 : Blo 2215435 2804797 := bbase (se 3 (by rfl) ⟨525899, by rfl⟩ : syracuseStep 2804797 = 1051799) (by norm_num)
theorem B3739729 : Blo 2215435 3739729 := bstep (se 2 (by rfl) ⟨1402398, by rfl⟩ : syracuseStep 3739729 = 2804797) B2804797
theorem B4986305 : Blo 2215435 4986305 := bstep (se 2 (by rfl) ⟨1869864, by rfl⟩ : syracuseStep 4986305 = 3739729) B3739729
theorem B3324203 : Blo 2215435 3324203 := bstep (se 1 (by rfl) ⟨2493152, by rfl⟩ : syracuseStep 3324203 = 4986305) B4986305
theorem B2216135 : Blo 2215435 2216135 := bstep (se 1 (by rfl) ⟨1662101, by rfl⟩ : syracuseStep 2216135 = 3324203) B3324203
theorem B2493157 : Blo 2215435 2493157 := bbase (se 4 (by rfl) ⟨233733, by rfl⟩ : syracuseStep 2493157 = 467467) (by norm_num)
theorem B3324209 : Blo 2215435 3324209 := bstep (se 2 (by rfl) ⟨1246578, by rfl⟩ : syracuseStep 3324209 = 2493157) B2493157
theorem B2216139 : Blo 2215435 2216139 := bstep (se 1 (by rfl) ⟨1662104, by rfl⟩ : syracuseStep 2216139 = 3324209) B3324209
theorem B3993565 : Blo 2215435 3993565 := bbase (se 3 (by rfl) ⟨748793, by rfl⟩ : syracuseStep 3993565 = 1497587) (by norm_num)
theorem B5324753 : Blo 2215435 5324753 := bstep (se 2 (by rfl) ⟨1996782, by rfl⟩ : syracuseStep 5324753 = 3993565) B3993565
theorem B3549835 : Blo 2215435 3549835 := bstep (se 1 (by rfl) ⟨2662376, by rfl⟩ : syracuseStep 3549835 = 5324753) B5324753
theorem B4733113 : Blo 2215435 4733113 := bstep (se 2 (by rfl) ⟨1774917, by rfl⟩ : syracuseStep 4733113 = 3549835) B3549835
theorem B6310817 : Blo 2215435 6310817 := bstep (se 2 (by rfl) ⟨2366556, by rfl⟩ : syracuseStep 6310817 = 4733113) B4733113
theorem B4207211 : Blo 2215435 4207211 := bstep (se 1 (by rfl) ⟨3155408, by rfl⟩ : syracuseStep 4207211 = 6310817) B6310817
theorem B2804807 : Blo 2215435 2804807 := bstep (se 1 (by rfl) ⟨2103605, by rfl⟩ : syracuseStep 2804807 = 4207211) B4207211
theorem B7479485 : Blo 2215435 7479485 := bstep (se 3 (by rfl) ⟨1402403, by rfl⟩ : syracuseStep 7479485 = 2804807) B2804807
theorem B4986323 : Blo 2215435 4986323 := bstep (se 1 (by rfl) ⟨3739742, by rfl⟩ : syracuseStep 4986323 = 7479485) B7479485
theorem B3324215 : Blo 2215435 3324215 := bstep (se 1 (by rfl) ⟨2493161, by rfl⟩ : syracuseStep 3324215 = 4986323) B4986323
theorem B2216143 : Blo 2215435 2216143 := bstep (se 1 (by rfl) ⟨1662107, by rfl⟩ : syracuseStep 2216143 = 3324215) B3324215
theorem B3324221 : Blo 2215435 3324221 := bbase (se 3 (by rfl) ⟨623291, by rfl⟩ : syracuseStep 3324221 = 1246583) (by norm_num)
theorem B2216147 : Blo 2215435 2216147 := bstep (se 1 (by rfl) ⟨1662110, by rfl⟩ : syracuseStep 2216147 = 3324221) B3324221
theorem B4986341 : Blo 2215435 4986341 := bbase (se 4 (by rfl) ⟨467469, by rfl⟩ : syracuseStep 4986341 = 934939) (by norm_num)
theorem B3324227 : Blo 2215435 3324227 := bstep (se 1 (by rfl) ⟨2493170, by rfl⟩ : syracuseStep 3324227 = 4986341) B4986341
theorem B2216151 : Blo 2215435 2216151 := bstep (se 1 (by rfl) ⟨1662113, by rfl⟩ : syracuseStep 2216151 = 3324227) B3324227
theorem B5609645 : Blo 2215435 5609645 := bbase (se 3 (by rfl) ⟨1051808, by rfl⟩ : syracuseStep 5609645 = 2103617) (by norm_num)
theorem B3739763 : Blo 2215435 3739763 := bstep (se 1 (by rfl) ⟨2804822, by rfl⟩ : syracuseStep 3739763 = 5609645) B5609645
theorem B2493175 : Blo 2215435 2493175 := bstep (se 1 (by rfl) ⟨1869881, by rfl⟩ : syracuseStep 2493175 = 3739763) B3739763
theorem B3324233 : Blo 2215435 3324233 := bstep (se 2 (by rfl) ⟨1246587, by rfl⟩ : syracuseStep 3324233 = 2493175) B2493175
theorem B2216155 : Blo 2215435 2216155 := bstep (se 1 (by rfl) ⟨1662116, by rfl⟩ : syracuseStep 2216155 = 3324233) B3324233
theorem B4264645 : Blo 2215435 4264645 := bbase (se 4 (by rfl) ⟨399810, by rfl⟩ : syracuseStep 4264645 = 799621) (by norm_num)
theorem B5686193 : Blo 2215435 5686193 := bstep (se 2 (by rfl) ⟨2132322, by rfl⟩ : syracuseStep 5686193 = 4264645) B4264645
theorem B3790795 : Blo 2215435 3790795 := bstep (se 1 (by rfl) ⟨2843096, by rfl⟩ : syracuseStep 3790795 = 5686193) B5686193
theorem B5054393 : Blo 2215435 5054393 := bstep (se 2 (by rfl) ⟨1895397, by rfl⟩ : syracuseStep 5054393 = 3790795) B3790795
theorem B3369595 : Blo 2215435 3369595 := bstep (se 1 (by rfl) ⟨2527196, by rfl⟩ : syracuseStep 3369595 = 5054393) B5054393
theorem B4492793 : Blo 2215435 4492793 := bstep (se 2 (by rfl) ⟨1684797, by rfl⟩ : syracuseStep 4492793 = 3369595) B3369595
theorem B11980781 : Blo 2215435 11980781 := bstep (se 3 (by rfl) ⟨2246396, by rfl⟩ : syracuseStep 11980781 = 4492793) B4492793
theorem B7987187 : Blo 2215435 7987187 := bstep (se 1 (by rfl) ⟨5990390, by rfl⟩ : syracuseStep 7987187 = 11980781) B11980781
theorem B5324791 : Blo 2215435 5324791 := bstep (se 1 (by rfl) ⟨3993593, by rfl⟩ : syracuseStep 5324791 = 7987187) B7987187
theorem B7099721 : Blo 2215435 7099721 := bstep (se 2 (by rfl) ⟨2662395, by rfl⟩ : syracuseStep 7099721 = 5324791) B5324791
theorem B4733147 : Blo 2215435 4733147 := bstep (se 1 (by rfl) ⟨3549860, by rfl⟩ : syracuseStep 4733147 = 7099721) B7099721
theorem B3155431 : Blo 2215435 3155431 := bstep (se 1 (by rfl) ⟨2366573, by rfl⟩ : syracuseStep 3155431 = 4733147) B4733147
theorem B4207241 : Blo 2215435 4207241 := bstep (se 2 (by rfl) ⟨1577715, by rfl⟩ : syracuseStep 4207241 = 3155431) B3155431
theorem B11219309 : Blo 2215435 11219309 := bstep (se 3 (by rfl) ⟨2103620, by rfl⟩ : syracuseStep 11219309 = 4207241) B4207241
theorem B7479539 : Blo 2215435 7479539 := bstep (se 1 (by rfl) ⟨5609654, by rfl⟩ : syracuseStep 7479539 = 11219309) B11219309
theorem B4986359 : Blo 2215435 4986359 := bstep (se 1 (by rfl) ⟨3739769, by rfl⟩ : syracuseStep 4986359 = 7479539) B7479539
theorem B3324239 : Blo 2215435 3324239 := bstep (se 1 (by rfl) ⟨2493179, by rfl⟩ : syracuseStep 3324239 = 4986359) B4986359
theorem B2216159 : Blo 2215435 2216159 := bstep (se 1 (by rfl) ⟨1662119, by rfl⟩ : syracuseStep 2216159 = 3324239) B3324239
theorem B3324245 : Blo 2215435 3324245 := bbase (se 10 (by rfl) ⟨4869, by rfl⟩ : syracuseStep 3324245 = 9739) (by norm_num)
theorem B2216163 : Blo 2215435 2216163 := bstep (se 1 (by rfl) ⟨1662122, by rfl⟩ : syracuseStep 2216163 = 3324245) B3324245
theorem B6310885 : Blo 2215435 6310885 := bbase (se 4 (by rfl) ⟨591645, by rfl⟩ : syracuseStep 6310885 = 1183291) (by norm_num)
theorem B8414513 : Blo 2215435 8414513 := bstep (se 2 (by rfl) ⟨3155442, by rfl⟩ : syracuseStep 8414513 = 6310885) B6310885
theorem B5609675 : Blo 2215435 5609675 := bstep (se 1 (by rfl) ⟨4207256, by rfl⟩ : syracuseStep 5609675 = 8414513) B8414513
theorem B3739783 : Blo 2215435 3739783 := bstep (se 1 (by rfl) ⟨2804837, by rfl⟩ : syracuseStep 3739783 = 5609675) B5609675
theorem B4986377 : Blo 2215435 4986377 := bstep (se 2 (by rfl) ⟨1869891, by rfl⟩ : syracuseStep 4986377 = 3739783) B3739783
theorem B3324251 : Blo 2215435 3324251 := bstep (se 1 (by rfl) ⟨2493188, by rfl⟩ : syracuseStep 3324251 = 4986377) B4986377
theorem B2216167 : Blo 2215435 2216167 := bstep (se 1 (by rfl) ⟨1662125, by rfl⟩ : syracuseStep 2216167 = 3324251) B3324251
theorem B2493193 : Blo 2215435 2493193 := bbase (se 2 (by rfl) ⟨934947, by rfl⟩ : syracuseStep 2493193 = 1869895) (by norm_num)
theorem B3324257 : Blo 2215435 3324257 := bstep (se 2 (by rfl) ⟨1246596, by rfl⟩ : syracuseStep 3324257 = 2493193) B2493193
theorem B2216171 : Blo 2215435 2216171 := bstep (se 1 (by rfl) ⟨1662128, by rfl⟩ : syracuseStep 2216171 = 3324257) B3324257
theorem B6739237 : Blo 2215435 6739237 := bbase (se 4 (by rfl) ⟨631803, by rfl⟩ : syracuseStep 6739237 = 1263607) (by norm_num)
theorem B8985649 : Blo 2215435 8985649 := bstep (se 2 (by rfl) ⟨3369618, by rfl⟩ : syracuseStep 8985649 = 6739237) B6739237
theorem B11980865 : Blo 2215435 11980865 := bstep (se 2 (by rfl) ⟨4492824, by rfl⟩ : syracuseStep 11980865 = 8985649) B8985649
theorem B7987243 : Blo 2215435 7987243 := bstep (se 1 (by rfl) ⟨5990432, by rfl⟩ : syracuseStep 7987243 = 11980865) B11980865
theorem B10649657 : Blo 2215435 10649657 := bstep (se 2 (by rfl) ⟨3993621, by rfl⟩ : syracuseStep 10649657 = 7987243) B7987243
theorem B28399085 : Blo 2215435 28399085 := bstep (se 3 (by rfl) ⟨5324828, by rfl⟩ : syracuseStep 28399085 = 10649657) B10649657
theorem B18932723 : Blo 2215435 18932723 := bstep (se 1 (by rfl) ⟨14199542, by rfl⟩ : syracuseStep 18932723 = 28399085) B28399085
theorem B12621815 : Blo 2215435 12621815 := bstep (se 1 (by rfl) ⟨9466361, by rfl⟩ : syracuseStep 12621815 = 18932723) B18932723
theorem B8414543 : Blo 2215435 8414543 := bstep (se 1 (by rfl) ⟨6310907, by rfl⟩ : syracuseStep 8414543 = 12621815) B12621815
theorem B5609695 : Blo 2215435 5609695 := bstep (se 1 (by rfl) ⟨4207271, by rfl⟩ : syracuseStep 5609695 = 8414543) B8414543
theorem B7479593 : Blo 2215435 7479593 := bstep (se 2 (by rfl) ⟨2804847, by rfl⟩ : syracuseStep 7479593 = 5609695) B5609695
theorem B4986395 : Blo 2215435 4986395 := bstep (se 1 (by rfl) ⟨3739796, by rfl⟩ : syracuseStep 4986395 = 7479593) B7479593
theorem B3324263 : Blo 2215435 3324263 := bstep (se 1 (by rfl) ⟨2493197, by rfl⟩ : syracuseStep 3324263 = 4986395) B4986395
theorem B2216175 : Blo 2215435 2216175 := bstep (se 1 (by rfl) ⟨1662131, by rfl⟩ : syracuseStep 2216175 = 3324263) B3324263
theorem B3324269 : Blo 2215435 3324269 := bbase (se 3 (by rfl) ⟨623300, by rfl⟩ : syracuseStep 3324269 = 1246601) (by norm_num)
theorem B2216179 : Blo 2215435 2216179 := bstep (se 1 (by rfl) ⟨1662134, by rfl⟩ : syracuseStep 2216179 = 3324269) B3324269
theorem B4986413 : Blo 2215435 4986413 := bbase (se 3 (by rfl) ⟨934952, by rfl⟩ : syracuseStep 4986413 = 1869905) (by norm_num)
theorem B3324275 : Blo 2215435 3324275 := bstep (se 1 (by rfl) ⟨2493206, by rfl⟩ : syracuseStep 3324275 = 4986413) B4986413
theorem B2216183 : Blo 2215435 2216183 := bstep (se 1 (by rfl) ⟨1662137, by rfl⟩ : syracuseStep 2216183 = 3324275) B3324275
theorem B5397509 : Blo 2215435 5397509 := bbase (se 4 (by rfl) ⟨506016, by rfl⟩ : syracuseStep 5397509 = 1012033) (by norm_num)
theorem B3598339 : Blo 2215435 3598339 := bstep (se 1 (by rfl) ⟨2698754, by rfl⟩ : syracuseStep 3598339 = 5397509) B5397509
theorem B4797785 : Blo 2215435 4797785 := bstep (se 2 (by rfl) ⟨1799169, by rfl⟩ : syracuseStep 4797785 = 3598339) B3598339
theorem B12794093 : Blo 2215435 12794093 := bstep (se 3 (by rfl) ⟨2398892, by rfl⟩ : syracuseStep 12794093 = 4797785) B4797785
theorem B8529395 : Blo 2215435 8529395 := bstep (se 1 (by rfl) ⟨6397046, by rfl⟩ : syracuseStep 8529395 = 12794093) B12794093
theorem B22745053 : Blo 2215435 22745053 := bstep (se 3 (by rfl) ⟨4264697, by rfl⟩ : syracuseStep 22745053 = 8529395) B8529395
theorem B30326737 : Blo 2215435 30326737 := bstep (se 2 (by rfl) ⟨11372526, by rfl⟩ : syracuseStep 30326737 = 22745053) B22745053
theorem B40435649 : Blo 2215435 40435649 := bstep (se 2 (by rfl) ⟨15163368, by rfl⟩ : syracuseStep 40435649 = 30326737) B30326737
theorem B26957099 : Blo 2215435 26957099 := bstep (se 1 (by rfl) ⟨20217824, by rfl⟩ : syracuseStep 26957099 = 40435649) B40435649
theorem B17971399 : Blo 2215435 17971399 := bstep (se 1 (by rfl) ⟨13478549, by rfl⟩ : syracuseStep 17971399 = 26957099) B26957099
theorem B23961865 : Blo 2215435 23961865 := bstep (se 2 (by rfl) ⟨8985699, by rfl⟩ : syracuseStep 23961865 = 17971399) B17971399
theorem B31949153 : Blo 2215435 31949153 := bstep (se 2 (by rfl) ⟨11980932, by rfl⟩ : syracuseStep 31949153 = 23961865) B23961865
theorem B21299435 : Blo 2215435 21299435 := bstep (se 1 (by rfl) ⟨15974576, by rfl⟩ : syracuseStep 21299435 = 31949153) B31949153
theorem B14199623 : Blo 2215435 14199623 := bstep (se 1 (by rfl) ⟨10649717, by rfl⟩ : syracuseStep 14199623 = 21299435) B21299435
theorem B9466415 : Blo 2215435 9466415 := bstep (se 1 (by rfl) ⟨7099811, by rfl⟩ : syracuseStep 9466415 = 14199623) B14199623
theorem B6310943 : Blo 2215435 6310943 := bstep (se 1 (by rfl) ⟨4733207, by rfl⟩ : syracuseStep 6310943 = 9466415) B9466415
theorem B4207295 : Blo 2215435 4207295 := bstep (se 1 (by rfl) ⟨3155471, by rfl⟩ : syracuseStep 4207295 = 6310943) B6310943
theorem B2804863 : Blo 2215435 2804863 := bstep (se 1 (by rfl) ⟨2103647, by rfl⟩ : syracuseStep 2804863 = 4207295) B4207295
theorem B3739817 : Blo 2215435 3739817 := bstep (se 2 (by rfl) ⟨1402431, by rfl⟩ : syracuseStep 3739817 = 2804863) B2804863
theorem B2493211 : Blo 2215435 2493211 := bstep (se 1 (by rfl) ⟨1869908, by rfl⟩ : syracuseStep 2493211 = 3739817) B3739817
theorem B3324281 : Blo 2215435 3324281 := bstep (se 2 (by rfl) ⟨1246605, by rfl⟩ : syracuseStep 3324281 = 2493211) B2493211
theorem B2216187 : Blo 2215435 2216187 := bstep (se 1 (by rfl) ⟨1662140, by rfl⟩ : syracuseStep 2216187 = 3324281) B3324281
theorem B7987301 : Blo 2215435 7987301 := bbase (se 4 (by rfl) ⟨748809, by rfl⟩ : syracuseStep 7987301 = 1497619) (by norm_num)
theorem B5324867 : Blo 2215435 5324867 := bstep (se 1 (by rfl) ⟨3993650, by rfl⟩ : syracuseStep 5324867 = 7987301) B7987301
theorem B3549911 : Blo 2215435 3549911 := bstep (se 1 (by rfl) ⟨2662433, by rfl⟩ : syracuseStep 3549911 = 5324867) B5324867
theorem B37865717 : Blo 2215435 37865717 := bstep (se 5 (by rfl) ⟨1774955, by rfl⟩ : syracuseStep 37865717 = 3549911) B3549911
theorem B25243811 : Blo 2215435 25243811 := bstep (se 1 (by rfl) ⟨18932858, by rfl⟩ : syracuseStep 25243811 = 37865717) B37865717
theorem B16829207 : Blo 2215435 16829207 := bstep (se 1 (by rfl) ⟨12621905, by rfl⟩ : syracuseStep 16829207 = 25243811) B25243811
theorem B11219471 : Blo 2215435 11219471 := bstep (se 1 (by rfl) ⟨8414603, by rfl⟩ : syracuseStep 11219471 = 16829207) B16829207
theorem B7479647 : Blo 2215435 7479647 := bstep (se 1 (by rfl) ⟨5609735, by rfl⟩ : syracuseStep 7479647 = 11219471) B11219471
theorem B4986431 : Blo 2215435 4986431 := bstep (se 1 (by rfl) ⟨3739823, by rfl⟩ : syracuseStep 4986431 = 7479647) B7479647
theorem B3324287 : Blo 2215435 3324287 := bstep (se 1 (by rfl) ⟨2493215, by rfl⟩ : syracuseStep 3324287 = 4986431) B4986431
theorem B2216191 : Blo 2215435 2216191 := bstep (se 1 (by rfl) ⟨1662143, by rfl⟩ : syracuseStep 2216191 = 3324287) B3324287
theorem B3324293 : Blo 2215435 3324293 := bbase (se 4 (by rfl) ⟨311652, by rfl⟩ : syracuseStep 3324293 = 623305) (by norm_num)
theorem B2216195 : Blo 2215435 2216195 := bstep (se 1 (by rfl) ⟨1662146, by rfl⟩ : syracuseStep 2216195 = 3324293) B3324293
theorem B3739837 : Blo 2215435 3739837 := bbase (se 3 (by rfl) ⟨701219, by rfl⟩ : syracuseStep 3739837 = 1402439) (by norm_num)
theorem B4986449 : Blo 2215435 4986449 := bstep (se 2 (by rfl) ⟨1869918, by rfl⟩ : syracuseStep 4986449 = 3739837) B3739837
theorem B3324299 : Blo 2215435 3324299 := bstep (se 1 (by rfl) ⟨2493224, by rfl⟩ : syracuseStep 3324299 = 4986449) B4986449
theorem B2216199 : Blo 2215435 2216199 := bstep (se 1 (by rfl) ⟨1662149, by rfl⟩ : syracuseStep 2216199 = 3324299) B3324299
theorem B2493229 : Blo 2215435 2493229 := bbase (se 3 (by rfl) ⟨467480, by rfl⟩ : syracuseStep 2493229 = 934961) (by norm_num)
theorem B3324305 : Blo 2215435 3324305 := bstep (se 2 (by rfl) ⟨1246614, by rfl⟩ : syracuseStep 3324305 = 2493229) B2493229
theorem B2216203 : Blo 2215435 2216203 := bstep (se 1 (by rfl) ⟨1662152, by rfl⟩ : syracuseStep 2216203 = 3324305) B3324305
theorem B7479701 : Blo 2215435 7479701 := bbase (se 6 (by rfl) ⟨175305, by rfl⟩ : syracuseStep 7479701 = 350611) (by norm_num)
theorem B4986467 : Blo 2215435 4986467 := bstep (se 1 (by rfl) ⟨3739850, by rfl⟩ : syracuseStep 4986467 = 7479701) B7479701
theorem B3324311 : Blo 2215435 3324311 := bstep (se 1 (by rfl) ⟨2493233, by rfl⟩ : syracuseStep 3324311 = 4986467) B4986467
theorem B2216207 : Blo 2215435 2216207 := bstep (se 1 (by rfl) ⟨1662155, by rfl⟩ : syracuseStep 2216207 = 3324311) B3324311
theorem B3324317 : Blo 2215435 3324317 := bbase (se 3 (by rfl) ⟨623309, by rfl⟩ : syracuseStep 3324317 = 1246619) (by norm_num)
theorem B2216211 : Blo 2215435 2216211 := bstep (se 1 (by rfl) ⟨1662158, by rfl⟩ : syracuseStep 2216211 = 3324317) B3324317
theorem B4986485 : Blo 2215435 4986485 := bbase (se 5 (by rfl) ⟨233741, by rfl⟩ : syracuseStep 4986485 = 467483) (by norm_num)
theorem B3324323 : Blo 2215435 3324323 := bstep (se 1 (by rfl) ⟨2493242, by rfl⟩ : syracuseStep 3324323 = 4986485) B4986485
theorem B2216215 : Blo 2215435 2216215 := bstep (se 1 (by rfl) ⟨1662161, by rfl⟩ : syracuseStep 2216215 = 3324323) B3324323
theorem B8985829 : Blo 2215435 8985829 := bbase (se 4 (by rfl) ⟨842421, by rfl⟩ : syracuseStep 8985829 = 1684843) (by norm_num)
theorem B11981105 : Blo 2215435 11981105 := bstep (se 2 (by rfl) ⟨4492914, by rfl⟩ : syracuseStep 11981105 = 8985829) B8985829
theorem B7987403 : Blo 2215435 7987403 := bstep (se 1 (by rfl) ⟨5990552, by rfl⟩ : syracuseStep 7987403 = 11981105) B11981105
theorem B5324935 : Blo 2215435 5324935 := bstep (se 1 (by rfl) ⟨3993701, by rfl⟩ : syracuseStep 5324935 = 7987403) B7987403
theorem B7099913 : Blo 2215435 7099913 := bstep (se 2 (by rfl) ⟨2662467, by rfl⟩ : syracuseStep 7099913 = 5324935) B5324935
theorem B18933101 : Blo 2215435 18933101 := bstep (se 3 (by rfl) ⟨3549956, by rfl⟩ : syracuseStep 18933101 = 7099913) B7099913
theorem B12622067 : Blo 2215435 12622067 := bstep (se 1 (by rfl) ⟨9466550, by rfl⟩ : syracuseStep 12622067 = 18933101) B18933101
theorem B8414711 : Blo 2215435 8414711 := bstep (se 1 (by rfl) ⟨6311033, by rfl⟩ : syracuseStep 8414711 = 12622067) B12622067
theorem B5609807 : Blo 2215435 5609807 := bstep (se 1 (by rfl) ⟨4207355, by rfl⟩ : syracuseStep 5609807 = 8414711) B8414711
theorem B3739871 : Blo 2215435 3739871 := bstep (se 1 (by rfl) ⟨2804903, by rfl⟩ : syracuseStep 3739871 = 5609807) B5609807
theorem B2493247 : Blo 2215435 2493247 := bstep (se 1 (by rfl) ⟨1869935, by rfl⟩ : syracuseStep 2493247 = 3739871) B3739871
theorem B3324329 : Blo 2215435 3324329 := bstep (se 2 (by rfl) ⟨1246623, by rfl⟩ : syracuseStep 3324329 = 2493247) B2493247
theorem B2216219 : Blo 2215435 2216219 := bstep (se 1 (by rfl) ⟨1662164, by rfl⟩ : syracuseStep 2216219 = 3324329) B3324329
theorem B8414725 : Blo 2215435 8414725 := bbase (se 4 (by rfl) ⟨788880, by rfl⟩ : syracuseStep 8414725 = 1577761) (by norm_num)
theorem B11219633 : Blo 2215435 11219633 := bstep (se 2 (by rfl) ⟨4207362, by rfl⟩ : syracuseStep 11219633 = 8414725) B8414725
theorem B7479755 : Blo 2215435 7479755 := bstep (se 1 (by rfl) ⟨5609816, by rfl⟩ : syracuseStep 7479755 = 11219633) B11219633
theorem B4986503 : Blo 2215435 4986503 := bstep (se 1 (by rfl) ⟨3739877, by rfl⟩ : syracuseStep 4986503 = 7479755) B7479755
theorem B3324335 : Blo 2215435 3324335 := bstep (se 1 (by rfl) ⟨2493251, by rfl⟩ : syracuseStep 3324335 = 4986503) B4986503
theorem B2216223 : Blo 2215435 2216223 := bstep (se 1 (by rfl) ⟨1662167, by rfl⟩ : syracuseStep 2216223 = 3324335) B3324335
theorem B3324341 : Blo 2215435 3324341 := bbase (se 5 (by rfl) ⟨155828, by rfl⟩ : syracuseStep 3324341 = 311657) (by norm_num)
theorem B2216227 : Blo 2215435 2216227 := bstep (se 1 (by rfl) ⟨1662170, by rfl⟩ : syracuseStep 2216227 = 3324341) B3324341
theorem B5609837 : Blo 2215435 5609837 := bbase (se 3 (by rfl) ⟨1051844, by rfl⟩ : syracuseStep 5609837 = 2103689) (by norm_num)
theorem B3739891 : Blo 2215435 3739891 := bstep (se 1 (by rfl) ⟨2804918, by rfl⟩ : syracuseStep 3739891 = 5609837) B5609837
theorem B4986521 : Blo 2215435 4986521 := bstep (se 2 (by rfl) ⟨1869945, by rfl⟩ : syracuseStep 4986521 = 3739891) B3739891
theorem B3324347 : Blo 2215435 3324347 := bstep (se 1 (by rfl) ⟨2493260, by rfl⟩ : syracuseStep 3324347 = 4986521) B4986521
theorem B2216231 : Blo 2215435 2216231 := bstep (se 1 (by rfl) ⟨1662173, by rfl⟩ : syracuseStep 2216231 = 3324347) B3324347
theorem B2493265 : Blo 2215435 2493265 := bbase (se 2 (by rfl) ⟨934974, by rfl⟩ : syracuseStep 2493265 = 1869949) (by norm_num)
theorem B3324353 : Blo 2215435 3324353 := bstep (se 2 (by rfl) ⟨1246632, by rfl⟩ : syracuseStep 3324353 = 2493265) B2493265
theorem B2216235 : Blo 2215435 2216235 := bstep (se 1 (by rfl) ⟨1662176, by rfl⟩ : syracuseStep 2216235 = 3324353) B3324353
theorem B3549989 : Blo 2215435 3549989 := bbase (se 4 (by rfl) ⟨332811, by rfl⟩ : syracuseStep 3549989 = 665623) (by norm_num)
theorem B2366659 : Blo 2215435 2366659 := bstep (se 1 (by rfl) ⟨1774994, by rfl⟩ : syracuseStep 2366659 = 3549989) B3549989
theorem B3155545 : Blo 2215435 3155545 := bstep (se 2 (by rfl) ⟨1183329, by rfl⟩ : syracuseStep 3155545 = 2366659) B2366659
theorem B4207393 : Blo 2215435 4207393 := bstep (se 2 (by rfl) ⟨1577772, by rfl⟩ : syracuseStep 4207393 = 3155545) B3155545
theorem B5609857 : Blo 2215435 5609857 := bstep (se 2 (by rfl) ⟨2103696, by rfl⟩ : syracuseStep 5609857 = 4207393) B4207393
theorem B7479809 : Blo 2215435 7479809 := bstep (se 2 (by rfl) ⟨2804928, by rfl⟩ : syracuseStep 7479809 = 5609857) B5609857
theorem B4986539 : Blo 2215435 4986539 := bstep (se 1 (by rfl) ⟨3739904, by rfl⟩ : syracuseStep 4986539 = 7479809) B7479809
theorem B3324359 : Blo 2215435 3324359 := bstep (se 1 (by rfl) ⟨2493269, by rfl⟩ : syracuseStep 3324359 = 4986539) B4986539
theorem B2216239 : Blo 2215435 2216239 := bstep (se 1 (by rfl) ⟨1662179, by rfl⟩ : syracuseStep 2216239 = 3324359) B3324359
theorem B3324365 : Blo 2215435 3324365 := bbase (se 3 (by rfl) ⟨623318, by rfl⟩ : syracuseStep 3324365 = 1246637) (by norm_num)
theorem B2216243 : Blo 2215435 2216243 := bstep (se 1 (by rfl) ⟨1662182, by rfl⟩ : syracuseStep 2216243 = 3324365) B3324365
theorem B4986557 : Blo 2215435 4986557 := bbase (se 3 (by rfl) ⟨934979, by rfl⟩ : syracuseStep 4986557 = 1869959) (by norm_num)
theorem B3324371 : Blo 2215435 3324371 := bstep (se 1 (by rfl) ⟨2493278, by rfl⟩ : syracuseStep 3324371 = 4986557) B4986557
theorem B2216247 : Blo 2215435 2216247 := bstep (se 1 (by rfl) ⟨1662185, by rfl⟩ : syracuseStep 2216247 = 3324371) B3324371
theorem B3739925 : Blo 2215435 3739925 := bbase (se 6 (by rfl) ⟨87654, by rfl⟩ : syracuseStep 3739925 = 175309) (by norm_num)
theorem B2493283 : Blo 2215435 2493283 := bstep (se 1 (by rfl) ⟨1869962, by rfl⟩ : syracuseStep 2493283 = 3739925) B3739925
theorem B3324377 : Blo 2215435 3324377 := bstep (se 2 (by rfl) ⟨1246641, by rfl⟩ : syracuseStep 3324377 = 2493283) B2493283
theorem B2216251 : Blo 2215435 2216251 := bstep (se 1 (by rfl) ⟨1662188, by rfl⟩ : syracuseStep 2216251 = 3324377) B3324377
theorem B8985973 : Blo 2215435 8985973 := bbase (se 5 (by rfl) ⟨421217, by rfl⟩ : syracuseStep 8985973 = 842435) (by norm_num)
theorem B11981297 : Blo 2215435 11981297 := bstep (se 2 (by rfl) ⟨4492986, by rfl⟩ : syracuseStep 11981297 = 8985973) B8985973
theorem B31950125 : Blo 2215435 31950125 := bstep (se 3 (by rfl) ⟨5990648, by rfl⟩ : syracuseStep 31950125 = 11981297) B11981297
theorem B21300083 : Blo 2215435 21300083 := bstep (se 1 (by rfl) ⟨15975062, by rfl⟩ : syracuseStep 21300083 = 31950125) B31950125
theorem B14200055 : Blo 2215435 14200055 := bstep (se 1 (by rfl) ⟨10650041, by rfl⟩ : syracuseStep 14200055 = 21300083) B21300083
theorem B9466703 : Blo 2215435 9466703 := bstep (se 1 (by rfl) ⟨7100027, by rfl⟩ : syracuseStep 9466703 = 14200055) B14200055
theorem B6311135 : Blo 2215435 6311135 := bstep (se 1 (by rfl) ⟨4733351, by rfl⟩ : syracuseStep 6311135 = 9466703) B9466703
theorem B16829693 : Blo 2215435 16829693 := bstep (se 3 (by rfl) ⟨3155567, by rfl⟩ : syracuseStep 16829693 = 6311135) B6311135
theorem B11219795 : Blo 2215435 11219795 := bstep (se 1 (by rfl) ⟨8414846, by rfl⟩ : syracuseStep 11219795 = 16829693) B16829693
theorem B7479863 : Blo 2215435 7479863 := bstep (se 1 (by rfl) ⟨5609897, by rfl⟩ : syracuseStep 7479863 = 11219795) B11219795
theorem B4986575 : Blo 2215435 4986575 := bstep (se 1 (by rfl) ⟨3739931, by rfl⟩ : syracuseStep 4986575 = 7479863) B7479863
theorem B3324383 : Blo 2215435 3324383 := bstep (se 1 (by rfl) ⟨2493287, by rfl⟩ : syracuseStep 3324383 = 4986575) B4986575
theorem B2216255 : Blo 2215435 2216255 := bstep (se 1 (by rfl) ⟨1662191, by rfl⟩ : syracuseStep 2216255 = 3324383) B3324383
theorem B3324389 : Blo 2215435 3324389 := bbase (se 4 (by rfl) ⟨311661, by rfl⟩ : syracuseStep 3324389 = 623323) (by norm_num)
theorem B2216259 : Blo 2215435 2216259 := bstep (se 1 (by rfl) ⟨1662194, by rfl⟩ : syracuseStep 2216259 = 3324389) B3324389
theorem B3993781 : Blo 2215435 3993781 := bbase (se 5 (by rfl) ⟨187208, by rfl⟩ : syracuseStep 3993781 = 374417) (by norm_num)
theorem B5325041 : Blo 2215435 5325041 := bstep (se 2 (by rfl) ⟨1996890, by rfl⟩ : syracuseStep 5325041 = 3993781) B3993781
theorem B14200109 : Blo 2215435 14200109 := bstep (se 3 (by rfl) ⟨2662520, by rfl⟩ : syracuseStep 14200109 = 5325041) B5325041
theorem B9466739 : Blo 2215435 9466739 := bstep (se 1 (by rfl) ⟨7100054, by rfl⟩ : syracuseStep 9466739 = 14200109) B14200109
theorem B6311159 : Blo 2215435 6311159 := bstep (se 1 (by rfl) ⟨4733369, by rfl⟩ : syracuseStep 6311159 = 9466739) B9466739
theorem B4207439 : Blo 2215435 4207439 := bstep (se 1 (by rfl) ⟨3155579, by rfl⟩ : syracuseStep 4207439 = 6311159) B6311159
theorem B2804959 : Blo 2215435 2804959 := bstep (se 1 (by rfl) ⟨2103719, by rfl⟩ : syracuseStep 2804959 = 4207439) B4207439
theorem B3739945 : Blo 2215435 3739945 := bstep (se 2 (by rfl) ⟨1402479, by rfl⟩ : syracuseStep 3739945 = 2804959) B2804959
theorem B4986593 : Blo 2215435 4986593 := bstep (se 2 (by rfl) ⟨1869972, by rfl⟩ : syracuseStep 4986593 = 3739945) B3739945
theorem B3324395 : Blo 2215435 3324395 := bstep (se 1 (by rfl) ⟨2493296, by rfl⟩ : syracuseStep 3324395 = 4986593) B4986593
theorem B2216263 : Blo 2215435 2216263 := bstep (se 1 (by rfl) ⟨1662197, by rfl⟩ : syracuseStep 2216263 = 3324395) B3324395
theorem B2493301 : Blo 2215435 2493301 := bbase (se 5 (by rfl) ⟨116873, by rfl⟩ : syracuseStep 2493301 = 233747) (by norm_num)
theorem B3324401 : Blo 2215435 3324401 := bstep (se 2 (by rfl) ⟨1246650, by rfl⟩ : syracuseStep 3324401 = 2493301) B2493301
theorem B2216267 : Blo 2215435 2216267 := bstep (se 1 (by rfl) ⟨1662200, by rfl⟩ : syracuseStep 2216267 = 3324401) B3324401
theorem B2804969 : Blo 2215435 2804969 := bbase (se 2 (by rfl) ⟨1051863, by rfl⟩ : syracuseStep 2804969 = 2103727) (by norm_num)
theorem B7479917 : Blo 2215435 7479917 := bstep (se 3 (by rfl) ⟨1402484, by rfl⟩ : syracuseStep 7479917 = 2804969) B2804969
theorem B4986611 : Blo 2215435 4986611 := bstep (se 1 (by rfl) ⟨3739958, by rfl⟩ : syracuseStep 4986611 = 7479917) B7479917
theorem B3324407 : Blo 2215435 3324407 := bstep (se 1 (by rfl) ⟨2493305, by rfl⟩ : syracuseStep 3324407 = 4986611) B4986611
theorem B2216271 : Blo 2215435 2216271 := bstep (se 1 (by rfl) ⟨1662203, by rfl⟩ : syracuseStep 2216271 = 3324407) B3324407
theorem B3324413 : Blo 2215435 3324413 := bbase (se 3 (by rfl) ⟨623327, by rfl⟩ : syracuseStep 3324413 = 1246655) (by norm_num)
theorem B2216275 : Blo 2215435 2216275 := bstep (se 1 (by rfl) ⟨1662206, by rfl⟩ : syracuseStep 2216275 = 3324413) B3324413
theorem B4986629 : Blo 2215435 4986629 := bbase (se 4 (by rfl) ⟨467496, by rfl⟩ : syracuseStep 4986629 = 934993) (by norm_num)
theorem B3324419 : Blo 2215435 3324419 := bstep (se 1 (by rfl) ⟨2493314, by rfl⟩ : syracuseStep 3324419 = 4986629) B4986629
theorem B2216279 : Blo 2215435 2216279 := bstep (se 1 (by rfl) ⟨1662209, by rfl⟩ : syracuseStep 2216279 = 3324419) B3324419
theorem B4207477 : Blo 2215435 4207477 := bbase (se 5 (by rfl) ⟨197225, by rfl⟩ : syracuseStep 4207477 = 394451) (by norm_num)
theorem B5609969 : Blo 2215435 5609969 := bstep (se 2 (by rfl) ⟨2103738, by rfl⟩ : syracuseStep 5609969 = 4207477) B4207477
theorem B3739979 : Blo 2215435 3739979 := bstep (se 1 (by rfl) ⟨2804984, by rfl⟩ : syracuseStep 3739979 = 5609969) B5609969
theorem B2493319 : Blo 2215435 2493319 := bstep (se 1 (by rfl) ⟨1869989, by rfl⟩ : syracuseStep 2493319 = 3739979) B3739979
theorem B3324425 : Blo 2215435 3324425 := bstep (se 2 (by rfl) ⟨1246659, by rfl⟩ : syracuseStep 3324425 = 2493319) B2493319
theorem B2216283 : Blo 2215435 2216283 := bstep (se 1 (by rfl) ⟨1662212, by rfl⟩ : syracuseStep 2216283 = 3324425) B3324425
theorem B11219957 : Blo 2215435 11219957 := bbase (se 5 (by rfl) ⟨525935, by rfl⟩ : syracuseStep 11219957 = 1051871) (by norm_num)
theorem B7479971 : Blo 2215435 7479971 := bstep (se 1 (by rfl) ⟨5609978, by rfl⟩ : syracuseStep 7479971 = 11219957) B11219957
theorem B4986647 : Blo 2215435 4986647 := bstep (se 1 (by rfl) ⟨3739985, by rfl⟩ : syracuseStep 4986647 = 7479971) B7479971
theorem B3324431 : Blo 2215435 3324431 := bstep (se 1 (by rfl) ⟨2493323, by rfl⟩ : syracuseStep 3324431 = 4986647) B4986647
theorem B2216287 : Blo 2215435 2216287 := bstep (se 1 (by rfl) ⟨1662215, by rfl⟩ : syracuseStep 2216287 = 3324431) B3324431
theorem B3324437 : Blo 2215435 3324437 := bbase (se 6 (by rfl) ⟨77916, by rfl⟩ : syracuseStep 3324437 = 155833) (by norm_num)
theorem B2216291 : Blo 2215435 2216291 := bstep (se 1 (by rfl) ⟨1662218, by rfl⟩ : syracuseStep 2216291 = 3324437) B3324437
theorem B18933749 : Blo 2215435 18933749 := bbase (se 5 (by rfl) ⟨887519, by rfl⟩ : syracuseStep 18933749 = 1775039) (by norm_num)
theorem B12622499 : Blo 2215435 12622499 := bstep (se 1 (by rfl) ⟨9466874, by rfl⟩ : syracuseStep 12622499 = 18933749) B18933749
theorem B8414999 : Blo 2215435 8414999 := bstep (se 1 (by rfl) ⟨6311249, by rfl⟩ : syracuseStep 8414999 = 12622499) B12622499
theorem B5609999 : Blo 2215435 5609999 := bstep (se 1 (by rfl) ⟨4207499, by rfl⟩ : syracuseStep 5609999 = 8414999) B8414999
theorem B3739999 : Blo 2215435 3739999 := bstep (se 1 (by rfl) ⟨2804999, by rfl⟩ : syracuseStep 3739999 = 5609999) B5609999
theorem B4986665 : Blo 2215435 4986665 := bstep (se 2 (by rfl) ⟨1869999, by rfl⟩ : syracuseStep 4986665 = 3739999) B3739999
theorem B3324443 : Blo 2215435 3324443 := bstep (se 1 (by rfl) ⟨2493332, by rfl⟩ : syracuseStep 3324443 = 4986665) B4986665
theorem B2216295 : Blo 2215435 2216295 := bstep (se 1 (by rfl) ⟨1662221, by rfl⟩ : syracuseStep 2216295 = 3324443) B3324443
theorem B2493337 : Blo 2215435 2493337 := bbase (se 2 (by rfl) ⟨935001, by rfl⟩ : syracuseStep 2493337 = 1870003) (by norm_num)
theorem B3324449 : Blo 2215435 3324449 := bstep (se 2 (by rfl) ⟨1246668, by rfl⟩ : syracuseStep 3324449 = 2493337) B2493337
theorem B2216299 : Blo 2215435 2216299 := bstep (se 1 (by rfl) ⟨1662224, by rfl⟩ : syracuseStep 2216299 = 3324449) B3324449
theorem B8415029 : Blo 2215435 8415029 := bbase (se 5 (by rfl) ⟨394454, by rfl⟩ : syracuseStep 8415029 = 788909) (by norm_num)
theorem B5610019 : Blo 2215435 5610019 := bstep (se 1 (by rfl) ⟨4207514, by rfl⟩ : syracuseStep 5610019 = 8415029) B8415029
theorem B7480025 : Blo 2215435 7480025 := bstep (se 2 (by rfl) ⟨2805009, by rfl⟩ : syracuseStep 7480025 = 5610019) B5610019
theorem B4986683 : Blo 2215435 4986683 := bstep (se 1 (by rfl) ⟨3740012, by rfl⟩ : syracuseStep 4986683 = 7480025) B7480025
theorem B3324455 : Blo 2215435 3324455 := bstep (se 1 (by rfl) ⟨2493341, by rfl⟩ : syracuseStep 3324455 = 4986683) B4986683
theorem B2216303 : Blo 2215435 2216303 := bstep (se 1 (by rfl) ⟨1662227, by rfl⟩ : syracuseStep 2216303 = 3324455) B3324455
theorem B3324461 : Blo 2215435 3324461 := bbase (se 3 (by rfl) ⟨623336, by rfl⟩ : syracuseStep 3324461 = 1246673) (by norm_num)
theorem B2216307 : Blo 2215435 2216307 := bstep (se 1 (by rfl) ⟨1662230, by rfl⟩ : syracuseStep 2216307 = 3324461) B3324461
theorem B4986701 : Blo 2215435 4986701 := bbase (se 3 (by rfl) ⟨935006, by rfl⟩ : syracuseStep 4986701 = 1870013) (by norm_num)
theorem B3324467 : Blo 2215435 3324467 := bstep (se 1 (by rfl) ⟨2493350, by rfl⟩ : syracuseStep 3324467 = 4986701) B4986701
theorem B2216311 : Blo 2215435 2216311 := bstep (se 1 (by rfl) ⟨1662233, by rfl⟩ : syracuseStep 2216311 = 3324467) B3324467
theorem B2805025 : Blo 2215435 2805025 := bbase (se 2 (by rfl) ⟨1051884, by rfl⟩ : syracuseStep 2805025 = 2103769) (by norm_num)
theorem B3740033 : Blo 2215435 3740033 := bstep (se 2 (by rfl) ⟨1402512, by rfl⟩ : syracuseStep 3740033 = 2805025) B2805025
theorem B2493355 : Blo 2215435 2493355 := bstep (se 1 (by rfl) ⟨1870016, by rfl⟩ : syracuseStep 2493355 = 3740033) B3740033
theorem B3324473 : Blo 2215435 3324473 := bstep (se 2 (by rfl) ⟨1246677, by rfl⟩ : syracuseStep 3324473 = 2493355) B2493355
theorem B2216315 : Blo 2215435 2216315 := bstep (se 1 (by rfl) ⟨1662236, by rfl⟩ : syracuseStep 2216315 = 3324473) B3324473
theorem B25245269 : Blo 2215435 25245269 := bbase (se 8 (by rfl) ⟨147921, by rfl⟩ : syracuseStep 25245269 = 295843) (by norm_num)
theorem B16830179 : Blo 2215435 16830179 := bstep (se 1 (by rfl) ⟨12622634, by rfl⟩ : syracuseStep 16830179 = 25245269) B25245269
theorem B11220119 : Blo 2215435 11220119 := bstep (se 1 (by rfl) ⟨8415089, by rfl⟩ : syracuseStep 11220119 = 16830179) B16830179
theorem B7480079 : Blo 2215435 7480079 := bstep (se 1 (by rfl) ⟨5610059, by rfl⟩ : syracuseStep 7480079 = 11220119) B11220119
theorem B4986719 : Blo 2215435 4986719 := bstep (se 1 (by rfl) ⟨3740039, by rfl⟩ : syracuseStep 4986719 = 7480079) B7480079
theorem B3324479 : Blo 2215435 3324479 := bstep (se 1 (by rfl) ⟨2493359, by rfl⟩ : syracuseStep 3324479 = 4986719) B4986719
theorem B2216319 : Blo 2215435 2216319 := bstep (se 1 (by rfl) ⟨1662239, by rfl⟩ : syracuseStep 2216319 = 3324479) B3324479
theorem B3324485 : Blo 2215435 3324485 := bbase (se 4 (by rfl) ⟨311670, by rfl⟩ : syracuseStep 3324485 = 623341) (by norm_num)
theorem B2216323 : Blo 2215435 2216323 := bstep (se 1 (by rfl) ⟨1662242, by rfl⟩ : syracuseStep 2216323 = 3324485) B3324485
theorem B3740053 : Blo 2215435 3740053 := bbase (se 6 (by rfl) ⟨87657, by rfl⟩ : syracuseStep 3740053 = 175315) (by norm_num)
theorem B4986737 : Blo 2215435 4986737 := bstep (se 2 (by rfl) ⟨1870026, by rfl⟩ : syracuseStep 4986737 = 3740053) B3740053
theorem B3324491 : Blo 2215435 3324491 := bstep (se 1 (by rfl) ⟨2493368, by rfl⟩ : syracuseStep 3324491 = 4986737) B4986737
theorem B2216327 : Blo 2215435 2216327 := bstep (se 1 (by rfl) ⟨1662245, by rfl⟩ : syracuseStep 2216327 = 3324491) B3324491
theorem B2493373 : Blo 2215435 2493373 := bbase (se 3 (by rfl) ⟨467507, by rfl⟩ : syracuseStep 2493373 = 935015) (by norm_num)
theorem B3324497 : Blo 2215435 3324497 := bstep (se 2 (by rfl) ⟨1246686, by rfl⟩ : syracuseStep 3324497 = 2493373) B2493373
theorem B2216331 : Blo 2215435 2216331 := bstep (se 1 (by rfl) ⟨1662248, by rfl⟩ : syracuseStep 2216331 = 3324497) B3324497
theorem B7480133 : Blo 2215435 7480133 := bbase (se 4 (by rfl) ⟨701262, by rfl⟩ : syracuseStep 7480133 = 1402525) (by norm_num)
theorem B4986755 : Blo 2215435 4986755 := bstep (se 1 (by rfl) ⟨3740066, by rfl⟩ : syracuseStep 4986755 = 7480133) B7480133
theorem B3324503 : Blo 2215435 3324503 := bstep (se 1 (by rfl) ⟨2493377, by rfl⟩ : syracuseStep 3324503 = 4986755) B4986755
theorem B2216335 : Blo 2215435 2216335 := bstep (se 1 (by rfl) ⟨1662251, by rfl⟩ : syracuseStep 2216335 = 3324503) B3324503
theorem B3324509 : Blo 2215435 3324509 := bbase (se 3 (by rfl) ⟨623345, by rfl⟩ : syracuseStep 3324509 = 1246691) (by norm_num)
theorem B2216339 : Blo 2215435 2216339 := bstep (se 1 (by rfl) ⟨1662254, by rfl⟩ : syracuseStep 2216339 = 3324509) B3324509
theorem B4986773 : Blo 2215435 4986773 := bbase (se 6 (by rfl) ⟨116877, by rfl⟩ : syracuseStep 4986773 = 233755) (by norm_num)
theorem B3324515 : Blo 2215435 3324515 := bstep (se 1 (by rfl) ⟨2493386, by rfl⟩ : syracuseStep 3324515 = 4986773) B4986773
theorem B2216343 : Blo 2215435 2216343 := bstep (se 1 (by rfl) ⟨1662257, by rfl⟩ : syracuseStep 2216343 = 3324515) B3324515
theorem B4733549 : Blo 2215435 4733549 := bbase (se 3 (by rfl) ⟨887540, by rfl⟩ : syracuseStep 4733549 = 1775081) (by norm_num)
theorem B3155699 : Blo 2215435 3155699 := bstep (se 1 (by rfl) ⟨2366774, by rfl⟩ : syracuseStep 3155699 = 4733549) B4733549
theorem B8415197 : Blo 2215435 8415197 := bstep (se 3 (by rfl) ⟨1577849, by rfl⟩ : syracuseStep 8415197 = 3155699) B3155699
theorem B5610131 : Blo 2215435 5610131 := bstep (se 1 (by rfl) ⟨4207598, by rfl⟩ : syracuseStep 5610131 = 8415197) B8415197
theorem B3740087 : Blo 2215435 3740087 := bstep (se 1 (by rfl) ⟨2805065, by rfl⟩ : syracuseStep 3740087 = 5610131) B5610131
theorem B2493391 : Blo 2215435 2493391 := bstep (se 1 (by rfl) ⟨1870043, by rfl⟩ : syracuseStep 2493391 = 3740087) B3740087
theorem B3324521 : Blo 2215435 3324521 := bstep (se 2 (by rfl) ⟨1246695, by rfl⟩ : syracuseStep 3324521 = 2493391) B2493391
theorem B2216347 : Blo 2215435 2216347 := bstep (se 1 (by rfl) ⟨1662260, by rfl⟩ : syracuseStep 2216347 = 3324521) B3324521
theorem B17972725 : Blo 2215435 17972725 := bbase (se 5 (by rfl) ⟨842471, by rfl⟩ : syracuseStep 17972725 = 1684943) (by norm_num)
theorem B23963633 : Blo 2215435 23963633 := bstep (se 2 (by rfl) ⟨8986362, by rfl⟩ : syracuseStep 23963633 = 17972725) B17972725
theorem B15975755 : Blo 2215435 15975755 := bstep (se 1 (by rfl) ⟨11981816, by rfl⟩ : syracuseStep 15975755 = 23963633) B23963633
theorem B10650503 : Blo 2215435 10650503 := bstep (se 1 (by rfl) ⟨7987877, by rfl⟩ : syracuseStep 10650503 = 15975755) B15975755
theorem B7100335 : Blo 2215435 7100335 := bstep (se 1 (by rfl) ⟨5325251, by rfl⟩ : syracuseStep 7100335 = 10650503) B10650503
theorem B9467113 : Blo 2215435 9467113 := bstep (se 2 (by rfl) ⟨3550167, by rfl⟩ : syracuseStep 9467113 = 7100335) B7100335
theorem B12622817 : Blo 2215435 12622817 := bstep (se 2 (by rfl) ⟨4733556, by rfl⟩ : syracuseStep 12622817 = 9467113) B9467113
theorem B8415211 : Blo 2215435 8415211 := bstep (se 1 (by rfl) ⟨6311408, by rfl⟩ : syracuseStep 8415211 = 12622817) B12622817
theorem B11220281 : Blo 2215435 11220281 := bstep (se 2 (by rfl) ⟨4207605, by rfl⟩ : syracuseStep 11220281 = 8415211) B8415211
theorem B7480187 : Blo 2215435 7480187 := bstep (se 1 (by rfl) ⟨5610140, by rfl⟩ : syracuseStep 7480187 = 11220281) B11220281
theorem B4986791 : Blo 2215435 4986791 := bstep (se 1 (by rfl) ⟨3740093, by rfl⟩ : syracuseStep 4986791 = 7480187) B7480187
theorem B3324527 : Blo 2215435 3324527 := bstep (se 1 (by rfl) ⟨2493395, by rfl⟩ : syracuseStep 3324527 = 4986791) B4986791
theorem B2216351 : Blo 2215435 2216351 := bstep (se 1 (by rfl) ⟨1662263, by rfl⟩ : syracuseStep 2216351 = 3324527) B3324527
theorem B3324533 : Blo 2215435 3324533 := bbase (se 5 (by rfl) ⟨155837, by rfl⟩ : syracuseStep 3324533 = 311675) (by norm_num)
theorem B2216355 : Blo 2215435 2216355 := bstep (se 1 (by rfl) ⟨1662266, by rfl⟩ : syracuseStep 2216355 = 3324533) B3324533
theorem B4207621 : Blo 2215435 4207621 := bbase (se 4 (by rfl) ⟨394464, by rfl⟩ : syracuseStep 4207621 = 788929) (by norm_num)
theorem B5610161 : Blo 2215435 5610161 := bstep (se 2 (by rfl) ⟨2103810, by rfl⟩ : syracuseStep 5610161 = 4207621) B4207621
theorem B3740107 : Blo 2215435 3740107 := bstep (se 1 (by rfl) ⟨2805080, by rfl⟩ : syracuseStep 3740107 = 5610161) B5610161
theorem B4986809 : Blo 2215435 4986809 := bstep (se 2 (by rfl) ⟨1870053, by rfl⟩ : syracuseStep 4986809 = 3740107) B3740107
theorem B3324539 : Blo 2215435 3324539 := bstep (se 1 (by rfl) ⟨2493404, by rfl⟩ : syracuseStep 3324539 = 4986809) B4986809
theorem B2216359 : Blo 2215435 2216359 := bstep (se 1 (by rfl) ⟨1662269, by rfl⟩ : syracuseStep 2216359 = 3324539) B3324539
theorem B2493409 : Blo 2215435 2493409 := bbase (se 2 (by rfl) ⟨935028, by rfl⟩ : syracuseStep 2493409 = 1870057) (by norm_num)
theorem B3324545 : Blo 2215435 3324545 := bstep (se 2 (by rfl) ⟨1246704, by rfl⟩ : syracuseStep 3324545 = 2493409) B2493409
theorem B2216363 : Blo 2215435 2216363 := bstep (se 1 (by rfl) ⟨1662272, by rfl⟩ : syracuseStep 2216363 = 3324545) B3324545
theorem B5610181 : Blo 2215435 5610181 := bbase (se 4 (by rfl) ⟨525954, by rfl⟩ : syracuseStep 5610181 = 1051909) (by norm_num)
theorem B7480241 : Blo 2215435 7480241 := bstep (se 2 (by rfl) ⟨2805090, by rfl⟩ : syracuseStep 7480241 = 5610181) B5610181
theorem B4986827 : Blo 2215435 4986827 := bstep (se 1 (by rfl) ⟨3740120, by rfl⟩ : syracuseStep 4986827 = 7480241) B7480241
theorem B3324551 : Blo 2215435 3324551 := bstep (se 1 (by rfl) ⟨2493413, by rfl⟩ : syracuseStep 3324551 = 4986827) B4986827
theorem B2216367 : Blo 2215435 2216367 := bstep (se 1 (by rfl) ⟨1662275, by rfl⟩ : syracuseStep 2216367 = 3324551) B3324551
theorem B3324557 : Blo 2215435 3324557 := bbase (se 3 (by rfl) ⟨623354, by rfl⟩ : syracuseStep 3324557 = 1246709) (by norm_num)
theorem B2216371 : Blo 2215435 2216371 := bstep (se 1 (by rfl) ⟨1662278, by rfl⟩ : syracuseStep 2216371 = 3324557) B3324557
theorem B4986845 : Blo 2215435 4986845 := bbase (se 3 (by rfl) ⟨935033, by rfl⟩ : syracuseStep 4986845 = 1870067) (by norm_num)
theorem B3324563 : Blo 2215435 3324563 := bstep (se 1 (by rfl) ⟨2493422, by rfl⟩ : syracuseStep 3324563 = 4986845) B4986845
theorem B2216375 : Blo 2215435 2216375 := bstep (se 1 (by rfl) ⟨1662281, by rfl⟩ : syracuseStep 2216375 = 3324563) B3324563
theorem B3740141 : Blo 2215435 3740141 := bbase (se 3 (by rfl) ⟨701276, by rfl⟩ : syracuseStep 3740141 = 1402553) (by norm_num)
theorem B2493427 : Blo 2215435 2493427 := bstep (se 1 (by rfl) ⟨1870070, by rfl⟩ : syracuseStep 2493427 = 3740141) B3740141
theorem B3324569 : Blo 2215435 3324569 := bstep (se 2 (by rfl) ⟨1246713, by rfl⟩ : syracuseStep 3324569 = 2493427) B2493427
theorem B2216379 : Blo 2215435 2216379 := bstep (se 1 (by rfl) ⟨1662284, by rfl⟩ : syracuseStep 2216379 = 3324569) B3324569
theorem B28401749 : Blo 2215435 28401749 := bbase (se 8 (by rfl) ⟨166416, by rfl⟩ : syracuseStep 28401749 = 332833) (by norm_num)
theorem B18934499 : Blo 2215435 18934499 := bstep (se 1 (by rfl) ⟨14200874, by rfl⟩ : syracuseStep 18934499 = 28401749) B28401749
theorem B12622999 : Blo 2215435 12622999 := bstep (se 1 (by rfl) ⟨9467249, by rfl⟩ : syracuseStep 12622999 = 18934499) B18934499
theorem B16830665 : Blo 2215435 16830665 := bstep (se 2 (by rfl) ⟨6311499, by rfl⟩ : syracuseStep 16830665 = 12622999) B12622999
theorem B11220443 : Blo 2215435 11220443 := bstep (se 1 (by rfl) ⟨8415332, by rfl⟩ : syracuseStep 11220443 = 16830665) B16830665
theorem B7480295 : Blo 2215435 7480295 := bstep (se 1 (by rfl) ⟨5610221, by rfl⟩ : syracuseStep 7480295 = 11220443) B11220443
theorem B4986863 : Blo 2215435 4986863 := bstep (se 1 (by rfl) ⟨3740147, by rfl⟩ : syracuseStep 4986863 = 7480295) B7480295
theorem B3324575 : Blo 2215435 3324575 := bstep (se 1 (by rfl) ⟨2493431, by rfl⟩ : syracuseStep 3324575 = 4986863) B4986863
theorem B2216383 : Blo 2215435 2216383 := bstep (se 1 (by rfl) ⟨1662287, by rfl⟩ : syracuseStep 2216383 = 3324575) B3324575
theorem B3324581 : Blo 2215435 3324581 := bbase (se 4 (by rfl) ⟨311679, by rfl⟩ : syracuseStep 3324581 = 623359) (by norm_num)
theorem B2216387 : Blo 2215435 2216387 := bstep (se 1 (by rfl) ⟨1662290, by rfl⟩ : syracuseStep 2216387 = 3324581) B3324581
theorem B2805121 : Blo 2215435 2805121 := bbase (se 2 (by rfl) ⟨1051920, by rfl⟩ : syracuseStep 2805121 = 2103841) (by norm_num)
theorem B3740161 : Blo 2215435 3740161 := bstep (se 2 (by rfl) ⟨1402560, by rfl⟩ : syracuseStep 3740161 = 2805121) B2805121
theorem B4986881 : Blo 2215435 4986881 := bstep (se 2 (by rfl) ⟨1870080, by rfl⟩ : syracuseStep 4986881 = 3740161) B3740161
theorem B3324587 : Blo 2215435 3324587 := bstep (se 1 (by rfl) ⟨2493440, by rfl⟩ : syracuseStep 3324587 = 4986881) B4986881
theorem B2216391 : Blo 2215435 2216391 := bstep (se 1 (by rfl) ⟨1662293, by rfl⟩ : syracuseStep 2216391 = 3324587) B3324587
theorem B2493445 : Blo 2215435 2493445 := bbase (se 4 (by rfl) ⟨233760, by rfl⟩ : syracuseStep 2493445 = 467521) (by norm_num)
theorem B3324593 : Blo 2215435 3324593 := bstep (se 2 (by rfl) ⟨1246722, by rfl⟩ : syracuseStep 3324593 = 2493445) B2493445
theorem B2216395 : Blo 2215435 2216395 := bstep (se 1 (by rfl) ⟨1662296, by rfl⟩ : syracuseStep 2216395 = 3324593) B3324593
theorem B3155773 : Blo 2215435 3155773 := bbase (se 3 (by rfl) ⟨591707, by rfl⟩ : syracuseStep 3155773 = 1183415) (by norm_num)
theorem B4207697 : Blo 2215435 4207697 := bstep (se 2 (by rfl) ⟨1577886, by rfl⟩ : syracuseStep 4207697 = 3155773) B3155773
theorem B2805131 : Blo 2215435 2805131 := bstep (se 1 (by rfl) ⟨2103848, by rfl⟩ : syracuseStep 2805131 = 4207697) B4207697
theorem B7480349 : Blo 2215435 7480349 := bstep (se 3 (by rfl) ⟨1402565, by rfl⟩ : syracuseStep 7480349 = 2805131) B2805131
theorem B4986899 : Blo 2215435 4986899 := bstep (se 1 (by rfl) ⟨3740174, by rfl⟩ : syracuseStep 4986899 = 7480349) B7480349
theorem B3324599 : Blo 2215435 3324599 := bstep (se 1 (by rfl) ⟨2493449, by rfl⟩ : syracuseStep 3324599 = 4986899) B4986899
theorem B2216399 : Blo 2215435 2216399 := bstep (se 1 (by rfl) ⟨1662299, by rfl⟩ : syracuseStep 2216399 = 3324599) B3324599
theorem B3324605 : Blo 2215435 3324605 := bbase (se 3 (by rfl) ⟨623363, by rfl⟩ : syracuseStep 3324605 = 1246727) (by norm_num)
theorem B2216403 : Blo 2215435 2216403 := bstep (se 1 (by rfl) ⟨1662302, by rfl⟩ : syracuseStep 2216403 = 3324605) B3324605
theorem B4986917 : Blo 2215435 4986917 := bbase (se 4 (by rfl) ⟨467523, by rfl⟩ : syracuseStep 4986917 = 935047) (by norm_num)
theorem B3324611 : Blo 2215435 3324611 := bstep (se 1 (by rfl) ⟨2493458, by rfl⟩ : syracuseStep 3324611 = 4986917) B4986917
theorem B2216407 : Blo 2215435 2216407 := bstep (se 1 (by rfl) ⟨1662305, by rfl⟩ : syracuseStep 2216407 = 3324611) B3324611
theorem B5610293 : Blo 2215435 5610293 := bbase (se 5 (by rfl) ⟨262982, by rfl⟩ : syracuseStep 5610293 = 525965) (by norm_num)
theorem B3740195 : Blo 2215435 3740195 := bstep (se 1 (by rfl) ⟨2805146, by rfl⟩ : syracuseStep 3740195 = 5610293) B5610293
theorem B2493463 : Blo 2215435 2493463 := bstep (se 1 (by rfl) ⟨1870097, by rfl⟩ : syracuseStep 2493463 = 3740195) B3740195
theorem B3324617 : Blo 2215435 3324617 := bstep (se 2 (by rfl) ⟨1246731, by rfl⟩ : syracuseStep 3324617 = 2493463) B2493463
theorem B2216411 : Blo 2215435 2216411 := bstep (se 1 (by rfl) ⟨1662308, by rfl⟩ : syracuseStep 2216411 = 3324617) B3324617
theorem B2632357 : Blo 2215435 2632357 := bbase (se 4 (by rfl) ⟨246783, by rfl⟩ : syracuseStep 2632357 = 493567) (by norm_num)
theorem B14039237 : Blo 2215435 14039237 := bstep (se 4 (by rfl) ⟨1316178, by rfl⟩ : syracuseStep 14039237 = 2632357) B2632357
theorem B9359491 : Blo 2215435 9359491 := bstep (se 1 (by rfl) ⟨7019618, by rfl⟩ : syracuseStep 9359491 = 14039237) B14039237
theorem B12479321 : Blo 2215435 12479321 := bstep (se 2 (by rfl) ⟨4679745, by rfl⟩ : syracuseStep 12479321 = 9359491) B9359491
theorem B8319547 : Blo 2215435 8319547 := bstep (se 1 (by rfl) ⟨6239660, by rfl⟩ : syracuseStep 8319547 = 12479321) B12479321
theorem B11092729 : Blo 2215435 11092729 := bstep (se 2 (by rfl) ⟨4159773, by rfl⟩ : syracuseStep 11092729 = 8319547) B8319547
theorem B14790305 : Blo 2215435 14790305 := bstep (se 2 (by rfl) ⟨5546364, by rfl⟩ : syracuseStep 14790305 = 11092729) B11092729
theorem B9860203 : Blo 2215435 9860203 := bstep (se 1 (by rfl) ⟨7395152, by rfl⟩ : syracuseStep 9860203 = 14790305) B14790305
theorem B13146937 : Blo 2215435 13146937 := bstep (se 2 (by rfl) ⟨4930101, by rfl⟩ : syracuseStep 13146937 = 9860203) B9860203
theorem B70116997 : Blo 2215435 70116997 := bstep (se 4 (by rfl) ⟨6573468, by rfl⟩ : syracuseStep 70116997 = 13146937) B13146937
theorem B93489329 : Blo 2215435 93489329 := bstep (se 2 (by rfl) ⟨35058498, by rfl⟩ : syracuseStep 93489329 = 70116997) B70116997
theorem B62326219 : Blo 2215435 62326219 := bstep (se 1 (by rfl) ⟨46744664, by rfl⟩ : syracuseStep 62326219 = 93489329) B93489329
theorem B83101625 : Blo 2215435 83101625 := bstep (se 2 (by rfl) ⟨31163109, by rfl⟩ : syracuseStep 83101625 = 62326219) B62326219
theorem B55401083 : Blo 2215435 55401083 := bstep (se 1 (by rfl) ⟨41550812, by rfl⟩ : syracuseStep 55401083 = 83101625) B83101625
theorem B36934055 : Blo 2215435 36934055 := bstep (se 1 (by rfl) ⟨27700541, by rfl⟩ : syracuseStep 36934055 = 55401083) B55401083
theorem B24622703 : Blo 2215435 24622703 := bstep (se 1 (by rfl) ⟨18467027, by rfl⟩ : syracuseStep 24622703 = 36934055) B36934055
theorem B16415135 : Blo 2215435 16415135 := bstep (se 1 (by rfl) ⟨12311351, by rfl⟩ : syracuseStep 16415135 = 24622703) B24622703
theorem B10943423 : Blo 2215435 10943423 := bstep (se 1 (by rfl) ⟨8207567, by rfl⟩ : syracuseStep 10943423 = 16415135) B16415135
theorem B7295615 : Blo 2215435 7295615 := bstep (se 1 (by rfl) ⟨5471711, by rfl⟩ : syracuseStep 7295615 = 10943423) B10943423
theorem B4863743 : Blo 2215435 4863743 := bstep (se 1 (by rfl) ⟨3647807, by rfl⟩ : syracuseStep 4863743 = 7295615) B7295615
theorem B3242495 : Blo 2215435 3242495 := bstep (se 1 (by rfl) ⟨2431871, by rfl⟩ : syracuseStep 3242495 = 4863743) B4863743
theorem B8646653 : Blo 2215435 8646653 := bstep (se 3 (by rfl) ⟨1621247, by rfl⟩ : syracuseStep 8646653 = 3242495) B3242495
theorem B23057741 : Blo 2215435 23057741 := bstep (se 3 (by rfl) ⟨4323326, by rfl⟩ : syracuseStep 23057741 = 8646653) B8646653
theorem B61487309 : Blo 2215435 61487309 := bstep (se 3 (by rfl) ⟨11528870, by rfl⟩ : syracuseStep 61487309 = 23057741) B23057741
theorem B163966157 : Blo 2215435 163966157 := bstep (se 3 (by rfl) ⟨30743654, by rfl⟩ : syracuseStep 163966157 = 61487309) B61487309
theorem B109310771 : Blo 2215435 109310771 := bstep (se 1 (by rfl) ⟨81983078, by rfl⟩ : syracuseStep 109310771 = 163966157) B163966157
theorem B72873847 : Blo 2215435 72873847 := bstep (se 1 (by rfl) ⟨54655385, by rfl⟩ : syracuseStep 72873847 = 109310771) B109310771
theorem B388660517 : Blo 2215435 388660517 := bstep (se 4 (by rfl) ⟨36436923, by rfl⟩ : syracuseStep 388660517 = 72873847) B72873847
theorem B259107011 : Blo 2215435 259107011 := bstep (se 1 (by rfl) ⟨194330258, by rfl⟩ : syracuseStep 259107011 = 388660517) B388660517
theorem B172738007 : Blo 2215435 172738007 := bstep (se 1 (by rfl) ⟨129553505, by rfl⟩ : syracuseStep 172738007 = 259107011) B259107011
theorem B115158671 : Blo 2215435 115158671 := bstep (se 1 (by rfl) ⟨86369003, by rfl⟩ : syracuseStep 115158671 = 172738007) B172738007
theorem B76772447 : Blo 2215435 76772447 := bstep (se 1 (by rfl) ⟨57579335, by rfl⟩ : syracuseStep 76772447 = 115158671) B115158671
theorem B51181631 : Blo 2215435 51181631 := bstep (se 1 (by rfl) ⟨38386223, by rfl⟩ : syracuseStep 51181631 = 76772447) B76772447
theorem B34121087 : Blo 2215435 34121087 := bstep (se 1 (by rfl) ⟨25590815, by rfl⟩ : syracuseStep 34121087 = 51181631) B51181631
theorem B22747391 : Blo 2215435 22747391 := bstep (se 1 (by rfl) ⟨17060543, by rfl⟩ : syracuseStep 22747391 = 34121087) B34121087
theorem B15164927 : Blo 2215435 15164927 := bstep (se 1 (by rfl) ⟨11373695, by rfl⟩ : syracuseStep 15164927 = 22747391) B22747391
theorem B10109951 : Blo 2215435 10109951 := bstep (se 1 (by rfl) ⟨7582463, by rfl⟩ : syracuseStep 10109951 = 15164927) B15164927
theorem B6739967 : Blo 2215435 6739967 := bstep (se 1 (by rfl) ⟨5054975, by rfl⟩ : syracuseStep 6739967 = 10109951) B10109951
theorem B17973245 : Blo 2215435 17973245 := bstep (se 3 (by rfl) ⟨3369983, by rfl⟩ : syracuseStep 17973245 = 6739967) B6739967
theorem B11982163 : Blo 2215435 11982163 := bstep (se 1 (by rfl) ⟨8986622, by rfl⟩ : syracuseStep 11982163 = 17973245) B17973245
theorem B15976217 : Blo 2215435 15976217 := bstep (se 2 (by rfl) ⟨5991081, by rfl⟩ : syracuseStep 15976217 = 11982163) B11982163
theorem B10650811 : Blo 2215435 10650811 := bstep (se 1 (by rfl) ⟨7988108, by rfl⟩ : syracuseStep 10650811 = 15976217) B15976217
theorem B14201081 : Blo 2215435 14201081 := bstep (se 2 (by rfl) ⟨5325405, by rfl⟩ : syracuseStep 14201081 = 10650811) B10650811
theorem B9467387 : Blo 2215435 9467387 := bstep (se 1 (by rfl) ⟨7100540, by rfl⟩ : syracuseStep 9467387 = 14201081) B14201081
theorem B6311591 : Blo 2215435 6311591 := bstep (se 1 (by rfl) ⟨4733693, by rfl⟩ : syracuseStep 6311591 = 9467387) B9467387
theorem B4207727 : Blo 2215435 4207727 := bstep (se 1 (by rfl) ⟨3155795, by rfl⟩ : syracuseStep 4207727 = 6311591) B6311591
theorem B11220605 : Blo 2215435 11220605 := bstep (se 3 (by rfl) ⟨2103863, by rfl⟩ : syracuseStep 11220605 = 4207727) B4207727
theorem B7480403 : Blo 2215435 7480403 := bstep (se 1 (by rfl) ⟨5610302, by rfl⟩ : syracuseStep 7480403 = 11220605) B11220605
theorem B4986935 : Blo 2215435 4986935 := bstep (se 1 (by rfl) ⟨3740201, by rfl⟩ : syracuseStep 4986935 = 7480403) B7480403
theorem B3324623 : Blo 2215435 3324623 := bstep (se 1 (by rfl) ⟨2493467, by rfl⟩ : syracuseStep 3324623 = 4986935) B4986935
theorem B2216415 : Blo 2215435 2216415 := bstep (se 1 (by rfl) ⟨1662311, by rfl⟩ : syracuseStep 2216415 = 3324623) B3324623
theorem B3324629 : Blo 2215435 3324629 := bbase (se 7 (by rfl) ⟨38960, by rfl⟩ : syracuseStep 3324629 = 77921) (by norm_num)
theorem B2216419 : Blo 2215435 2216419 := bstep (se 1 (by rfl) ⟨1662314, by rfl⟩ : syracuseStep 2216419 = 3324629) B3324629
theorem B15976277 : Blo 2215435 15976277 := bbase (se 9 (by rfl) ⟨46805, by rfl⟩ : syracuseStep 15976277 = 93611) (by norm_num)
theorem B10650851 : Blo 2215435 10650851 := bstep (se 1 (by rfl) ⟨7988138, by rfl⟩ : syracuseStep 10650851 = 15976277) B15976277
theorem B7100567 : Blo 2215435 7100567 := bstep (se 1 (by rfl) ⟨5325425, by rfl⟩ : syracuseStep 7100567 = 10650851) B10650851
theorem B4733711 : Blo 2215435 4733711 := bstep (se 1 (by rfl) ⟨3550283, by rfl⟩ : syracuseStep 4733711 = 7100567) B7100567
theorem B3155807 : Blo 2215435 3155807 := bstep (se 1 (by rfl) ⟨2366855, by rfl⟩ : syracuseStep 3155807 = 4733711) B4733711
theorem B8415485 : Blo 2215435 8415485 := bstep (se 3 (by rfl) ⟨1577903, by rfl⟩ : syracuseStep 8415485 = 3155807) B3155807
theorem B5610323 : Blo 2215435 5610323 := bstep (se 1 (by rfl) ⟨4207742, by rfl⟩ : syracuseStep 5610323 = 8415485) B8415485
theorem B3740215 : Blo 2215435 3740215 := bstep (se 1 (by rfl) ⟨2805161, by rfl⟩ : syracuseStep 3740215 = 5610323) B5610323
theorem B4986953 : Blo 2215435 4986953 := bstep (se 2 (by rfl) ⟨1870107, by rfl⟩ : syracuseStep 4986953 = 3740215) B3740215
theorem B3324635 : Blo 2215435 3324635 := bstep (se 1 (by rfl) ⟨2493476, by rfl⟩ : syracuseStep 3324635 = 4986953) B4986953
theorem B2216423 : Blo 2215435 2216423 := bstep (se 1 (by rfl) ⟨1662317, by rfl⟩ : syracuseStep 2216423 = 3324635) B3324635
theorem B2493481 : Blo 2215435 2493481 := bbase (se 2 (by rfl) ⟨935055, by rfl⟩ : syracuseStep 2493481 = 1870111) (by norm_num)
theorem B3324641 : Blo 2215435 3324641 := bstep (se 2 (by rfl) ⟨1246740, by rfl⟩ : syracuseStep 3324641 = 2493481) B2493481
theorem B2216427 : Blo 2215435 2216427 := bstep (se 1 (by rfl) ⟨1662320, by rfl⟩ : syracuseStep 2216427 = 3324641) B3324641
theorem B6831973 : Blo 2215435 6831973 := bbase (se 4 (by rfl) ⟨640497, by rfl⟩ : syracuseStep 6831973 = 1280995) (by norm_num)
theorem B9109297 : Blo 2215435 9109297 := bstep (se 2 (by rfl) ⟨3415986, by rfl⟩ : syracuseStep 9109297 = 6831973) B6831973
theorem B12145729 : Blo 2215435 12145729 := bstep (se 2 (by rfl) ⟨4554648, by rfl⟩ : syracuseStep 12145729 = 9109297) B9109297
theorem B16194305 : Blo 2215435 16194305 := bstep (se 2 (by rfl) ⟨6072864, by rfl⟩ : syracuseStep 16194305 = 12145729) B12145729
theorem B10796203 : Blo 2215435 10796203 := bstep (se 1 (by rfl) ⟨8097152, by rfl⟩ : syracuseStep 10796203 = 16194305) B16194305
theorem B14394937 : Blo 2215435 14394937 := bstep (se 2 (by rfl) ⟨5398101, by rfl⟩ : syracuseStep 14394937 = 10796203) B10796203
theorem B19193249 : Blo 2215435 19193249 := bstep (se 2 (by rfl) ⟨7197468, by rfl⟩ : syracuseStep 19193249 = 14394937) B14394937
theorem B12795499 : Blo 2215435 12795499 := bstep (se 1 (by rfl) ⟨9596624, by rfl⟩ : syracuseStep 12795499 = 19193249) B19193249
theorem B17060665 : Blo 2215435 17060665 := bstep (se 2 (by rfl) ⟨6397749, by rfl⟩ : syracuseStep 17060665 = 12795499) B12795499
theorem B22747553 : Blo 2215435 22747553 := bstep (se 2 (by rfl) ⟨8530332, by rfl⟩ : syracuseStep 22747553 = 17060665) B17060665
theorem B15165035 : Blo 2215435 15165035 := bstep (se 1 (by rfl) ⟨11373776, by rfl⟩ : syracuseStep 15165035 = 22747553) B22747553
theorem B10110023 : Blo 2215435 10110023 := bstep (se 1 (by rfl) ⟨7582517, by rfl⟩ : syracuseStep 10110023 = 15165035) B15165035
theorem B6740015 : Blo 2215435 6740015 := bstep (se 1 (by rfl) ⟨5055011, by rfl⟩ : syracuseStep 6740015 = 10110023) B10110023
theorem B71893493 : Blo 2215435 71893493 := bstep (se 5 (by rfl) ⟨3370007, by rfl⟩ : syracuseStep 71893493 = 6740015) B6740015
theorem B47928995 : Blo 2215435 47928995 := bstep (se 1 (by rfl) ⟨35946746, by rfl⟩ : syracuseStep 47928995 = 71893493) B71893493
theorem B31952663 : Blo 2215435 31952663 := bstep (se 1 (by rfl) ⟨23964497, by rfl⟩ : syracuseStep 31952663 = 47928995) B47928995
theorem B21301775 : Blo 2215435 21301775 := bstep (se 1 (by rfl) ⟨15976331, by rfl⟩ : syracuseStep 21301775 = 31952663) B31952663
theorem B14201183 : Blo 2215435 14201183 := bstep (se 1 (by rfl) ⟨10650887, by rfl⟩ : syracuseStep 14201183 = 21301775) B21301775
theorem B9467455 : Blo 2215435 9467455 := bstep (se 1 (by rfl) ⟨7100591, by rfl⟩ : syracuseStep 9467455 = 14201183) B14201183
theorem B12623273 : Blo 2215435 12623273 := bstep (se 2 (by rfl) ⟨4733727, by rfl⟩ : syracuseStep 12623273 = 9467455) B9467455
theorem B8415515 : Blo 2215435 8415515 := bstep (se 1 (by rfl) ⟨6311636, by rfl⟩ : syracuseStep 8415515 = 12623273) B12623273
theorem B5610343 : Blo 2215435 5610343 := bstep (se 1 (by rfl) ⟨4207757, by rfl⟩ : syracuseStep 5610343 = 8415515) B8415515
theorem B7480457 : Blo 2215435 7480457 := bstep (se 2 (by rfl) ⟨2805171, by rfl⟩ : syracuseStep 7480457 = 5610343) B5610343
theorem B4986971 : Blo 2215435 4986971 := bstep (se 1 (by rfl) ⟨3740228, by rfl⟩ : syracuseStep 4986971 = 7480457) B7480457
theorem B3324647 : Blo 2215435 3324647 := bstep (se 1 (by rfl) ⟨2493485, by rfl⟩ : syracuseStep 3324647 = 4986971) B4986971
theorem B2216431 : Blo 2215435 2216431 := bstep (se 1 (by rfl) ⟨1662323, by rfl⟩ : syracuseStep 2216431 = 3324647) B3324647
theorem B3324653 : Blo 2215435 3324653 := bbase (se 3 (by rfl) ⟨623372, by rfl⟩ : syracuseStep 3324653 = 1246745) (by norm_num)
theorem B2216435 : Blo 2215435 2216435 := bstep (se 1 (by rfl) ⟨1662326, by rfl⟩ : syracuseStep 2216435 = 3324653) B3324653
theorem B4986989 : Blo 2215435 4986989 := bbase (se 3 (by rfl) ⟨935060, by rfl⟩ : syracuseStep 4986989 = 1870121) (by norm_num)
theorem B3324659 : Blo 2215435 3324659 := bstep (se 1 (by rfl) ⟨2493494, by rfl⟩ : syracuseStep 3324659 = 4986989) B4986989
theorem B2216439 : Blo 2215435 2216439 := bstep (se 1 (by rfl) ⟨1662329, by rfl⟩ : syracuseStep 2216439 = 3324659) B3324659
theorem B4207781 : Blo 2215435 4207781 := bbase (se 4 (by rfl) ⟨394479, by rfl⟩ : syracuseStep 4207781 = 788959) (by norm_num)
theorem B2805187 : Blo 2215435 2805187 := bstep (se 1 (by rfl) ⟨2103890, by rfl⟩ : syracuseStep 2805187 = 4207781) B4207781
theorem B3740249 : Blo 2215435 3740249 := bstep (se 2 (by rfl) ⟨1402593, by rfl⟩ : syracuseStep 3740249 = 2805187) B2805187
theorem B2493499 : Blo 2215435 2493499 := bstep (se 1 (by rfl) ⟨1870124, by rfl⟩ : syracuseStep 2493499 = 3740249) B3740249
theorem B3324665 : Blo 2215435 3324665 := bstep (se 2 (by rfl) ⟨1246749, by rfl⟩ : syracuseStep 3324665 = 2493499) B2493499
theorem B2216443 : Blo 2215435 2216443 := bstep (se 1 (by rfl) ⟨1662332, by rfl⟩ : syracuseStep 2216443 = 3324665) B3324665
theorem B9860341 : Blo 2215435 9860341 := bbase (se 5 (by rfl) ⟨462203, by rfl⟩ : syracuseStep 9860341 = 924407) (by norm_num)
theorem B13147121 : Blo 2215435 13147121 := bstep (se 2 (by rfl) ⟨4930170, by rfl⟩ : syracuseStep 13147121 = 9860341) B9860341
theorem B35058989 : Blo 2215435 35058989 := bstep (se 3 (by rfl) ⟨6573560, by rfl⟩ : syracuseStep 35058989 = 13147121) B13147121
theorem B23372659 : Blo 2215435 23372659 := bstep (se 1 (by rfl) ⟨17529494, by rfl⟩ : syracuseStep 23372659 = 35058989) B35058989
theorem B31163545 : Blo 2215435 31163545 := bstep (se 2 (by rfl) ⟨11686329, by rfl⟩ : syracuseStep 31163545 = 23372659) B23372659
theorem B166205573 : Blo 2215435 166205573 := bstep (se 4 (by rfl) ⟨15581772, by rfl⟩ : syracuseStep 166205573 = 31163545) B31163545
theorem B110803715 : Blo 2215435 110803715 := bstep (se 1 (by rfl) ⟨83102786, by rfl⟩ : syracuseStep 110803715 = 166205573) B166205573
theorem B73869143 : Blo 2215435 73869143 := bstep (se 1 (by rfl) ⟨55401857, by rfl⟩ : syracuseStep 73869143 = 110803715) B110803715
theorem B196984381 : Blo 2215435 196984381 := bstep (se 3 (by rfl) ⟨36934571, by rfl⟩ : syracuseStep 196984381 = 73869143) B73869143
theorem B262645841 : Blo 2215435 262645841 := bstep (se 2 (by rfl) ⟨98492190, by rfl⟩ : syracuseStep 262645841 = 196984381) B196984381
theorem B175097227 : Blo 2215435 175097227 := bstep (se 1 (by rfl) ⟨131322920, by rfl⟩ : syracuseStep 175097227 = 262645841) B262645841
theorem B233462969 : Blo 2215435 233462969 := bstep (se 2 (by rfl) ⟨87548613, by rfl⟩ : syracuseStep 233462969 = 175097227) B175097227
theorem B155641979 : Blo 2215435 155641979 := bstep (se 1 (by rfl) ⟨116731484, by rfl⟩ : syracuseStep 155641979 = 233462969) B233462969
theorem B103761319 : Blo 2215435 103761319 := bstep (se 1 (by rfl) ⟨77820989, by rfl⟩ : syracuseStep 103761319 = 155641979) B155641979
theorem B138348425 : Blo 2215435 138348425 := bstep (se 2 (by rfl) ⟨51880659, by rfl⟩ : syracuseStep 138348425 = 103761319) B103761319
theorem B92232283 : Blo 2215435 92232283 := bstep (se 1 (by rfl) ⟨69174212, by rfl⟩ : syracuseStep 92232283 = 138348425) B138348425
theorem B122976377 : Blo 2215435 122976377 := bstep (se 2 (by rfl) ⟨46116141, by rfl⟩ : syracuseStep 122976377 = 92232283) B92232283
theorem B81984251 : Blo 2215435 81984251 := bstep (se 1 (by rfl) ⟨61488188, by rfl⟩ : syracuseStep 81984251 = 122976377) B122976377
theorem B54656167 : Blo 2215435 54656167 := bstep (se 1 (by rfl) ⟨40992125, by rfl⟩ : syracuseStep 54656167 = 81984251) B81984251
theorem B72874889 : Blo 2215435 72874889 := bstep (se 2 (by rfl) ⟨27328083, by rfl⟩ : syracuseStep 72874889 = 54656167) B54656167
theorem B48583259 : Blo 2215435 48583259 := bstep (se 1 (by rfl) ⟨36437444, by rfl⟩ : syracuseStep 48583259 = 72874889) B72874889
theorem B32388839 : Blo 2215435 32388839 := bstep (se 1 (by rfl) ⟨24291629, by rfl⟩ : syracuseStep 32388839 = 48583259) B48583259
theorem B21592559 : Blo 2215435 21592559 := bstep (se 1 (by rfl) ⟨16194419, by rfl⟩ : syracuseStep 21592559 = 32388839) B32388839
theorem B14395039 : Blo 2215435 14395039 := bstep (se 1 (by rfl) ⟨10796279, by rfl⟩ : syracuseStep 14395039 = 21592559) B21592559
theorem B76773541 : Blo 2215435 76773541 := bstep (se 4 (by rfl) ⟨7197519, by rfl⟩ : syracuseStep 76773541 = 14395039) B14395039
theorem B102364721 : Blo 2215435 102364721 := bstep (se 2 (by rfl) ⟨38386770, by rfl⟩ : syracuseStep 102364721 = 76773541) B76773541
theorem B68243147 : Blo 2215435 68243147 := bstep (se 1 (by rfl) ⟨51182360, by rfl⟩ : syracuseStep 68243147 = 102364721) B102364721
theorem B45495431 : Blo 2215435 45495431 := bstep (se 1 (by rfl) ⟨34121573, by rfl⟩ : syracuseStep 45495431 = 68243147) B68243147
theorem B30330287 : Blo 2215435 30330287 := bstep (se 1 (by rfl) ⟨22747715, by rfl⟩ : syracuseStep 30330287 = 45495431) B45495431
theorem B20220191 : Blo 2215435 20220191 := bstep (se 1 (by rfl) ⟨15165143, by rfl⟩ : syracuseStep 20220191 = 30330287) B30330287
theorem B13480127 : Blo 2215435 13480127 := bstep (se 1 (by rfl) ⟨10110095, by rfl⟩ : syracuseStep 13480127 = 20220191) B20220191
theorem B8986751 : Blo 2215435 8986751 := bstep (se 1 (by rfl) ⟨6740063, by rfl⟩ : syracuseStep 8986751 = 13480127) B13480127
theorem B5991167 : Blo 2215435 5991167 := bstep (se 1 (by rfl) ⟨4493375, by rfl⟩ : syracuseStep 5991167 = 8986751) B8986751
theorem B15976445 : Blo 2215435 15976445 := bstep (se 3 (by rfl) ⟨2995583, by rfl⟩ : syracuseStep 15976445 = 5991167) B5991167
theorem B42603853 : Blo 2215435 42603853 := bstep (se 3 (by rfl) ⟨7988222, by rfl⟩ : syracuseStep 42603853 = 15976445) B15976445
theorem B56805137 : Blo 2215435 56805137 := bstep (se 2 (by rfl) ⟨21301926, by rfl⟩ : syracuseStep 56805137 = 42603853) B42603853
theorem B37870091 : Blo 2215435 37870091 := bstep (se 1 (by rfl) ⟨28402568, by rfl⟩ : syracuseStep 37870091 = 56805137) B56805137
theorem B25246727 : Blo 2215435 25246727 := bstep (se 1 (by rfl) ⟨18935045, by rfl⟩ : syracuseStep 25246727 = 37870091) B37870091
theorem B16831151 : Blo 2215435 16831151 := bstep (se 1 (by rfl) ⟨12623363, by rfl⟩ : syracuseStep 16831151 = 25246727) B25246727
theorem B11220767 : Blo 2215435 11220767 := bstep (se 1 (by rfl) ⟨8415575, by rfl⟩ : syracuseStep 11220767 = 16831151) B16831151
theorem B7480511 : Blo 2215435 7480511 := bstep (se 1 (by rfl) ⟨5610383, by rfl⟩ : syracuseStep 7480511 = 11220767) B11220767
theorem B4987007 : Blo 2215435 4987007 := bstep (se 1 (by rfl) ⟨3740255, by rfl⟩ : syracuseStep 4987007 = 7480511) B7480511
theorem B3324671 : Blo 2215435 3324671 := bstep (se 1 (by rfl) ⟨2493503, by rfl⟩ : syracuseStep 3324671 = 4987007) B4987007
theorem B2216447 : Blo 2215435 2216447 := bstep (se 1 (by rfl) ⟨1662335, by rfl⟩ : syracuseStep 2216447 = 3324671) B3324671
theorem B3324677 : Blo 2215435 3324677 := bbase (se 4 (by rfl) ⟨311688, by rfl⟩ : syracuseStep 3324677 = 623377) (by norm_num)
theorem B2216451 : Blo 2215435 2216451 := bstep (se 1 (by rfl) ⟨1662338, by rfl⟩ : syracuseStep 2216451 = 3324677) B3324677
theorem B3740269 : Blo 2215435 3740269 := bbase (se 3 (by rfl) ⟨701300, by rfl⟩ : syracuseStep 3740269 = 1402601) (by norm_num)
theorem B4987025 : Blo 2215435 4987025 := bstep (se 2 (by rfl) ⟨1870134, by rfl⟩ : syracuseStep 4987025 = 3740269) B3740269
theorem B3324683 : Blo 2215435 3324683 := bstep (se 1 (by rfl) ⟨2493512, by rfl⟩ : syracuseStep 3324683 = 4987025) B4987025
theorem B2216455 : Blo 2215435 2216455 := bstep (se 1 (by rfl) ⟨1662341, by rfl⟩ : syracuseStep 2216455 = 3324683) B3324683
theorem B2493517 : Blo 2215435 2493517 := bbase (se 3 (by rfl) ⟨467534, by rfl⟩ : syracuseStep 2493517 = 935069) (by norm_num)
theorem B3324689 : Blo 2215435 3324689 := bstep (se 2 (by rfl) ⟨1246758, by rfl⟩ : syracuseStep 3324689 = 2493517) B2493517
theorem B2216459 : Blo 2215435 2216459 := bstep (se 1 (by rfl) ⟨1662344, by rfl⟩ : syracuseStep 2216459 = 3324689) B3324689
theorem B7480565 : Blo 2215435 7480565 := bbase (se 5 (by rfl) ⟨350651, by rfl⟩ : syracuseStep 7480565 = 701303) (by norm_num)
theorem B4987043 : Blo 2215435 4987043 := bstep (se 1 (by rfl) ⟨3740282, by rfl⟩ : syracuseStep 4987043 = 7480565) B7480565
theorem B3324695 : Blo 2215435 3324695 := bstep (se 1 (by rfl) ⟨2493521, by rfl⟩ : syracuseStep 3324695 = 4987043) B4987043
theorem B2216463 : Blo 2215435 2216463 := bstep (se 1 (by rfl) ⟨1662347, by rfl⟩ : syracuseStep 2216463 = 3324695) B3324695
theorem B3324701 : Blo 2215435 3324701 := bbase (se 3 (by rfl) ⟨623381, by rfl⟩ : syracuseStep 3324701 = 1246763) (by norm_num)
theorem B2216467 : Blo 2215435 2216467 := bstep (se 1 (by rfl) ⟨1662350, by rfl⟩ : syracuseStep 2216467 = 3324701) B3324701
theorem B4987061 : Blo 2215435 4987061 := bbase (se 5 (by rfl) ⟨233768, by rfl⟩ : syracuseStep 4987061 = 467537) (by norm_num)
theorem B3324707 : Blo 2215435 3324707 := bstep (se 1 (by rfl) ⟨2493530, by rfl⟩ : syracuseStep 3324707 = 4987061) B4987061
theorem B2216471 : Blo 2215435 2216471 := bstep (se 1 (by rfl) ⟨1662353, by rfl⟩ : syracuseStep 2216471 = 3324707) B3324707
theorem B8097317 : Blo 2215435 8097317 := bbase (se 4 (by rfl) ⟨759123, by rfl⟩ : syracuseStep 8097317 = 1518247) (by norm_num)
theorem B5398211 : Blo 2215435 5398211 := bstep (se 1 (by rfl) ⟨4048658, by rfl⟩ : syracuseStep 5398211 = 8097317) B8097317
theorem B3598807 : Blo 2215435 3598807 := bstep (se 1 (by rfl) ⟨2699105, by rfl⟩ : syracuseStep 3598807 = 5398211) B5398211
theorem B4798409 : Blo 2215435 4798409 := bstep (se 2 (by rfl) ⟨1799403, by rfl⟩ : syracuseStep 4798409 = 3598807) B3598807
theorem B51183029 : Blo 2215435 51183029 := bstep (se 5 (by rfl) ⟨2399204, by rfl⟩ : syracuseStep 51183029 = 4798409) B4798409
theorem B34122019 : Blo 2215435 34122019 := bstep (se 1 (by rfl) ⟨25591514, by rfl⟩ : syracuseStep 34122019 = 51183029) B51183029
theorem B45496025 : Blo 2215435 45496025 := bstep (se 2 (by rfl) ⟨17061009, by rfl⟩ : syracuseStep 45496025 = 34122019) B34122019
theorem B30330683 : Blo 2215435 30330683 := bstep (se 1 (by rfl) ⟨22748012, by rfl⟩ : syracuseStep 30330683 = 45496025) B45496025
theorem B20220455 : Blo 2215435 20220455 := bstep (se 1 (by rfl) ⟨15165341, by rfl⟩ : syracuseStep 20220455 = 30330683) B30330683
theorem B13480303 : Blo 2215435 13480303 := bstep (se 1 (by rfl) ⟨10110227, by rfl⟩ : syracuseStep 13480303 = 20220455) B20220455
theorem B17973737 : Blo 2215435 17973737 := bstep (se 2 (by rfl) ⟨6740151, by rfl⟩ : syracuseStep 17973737 = 13480303) B13480303
theorem B11982491 : Blo 2215435 11982491 := bstep (se 1 (by rfl) ⟨8986868, by rfl⟩ : syracuseStep 11982491 = 17973737) B17973737
theorem B7988327 : Blo 2215435 7988327 := bstep (se 1 (by rfl) ⟨5991245, by rfl⟩ : syracuseStep 7988327 = 11982491) B11982491
theorem B5325551 : Blo 2215435 5325551 := bstep (se 1 (by rfl) ⟨3994163, by rfl⟩ : syracuseStep 5325551 = 7988327) B7988327
theorem B3550367 : Blo 2215435 3550367 := bstep (se 1 (by rfl) ⟨2662775, by rfl⟩ : syracuseStep 3550367 = 5325551) B5325551
theorem B2366911 : Blo 2215435 2366911 := bstep (se 1 (by rfl) ⟨1775183, by rfl⟩ : syracuseStep 2366911 = 3550367) B3550367
theorem B12623525 : Blo 2215435 12623525 := bstep (se 4 (by rfl) ⟨1183455, by rfl⟩ : syracuseStep 12623525 = 2366911) B2366911
theorem B8415683 : Blo 2215435 8415683 := bstep (se 1 (by rfl) ⟨6311762, by rfl⟩ : syracuseStep 8415683 = 12623525) B12623525
theorem B5610455 : Blo 2215435 5610455 := bstep (se 1 (by rfl) ⟨4207841, by rfl⟩ : syracuseStep 5610455 = 8415683) B8415683
theorem B3740303 : Blo 2215435 3740303 := bstep (se 1 (by rfl) ⟨2805227, by rfl⟩ : syracuseStep 3740303 = 5610455) B5610455
theorem B2493535 : Blo 2215435 2493535 := bstep (se 1 (by rfl) ⟨1870151, by rfl⟩ : syracuseStep 2493535 = 3740303) B3740303
theorem B3324713 : Blo 2215435 3324713 := bstep (se 2 (by rfl) ⟨1246767, by rfl⟩ : syracuseStep 3324713 = 2493535) B2493535
theorem B2216475 : Blo 2215435 2216475 := bstep (se 1 (by rfl) ⟨1662356, by rfl⟩ : syracuseStep 2216475 = 3324713) B3324713
theorem B3550373 : Blo 2215435 3550373 := bbase (se 4 (by rfl) ⟨332847, by rfl⟩ : syracuseStep 3550373 = 665695) (by norm_num)
theorem B2366915 : Blo 2215435 2366915 := bstep (se 1 (by rfl) ⟨1775186, by rfl⟩ : syracuseStep 2366915 = 3550373) B3550373
theorem B6311773 : Blo 2215435 6311773 := bstep (se 3 (by rfl) ⟨1183457, by rfl⟩ : syracuseStep 6311773 = 2366915) B2366915
theorem B8415697 : Blo 2215435 8415697 := bstep (se 2 (by rfl) ⟨3155886, by rfl⟩ : syracuseStep 8415697 = 6311773) B6311773
theorem B11220929 : Blo 2215435 11220929 := bstep (se 2 (by rfl) ⟨4207848, by rfl⟩ : syracuseStep 11220929 = 8415697) B8415697
theorem B7480619 : Blo 2215435 7480619 := bstep (se 1 (by rfl) ⟨5610464, by rfl⟩ : syracuseStep 7480619 = 11220929) B11220929
theorem B4987079 : Blo 2215435 4987079 := bstep (se 1 (by rfl) ⟨3740309, by rfl⟩ : syracuseStep 4987079 = 7480619) B7480619
theorem B3324719 : Blo 2215435 3324719 := bstep (se 1 (by rfl) ⟨2493539, by rfl⟩ : syracuseStep 3324719 = 4987079) B4987079
theorem B2216479 : Blo 2215435 2216479 := bstep (se 1 (by rfl) ⟨1662359, by rfl⟩ : syracuseStep 2216479 = 3324719) B3324719
theorem B3324725 : Blo 2215435 3324725 := bbase (se 5 (by rfl) ⟨155846, by rfl⟩ : syracuseStep 3324725 = 311693) (by norm_num)
theorem B2216483 : Blo 2215435 2216483 := bstep (se 1 (by rfl) ⟨1662362, by rfl⟩ : syracuseStep 2216483 = 3324725) B3324725
theorem B5610485 : Blo 2215435 5610485 := bbase (se 5 (by rfl) ⟨262991, by rfl⟩ : syracuseStep 5610485 = 525983) (by norm_num)
theorem B3740323 : Blo 2215435 3740323 := bstep (se 1 (by rfl) ⟨2805242, by rfl⟩ : syracuseStep 3740323 = 5610485) B5610485
theorem B4987097 : Blo 2215435 4987097 := bstep (se 2 (by rfl) ⟨1870161, by rfl⟩ : syracuseStep 4987097 = 3740323) B3740323
theorem B3324731 : Blo 2215435 3324731 := bstep (se 1 (by rfl) ⟨2493548, by rfl⟩ : syracuseStep 3324731 = 4987097) B4987097
theorem B2216487 : Blo 2215435 2216487 := bstep (se 1 (by rfl) ⟨1662365, by rfl⟩ : syracuseStep 2216487 = 3324731) B3324731
theorem B2493553 : Blo 2215435 2493553 := bbase (se 2 (by rfl) ⟨935082, by rfl⟩ : syracuseStep 2493553 = 1870165) (by norm_num)
theorem B3324737 : Blo 2215435 3324737 := bstep (se 2 (by rfl) ⟨1246776, by rfl⟩ : syracuseStep 3324737 = 2493553) B2493553
theorem B2216491 : Blo 2215435 2216491 := bstep (se 1 (by rfl) ⟨1662368, by rfl⟩ : syracuseStep 2216491 = 3324737) B3324737
theorem B8986949 : Blo 2215435 8986949 := bbase (se 4 (by rfl) ⟨842526, by rfl⟩ : syracuseStep 8986949 = 1685053) (by norm_num)
theorem B5991299 : Blo 2215435 5991299 := bstep (se 1 (by rfl) ⟨4493474, by rfl⟩ : syracuseStep 5991299 = 8986949) B8986949
theorem B3994199 : Blo 2215435 3994199 := bstep (se 1 (by rfl) ⟨2995649, by rfl⟩ : syracuseStep 3994199 = 5991299) B5991299
theorem B2662799 : Blo 2215435 2662799 := bstep (se 1 (by rfl) ⟨1997099, by rfl⟩ : syracuseStep 2662799 = 3994199) B3994199
theorem B7100797 : Blo 2215435 7100797 := bstep (se 3 (by rfl) ⟨1331399, by rfl⟩ : syracuseStep 7100797 = 2662799) B2662799
theorem B9467729 : Blo 2215435 9467729 := bstep (se 2 (by rfl) ⟨3550398, by rfl⟩ : syracuseStep 9467729 = 7100797) B7100797
theorem B6311819 : Blo 2215435 6311819 := bstep (se 1 (by rfl) ⟨4733864, by rfl⟩ : syracuseStep 6311819 = 9467729) B9467729
theorem B4207879 : Blo 2215435 4207879 := bstep (se 1 (by rfl) ⟨3155909, by rfl⟩ : syracuseStep 4207879 = 6311819) B6311819
theorem B5610505 : Blo 2215435 5610505 := bstep (se 2 (by rfl) ⟨2103939, by rfl⟩ : syracuseStep 5610505 = 4207879) B4207879
theorem B7480673 : Blo 2215435 7480673 := bstep (se 2 (by rfl) ⟨2805252, by rfl⟩ : syracuseStep 7480673 = 5610505) B5610505
theorem B4987115 : Blo 2215435 4987115 := bstep (se 1 (by rfl) ⟨3740336, by rfl⟩ : syracuseStep 4987115 = 7480673) B7480673
theorem B3324743 : Blo 2215435 3324743 := bstep (se 1 (by rfl) ⟨2493557, by rfl⟩ : syracuseStep 3324743 = 4987115) B4987115
theorem B2216495 : Blo 2215435 2216495 := bstep (se 1 (by rfl) ⟨1662371, by rfl⟩ : syracuseStep 2216495 = 3324743) B3324743
theorem B3324749 : Blo 2215435 3324749 := bbase (se 3 (by rfl) ⟨623390, by rfl⟩ : syracuseStep 3324749 = 1246781) (by norm_num)
theorem B2216499 : Blo 2215435 2216499 := bstep (se 1 (by rfl) ⟨1662374, by rfl⟩ : syracuseStep 2216499 = 3324749) B3324749
theorem B4987133 : Blo 2215435 4987133 := bbase (se 3 (by rfl) ⟨935087, by rfl⟩ : syracuseStep 4987133 = 1870175) (by norm_num)
theorem B3324755 : Blo 2215435 3324755 := bstep (se 1 (by rfl) ⟨2493566, by rfl⟩ : syracuseStep 3324755 = 4987133) B4987133
theorem B2216503 : Blo 2215435 2216503 := bstep (se 1 (by rfl) ⟨1662377, by rfl⟩ : syracuseStep 2216503 = 3324755) B3324755
theorem B3740357 : Blo 2215435 3740357 := bbase (se 4 (by rfl) ⟨350658, by rfl⟩ : syracuseStep 3740357 = 701317) (by norm_num)
theorem B2493571 : Blo 2215435 2493571 := bstep (se 1 (by rfl) ⟨1870178, by rfl⟩ : syracuseStep 2493571 = 3740357) B3740357
theorem B3324761 : Blo 2215435 3324761 := bstep (se 2 (by rfl) ⟨1246785, by rfl⟩ : syracuseStep 3324761 = 2493571) B2493571
theorem B2216507 : Blo 2215435 2216507 := bstep (se 1 (by rfl) ⟨1662380, by rfl⟩ : syracuseStep 2216507 = 3324761) B3324761
theorem B16831637 : Blo 2215435 16831637 := bbase (se 6 (by rfl) ⟨394491, by rfl⟩ : syracuseStep 16831637 = 788983) (by norm_num)
theorem B11221091 : Blo 2215435 11221091 := bstep (se 1 (by rfl) ⟨8415818, by rfl⟩ : syracuseStep 11221091 = 16831637) B16831637
theorem B7480727 : Blo 2215435 7480727 := bstep (se 1 (by rfl) ⟨5610545, by rfl⟩ : syracuseStep 7480727 = 11221091) B11221091
theorem B4987151 : Blo 2215435 4987151 := bstep (se 1 (by rfl) ⟨3740363, by rfl⟩ : syracuseStep 4987151 = 7480727) B7480727
theorem B3324767 : Blo 2215435 3324767 := bstep (se 1 (by rfl) ⟨2493575, by rfl⟩ : syracuseStep 3324767 = 4987151) B4987151
theorem B2216511 : Blo 2215435 2216511 := bstep (se 1 (by rfl) ⟨1662383, by rfl⟩ : syracuseStep 2216511 = 3324767) B3324767
theorem B3324773 : Blo 2215435 3324773 := bbase (se 4 (by rfl) ⟨311697, by rfl⟩ : syracuseStep 3324773 = 623395) (by norm_num)
theorem B2216515 : Blo 2215435 2216515 := bstep (se 1 (by rfl) ⟨1662386, by rfl⟩ : syracuseStep 2216515 = 3324773) B3324773
theorem B4207925 : Blo 2215435 4207925 := bbase (se 5 (by rfl) ⟨197246, by rfl⟩ : syracuseStep 4207925 = 394493) (by norm_num)
theorem B2805283 : Blo 2215435 2805283 := bstep (se 1 (by rfl) ⟨2103962, by rfl⟩ : syracuseStep 2805283 = 4207925) B4207925
theorem B3740377 : Blo 2215435 3740377 := bstep (se 2 (by rfl) ⟨1402641, by rfl⟩ : syracuseStep 3740377 = 2805283) B2805283
theorem B4987169 : Blo 2215435 4987169 := bstep (se 2 (by rfl) ⟨1870188, by rfl⟩ : syracuseStep 4987169 = 3740377) B3740377
theorem B3324779 : Blo 2215435 3324779 := bstep (se 1 (by rfl) ⟨2493584, by rfl⟩ : syracuseStep 3324779 = 4987169) B4987169
theorem B2216519 : Blo 2215435 2216519 := bstep (se 1 (by rfl) ⟨1662389, by rfl⟩ : syracuseStep 2216519 = 3324779) B3324779
theorem B2493589 : Blo 2215435 2493589 := bbase (se 6 (by rfl) ⟨58443, by rfl⟩ : syracuseStep 2493589 = 116887) (by norm_num)
theorem B3324785 : Blo 2215435 3324785 := bstep (se 2 (by rfl) ⟨1246794, by rfl⟩ : syracuseStep 3324785 = 2493589) B2493589
theorem B2216523 : Blo 2215435 2216523 := bstep (se 1 (by rfl) ⟨1662392, by rfl⟩ : syracuseStep 2216523 = 3324785) B3324785
theorem B2805293 : Blo 2215435 2805293 := bbase (se 3 (by rfl) ⟨525992, by rfl⟩ : syracuseStep 2805293 = 1051985) (by norm_num)
theorem B7480781 : Blo 2215435 7480781 := bstep (se 3 (by rfl) ⟨1402646, by rfl⟩ : syracuseStep 7480781 = 2805293) B2805293
theorem B4987187 : Blo 2215435 4987187 := bstep (se 1 (by rfl) ⟨3740390, by rfl⟩ : syracuseStep 4987187 = 7480781) B7480781
theorem B3324791 : Blo 2215435 3324791 := bstep (se 1 (by rfl) ⟨2493593, by rfl⟩ : syracuseStep 3324791 = 4987187) B4987187
theorem B2216527 : Blo 2215435 2216527 := bstep (se 1 (by rfl) ⟨1662395, by rfl⟩ : syracuseStep 2216527 = 3324791) B3324791
theorem B3324797 : Blo 2215435 3324797 := bbase (se 3 (by rfl) ⟨623399, by rfl⟩ : syracuseStep 3324797 = 1246799) (by norm_num)
theorem B2216531 : Blo 2215435 2216531 := bstep (se 1 (by rfl) ⟨1662398, by rfl⟩ : syracuseStep 2216531 = 3324797) B3324797
theorem B4987205 : Blo 2215435 4987205 := bbase (se 4 (by rfl) ⟨467550, by rfl⟩ : syracuseStep 4987205 = 935101) (by norm_num)
theorem B3324803 : Blo 2215435 3324803 := bstep (se 1 (by rfl) ⟨2493602, by rfl⟩ : syracuseStep 3324803 = 4987205) B4987205
theorem B2216535 : Blo 2215435 2216535 := bstep (se 1 (by rfl) ⟨1662401, by rfl⟩ : syracuseStep 2216535 = 3324803) B3324803
theorem B2995709 : Blo 2215435 2995709 := bbase (se 3 (by rfl) ⟨561695, by rfl⟩ : syracuseStep 2995709 = 1123391) (by norm_num)
theorem B7988557 : Blo 2215435 7988557 := bstep (se 3 (by rfl) ⟨1497854, by rfl⟩ : syracuseStep 7988557 = 2995709) B2995709
theorem B10651409 : Blo 2215435 10651409 := bstep (se 2 (by rfl) ⟨3994278, by rfl⟩ : syracuseStep 10651409 = 7988557) B7988557
theorem B7100939 : Blo 2215435 7100939 := bstep (se 1 (by rfl) ⟨5325704, by rfl⟩ : syracuseStep 7100939 = 10651409) B10651409
theorem B4733959 : Blo 2215435 4733959 := bstep (se 1 (by rfl) ⟨3550469, by rfl⟩ : syracuseStep 4733959 = 7100939) B7100939
theorem B6311945 : Blo 2215435 6311945 := bstep (se 2 (by rfl) ⟨2366979, by rfl⟩ : syracuseStep 6311945 = 4733959) B4733959
theorem B4207963 : Blo 2215435 4207963 := bstep (se 1 (by rfl) ⟨3155972, by rfl⟩ : syracuseStep 4207963 = 6311945) B6311945
theorem B5610617 : Blo 2215435 5610617 := bstep (se 2 (by rfl) ⟨2103981, by rfl⟩ : syracuseStep 5610617 = 4207963) B4207963
theorem B3740411 : Blo 2215435 3740411 := bstep (se 1 (by rfl) ⟨2805308, by rfl⟩ : syracuseStep 3740411 = 5610617) B5610617
theorem B2493607 : Blo 2215435 2493607 := bstep (se 1 (by rfl) ⟨1870205, by rfl⟩ : syracuseStep 2493607 = 3740411) B3740411
theorem B3324809 : Blo 2215435 3324809 := bstep (se 2 (by rfl) ⟨1246803, by rfl⟩ : syracuseStep 3324809 = 2493607) B2493607
theorem B2216539 : Blo 2215435 2216539 := bstep (se 1 (by rfl) ⟨1662404, by rfl⟩ : syracuseStep 2216539 = 3324809) B3324809
theorem B11221253 : Blo 2215435 11221253 := bbase (se 4 (by rfl) ⟨1051992, by rfl⟩ : syracuseStep 11221253 = 2103985) (by norm_num)
theorem B7480835 : Blo 2215435 7480835 := bstep (se 1 (by rfl) ⟨5610626, by rfl⟩ : syracuseStep 7480835 = 11221253) B11221253
theorem B4987223 : Blo 2215435 4987223 := bstep (se 1 (by rfl) ⟨3740417, by rfl⟩ : syracuseStep 4987223 = 7480835) B7480835
theorem B3324815 : Blo 2215435 3324815 := bstep (se 1 (by rfl) ⟨2493611, by rfl⟩ : syracuseStep 3324815 = 4987223) B4987223
theorem B2216543 : Blo 2215435 2216543 := bstep (se 1 (by rfl) ⟨1662407, by rfl⟩ : syracuseStep 2216543 = 3324815) B3324815
theorem B3324821 : Blo 2215435 3324821 := bbase (se 6 (by rfl) ⟨77925, by rfl⟩ : syracuseStep 3324821 = 155851) (by norm_num)
theorem B2216547 : Blo 2215435 2216547 := bstep (se 1 (by rfl) ⟨1662410, by rfl⟩ : syracuseStep 2216547 = 3324821) B3324821
theorem B12623957 : Blo 2215435 12623957 := bbase (se 8 (by rfl) ⟨73968, by rfl⟩ : syracuseStep 12623957 = 147937) (by norm_num)
theorem B8415971 : Blo 2215435 8415971 := bstep (se 1 (by rfl) ⟨6311978, by rfl⟩ : syracuseStep 8415971 = 12623957) B12623957
theorem B5610647 : Blo 2215435 5610647 := bstep (se 1 (by rfl) ⟨4207985, by rfl⟩ : syracuseStep 5610647 = 8415971) B8415971
theorem B3740431 : Blo 2215435 3740431 := bstep (se 1 (by rfl) ⟨2805323, by rfl⟩ : syracuseStep 3740431 = 5610647) B5610647
theorem B4987241 : Blo 2215435 4987241 := bstep (se 2 (by rfl) ⟨1870215, by rfl⟩ : syracuseStep 4987241 = 3740431) B3740431
theorem B3324827 : Blo 2215435 3324827 := bstep (se 1 (by rfl) ⟨2493620, by rfl⟩ : syracuseStep 3324827 = 4987241) B4987241
theorem B2216551 : Blo 2215435 2216551 := bstep (se 1 (by rfl) ⟨1662413, by rfl⟩ : syracuseStep 2216551 = 3324827) B3324827
theorem B2493625 : Blo 2215435 2493625 := bbase (se 2 (by rfl) ⟨935109, by rfl⟩ : syracuseStep 2493625 = 1870219) (by norm_num)
theorem B3324833 : Blo 2215435 3324833 := bstep (se 2 (by rfl) ⟨1246812, by rfl⟩ : syracuseStep 3324833 = 2493625) B2493625
theorem B2216555 : Blo 2215435 2216555 := bstep (se 1 (by rfl) ⟨1662416, by rfl⟩ : syracuseStep 2216555 = 3324833) B3324833
theorem B3550501 : Blo 2215435 3550501 := bbase (se 4 (by rfl) ⟨332859, by rfl⟩ : syracuseStep 3550501 = 665719) (by norm_num)
theorem B4734001 : Blo 2215435 4734001 := bstep (se 2 (by rfl) ⟨1775250, by rfl⟩ : syracuseStep 4734001 = 3550501) B3550501
theorem B6312001 : Blo 2215435 6312001 := bstep (se 2 (by rfl) ⟨2367000, by rfl⟩ : syracuseStep 6312001 = 4734001) B4734001
theorem B8416001 : Blo 2215435 8416001 := bstep (se 2 (by rfl) ⟨3156000, by rfl⟩ : syracuseStep 8416001 = 6312001) B6312001
theorem B5610667 : Blo 2215435 5610667 := bstep (se 1 (by rfl) ⟨4208000, by rfl⟩ : syracuseStep 5610667 = 8416001) B8416001
theorem B7480889 : Blo 2215435 7480889 := bstep (se 2 (by rfl) ⟨2805333, by rfl⟩ : syracuseStep 7480889 = 5610667) B5610667
theorem B4987259 : Blo 2215435 4987259 := bstep (se 1 (by rfl) ⟨3740444, by rfl⟩ : syracuseStep 4987259 = 7480889) B7480889
theorem B3324839 : Blo 2215435 3324839 := bstep (se 1 (by rfl) ⟨2493629, by rfl⟩ : syracuseStep 3324839 = 4987259) B4987259
theorem B2216559 : Blo 2215435 2216559 := bstep (se 1 (by rfl) ⟨1662419, by rfl⟩ : syracuseStep 2216559 = 3324839) B3324839
theorem B3324845 : Blo 2215435 3324845 := bbase (se 3 (by rfl) ⟨623408, by rfl⟩ : syracuseStep 3324845 = 1246817) (by norm_num)
theorem B2216563 : Blo 2215435 2216563 := bstep (se 1 (by rfl) ⟨1662422, by rfl⟩ : syracuseStep 2216563 = 3324845) B3324845
theorem B4987277 : Blo 2215435 4987277 := bbase (se 3 (by rfl) ⟨935114, by rfl⟩ : syracuseStep 4987277 = 1870229) (by norm_num)
theorem B3324851 : Blo 2215435 3324851 := bstep (se 1 (by rfl) ⟨2493638, by rfl⟩ : syracuseStep 3324851 = 4987277) B4987277
theorem B2216567 : Blo 2215435 2216567 := bstep (se 1 (by rfl) ⟨1662425, by rfl⟩ : syracuseStep 2216567 = 3324851) B3324851
theorem B2805349 : Blo 2215435 2805349 := bbase (se 4 (by rfl) ⟨263001, by rfl⟩ : syracuseStep 2805349 = 526003) (by norm_num)
theorem B3740465 : Blo 2215435 3740465 := bstep (se 2 (by rfl) ⟨1402674, by rfl⟩ : syracuseStep 3740465 = 2805349) B2805349
theorem B2493643 : Blo 2215435 2493643 := bstep (se 1 (by rfl) ⟨1870232, by rfl⟩ : syracuseStep 2493643 = 3740465) B3740465
theorem B3324857 : Blo 2215435 3324857 := bstep (se 2 (by rfl) ⟨1246821, by rfl⟩ : syracuseStep 3324857 = 2493643) B2493643
theorem B2216571 : Blo 2215435 2216571 := bstep (se 1 (by rfl) ⟨1662428, by rfl⟩ : syracuseStep 2216571 = 3324857) B3324857
theorem B21303157 : Blo 2215435 21303157 := bbase (se 5 (by rfl) ⟨998585, by rfl⟩ : syracuseStep 21303157 = 1997171) (by norm_num)
theorem B28404209 : Blo 2215435 28404209 := bstep (se 2 (by rfl) ⟨10651578, by rfl⟩ : syracuseStep 28404209 = 21303157) B21303157
theorem B18936139 : Blo 2215435 18936139 := bstep (se 1 (by rfl) ⟨14202104, by rfl⟩ : syracuseStep 18936139 = 28404209) B28404209
theorem B25248185 : Blo 2215435 25248185 := bstep (se 2 (by rfl) ⟨9468069, by rfl⟩ : syracuseStep 25248185 = 18936139) B18936139
theorem B16832123 : Blo 2215435 16832123 := bstep (se 1 (by rfl) ⟨12624092, by rfl⟩ : syracuseStep 16832123 = 25248185) B25248185
theorem B11221415 : Blo 2215435 11221415 := bstep (se 1 (by rfl) ⟨8416061, by rfl⟩ : syracuseStep 11221415 = 16832123) B16832123
theorem B7480943 : Blo 2215435 7480943 := bstep (se 1 (by rfl) ⟨5610707, by rfl⟩ : syracuseStep 7480943 = 11221415) B11221415
theorem B4987295 : Blo 2215435 4987295 := bstep (se 1 (by rfl) ⟨3740471, by rfl⟩ : syracuseStep 4987295 = 7480943) B7480943
theorem B3324863 : Blo 2215435 3324863 := bstep (se 1 (by rfl) ⟨2493647, by rfl⟩ : syracuseStep 3324863 = 4987295) B4987295
theorem B2216575 : Blo 2215435 2216575 := bstep (se 1 (by rfl) ⟨1662431, by rfl⟩ : syracuseStep 2216575 = 3324863) B3324863
theorem B3324869 : Blo 2215435 3324869 := bbase (se 4 (by rfl) ⟨311706, by rfl⟩ : syracuseStep 3324869 = 623413) (by norm_num)
theorem B2216579 : Blo 2215435 2216579 := bstep (se 1 (by rfl) ⟨1662434, by rfl⟩ : syracuseStep 2216579 = 3324869) B3324869
theorem B3740485 : Blo 2215435 3740485 := bbase (se 4 (by rfl) ⟨350670, by rfl⟩ : syracuseStep 3740485 = 701341) (by norm_num)
theorem B4987313 : Blo 2215435 4987313 := bstep (se 2 (by rfl) ⟨1870242, by rfl⟩ : syracuseStep 4987313 = 3740485) B3740485
theorem B3324875 : Blo 2215435 3324875 := bstep (se 1 (by rfl) ⟨2493656, by rfl⟩ : syracuseStep 3324875 = 4987313) B4987313
theorem B2216583 : Blo 2215435 2216583 := bstep (se 1 (by rfl) ⟨1662437, by rfl⟩ : syracuseStep 2216583 = 3324875) B3324875
theorem B2493661 : Blo 2215435 2493661 := bbase (se 3 (by rfl) ⟨467561, by rfl⟩ : syracuseStep 2493661 = 935123) (by norm_num)
theorem B3324881 : Blo 2215435 3324881 := bstep (se 2 (by rfl) ⟨1246830, by rfl⟩ : syracuseStep 3324881 = 2493661) B2493661
theorem B2216587 : Blo 2215435 2216587 := bstep (se 1 (by rfl) ⟨1662440, by rfl⟩ : syracuseStep 2216587 = 3324881) B3324881
theorem B7480997 : Blo 2215435 7480997 := bbase (se 4 (by rfl) ⟨701343, by rfl⟩ : syracuseStep 7480997 = 1402687) (by norm_num)
theorem B4987331 : Blo 2215435 4987331 := bstep (se 1 (by rfl) ⟨3740498, by rfl⟩ : syracuseStep 4987331 = 7480997) B7480997
theorem B3324887 : Blo 2215435 3324887 := bstep (se 1 (by rfl) ⟨2493665, by rfl⟩ : syracuseStep 3324887 = 4987331) B4987331
theorem B2216591 : Blo 2215435 2216591 := bstep (se 1 (by rfl) ⟨1662443, by rfl⟩ : syracuseStep 2216591 = 3324887) B3324887
theorem B3324893 : Blo 2215435 3324893 := bbase (se 3 (by rfl) ⟨623417, by rfl⟩ : syracuseStep 3324893 = 1246835) (by norm_num)
theorem B2216595 : Blo 2215435 2216595 := bstep (se 1 (by rfl) ⟨1662446, by rfl⟩ : syracuseStep 2216595 = 3324893) B3324893
theorem B4987349 : Blo 2215435 4987349 := bbase (se 7 (by rfl) ⟨58445, by rfl⟩ : syracuseStep 4987349 = 116891) (by norm_num)
theorem B3324899 : Blo 2215435 3324899 := bstep (se 1 (by rfl) ⟨2493674, by rfl⟩ : syracuseStep 3324899 = 4987349) B4987349
theorem B2216599 : Blo 2215435 2216599 := bstep (se 1 (by rfl) ⟨1662449, by rfl⟩ : syracuseStep 2216599 = 3324899) B3324899
theorem B11374661 : Blo 2215435 11374661 := bbase (se 4 (by rfl) ⟨1066374, by rfl⟩ : syracuseStep 11374661 = 2132749) (by norm_num)
theorem B7583107 : Blo 2215435 7583107 := bstep (se 1 (by rfl) ⟨5687330, by rfl⟩ : syracuseStep 7583107 = 11374661) B11374661
theorem B10110809 : Blo 2215435 10110809 := bstep (se 2 (by rfl) ⟨3791553, by rfl⟩ : syracuseStep 10110809 = 7583107) B7583107
theorem B6740539 : Blo 2215435 6740539 := bstep (se 1 (by rfl) ⟨5055404, by rfl⟩ : syracuseStep 6740539 = 10110809) B10110809
theorem B35949541 : Blo 2215435 35949541 := bstep (se 4 (by rfl) ⟨3370269, by rfl⟩ : syracuseStep 35949541 = 6740539) B6740539
theorem B47932721 : Blo 2215435 47932721 := bstep (se 2 (by rfl) ⟨17974770, by rfl⟩ : syracuseStep 47932721 = 35949541) B35949541
theorem B31955147 : Blo 2215435 31955147 := bstep (se 1 (by rfl) ⟨23966360, by rfl⟩ : syracuseStep 31955147 = 47932721) B47932721
theorem B21303431 : Blo 2215435 21303431 := bstep (se 1 (by rfl) ⟨15977573, by rfl⟩ : syracuseStep 21303431 = 31955147) B31955147
theorem B14202287 : Blo 2215435 14202287 := bstep (se 1 (by rfl) ⟨10651715, by rfl⟩ : syracuseStep 14202287 = 21303431) B21303431
theorem B9468191 : Blo 2215435 9468191 := bstep (se 1 (by rfl) ⟨7101143, by rfl⟩ : syracuseStep 9468191 = 14202287) B14202287
theorem B6312127 : Blo 2215435 6312127 := bstep (se 1 (by rfl) ⟨4734095, by rfl⟩ : syracuseStep 6312127 = 9468191) B9468191
theorem B8416169 : Blo 2215435 8416169 := bstep (se 2 (by rfl) ⟨3156063, by rfl⟩ : syracuseStep 8416169 = 6312127) B6312127
theorem B5610779 : Blo 2215435 5610779 := bstep (se 1 (by rfl) ⟨4208084, by rfl⟩ : syracuseStep 5610779 = 8416169) B8416169
theorem B3740519 : Blo 2215435 3740519 := bstep (se 1 (by rfl) ⟨2805389, by rfl⟩ : syracuseStep 3740519 = 5610779) B5610779
theorem B2493679 : Blo 2215435 2493679 := bstep (se 1 (by rfl) ⟨1870259, by rfl⟩ : syracuseStep 2493679 = 3740519) B3740519
theorem B3324905 : Blo 2215435 3324905 := bstep (se 2 (by rfl) ⟨1246839, by rfl⟩ : syracuseStep 3324905 = 2493679) B2493679
theorem B2216603 : Blo 2215435 2216603 := bstep (se 1 (by rfl) ⟨1662452, by rfl⟩ : syracuseStep 2216603 = 3324905) B3324905
theorem B10651733 : Blo 2215435 10651733 := bbase (se 8 (by rfl) ⟨62412, by rfl⟩ : syracuseStep 10651733 = 124825) (by norm_num)
theorem B7101155 : Blo 2215435 7101155 := bstep (se 1 (by rfl) ⟨5325866, by rfl⟩ : syracuseStep 7101155 = 10651733) B10651733
theorem B18936413 : Blo 2215435 18936413 := bstep (se 3 (by rfl) ⟨3550577, by rfl⟩ : syracuseStep 18936413 = 7101155) B7101155
theorem B12624275 : Blo 2215435 12624275 := bstep (se 1 (by rfl) ⟨9468206, by rfl⟩ : syracuseStep 12624275 = 18936413) B18936413
theorem B8416183 : Blo 2215435 8416183 := bstep (se 1 (by rfl) ⟨6312137, by rfl⟩ : syracuseStep 8416183 = 12624275) B12624275
theorem B11221577 : Blo 2215435 11221577 := bstep (se 2 (by rfl) ⟨4208091, by rfl⟩ : syracuseStep 11221577 = 8416183) B8416183
theorem B7481051 : Blo 2215435 7481051 := bstep (se 1 (by rfl) ⟨5610788, by rfl⟩ : syracuseStep 7481051 = 11221577) B11221577
theorem B4987367 : Blo 2215435 4987367 := bstep (se 1 (by rfl) ⟨3740525, by rfl⟩ : syracuseStep 4987367 = 7481051) B7481051
theorem B3324911 : Blo 2215435 3324911 := bstep (se 1 (by rfl) ⟨2493683, by rfl⟩ : syracuseStep 3324911 = 4987367) B4987367
theorem B2216607 : Blo 2215435 2216607 := bstep (se 1 (by rfl) ⟨1662455, by rfl⟩ : syracuseStep 2216607 = 3324911) B3324911
theorem B3324917 : Blo 2215435 3324917 := bbase (se 5 (by rfl) ⟨155855, by rfl⟩ : syracuseStep 3324917 = 311711) (by norm_num)
theorem B2216611 : Blo 2215435 2216611 := bstep (se 1 (by rfl) ⟨1662458, by rfl⟩ : syracuseStep 2216611 = 3324917) B3324917
theorem B2843681 : Blo 2215435 2843681 := bbase (se 2 (by rfl) ⟨1066380, by rfl⟩ : syracuseStep 2843681 = 2132761) (by norm_num)
theorem B7583149 : Blo 2215435 7583149 := bstep (se 3 (by rfl) ⟨1421840, by rfl⟩ : syracuseStep 7583149 = 2843681) B2843681
theorem B40443461 : Blo 2215435 40443461 := bstep (se 4 (by rfl) ⟨3791574, by rfl⟩ : syracuseStep 40443461 = 7583149) B7583149
theorem B26962307 : Blo 2215435 26962307 := bstep (se 1 (by rfl) ⟨20221730, by rfl⟩ : syracuseStep 26962307 = 40443461) B40443461
theorem B17974871 : Blo 2215435 17974871 := bstep (se 1 (by rfl) ⟨13481153, by rfl⟩ : syracuseStep 17974871 = 26962307) B26962307
theorem B11983247 : Blo 2215435 11983247 := bstep (se 1 (by rfl) ⟨8987435, by rfl⟩ : syracuseStep 11983247 = 17974871) B17974871
theorem B7988831 : Blo 2215435 7988831 := bstep (se 1 (by rfl) ⟨5991623, by rfl⟩ : syracuseStep 7988831 = 11983247) B11983247
theorem B5325887 : Blo 2215435 5325887 := bstep (se 1 (by rfl) ⟨3994415, by rfl⟩ : syracuseStep 5325887 = 7988831) B7988831
theorem B3550591 : Blo 2215435 3550591 := bstep (se 1 (by rfl) ⟨2662943, by rfl⟩ : syracuseStep 3550591 = 5325887) B5325887
theorem B4734121 : Blo 2215435 4734121 := bstep (se 2 (by rfl) ⟨1775295, by rfl⟩ : syracuseStep 4734121 = 3550591) B3550591
theorem B6312161 : Blo 2215435 6312161 := bstep (se 2 (by rfl) ⟨2367060, by rfl⟩ : syracuseStep 6312161 = 4734121) B4734121
theorem B4208107 : Blo 2215435 4208107 := bstep (se 1 (by rfl) ⟨3156080, by rfl⟩ : syracuseStep 4208107 = 6312161) B6312161
theorem B5610809 : Blo 2215435 5610809 := bstep (se 2 (by rfl) ⟨2104053, by rfl⟩ : syracuseStep 5610809 = 4208107) B4208107
theorem B3740539 : Blo 2215435 3740539 := bstep (se 1 (by rfl) ⟨2805404, by rfl⟩ : syracuseStep 3740539 = 5610809) B5610809
theorem B4987385 : Blo 2215435 4987385 := bstep (se 2 (by rfl) ⟨1870269, by rfl⟩ : syracuseStep 4987385 = 3740539) B3740539
theorem B3324923 : Blo 2215435 3324923 := bstep (se 1 (by rfl) ⟨2493692, by rfl⟩ : syracuseStep 3324923 = 4987385) B4987385
theorem B2216615 : Blo 2215435 2216615 := bstep (se 1 (by rfl) ⟨1662461, by rfl⟩ : syracuseStep 2216615 = 3324923) B3324923
theorem B2493697 : Blo 2215435 2493697 := bbase (se 2 (by rfl) ⟨935136, by rfl⟩ : syracuseStep 2493697 = 1870273) (by norm_num)
theorem B3324929 : Blo 2215435 3324929 := bstep (se 2 (by rfl) ⟨1246848, by rfl⟩ : syracuseStep 3324929 = 2493697) B2493697
theorem B2216619 : Blo 2215435 2216619 := bstep (se 1 (by rfl) ⟨1662464, by rfl⟩ : syracuseStep 2216619 = 3324929) B3324929
theorem B5610829 : Blo 2215435 5610829 := bbase (se 3 (by rfl) ⟨1052030, by rfl⟩ : syracuseStep 5610829 = 2104061) (by norm_num)
theorem B7481105 : Blo 2215435 7481105 := bstep (se 2 (by rfl) ⟨2805414, by rfl⟩ : syracuseStep 7481105 = 5610829) B5610829
theorem B4987403 : Blo 2215435 4987403 := bstep (se 1 (by rfl) ⟨3740552, by rfl⟩ : syracuseStep 4987403 = 7481105) B7481105
theorem B3324935 : Blo 2215435 3324935 := bstep (se 1 (by rfl) ⟨2493701, by rfl⟩ : syracuseStep 3324935 = 4987403) B4987403
theorem B2216623 : Blo 2215435 2216623 := bstep (se 1 (by rfl) ⟨1662467, by rfl⟩ : syracuseStep 2216623 = 3324935) B3324935
theorem B3324941 : Blo 2215435 3324941 := bbase (se 3 (by rfl) ⟨623426, by rfl⟩ : syracuseStep 3324941 = 1246853) (by norm_num)
theorem B2216627 : Blo 2215435 2216627 := bstep (se 1 (by rfl) ⟨1662470, by rfl⟩ : syracuseStep 2216627 = 3324941) B3324941
theorem B4987421 : Blo 2215435 4987421 := bbase (se 3 (by rfl) ⟨935141, by rfl⟩ : syracuseStep 4987421 = 1870283) (by norm_num)
theorem B3324947 : Blo 2215435 3324947 := bstep (se 1 (by rfl) ⟨2493710, by rfl⟩ : syracuseStep 3324947 = 4987421) B4987421
theorem B2216631 : Blo 2215435 2216631 := bstep (se 1 (by rfl) ⟨1662473, by rfl⟩ : syracuseStep 2216631 = 3324947) B3324947
theorem B3740573 : Blo 2215435 3740573 := bbase (se 3 (by rfl) ⟨701357, by rfl⟩ : syracuseStep 3740573 = 1402715) (by norm_num)
theorem B2493715 : Blo 2215435 2493715 := bstep (se 1 (by rfl) ⟨1870286, by rfl⟩ : syracuseStep 2493715 = 3740573) B3740573
theorem B3324953 : Blo 2215435 3324953 := bstep (se 2 (by rfl) ⟨1246857, by rfl⟩ : syracuseStep 3324953 = 2493715) B2493715
theorem B2216635 : Blo 2215435 2216635 := bstep (se 1 (by rfl) ⟨1662476, by rfl⟩ : syracuseStep 2216635 = 3324953) B3324953
theorem B4493765 : Blo 2215435 4493765 := bbase (se 4 (by rfl) ⟨421290, by rfl⟩ : syracuseStep 4493765 = 842581) (by norm_num)
theorem B11983373 : Blo 2215435 11983373 := bstep (se 3 (by rfl) ⟨2246882, by rfl⟩ : syracuseStep 11983373 = 4493765) B4493765
theorem B7988915 : Blo 2215435 7988915 := bstep (se 1 (by rfl) ⟨5991686, by rfl⟩ : syracuseStep 7988915 = 11983373) B11983373
theorem B21303773 : Blo 2215435 21303773 := bstep (se 3 (by rfl) ⟨3994457, by rfl⟩ : syracuseStep 21303773 = 7988915) B7988915
theorem B14202515 : Blo 2215435 14202515 := bstep (se 1 (by rfl) ⟨10651886, by rfl⟩ : syracuseStep 14202515 = 21303773) B21303773
theorem B9468343 : Blo 2215435 9468343 := bstep (se 1 (by rfl) ⟨7101257, by rfl⟩ : syracuseStep 9468343 = 14202515) B14202515
theorem B12624457 : Blo 2215435 12624457 := bstep (se 2 (by rfl) ⟨4734171, by rfl⟩ : syracuseStep 12624457 = 9468343) B9468343
theorem B16832609 : Blo 2215435 16832609 := bstep (se 2 (by rfl) ⟨6312228, by rfl⟩ : syracuseStep 16832609 = 12624457) B12624457
theorem B11221739 : Blo 2215435 11221739 := bstep (se 1 (by rfl) ⟨8416304, by rfl⟩ : syracuseStep 11221739 = 16832609) B16832609
theorem B7481159 : Blo 2215435 7481159 := bstep (se 1 (by rfl) ⟨5610869, by rfl⟩ : syracuseStep 7481159 = 11221739) B11221739
theorem B4987439 : Blo 2215435 4987439 := bstep (se 1 (by rfl) ⟨3740579, by rfl⟩ : syracuseStep 4987439 = 7481159) B7481159
theorem B3324959 : Blo 2215435 3324959 := bstep (se 1 (by rfl) ⟨2493719, by rfl⟩ : syracuseStep 3324959 = 4987439) B4987439
theorem B2216639 : Blo 2215435 2216639 := bstep (se 1 (by rfl) ⟨1662479, by rfl⟩ : syracuseStep 2216639 = 3324959) B3324959
theorem B3324965 : Blo 2215435 3324965 := bbase (se 4 (by rfl) ⟨311715, by rfl⟩ : syracuseStep 3324965 = 623431) (by norm_num)
theorem B2216643 : Blo 2215435 2216643 := bstep (se 1 (by rfl) ⟨1662482, by rfl⟩ : syracuseStep 2216643 = 3324965) B3324965
theorem B2805445 : Blo 2215435 2805445 := bbase (se 4 (by rfl) ⟨263010, by rfl⟩ : syracuseStep 2805445 = 526021) (by norm_num)
theorem B3740593 : Blo 2215435 3740593 := bstep (se 2 (by rfl) ⟨1402722, by rfl⟩ : syracuseStep 3740593 = 2805445) B2805445
theorem B4987457 : Blo 2215435 4987457 := bstep (se 2 (by rfl) ⟨1870296, by rfl⟩ : syracuseStep 4987457 = 3740593) B3740593
theorem B3324971 : Blo 2215435 3324971 := bstep (se 1 (by rfl) ⟨2493728, by rfl⟩ : syracuseStep 3324971 = 4987457) B4987457
theorem B2216647 : Blo 2215435 2216647 := bstep (se 1 (by rfl) ⟨1662485, by rfl⟩ : syracuseStep 2216647 = 3324971) B3324971
theorem B2493733 : Blo 2215435 2493733 := bbase (se 4 (by rfl) ⟨233787, by rfl⟩ : syracuseStep 2493733 = 467575) (by norm_num)
theorem B3324977 : Blo 2215435 3324977 := bstep (se 2 (by rfl) ⟨1246866, by rfl⟩ : syracuseStep 3324977 = 2493733) B2493733
theorem B2216651 : Blo 2215435 2216651 := bstep (se 1 (by rfl) ⟨1662488, by rfl⟩ : syracuseStep 2216651 = 3324977) B3324977
theorem B40995989 : Blo 2215435 40995989 := bbase (se 6 (by rfl) ⟨960843, by rfl⟩ : syracuseStep 40995989 = 1921687) (by norm_num)
theorem B27330659 : Blo 2215435 27330659 := bstep (se 1 (by rfl) ⟨20497994, by rfl⟩ : syracuseStep 27330659 = 40995989) B40995989
theorem B18220439 : Blo 2215435 18220439 := bstep (se 1 (by rfl) ⟨13665329, by rfl⟩ : syracuseStep 18220439 = 27330659) B27330659
theorem B12146959 : Blo 2215435 12146959 := bstep (se 1 (by rfl) ⟨9110219, by rfl⟩ : syracuseStep 12146959 = 18220439) B18220439
theorem B16195945 : Blo 2215435 16195945 := bstep (se 2 (by rfl) ⟨6073479, by rfl⟩ : syracuseStep 16195945 = 12146959) B12146959
theorem B21594593 : Blo 2215435 21594593 := bstep (se 2 (by rfl) ⟨8097972, by rfl⟩ : syracuseStep 21594593 = 16195945) B16195945
theorem B14396395 : Blo 2215435 14396395 := bstep (se 1 (by rfl) ⟨10797296, by rfl⟩ : syracuseStep 14396395 = 21594593) B21594593
theorem B19195193 : Blo 2215435 19195193 := bstep (se 2 (by rfl) ⟨7198197, by rfl⟩ : syracuseStep 19195193 = 14396395) B14396395
theorem B12796795 : Blo 2215435 12796795 := bstep (se 1 (by rfl) ⟨9597596, by rfl⟩ : syracuseStep 12796795 = 19195193) B19195193
theorem B68249573 : Blo 2215435 68249573 := bstep (se 4 (by rfl) ⟨6398397, by rfl⟩ : syracuseStep 68249573 = 12796795) B12796795
theorem B45499715 : Blo 2215435 45499715 := bstep (se 1 (by rfl) ⟨34124786, by rfl⟩ : syracuseStep 45499715 = 68249573) B68249573
theorem B30333143 : Blo 2215435 30333143 := bstep (se 1 (by rfl) ⟨22749857, by rfl⟩ : syracuseStep 30333143 = 45499715) B45499715
theorem B20222095 : Blo 2215435 20222095 := bstep (se 1 (by rfl) ⟨15166571, by rfl⟩ : syracuseStep 20222095 = 30333143) B30333143
theorem B26962793 : Blo 2215435 26962793 := bstep (se 2 (by rfl) ⟨10111047, by rfl⟩ : syracuseStep 26962793 = 20222095) B20222095
theorem B17975195 : Blo 2215435 17975195 := bstep (se 1 (by rfl) ⟨13481396, by rfl⟩ : syracuseStep 17975195 = 26962793) B26962793
theorem B11983463 : Blo 2215435 11983463 := bstep (se 1 (by rfl) ⟨8987597, by rfl⟩ : syracuseStep 11983463 = 17975195) B17975195
theorem B7988975 : Blo 2215435 7988975 := bstep (se 1 (by rfl) ⟨5991731, by rfl⟩ : syracuseStep 7988975 = 11983463) B11983463
theorem B5325983 : Blo 2215435 5325983 := bstep (se 1 (by rfl) ⟨3994487, by rfl⟩ : syracuseStep 5325983 = 7988975) B7988975
theorem B3550655 : Blo 2215435 3550655 := bstep (se 1 (by rfl) ⟨2662991, by rfl⟩ : syracuseStep 3550655 = 5325983) B5325983
theorem B9468413 : Blo 2215435 9468413 := bstep (se 3 (by rfl) ⟨1775327, by rfl⟩ : syracuseStep 9468413 = 3550655) B3550655
theorem B6312275 : Blo 2215435 6312275 := bstep (se 1 (by rfl) ⟨4734206, by rfl⟩ : syracuseStep 6312275 = 9468413) B9468413
theorem B4208183 : Blo 2215435 4208183 := bstep (se 1 (by rfl) ⟨3156137, by rfl⟩ : syracuseStep 4208183 = 6312275) B6312275
theorem B2805455 : Blo 2215435 2805455 := bstep (se 1 (by rfl) ⟨2104091, by rfl⟩ : syracuseStep 2805455 = 4208183) B4208183
theorem B7481213 : Blo 2215435 7481213 := bstep (se 3 (by rfl) ⟨1402727, by rfl⟩ : syracuseStep 7481213 = 2805455) B2805455
theorem B4987475 : Blo 2215435 4987475 := bstep (se 1 (by rfl) ⟨3740606, by rfl⟩ : syracuseStep 4987475 = 7481213) B7481213
theorem B3324983 : Blo 2215435 3324983 := bstep (se 1 (by rfl) ⟨2493737, by rfl⟩ : syracuseStep 3324983 = 4987475) B4987475
theorem B2216655 : Blo 2215435 2216655 := bstep (se 1 (by rfl) ⟨1662491, by rfl⟩ : syracuseStep 2216655 = 3324983) B3324983
theorem B3324989 : Blo 2215435 3324989 := bbase (se 3 (by rfl) ⟨623435, by rfl⟩ : syracuseStep 3324989 = 1246871) (by norm_num)
theorem B2216659 : Blo 2215435 2216659 := bstep (se 1 (by rfl) ⟨1662494, by rfl⟩ : syracuseStep 2216659 = 3324989) B3324989
theorem B4987493 : Blo 2215435 4987493 := bbase (se 4 (by rfl) ⟨467577, by rfl⟩ : syracuseStep 4987493 = 935155) (by norm_num)
theorem B3324995 : Blo 2215435 3324995 := bstep (se 1 (by rfl) ⟨2493746, by rfl⟩ : syracuseStep 3324995 = 4987493) B4987493
theorem B2216663 : Blo 2215435 2216663 := bstep (se 1 (by rfl) ⟨1662497, by rfl⟩ : syracuseStep 2216663 = 3324995) B3324995
theorem B5610941 : Blo 2215435 5610941 := bbase (se 3 (by rfl) ⟨1052051, by rfl⟩ : syracuseStep 5610941 = 2104103) (by norm_num)
theorem B3740627 : Blo 2215435 3740627 := bstep (se 1 (by rfl) ⟨2805470, by rfl⟩ : syracuseStep 3740627 = 5610941) B5610941
theorem B2493751 : Blo 2215435 2493751 := bstep (se 1 (by rfl) ⟨1870313, by rfl⟩ : syracuseStep 2493751 = 3740627) B3740627
theorem B3325001 : Blo 2215435 3325001 := bstep (se 2 (by rfl) ⟨1246875, by rfl⟩ : syracuseStep 3325001 = 2493751) B2493751
theorem B2216667 : Blo 2215435 2216667 := bstep (se 1 (by rfl) ⟨1662500, by rfl⟩ : syracuseStep 2216667 = 3325001) B3325001
theorem B4208213 : Blo 2215435 4208213 := bbase (se 8 (by rfl) ⟨24657, by rfl⟩ : syracuseStep 4208213 = 49315) (by norm_num)
theorem B11221901 : Blo 2215435 11221901 := bstep (se 3 (by rfl) ⟨2104106, by rfl⟩ : syracuseStep 11221901 = 4208213) B4208213
theorem B7481267 : Blo 2215435 7481267 := bstep (se 1 (by rfl) ⟨5610950, by rfl⟩ : syracuseStep 7481267 = 11221901) B11221901
theorem B4987511 : Blo 2215435 4987511 := bstep (se 1 (by rfl) ⟨3740633, by rfl⟩ : syracuseStep 4987511 = 7481267) B7481267
theorem B3325007 : Blo 2215435 3325007 := bstep (se 1 (by rfl) ⟨2493755, by rfl⟩ : syracuseStep 3325007 = 4987511) B4987511
theorem B2216671 : Blo 2215435 2216671 := bstep (se 1 (by rfl) ⟨1662503, by rfl⟩ : syracuseStep 2216671 = 3325007) B3325007
theorem B3325013 : Blo 2215435 3325013 := bbase (se 8 (by rfl) ⟨19482, by rfl⟩ : syracuseStep 3325013 = 38965) (by norm_num)
theorem B2216675 : Blo 2215435 2216675 := bstep (se 1 (by rfl) ⟨1662506, by rfl⟩ : syracuseStep 2216675 = 3325013) B3325013
theorem B14202773 : Blo 2215435 14202773 := bbase (se 6 (by rfl) ⟨332877, by rfl⟩ : syracuseStep 14202773 = 665755) (by norm_num)
theorem B9468515 : Blo 2215435 9468515 := bstep (se 1 (by rfl) ⟨7101386, by rfl⟩ : syracuseStep 9468515 = 14202773) B14202773
theorem B6312343 : Blo 2215435 6312343 := bstep (se 1 (by rfl) ⟨4734257, by rfl⟩ : syracuseStep 6312343 = 9468515) B9468515
theorem B8416457 : Blo 2215435 8416457 := bstep (se 2 (by rfl) ⟨3156171, by rfl⟩ : syracuseStep 8416457 = 6312343) B6312343
theorem B5610971 : Blo 2215435 5610971 := bstep (se 1 (by rfl) ⟨4208228, by rfl⟩ : syracuseStep 5610971 = 8416457) B8416457
theorem B3740647 : Blo 2215435 3740647 := bstep (se 1 (by rfl) ⟨2805485, by rfl⟩ : syracuseStep 3740647 = 5610971) B5610971
theorem B4987529 : Blo 2215435 4987529 := bstep (se 2 (by rfl) ⟨1870323, by rfl⟩ : syracuseStep 4987529 = 3740647) B3740647
theorem B3325019 : Blo 2215435 3325019 := bstep (se 1 (by rfl) ⟨2493764, by rfl⟩ : syracuseStep 3325019 = 4987529) B4987529
theorem B2216679 : Blo 2215435 2216679 := bstep (se 1 (by rfl) ⟨1662509, by rfl⟩ : syracuseStep 2216679 = 3325019) B3325019
theorem B2493769 : Blo 2215435 2493769 := bbase (se 2 (by rfl) ⟨935163, by rfl⟩ : syracuseStep 2493769 = 1870327) (by norm_num)
theorem B3325025 : Blo 2215435 3325025 := bstep (se 2 (by rfl) ⟨1246884, by rfl⟩ : syracuseStep 3325025 = 2493769) B2493769
theorem B2216683 : Blo 2215435 2216683 := bstep (se 1 (by rfl) ⟨1662512, by rfl⟩ : syracuseStep 2216683 = 3325025) B3325025
theorem B4049045 : Blo 2215435 4049045 := bbase (se 6 (by rfl) ⟨94899, by rfl⟩ : syracuseStep 4049045 = 189799) (by norm_num)
theorem B2699363 : Blo 2215435 2699363 := bstep (se 1 (by rfl) ⟨2024522, by rfl⟩ : syracuseStep 2699363 = 4049045) B4049045
theorem B7198301 : Blo 2215435 7198301 := bstep (se 3 (by rfl) ⟨1349681, by rfl⟩ : syracuseStep 7198301 = 2699363) B2699363
theorem B4798867 : Blo 2215435 4798867 := bstep (se 1 (by rfl) ⟨3599150, by rfl⟩ : syracuseStep 4798867 = 7198301) B7198301
theorem B6398489 : Blo 2215435 6398489 := bstep (se 2 (by rfl) ⟨2399433, by rfl⟩ : syracuseStep 6398489 = 4798867) B4798867
theorem B4265659 : Blo 2215435 4265659 := bstep (se 1 (by rfl) ⟨3199244, by rfl⟩ : syracuseStep 4265659 = 6398489) B6398489
theorem B5687545 : Blo 2215435 5687545 := bstep (se 2 (by rfl) ⟨2132829, by rfl⟩ : syracuseStep 5687545 = 4265659) B4265659
theorem B7583393 : Blo 2215435 7583393 := bstep (se 2 (by rfl) ⟨2843772, by rfl⟩ : syracuseStep 7583393 = 5687545) B5687545
theorem B20222381 : Blo 2215435 20222381 := bstep (se 3 (by rfl) ⟨3791696, by rfl⟩ : syracuseStep 20222381 = 7583393) B7583393
theorem B13481587 : Blo 2215435 13481587 := bstep (se 1 (by rfl) ⟨10111190, by rfl⟩ : syracuseStep 13481587 = 20222381) B20222381
theorem B17975449 : Blo 2215435 17975449 := bstep (se 2 (by rfl) ⟨6740793, by rfl⟩ : syracuseStep 17975449 = 13481587) B13481587
theorem B23967265 : Blo 2215435 23967265 := bstep (se 2 (by rfl) ⟨8987724, by rfl⟩ : syracuseStep 23967265 = 17975449) B17975449
theorem B31956353 : Blo 2215435 31956353 := bstep (se 2 (by rfl) ⟨11983632, by rfl⟩ : syracuseStep 31956353 = 23967265) B23967265
theorem B21304235 : Blo 2215435 21304235 := bstep (se 1 (by rfl) ⟨15978176, by rfl⟩ : syracuseStep 21304235 = 31956353) B31956353
theorem B14202823 : Blo 2215435 14202823 := bstep (se 1 (by rfl) ⟨10652117, by rfl⟩ : syracuseStep 14202823 = 21304235) B21304235
theorem B18937097 : Blo 2215435 18937097 := bstep (se 2 (by rfl) ⟨7101411, by rfl⟩ : syracuseStep 18937097 = 14202823) B14202823
theorem B12624731 : Blo 2215435 12624731 := bstep (se 1 (by rfl) ⟨9468548, by rfl⟩ : syracuseStep 12624731 = 18937097) B18937097
theorem B8416487 : Blo 2215435 8416487 := bstep (se 1 (by rfl) ⟨6312365, by rfl⟩ : syracuseStep 8416487 = 12624731) B12624731
theorem B5610991 : Blo 2215435 5610991 := bstep (se 1 (by rfl) ⟨4208243, by rfl⟩ : syracuseStep 5610991 = 8416487) B8416487
theorem B7481321 : Blo 2215435 7481321 := bstep (se 2 (by rfl) ⟨2805495, by rfl⟩ : syracuseStep 7481321 = 5610991) B5610991
theorem B4987547 : Blo 2215435 4987547 := bstep (se 1 (by rfl) ⟨3740660, by rfl⟩ : syracuseStep 4987547 = 7481321) B7481321
theorem B3325031 : Blo 2215435 3325031 := bstep (se 1 (by rfl) ⟨2493773, by rfl⟩ : syracuseStep 3325031 = 4987547) B4987547
theorem B2216687 : Blo 2215435 2216687 := bstep (se 1 (by rfl) ⟨1662515, by rfl⟩ : syracuseStep 2216687 = 3325031) B3325031
theorem B3325037 : Blo 2215435 3325037 := bbase (se 3 (by rfl) ⟨623444, by rfl⟩ : syracuseStep 3325037 = 1246889) (by norm_num)
theorem B2216691 : Blo 2215435 2216691 := bstep (se 1 (by rfl) ⟨1662518, by rfl⟩ : syracuseStep 2216691 = 3325037) B3325037
theorem B4987565 : Blo 2215435 4987565 := bbase (se 3 (by rfl) ⟨935168, by rfl⟩ : syracuseStep 4987565 = 1870337) (by norm_num)
theorem B3325043 : Blo 2215435 3325043 := bstep (se 1 (by rfl) ⟨2493782, by rfl⟩ : syracuseStep 3325043 = 4987565) B4987565
theorem B2216695 : Blo 2215435 2216695 := bstep (se 1 (by rfl) ⟨1662521, by rfl⟩ : syracuseStep 2216695 = 3325043) B3325043
theorem B4734301 : Blo 2215435 4734301 := bbase (se 3 (by rfl) ⟨887681, by rfl⟩ : syracuseStep 4734301 = 1775363) (by norm_num)
theorem B6312401 : Blo 2215435 6312401 := bstep (se 2 (by rfl) ⟨2367150, by rfl⟩ : syracuseStep 6312401 = 4734301) B4734301
theorem B4208267 : Blo 2215435 4208267 := bstep (se 1 (by rfl) ⟨3156200, by rfl⟩ : syracuseStep 4208267 = 6312401) B6312401
theorem B2805511 : Blo 2215435 2805511 := bstep (se 1 (by rfl) ⟨2104133, by rfl⟩ : syracuseStep 2805511 = 4208267) B4208267
theorem B3740681 : Blo 2215435 3740681 := bstep (se 2 (by rfl) ⟨1402755, by rfl⟩ : syracuseStep 3740681 = 2805511) B2805511
theorem B2493787 : Blo 2215435 2493787 := bstep (se 1 (by rfl) ⟨1870340, by rfl⟩ : syracuseStep 2493787 = 3740681) B3740681
theorem B3325049 : Blo 2215435 3325049 := bstep (se 2 (by rfl) ⟨1246893, by rfl⟩ : syracuseStep 3325049 = 2493787) B2493787
theorem B2216699 : Blo 2215435 2216699 := bstep (se 1 (by rfl) ⟨1662524, by rfl⟩ : syracuseStep 2216699 = 3325049) B3325049
theorem B3370421 : Blo 2215435 3370421 := bbase (se 5 (by rfl) ⟨157988, by rfl⟩ : syracuseStep 3370421 = 315977) (by norm_num)
theorem B8987789 : Blo 2215435 8987789 := bstep (se 3 (by rfl) ⟨1685210, by rfl⟩ : syracuseStep 8987789 = 3370421) B3370421
theorem B5991859 : Blo 2215435 5991859 := bstep (se 1 (by rfl) ⟨4493894, by rfl⟩ : syracuseStep 5991859 = 8987789) B8987789
theorem B31956581 : Blo 2215435 31956581 := bstep (se 4 (by rfl) ⟨2995929, by rfl⟩ : syracuseStep 31956581 = 5991859) B5991859
theorem B21304387 : Blo 2215435 21304387 := bstep (se 1 (by rfl) ⟨15978290, by rfl⟩ : syracuseStep 21304387 = 31956581) B31956581
theorem B28405849 : Blo 2215435 28405849 := bstep (se 2 (by rfl) ⟨10652193, by rfl⟩ : syracuseStep 28405849 = 21304387) B21304387
theorem B37874465 : Blo 2215435 37874465 := bstep (se 2 (by rfl) ⟨14202924, by rfl⟩ : syracuseStep 37874465 = 28405849) B28405849
theorem B25249643 : Blo 2215435 25249643 := bstep (se 1 (by rfl) ⟨18937232, by rfl⟩ : syracuseStep 25249643 = 37874465) B37874465
theorem B16833095 : Blo 2215435 16833095 := bstep (se 1 (by rfl) ⟨12624821, by rfl⟩ : syracuseStep 16833095 = 25249643) B25249643
theorem B11222063 : Blo 2215435 11222063 := bstep (se 1 (by rfl) ⟨8416547, by rfl⟩ : syracuseStep 11222063 = 16833095) B16833095
theorem B7481375 : Blo 2215435 7481375 := bstep (se 1 (by rfl) ⟨5611031, by rfl⟩ : syracuseStep 7481375 = 11222063) B11222063
theorem B4987583 : Blo 2215435 4987583 := bstep (se 1 (by rfl) ⟨3740687, by rfl⟩ : syracuseStep 4987583 = 7481375) B7481375
theorem B3325055 : Blo 2215435 3325055 := bstep (se 1 (by rfl) ⟨2493791, by rfl⟩ : syracuseStep 3325055 = 4987583) B4987583
theorem B2216703 : Blo 2215435 2216703 := bstep (se 1 (by rfl) ⟨1662527, by rfl⟩ : syracuseStep 2216703 = 3325055) B3325055
theorem B3325061 : Blo 2215435 3325061 := bbase (se 4 (by rfl) ⟨311724, by rfl⟩ : syracuseStep 3325061 = 623449) (by norm_num)
theorem B2216707 : Blo 2215435 2216707 := bstep (se 1 (by rfl) ⟨1662530, by rfl⟩ : syracuseStep 2216707 = 3325061) B3325061
theorem B3740701 : Blo 2215435 3740701 := bbase (se 3 (by rfl) ⟨701381, by rfl⟩ : syracuseStep 3740701 = 1402763) (by norm_num)
theorem B4987601 : Blo 2215435 4987601 := bstep (se 2 (by rfl) ⟨1870350, by rfl⟩ : syracuseStep 4987601 = 3740701) B3740701
theorem B3325067 : Blo 2215435 3325067 := bstep (se 1 (by rfl) ⟨2493800, by rfl⟩ : syracuseStep 3325067 = 4987601) B4987601
theorem B2216711 : Blo 2215435 2216711 := bstep (se 1 (by rfl) ⟨1662533, by rfl⟩ : syracuseStep 2216711 = 3325067) B3325067
theorem B2493805 : Blo 2215435 2493805 := bbase (se 3 (by rfl) ⟨467588, by rfl⟩ : syracuseStep 2493805 = 935177) (by norm_num)
theorem B3325073 : Blo 2215435 3325073 := bstep (se 2 (by rfl) ⟨1246902, by rfl⟩ : syracuseStep 3325073 = 2493805) B2493805
theorem B2216715 : Blo 2215435 2216715 := bstep (se 1 (by rfl) ⟨1662536, by rfl⟩ : syracuseStep 2216715 = 3325073) B3325073
theorem B7481429 : Blo 2215435 7481429 := bbase (se 8 (by rfl) ⟨43836, by rfl⟩ : syracuseStep 7481429 = 87673) (by norm_num)
theorem B4987619 : Blo 2215435 4987619 := bstep (se 1 (by rfl) ⟨3740714, by rfl⟩ : syracuseStep 4987619 = 7481429) B7481429
theorem B3325079 : Blo 2215435 3325079 := bstep (se 1 (by rfl) ⟨2493809, by rfl⟩ : syracuseStep 3325079 = 4987619) B4987619
theorem B2216719 : Blo 2215435 2216719 := bstep (se 1 (by rfl) ⟨1662539, by rfl⟩ : syracuseStep 2216719 = 3325079) B3325079
theorem B3325085 : Blo 2215435 3325085 := bbase (se 3 (by rfl) ⟨623453, by rfl⟩ : syracuseStep 3325085 = 1246907) (by norm_num)
theorem B2216723 : Blo 2215435 2216723 := bstep (se 1 (by rfl) ⟨1662542, by rfl⟩ : syracuseStep 2216723 = 3325085) B3325085
theorem B4987637 : Blo 2215435 4987637 := bbase (se 5 (by rfl) ⟨233795, by rfl⟩ : syracuseStep 4987637 = 467591) (by norm_num)
theorem B3325091 : Blo 2215435 3325091 := bstep (se 1 (by rfl) ⟨2493818, by rfl⟩ : syracuseStep 3325091 = 4987637) B4987637
theorem B2216727 : Blo 2215435 2216727 := bstep (se 1 (by rfl) ⟨1662545, by rfl⟩ : syracuseStep 2216727 = 3325091) B3325091
theorem B5326165 : Blo 2215435 5326165 := bbase (se 12 (by rfl) ⟨1950, by rfl⟩ : syracuseStep 5326165 = 3901) (by norm_num)
theorem B28406213 : Blo 2215435 28406213 := bstep (se 4 (by rfl) ⟨2663082, by rfl⟩ : syracuseStep 28406213 = 5326165) B5326165
theorem B18937475 : Blo 2215435 18937475 := bstep (se 1 (by rfl) ⟨14203106, by rfl⟩ : syracuseStep 18937475 = 28406213) B28406213
theorem B12624983 : Blo 2215435 12624983 := bstep (se 1 (by rfl) ⟨9468737, by rfl⟩ : syracuseStep 12624983 = 18937475) B18937475
theorem B8416655 : Blo 2215435 8416655 := bstep (se 1 (by rfl) ⟨6312491, by rfl⟩ : syracuseStep 8416655 = 12624983) B12624983
theorem B5611103 : Blo 2215435 5611103 := bstep (se 1 (by rfl) ⟨4208327, by rfl⟩ : syracuseStep 5611103 = 8416655) B8416655
theorem B3740735 : Blo 2215435 3740735 := bstep (se 1 (by rfl) ⟨2805551, by rfl⟩ : syracuseStep 3740735 = 5611103) B5611103
theorem B2493823 : Blo 2215435 2493823 := bstep (se 1 (by rfl) ⟨1870367, by rfl⟩ : syracuseStep 2493823 = 3740735) B3740735
theorem B3325097 : Blo 2215435 3325097 := bstep (se 2 (by rfl) ⟨1246911, by rfl⟩ : syracuseStep 3325097 = 2493823) B2493823
theorem B2216731 : Blo 2215435 2216731 := bstep (se 1 (by rfl) ⟨1662548, by rfl⟩ : syracuseStep 2216731 = 3325097) B3325097
theorem B2527853 : Blo 2215435 2527853 := bbase (se 3 (by rfl) ⟨473972, by rfl⟩ : syracuseStep 2527853 = 947945) (by norm_num)
theorem B26963765 : Blo 2215435 26963765 := bstep (se 5 (by rfl) ⟨1263926, by rfl⟩ : syracuseStep 26963765 = 2527853) B2527853
theorem B17975843 : Blo 2215435 17975843 := bstep (se 1 (by rfl) ⟨13481882, by rfl⟩ : syracuseStep 17975843 = 26963765) B26963765
theorem B11983895 : Blo 2215435 11983895 := bstep (se 1 (by rfl) ⟨8987921, by rfl⟩ : syracuseStep 11983895 = 17975843) B17975843
theorem B7989263 : Blo 2215435 7989263 := bstep (se 1 (by rfl) ⟨5991947, by rfl⟩ : syracuseStep 7989263 = 11983895) B11983895
theorem B5326175 : Blo 2215435 5326175 := bstep (se 1 (by rfl) ⟨3994631, by rfl⟩ : syracuseStep 5326175 = 7989263) B7989263
theorem B3550783 : Blo 2215435 3550783 := bstep (se 1 (by rfl) ⟨2663087, by rfl⟩ : syracuseStep 3550783 = 5326175) B5326175
theorem B4734377 : Blo 2215435 4734377 := bstep (se 2 (by rfl) ⟨1775391, by rfl⟩ : syracuseStep 4734377 = 3550783) B3550783
theorem B3156251 : Blo 2215435 3156251 := bstep (se 1 (by rfl) ⟨2367188, by rfl⟩ : syracuseStep 3156251 = 4734377) B4734377
theorem B8416669 : Blo 2215435 8416669 := bstep (se 3 (by rfl) ⟨1578125, by rfl⟩ : syracuseStep 8416669 = 3156251) B3156251
theorem B11222225 : Blo 2215435 11222225 := bstep (se 2 (by rfl) ⟨4208334, by rfl⟩ : syracuseStep 11222225 = 8416669) B8416669
theorem B7481483 : Blo 2215435 7481483 := bstep (se 1 (by rfl) ⟨5611112, by rfl⟩ : syracuseStep 7481483 = 11222225) B11222225
theorem B4987655 : Blo 2215435 4987655 := bstep (se 1 (by rfl) ⟨3740741, by rfl⟩ : syracuseStep 4987655 = 7481483) B7481483
theorem B3325103 : Blo 2215435 3325103 := bstep (se 1 (by rfl) ⟨2493827, by rfl⟩ : syracuseStep 3325103 = 4987655) B4987655
theorem B2216735 : Blo 2215435 2216735 := bstep (se 1 (by rfl) ⟨1662551, by rfl⟩ : syracuseStep 2216735 = 3325103) B3325103
theorem B3325109 : Blo 2215435 3325109 := bbase (se 5 (by rfl) ⟨155864, by rfl⟩ : syracuseStep 3325109 = 311729) (by norm_num)
theorem B2216739 : Blo 2215435 2216739 := bstep (se 1 (by rfl) ⟨1662554, by rfl⟩ : syracuseStep 2216739 = 3325109) B3325109
theorem B5611133 : Blo 2215435 5611133 := bbase (se 3 (by rfl) ⟨1052087, by rfl⟩ : syracuseStep 5611133 = 2104175) (by norm_num)
theorem B3740755 : Blo 2215435 3740755 := bstep (se 1 (by rfl) ⟨2805566, by rfl⟩ : syracuseStep 3740755 = 5611133) B5611133
theorem B4987673 : Blo 2215435 4987673 := bstep (se 2 (by rfl) ⟨1870377, by rfl⟩ : syracuseStep 4987673 = 3740755) B3740755
theorem B3325115 : Blo 2215435 3325115 := bstep (se 1 (by rfl) ⟨2493836, by rfl⟩ : syracuseStep 3325115 = 4987673) B4987673
theorem B2216743 : Blo 2215435 2216743 := bstep (se 1 (by rfl) ⟨1662557, by rfl⟩ : syracuseStep 2216743 = 3325115) B3325115
theorem B2493841 : Blo 2215435 2493841 := bbase (se 2 (by rfl) ⟨935190, by rfl⟩ : syracuseStep 2493841 = 1870381) (by norm_num)
theorem B3325121 : Blo 2215435 3325121 := bstep (se 2 (by rfl) ⟨1246920, by rfl⟩ : syracuseStep 3325121 = 2493841) B2493841
theorem B2216747 : Blo 2215435 2216747 := bstep (se 1 (by rfl) ⟨1662560, by rfl⟩ : syracuseStep 2216747 = 3325121) B3325121
theorem B4208365 : Blo 2215435 4208365 := bbase (se 3 (by rfl) ⟨789068, by rfl⟩ : syracuseStep 4208365 = 1578137) (by norm_num)
theorem B5611153 : Blo 2215435 5611153 := bstep (se 2 (by rfl) ⟨2104182, by rfl⟩ : syracuseStep 5611153 = 4208365) B4208365
theorem B7481537 : Blo 2215435 7481537 := bstep (se 2 (by rfl) ⟨2805576, by rfl⟩ : syracuseStep 7481537 = 5611153) B5611153
theorem B4987691 : Blo 2215435 4987691 := bstep (se 1 (by rfl) ⟨3740768, by rfl⟩ : syracuseStep 4987691 = 7481537) B7481537
theorem B3325127 : Blo 2215435 3325127 := bstep (se 1 (by rfl) ⟨2493845, by rfl⟩ : syracuseStep 3325127 = 4987691) B4987691
theorem B2216751 : Blo 2215435 2216751 := bstep (se 1 (by rfl) ⟨1662563, by rfl⟩ : syracuseStep 2216751 = 3325127) B3325127
theorem B3325133 : Blo 2215435 3325133 := bbase (se 3 (by rfl) ⟨623462, by rfl⟩ : syracuseStep 3325133 = 1246925) (by norm_num)
theorem B2216755 : Blo 2215435 2216755 := bstep (se 1 (by rfl) ⟨1662566, by rfl⟩ : syracuseStep 2216755 = 3325133) B3325133
theorem B4987709 : Blo 2215435 4987709 := bbase (se 3 (by rfl) ⟨935195, by rfl⟩ : syracuseStep 4987709 = 1870391) (by norm_num)
theorem B3325139 : Blo 2215435 3325139 := bstep (se 1 (by rfl) ⟨2493854, by rfl⟩ : syracuseStep 3325139 = 4987709) B4987709
theorem B2216759 : Blo 2215435 2216759 := bstep (se 1 (by rfl) ⟨1662569, by rfl⟩ : syracuseStep 2216759 = 3325139) B3325139
theorem B3740789 : Blo 2215435 3740789 := bbase (se 5 (by rfl) ⟨175349, by rfl⟩ : syracuseStep 3740789 = 350699) (by norm_num)
theorem B2493859 : Blo 2215435 2493859 := bstep (se 1 (by rfl) ⟨1870394, by rfl⟩ : syracuseStep 2493859 = 3740789) B3740789
theorem B3325145 : Blo 2215435 3325145 := bstep (se 2 (by rfl) ⟨1246929, by rfl⟩ : syracuseStep 3325145 = 2493859) B2493859
theorem B2216763 : Blo 2215435 2216763 := bstep (se 1 (by rfl) ⟨1662572, by rfl⟩ : syracuseStep 2216763 = 3325145) B3325145
theorem B4734445 : Blo 2215435 4734445 := bbase (se 3 (by rfl) ⟨887708, by rfl⟩ : syracuseStep 4734445 = 1775417) (by norm_num)
theorem B6312593 : Blo 2215435 6312593 := bstep (se 2 (by rfl) ⟨2367222, by rfl⟩ : syracuseStep 6312593 = 4734445) B4734445
theorem B16833581 : Blo 2215435 16833581 := bstep (se 3 (by rfl) ⟨3156296, by rfl⟩ : syracuseStep 16833581 = 6312593) B6312593
theorem B11222387 : Blo 2215435 11222387 := bstep (se 1 (by rfl) ⟨8416790, by rfl⟩ : syracuseStep 11222387 = 16833581) B16833581
theorem B7481591 : Blo 2215435 7481591 := bstep (se 1 (by rfl) ⟨5611193, by rfl⟩ : syracuseStep 7481591 = 11222387) B11222387
theorem B4987727 : Blo 2215435 4987727 := bstep (se 1 (by rfl) ⟨3740795, by rfl⟩ : syracuseStep 4987727 = 7481591) B7481591
theorem B3325151 : Blo 2215435 3325151 := bstep (se 1 (by rfl) ⟨2493863, by rfl⟩ : syracuseStep 3325151 = 4987727) B4987727
theorem B2216767 : Blo 2215435 2216767 := bstep (se 1 (by rfl) ⟨1662575, by rfl⟩ : syracuseStep 2216767 = 3325151) B3325151
theorem B3325157 : Blo 2215435 3325157 := bbase (se 4 (by rfl) ⟨311733, by rfl⟩ : syracuseStep 3325157 = 623467) (by norm_num)
theorem B2216771 : Blo 2215435 2216771 := bstep (se 1 (by rfl) ⟨1662578, by rfl⟩ : syracuseStep 2216771 = 3325157) B3325157
theorem B61497301 : Blo 2215435 61497301 := bbase (se 7 (by rfl) ⟨720671, by rfl⟩ : syracuseStep 61497301 = 1441343) (by norm_num)
theorem B81996401 : Blo 2215435 81996401 := bstep (se 2 (by rfl) ⟨30748650, by rfl⟩ : syracuseStep 81996401 = 61497301) B61497301
theorem B54664267 : Blo 2215435 54664267 := bstep (se 1 (by rfl) ⟨40998200, by rfl⟩ : syracuseStep 54664267 = 81996401) B81996401
theorem B72885689 : Blo 2215435 72885689 := bstep (se 2 (by rfl) ⟨27332133, by rfl⟩ : syracuseStep 72885689 = 54664267) B54664267
theorem B48590459 : Blo 2215435 48590459 := bstep (se 1 (by rfl) ⟨36442844, by rfl⟩ : syracuseStep 48590459 = 72885689) B72885689
theorem B32393639 : Blo 2215435 32393639 := bstep (se 1 (by rfl) ⟨24295229, by rfl⟩ : syracuseStep 32393639 = 48590459) B48590459
theorem B86383037 : Blo 2215435 86383037 := bstep (se 3 (by rfl) ⟨16196819, by rfl⟩ : syracuseStep 86383037 = 32393639) B32393639
theorem B230354765 : Blo 2215435 230354765 := bstep (se 3 (by rfl) ⟨43191518, by rfl⟩ : syracuseStep 230354765 = 86383037) B86383037
theorem B153569843 : Blo 2215435 153569843 := bstep (se 1 (by rfl) ⟨115177382, by rfl⟩ : syracuseStep 153569843 = 230354765) B230354765
theorem B102379895 : Blo 2215435 102379895 := bstep (se 1 (by rfl) ⟨76784921, by rfl⟩ : syracuseStep 102379895 = 153569843) B153569843
theorem B68253263 : Blo 2215435 68253263 := bstep (se 1 (by rfl) ⟨51189947, by rfl⟩ : syracuseStep 68253263 = 102379895) B102379895
theorem B45502175 : Blo 2215435 45502175 := bstep (se 1 (by rfl) ⟨34126631, by rfl⟩ : syracuseStep 45502175 = 68253263) B68253263
theorem B121339133 : Blo 2215435 121339133 := bstep (se 3 (by rfl) ⟨22751087, by rfl⟩ : syracuseStep 121339133 = 45502175) B45502175
theorem B80892755 : Blo 2215435 80892755 := bstep (se 1 (by rfl) ⟨60669566, by rfl⟩ : syracuseStep 80892755 = 121339133) B121339133
theorem B53928503 : Blo 2215435 53928503 := bstep (se 1 (by rfl) ⟨40446377, by rfl⟩ : syracuseStep 53928503 = 80892755) B80892755
theorem B35952335 : Blo 2215435 35952335 := bstep (se 1 (by rfl) ⟨26964251, by rfl⟩ : syracuseStep 35952335 = 53928503) B53928503
theorem B23968223 : Blo 2215435 23968223 := bstep (se 1 (by rfl) ⟨17976167, by rfl⟩ : syracuseStep 23968223 = 35952335) B35952335
theorem B15978815 : Blo 2215435 15978815 := bstep (se 1 (by rfl) ⟨11984111, by rfl⟩ : syracuseStep 15978815 = 23968223) B23968223
theorem B10652543 : Blo 2215435 10652543 := bstep (se 1 (by rfl) ⟨7989407, by rfl⟩ : syracuseStep 10652543 = 15978815) B15978815
theorem B7101695 : Blo 2215435 7101695 := bstep (se 1 (by rfl) ⟨5326271, by rfl⟩ : syracuseStep 7101695 = 10652543) B10652543
theorem B4734463 : Blo 2215435 4734463 := bstep (se 1 (by rfl) ⟨3550847, by rfl⟩ : syracuseStep 4734463 = 7101695) B7101695
theorem B6312617 : Blo 2215435 6312617 := bstep (se 2 (by rfl) ⟨2367231, by rfl⟩ : syracuseStep 6312617 = 4734463) B4734463
theorem B4208411 : Blo 2215435 4208411 := bstep (se 1 (by rfl) ⟨3156308, by rfl⟩ : syracuseStep 4208411 = 6312617) B6312617
theorem B2805607 : Blo 2215435 2805607 := bstep (se 1 (by rfl) ⟨2104205, by rfl⟩ : syracuseStep 2805607 = 4208411) B4208411
theorem B3740809 : Blo 2215435 3740809 := bstep (se 2 (by rfl) ⟨1402803, by rfl⟩ : syracuseStep 3740809 = 2805607) B2805607
theorem B4987745 : Blo 2215435 4987745 := bstep (se 2 (by rfl) ⟨1870404, by rfl⟩ : syracuseStep 4987745 = 3740809) B3740809
theorem B3325163 : Blo 2215435 3325163 := bstep (se 1 (by rfl) ⟨2493872, by rfl⟩ : syracuseStep 3325163 = 4987745) B4987745
theorem B2216775 : Blo 2215435 2216775 := bstep (se 1 (by rfl) ⟨1662581, by rfl⟩ : syracuseStep 2216775 = 3325163) B3325163
theorem B2493877 : Blo 2215435 2493877 := bbase (se 5 (by rfl) ⟨116900, by rfl⟩ : syracuseStep 2493877 = 233801) (by norm_num)
theorem B3325169 : Blo 2215435 3325169 := bstep (se 2 (by rfl) ⟨1246938, by rfl⟩ : syracuseStep 3325169 = 2493877) B2493877
theorem B2216779 : Blo 2215435 2216779 := bstep (se 1 (by rfl) ⟨1662584, by rfl⟩ : syracuseStep 2216779 = 3325169) B3325169
theorem B2805617 : Blo 2215435 2805617 := bbase (se 2 (by rfl) ⟨1052106, by rfl⟩ : syracuseStep 2805617 = 2104213) (by norm_num)
theorem B7481645 : Blo 2215435 7481645 := bstep (se 3 (by rfl) ⟨1402808, by rfl⟩ : syracuseStep 7481645 = 2805617) B2805617
theorem B4987763 : Blo 2215435 4987763 := bstep (se 1 (by rfl) ⟨3740822, by rfl⟩ : syracuseStep 4987763 = 7481645) B7481645
theorem B3325175 : Blo 2215435 3325175 := bstep (se 1 (by rfl) ⟨2493881, by rfl⟩ : syracuseStep 3325175 = 4987763) B4987763
theorem B2216783 : Blo 2215435 2216783 := bstep (se 1 (by rfl) ⟨1662587, by rfl⟩ : syracuseStep 2216783 = 3325175) B3325175
theorem B3325181 : Blo 2215435 3325181 := bbase (se 3 (by rfl) ⟨623471, by rfl⟩ : syracuseStep 3325181 = 1246943) (by norm_num)
theorem B2216787 : Blo 2215435 2216787 := bstep (se 1 (by rfl) ⟨1662590, by rfl⟩ : syracuseStep 2216787 = 3325181) B3325181
theorem B4987781 : Blo 2215435 4987781 := bbase (se 4 (by rfl) ⟨467604, by rfl⟩ : syracuseStep 4987781 = 935209) (by norm_num)
theorem B3325187 : Blo 2215435 3325187 := bstep (se 1 (by rfl) ⟨2493890, by rfl⟩ : syracuseStep 3325187 = 4987781) B4987781
theorem B2216791 : Blo 2215435 2216791 := bstep (se 1 (by rfl) ⟨1662593, by rfl⟩ : syracuseStep 2216791 = 3325187) B3325187
theorem B2367253 : Blo 2215435 2367253 := bbase (se 6 (by rfl) ⟨55482, by rfl⟩ : syracuseStep 2367253 = 110965) (by norm_num)
theorem B3156337 : Blo 2215435 3156337 := bstep (se 2 (by rfl) ⟨1183626, by rfl⟩ : syracuseStep 3156337 = 2367253) B2367253
theorem B4208449 : Blo 2215435 4208449 := bstep (se 2 (by rfl) ⟨1578168, by rfl⟩ : syracuseStep 4208449 = 3156337) B3156337
theorem B5611265 : Blo 2215435 5611265 := bstep (se 2 (by rfl) ⟨2104224, by rfl⟩ : syracuseStep 5611265 = 4208449) B4208449
theorem B3740843 : Blo 2215435 3740843 := bstep (se 1 (by rfl) ⟨2805632, by rfl⟩ : syracuseStep 3740843 = 5611265) B5611265
theorem B2493895 : Blo 2215435 2493895 := bstep (se 1 (by rfl) ⟨1870421, by rfl⟩ : syracuseStep 2493895 = 3740843) B3740843
theorem B3325193 : Blo 2215435 3325193 := bstep (se 2 (by rfl) ⟨1246947, by rfl⟩ : syracuseStep 3325193 = 2493895) B2493895
theorem B2216795 : Blo 2215435 2216795 := bstep (se 1 (by rfl) ⟨1662596, by rfl⟩ : syracuseStep 2216795 = 3325193) B3325193
theorem B11222549 : Blo 2215435 11222549 := bbase (se 6 (by rfl) ⟨263028, by rfl⟩ : syracuseStep 11222549 = 526057) (by norm_num)
theorem B7481699 : Blo 2215435 7481699 := bstep (se 1 (by rfl) ⟨5611274, by rfl⟩ : syracuseStep 7481699 = 11222549) B11222549
theorem B4987799 : Blo 2215435 4987799 := bstep (se 1 (by rfl) ⟨3740849, by rfl⟩ : syracuseStep 4987799 = 7481699) B7481699
theorem B3325199 : Blo 2215435 3325199 := bstep (se 1 (by rfl) ⟨2493899, by rfl⟩ : syracuseStep 3325199 = 4987799) B4987799
theorem B2216799 : Blo 2215435 2216799 := bstep (se 1 (by rfl) ⟨1662599, by rfl⟩ : syracuseStep 2216799 = 3325199) B3325199
theorem B3325205 : Blo 2215435 3325205 := bbase (se 6 (by rfl) ⟨77934, by rfl⟩ : syracuseStep 3325205 = 155869) (by norm_num)
theorem B2216803 : Blo 2215435 2216803 := bstep (se 1 (by rfl) ⟨1662602, by rfl⟩ : syracuseStep 2216803 = 3325205) B3325205
theorem B2247053 : Blo 2215435 2247053 := bbase (se 3 (by rfl) ⟨421322, by rfl⟩ : syracuseStep 2247053 = 842645) (by norm_num)
theorem B5992141 : Blo 2215435 5992141 := bstep (se 3 (by rfl) ⟨1123526, by rfl⟩ : syracuseStep 5992141 = 2247053) B2247053
theorem B7989521 : Blo 2215435 7989521 := bstep (se 2 (by rfl) ⟨2996070, by rfl⟩ : syracuseStep 7989521 = 5992141) B5992141
theorem B21305389 : Blo 2215435 21305389 := bstep (se 3 (by rfl) ⟨3994760, by rfl⟩ : syracuseStep 21305389 = 7989521) B7989521
theorem B28407185 : Blo 2215435 28407185 := bstep (se 2 (by rfl) ⟨10652694, by rfl⟩ : syracuseStep 28407185 = 21305389) B21305389
theorem B18938123 : Blo 2215435 18938123 := bstep (se 1 (by rfl) ⟨14203592, by rfl⟩ : syracuseStep 18938123 = 28407185) B28407185
theorem B12625415 : Blo 2215435 12625415 := bstep (se 1 (by rfl) ⟨9469061, by rfl⟩ : syracuseStep 12625415 = 18938123) B18938123
theorem B8416943 : Blo 2215435 8416943 := bstep (se 1 (by rfl) ⟨6312707, by rfl⟩ : syracuseStep 8416943 = 12625415) B12625415
theorem B5611295 : Blo 2215435 5611295 := bstep (se 1 (by rfl) ⟨4208471, by rfl⟩ : syracuseStep 5611295 = 8416943) B8416943
theorem B3740863 : Blo 2215435 3740863 := bstep (se 1 (by rfl) ⟨2805647, by rfl⟩ : syracuseStep 3740863 = 5611295) B5611295
theorem B4987817 : Blo 2215435 4987817 := bstep (se 2 (by rfl) ⟨1870431, by rfl⟩ : syracuseStep 4987817 = 3740863) B3740863
theorem B3325211 : Blo 2215435 3325211 := bstep (se 1 (by rfl) ⟨2493908, by rfl⟩ : syracuseStep 3325211 = 4987817) B4987817
theorem B2216807 : Blo 2215435 2216807 := bstep (se 1 (by rfl) ⟨1662605, by rfl⟩ : syracuseStep 2216807 = 3325211) B3325211
theorem B2493913 : Blo 2215435 2493913 := bbase (se 2 (by rfl) ⟨935217, by rfl⟩ : syracuseStep 2493913 = 1870435) (by norm_num)
theorem B3325217 : Blo 2215435 3325217 := bstep (se 2 (by rfl) ⟨1246956, by rfl⟩ : syracuseStep 3325217 = 2493913) B2493913
theorem B2216811 : Blo 2215435 2216811 := bstep (se 1 (by rfl) ⟨1662608, by rfl⟩ : syracuseStep 2216811 = 3325217) B3325217
theorem B3156365 : Blo 2215435 3156365 := bbase (se 3 (by rfl) ⟨591818, by rfl⟩ : syracuseStep 3156365 = 1183637) (by norm_num)
theorem B8416973 : Blo 2215435 8416973 := bstep (se 3 (by rfl) ⟨1578182, by rfl⟩ : syracuseStep 8416973 = 3156365) B3156365
theorem B5611315 : Blo 2215435 5611315 := bstep (se 1 (by rfl) ⟨4208486, by rfl⟩ : syracuseStep 5611315 = 8416973) B8416973
theorem B7481753 : Blo 2215435 7481753 := bstep (se 2 (by rfl) ⟨2805657, by rfl⟩ : syracuseStep 7481753 = 5611315) B5611315
theorem B4987835 : Blo 2215435 4987835 := bstep (se 1 (by rfl) ⟨3740876, by rfl⟩ : syracuseStep 4987835 = 7481753) B7481753
theorem B3325223 : Blo 2215435 3325223 := bstep (se 1 (by rfl) ⟨2493917, by rfl⟩ : syracuseStep 3325223 = 4987835) B4987835
theorem B2216815 : Blo 2215435 2216815 := bstep (se 1 (by rfl) ⟨1662611, by rfl⟩ : syracuseStep 2216815 = 3325223) B3325223
theorem B3325229 : Blo 2215435 3325229 := bbase (se 3 (by rfl) ⟨623480, by rfl⟩ : syracuseStep 3325229 = 1246961) (by norm_num)
theorem B2216819 : Blo 2215435 2216819 := bstep (se 1 (by rfl) ⟨1662614, by rfl⟩ : syracuseStep 2216819 = 3325229) B3325229
theorem B4987853 : Blo 2215435 4987853 := bbase (se 3 (by rfl) ⟨935222, by rfl⟩ : syracuseStep 4987853 = 1870445) (by norm_num)
theorem B3325235 : Blo 2215435 3325235 := bstep (se 1 (by rfl) ⟨2493926, by rfl⟩ : syracuseStep 3325235 = 4987853) B4987853
theorem B2216823 : Blo 2215435 2216823 := bstep (se 1 (by rfl) ⟨1662617, by rfl⟩ : syracuseStep 2216823 = 3325235) B3325235
theorem B2805673 : Blo 2215435 2805673 := bbase (se 2 (by rfl) ⟨1052127, by rfl⟩ : syracuseStep 2805673 = 2104255) (by norm_num)
theorem B3740897 : Blo 2215435 3740897 := bstep (se 2 (by rfl) ⟨1402836, by rfl⟩ : syracuseStep 3740897 = 2805673) B2805673
theorem B2493931 : Blo 2215435 2493931 := bstep (se 1 (by rfl) ⟨1870448, by rfl⟩ : syracuseStep 2493931 = 3740897) B3740897
theorem B3325241 : Blo 2215435 3325241 := bstep (se 2 (by rfl) ⟨1246965, by rfl⟩ : syracuseStep 3325241 = 2493931) B2493931
theorem B2216827 : Blo 2215435 2216827 := bstep (se 1 (by rfl) ⟨1662620, by rfl⟩ : syracuseStep 2216827 = 3325241) B3325241
theorem B10389653 : Blo 2215435 10389653 := bbase (se 6 (by rfl) ⟨243507, by rfl⟩ : syracuseStep 10389653 = 487015) (by norm_num)
theorem B6926435 : Blo 2215435 6926435 := bstep (se 1 (by rfl) ⟨5194826, by rfl⟩ : syracuseStep 6926435 = 10389653) B10389653
theorem B4617623 : Blo 2215435 4617623 := bstep (se 1 (by rfl) ⟨3463217, by rfl⟩ : syracuseStep 4617623 = 6926435) B6926435
theorem B3078415 : Blo 2215435 3078415 := bstep (se 1 (by rfl) ⟨2308811, by rfl⟩ : syracuseStep 3078415 = 4617623) B4617623
theorem B16418213 : Blo 2215435 16418213 := bstep (se 4 (by rfl) ⟨1539207, by rfl⟩ : syracuseStep 16418213 = 3078415) B3078415
theorem B10945475 : Blo 2215435 10945475 := bstep (se 1 (by rfl) ⟨8209106, by rfl⟩ : syracuseStep 10945475 = 16418213) B16418213
theorem B7296983 : Blo 2215435 7296983 := bstep (se 1 (by rfl) ⟨5472737, by rfl⟩ : syracuseStep 7296983 = 10945475) B10945475
theorem B4864655 : Blo 2215435 4864655 := bstep (se 1 (by rfl) ⟨3648491, by rfl⟩ : syracuseStep 4864655 = 7296983) B7296983
theorem B12972413 : Blo 2215435 12972413 := bstep (se 3 (by rfl) ⟨2432327, by rfl⟩ : syracuseStep 12972413 = 4864655) B4864655
theorem B34593101 : Blo 2215435 34593101 := bstep (se 3 (by rfl) ⟨6486206, by rfl⟩ : syracuseStep 34593101 = 12972413) B12972413
theorem B23062067 : Blo 2215435 23062067 := bstep (se 1 (by rfl) ⟨17296550, by rfl⟩ : syracuseStep 23062067 = 34593101) B34593101
theorem B15374711 : Blo 2215435 15374711 := bstep (se 1 (by rfl) ⟨11531033, by rfl⟩ : syracuseStep 15374711 = 23062067) B23062067
theorem B40999229 : Blo 2215435 40999229 := bstep (se 3 (by rfl) ⟨7687355, by rfl⟩ : syracuseStep 40999229 = 15374711) B15374711
theorem B27332819 : Blo 2215435 27332819 := bstep (se 1 (by rfl) ⟨20499614, by rfl⟩ : syracuseStep 27332819 = 40999229) B40999229
theorem B18221879 : Blo 2215435 18221879 := bstep (se 1 (by rfl) ⟨13666409, by rfl⟩ : syracuseStep 18221879 = 27332819) B27332819
theorem B48591677 : Blo 2215435 48591677 := bstep (se 3 (by rfl) ⟨9110939, by rfl⟩ : syracuseStep 48591677 = 18221879) B18221879
theorem B129577805 : Blo 2215435 129577805 := bstep (se 3 (by rfl) ⟨24295838, by rfl⟩ : syracuseStep 129577805 = 48591677) B48591677
theorem B86385203 : Blo 2215435 86385203 := bstep (se 1 (by rfl) ⟨64788902, by rfl⟩ : syracuseStep 86385203 = 129577805) B129577805
theorem B57590135 : Blo 2215435 57590135 := bstep (se 1 (by rfl) ⟨43192601, by rfl⟩ : syracuseStep 57590135 = 86385203) B86385203
theorem B38393423 : Blo 2215435 38393423 := bstep (se 1 (by rfl) ⟨28795067, by rfl⟩ : syracuseStep 38393423 = 57590135) B57590135
theorem B25595615 : Blo 2215435 25595615 := bstep (se 1 (by rfl) ⟨19196711, by rfl⟩ : syracuseStep 25595615 = 38393423) B38393423
theorem B68254973 : Blo 2215435 68254973 := bstep (se 3 (by rfl) ⟨12797807, by rfl⟩ : syracuseStep 68254973 = 25595615) B25595615
theorem B45503315 : Blo 2215435 45503315 := bstep (se 1 (by rfl) ⟨34127486, by rfl⟩ : syracuseStep 45503315 = 68254973) B68254973
theorem B30335543 : Blo 2215435 30335543 := bstep (se 1 (by rfl) ⟨22751657, by rfl⟩ : syracuseStep 30335543 = 45503315) B45503315
theorem B20223695 : Blo 2215435 20223695 := bstep (se 1 (by rfl) ⟨15167771, by rfl⟩ : syracuseStep 20223695 = 30335543) B30335543
theorem B13482463 : Blo 2215435 13482463 := bstep (se 1 (by rfl) ⟨10111847, by rfl⟩ : syracuseStep 13482463 = 20223695) B20223695
theorem B17976617 : Blo 2215435 17976617 := bstep (se 2 (by rfl) ⟨6741231, by rfl⟩ : syracuseStep 17976617 = 13482463) B13482463
theorem B11984411 : Blo 2215435 11984411 := bstep (se 1 (by rfl) ⟨8988308, by rfl⟩ : syracuseStep 11984411 = 17976617) B17976617
theorem B7989607 : Blo 2215435 7989607 := bstep (se 1 (by rfl) ⟨5992205, by rfl⟩ : syracuseStep 7989607 = 11984411) B11984411
theorem B10652809 : Blo 2215435 10652809 := bstep (se 2 (by rfl) ⟨3994803, by rfl⟩ : syracuseStep 10652809 = 7989607) B7989607
theorem B14203745 : Blo 2215435 14203745 := bstep (se 2 (by rfl) ⟨5326404, by rfl⟩ : syracuseStep 14203745 = 10652809) B10652809
theorem B9469163 : Blo 2215435 9469163 := bstep (se 1 (by rfl) ⟨7101872, by rfl⟩ : syracuseStep 9469163 = 14203745) B14203745
theorem B25251101 : Blo 2215435 25251101 := bstep (se 3 (by rfl) ⟨4734581, by rfl⟩ : syracuseStep 25251101 = 9469163) B9469163
theorem B16834067 : Blo 2215435 16834067 := bstep (se 1 (by rfl) ⟨12625550, by rfl⟩ : syracuseStep 16834067 = 25251101) B25251101
theorem B11222711 : Blo 2215435 11222711 := bstep (se 1 (by rfl) ⟨8417033, by rfl⟩ : syracuseStep 11222711 = 16834067) B16834067
theorem B7481807 : Blo 2215435 7481807 := bstep (se 1 (by rfl) ⟨5611355, by rfl⟩ : syracuseStep 7481807 = 11222711) B11222711
theorem B4987871 : Blo 2215435 4987871 := bstep (se 1 (by rfl) ⟨3740903, by rfl⟩ : syracuseStep 4987871 = 7481807) B7481807
theorem B3325247 : Blo 2215435 3325247 := bstep (se 1 (by rfl) ⟨2493935, by rfl⟩ : syracuseStep 3325247 = 4987871) B4987871
theorem B2216831 : Blo 2215435 2216831 := bstep (se 1 (by rfl) ⟨1662623, by rfl⟩ : syracuseStep 2216831 = 3325247) B3325247
theorem B3325253 : Blo 2215435 3325253 := bbase (se 4 (by rfl) ⟨311742, by rfl⟩ : syracuseStep 3325253 = 623485) (by norm_num)
theorem B2216835 : Blo 2215435 2216835 := bstep (se 1 (by rfl) ⟨1662626, by rfl⟩ : syracuseStep 2216835 = 3325253) B3325253
theorem B3740917 : Blo 2215435 3740917 := bbase (se 5 (by rfl) ⟨175355, by rfl⟩ : syracuseStep 3740917 = 350711) (by norm_num)
theorem B4987889 : Blo 2215435 4987889 := bstep (se 2 (by rfl) ⟨1870458, by rfl⟩ : syracuseStep 4987889 = 3740917) B3740917
theorem B3325259 : Blo 2215435 3325259 := bstep (se 1 (by rfl) ⟨2493944, by rfl⟩ : syracuseStep 3325259 = 4987889) B4987889
theorem B2216839 : Blo 2215435 2216839 := bstep (se 1 (by rfl) ⟨1662629, by rfl⟩ : syracuseStep 2216839 = 3325259) B3325259
theorem B2493949 : Blo 2215435 2493949 := bbase (se 3 (by rfl) ⟨467615, by rfl⟩ : syracuseStep 2493949 = 935231) (by norm_num)
theorem B3325265 : Blo 2215435 3325265 := bstep (se 2 (by rfl) ⟨1246974, by rfl⟩ : syracuseStep 3325265 = 2493949) B2493949
theorem B2216843 : Blo 2215435 2216843 := bstep (se 1 (by rfl) ⟨1662632, by rfl⟩ : syracuseStep 2216843 = 3325265) B3325265
theorem B7481861 : Blo 2215435 7481861 := bbase (se 4 (by rfl) ⟨701424, by rfl⟩ : syracuseStep 7481861 = 1402849) (by norm_num)
theorem B4987907 : Blo 2215435 4987907 := bstep (se 1 (by rfl) ⟨3740930, by rfl⟩ : syracuseStep 4987907 = 7481861) B7481861
theorem B3325271 : Blo 2215435 3325271 := bstep (se 1 (by rfl) ⟨2493953, by rfl⟩ : syracuseStep 3325271 = 4987907) B4987907
theorem B2216847 : Blo 2215435 2216847 := bstep (se 1 (by rfl) ⟨1662635, by rfl⟩ : syracuseStep 2216847 = 3325271) B3325271
theorem B3325277 : Blo 2215435 3325277 := bbase (se 3 (by rfl) ⟨623489, by rfl⟩ : syracuseStep 3325277 = 1246979) (by norm_num)
theorem B2216851 : Blo 2215435 2216851 := bstep (se 1 (by rfl) ⟨1662638, by rfl⟩ : syracuseStep 2216851 = 3325277) B3325277
theorem B4987925 : Blo 2215435 4987925 := bbase (se 6 (by rfl) ⟨116904, by rfl⟩ : syracuseStep 4987925 = 233809) (by norm_num)
theorem B3325283 : Blo 2215435 3325283 := bstep (se 1 (by rfl) ⟨2493962, by rfl⟩ : syracuseStep 3325283 = 4987925) B4987925
theorem B2216855 : Blo 2215435 2216855 := bstep (se 1 (by rfl) ⟨1662641, by rfl⟩ : syracuseStep 2216855 = 3325283) B3325283
theorem B8417141 : Blo 2215435 8417141 := bbase (se 5 (by rfl) ⟨394553, by rfl⟩ : syracuseStep 8417141 = 789107) (by norm_num)
theorem B5611427 : Blo 2215435 5611427 := bstep (se 1 (by rfl) ⟨4208570, by rfl⟩ : syracuseStep 5611427 = 8417141) B8417141
theorem B3740951 : Blo 2215435 3740951 := bstep (se 1 (by rfl) ⟨2805713, by rfl⟩ : syracuseStep 3740951 = 5611427) B5611427
theorem B2493967 : Blo 2215435 2493967 := bstep (se 1 (by rfl) ⟨1870475, by rfl⟩ : syracuseStep 2493967 = 3740951) B3740951
theorem B3325289 : Blo 2215435 3325289 := bstep (se 2 (by rfl) ⟨1246983, by rfl⟩ : syracuseStep 3325289 = 2493967) B2493967
theorem B2216859 : Blo 2215435 2216859 := bstep (se 1 (by rfl) ⟨1662644, by rfl⟩ : syracuseStep 2216859 = 3325289) B3325289
theorem B2367325 : Blo 2215435 2367325 := bbase (se 3 (by rfl) ⟨443873, by rfl⟩ : syracuseStep 2367325 = 887747) (by norm_num)
theorem B12625733 : Blo 2215435 12625733 := bstep (se 4 (by rfl) ⟨1183662, by rfl⟩ : syracuseStep 12625733 = 2367325) B2367325
theorem B8417155 : Blo 2215435 8417155 := bstep (se 1 (by rfl) ⟨6312866, by rfl⟩ : syracuseStep 8417155 = 12625733) B12625733
theorem B11222873 : Blo 2215435 11222873 := bstep (se 2 (by rfl) ⟨4208577, by rfl⟩ : syracuseStep 11222873 = 8417155) B8417155
theorem B7481915 : Blo 2215435 7481915 := bstep (se 1 (by rfl) ⟨5611436, by rfl⟩ : syracuseStep 7481915 = 11222873) B11222873
theorem B4987943 : Blo 2215435 4987943 := bstep (se 1 (by rfl) ⟨3740957, by rfl⟩ : syracuseStep 4987943 = 7481915) B7481915
theorem B3325295 : Blo 2215435 3325295 := bstep (se 1 (by rfl) ⟨2493971, by rfl⟩ : syracuseStep 3325295 = 4987943) B4987943
theorem B2216863 : Blo 2215435 2216863 := bstep (se 1 (by rfl) ⟨1662647, by rfl⟩ : syracuseStep 2216863 = 3325295) B3325295
theorem B3325301 : Blo 2215435 3325301 := bbase (se 5 (by rfl) ⟨155873, by rfl⟩ : syracuseStep 3325301 = 311747) (by norm_num)
theorem B2216867 : Blo 2215435 2216867 := bstep (se 1 (by rfl) ⟨1662650, by rfl⟩ : syracuseStep 2216867 = 3325301) B3325301
theorem B3156445 : Blo 2215435 3156445 := bbase (se 3 (by rfl) ⟨591833, by rfl⟩ : syracuseStep 3156445 = 1183667) (by norm_num)
theorem B4208593 : Blo 2215435 4208593 := bstep (se 2 (by rfl) ⟨1578222, by rfl⟩ : syracuseStep 4208593 = 3156445) B3156445
theorem B5611457 : Blo 2215435 5611457 := bstep (se 2 (by rfl) ⟨2104296, by rfl⟩ : syracuseStep 5611457 = 4208593) B4208593
theorem B3740971 : Blo 2215435 3740971 := bstep (se 1 (by rfl) ⟨2805728, by rfl⟩ : syracuseStep 3740971 = 5611457) B5611457
theorem B4987961 : Blo 2215435 4987961 := bstep (se 2 (by rfl) ⟨1870485, by rfl⟩ : syracuseStep 4987961 = 3740971) B3740971
theorem B3325307 : Blo 2215435 3325307 := bstep (se 1 (by rfl) ⟨2493980, by rfl⟩ : syracuseStep 3325307 = 4987961) B4987961
theorem B2216871 : Blo 2215435 2216871 := bstep (se 1 (by rfl) ⟨1662653, by rfl⟩ : syracuseStep 2216871 = 3325307) B3325307
theorem B2493985 : Blo 2215435 2493985 := bbase (se 2 (by rfl) ⟨935244, by rfl⟩ : syracuseStep 2493985 = 1870489) (by norm_num)
theorem B3325313 : Blo 2215435 3325313 := bstep (se 2 (by rfl) ⟨1246992, by rfl⟩ : syracuseStep 3325313 = 2493985) B2493985
theorem B2216875 : Blo 2215435 2216875 := bstep (se 1 (by rfl) ⟨1662656, by rfl⟩ : syracuseStep 2216875 = 3325313) B3325313
theorem B5611477 : Blo 2215435 5611477 := bbase (se 7 (by rfl) ⟨65759, by rfl⟩ : syracuseStep 5611477 = 131519) (by norm_num)
theorem B7481969 : Blo 2215435 7481969 := bstep (se 2 (by rfl) ⟨2805738, by rfl⟩ : syracuseStep 7481969 = 5611477) B5611477
theorem B4987979 : Blo 2215435 4987979 := bstep (se 1 (by rfl) ⟨3740984, by rfl⟩ : syracuseStep 4987979 = 7481969) B7481969
theorem B3325319 : Blo 2215435 3325319 := bstep (se 1 (by rfl) ⟨2493989, by rfl⟩ : syracuseStep 3325319 = 4987979) B4987979
theorem B2216879 : Blo 2215435 2216879 := bstep (se 1 (by rfl) ⟨1662659, by rfl⟩ : syracuseStep 2216879 = 3325319) B3325319
theorem B3325325 : Blo 2215435 3325325 := bbase (se 3 (by rfl) ⟨623498, by rfl⟩ : syracuseStep 3325325 = 1246997) (by norm_num)
theorem B2216883 : Blo 2215435 2216883 := bstep (se 1 (by rfl) ⟨1662662, by rfl⟩ : syracuseStep 2216883 = 3325325) B3325325
theorem B4987997 : Blo 2215435 4987997 := bbase (se 3 (by rfl) ⟨935249, by rfl⟩ : syracuseStep 4987997 = 1870499) (by norm_num)
theorem B3325331 : Blo 2215435 3325331 := bstep (se 1 (by rfl) ⟨2493998, by rfl⟩ : syracuseStep 3325331 = 4987997) B4987997
theorem B2216887 : Blo 2215435 2216887 := bstep (se 1 (by rfl) ⟨1662665, by rfl⟩ : syracuseStep 2216887 = 3325331) B3325331
theorem B3741005 : Blo 2215435 3741005 := bbase (se 3 (by rfl) ⟨701438, by rfl⟩ : syracuseStep 3741005 = 1402877) (by norm_num)
theorem B2494003 : Blo 2215435 2494003 := bstep (se 1 (by rfl) ⟨1870502, by rfl⟩ : syracuseStep 2494003 = 3741005) B3741005
theorem B3325337 : Blo 2215435 3325337 := bstep (se 2 (by rfl) ⟨1247001, by rfl⟩ : syracuseStep 3325337 = 2494003) B2494003
theorem B2216891 : Blo 2215435 2216891 := bstep (se 1 (by rfl) ⟨1662668, by rfl⟩ : syracuseStep 2216891 = 3325337) B3325337
theorem B34128469 : Blo 2215435 34128469 := bbase (se 8 (by rfl) ⟨199971, by rfl⟩ : syracuseStep 34128469 = 399943) (by norm_num)
theorem B45504625 : Blo 2215435 45504625 := bstep (se 2 (by rfl) ⟨17064234, by rfl⟩ : syracuseStep 45504625 = 34128469) B34128469
theorem B60672833 : Blo 2215435 60672833 := bstep (se 2 (by rfl) ⟨22752312, by rfl⟩ : syracuseStep 60672833 = 45504625) B45504625
theorem B40448555 : Blo 2215435 40448555 := bstep (se 1 (by rfl) ⟨30336416, by rfl⟩ : syracuseStep 40448555 = 60672833) B60672833
theorem B26965703 : Blo 2215435 26965703 := bstep (se 1 (by rfl) ⟨20224277, by rfl⟩ : syracuseStep 26965703 = 40448555) B40448555
theorem B17977135 : Blo 2215435 17977135 := bstep (se 1 (by rfl) ⟨13482851, by rfl⟩ : syracuseStep 17977135 = 26965703) B26965703
theorem B23969513 : Blo 2215435 23969513 := bstep (se 2 (by rfl) ⟨8988567, by rfl⟩ : syracuseStep 23969513 = 17977135) B17977135
theorem B15979675 : Blo 2215435 15979675 := bstep (se 1 (by rfl) ⟨11984756, by rfl⟩ : syracuseStep 15979675 = 23969513) B23969513
theorem B21306233 : Blo 2215435 21306233 := bstep (se 2 (by rfl) ⟨7989837, by rfl⟩ : syracuseStep 21306233 = 15979675) B15979675
theorem B14204155 : Blo 2215435 14204155 := bstep (se 1 (by rfl) ⟨10653116, by rfl⟩ : syracuseStep 14204155 = 21306233) B21306233
theorem B18938873 : Blo 2215435 18938873 := bstep (se 2 (by rfl) ⟨7102077, by rfl⟩ : syracuseStep 18938873 = 14204155) B14204155
theorem B12625915 : Blo 2215435 12625915 := bstep (se 1 (by rfl) ⟨9469436, by rfl⟩ : syracuseStep 12625915 = 18938873) B18938873
theorem B16834553 : Blo 2215435 16834553 := bstep (se 2 (by rfl) ⟨6312957, by rfl⟩ : syracuseStep 16834553 = 12625915) B12625915
theorem B11223035 : Blo 2215435 11223035 := bstep (se 1 (by rfl) ⟨8417276, by rfl⟩ : syracuseStep 11223035 = 16834553) B16834553
theorem B7482023 : Blo 2215435 7482023 := bstep (se 1 (by rfl) ⟨5611517, by rfl⟩ : syracuseStep 7482023 = 11223035) B11223035
theorem B4988015 : Blo 2215435 4988015 := bstep (se 1 (by rfl) ⟨3741011, by rfl⟩ : syracuseStep 4988015 = 7482023) B7482023
theorem B3325343 : Blo 2215435 3325343 := bstep (se 1 (by rfl) ⟨2494007, by rfl⟩ : syracuseStep 3325343 = 4988015) B4988015
theorem B2216895 : Blo 2215435 2216895 := bstep (se 1 (by rfl) ⟨1662671, by rfl⟩ : syracuseStep 2216895 = 3325343) B3325343
theorem B3325349 : Blo 2215435 3325349 := bbase (se 4 (by rfl) ⟨311751, by rfl⟩ : syracuseStep 3325349 = 623503) (by norm_num)
theorem B2216899 : Blo 2215435 2216899 := bstep (se 1 (by rfl) ⟨1662674, by rfl⟩ : syracuseStep 2216899 = 3325349) B3325349
theorem B2805769 : Blo 2215435 2805769 := bbase (se 2 (by rfl) ⟨1052163, by rfl⟩ : syracuseStep 2805769 = 2104327) (by norm_num)
theorem B3741025 : Blo 2215435 3741025 := bstep (se 2 (by rfl) ⟨1402884, by rfl⟩ : syracuseStep 3741025 = 2805769) B2805769
theorem B4988033 : Blo 2215435 4988033 := bstep (se 2 (by rfl) ⟨1870512, by rfl⟩ : syracuseStep 4988033 = 3741025) B3741025
theorem B3325355 : Blo 2215435 3325355 := bstep (se 1 (by rfl) ⟨2494016, by rfl⟩ : syracuseStep 3325355 = 4988033) B4988033
theorem B2216903 : Blo 2215435 2216903 := bstep (se 1 (by rfl) ⟨1662677, by rfl⟩ : syracuseStep 2216903 = 3325355) B3325355
theorem B2494021 : Blo 2215435 2494021 := bbase (se 4 (by rfl) ⟨233814, by rfl⟩ : syracuseStep 2494021 = 467629) (by norm_num)
theorem B3325361 : Blo 2215435 3325361 := bstep (se 2 (by rfl) ⟨1247010, by rfl⟩ : syracuseStep 3325361 = 2494021) B2494021
theorem B2216907 : Blo 2215435 2216907 := bstep (se 1 (by rfl) ⟨1662680, by rfl⟩ : syracuseStep 2216907 = 3325361) B3325361
theorem B4208669 : Blo 2215435 4208669 := bbase (se 3 (by rfl) ⟨789125, by rfl⟩ : syracuseStep 4208669 = 1578251) (by norm_num)
theorem B2805779 : Blo 2215435 2805779 := bstep (se 1 (by rfl) ⟨2104334, by rfl⟩ : syracuseStep 2805779 = 4208669) B4208669
theorem B7482077 : Blo 2215435 7482077 := bstep (se 3 (by rfl) ⟨1402889, by rfl⟩ : syracuseStep 7482077 = 2805779) B2805779
theorem B4988051 : Blo 2215435 4988051 := bstep (se 1 (by rfl) ⟨3741038, by rfl⟩ : syracuseStep 4988051 = 7482077) B7482077
theorem B3325367 : Blo 2215435 3325367 := bstep (se 1 (by rfl) ⟨2494025, by rfl⟩ : syracuseStep 3325367 = 4988051) B4988051
theorem B2216911 : Blo 2215435 2216911 := bstep (se 1 (by rfl) ⟨1662683, by rfl⟩ : syracuseStep 2216911 = 3325367) B3325367
theorem B3325373 : Blo 2215435 3325373 := bbase (se 3 (by rfl) ⟨623507, by rfl⟩ : syracuseStep 3325373 = 1247015) (by norm_num)
theorem B2216915 : Blo 2215435 2216915 := bstep (se 1 (by rfl) ⟨1662686, by rfl⟩ : syracuseStep 2216915 = 3325373) B3325373
theorem B4988069 : Blo 2215435 4988069 := bbase (se 4 (by rfl) ⟨467631, by rfl⟩ : syracuseStep 4988069 = 935263) (by norm_num)
theorem B3325379 : Blo 2215435 3325379 := bstep (se 1 (by rfl) ⟨2494034, by rfl⟩ : syracuseStep 3325379 = 4988069) B4988069
theorem B2216919 : Blo 2215435 2216919 := bstep (se 1 (by rfl) ⟨1662689, by rfl⟩ : syracuseStep 2216919 = 3325379) B3325379
theorem B5611589 : Blo 2215435 5611589 := bbase (se 4 (by rfl) ⟨526086, by rfl⟩ : syracuseStep 5611589 = 1052173) (by norm_num)
theorem B3741059 : Blo 2215435 3741059 := bstep (se 1 (by rfl) ⟨2805794, by rfl⟩ : syracuseStep 3741059 = 5611589) B5611589
theorem B2494039 : Blo 2215435 2494039 := bstep (se 1 (by rfl) ⟨1870529, by rfl⟩ : syracuseStep 2494039 = 3741059) B3741059
theorem B3325385 : Blo 2215435 3325385 := bstep (se 2 (by rfl) ⟨1247019, by rfl⟩ : syracuseStep 3325385 = 2494039) B2494039
theorem B2216923 : Blo 2215435 2216923 := bstep (se 1 (by rfl) ⟨1662692, by rfl⟩ : syracuseStep 2216923 = 3325385) B3325385
theorem B7102181 : Blo 2215435 7102181 := bbase (se 4 (by rfl) ⟨665829, by rfl⟩ : syracuseStep 7102181 = 1331659) (by norm_num)
theorem B4734787 : Blo 2215435 4734787 := bstep (se 1 (by rfl) ⟨3551090, by rfl⟩ : syracuseStep 4734787 = 7102181) B7102181
theorem B6313049 : Blo 2215435 6313049 := bstep (se 2 (by rfl) ⟨2367393, by rfl⟩ : syracuseStep 6313049 = 4734787) B4734787
theorem B4208699 : Blo 2215435 4208699 := bstep (se 1 (by rfl) ⟨3156524, by rfl⟩ : syracuseStep 4208699 = 6313049) B6313049
theorem B11223197 : Blo 2215435 11223197 := bstep (se 3 (by rfl) ⟨2104349, by rfl⟩ : syracuseStep 11223197 = 4208699) B4208699
theorem B7482131 : Blo 2215435 7482131 := bstep (se 1 (by rfl) ⟨5611598, by rfl⟩ : syracuseStep 7482131 = 11223197) B11223197
theorem B4988087 : Blo 2215435 4988087 := bstep (se 1 (by rfl) ⟨3741065, by rfl⟩ : syracuseStep 4988087 = 7482131) B7482131
theorem B3325391 : Blo 2215435 3325391 := bstep (se 1 (by rfl) ⟨2494043, by rfl⟩ : syracuseStep 3325391 = 4988087) B4988087
theorem B2216927 : Blo 2215435 2216927 := bstep (se 1 (by rfl) ⟨1662695, by rfl⟩ : syracuseStep 2216927 = 3325391) B3325391
theorem B3325397 : Blo 2215435 3325397 := bbase (se 7 (by rfl) ⟨38969, by rfl⟩ : syracuseStep 3325397 = 77939) (by norm_num)
theorem B2216931 : Blo 2215435 2216931 := bstep (se 1 (by rfl) ⟨1662698, by rfl⟩ : syracuseStep 2216931 = 3325397) B3325397
theorem B8417429 : Blo 2215435 8417429 := bbase (se 6 (by rfl) ⟨197283, by rfl⟩ : syracuseStep 8417429 = 394567) (by norm_num)
theorem B5611619 : Blo 2215435 5611619 := bstep (se 1 (by rfl) ⟨4208714, by rfl⟩ : syracuseStep 5611619 = 8417429) B8417429
theorem B3741079 : Blo 2215435 3741079 := bstep (se 1 (by rfl) ⟨2805809, by rfl⟩ : syracuseStep 3741079 = 5611619) B5611619
theorem B4988105 : Blo 2215435 4988105 := bstep (se 2 (by rfl) ⟨1870539, by rfl⟩ : syracuseStep 4988105 = 3741079) B3741079
theorem B3325403 : Blo 2215435 3325403 := bstep (se 1 (by rfl) ⟨2494052, by rfl⟩ : syracuseStep 3325403 = 4988105) B4988105
theorem B2216935 : Blo 2215435 2216935 := bstep (se 1 (by rfl) ⟨1662701, by rfl⟩ : syracuseStep 2216935 = 3325403) B3325403
theorem B2494057 : Blo 2215435 2494057 := bbase (se 2 (by rfl) ⟨935271, by rfl⟩ : syracuseStep 2494057 = 1870543) (by norm_num)
theorem B3325409 : Blo 2215435 3325409 := bstep (se 2 (by rfl) ⟨1247028, by rfl⟩ : syracuseStep 3325409 = 2494057) B2494057
theorem B2216939 : Blo 2215435 2216939 := bstep (se 1 (by rfl) ⟨1662704, by rfl⟩ : syracuseStep 2216939 = 3325409) B3325409
theorem B4734821 : Blo 2215435 4734821 := bbase (se 4 (by rfl) ⟨443889, by rfl⟩ : syracuseStep 4734821 = 887779) (by norm_num)
theorem B12626189 : Blo 2215435 12626189 := bstep (se 3 (by rfl) ⟨2367410, by rfl⟩ : syracuseStep 12626189 = 4734821) B4734821
theorem B8417459 : Blo 2215435 8417459 := bstep (se 1 (by rfl) ⟨6313094, by rfl⟩ : syracuseStep 8417459 = 12626189) B12626189
theorem B5611639 : Blo 2215435 5611639 := bstep (se 1 (by rfl) ⟨4208729, by rfl⟩ : syracuseStep 5611639 = 8417459) B8417459
theorem B7482185 : Blo 2215435 7482185 := bstep (se 2 (by rfl) ⟨2805819, by rfl⟩ : syracuseStep 7482185 = 5611639) B5611639
theorem B4988123 : Blo 2215435 4988123 := bstep (se 1 (by rfl) ⟨3741092, by rfl⟩ : syracuseStep 4988123 = 7482185) B7482185
theorem B3325415 : Blo 2215435 3325415 := bstep (se 1 (by rfl) ⟨2494061, by rfl⟩ : syracuseStep 3325415 = 4988123) B4988123
theorem B2216943 : Blo 2215435 2216943 := bstep (se 1 (by rfl) ⟨1662707, by rfl⟩ : syracuseStep 2216943 = 3325415) B3325415
theorem B3325421 : Blo 2215435 3325421 := bbase (se 3 (by rfl) ⟨623516, by rfl⟩ : syracuseStep 3325421 = 1247033) (by norm_num)
theorem B2216947 : Blo 2215435 2216947 := bstep (se 1 (by rfl) ⟨1662710, by rfl⟩ : syracuseStep 2216947 = 3325421) B3325421
theorem B4988141 : Blo 2215435 4988141 := bbase (se 3 (by rfl) ⟨935276, by rfl⟩ : syracuseStep 4988141 = 1870553) (by norm_num)
theorem B3325427 : Blo 2215435 3325427 := bstep (se 1 (by rfl) ⟨2494070, by rfl⟩ : syracuseStep 3325427 = 4988141) B4988141
theorem B2216951 : Blo 2215435 2216951 := bstep (se 1 (by rfl) ⟨1662713, by rfl⟩ : syracuseStep 2216951 = 3325427) B3325427
theorem B3156565 : Blo 2215435 3156565 := bbase (se 8 (by rfl) ⟨18495, by rfl⟩ : syracuseStep 3156565 = 36991) (by norm_num)
theorem B4208753 : Blo 2215435 4208753 := bstep (se 2 (by rfl) ⟨1578282, by rfl⟩ : syracuseStep 4208753 = 3156565) B3156565
theorem B2805835 : Blo 2215435 2805835 := bstep (se 1 (by rfl) ⟨2104376, by rfl⟩ : syracuseStep 2805835 = 4208753) B4208753
theorem B3741113 : Blo 2215435 3741113 := bstep (se 2 (by rfl) ⟨1402917, by rfl⟩ : syracuseStep 3741113 = 2805835) B2805835
theorem B2494075 : Blo 2215435 2494075 := bstep (se 1 (by rfl) ⟨1870556, by rfl⟩ : syracuseStep 2494075 = 3741113) B3741113
theorem B3325433 : Blo 2215435 3325433 := bstep (se 2 (by rfl) ⟨1247037, by rfl⟩ : syracuseStep 3325433 = 2494075) B2494075
theorem B2216955 : Blo 2215435 2216955 := bstep (se 1 (by rfl) ⟨1662716, by rfl⟩ : syracuseStep 2216955 = 3325433) B3325433
theorem B2699693 : Blo 2215435 2699693 := bbase (se 3 (by rfl) ⟨506192, by rfl⟩ : syracuseStep 2699693 = 1012385) (by norm_num)
theorem B28796725 : Blo 2215435 28796725 := bstep (se 5 (by rfl) ⟨1349846, by rfl⟩ : syracuseStep 28796725 = 2699693) B2699693
theorem B38395633 : Blo 2215435 38395633 := bstep (se 2 (by rfl) ⟨14398362, by rfl⟩ : syracuseStep 38395633 = 28796725) B28796725
theorem B51194177 : Blo 2215435 51194177 := bstep (se 2 (by rfl) ⟨19197816, by rfl⟩ : syracuseStep 51194177 = 38395633) B38395633
theorem B34129451 : Blo 2215435 34129451 := bstep (se 1 (by rfl) ⟨25597088, by rfl⟩ : syracuseStep 34129451 = 51194177) B51194177
theorem B91011869 : Blo 2215435 91011869 := bstep (se 3 (by rfl) ⟨17064725, by rfl⟩ : syracuseStep 91011869 = 34129451) B34129451
theorem B60674579 : Blo 2215435 60674579 := bstep (se 1 (by rfl) ⟨45505934, by rfl⟩ : syracuseStep 60674579 = 91011869) B91011869
theorem B40449719 : Blo 2215435 40449719 := bstep (se 1 (by rfl) ⟨30337289, by rfl⟩ : syracuseStep 40449719 = 60674579) B60674579
theorem B107865917 : Blo 2215435 107865917 := bstep (se 3 (by rfl) ⟨20224859, by rfl⟩ : syracuseStep 107865917 = 40449719) B40449719
theorem B71910611 : Blo 2215435 71910611 := bstep (se 1 (by rfl) ⟨53932958, by rfl⟩ : syracuseStep 71910611 = 107865917) B107865917
theorem B47940407 : Blo 2215435 47940407 := bstep (se 1 (by rfl) ⟨35955305, by rfl⟩ : syracuseStep 47940407 = 71910611) B71910611
theorem B31960271 : Blo 2215435 31960271 := bstep (se 1 (by rfl) ⟨23970203, by rfl⟩ : syracuseStep 31960271 = 47940407) B47940407
theorem B85227389 : Blo 2215435 85227389 := bstep (se 3 (by rfl) ⟨15980135, by rfl⟩ : syracuseStep 85227389 = 31960271) B31960271
theorem B56818259 : Blo 2215435 56818259 := bstep (se 1 (by rfl) ⟨42613694, by rfl⟩ : syracuseStep 56818259 = 85227389) B85227389
theorem B37878839 : Blo 2215435 37878839 := bstep (se 1 (by rfl) ⟨28409129, by rfl⟩ : syracuseStep 37878839 = 56818259) B56818259
theorem B25252559 : Blo 2215435 25252559 := bstep (se 1 (by rfl) ⟨18939419, by rfl⟩ : syracuseStep 25252559 = 37878839) B37878839
theorem B16835039 : Blo 2215435 16835039 := bstep (se 1 (by rfl) ⟨12626279, by rfl⟩ : syracuseStep 16835039 = 25252559) B25252559
theorem B11223359 : Blo 2215435 11223359 := bstep (se 1 (by rfl) ⟨8417519, by rfl⟩ : syracuseStep 11223359 = 16835039) B16835039
theorem B7482239 : Blo 2215435 7482239 := bstep (se 1 (by rfl) ⟨5611679, by rfl⟩ : syracuseStep 7482239 = 11223359) B11223359
theorem B4988159 : Blo 2215435 4988159 := bstep (se 1 (by rfl) ⟨3741119, by rfl⟩ : syracuseStep 4988159 = 7482239) B7482239
theorem B3325439 : Blo 2215435 3325439 := bstep (se 1 (by rfl) ⟨2494079, by rfl⟩ : syracuseStep 3325439 = 4988159) B4988159
theorem B2216959 : Blo 2215435 2216959 := bstep (se 1 (by rfl) ⟨1662719, by rfl⟩ : syracuseStep 2216959 = 3325439) B3325439
theorem B3325445 : Blo 2215435 3325445 := bbase (se 4 (by rfl) ⟨311760, by rfl⟩ : syracuseStep 3325445 = 623521) (by norm_num)
theorem B2216963 : Blo 2215435 2216963 := bstep (se 1 (by rfl) ⟨1662722, by rfl⟩ : syracuseStep 2216963 = 3325445) B3325445
theorem B3741133 : Blo 2215435 3741133 := bbase (se 3 (by rfl) ⟨701462, by rfl⟩ : syracuseStep 3741133 = 1402925) (by norm_num)
theorem B4988177 : Blo 2215435 4988177 := bstep (se 2 (by rfl) ⟨1870566, by rfl⟩ : syracuseStep 4988177 = 3741133) B3741133
theorem B3325451 : Blo 2215435 3325451 := bstep (se 1 (by rfl) ⟨2494088, by rfl⟩ : syracuseStep 3325451 = 4988177) B4988177
theorem B2216967 : Blo 2215435 2216967 := bstep (se 1 (by rfl) ⟨1662725, by rfl⟩ : syracuseStep 2216967 = 3325451) B3325451
theorem B2494093 : Blo 2215435 2494093 := bbase (se 3 (by rfl) ⟨467642, by rfl⟩ : syracuseStep 2494093 = 935285) (by norm_num)
theorem B3325457 : Blo 2215435 3325457 := bstep (se 2 (by rfl) ⟨1247046, by rfl⟩ : syracuseStep 3325457 = 2494093) B2494093
theorem B2216971 : Blo 2215435 2216971 := bstep (se 1 (by rfl) ⟨1662728, by rfl⟩ : syracuseStep 2216971 = 3325457) B3325457
theorem B7482293 : Blo 2215435 7482293 := bbase (se 5 (by rfl) ⟨350732, by rfl⟩ : syracuseStep 7482293 = 701465) (by norm_num)
theorem B4988195 : Blo 2215435 4988195 := bstep (se 1 (by rfl) ⟨3741146, by rfl⟩ : syracuseStep 4988195 = 7482293) B7482293
theorem B3325463 : Blo 2215435 3325463 := bstep (se 1 (by rfl) ⟨2494097, by rfl⟩ : syracuseStep 3325463 = 4988195) B4988195
theorem B2216975 : Blo 2215435 2216975 := bstep (se 1 (by rfl) ⟨1662731, by rfl⟩ : syracuseStep 2216975 = 3325463) B3325463
theorem B3325469 : Blo 2215435 3325469 := bbase (se 3 (by rfl) ⟨623525, by rfl⟩ : syracuseStep 3325469 = 1247051) (by norm_num)
theorem B2216979 : Blo 2215435 2216979 := bstep (se 1 (by rfl) ⟨1662734, by rfl⟩ : syracuseStep 2216979 = 3325469) B3325469
theorem B4988213 : Blo 2215435 4988213 := bbase (se 5 (by rfl) ⟨233822, by rfl⟩ : syracuseStep 4988213 = 467645) (by norm_num)
theorem B3325475 : Blo 2215435 3325475 := bstep (se 1 (by rfl) ⟨2494106, by rfl⟩ : syracuseStep 3325475 = 4988213) B4988213
theorem B2216983 : Blo 2215435 2216983 := bstep (se 1 (by rfl) ⟨1662737, by rfl⟩ : syracuseStep 2216983 = 3325475) B3325475
theorem B15980341 : Blo 2215435 15980341 := bbase (se 5 (by rfl) ⟨749078, by rfl⟩ : syracuseStep 15980341 = 1498157) (by norm_num)
theorem B21307121 : Blo 2215435 21307121 := bstep (se 2 (by rfl) ⟨7990170, by rfl⟩ : syracuseStep 21307121 = 15980341) B15980341
theorem B14204747 : Blo 2215435 14204747 := bstep (se 1 (by rfl) ⟨10653560, by rfl⟩ : syracuseStep 14204747 = 21307121) B21307121
theorem B9469831 : Blo 2215435 9469831 := bstep (se 1 (by rfl) ⟨7102373, by rfl⟩ : syracuseStep 9469831 = 14204747) B14204747
theorem B12626441 : Blo 2215435 12626441 := bstep (se 2 (by rfl) ⟨4734915, by rfl⟩ : syracuseStep 12626441 = 9469831) B9469831
theorem B8417627 : Blo 2215435 8417627 := bstep (se 1 (by rfl) ⟨6313220, by rfl⟩ : syracuseStep 8417627 = 12626441) B12626441
theorem B5611751 : Blo 2215435 5611751 := bstep (se 1 (by rfl) ⟨4208813, by rfl⟩ : syracuseStep 5611751 = 8417627) B8417627
theorem B3741167 : Blo 2215435 3741167 := bstep (se 1 (by rfl) ⟨2805875, by rfl⟩ : syracuseStep 3741167 = 5611751) B5611751
theorem B2494111 : Blo 2215435 2494111 := bstep (se 1 (by rfl) ⟨1870583, by rfl⟩ : syracuseStep 2494111 = 3741167) B3741167
theorem B3325481 : Blo 2215435 3325481 := bstep (se 2 (by rfl) ⟨1247055, by rfl⟩ : syracuseStep 3325481 = 2494111) B2494111
theorem B2216987 : Blo 2215435 2216987 := bstep (se 1 (by rfl) ⟨1662740, by rfl⟩ : syracuseStep 2216987 = 3325481) B3325481
theorem B21307157 : Blo 2215435 21307157 := bbase (se 6 (by rfl) ⟨499386, by rfl⟩ : syracuseStep 21307157 = 998773) (by norm_num)
theorem B14204771 : Blo 2215435 14204771 := bstep (se 1 (by rfl) ⟨10653578, by rfl⟩ : syracuseStep 14204771 = 21307157) B21307157
theorem B9469847 : Blo 2215435 9469847 := bstep (se 1 (by rfl) ⟨7102385, by rfl⟩ : syracuseStep 9469847 = 14204771) B14204771
theorem B6313231 : Blo 2215435 6313231 := bstep (se 1 (by rfl) ⟨4734923, by rfl⟩ : syracuseStep 6313231 = 9469847) B9469847
theorem B8417641 : Blo 2215435 8417641 := bstep (se 2 (by rfl) ⟨3156615, by rfl⟩ : syracuseStep 8417641 = 6313231) B6313231
theorem B11223521 : Blo 2215435 11223521 := bstep (se 2 (by rfl) ⟨4208820, by rfl⟩ : syracuseStep 11223521 = 8417641) B8417641
theorem B7482347 : Blo 2215435 7482347 := bstep (se 1 (by rfl) ⟨5611760, by rfl⟩ : syracuseStep 7482347 = 11223521) B11223521
theorem B4988231 : Blo 2215435 4988231 := bstep (se 1 (by rfl) ⟨3741173, by rfl⟩ : syracuseStep 4988231 = 7482347) B7482347
theorem B3325487 : Blo 2215435 3325487 := bstep (se 1 (by rfl) ⟨2494115, by rfl⟩ : syracuseStep 3325487 = 4988231) B4988231
theorem B2216991 : Blo 2215435 2216991 := bstep (se 1 (by rfl) ⟨1662743, by rfl⟩ : syracuseStep 2216991 = 3325487) B3325487
theorem B3325493 : Blo 2215435 3325493 := bbase (se 5 (by rfl) ⟨155882, by rfl⟩ : syracuseStep 3325493 = 311765) (by norm_num)
theorem B2216995 : Blo 2215435 2216995 := bstep (se 1 (by rfl) ⟨1662746, by rfl⟩ : syracuseStep 2216995 = 3325493) B3325493
theorem B5611781 : Blo 2215435 5611781 := bbase (se 4 (by rfl) ⟨526104, by rfl⟩ : syracuseStep 5611781 = 1052209) (by norm_num)
theorem B3741187 : Blo 2215435 3741187 := bstep (se 1 (by rfl) ⟨2805890, by rfl⟩ : syracuseStep 3741187 = 5611781) B5611781
theorem B4988249 : Blo 2215435 4988249 := bstep (se 2 (by rfl) ⟨1870593, by rfl⟩ : syracuseStep 4988249 = 3741187) B3741187
theorem B3325499 : Blo 2215435 3325499 := bstep (se 1 (by rfl) ⟨2494124, by rfl⟩ : syracuseStep 3325499 = 4988249) B4988249
theorem B2216999 : Blo 2215435 2216999 := bstep (se 1 (by rfl) ⟨1662749, by rfl⟩ : syracuseStep 2216999 = 3325499) B3325499
theorem B2494129 : Blo 2215435 2494129 := bbase (se 2 (by rfl) ⟨935298, by rfl⟩ : syracuseStep 2494129 = 1870597) (by norm_num)
theorem B3325505 : Blo 2215435 3325505 := bstep (se 2 (by rfl) ⟨1247064, by rfl⟩ : syracuseStep 3325505 = 2494129) B2494129
theorem B2217003 : Blo 2215435 2217003 := bstep (se 1 (by rfl) ⟨1662752, by rfl⟩ : syracuseStep 2217003 = 3325505) B3325505
theorem B5326829 : Blo 2215435 5326829 := bbase (se 3 (by rfl) ⟨998780, by rfl⟩ : syracuseStep 5326829 = 1997561) (by norm_num)
theorem B3551219 : Blo 2215435 3551219 := bstep (se 1 (by rfl) ⟨2663414, by rfl⟩ : syracuseStep 3551219 = 5326829) B5326829
theorem B2367479 : Blo 2215435 2367479 := bstep (se 1 (by rfl) ⟨1775609, by rfl⟩ : syracuseStep 2367479 = 3551219) B3551219
theorem B6313277 : Blo 2215435 6313277 := bstep (se 3 (by rfl) ⟨1183739, by rfl⟩ : syracuseStep 6313277 = 2367479) B2367479
theorem B4208851 : Blo 2215435 4208851 := bstep (se 1 (by rfl) ⟨3156638, by rfl⟩ : syracuseStep 4208851 = 6313277) B6313277
theorem B5611801 : Blo 2215435 5611801 := bstep (se 2 (by rfl) ⟨2104425, by rfl⟩ : syracuseStep 5611801 = 4208851) B4208851
theorem B7482401 : Blo 2215435 7482401 := bstep (se 2 (by rfl) ⟨2805900, by rfl⟩ : syracuseStep 7482401 = 5611801) B5611801
theorem B4988267 : Blo 2215435 4988267 := bstep (se 1 (by rfl) ⟨3741200, by rfl⟩ : syracuseStep 4988267 = 7482401) B7482401
theorem B3325511 : Blo 2215435 3325511 := bstep (se 1 (by rfl) ⟨2494133, by rfl⟩ : syracuseStep 3325511 = 4988267) B4988267
theorem B2217007 : Blo 2215435 2217007 := bstep (se 1 (by rfl) ⟨1662755, by rfl⟩ : syracuseStep 2217007 = 3325511) B3325511
theorem B3325517 : Blo 2215435 3325517 := bbase (se 3 (by rfl) ⟨623534, by rfl⟩ : syracuseStep 3325517 = 1247069) (by norm_num)
theorem B2217011 : Blo 2215435 2217011 := bstep (se 1 (by rfl) ⟨1662758, by rfl⟩ : syracuseStep 2217011 = 3325517) B3325517
theorem B4988285 : Blo 2215435 4988285 := bbase (se 3 (by rfl) ⟨935303, by rfl⟩ : syracuseStep 4988285 = 1870607) (by norm_num)
theorem B3325523 : Blo 2215435 3325523 := bstep (se 1 (by rfl) ⟨2494142, by rfl⟩ : syracuseStep 3325523 = 4988285) B4988285
theorem B2217015 : Blo 2215435 2217015 := bstep (se 1 (by rfl) ⟨1662761, by rfl⟩ : syracuseStep 2217015 = 3325523) B3325523
theorem B3741221 : Blo 2215435 3741221 := bbase (se 4 (by rfl) ⟨350739, by rfl⟩ : syracuseStep 3741221 = 701479) (by norm_num)
theorem B2494147 : Blo 2215435 2494147 := bstep (se 1 (by rfl) ⟨1870610, by rfl⟩ : syracuseStep 2494147 = 3741221) B3741221
theorem B3325529 : Blo 2215435 3325529 := bstep (se 2 (by rfl) ⟨1247073, by rfl⟩ : syracuseStep 3325529 = 2494147) B2494147
theorem B2217019 : Blo 2215435 2217019 := bstep (se 1 (by rfl) ⟨1662764, by rfl⟩ : syracuseStep 2217019 = 3325529) B3325529
theorem B3156661 : Blo 2215435 3156661 := bbase (se 5 (by rfl) ⟨147968, by rfl⟩ : syracuseStep 3156661 = 295937) (by norm_num)
theorem B16835525 : Blo 2215435 16835525 := bstep (se 4 (by rfl) ⟨1578330, by rfl⟩ : syracuseStep 16835525 = 3156661) B3156661
theorem B11223683 : Blo 2215435 11223683 := bstep (se 1 (by rfl) ⟨8417762, by rfl⟩ : syracuseStep 11223683 = 16835525) B16835525
theorem B7482455 : Blo 2215435 7482455 := bstep (se 1 (by rfl) ⟨5611841, by rfl⟩ : syracuseStep 7482455 = 11223683) B11223683
theorem B4988303 : Blo 2215435 4988303 := bstep (se 1 (by rfl) ⟨3741227, by rfl⟩ : syracuseStep 4988303 = 7482455) B7482455
theorem B3325535 : Blo 2215435 3325535 := bstep (se 1 (by rfl) ⟨2494151, by rfl⟩ : syracuseStep 3325535 = 4988303) B4988303
theorem B2217023 : Blo 2215435 2217023 := bstep (se 1 (by rfl) ⟨1662767, by rfl⟩ : syracuseStep 2217023 = 3325535) B3325535
theorem B3325541 : Blo 2215435 3325541 := bbase (se 4 (by rfl) ⟨311769, by rfl⟩ : syracuseStep 3325541 = 623539) (by norm_num)
theorem B2217027 : Blo 2215435 2217027 := bstep (se 1 (by rfl) ⟨1662770, by rfl⟩ : syracuseStep 2217027 = 3325541) B3325541
theorem B2367505 : Blo 2215435 2367505 := bbase (se 2 (by rfl) ⟨887814, by rfl⟩ : syracuseStep 2367505 = 1775629) (by norm_num)
theorem B3156673 : Blo 2215435 3156673 := bstep (se 2 (by rfl) ⟨1183752, by rfl⟩ : syracuseStep 3156673 = 2367505) B2367505
theorem B4208897 : Blo 2215435 4208897 := bstep (se 2 (by rfl) ⟨1578336, by rfl⟩ : syracuseStep 4208897 = 3156673) B3156673
theorem B2805931 : Blo 2215435 2805931 := bstep (se 1 (by rfl) ⟨2104448, by rfl⟩ : syracuseStep 2805931 = 4208897) B4208897
theorem B3741241 : Blo 2215435 3741241 := bstep (se 2 (by rfl) ⟨1402965, by rfl⟩ : syracuseStep 3741241 = 2805931) B2805931
theorem B4988321 : Blo 2215435 4988321 := bstep (se 2 (by rfl) ⟨1870620, by rfl⟩ : syracuseStep 4988321 = 3741241) B3741241
theorem B3325547 : Blo 2215435 3325547 := bstep (se 1 (by rfl) ⟨2494160, by rfl⟩ : syracuseStep 3325547 = 4988321) B4988321
theorem B2217031 : Blo 2215435 2217031 := bstep (se 1 (by rfl) ⟨1662773, by rfl⟩ : syracuseStep 2217031 = 3325547) B3325547
theorem B2494165 : Blo 2215435 2494165 := bbase (se 7 (by rfl) ⟨29228, by rfl⟩ : syracuseStep 2494165 = 58457) (by norm_num)
theorem B3325553 : Blo 2215435 3325553 := bstep (se 2 (by rfl) ⟨1247082, by rfl⟩ : syracuseStep 3325553 = 2494165) B2494165
theorem B2217035 : Blo 2215435 2217035 := bstep (se 1 (by rfl) ⟨1662776, by rfl⟩ : syracuseStep 2217035 = 3325553) B3325553
theorem B2805941 : Blo 2215435 2805941 := bbase (se 5 (by rfl) ⟨131528, by rfl⟩ : syracuseStep 2805941 = 263057) (by norm_num)
theorem B7482509 : Blo 2215435 7482509 := bstep (se 3 (by rfl) ⟨1402970, by rfl⟩ : syracuseStep 7482509 = 2805941) B2805941
theorem B4988339 : Blo 2215435 4988339 := bstep (se 1 (by rfl) ⟨3741254, by rfl⟩ : syracuseStep 4988339 = 7482509) B7482509
theorem B3325559 : Blo 2215435 3325559 := bstep (se 1 (by rfl) ⟨2494169, by rfl⟩ : syracuseStep 3325559 = 4988339) B4988339
theorem B2217039 : Blo 2215435 2217039 := bstep (se 1 (by rfl) ⟨1662779, by rfl⟩ : syracuseStep 2217039 = 3325559) B3325559
theorem B3325565 : Blo 2215435 3325565 := bbase (se 3 (by rfl) ⟨623543, by rfl⟩ : syracuseStep 3325565 = 1247087) (by norm_num)
theorem B2217043 : Blo 2215435 2217043 := bstep (se 1 (by rfl) ⟨1662782, by rfl⟩ : syracuseStep 2217043 = 3325565) B3325565
theorem B4988357 : Blo 2215435 4988357 := bbase (se 4 (by rfl) ⟨467658, by rfl⟩ : syracuseStep 4988357 = 935317) (by norm_num)
theorem B3325571 : Blo 2215435 3325571 := bstep (se 1 (by rfl) ⟨2494178, by rfl⟩ : syracuseStep 3325571 = 4988357) B4988357
theorem B2217047 : Blo 2215435 2217047 := bstep (se 1 (by rfl) ⟨1662785, by rfl⟩ : syracuseStep 2217047 = 3325571) B3325571
theorem B2247301 : Blo 2215435 2247301 := bbase (se 4 (by rfl) ⟨210684, by rfl⟩ : syracuseStep 2247301 = 421369) (by norm_num)
theorem B2996401 : Blo 2215435 2996401 := bstep (se 2 (by rfl) ⟨1123650, by rfl⟩ : syracuseStep 2996401 = 2247301) B2247301
theorem B3995201 : Blo 2215435 3995201 := bstep (se 2 (by rfl) ⟨1498200, by rfl⟩ : syracuseStep 3995201 = 2996401) B2996401
theorem B10653869 : Blo 2215435 10653869 := bstep (se 3 (by rfl) ⟨1997600, by rfl⟩ : syracuseStep 10653869 = 3995201) B3995201
theorem B7102579 : Blo 2215435 7102579 := bstep (se 1 (by rfl) ⟨5326934, by rfl⟩ : syracuseStep 7102579 = 10653869) B10653869
theorem B9470105 : Blo 2215435 9470105 := bstep (se 2 (by rfl) ⟨3551289, by rfl⟩ : syracuseStep 9470105 = 7102579) B7102579
theorem B6313403 : Blo 2215435 6313403 := bstep (se 1 (by rfl) ⟨4735052, by rfl⟩ : syracuseStep 6313403 = 9470105) B9470105
theorem B4208935 : Blo 2215435 4208935 := bstep (se 1 (by rfl) ⟨3156701, by rfl⟩ : syracuseStep 4208935 = 6313403) B6313403
theorem B5611913 : Blo 2215435 5611913 := bstep (se 2 (by rfl) ⟨2104467, by rfl⟩ : syracuseStep 5611913 = 4208935) B4208935
theorem B3741275 : Blo 2215435 3741275 := bstep (se 1 (by rfl) ⟨2805956, by rfl⟩ : syracuseStep 3741275 = 5611913) B5611913
theorem B2494183 : Blo 2215435 2494183 := bstep (se 1 (by rfl) ⟨1870637, by rfl⟩ : syracuseStep 2494183 = 3741275) B3741275
theorem B3325577 : Blo 2215435 3325577 := bstep (se 2 (by rfl) ⟨1247091, by rfl⟩ : syracuseStep 3325577 = 2494183) B2494183
theorem B2217051 : Blo 2215435 2217051 := bstep (se 1 (by rfl) ⟨1662788, by rfl⟩ : syracuseStep 2217051 = 3325577) B3325577
theorem B11223845 : Blo 2215435 11223845 := bbase (se 4 (by rfl) ⟨1052235, by rfl⟩ : syracuseStep 11223845 = 2104471) (by norm_num)
theorem B7482563 : Blo 2215435 7482563 := bstep (se 1 (by rfl) ⟨5611922, by rfl⟩ : syracuseStep 7482563 = 11223845) B11223845
theorem B4988375 : Blo 2215435 4988375 := bstep (se 1 (by rfl) ⟨3741281, by rfl⟩ : syracuseStep 4988375 = 7482563) B7482563
theorem B3325583 : Blo 2215435 3325583 := bstep (se 1 (by rfl) ⟨2494187, by rfl⟩ : syracuseStep 3325583 = 4988375) B4988375
theorem B2217055 : Blo 2215435 2217055 := bstep (se 1 (by rfl) ⟨1662791, by rfl⟩ : syracuseStep 2217055 = 3325583) B3325583
theorem B3325589 : Blo 2215435 3325589 := bbase (se 6 (by rfl) ⟨77943, by rfl⟩ : syracuseStep 3325589 = 155887) (by norm_num)
theorem B2217059 : Blo 2215435 2217059 := bstep (se 1 (by rfl) ⟨1662794, by rfl⟩ : syracuseStep 2217059 = 3325589) B3325589
theorem B10653925 : Blo 2215435 10653925 := bbase (se 4 (by rfl) ⟨998805, by rfl⟩ : syracuseStep 10653925 = 1997611) (by norm_num)
theorem B14205233 : Blo 2215435 14205233 := bstep (se 2 (by rfl) ⟨5326962, by rfl⟩ : syracuseStep 14205233 = 10653925) B10653925
theorem B9470155 : Blo 2215435 9470155 := bstep (se 1 (by rfl) ⟨7102616, by rfl⟩ : syracuseStep 9470155 = 14205233) B14205233
theorem B12626873 : Blo 2215435 12626873 := bstep (se 2 (by rfl) ⟨4735077, by rfl⟩ : syracuseStep 12626873 = 9470155) B9470155
theorem B8417915 : Blo 2215435 8417915 := bstep (se 1 (by rfl) ⟨6313436, by rfl⟩ : syracuseStep 8417915 = 12626873) B12626873
theorem B5611943 : Blo 2215435 5611943 := bstep (se 1 (by rfl) ⟨4208957, by rfl⟩ : syracuseStep 5611943 = 8417915) B8417915
theorem B3741295 : Blo 2215435 3741295 := bstep (se 1 (by rfl) ⟨2805971, by rfl⟩ : syracuseStep 3741295 = 5611943) B5611943
theorem B4988393 : Blo 2215435 4988393 := bstep (se 2 (by rfl) ⟨1870647, by rfl⟩ : syracuseStep 4988393 = 3741295) B3741295
theorem B3325595 : Blo 2215435 3325595 := bstep (se 1 (by rfl) ⟨2494196, by rfl⟩ : syracuseStep 3325595 = 4988393) B4988393
theorem B2217063 : Blo 2215435 2217063 := bstep (se 1 (by rfl) ⟨1662797, by rfl⟩ : syracuseStep 2217063 = 3325595) B3325595
theorem B2494201 : Blo 2215435 2494201 := bbase (se 2 (by rfl) ⟨935325, by rfl⟩ : syracuseStep 2494201 = 1870651) (by norm_num)
theorem B3325601 : Blo 2215435 3325601 := bstep (se 2 (by rfl) ⟨1247100, by rfl⟩ : syracuseStep 3325601 = 2494201) B2494201
theorem B2217067 : Blo 2215435 2217067 := bstep (se 1 (by rfl) ⟨1662800, by rfl⟩ : syracuseStep 2217067 = 3325601) B3325601
theorem B3995237 : Blo 2215435 3995237 := bbase (se 4 (by rfl) ⟨374553, by rfl⟩ : syracuseStep 3995237 = 749107) (by norm_num)
theorem B2663491 : Blo 2215435 2663491 := bstep (se 1 (by rfl) ⟨1997618, by rfl⟩ : syracuseStep 2663491 = 3995237) B3995237
theorem B3551321 : Blo 2215435 3551321 := bstep (se 2 (by rfl) ⟨1331745, by rfl⟩ : syracuseStep 3551321 = 2663491) B2663491
theorem B9470189 : Blo 2215435 9470189 := bstep (se 3 (by rfl) ⟨1775660, by rfl⟩ : syracuseStep 9470189 = 3551321) B3551321
theorem B6313459 : Blo 2215435 6313459 := bstep (se 1 (by rfl) ⟨4735094, by rfl⟩ : syracuseStep 6313459 = 9470189) B9470189
theorem B8417945 : Blo 2215435 8417945 := bstep (se 2 (by rfl) ⟨3156729, by rfl⟩ : syracuseStep 8417945 = 6313459) B6313459
theorem B5611963 : Blo 2215435 5611963 := bstep (se 1 (by rfl) ⟨4208972, by rfl⟩ : syracuseStep 5611963 = 8417945) B8417945
theorem B7482617 : Blo 2215435 7482617 := bstep (se 2 (by rfl) ⟨2805981, by rfl⟩ : syracuseStep 7482617 = 5611963) B5611963
theorem B4988411 : Blo 2215435 4988411 := bstep (se 1 (by rfl) ⟨3741308, by rfl⟩ : syracuseStep 4988411 = 7482617) B7482617
theorem B3325607 : Blo 2215435 3325607 := bstep (se 1 (by rfl) ⟨2494205, by rfl⟩ : syracuseStep 3325607 = 4988411) B4988411
theorem B2217071 : Blo 2215435 2217071 := bstep (se 1 (by rfl) ⟨1662803, by rfl⟩ : syracuseStep 2217071 = 3325607) B3325607
theorem B3325613 : Blo 2215435 3325613 := bbase (se 3 (by rfl) ⟨623552, by rfl⟩ : syracuseStep 3325613 = 1247105) (by norm_num)
theorem B2217075 : Blo 2215435 2217075 := bstep (se 1 (by rfl) ⟨1662806, by rfl⟩ : syracuseStep 2217075 = 3325613) B3325613
theorem B4988429 : Blo 2215435 4988429 := bbase (se 3 (by rfl) ⟨935330, by rfl⟩ : syracuseStep 4988429 = 1870661) (by norm_num)
theorem B3325619 : Blo 2215435 3325619 := bstep (se 1 (by rfl) ⟨2494214, by rfl⟩ : syracuseStep 3325619 = 4988429) B4988429
theorem B2217079 : Blo 2215435 2217079 := bstep (se 1 (by rfl) ⟨1662809, by rfl⟩ : syracuseStep 2217079 = 3325619) B3325619
theorem B2805997 : Blo 2215435 2805997 := bbase (se 3 (by rfl) ⟨526124, by rfl⟩ : syracuseStep 2805997 = 1052249) (by norm_num)
theorem B3741329 : Blo 2215435 3741329 := bstep (se 2 (by rfl) ⟨1402998, by rfl⟩ : syracuseStep 3741329 = 2805997) B2805997
theorem B2494219 : Blo 2215435 2494219 := bstep (se 1 (by rfl) ⟨1870664, by rfl⟩ : syracuseStep 2494219 = 3741329) B3741329
theorem B3325625 : Blo 2215435 3325625 := bstep (se 2 (by rfl) ⟨1247109, by rfl⟩ : syracuseStep 3325625 = 2494219) B2494219
theorem B2217083 : Blo 2215435 2217083 := bstep (se 1 (by rfl) ⟨1662812, by rfl⟩ : syracuseStep 2217083 = 3325625) B3325625
theorem B3371005 : Blo 2215435 3371005 := bbase (se 3 (by rfl) ⟨632063, by rfl⟩ : syracuseStep 3371005 = 1264127) (by norm_num)
theorem B4494673 : Blo 2215435 4494673 := bstep (se 2 (by rfl) ⟨1685502, by rfl⟩ : syracuseStep 4494673 = 3371005) B3371005
theorem B23971589 : Blo 2215435 23971589 := bstep (se 4 (by rfl) ⟨2247336, by rfl⟩ : syracuseStep 23971589 = 4494673) B4494673
theorem B15981059 : Blo 2215435 15981059 := bstep (se 1 (by rfl) ⟨11985794, by rfl⟩ : syracuseStep 15981059 = 23971589) B23971589
theorem B10654039 : Blo 2215435 10654039 := bstep (se 1 (by rfl) ⟨7990529, by rfl⟩ : syracuseStep 10654039 = 15981059) B15981059
theorem B14205385 : Blo 2215435 14205385 := bstep (se 2 (by rfl) ⟨5327019, by rfl⟩ : syracuseStep 14205385 = 10654039) B10654039
theorem B18940513 : Blo 2215435 18940513 := bstep (se 2 (by rfl) ⟨7102692, by rfl⟩ : syracuseStep 18940513 = 14205385) B14205385
theorem B25254017 : Blo 2215435 25254017 := bstep (se 2 (by rfl) ⟨9470256, by rfl⟩ : syracuseStep 25254017 = 18940513) B18940513
theorem B16836011 : Blo 2215435 16836011 := bstep (se 1 (by rfl) ⟨12627008, by rfl⟩ : syracuseStep 16836011 = 25254017) B25254017
theorem B11224007 : Blo 2215435 11224007 := bstep (se 1 (by rfl) ⟨8418005, by rfl⟩ : syracuseStep 11224007 = 16836011) B16836011
theorem B7482671 : Blo 2215435 7482671 := bstep (se 1 (by rfl) ⟨5612003, by rfl⟩ : syracuseStep 7482671 = 11224007) B11224007
theorem B4988447 : Blo 2215435 4988447 := bstep (se 1 (by rfl) ⟨3741335, by rfl⟩ : syracuseStep 4988447 = 7482671) B7482671
theorem B3325631 : Blo 2215435 3325631 := bstep (se 1 (by rfl) ⟨2494223, by rfl⟩ : syracuseStep 3325631 = 4988447) B4988447
theorem B2217087 : Blo 2215435 2217087 := bstep (se 1 (by rfl) ⟨1662815, by rfl⟩ : syracuseStep 2217087 = 3325631) B3325631
theorem B3325637 : Blo 2215435 3325637 := bbase (se 4 (by rfl) ⟨311778, by rfl⟩ : syracuseStep 3325637 = 623557) (by norm_num)
theorem B2217091 : Blo 2215435 2217091 := bstep (se 1 (by rfl) ⟨1662818, by rfl⟩ : syracuseStep 2217091 = 3325637) B3325637
theorem B3741349 : Blo 2215435 3741349 := bbase (se 4 (by rfl) ⟨350751, by rfl⟩ : syracuseStep 3741349 = 701503) (by norm_num)
theorem B4988465 : Blo 2215435 4988465 := bstep (se 2 (by rfl) ⟨1870674, by rfl⟩ : syracuseStep 4988465 = 3741349) B3741349
theorem B3325643 : Blo 2215435 3325643 := bstep (se 1 (by rfl) ⟨2494232, by rfl⟩ : syracuseStep 3325643 = 4988465) B4988465
theorem B2217095 : Blo 2215435 2217095 := bstep (se 1 (by rfl) ⟨1662821, by rfl⟩ : syracuseStep 2217095 = 3325643) B3325643
theorem B2494237 : Blo 2215435 2494237 := bbase (se 3 (by rfl) ⟨467669, by rfl⟩ : syracuseStep 2494237 = 935339) (by norm_num)
theorem B3325649 : Blo 2215435 3325649 := bstep (se 2 (by rfl) ⟨1247118, by rfl⟩ : syracuseStep 3325649 = 2494237) B2494237
theorem B2217099 : Blo 2215435 2217099 := bstep (se 1 (by rfl) ⟨1662824, by rfl⟩ : syracuseStep 2217099 = 3325649) B3325649
theorem B7482725 : Blo 2215435 7482725 := bbase (se 4 (by rfl) ⟨701505, by rfl⟩ : syracuseStep 7482725 = 1403011) (by norm_num)
theorem B4988483 : Blo 2215435 4988483 := bstep (se 1 (by rfl) ⟨3741362, by rfl⟩ : syracuseStep 4988483 = 7482725) B7482725
theorem B3325655 : Blo 2215435 3325655 := bstep (se 1 (by rfl) ⟨2494241, by rfl⟩ : syracuseStep 3325655 = 4988483) B4988483
theorem B2217103 : Blo 2215435 2217103 := bstep (se 1 (by rfl) ⟨1662827, by rfl⟩ : syracuseStep 2217103 = 3325655) B3325655
theorem B3325661 : Blo 2215435 3325661 := bbase (se 3 (by rfl) ⟨623561, by rfl⟩ : syracuseStep 3325661 = 1247123) (by norm_num)
theorem B2217107 : Blo 2215435 2217107 := bstep (se 1 (by rfl) ⟨1662830, by rfl⟩ : syracuseStep 2217107 = 3325661) B3325661
theorem B4988501 : Blo 2215435 4988501 := bbase (se 8 (by rfl) ⟨29229, by rfl⟩ : syracuseStep 4988501 = 58459) (by norm_num)
theorem B3325667 : Blo 2215435 3325667 := bstep (se 1 (by rfl) ⟨2494250, by rfl⟩ : syracuseStep 3325667 = 4988501) B4988501
theorem B2217111 : Blo 2215435 2217111 := bstep (se 1 (by rfl) ⟨1662833, by rfl⟩ : syracuseStep 2217111 = 3325667) B3325667
theorem B4735189 : Blo 2215435 4735189 := bbase (se 7 (by rfl) ⟨55490, by rfl⟩ : syracuseStep 4735189 = 110981) (by norm_num)
theorem B6313585 : Blo 2215435 6313585 := bstep (se 2 (by rfl) ⟨2367594, by rfl⟩ : syracuseStep 6313585 = 4735189) B4735189
theorem B8418113 : Blo 2215435 8418113 := bstep (se 2 (by rfl) ⟨3156792, by rfl⟩ : syracuseStep 8418113 = 6313585) B6313585
theorem B5612075 : Blo 2215435 5612075 := bstep (se 1 (by rfl) ⟨4209056, by rfl⟩ : syracuseStep 5612075 = 8418113) B8418113
theorem B3741383 : Blo 2215435 3741383 := bstep (se 1 (by rfl) ⟨2806037, by rfl⟩ : syracuseStep 3741383 = 5612075) B5612075
theorem B2494255 : Blo 2215435 2494255 := bstep (se 1 (by rfl) ⟨1870691, by rfl⟩ : syracuseStep 2494255 = 3741383) B3741383
theorem B3325673 : Blo 2215435 3325673 := bstep (se 2 (by rfl) ⟨1247127, by rfl⟩ : syracuseStep 3325673 = 2494255) B2494255
theorem B2217115 : Blo 2215435 2217115 := bstep (se 1 (by rfl) ⟨1662836, by rfl⟩ : syracuseStep 2217115 = 3325673) B3325673
theorem B7990645 : Blo 2215435 7990645 := bbase (se 5 (by rfl) ⟨374561, by rfl⟩ : syracuseStep 7990645 = 749123) (by norm_num)
theorem B10654193 : Blo 2215435 10654193 := bstep (se 2 (by rfl) ⟨3995322, by rfl⟩ : syracuseStep 10654193 = 7990645) B7990645
theorem B28411181 : Blo 2215435 28411181 := bstep (se 3 (by rfl) ⟨5327096, by rfl⟩ : syracuseStep 28411181 = 10654193) B10654193
theorem B18940787 : Blo 2215435 18940787 := bstep (se 1 (by rfl) ⟨14205590, by rfl⟩ : syracuseStep 18940787 = 28411181) B28411181
theorem B12627191 : Blo 2215435 12627191 := bstep (se 1 (by rfl) ⟨9470393, by rfl⟩ : syracuseStep 12627191 = 18940787) B18940787
theorem B8418127 : Blo 2215435 8418127 := bstep (se 1 (by rfl) ⟨6313595, by rfl⟩ : syracuseStep 8418127 = 12627191) B12627191
theorem B11224169 : Blo 2215435 11224169 := bstep (se 2 (by rfl) ⟨4209063, by rfl⟩ : syracuseStep 11224169 = 8418127) B8418127
theorem B7482779 : Blo 2215435 7482779 := bstep (se 1 (by rfl) ⟨5612084, by rfl⟩ : syracuseStep 7482779 = 11224169) B11224169
theorem B4988519 : Blo 2215435 4988519 := bstep (se 1 (by rfl) ⟨3741389, by rfl⟩ : syracuseStep 4988519 = 7482779) B7482779
theorem B3325679 : Blo 2215435 3325679 := bstep (se 1 (by rfl) ⟨2494259, by rfl⟩ : syracuseStep 3325679 = 4988519) B4988519
theorem B2217119 : Blo 2215435 2217119 := bstep (se 1 (by rfl) ⟨1662839, by rfl⟩ : syracuseStep 2217119 = 3325679) B3325679
theorem B3325685 : Blo 2215435 3325685 := bbase (se 5 (by rfl) ⟨155891, by rfl⟩ : syracuseStep 3325685 = 311783) (by norm_num)
theorem B2217123 : Blo 2215435 2217123 := bstep (se 1 (by rfl) ⟨1662842, by rfl⟩ : syracuseStep 2217123 = 3325685) B3325685
theorem B5327117 : Blo 2215435 5327117 := bbase (se 3 (by rfl) ⟨998834, by rfl⟩ : syracuseStep 5327117 = 1997669) (by norm_num)
theorem B3551411 : Blo 2215435 3551411 := bstep (se 1 (by rfl) ⟨2663558, by rfl⟩ : syracuseStep 3551411 = 5327117) B5327117
theorem B9470429 : Blo 2215435 9470429 := bstep (se 3 (by rfl) ⟨1775705, by rfl⟩ : syracuseStep 9470429 = 3551411) B3551411
theorem B6313619 : Blo 2215435 6313619 := bstep (se 1 (by rfl) ⟨4735214, by rfl⟩ : syracuseStep 6313619 = 9470429) B9470429
theorem B4209079 : Blo 2215435 4209079 := bstep (se 1 (by rfl) ⟨3156809, by rfl⟩ : syracuseStep 4209079 = 6313619) B6313619
theorem B5612105 : Blo 2215435 5612105 := bstep (se 2 (by rfl) ⟨2104539, by rfl⟩ : syracuseStep 5612105 = 4209079) B4209079
theorem B3741403 : Blo 2215435 3741403 := bstep (se 1 (by rfl) ⟨2806052, by rfl⟩ : syracuseStep 3741403 = 5612105) B5612105
theorem B4988537 : Blo 2215435 4988537 := bstep (se 2 (by rfl) ⟨1870701, by rfl⟩ : syracuseStep 4988537 = 3741403) B3741403
theorem B3325691 : Blo 2215435 3325691 := bstep (se 1 (by rfl) ⟨2494268, by rfl⟩ : syracuseStep 3325691 = 4988537) B4988537
theorem B2217127 : Blo 2215435 2217127 := bstep (se 1 (by rfl) ⟨1662845, by rfl⟩ : syracuseStep 2217127 = 3325691) B3325691
theorem B2494273 : Blo 2215435 2494273 := bbase (se 2 (by rfl) ⟨935352, by rfl⟩ : syracuseStep 2494273 = 1870705) (by norm_num)
theorem B3325697 : Blo 2215435 3325697 := bstep (se 2 (by rfl) ⟨1247136, by rfl⟩ : syracuseStep 3325697 = 2494273) B2494273
theorem B2217131 : Blo 2215435 2217131 := bstep (se 1 (by rfl) ⟨1662848, by rfl⟩ : syracuseStep 2217131 = 3325697) B3325697
theorem B5612125 : Blo 2215435 5612125 := bbase (se 3 (by rfl) ⟨1052273, by rfl⟩ : syracuseStep 5612125 = 2104547) (by norm_num)
theorem B7482833 : Blo 2215435 7482833 := bstep (se 2 (by rfl) ⟨2806062, by rfl⟩ : syracuseStep 7482833 = 5612125) B5612125
theorem B4988555 : Blo 2215435 4988555 := bstep (se 1 (by rfl) ⟨3741416, by rfl⟩ : syracuseStep 4988555 = 7482833) B7482833
theorem B3325703 : Blo 2215435 3325703 := bstep (se 1 (by rfl) ⟨2494277, by rfl⟩ : syracuseStep 3325703 = 4988555) B4988555
theorem B2217135 : Blo 2215435 2217135 := bstep (se 1 (by rfl) ⟨1662851, by rfl⟩ : syracuseStep 2217135 = 3325703) B3325703
theorem B3325709 : Blo 2215435 3325709 := bbase (se 3 (by rfl) ⟨623570, by rfl⟩ : syracuseStep 3325709 = 1247141) (by norm_num)
theorem B2217139 : Blo 2215435 2217139 := bstep (se 1 (by rfl) ⟨1662854, by rfl⟩ : syracuseStep 2217139 = 3325709) B3325709
theorem B4988573 : Blo 2215435 4988573 := bbase (se 3 (by rfl) ⟨935357, by rfl⟩ : syracuseStep 4988573 = 1870715) (by norm_num)
theorem B3325715 : Blo 2215435 3325715 := bstep (se 1 (by rfl) ⟨2494286, by rfl⟩ : syracuseStep 3325715 = 4988573) B4988573
theorem B2217143 : Blo 2215435 2217143 := bstep (se 1 (by rfl) ⟨1662857, by rfl⟩ : syracuseStep 2217143 = 3325715) B3325715
theorem B3741437 : Blo 2215435 3741437 := bbase (se 3 (by rfl) ⟨701519, by rfl⟩ : syracuseStep 3741437 = 1403039) (by norm_num)
theorem B2494291 : Blo 2215435 2494291 := bstep (se 1 (by rfl) ⟨1870718, by rfl⟩ : syracuseStep 2494291 = 3741437) B3741437
theorem B3325721 : Blo 2215435 3325721 := bstep (se 2 (by rfl) ⟨1247145, by rfl⟩ : syracuseStep 3325721 = 2494291) B2494291
theorem B2217147 : Blo 2215435 2217147 := bstep (se 1 (by rfl) ⟨1662860, by rfl⟩ : syracuseStep 2217147 = 3325721) B3325721
theorem B3995381 : Blo 2215435 3995381 := bbase (se 5 (by rfl) ⟨187283, by rfl⟩ : syracuseStep 3995381 = 374567) (by norm_num)
theorem B2663587 : Blo 2215435 2663587 := bstep (se 1 (by rfl) ⟨1997690, by rfl⟩ : syracuseStep 2663587 = 3995381) B3995381
theorem B3551449 : Blo 2215435 3551449 := bstep (se 2 (by rfl) ⟨1331793, by rfl⟩ : syracuseStep 3551449 = 2663587) B2663587
theorem B4735265 : Blo 2215435 4735265 := bstep (se 2 (by rfl) ⟨1775724, by rfl⟩ : syracuseStep 4735265 = 3551449) B3551449
theorem B12627373 : Blo 2215435 12627373 := bstep (se 3 (by rfl) ⟨2367632, by rfl⟩ : syracuseStep 12627373 = 4735265) B4735265
theorem B16836497 : Blo 2215435 16836497 := bstep (se 2 (by rfl) ⟨6313686, by rfl⟩ : syracuseStep 16836497 = 12627373) B12627373
theorem B11224331 : Blo 2215435 11224331 := bstep (se 1 (by rfl) ⟨8418248, by rfl⟩ : syracuseStep 11224331 = 16836497) B16836497
theorem B7482887 : Blo 2215435 7482887 := bstep (se 1 (by rfl) ⟨5612165, by rfl⟩ : syracuseStep 7482887 = 11224331) B11224331
theorem B4988591 : Blo 2215435 4988591 := bstep (se 1 (by rfl) ⟨3741443, by rfl⟩ : syracuseStep 4988591 = 7482887) B7482887
theorem B3325727 : Blo 2215435 3325727 := bstep (se 1 (by rfl) ⟨2494295, by rfl⟩ : syracuseStep 3325727 = 4988591) B4988591
theorem B2217151 : Blo 2215435 2217151 := bstep (se 1 (by rfl) ⟨1662863, by rfl⟩ : syracuseStep 2217151 = 3325727) B3325727
theorem B3325733 : Blo 2215435 3325733 := bbase (se 4 (by rfl) ⟨311787, by rfl⟩ : syracuseStep 3325733 = 623575) (by norm_num)
theorem B2217155 : Blo 2215435 2217155 := bstep (se 1 (by rfl) ⟨1662866, by rfl⟩ : syracuseStep 2217155 = 3325733) B3325733
theorem B2806093 : Blo 2215435 2806093 := bbase (se 3 (by rfl) ⟨526142, by rfl⟩ : syracuseStep 2806093 = 1052285) (by norm_num)
theorem B3741457 : Blo 2215435 3741457 := bstep (se 2 (by rfl) ⟨1403046, by rfl⟩ : syracuseStep 3741457 = 2806093) B2806093
theorem B4988609 : Blo 2215435 4988609 := bstep (se 2 (by rfl) ⟨1870728, by rfl⟩ : syracuseStep 4988609 = 3741457) B3741457
theorem B3325739 : Blo 2215435 3325739 := bstep (se 1 (by rfl) ⟨2494304, by rfl⟩ : syracuseStep 3325739 = 4988609) B4988609
theorem B2217159 : Blo 2215435 2217159 := bstep (se 1 (by rfl) ⟨1662869, by rfl⟩ : syracuseStep 2217159 = 3325739) B3325739
theorem B2494309 : Blo 2215435 2494309 := bbase (se 4 (by rfl) ⟨233841, by rfl⟩ : syracuseStep 2494309 = 467683) (by norm_num)
theorem B3325745 : Blo 2215435 3325745 := bstep (se 2 (by rfl) ⟨1247154, by rfl⟩ : syracuseStep 3325745 = 2494309) B2494309
theorem B2217163 : Blo 2215435 2217163 := bstep (se 1 (by rfl) ⟨1662872, by rfl⟩ : syracuseStep 2217163 = 3325745) B3325745
theorem B6313733 : Blo 2215435 6313733 := bbase (se 4 (by rfl) ⟨591912, by rfl⟩ : syracuseStep 6313733 = 1183825) (by norm_num)
theorem B4209155 : Blo 2215435 4209155 := bstep (se 1 (by rfl) ⟨3156866, by rfl⟩ : syracuseStep 4209155 = 6313733) B6313733
theorem B2806103 : Blo 2215435 2806103 := bstep (se 1 (by rfl) ⟨2104577, by rfl⟩ : syracuseStep 2806103 = 4209155) B4209155
theorem B7482941 : Blo 2215435 7482941 := bstep (se 3 (by rfl) ⟨1403051, by rfl⟩ : syracuseStep 7482941 = 2806103) B2806103
theorem B4988627 : Blo 2215435 4988627 := bstep (se 1 (by rfl) ⟨3741470, by rfl⟩ : syracuseStep 4988627 = 7482941) B7482941
theorem B3325751 : Blo 2215435 3325751 := bstep (se 1 (by rfl) ⟨2494313, by rfl⟩ : syracuseStep 3325751 = 4988627) B4988627
theorem B2217167 : Blo 2215435 2217167 := bstep (se 1 (by rfl) ⟨1662875, by rfl⟩ : syracuseStep 2217167 = 3325751) B3325751
theorem B3325757 : Blo 2215435 3325757 := bbase (se 3 (by rfl) ⟨623579, by rfl⟩ : syracuseStep 3325757 = 1247159) (by norm_num)
theorem B2217171 : Blo 2215435 2217171 := bstep (se 1 (by rfl) ⟨1662878, by rfl⟩ : syracuseStep 2217171 = 3325757) B3325757
theorem B4988645 : Blo 2215435 4988645 := bbase (se 4 (by rfl) ⟨467685, by rfl⟩ : syracuseStep 4988645 = 935371) (by norm_num)
theorem B3325763 : Blo 2215435 3325763 := bstep (se 1 (by rfl) ⟨2494322, by rfl⟩ : syracuseStep 3325763 = 4988645) B4988645
theorem B2217175 : Blo 2215435 2217175 := bstep (se 1 (by rfl) ⟨1662881, by rfl⟩ : syracuseStep 2217175 = 3325763) B3325763
theorem B5612237 : Blo 2215435 5612237 := bbase (se 3 (by rfl) ⟨1052294, by rfl⟩ : syracuseStep 5612237 = 2104589) (by norm_num)
theorem B3741491 : Blo 2215435 3741491 := bstep (se 1 (by rfl) ⟨2806118, by rfl⟩ : syracuseStep 3741491 = 5612237) B5612237
theorem B2494327 : Blo 2215435 2494327 := bstep (se 1 (by rfl) ⟨1870745, by rfl⟩ : syracuseStep 2494327 = 3741491) B3741491
theorem B3325769 : Blo 2215435 3325769 := bstep (se 2 (by rfl) ⟨1247163, by rfl⟩ : syracuseStep 3325769 = 2494327) B2494327
theorem B2217179 : Blo 2215435 2217179 := bstep (se 1 (by rfl) ⟨1662884, by rfl⟩ : syracuseStep 2217179 = 3325769) B3325769
theorem B3551501 : Blo 2215435 3551501 := bbase (se 3 (by rfl) ⟨665906, by rfl⟩ : syracuseStep 3551501 = 1331813) (by norm_num)
theorem B2367667 : Blo 2215435 2367667 := bstep (se 1 (by rfl) ⟨1775750, by rfl⟩ : syracuseStep 2367667 = 3551501) B3551501
theorem B3156889 : Blo 2215435 3156889 := bstep (se 2 (by rfl) ⟨1183833, by rfl⟩ : syracuseStep 3156889 = 2367667) B2367667
theorem B4209185 : Blo 2215435 4209185 := bstep (se 2 (by rfl) ⟨1578444, by rfl⟩ : syracuseStep 4209185 = 3156889) B3156889
theorem B11224493 : Blo 2215435 11224493 := bstep (se 3 (by rfl) ⟨2104592, by rfl⟩ : syracuseStep 11224493 = 4209185) B4209185
theorem B7482995 : Blo 2215435 7482995 := bstep (se 1 (by rfl) ⟨5612246, by rfl⟩ : syracuseStep 7482995 = 11224493) B11224493
theorem B4988663 : Blo 2215435 4988663 := bstep (se 1 (by rfl) ⟨3741497, by rfl⟩ : syracuseStep 4988663 = 7482995) B7482995
theorem B3325775 : Blo 2215435 3325775 := bstep (se 1 (by rfl) ⟨2494331, by rfl⟩ : syracuseStep 3325775 = 4988663) B4988663
theorem B2217183 : Blo 2215435 2217183 := bstep (se 1 (by rfl) ⟨1662887, by rfl⟩ : syracuseStep 2217183 = 3325775) B3325775
theorem B3325781 : Blo 2215435 3325781 := bbase (se 9 (by rfl) ⟨9743, by rfl⟩ : syracuseStep 3325781 = 19487) (by norm_num)
theorem B2217187 : Blo 2215435 2217187 := bstep (se 1 (by rfl) ⟨1662890, by rfl⟩ : syracuseStep 2217187 = 3325781) B3325781
theorem B3995453 : Blo 2215435 3995453 := bbase (se 3 (by rfl) ⟨749147, by rfl⟩ : syracuseStep 3995453 = 1498295) (by norm_num)
theorem B10654541 : Blo 2215435 10654541 := bstep (se 3 (by rfl) ⟨1997726, by rfl⟩ : syracuseStep 10654541 = 3995453) B3995453
theorem B7103027 : Blo 2215435 7103027 := bstep (se 1 (by rfl) ⟨5327270, by rfl⟩ : syracuseStep 7103027 = 10654541) B10654541
theorem B4735351 : Blo 2215435 4735351 := bstep (se 1 (by rfl) ⟨3551513, by rfl⟩ : syracuseStep 4735351 = 7103027) B7103027
theorem B6313801 : Blo 2215435 6313801 := bstep (se 2 (by rfl) ⟨2367675, by rfl⟩ : syracuseStep 6313801 = 4735351) B4735351
theorem B8418401 : Blo 2215435 8418401 := bstep (se 2 (by rfl) ⟨3156900, by rfl⟩ : syracuseStep 8418401 = 6313801) B6313801
theorem B5612267 : Blo 2215435 5612267 := bstep (se 1 (by rfl) ⟨4209200, by rfl⟩ : syracuseStep 5612267 = 8418401) B8418401
theorem B3741511 : Blo 2215435 3741511 := bstep (se 1 (by rfl) ⟨2806133, by rfl⟩ : syracuseStep 3741511 = 5612267) B5612267
theorem B4988681 : Blo 2215435 4988681 := bstep (se 2 (by rfl) ⟨1870755, by rfl⟩ : syracuseStep 4988681 = 3741511) B3741511
theorem B3325787 : Blo 2215435 3325787 := bstep (se 1 (by rfl) ⟨2494340, by rfl⟩ : syracuseStep 3325787 = 4988681) B4988681
theorem B2217191 : Blo 2215435 2217191 := bstep (se 1 (by rfl) ⟨1662893, by rfl⟩ : syracuseStep 2217191 = 3325787) B3325787
theorem B2494345 : Blo 2215435 2494345 := bbase (se 2 (by rfl) ⟨935379, by rfl⟩ : syracuseStep 2494345 = 1870759) (by norm_num)
theorem B3325793 : Blo 2215435 3325793 := bstep (se 2 (by rfl) ⟨1247172, by rfl⟩ : syracuseStep 3325793 = 2494345) B2494345
theorem B2217195 : Blo 2215435 2217195 := bstep (se 1 (by rfl) ⟨1662896, by rfl⟩ : syracuseStep 2217195 = 3325793) B3325793
theorem B40454101 : Blo 2215435 40454101 := bbase (se 7 (by rfl) ⟨474071, by rfl⟩ : syracuseStep 40454101 = 948143) (by norm_num)
theorem B53938801 : Blo 2215435 53938801 := bstep (se 2 (by rfl) ⟨20227050, by rfl⟩ : syracuseStep 53938801 = 40454101) B40454101
theorem B71918401 : Blo 2215435 71918401 := bstep (se 2 (by rfl) ⟨26969400, by rfl⟩ : syracuseStep 71918401 = 53938801) B53938801
theorem B95891201 : Blo 2215435 95891201 := bstep (se 2 (by rfl) ⟨35959200, by rfl⟩ : syracuseStep 95891201 = 71918401) B71918401
theorem B63927467 : Blo 2215435 63927467 := bstep (se 1 (by rfl) ⟨47945600, by rfl⟩ : syracuseStep 63927467 = 95891201) B95891201
theorem B42618311 : Blo 2215435 42618311 := bstep (se 1 (by rfl) ⟨31963733, by rfl⟩ : syracuseStep 42618311 = 63927467) B63927467
theorem B28412207 : Blo 2215435 28412207 := bstep (se 1 (by rfl) ⟨21309155, by rfl⟩ : syracuseStep 28412207 = 42618311) B42618311
theorem B18941471 : Blo 2215435 18941471 := bstep (se 1 (by rfl) ⟨14206103, by rfl⟩ : syracuseStep 18941471 = 28412207) B28412207
theorem B12627647 : Blo 2215435 12627647 := bstep (se 1 (by rfl) ⟨9470735, by rfl⟩ : syracuseStep 12627647 = 18941471) B18941471
theorem B8418431 : Blo 2215435 8418431 := bstep (se 1 (by rfl) ⟨6313823, by rfl⟩ : syracuseStep 8418431 = 12627647) B12627647
theorem B5612287 : Blo 2215435 5612287 := bstep (se 1 (by rfl) ⟨4209215, by rfl⟩ : syracuseStep 5612287 = 8418431) B8418431
theorem B7483049 : Blo 2215435 7483049 := bstep (se 2 (by rfl) ⟨2806143, by rfl⟩ : syracuseStep 7483049 = 5612287) B5612287
theorem B4988699 : Blo 2215435 4988699 := bstep (se 1 (by rfl) ⟨3741524, by rfl⟩ : syracuseStep 4988699 = 7483049) B7483049
theorem B3325799 : Blo 2215435 3325799 := bstep (se 1 (by rfl) ⟨2494349, by rfl⟩ : syracuseStep 3325799 = 4988699) B4988699
theorem B2217199 : Blo 2215435 2217199 := bstep (se 1 (by rfl) ⟨1662899, by rfl⟩ : syracuseStep 2217199 = 3325799) B3325799
theorem B3325805 : Blo 2215435 3325805 := bbase (se 3 (by rfl) ⟨623588, by rfl⟩ : syracuseStep 3325805 = 1247177) (by norm_num)
theorem B2217203 : Blo 2215435 2217203 := bstep (se 1 (by rfl) ⟨1662902, by rfl⟩ : syracuseStep 2217203 = 3325805) B3325805
theorem B4988717 : Blo 2215435 4988717 := bbase (se 3 (by rfl) ⟨935384, by rfl⟩ : syracuseStep 4988717 = 1870769) (by norm_num)
theorem B3325811 : Blo 2215435 3325811 := bstep (se 1 (by rfl) ⟨2494358, by rfl⟩ : syracuseStep 3325811 = 4988717) B4988717
theorem B2217207 : Blo 2215435 2217207 := bstep (se 1 (by rfl) ⟨1662905, by rfl⟩ : syracuseStep 2217207 = 3325811) B3325811
theorem B9470789 : Blo 2215435 9470789 := bbase (se 4 (by rfl) ⟨887886, by rfl⟩ : syracuseStep 9470789 = 1775773) (by norm_num)
theorem B6313859 : Blo 2215435 6313859 := bstep (se 1 (by rfl) ⟨4735394, by rfl⟩ : syracuseStep 6313859 = 9470789) B9470789
theorem B4209239 : Blo 2215435 4209239 := bstep (se 1 (by rfl) ⟨3156929, by rfl⟩ : syracuseStep 4209239 = 6313859) B6313859
theorem B2806159 : Blo 2215435 2806159 := bstep (se 1 (by rfl) ⟨2104619, by rfl⟩ : syracuseStep 2806159 = 4209239) B4209239
theorem B3741545 : Blo 2215435 3741545 := bstep (se 2 (by rfl) ⟨1403079, by rfl⟩ : syracuseStep 3741545 = 2806159) B2806159
theorem B2494363 : Blo 2215435 2494363 := bstep (se 1 (by rfl) ⟨1870772, by rfl⟩ : syracuseStep 2494363 = 3741545) B3741545
theorem B3325817 : Blo 2215435 3325817 := bstep (se 2 (by rfl) ⟨1247181, by rfl⟩ : syracuseStep 3325817 = 2494363) B2494363
theorem B2217211 : Blo 2215435 2217211 := bstep (se 1 (by rfl) ⟨1662908, by rfl⟩ : syracuseStep 2217211 = 3325817) B3325817
theorem B6075013 : Blo 2215435 6075013 := bbase (se 4 (by rfl) ⟨569532, by rfl⟩ : syracuseStep 6075013 = 1139065) (by norm_num)
theorem B8100017 : Blo 2215435 8100017 := bstep (se 2 (by rfl) ⟨3037506, by rfl⟩ : syracuseStep 8100017 = 6075013) B6075013
theorem B5400011 : Blo 2215435 5400011 := bstep (se 1 (by rfl) ⟨4050008, by rfl⟩ : syracuseStep 5400011 = 8100017) B8100017
theorem B3600007 : Blo 2215435 3600007 := bstep (se 1 (by rfl) ⟨2700005, by rfl⟩ : syracuseStep 3600007 = 5400011) B5400011
theorem B76800149 : Blo 2215435 76800149 := bstep (se 6 (by rfl) ⟨1800003, by rfl⟩ : syracuseStep 76800149 = 3600007) B3600007
theorem B51200099 : Blo 2215435 51200099 := bstep (se 1 (by rfl) ⟨38400074, by rfl⟩ : syracuseStep 51200099 = 76800149) B76800149
theorem B34133399 : Blo 2215435 34133399 := bstep (se 1 (by rfl) ⟨25600049, by rfl⟩ : syracuseStep 34133399 = 51200099) B51200099
theorem B22755599 : Blo 2215435 22755599 := bstep (se 1 (by rfl) ⟨17066699, by rfl⟩ : syracuseStep 22755599 = 34133399) B34133399
theorem B15170399 : Blo 2215435 15170399 := bstep (se 1 (by rfl) ⟨11377799, by rfl⟩ : syracuseStep 15170399 = 22755599) B22755599
theorem B10113599 : Blo 2215435 10113599 := bstep (se 1 (by rfl) ⟨7585199, by rfl⟩ : syracuseStep 10113599 = 15170399) B15170399
theorem B26969597 : Blo 2215435 26969597 := bstep (se 3 (by rfl) ⟨5056799, by rfl⟩ : syracuseStep 26969597 = 10113599) B10113599
theorem B17979731 : Blo 2215435 17979731 := bstep (se 1 (by rfl) ⟨13484798, by rfl⟩ : syracuseStep 17979731 = 26969597) B26969597
theorem B11986487 : Blo 2215435 11986487 := bstep (se 1 (by rfl) ⟨8989865, by rfl⟩ : syracuseStep 11986487 = 17979731) B17979731
theorem B7990991 : Blo 2215435 7990991 := bstep (se 1 (by rfl) ⟨5993243, by rfl⟩ : syracuseStep 7990991 = 11986487) B11986487
theorem B5327327 : Blo 2215435 5327327 := bstep (se 1 (by rfl) ⟨3995495, by rfl⟩ : syracuseStep 5327327 = 7990991) B7990991
theorem B14206205 : Blo 2215435 14206205 := bstep (se 3 (by rfl) ⟨2663663, by rfl⟩ : syracuseStep 14206205 = 5327327) B5327327
theorem B37883213 : Blo 2215435 37883213 := bstep (se 3 (by rfl) ⟨7103102, by rfl⟩ : syracuseStep 37883213 = 14206205) B14206205
theorem B25255475 : Blo 2215435 25255475 := bstep (se 1 (by rfl) ⟨18941606, by rfl⟩ : syracuseStep 25255475 = 37883213) B37883213
theorem B16836983 : Blo 2215435 16836983 := bstep (se 1 (by rfl) ⟨12627737, by rfl⟩ : syracuseStep 16836983 = 25255475) B25255475
theorem B11224655 : Blo 2215435 11224655 := bstep (se 1 (by rfl) ⟨8418491, by rfl⟩ : syracuseStep 11224655 = 16836983) B16836983
theorem B7483103 : Blo 2215435 7483103 := bstep (se 1 (by rfl) ⟨5612327, by rfl⟩ : syracuseStep 7483103 = 11224655) B11224655
theorem B4988735 : Blo 2215435 4988735 := bstep (se 1 (by rfl) ⟨3741551, by rfl⟩ : syracuseStep 4988735 = 7483103) B7483103
theorem B3325823 : Blo 2215435 3325823 := bstep (se 1 (by rfl) ⟨2494367, by rfl⟩ : syracuseStep 3325823 = 4988735) B4988735
theorem B2217215 : Blo 2215435 2217215 := bstep (se 1 (by rfl) ⟨1662911, by rfl⟩ : syracuseStep 2217215 = 3325823) B3325823
theorem B3325829 : Blo 2215435 3325829 := bbase (se 4 (by rfl) ⟨311796, by rfl⟩ : syracuseStep 3325829 = 623593) (by norm_num)
theorem B2217219 : Blo 2215435 2217219 := bstep (se 1 (by rfl) ⟨1662914, by rfl⟩ : syracuseStep 2217219 = 3325829) B3325829
theorem B3741565 : Blo 2215435 3741565 := bbase (se 3 (by rfl) ⟨701543, by rfl⟩ : syracuseStep 3741565 = 1403087) (by norm_num)
theorem B4988753 : Blo 2215435 4988753 := bstep (se 2 (by rfl) ⟨1870782, by rfl⟩ : syracuseStep 4988753 = 3741565) B3741565
theorem B3325835 : Blo 2215435 3325835 := bstep (se 1 (by rfl) ⟨2494376, by rfl⟩ : syracuseStep 3325835 = 4988753) B4988753
theorem B2217223 : Blo 2215435 2217223 := bstep (se 1 (by rfl) ⟨1662917, by rfl⟩ : syracuseStep 2217223 = 3325835) B3325835
theorem B2494381 : Blo 2215435 2494381 := bbase (se 3 (by rfl) ⟨467696, by rfl⟩ : syracuseStep 2494381 = 935393) (by norm_num)
theorem B3325841 : Blo 2215435 3325841 := bstep (se 2 (by rfl) ⟨1247190, by rfl⟩ : syracuseStep 3325841 = 2494381) B2494381
theorem B2217227 : Blo 2215435 2217227 := bstep (se 1 (by rfl) ⟨1662920, by rfl⟩ : syracuseStep 2217227 = 3325841) B3325841
theorem B7483157 : Blo 2215435 7483157 := bbase (se 6 (by rfl) ⟨175386, by rfl⟩ : syracuseStep 7483157 = 350773) (by norm_num)
theorem B4988771 : Blo 2215435 4988771 := bstep (se 1 (by rfl) ⟨3741578, by rfl⟩ : syracuseStep 4988771 = 7483157) B7483157
theorem B3325847 : Blo 2215435 3325847 := bstep (se 1 (by rfl) ⟨2494385, by rfl⟩ : syracuseStep 3325847 = 4988771) B4988771
theorem B2217231 : Blo 2215435 2217231 := bstep (se 1 (by rfl) ⟨1662923, by rfl⟩ : syracuseStep 2217231 = 3325847) B3325847
theorem B3325853 : Blo 2215435 3325853 := bbase (se 3 (by rfl) ⟨623597, by rfl⟩ : syracuseStep 3325853 = 1247195) (by norm_num)
theorem B2217235 : Blo 2215435 2217235 := bstep (se 1 (by rfl) ⟨1662926, by rfl⟩ : syracuseStep 2217235 = 3325853) B3325853
theorem B4988789 : Blo 2215435 4988789 := bbase (se 5 (by rfl) ⟨233849, by rfl⟩ : syracuseStep 4988789 = 467699) (by norm_num)
theorem B3325859 : Blo 2215435 3325859 := bstep (se 1 (by rfl) ⟨2494394, by rfl⟩ : syracuseStep 3325859 = 4988789) B4988789
theorem B2217239 : Blo 2215435 2217239 := bstep (se 1 (by rfl) ⟨1662929, by rfl⟩ : syracuseStep 2217239 = 3325859) B3325859
theorem B7991093 : Blo 2215435 7991093 := bbase (se 5 (by rfl) ⟨374582, by rfl⟩ : syracuseStep 7991093 = 749165) (by norm_num)
theorem B21309581 : Blo 2215435 21309581 := bstep (se 3 (by rfl) ⟨3995546, by rfl⟩ : syracuseStep 21309581 = 7991093) B7991093
theorem B14206387 : Blo 2215435 14206387 := bstep (se 1 (by rfl) ⟨10654790, by rfl⟩ : syracuseStep 14206387 = 21309581) B21309581
theorem B18941849 : Blo 2215435 18941849 := bstep (se 2 (by rfl) ⟨7103193, by rfl⟩ : syracuseStep 18941849 = 14206387) B14206387
theorem B12627899 : Blo 2215435 12627899 := bstep (se 1 (by rfl) ⟨9470924, by rfl⟩ : syracuseStep 12627899 = 18941849) B18941849
theorem B8418599 : Blo 2215435 8418599 := bstep (se 1 (by rfl) ⟨6313949, by rfl⟩ : syracuseStep 8418599 = 12627899) B12627899
theorem B5612399 : Blo 2215435 5612399 := bstep (se 1 (by rfl) ⟨4209299, by rfl⟩ : syracuseStep 5612399 = 8418599) B8418599
theorem B3741599 : Blo 2215435 3741599 := bstep (se 1 (by rfl) ⟨2806199, by rfl⟩ : syracuseStep 3741599 = 5612399) B5612399
theorem B2494399 : Blo 2215435 2494399 := bstep (se 1 (by rfl) ⟨1870799, by rfl⟩ : syracuseStep 2494399 = 3741599) B3741599
theorem B3325865 : Blo 2215435 3325865 := bstep (se 2 (by rfl) ⟨1247199, by rfl⟩ : syracuseStep 3325865 = 2494399) B2494399
theorem B2217243 : Blo 2215435 2217243 := bstep (se 1 (by rfl) ⟨1662932, by rfl⟩ : syracuseStep 2217243 = 3325865) B3325865
theorem B8418613 : Blo 2215435 8418613 := bbase (se 5 (by rfl) ⟨394622, by rfl⟩ : syracuseStep 8418613 = 789245) (by norm_num)
theorem B11224817 : Blo 2215435 11224817 := bstep (se 2 (by rfl) ⟨4209306, by rfl⟩ : syracuseStep 11224817 = 8418613) B8418613
theorem B7483211 : Blo 2215435 7483211 := bstep (se 1 (by rfl) ⟨5612408, by rfl⟩ : syracuseStep 7483211 = 11224817) B11224817
theorem B4988807 : Blo 2215435 4988807 := bstep (se 1 (by rfl) ⟨3741605, by rfl⟩ : syracuseStep 4988807 = 7483211) B7483211
theorem B3325871 : Blo 2215435 3325871 := bstep (se 1 (by rfl) ⟨2494403, by rfl⟩ : syracuseStep 3325871 = 4988807) B4988807
theorem B2217247 : Blo 2215435 2217247 := bstep (se 1 (by rfl) ⟨1662935, by rfl⟩ : syracuseStep 2217247 = 3325871) B3325871
theorem B3325877 : Blo 2215435 3325877 := bbase (se 5 (by rfl) ⟨155900, by rfl⟩ : syracuseStep 3325877 = 311801) (by norm_num)
theorem B2217251 : Blo 2215435 2217251 := bstep (se 1 (by rfl) ⟨1662938, by rfl⟩ : syracuseStep 2217251 = 3325877) B3325877
theorem B5612429 : Blo 2215435 5612429 := bbase (se 3 (by rfl) ⟨1052330, by rfl⟩ : syracuseStep 5612429 = 2104661) (by norm_num)
theorem B3741619 : Blo 2215435 3741619 := bstep (se 1 (by rfl) ⟨2806214, by rfl⟩ : syracuseStep 3741619 = 5612429) B5612429
theorem B4988825 : Blo 2215435 4988825 := bstep (se 2 (by rfl) ⟨1870809, by rfl⟩ : syracuseStep 4988825 = 3741619) B3741619
theorem B3325883 : Blo 2215435 3325883 := bstep (se 1 (by rfl) ⟨2494412, by rfl⟩ : syracuseStep 3325883 = 4988825) B4988825
theorem B2217255 : Blo 2215435 2217255 := bstep (se 1 (by rfl) ⟨1662941, by rfl⟩ : syracuseStep 2217255 = 3325883) B3325883
theorem B2494417 : Blo 2215435 2494417 := bbase (se 2 (by rfl) ⟨935406, by rfl⟩ : syracuseStep 2494417 = 1870813) (by norm_num)
theorem B3325889 : Blo 2215435 3325889 := bstep (se 2 (by rfl) ⟨1247208, by rfl⟩ : syracuseStep 3325889 = 2494417) B2494417
theorem B2217259 : Blo 2215435 2217259 := bstep (se 1 (by rfl) ⟨1662944, by rfl⟩ : syracuseStep 2217259 = 3325889) B3325889
theorem B3551629 : Blo 2215435 3551629 := bbase (se 3 (by rfl) ⟨665930, by rfl⟩ : syracuseStep 3551629 = 1331861) (by norm_num)
theorem B4735505 : Blo 2215435 4735505 := bstep (se 2 (by rfl) ⟨1775814, by rfl⟩ : syracuseStep 4735505 = 3551629) B3551629
theorem B3157003 : Blo 2215435 3157003 := bstep (se 1 (by rfl) ⟨2367752, by rfl⟩ : syracuseStep 3157003 = 4735505) B4735505
theorem B4209337 : Blo 2215435 4209337 := bstep (se 2 (by rfl) ⟨1578501, by rfl⟩ : syracuseStep 4209337 = 3157003) B3157003
theorem B5612449 : Blo 2215435 5612449 := bstep (se 2 (by rfl) ⟨2104668, by rfl⟩ : syracuseStep 5612449 = 4209337) B4209337
theorem B7483265 : Blo 2215435 7483265 := bstep (se 2 (by rfl) ⟨2806224, by rfl⟩ : syracuseStep 7483265 = 5612449) B5612449
theorem B4988843 : Blo 2215435 4988843 := bstep (se 1 (by rfl) ⟨3741632, by rfl⟩ : syracuseStep 4988843 = 7483265) B7483265
theorem B3325895 : Blo 2215435 3325895 := bstep (se 1 (by rfl) ⟨2494421, by rfl⟩ : syracuseStep 3325895 = 4988843) B4988843
theorem B2217263 : Blo 2215435 2217263 := bstep (se 1 (by rfl) ⟨1662947, by rfl⟩ : syracuseStep 2217263 = 3325895) B3325895
theorem B3325901 : Blo 2215435 3325901 := bbase (se 3 (by rfl) ⟨623606, by rfl⟩ : syracuseStep 3325901 = 1247213) (by norm_num)
theorem B2217267 : Blo 2215435 2217267 := bstep (se 1 (by rfl) ⟨1662950, by rfl⟩ : syracuseStep 2217267 = 3325901) B3325901
theorem B4988861 : Blo 2215435 4988861 := bbase (se 3 (by rfl) ⟨935411, by rfl⟩ : syracuseStep 4988861 = 1870823) (by norm_num)
theorem B3325907 : Blo 2215435 3325907 := bstep (se 1 (by rfl) ⟨2494430, by rfl⟩ : syracuseStep 3325907 = 4988861) B4988861
theorem B2217271 : Blo 2215435 2217271 := bstep (se 1 (by rfl) ⟨1662953, by rfl⟩ : syracuseStep 2217271 = 3325907) B3325907
theorem B3741653 : Blo 2215435 3741653 := bbase (se 7 (by rfl) ⟨43847, by rfl⟩ : syracuseStep 3741653 = 87695) (by norm_num)
theorem B2494435 : Blo 2215435 2494435 := bstep (se 1 (by rfl) ⟨1870826, by rfl⟩ : syracuseStep 2494435 = 3741653) B3741653
theorem B3325913 : Blo 2215435 3325913 := bstep (se 2 (by rfl) ⟨1247217, by rfl⟩ : syracuseStep 3325913 = 2494435) B2494435
theorem B2217275 : Blo 2215435 2217275 := bstep (se 1 (by rfl) ⟨1662956, by rfl⟩ : syracuseStep 2217275 = 3325913) B3325913
theorem B9471077 : Blo 2215435 9471077 := bbase (se 4 (by rfl) ⟨887913, by rfl⟩ : syracuseStep 9471077 = 1775827) (by norm_num)
theorem B6314051 : Blo 2215435 6314051 := bstep (se 1 (by rfl) ⟨4735538, by rfl⟩ : syracuseStep 6314051 = 9471077) B9471077
theorem B16837469 : Blo 2215435 16837469 := bstep (se 3 (by rfl) ⟨3157025, by rfl⟩ : syracuseStep 16837469 = 6314051) B6314051
theorem B11224979 : Blo 2215435 11224979 := bstep (se 1 (by rfl) ⟨8418734, by rfl⟩ : syracuseStep 11224979 = 16837469) B16837469
theorem B7483319 : Blo 2215435 7483319 := bstep (se 1 (by rfl) ⟨5612489, by rfl⟩ : syracuseStep 7483319 = 11224979) B11224979
theorem B4988879 : Blo 2215435 4988879 := bstep (se 1 (by rfl) ⟨3741659, by rfl⟩ : syracuseStep 4988879 = 7483319) B7483319
theorem B3325919 : Blo 2215435 3325919 := bstep (se 1 (by rfl) ⟨2494439, by rfl⟩ : syracuseStep 3325919 = 4988879) B4988879
theorem B2217279 : Blo 2215435 2217279 := bstep (se 1 (by rfl) ⟨1662959, by rfl⟩ : syracuseStep 2217279 = 3325919) B3325919
theorem B3325925 : Blo 2215435 3325925 := bbase (se 4 (by rfl) ⟨311805, by rfl⟩ : syracuseStep 3325925 = 623611) (by norm_num)
theorem B2217283 : Blo 2215435 2217283 := bstep (se 1 (by rfl) ⟨1662962, by rfl⟩ : syracuseStep 2217283 = 3325925) B3325925
theorem B3600125 : Blo 2215435 3600125 := bbase (se 3 (by rfl) ⟨675023, by rfl⟩ : syracuseStep 3600125 = 1350047) (by norm_num)
theorem B2400083 : Blo 2215435 2400083 := bstep (se 1 (by rfl) ⟨1800062, by rfl⟩ : syracuseStep 2400083 = 3600125) B3600125
theorem B102403541 : Blo 2215435 102403541 := bstep (se 7 (by rfl) ⟨1200041, by rfl⟩ : syracuseStep 102403541 = 2400083) B2400083
theorem B68269027 : Blo 2215435 68269027 := bstep (se 1 (by rfl) ⟨51201770, by rfl⟩ : syracuseStep 68269027 = 102403541) B102403541
theorem B91025369 : Blo 2215435 91025369 := bstep (se 2 (by rfl) ⟨34134513, by rfl⟩ : syracuseStep 91025369 = 68269027) B68269027
theorem B60683579 : Blo 2215435 60683579 := bstep (se 1 (by rfl) ⟨45512684, by rfl⟩ : syracuseStep 60683579 = 91025369) B91025369
theorem B40455719 : Blo 2215435 40455719 := bstep (se 1 (by rfl) ⟨30341789, by rfl⟩ : syracuseStep 40455719 = 60683579) B60683579
theorem B26970479 : Blo 2215435 26970479 := bstep (se 1 (by rfl) ⟨20227859, by rfl⟩ : syracuseStep 26970479 = 40455719) B40455719
theorem B17980319 : Blo 2215435 17980319 := bstep (se 1 (by rfl) ⟨13485239, by rfl⟩ : syracuseStep 17980319 = 26970479) B26970479
theorem B11986879 : Blo 2215435 11986879 := bstep (se 1 (by rfl) ⟨8990159, by rfl⟩ : syracuseStep 11986879 = 17980319) B17980319
theorem B15982505 : Blo 2215435 15982505 := bstep (se 2 (by rfl) ⟨5993439, by rfl⟩ : syracuseStep 15982505 = 11986879) B11986879
theorem B10655003 : Blo 2215435 10655003 := bstep (se 1 (by rfl) ⟨7991252, by rfl⟩ : syracuseStep 10655003 = 15982505) B15982505
theorem B7103335 : Blo 2215435 7103335 := bstep (se 1 (by rfl) ⟨5327501, by rfl⟩ : syracuseStep 7103335 = 10655003) B10655003
theorem B9471113 : Blo 2215435 9471113 := bstep (se 2 (by rfl) ⟨3551667, by rfl⟩ : syracuseStep 9471113 = 7103335) B7103335
theorem B6314075 : Blo 2215435 6314075 := bstep (se 1 (by rfl) ⟨4735556, by rfl⟩ : syracuseStep 6314075 = 9471113) B9471113
theorem B4209383 : Blo 2215435 4209383 := bstep (se 1 (by rfl) ⟨3157037, by rfl⟩ : syracuseStep 4209383 = 6314075) B6314075
theorem B2806255 : Blo 2215435 2806255 := bstep (se 1 (by rfl) ⟨2104691, by rfl⟩ : syracuseStep 2806255 = 4209383) B4209383
theorem B3741673 : Blo 2215435 3741673 := bstep (se 2 (by rfl) ⟨1403127, by rfl⟩ : syracuseStep 3741673 = 2806255) B2806255
theorem B4988897 : Blo 2215435 4988897 := bstep (se 2 (by rfl) ⟨1870836, by rfl⟩ : syracuseStep 4988897 = 3741673) B3741673
theorem B3325931 : Blo 2215435 3325931 := bstep (se 1 (by rfl) ⟨2494448, by rfl⟩ : syracuseStep 3325931 = 4988897) B4988897
theorem B2217287 : Blo 2215435 2217287 := bstep (se 1 (by rfl) ⟨1662965, by rfl⟩ : syracuseStep 2217287 = 3325931) B3325931
theorem B2494453 : Blo 2215435 2494453 := bbase (se 5 (by rfl) ⟨116927, by rfl⟩ : syracuseStep 2494453 = 233855) (by norm_num)
theorem B3325937 : Blo 2215435 3325937 := bstep (se 2 (by rfl) ⟨1247226, by rfl⟩ : syracuseStep 3325937 = 2494453) B2494453
theorem B2217291 : Blo 2215435 2217291 := bstep (se 1 (by rfl) ⟨1662968, by rfl⟩ : syracuseStep 2217291 = 3325937) B3325937
theorem B2806265 : Blo 2215435 2806265 := bbase (se 2 (by rfl) ⟨1052349, by rfl⟩ : syracuseStep 2806265 = 2104699) (by norm_num)
theorem B7483373 : Blo 2215435 7483373 := bstep (se 3 (by rfl) ⟨1403132, by rfl⟩ : syracuseStep 7483373 = 2806265) B2806265
theorem B4988915 : Blo 2215435 4988915 := bstep (se 1 (by rfl) ⟨3741686, by rfl⟩ : syracuseStep 4988915 = 7483373) B7483373
theorem B3325943 : Blo 2215435 3325943 := bstep (se 1 (by rfl) ⟨2494457, by rfl⟩ : syracuseStep 3325943 = 4988915) B4988915
theorem B2217295 : Blo 2215435 2217295 := bstep (se 1 (by rfl) ⟨1662971, by rfl⟩ : syracuseStep 2217295 = 3325943) B3325943
theorem B3325949 : Blo 2215435 3325949 := bbase (se 3 (by rfl) ⟨623615, by rfl⟩ : syracuseStep 3325949 = 1247231) (by norm_num)
theorem B2217299 : Blo 2215435 2217299 := bstep (se 1 (by rfl) ⟨1662974, by rfl⟩ : syracuseStep 2217299 = 3325949) B3325949
theorem B4988933 : Blo 2215435 4988933 := bbase (se 4 (by rfl) ⟨467712, by rfl⟩ : syracuseStep 4988933 = 935425) (by norm_num)
theorem B3325955 : Blo 2215435 3325955 := bstep (se 1 (by rfl) ⟨2494466, by rfl⟩ : syracuseStep 3325955 = 4988933) B4988933
theorem B2217303 : Blo 2215435 2217303 := bstep (se 1 (by rfl) ⟨1662977, by rfl⟩ : syracuseStep 2217303 = 3325955) B3325955
theorem B4209421 : Blo 2215435 4209421 := bbase (se 3 (by rfl) ⟨789266, by rfl⟩ : syracuseStep 4209421 = 1578533) (by norm_num)
theorem B5612561 : Blo 2215435 5612561 := bstep (se 2 (by rfl) ⟨2104710, by rfl⟩ : syracuseStep 5612561 = 4209421) B4209421
theorem B3741707 : Blo 2215435 3741707 := bstep (se 1 (by rfl) ⟨2806280, by rfl⟩ : syracuseStep 3741707 = 5612561) B5612561
theorem B2494471 : Blo 2215435 2494471 := bstep (se 1 (by rfl) ⟨1870853, by rfl⟩ : syracuseStep 2494471 = 3741707) B3741707
theorem B3325961 : Blo 2215435 3325961 := bstep (se 2 (by rfl) ⟨1247235, by rfl⟩ : syracuseStep 3325961 = 2494471) B2494471
theorem B2217307 : Blo 2215435 2217307 := bstep (se 1 (by rfl) ⟨1662980, by rfl⟩ : syracuseStep 2217307 = 3325961) B3325961
theorem B11225141 : Blo 2215435 11225141 := bbase (se 5 (by rfl) ⟨526178, by rfl⟩ : syracuseStep 11225141 = 1052357) (by norm_num)
theorem B7483427 : Blo 2215435 7483427 := bstep (se 1 (by rfl) ⟨5612570, by rfl⟩ : syracuseStep 7483427 = 11225141) B11225141
theorem B4988951 : Blo 2215435 4988951 := bstep (se 1 (by rfl) ⟨3741713, by rfl⟩ : syracuseStep 4988951 = 7483427) B7483427
theorem B3325967 : Blo 2215435 3325967 := bstep (se 1 (by rfl) ⟨2494475, by rfl⟩ : syracuseStep 3325967 = 4988951) B4988951
theorem B2217311 : Blo 2215435 2217311 := bstep (se 1 (by rfl) ⟨1662983, by rfl⟩ : syracuseStep 2217311 = 3325967) B3325967
theorem B3325973 : Blo 2215435 3325973 := bbase (se 6 (by rfl) ⟨77952, by rfl⟩ : syracuseStep 3325973 = 155905) (by norm_num)
theorem B2217315 : Blo 2215435 2217315 := bstep (se 1 (by rfl) ⟨1662986, by rfl⟩ : syracuseStep 2217315 = 3325973) B3325973
theorem B5993525 : Blo 2215435 5993525 := bbase (se 5 (by rfl) ⟨280946, by rfl⟩ : syracuseStep 5993525 = 561893) (by norm_num)
theorem B15982733 : Blo 2215435 15982733 := bstep (se 3 (by rfl) ⟨2996762, by rfl⟩ : syracuseStep 15982733 = 5993525) B5993525
theorem B10655155 : Blo 2215435 10655155 := bstep (se 1 (by rfl) ⟨7991366, by rfl⟩ : syracuseStep 10655155 = 15982733) B15982733
theorem B14206873 : Blo 2215435 14206873 := bstep (se 2 (by rfl) ⟨5327577, by rfl⟩ : syracuseStep 14206873 = 10655155) B10655155
theorem B18942497 : Blo 2215435 18942497 := bstep (se 2 (by rfl) ⟨7103436, by rfl⟩ : syracuseStep 18942497 = 14206873) B14206873
theorem B12628331 : Blo 2215435 12628331 := bstep (se 1 (by rfl) ⟨9471248, by rfl⟩ : syracuseStep 12628331 = 18942497) B18942497
theorem B8418887 : Blo 2215435 8418887 := bstep (se 1 (by rfl) ⟨6314165, by rfl⟩ : syracuseStep 8418887 = 12628331) B12628331
theorem B5612591 : Blo 2215435 5612591 := bstep (se 1 (by rfl) ⟨4209443, by rfl⟩ : syracuseStep 5612591 = 8418887) B8418887
theorem B3741727 : Blo 2215435 3741727 := bstep (se 1 (by rfl) ⟨2806295, by rfl⟩ : syracuseStep 3741727 = 5612591) B5612591
theorem B4988969 : Blo 2215435 4988969 := bstep (se 2 (by rfl) ⟨1870863, by rfl⟩ : syracuseStep 4988969 = 3741727) B3741727
theorem B3325979 : Blo 2215435 3325979 := bstep (se 1 (by rfl) ⟨2494484, by rfl⟩ : syracuseStep 3325979 = 4988969) B4988969
theorem B2217319 : Blo 2215435 2217319 := bstep (se 1 (by rfl) ⟨1662989, by rfl⟩ : syracuseStep 2217319 = 3325979) B3325979
theorem B2494489 : Blo 2215435 2494489 := bbase (se 2 (by rfl) ⟨935433, by rfl⟩ : syracuseStep 2494489 = 1870867) (by norm_num)
theorem B3325985 : Blo 2215435 3325985 := bstep (se 2 (by rfl) ⟨1247244, by rfl⟩ : syracuseStep 3325985 = 2494489) B2494489
theorem B2217323 : Blo 2215435 2217323 := bstep (se 1 (by rfl) ⟨1662992, by rfl⟩ : syracuseStep 2217323 = 3325985) B3325985
theorem B8418917 : Blo 2215435 8418917 := bbase (se 4 (by rfl) ⟨789273, by rfl⟩ : syracuseStep 8418917 = 1578547) (by norm_num)
theorem B5612611 : Blo 2215435 5612611 := bstep (se 1 (by rfl) ⟨4209458, by rfl⟩ : syracuseStep 5612611 = 8418917) B8418917
theorem B7483481 : Blo 2215435 7483481 := bstep (se 2 (by rfl) ⟨2806305, by rfl⟩ : syracuseStep 7483481 = 5612611) B5612611
theorem B4988987 : Blo 2215435 4988987 := bstep (se 1 (by rfl) ⟨3741740, by rfl⟩ : syracuseStep 4988987 = 7483481) B7483481
theorem B3325991 : Blo 2215435 3325991 := bstep (se 1 (by rfl) ⟨2494493, by rfl⟩ : syracuseStep 3325991 = 4988987) B4988987
theorem B2217327 : Blo 2215435 2217327 := bstep (se 1 (by rfl) ⟨1662995, by rfl⟩ : syracuseStep 2217327 = 3325991) B3325991
theorem B3325997 : Blo 2215435 3325997 := bbase (se 3 (by rfl) ⟨623624, by rfl⟩ : syracuseStep 3325997 = 1247249) (by norm_num)
theorem B2217331 : Blo 2215435 2217331 := bstep (se 1 (by rfl) ⟨1662998, by rfl⟩ : syracuseStep 2217331 = 3325997) B3325997
theorem B4989005 : Blo 2215435 4989005 := bbase (se 3 (by rfl) ⟨935438, by rfl⟩ : syracuseStep 4989005 = 1870877) (by norm_num)
theorem B3326003 : Blo 2215435 3326003 := bstep (se 1 (by rfl) ⟨2494502, by rfl⟩ : syracuseStep 3326003 = 4989005) B4989005
theorem B2217335 : Blo 2215435 2217335 := bstep (se 1 (by rfl) ⟨1663001, by rfl⟩ : syracuseStep 2217335 = 3326003) B3326003
theorem B2806321 : Blo 2215435 2806321 := bbase (se 2 (by rfl) ⟨1052370, by rfl⟩ : syracuseStep 2806321 = 2104741) (by norm_num)
theorem B3741761 : Blo 2215435 3741761 := bstep (se 2 (by rfl) ⟨1403160, by rfl⟩ : syracuseStep 3741761 = 2806321) B2806321
theorem B2494507 : Blo 2215435 2494507 := bstep (se 1 (by rfl) ⟨1870880, by rfl⟩ : syracuseStep 2494507 = 3741761) B3741761
theorem B3326009 : Blo 2215435 3326009 := bstep (se 2 (by rfl) ⟨1247253, by rfl⟩ : syracuseStep 3326009 = 2494507) B2494507
theorem B2217339 : Blo 2215435 2217339 := bstep (se 1 (by rfl) ⟨1663004, by rfl⟩ : syracuseStep 2217339 = 3326009) B3326009
theorem B5057093 : Blo 2215435 5057093 := bbase (se 4 (by rfl) ⟨474102, by rfl⟩ : syracuseStep 5057093 = 948205) (by norm_num)
theorem B3371395 : Blo 2215435 3371395 := bstep (se 1 (by rfl) ⟨2528546, by rfl⟩ : syracuseStep 3371395 = 5057093) B5057093
theorem B4495193 : Blo 2215435 4495193 := bstep (se 2 (by rfl) ⟨1685697, by rfl⟩ : syracuseStep 4495193 = 3371395) B3371395
theorem B2996795 : Blo 2215435 2996795 := bstep (se 1 (by rfl) ⟨2247596, by rfl⟩ : syracuseStep 2996795 = 4495193) B4495193
theorem B7991453 : Blo 2215435 7991453 := bstep (se 3 (by rfl) ⟨1498397, by rfl⟩ : syracuseStep 7991453 = 2996795) B2996795
theorem B5327635 : Blo 2215435 5327635 := bstep (se 1 (by rfl) ⟨3995726, by rfl⟩ : syracuseStep 5327635 = 7991453) B7991453
theorem B7103513 : Blo 2215435 7103513 := bstep (se 2 (by rfl) ⟨2663817, by rfl⟩ : syracuseStep 7103513 = 5327635) B5327635
theorem B4735675 : Blo 2215435 4735675 := bstep (se 1 (by rfl) ⟨3551756, by rfl⟩ : syracuseStep 4735675 = 7103513) B7103513
theorem B25256933 : Blo 2215435 25256933 := bstep (se 4 (by rfl) ⟨2367837, by rfl⟩ : syracuseStep 25256933 = 4735675) B4735675
theorem B16837955 : Blo 2215435 16837955 := bstep (se 1 (by rfl) ⟨12628466, by rfl⟩ : syracuseStep 16837955 = 25256933) B25256933
theorem B11225303 : Blo 2215435 11225303 := bstep (se 1 (by rfl) ⟨8418977, by rfl⟩ : syracuseStep 11225303 = 16837955) B16837955
theorem B7483535 : Blo 2215435 7483535 := bstep (se 1 (by rfl) ⟨5612651, by rfl⟩ : syracuseStep 7483535 = 11225303) B11225303
theorem B4989023 : Blo 2215435 4989023 := bstep (se 1 (by rfl) ⟨3741767, by rfl⟩ : syracuseStep 4989023 = 7483535) B7483535
theorem B3326015 : Blo 2215435 3326015 := bstep (se 1 (by rfl) ⟨2494511, by rfl⟩ : syracuseStep 3326015 = 4989023) B4989023
theorem B2217343 : Blo 2215435 2217343 := bstep (se 1 (by rfl) ⟨1663007, by rfl⟩ : syracuseStep 2217343 = 3326015) B3326015
theorem B3326021 : Blo 2215435 3326021 := bbase (se 4 (by rfl) ⟨311814, by rfl⟩ : syracuseStep 3326021 = 623629) (by norm_num)
theorem B2217347 : Blo 2215435 2217347 := bstep (se 1 (by rfl) ⟨1663010, by rfl⟩ : syracuseStep 2217347 = 3326021) B3326021
theorem B3741781 : Blo 2215435 3741781 := bbase (se 8 (by rfl) ⟨21924, by rfl⟩ : syracuseStep 3741781 = 43849) (by norm_num)
theorem B4989041 : Blo 2215435 4989041 := bstep (se 2 (by rfl) ⟨1870890, by rfl⟩ : syracuseStep 4989041 = 3741781) B3741781
theorem B3326027 : Blo 2215435 3326027 := bstep (se 1 (by rfl) ⟨2494520, by rfl⟩ : syracuseStep 3326027 = 4989041) B4989041
theorem B2217351 : Blo 2215435 2217351 := bstep (se 1 (by rfl) ⟨1663013, by rfl⟩ : syracuseStep 2217351 = 3326027) B3326027
theorem B2494525 : Blo 2215435 2494525 := bbase (se 3 (by rfl) ⟨467723, by rfl⟩ : syracuseStep 2494525 = 935447) (by norm_num)
theorem B3326033 : Blo 2215435 3326033 := bstep (se 2 (by rfl) ⟨1247262, by rfl⟩ : syracuseStep 3326033 = 2494525) B2494525
theorem B2217355 : Blo 2215435 2217355 := bstep (se 1 (by rfl) ⟨1663016, by rfl⟩ : syracuseStep 2217355 = 3326033) B3326033
theorem B7483589 : Blo 2215435 7483589 := bbase (se 4 (by rfl) ⟨701586, by rfl⟩ : syracuseStep 7483589 = 1403173) (by norm_num)
theorem B4989059 : Blo 2215435 4989059 := bstep (se 1 (by rfl) ⟨3741794, by rfl⟩ : syracuseStep 4989059 = 7483589) B7483589
theorem B3326039 : Blo 2215435 3326039 := bstep (se 1 (by rfl) ⟨2494529, by rfl⟩ : syracuseStep 3326039 = 4989059) B4989059
theorem B2217359 : Blo 2215435 2217359 := bstep (se 1 (by rfl) ⟨1663019, by rfl⟩ : syracuseStep 2217359 = 3326039) B3326039
theorem B3326045 : Blo 2215435 3326045 := bbase (se 3 (by rfl) ⟨623633, by rfl⟩ : syracuseStep 3326045 = 1247267) (by norm_num)
theorem B2217363 : Blo 2215435 2217363 := bstep (se 1 (by rfl) ⟨1663022, by rfl⟩ : syracuseStep 2217363 = 3326045) B3326045
theorem B4989077 : Blo 2215435 4989077 := bbase (se 6 (by rfl) ⟨116931, by rfl⟩ : syracuseStep 4989077 = 233863) (by norm_num)
theorem B3326051 : Blo 2215435 3326051 := bstep (se 1 (by rfl) ⟨2494538, by rfl⟩ : syracuseStep 3326051 = 4989077) B4989077
theorem B2217367 : Blo 2215435 2217367 := bstep (se 1 (by rfl) ⟨1663025, by rfl⟩ : syracuseStep 2217367 = 3326051) B3326051
theorem B3157157 : Blo 2215435 3157157 := bbase (se 4 (by rfl) ⟨295983, by rfl⟩ : syracuseStep 3157157 = 591967) (by norm_num)
theorem B8419085 : Blo 2215435 8419085 := bstep (se 3 (by rfl) ⟨1578578, by rfl⟩ : syracuseStep 8419085 = 3157157) B3157157
theorem B5612723 : Blo 2215435 5612723 := bstep (se 1 (by rfl) ⟨4209542, by rfl⟩ : syracuseStep 5612723 = 8419085) B8419085
theorem B3741815 : Blo 2215435 3741815 := bstep (se 1 (by rfl) ⟨2806361, by rfl⟩ : syracuseStep 3741815 = 5612723) B5612723
theorem B2494543 : Blo 2215435 2494543 := bstep (se 1 (by rfl) ⟨1870907, by rfl⟩ : syracuseStep 2494543 = 3741815) B3741815
theorem B3326057 : Blo 2215435 3326057 := bstep (se 2 (by rfl) ⟨1247271, by rfl⟩ : syracuseStep 3326057 = 2494543) B2494543
theorem B2217371 : Blo 2215435 2217371 := bstep (se 1 (by rfl) ⟨1663028, by rfl⟩ : syracuseStep 2217371 = 3326057) B3326057
theorem B7200533 : Blo 2215435 7200533 := bbase (se 6 (by rfl) ⟨168762, by rfl⟩ : syracuseStep 7200533 = 337525) (by norm_num)
theorem B19201421 : Blo 2215435 19201421 := bstep (se 3 (by rfl) ⟨3600266, by rfl⟩ : syracuseStep 19201421 = 7200533) B7200533
theorem B12800947 : Blo 2215435 12800947 := bstep (se 1 (by rfl) ⟨9600710, by rfl⟩ : syracuseStep 12800947 = 19201421) B19201421
theorem B17067929 : Blo 2215435 17067929 := bstep (se 2 (by rfl) ⟨6400473, by rfl⟩ : syracuseStep 17067929 = 12800947) B12800947
theorem B45514477 : Blo 2215435 45514477 := bstep (se 3 (by rfl) ⟨8533964, by rfl⟩ : syracuseStep 45514477 = 17067929) B17067929
theorem B242743877 : Blo 2215435 242743877 := bstep (se 4 (by rfl) ⟨22757238, by rfl⟩ : syracuseStep 242743877 = 45514477) B45514477
theorem B161829251 : Blo 2215435 161829251 := bstep (se 1 (by rfl) ⟨121371938, by rfl⟩ : syracuseStep 161829251 = 242743877) B242743877
theorem B107886167 : Blo 2215435 107886167 := bstep (se 1 (by rfl) ⟨80914625, by rfl⟩ : syracuseStep 107886167 = 161829251) B161829251
theorem B71924111 : Blo 2215435 71924111 := bstep (se 1 (by rfl) ⟨53943083, by rfl⟩ : syracuseStep 71924111 = 107886167) B107886167
theorem B47949407 : Blo 2215435 47949407 := bstep (se 1 (by rfl) ⟨35962055, by rfl⟩ : syracuseStep 47949407 = 71924111) B71924111
theorem B31966271 : Blo 2215435 31966271 := bstep (se 1 (by rfl) ⟨23974703, by rfl⟩ : syracuseStep 31966271 = 47949407) B47949407
theorem B21310847 : Blo 2215435 21310847 := bstep (se 1 (by rfl) ⟨15983135, by rfl⟩ : syracuseStep 21310847 = 31966271) B31966271
theorem B14207231 : Blo 2215435 14207231 := bstep (se 1 (by rfl) ⟨10655423, by rfl⟩ : syracuseStep 14207231 = 21310847) B21310847
theorem B9471487 : Blo 2215435 9471487 := bstep (se 1 (by rfl) ⟨7103615, by rfl⟩ : syracuseStep 9471487 = 14207231) B14207231
theorem B12628649 : Blo 2215435 12628649 := bstep (se 2 (by rfl) ⟨4735743, by rfl⟩ : syracuseStep 12628649 = 9471487) B9471487
theorem B8419099 : Blo 2215435 8419099 := bstep (se 1 (by rfl) ⟨6314324, by rfl⟩ : syracuseStep 8419099 = 12628649) B12628649
theorem B11225465 : Blo 2215435 11225465 := bstep (se 2 (by rfl) ⟨4209549, by rfl⟩ : syracuseStep 11225465 = 8419099) B8419099
theorem B7483643 : Blo 2215435 7483643 := bstep (se 1 (by rfl) ⟨5612732, by rfl⟩ : syracuseStep 7483643 = 11225465) B11225465
theorem B4989095 : Blo 2215435 4989095 := bstep (se 1 (by rfl) ⟨3741821, by rfl⟩ : syracuseStep 4989095 = 7483643) B7483643
theorem B3326063 : Blo 2215435 3326063 := bstep (se 1 (by rfl) ⟨2494547, by rfl⟩ : syracuseStep 3326063 = 4989095) B4989095
theorem B2217375 : Blo 2215435 2217375 := bstep (se 1 (by rfl) ⟨1663031, by rfl⟩ : syracuseStep 2217375 = 3326063) B3326063
theorem B3326069 : Blo 2215435 3326069 := bbase (se 5 (by rfl) ⟨155909, by rfl⟩ : syracuseStep 3326069 = 311819) (by norm_num)
theorem B2217379 : Blo 2215435 2217379 := bstep (se 1 (by rfl) ⟨1663034, by rfl⟩ : syracuseStep 2217379 = 3326069) B3326069
theorem B4209565 : Blo 2215435 4209565 := bbase (se 3 (by rfl) ⟨789293, by rfl⟩ : syracuseStep 4209565 = 1578587) (by norm_num)
theorem B5612753 : Blo 2215435 5612753 := bstep (se 2 (by rfl) ⟨2104782, by rfl⟩ : syracuseStep 5612753 = 4209565) B4209565
theorem B3741835 : Blo 2215435 3741835 := bstep (se 1 (by rfl) ⟨2806376, by rfl⟩ : syracuseStep 3741835 = 5612753) B5612753
theorem B4989113 : Blo 2215435 4989113 := bstep (se 2 (by rfl) ⟨1870917, by rfl⟩ : syracuseStep 4989113 = 3741835) B3741835
theorem B3326075 : Blo 2215435 3326075 := bstep (se 1 (by rfl) ⟨2494556, by rfl⟩ : syracuseStep 3326075 = 4989113) B4989113
theorem B2217383 : Blo 2215435 2217383 := bstep (se 1 (by rfl) ⟨1663037, by rfl⟩ : syracuseStep 2217383 = 3326075) B3326075
theorem B2494561 : Blo 2215435 2494561 := bbase (se 2 (by rfl) ⟨935460, by rfl⟩ : syracuseStep 2494561 = 1870921) (by norm_num)
theorem B3326081 : Blo 2215435 3326081 := bstep (se 2 (by rfl) ⟨1247280, by rfl⟩ : syracuseStep 3326081 = 2494561) B2494561
theorem B2217387 : Blo 2215435 2217387 := bstep (se 1 (by rfl) ⟨1663040, by rfl⟩ : syracuseStep 2217387 = 3326081) B3326081
theorem B5612773 : Blo 2215435 5612773 := bbase (se 4 (by rfl) ⟨526197, by rfl⟩ : syracuseStep 5612773 = 1052395) (by norm_num)
theorem B7483697 : Blo 2215435 7483697 := bstep (se 2 (by rfl) ⟨2806386, by rfl⟩ : syracuseStep 7483697 = 5612773) B5612773
theorem B4989131 : Blo 2215435 4989131 := bstep (se 1 (by rfl) ⟨3741848, by rfl⟩ : syracuseStep 4989131 = 7483697) B7483697
theorem B3326087 : Blo 2215435 3326087 := bstep (se 1 (by rfl) ⟨2494565, by rfl⟩ : syracuseStep 3326087 = 4989131) B4989131
theorem B2217391 : Blo 2215435 2217391 := bstep (se 1 (by rfl) ⟨1663043, by rfl⟩ : syracuseStep 2217391 = 3326087) B3326087
theorem B3326093 : Blo 2215435 3326093 := bbase (se 3 (by rfl) ⟨623642, by rfl⟩ : syracuseStep 3326093 = 1247285) (by norm_num)
theorem B2217395 : Blo 2215435 2217395 := bstep (se 1 (by rfl) ⟨1663046, by rfl⟩ : syracuseStep 2217395 = 3326093) B3326093
theorem B4989149 : Blo 2215435 4989149 := bbase (se 3 (by rfl) ⟨935465, by rfl⟩ : syracuseStep 4989149 = 1870931) (by norm_num)
theorem B3326099 : Blo 2215435 3326099 := bstep (se 1 (by rfl) ⟨2494574, by rfl⟩ : syracuseStep 3326099 = 4989149) B4989149
theorem B2217399 : Blo 2215435 2217399 := bstep (se 1 (by rfl) ⟨1663049, by rfl⟩ : syracuseStep 2217399 = 3326099) B3326099
theorem B3741869 : Blo 2215435 3741869 := bbase (se 3 (by rfl) ⟨701600, by rfl⟩ : syracuseStep 3741869 = 1403201) (by norm_num)
theorem B2494579 : Blo 2215435 2494579 := bstep (se 1 (by rfl) ⟨1870934, by rfl⟩ : syracuseStep 2494579 = 3741869) B3741869
theorem B3326105 : Blo 2215435 3326105 := bstep (se 2 (by rfl) ⟨1247289, by rfl⟩ : syracuseStep 3326105 = 2494579) B2494579
theorem B2217403 : Blo 2215435 2217403 := bstep (se 1 (by rfl) ⟨1663052, by rfl⟩ : syracuseStep 2217403 = 3326105) B3326105
theorem B2247661 : Blo 2215435 2247661 := bbase (se 3 (by rfl) ⟨421436, by rfl⟩ : syracuseStep 2247661 = 842873) (by norm_num)
theorem B2996881 : Blo 2215435 2996881 := bstep (se 2 (by rfl) ⟨1123830, by rfl⟩ : syracuseStep 2996881 = 2247661) B2247661
theorem B63933461 : Blo 2215435 63933461 := bstep (se 6 (by rfl) ⟨1498440, by rfl⟩ : syracuseStep 63933461 = 2996881) B2996881
theorem B42622307 : Blo 2215435 42622307 := bstep (se 1 (by rfl) ⟨31966730, by rfl⟩ : syracuseStep 42622307 = 63933461) B63933461
theorem B28414871 : Blo 2215435 28414871 := bstep (se 1 (by rfl) ⟨21311153, by rfl⟩ : syracuseStep 28414871 = 42622307) B42622307
theorem B18943247 : Blo 2215435 18943247 := bstep (se 1 (by rfl) ⟨14207435, by rfl⟩ : syracuseStep 18943247 = 28414871) B28414871
theorem B12628831 : Blo 2215435 12628831 := bstep (se 1 (by rfl) ⟨9471623, by rfl⟩ : syracuseStep 12628831 = 18943247) B18943247
theorem B16838441 : Blo 2215435 16838441 := bstep (se 2 (by rfl) ⟨6314415, by rfl⟩ : syracuseStep 16838441 = 12628831) B12628831
theorem B11225627 : Blo 2215435 11225627 := bstep (se 1 (by rfl) ⟨8419220, by rfl⟩ : syracuseStep 11225627 = 16838441) B16838441
theorem B7483751 : Blo 2215435 7483751 := bstep (se 1 (by rfl) ⟨5612813, by rfl⟩ : syracuseStep 7483751 = 11225627) B11225627
theorem B4989167 : Blo 2215435 4989167 := bstep (se 1 (by rfl) ⟨3741875, by rfl⟩ : syracuseStep 4989167 = 7483751) B7483751
theorem B3326111 : Blo 2215435 3326111 := bstep (se 1 (by rfl) ⟨2494583, by rfl⟩ : syracuseStep 3326111 = 4989167) B4989167
theorem B2217407 : Blo 2215435 2217407 := bstep (se 1 (by rfl) ⟨1663055, by rfl⟩ : syracuseStep 2217407 = 3326111) B3326111
theorem B3326117 : Blo 2215435 3326117 := bbase (se 4 (by rfl) ⟨311823, by rfl⟩ : syracuseStep 3326117 = 623647) (by norm_num)
theorem B2217411 : Blo 2215435 2217411 := bstep (se 1 (by rfl) ⟨1663058, by rfl⟩ : syracuseStep 2217411 = 3326117) B3326117
theorem B2806417 : Blo 2215435 2806417 := bbase (se 2 (by rfl) ⟨1052406, by rfl⟩ : syracuseStep 2806417 = 2104813) (by norm_num)
theorem B3741889 : Blo 2215435 3741889 := bstep (se 2 (by rfl) ⟨1403208, by rfl⟩ : syracuseStep 3741889 = 2806417) B2806417
theorem B4989185 : Blo 2215435 4989185 := bstep (se 2 (by rfl) ⟨1870944, by rfl⟩ : syracuseStep 4989185 = 3741889) B3741889
theorem B3326123 : Blo 2215435 3326123 := bstep (se 1 (by rfl) ⟨2494592, by rfl⟩ : syracuseStep 3326123 = 4989185) B4989185
theorem B2217415 : Blo 2215435 2217415 := bstep (se 1 (by rfl) ⟨1663061, by rfl⟩ : syracuseStep 2217415 = 3326123) B3326123
theorem B2494597 : Blo 2215435 2494597 := bbase (se 4 (by rfl) ⟨233868, by rfl⟩ : syracuseStep 2494597 = 467737) (by norm_num)
theorem B3326129 : Blo 2215435 3326129 := bstep (se 2 (by rfl) ⟨1247298, by rfl⟩ : syracuseStep 3326129 = 2494597) B2494597
theorem B2217419 : Blo 2215435 2217419 := bstep (se 1 (by rfl) ⟨1663064, by rfl⟩ : syracuseStep 2217419 = 3326129) B3326129
theorem B4050389 : Blo 2215435 4050389 := bbase (se 7 (by rfl) ⟨47465, by rfl⟩ : syracuseStep 4050389 = 94931) (by norm_num)
theorem B10801037 : Blo 2215435 10801037 := bstep (se 3 (by rfl) ⟨2025194, by rfl⟩ : syracuseStep 10801037 = 4050389) B4050389
theorem B28802765 : Blo 2215435 28802765 := bstep (se 3 (by rfl) ⟨5400518, by rfl⟩ : syracuseStep 28802765 = 10801037) B10801037
theorem B19201843 : Blo 2215435 19201843 := bstep (se 1 (by rfl) ⟨14401382, by rfl⟩ : syracuseStep 19201843 = 28802765) B28802765
theorem B102409829 : Blo 2215435 102409829 := bstep (se 4 (by rfl) ⟨9600921, by rfl⟩ : syracuseStep 102409829 = 19201843) B19201843
theorem B68273219 : Blo 2215435 68273219 := bstep (se 1 (by rfl) ⟨51204914, by rfl⟩ : syracuseStep 68273219 = 102409829) B102409829
theorem B45515479 : Blo 2215435 45515479 := bstep (se 1 (by rfl) ⟨34136609, by rfl⟩ : syracuseStep 45515479 = 68273219) B68273219
theorem B60687305 : Blo 2215435 60687305 := bstep (se 2 (by rfl) ⟨22757739, by rfl⟩ : syracuseStep 60687305 = 45515479) B45515479
theorem B40458203 : Blo 2215435 40458203 := bstep (se 1 (by rfl) ⟨30343652, by rfl⟩ : syracuseStep 40458203 = 60687305) B60687305
theorem B26972135 : Blo 2215435 26972135 := bstep (se 1 (by rfl) ⟨20229101, by rfl⟩ : syracuseStep 26972135 = 40458203) B40458203
theorem B17981423 : Blo 2215435 17981423 := bstep (se 1 (by rfl) ⟨13486067, by rfl⟩ : syracuseStep 17981423 = 26972135) B26972135
theorem B11987615 : Blo 2215435 11987615 := bstep (se 1 (by rfl) ⟨8990711, by rfl⟩ : syracuseStep 11987615 = 17981423) B17981423
theorem B7991743 : Blo 2215435 7991743 := bstep (se 1 (by rfl) ⟨5993807, by rfl⟩ : syracuseStep 7991743 = 11987615) B11987615
theorem B10655657 : Blo 2215435 10655657 := bstep (se 2 (by rfl) ⟨3995871, by rfl⟩ : syracuseStep 10655657 = 7991743) B7991743
theorem B7103771 : Blo 2215435 7103771 := bstep (se 1 (by rfl) ⟨5327828, by rfl⟩ : syracuseStep 7103771 = 10655657) B10655657
theorem B4735847 : Blo 2215435 4735847 := bstep (se 1 (by rfl) ⟨3551885, by rfl⟩ : syracuseStep 4735847 = 7103771) B7103771
theorem B3157231 : Blo 2215435 3157231 := bstep (se 1 (by rfl) ⟨2367923, by rfl⟩ : syracuseStep 3157231 = 4735847) B4735847
theorem B4209641 : Blo 2215435 4209641 := bstep (se 2 (by rfl) ⟨1578615, by rfl⟩ : syracuseStep 4209641 = 3157231) B3157231
theorem B2806427 : Blo 2215435 2806427 := bstep (se 1 (by rfl) ⟨2104820, by rfl⟩ : syracuseStep 2806427 = 4209641) B4209641
theorem B7483805 : Blo 2215435 7483805 := bstep (se 3 (by rfl) ⟨1403213, by rfl⟩ : syracuseStep 7483805 = 2806427) B2806427
theorem B4989203 : Blo 2215435 4989203 := bstep (se 1 (by rfl) ⟨3741902, by rfl⟩ : syracuseStep 4989203 = 7483805) B7483805
theorem B3326135 : Blo 2215435 3326135 := bstep (se 1 (by rfl) ⟨2494601, by rfl⟩ : syracuseStep 3326135 = 4989203) B4989203
theorem B2217423 : Blo 2215435 2217423 := bstep (se 1 (by rfl) ⟨1663067, by rfl⟩ : syracuseStep 2217423 = 3326135) B3326135
theorem B3326141 : Blo 2215435 3326141 := bbase (se 3 (by rfl) ⟨623651, by rfl⟩ : syracuseStep 3326141 = 1247303) (by norm_num)
theorem B2217427 : Blo 2215435 2217427 := bstep (se 1 (by rfl) ⟨1663070, by rfl⟩ : syracuseStep 2217427 = 3326141) B3326141
theorem B4989221 : Blo 2215435 4989221 := bbase (se 4 (by rfl) ⟨467739, by rfl⟩ : syracuseStep 4989221 = 935479) (by norm_num)
theorem B3326147 : Blo 2215435 3326147 := bstep (se 1 (by rfl) ⟨2494610, by rfl⟩ : syracuseStep 3326147 = 4989221) B4989221
theorem B2217431 : Blo 2215435 2217431 := bstep (se 1 (by rfl) ⟨1663073, by rfl⟩ : syracuseStep 2217431 = 3326147) B3326147
theorem B5612885 : Blo 2215435 5612885 := bbase (se 12 (by rfl) ⟨2055, by rfl⟩ : syracuseStep 5612885 = 4111) (by norm_num)
theorem B3741923 : Blo 2215435 3741923 := bstep (se 1 (by rfl) ⟨2806442, by rfl⟩ : syracuseStep 3741923 = 5612885) B5612885
theorem B2494615 : Blo 2215435 2494615 := bstep (se 1 (by rfl) ⟨1870961, by rfl⟩ : syracuseStep 2494615 = 3741923) B3741923
theorem B3326153 : Blo 2215435 3326153 := bstep (se 2 (by rfl) ⟨1247307, by rfl⟩ : syracuseStep 3326153 = 2494615) B2494615
theorem B2217435 : Blo 2215435 2217435 := bstep (se 1 (by rfl) ⟨1663076, by rfl⟩ : syracuseStep 2217435 = 3326153) B3326153
theorem C0 (j : ℕ) (h1 : 553858 ≤ j) (h2 : j ≤ 554358) : Blo 2215435 (4 * j + 3) := by
  interval_cases j
  · exact B2215435
  · exact B2215439
  · exact B2215443
  · exact B2215447
  · exact B2215451
  · exact B2215455
  · exact B2215459
  · exact B2215463
  · exact B2215467
  · exact B2215471
  · exact B2215475
  · exact B2215479
  · exact B2215483
  · exact B2215487
  · exact B2215491
  · exact B2215495
  · exact B2215499
  · exact B2215503
  · exact B2215507
  · exact B2215511
  · exact B2215515
  · exact B2215519
  · exact B2215523
  · exact B2215527
  · exact B2215531
  · exact B2215535
  · exact B2215539
  · exact B2215543
  · exact B2215547
  · exact B2215551
  · exact B2215555
  · exact B2215559
  · exact B2215563
  · exact B2215567
  · exact B2215571
  · exact B2215575
  · exact B2215579
  · exact B2215583
  · exact B2215587
  · exact B2215591
  · exact B2215595
  · exact B2215599
  · exact B2215603
  · exact B2215607
  · exact B2215611
  · exact B2215615
  · exact B2215619
  · exact B2215623
  · exact B2215627
  · exact B2215631
  · exact B2215635
  · exact B2215639
  · exact B2215643
  · exact B2215647
  · exact B2215651
  · exact B2215655
  · exact B2215659
  · exact B2215663
  · exact B2215667
  · exact B2215671
  · exact B2215675
  · exact B2215679
  · exact B2215683
  · exact B2215687
  · exact B2215691
  · exact B2215695
  · exact B2215699
  · exact B2215703
  · exact B2215707
  · exact B2215711
  · exact B2215715
  · exact B2215719
  · exact B2215723
  · exact B2215727
  · exact B2215731
  · exact B2215735
  · exact B2215739
  · exact B2215743
  · exact B2215747
  · exact B2215751
  · exact B2215755
  · exact B2215759
  · exact B2215763
  · exact B2215767
  · exact B2215771
  · exact B2215775
  · exact B2215779
  · exact B2215783
  · exact B2215787
  · exact B2215791
  · exact B2215795
  · exact B2215799
  · exact B2215803
  · exact B2215807
  · exact B2215811
  · exact B2215815
  · exact B2215819
  · exact B2215823
  · exact B2215827
  · exact B2215831
  · exact B2215835
  · exact B2215839
  · exact B2215843
  · exact B2215847
  · exact B2215851
  · exact B2215855
  · exact B2215859
  · exact B2215863
  · exact B2215867
  · exact B2215871
  · exact B2215875
  · exact B2215879
  · exact B2215883
  · exact B2215887
  · exact B2215891
  · exact B2215895
  · exact B2215899
  · exact B2215903
  · exact B2215907
  · exact B2215911
  · exact B2215915
  · exact B2215919
  · exact B2215923
  · exact B2215927
  · exact B2215931
  · exact B2215935
  · exact B2215939
  · exact B2215943
  · exact B2215947
  · exact B2215951
  · exact B2215955
  · exact B2215959
  · exact B2215963
  · exact B2215967
  · exact B2215971
  · exact B2215975
  · exact B2215979
  · exact B2215983
  · exact B2215987
  · exact B2215991
  · exact B2215995
  · exact B2215999
  · exact B2216003
  · exact B2216007
  · exact B2216011
  · exact B2216015
  · exact B2216019
  · exact B2216023
  · exact B2216027
  · exact B2216031
  · exact B2216035
  · exact B2216039
  · exact B2216043
  · exact B2216047
  · exact B2216051
  · exact B2216055
  · exact B2216059
  · exact B2216063
  · exact B2216067
  · exact B2216071
  · exact B2216075
  · exact B2216079
  · exact B2216083
  · exact B2216087
  · exact B2216091
  · exact B2216095
  · exact B2216099
  · exact B2216103
  · exact B2216107
  · exact B2216111
  · exact B2216115
  · exact B2216119
  · exact B2216123
  · exact B2216127
  · exact B2216131
  · exact B2216135
  · exact B2216139
  · exact B2216143
  · exact B2216147
  · exact B2216151
  · exact B2216155
  · exact B2216159
  · exact B2216163
  · exact B2216167
  · exact B2216171
  · exact B2216175
  · exact B2216179
  · exact B2216183
  · exact B2216187
  · exact B2216191
  · exact B2216195
  · exact B2216199
  · exact B2216203
  · exact B2216207
  · exact B2216211
  · exact B2216215
  · exact B2216219
  · exact B2216223
  · exact B2216227
  · exact B2216231
  · exact B2216235
  · exact B2216239
  · exact B2216243
  · exact B2216247
  · exact B2216251
  · exact B2216255
  · exact B2216259
  · exact B2216263
  · exact B2216267
  · exact B2216271
  · exact B2216275
  · exact B2216279
  · exact B2216283
  · exact B2216287
  · exact B2216291
  · exact B2216295
  · exact B2216299
  · exact B2216303
  · exact B2216307
  · exact B2216311
  · exact B2216315
  · exact B2216319
  · exact B2216323
  · exact B2216327
  · exact B2216331
  · exact B2216335
  · exact B2216339
  · exact B2216343
  · exact B2216347
  · exact B2216351
  · exact B2216355
  · exact B2216359
  · exact B2216363
  · exact B2216367
  · exact B2216371
  · exact B2216375
  · exact B2216379
  · exact B2216383
  · exact B2216387
  · exact B2216391
  · exact B2216395
  · exact B2216399
  · exact B2216403
  · exact B2216407
  · exact B2216411
  · exact B2216415
  · exact B2216419
  · exact B2216423
  · exact B2216427
  · exact B2216431
  · exact B2216435
  · exact B2216439
  · exact B2216443
  · exact B2216447
  · exact B2216451
  · exact B2216455
  · exact B2216459
  · exact B2216463
  · exact B2216467
  · exact B2216471
  · exact B2216475
  · exact B2216479
  · exact B2216483
  · exact B2216487
  · exact B2216491
  · exact B2216495
  · exact B2216499
  · exact B2216503
  · exact B2216507
  · exact B2216511
  · exact B2216515
  · exact B2216519
  · exact B2216523
  · exact B2216527
  · exact B2216531
  · exact B2216535
  · exact B2216539
  · exact B2216543
  · exact B2216547
  · exact B2216551
  · exact B2216555
  · exact B2216559
  · exact B2216563
  · exact B2216567
  · exact B2216571
  · exact B2216575
  · exact B2216579
  · exact B2216583
  · exact B2216587
  · exact B2216591
  · exact B2216595
  · exact B2216599
  · exact B2216603
  · exact B2216607
  · exact B2216611
  · exact B2216615
  · exact B2216619
  · exact B2216623
  · exact B2216627
  · exact B2216631
  · exact B2216635
  · exact B2216639
  · exact B2216643
  · exact B2216647
  · exact B2216651
  · exact B2216655
  · exact B2216659
  · exact B2216663
  · exact B2216667
  · exact B2216671
  · exact B2216675
  · exact B2216679
  · exact B2216683
  · exact B2216687
  · exact B2216691
  · exact B2216695
  · exact B2216699
  · exact B2216703
  · exact B2216707
  · exact B2216711
  · exact B2216715
  · exact B2216719
  · exact B2216723
  · exact B2216727
  · exact B2216731
  · exact B2216735
  · exact B2216739
  · exact B2216743
  · exact B2216747
  · exact B2216751
  · exact B2216755
  · exact B2216759
  · exact B2216763
  · exact B2216767
  · exact B2216771
  · exact B2216775
  · exact B2216779
  · exact B2216783
  · exact B2216787
  · exact B2216791
  · exact B2216795
  · exact B2216799
  · exact B2216803
  · exact B2216807
  · exact B2216811
  · exact B2216815
  · exact B2216819
  · exact B2216823
  · exact B2216827
  · exact B2216831
  · exact B2216835
  · exact B2216839
  · exact B2216843
  · exact B2216847
  · exact B2216851
  · exact B2216855
  · exact B2216859
  · exact B2216863
  · exact B2216867
  · exact B2216871
  · exact B2216875
  · exact B2216879
  · exact B2216883
  · exact B2216887
  · exact B2216891
  · exact B2216895
  · exact B2216899
  · exact B2216903
  · exact B2216907
  · exact B2216911
  · exact B2216915
  · exact B2216919
  · exact B2216923
  · exact B2216927
  · exact B2216931
  · exact B2216935
  · exact B2216939
  · exact B2216943
  · exact B2216947
  · exact B2216951
  · exact B2216955
  · exact B2216959
  · exact B2216963
  · exact B2216967
  · exact B2216971
  · exact B2216975
  · exact B2216979
  · exact B2216983
  · exact B2216987
  · exact B2216991
  · exact B2216995
  · exact B2216999
  · exact B2217003
  · exact B2217007
  · exact B2217011
  · exact B2217015
  · exact B2217019
  · exact B2217023
  · exact B2217027
  · exact B2217031
  · exact B2217035
  · exact B2217039
  · exact B2217043
  · exact B2217047
  · exact B2217051
  · exact B2217055
  · exact B2217059
  · exact B2217063
  · exact B2217067
  · exact B2217071
  · exact B2217075
  · exact B2217079
  · exact B2217083
  · exact B2217087
  · exact B2217091
  · exact B2217095
  · exact B2217099
  · exact B2217103
  · exact B2217107
  · exact B2217111
  · exact B2217115
  · exact B2217119
  · exact B2217123
  · exact B2217127
  · exact B2217131
  · exact B2217135
  · exact B2217139
  · exact B2217143
  · exact B2217147
  · exact B2217151
  · exact B2217155
  · exact B2217159
  · exact B2217163
  · exact B2217167
  · exact B2217171
  · exact B2217175
  · exact B2217179
  · exact B2217183
  · exact B2217187
  · exact B2217191
  · exact B2217195
  · exact B2217199
  · exact B2217203
  · exact B2217207
  · exact B2217211
  · exact B2217215
  · exact B2217219
  · exact B2217223
  · exact B2217227
  · exact B2217231
  · exact B2217235
  · exact B2217239
  · exact B2217243
  · exact B2217247
  · exact B2217251
  · exact B2217255
  · exact B2217259
  · exact B2217263
  · exact B2217267
  · exact B2217271
  · exact B2217275
  · exact B2217279
  · exact B2217283
  · exact B2217287
  · exact B2217291
  · exact B2217295
  · exact B2217299
  · exact B2217303
  · exact B2217307
  · exact B2217311
  · exact B2217315
  · exact B2217319
  · exact B2217323
  · exact B2217327
  · exact B2217331
  · exact B2217335
  · exact B2217339
  · exact B2217343
  · exact B2217347
  · exact B2217351
  · exact B2217355
  · exact B2217359
  · exact B2217363
  · exact B2217367
  · exact B2217371
  · exact B2217375
  · exact B2217379
  · exact B2217383
  · exact B2217387
  · exact B2217391
  · exact B2217395
  · exact B2217399
  · exact B2217403
  · exact B2217407
  · exact B2217411
  · exact B2217415
  · exact B2217419
  · exact B2217423
  · exact B2217427
  · exact B2217431
  · exact B2217435
theorem solution (m : ℕ) (hlo : 2215435 ≤ m) (hhi : m ≤ 2217435) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 553858 ≤ j := by omega
    have hj2 : j ≤ 554358 := by omega
    have hb : Blo 2215435 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
