-- Prove2me | solution 1 for syracuse_descends_range_2293435_2295435
-- status  : ACCEPTED   (prove)
-- author  : @chstdu
-- created : 2026-09-23T17:49:51.621703+00:00
-- url     : https://prove2.me/submissions/ea1261fc-b0d1-431a-a9d5-72269a04a8de

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

theorem B3870173 : Blo 2293435 3870173 := bbase (se 3 (by rfl) ⟨725657, by rfl⟩ : syracuseStep 3870173 = 1451315) (by norm_num)
theorem B2580115 : Blo 2293435 2580115 := bstep (se 1 (by rfl) ⟨1935086, by rfl⟩ : syracuseStep 2580115 = 3870173) B3870173
theorem B3440153 : Blo 2293435 3440153 := bstep (se 2 (by rfl) ⟨1290057, by rfl⟩ : syracuseStep 3440153 = 2580115) B2580115
theorem B2293435 : Blo 2293435 2293435 := bstep (se 1 (by rfl) ⟨1720076, by rfl⟩ : syracuseStep 2293435 = 3440153) B3440153
theorem B5447669 : Blo 2293435 5447669 := bbase (se 5 (by rfl) ⟨255359, by rfl⟩ : syracuseStep 5447669 = 510719) (by norm_num)
theorem B14527117 : Blo 2293435 14527117 := bstep (se 3 (by rfl) ⟨2723834, by rfl⟩ : syracuseStep 14527117 = 5447669) B5447669
theorem B77477957 : Blo 2293435 77477957 := bstep (se 4 (by rfl) ⟨7263558, by rfl⟩ : syracuseStep 77477957 = 14527117) B14527117
theorem B51651971 : Blo 2293435 51651971 := bstep (se 1 (by rfl) ⟨38738978, by rfl⟩ : syracuseStep 51651971 = 77477957) B77477957
theorem B34434647 : Blo 2293435 34434647 := bstep (se 1 (by rfl) ⟨25825985, by rfl⟩ : syracuseStep 34434647 = 51651971) B51651971
theorem B22956431 : Blo 2293435 22956431 := bstep (se 1 (by rfl) ⟨17217323, by rfl⟩ : syracuseStep 22956431 = 34434647) B34434647
theorem B61217149 : Blo 2293435 61217149 := bstep (se 3 (by rfl) ⟨11478215, by rfl⟩ : syracuseStep 61217149 = 22956431) B22956431
theorem B81622865 : Blo 2293435 81622865 := bstep (se 2 (by rfl) ⟨30608574, by rfl⟩ : syracuseStep 81622865 = 61217149) B61217149
theorem B54415243 : Blo 2293435 54415243 := bstep (se 1 (by rfl) ⟨40811432, by rfl⟩ : syracuseStep 54415243 = 81622865) B81622865
theorem B72553657 : Blo 2293435 72553657 := bstep (se 2 (by rfl) ⟨27207621, by rfl⟩ : syracuseStep 72553657 = 54415243) B54415243
theorem B96738209 : Blo 2293435 96738209 := bstep (se 2 (by rfl) ⟨36276828, by rfl⟩ : syracuseStep 96738209 = 72553657) B72553657
theorem B64492139 : Blo 2293435 64492139 := bstep (se 1 (by rfl) ⟨48369104, by rfl⟩ : syracuseStep 64492139 = 96738209) B96738209
theorem B171979037 : Blo 2293435 171979037 := bstep (se 3 (by rfl) ⟨32246069, by rfl⟩ : syracuseStep 171979037 = 64492139) B64492139
theorem B114652691 : Blo 2293435 114652691 := bstep (se 1 (by rfl) ⟨85989518, by rfl⟩ : syracuseStep 114652691 = 171979037) B171979037
theorem B76435127 : Blo 2293435 76435127 := bstep (se 1 (by rfl) ⟨57326345, by rfl⟩ : syracuseStep 76435127 = 114652691) B114652691
theorem B50956751 : Blo 2293435 50956751 := bstep (se 1 (by rfl) ⟨38217563, by rfl⟩ : syracuseStep 50956751 = 76435127) B76435127
theorem B33971167 : Blo 2293435 33971167 := bstep (se 1 (by rfl) ⟨25478375, by rfl⟩ : syracuseStep 33971167 = 50956751) B50956751
theorem B45294889 : Blo 2293435 45294889 := bstep (se 2 (by rfl) ⟨16985583, by rfl⟩ : syracuseStep 45294889 = 33971167) B33971167
theorem B60393185 : Blo 2293435 60393185 := bstep (se 2 (by rfl) ⟨22647444, by rfl⟩ : syracuseStep 60393185 = 45294889) B45294889
theorem B40262123 : Blo 2293435 40262123 := bstep (se 1 (by rfl) ⟨30196592, by rfl⟩ : syracuseStep 40262123 = 60393185) B60393185
theorem B107365661 : Blo 2293435 107365661 := bstep (se 3 (by rfl) ⟨20131061, by rfl⟩ : syracuseStep 107365661 = 40262123) B40262123
theorem B71577107 : Blo 2293435 71577107 := bstep (se 1 (by rfl) ⟨53682830, by rfl⟩ : syracuseStep 71577107 = 107365661) B107365661
theorem B47718071 : Blo 2293435 47718071 := bstep (se 1 (by rfl) ⟨35788553, by rfl⟩ : syracuseStep 47718071 = 71577107) B71577107
theorem B31812047 : Blo 2293435 31812047 := bstep (se 1 (by rfl) ⟨23859035, by rfl⟩ : syracuseStep 31812047 = 47718071) B47718071
theorem B21208031 : Blo 2293435 21208031 := bstep (se 1 (by rfl) ⟨15906023, by rfl⟩ : syracuseStep 21208031 = 31812047) B31812047
theorem B14138687 : Blo 2293435 14138687 := bstep (se 1 (by rfl) ⟨10604015, by rfl⟩ : syracuseStep 14138687 = 21208031) B21208031
theorem B9425791 : Blo 2293435 9425791 := bstep (se 1 (by rfl) ⟨7069343, by rfl⟩ : syracuseStep 9425791 = 14138687) B14138687
theorem B12567721 : Blo 2293435 12567721 := bstep (se 2 (by rfl) ⟨4712895, by rfl⟩ : syracuseStep 12567721 = 9425791) B9425791
theorem B16756961 : Blo 2293435 16756961 := bstep (se 2 (by rfl) ⟨6283860, by rfl⟩ : syracuseStep 16756961 = 12567721) B12567721
theorem B44685229 : Blo 2293435 44685229 := bstep (se 3 (by rfl) ⟨8378480, by rfl⟩ : syracuseStep 44685229 = 16756961) B16756961
theorem B59580305 : Blo 2293435 59580305 := bstep (se 2 (by rfl) ⟨22342614, by rfl⟩ : syracuseStep 59580305 = 44685229) B44685229
theorem B39720203 : Blo 2293435 39720203 := bstep (se 1 (by rfl) ⟨29790152, by rfl⟩ : syracuseStep 39720203 = 59580305) B59580305
theorem B26480135 : Blo 2293435 26480135 := bstep (se 1 (by rfl) ⟨19860101, by rfl⟩ : syracuseStep 26480135 = 39720203) B39720203
theorem B17653423 : Blo 2293435 17653423 := bstep (se 1 (by rfl) ⟨13240067, by rfl⟩ : syracuseStep 17653423 = 26480135) B26480135
theorem B23537897 : Blo 2293435 23537897 := bstep (se 2 (by rfl) ⟨8826711, by rfl⟩ : syracuseStep 23537897 = 17653423) B17653423
theorem B15691931 : Blo 2293435 15691931 := bstep (se 1 (by rfl) ⟨11768948, by rfl⟩ : syracuseStep 15691931 = 23537897) B23537897
theorem B10461287 : Blo 2293435 10461287 := bstep (se 1 (by rfl) ⟨7845965, by rfl⟩ : syracuseStep 10461287 = 15691931) B15691931
theorem B6974191 : Blo 2293435 6974191 := bstep (se 1 (by rfl) ⟨5230643, by rfl⟩ : syracuseStep 6974191 = 10461287) B10461287
theorem B37195685 : Blo 2293435 37195685 := bstep (se 4 (by rfl) ⟨3487095, by rfl⟩ : syracuseStep 37195685 = 6974191) B6974191
theorem B24797123 : Blo 2293435 24797123 := bstep (se 1 (by rfl) ⟨18597842, by rfl⟩ : syracuseStep 24797123 = 37195685) B37195685
theorem B16531415 : Blo 2293435 16531415 := bstep (se 1 (by rfl) ⟨12398561, by rfl⟩ : syracuseStep 16531415 = 24797123) B24797123
theorem B11020943 : Blo 2293435 11020943 := bstep (se 1 (by rfl) ⟨8265707, by rfl⟩ : syracuseStep 11020943 = 16531415) B16531415
theorem B7347295 : Blo 2293435 7347295 := bstep (se 1 (by rfl) ⟨5510471, by rfl⟩ : syracuseStep 7347295 = 11020943) B11020943
theorem B9796393 : Blo 2293435 9796393 := bstep (se 2 (by rfl) ⟨3673647, by rfl⟩ : syracuseStep 9796393 = 7347295) B7347295
theorem B13061857 : Blo 2293435 13061857 := bstep (se 2 (by rfl) ⟨4898196, by rfl⟩ : syracuseStep 13061857 = 9796393) B9796393
theorem B17415809 : Blo 2293435 17415809 := bstep (se 2 (by rfl) ⟨6530928, by rfl⟩ : syracuseStep 17415809 = 13061857) B13061857
theorem B11610539 : Blo 2293435 11610539 := bstep (se 1 (by rfl) ⟨8707904, by rfl⟩ : syracuseStep 11610539 = 17415809) B17415809
theorem B7740359 : Blo 2293435 7740359 := bstep (se 1 (by rfl) ⟨5805269, by rfl⟩ : syracuseStep 7740359 = 11610539) B11610539
theorem B5160239 : Blo 2293435 5160239 := bstep (se 1 (by rfl) ⟨3870179, by rfl⟩ : syracuseStep 5160239 = 7740359) B7740359
theorem B3440159 : Blo 2293435 3440159 := bstep (se 1 (by rfl) ⟨2580119, by rfl⟩ : syracuseStep 3440159 = 5160239) B5160239
theorem B2293439 : Blo 2293435 2293439 := bstep (se 1 (by rfl) ⟨1720079, by rfl⟩ : syracuseStep 2293439 = 3440159) B3440159
theorem B3440165 : Blo 2293435 3440165 := bbase (se 4 (by rfl) ⟨322515, by rfl⟩ : syracuseStep 3440165 = 645031) (by norm_num)
theorem B2293443 : Blo 2293435 2293443 := bstep (se 1 (by rfl) ⟨1720082, by rfl⟩ : syracuseStep 2293443 = 3440165) B3440165
theorem B2902645 : Blo 2293435 2902645 := bbase (se 5 (by rfl) ⟨136061, by rfl⟩ : syracuseStep 2902645 = 272123) (by norm_num)
theorem B3870193 : Blo 2293435 3870193 := bstep (se 2 (by rfl) ⟨1451322, by rfl⟩ : syracuseStep 3870193 = 2902645) B2902645
theorem B5160257 : Blo 2293435 5160257 := bstep (se 2 (by rfl) ⟨1935096, by rfl⟩ : syracuseStep 5160257 = 3870193) B3870193
theorem B3440171 : Blo 2293435 3440171 := bstep (se 1 (by rfl) ⟨2580128, by rfl⟩ : syracuseStep 3440171 = 5160257) B5160257
theorem B2293447 : Blo 2293435 2293447 := bstep (se 1 (by rfl) ⟨1720085, by rfl⟩ : syracuseStep 2293447 = 3440171) B3440171
theorem B2580133 : Blo 2293435 2580133 := bbase (se 4 (by rfl) ⟨241887, by rfl⟩ : syracuseStep 2580133 = 483775) (by norm_num)
theorem B3440177 : Blo 2293435 3440177 := bstep (se 2 (by rfl) ⟨1290066, by rfl⟩ : syracuseStep 3440177 = 2580133) B2580133
theorem B2293451 : Blo 2293435 2293451 := bstep (se 1 (by rfl) ⟨1720088, by rfl⟩ : syracuseStep 2293451 = 3440177) B3440177
theorem B7846021 : Blo 2293435 7846021 := bbase (se 4 (by rfl) ⟨735564, by rfl⟩ : syracuseStep 7846021 = 1471129) (by norm_num)
theorem B10461361 : Blo 2293435 10461361 := bstep (se 2 (by rfl) ⟨3923010, by rfl⟩ : syracuseStep 10461361 = 7846021) B7846021
theorem B13948481 : Blo 2293435 13948481 := bstep (se 2 (by rfl) ⟨5230680, by rfl⟩ : syracuseStep 13948481 = 10461361) B10461361
theorem B37195949 : Blo 2293435 37195949 := bstep (se 3 (by rfl) ⟨6974240, by rfl⟩ : syracuseStep 37195949 = 13948481) B13948481
theorem B24797299 : Blo 2293435 24797299 := bstep (se 1 (by rfl) ⟨18597974, by rfl⟩ : syracuseStep 24797299 = 37195949) B37195949
theorem B33063065 : Blo 2293435 33063065 := bstep (se 2 (by rfl) ⟨12398649, by rfl⟩ : syracuseStep 33063065 = 24797299) B24797299
theorem B22042043 : Blo 2293435 22042043 := bstep (se 1 (by rfl) ⟨16531532, by rfl⟩ : syracuseStep 22042043 = 33063065) B33063065
theorem B14694695 : Blo 2293435 14694695 := bstep (se 1 (by rfl) ⟨11021021, by rfl⟩ : syracuseStep 14694695 = 22042043) B22042043
theorem B9796463 : Blo 2293435 9796463 := bstep (se 1 (by rfl) ⟨7347347, by rfl⟩ : syracuseStep 9796463 = 14694695) B14694695
theorem B6530975 : Blo 2293435 6530975 := bstep (se 1 (by rfl) ⟨4898231, by rfl⟩ : syracuseStep 6530975 = 9796463) B9796463
theorem B4353983 : Blo 2293435 4353983 := bstep (se 1 (by rfl) ⟨3265487, by rfl⟩ : syracuseStep 4353983 = 6530975) B6530975
theorem B2902655 : Blo 2293435 2902655 := bstep (se 1 (by rfl) ⟨2176991, by rfl⟩ : syracuseStep 2902655 = 4353983) B4353983
theorem B7740413 : Blo 2293435 7740413 := bstep (se 3 (by rfl) ⟨1451327, by rfl⟩ : syracuseStep 7740413 = 2902655) B2902655
theorem B5160275 : Blo 2293435 5160275 := bstep (se 1 (by rfl) ⟨3870206, by rfl⟩ : syracuseStep 5160275 = 7740413) B7740413
theorem B3440183 : Blo 2293435 3440183 := bstep (se 1 (by rfl) ⟨2580137, by rfl⟩ : syracuseStep 3440183 = 5160275) B5160275
theorem B2293455 : Blo 2293435 2293455 := bstep (se 1 (by rfl) ⟨1720091, by rfl⟩ : syracuseStep 2293455 = 3440183) B3440183
theorem B3440189 : Blo 2293435 3440189 := bbase (se 3 (by rfl) ⟨645035, by rfl⟩ : syracuseStep 3440189 = 1290071) (by norm_num)
theorem B2293459 : Blo 2293435 2293459 := bstep (se 1 (by rfl) ⟨1720094, by rfl⟩ : syracuseStep 2293459 = 3440189) B3440189
theorem B5160293 : Blo 2293435 5160293 := bbase (se 4 (by rfl) ⟨483777, by rfl⟩ : syracuseStep 5160293 = 967555) (by norm_num)
theorem B3440195 : Blo 2293435 3440195 := bstep (se 1 (by rfl) ⟨2580146, by rfl⟩ : syracuseStep 3440195 = 5160293) B5160293
theorem B2293463 : Blo 2293435 2293463 := bstep (se 1 (by rfl) ⟨1720097, by rfl⟩ : syracuseStep 2293463 = 3440195) B3440195
theorem B5805341 : Blo 2293435 5805341 := bbase (se 3 (by rfl) ⟨1088501, by rfl⟩ : syracuseStep 5805341 = 2177003) (by norm_num)
theorem B3870227 : Blo 2293435 3870227 := bstep (se 1 (by rfl) ⟨2902670, by rfl⟩ : syracuseStep 3870227 = 5805341) B5805341
theorem B2580151 : Blo 2293435 2580151 := bstep (se 1 (by rfl) ⟨1935113, by rfl⟩ : syracuseStep 2580151 = 3870227) B3870227
theorem B3440201 : Blo 2293435 3440201 := bstep (se 2 (by rfl) ⟨1290075, by rfl⟩ : syracuseStep 3440201 = 2580151) B2580151
theorem B2293467 : Blo 2293435 2293467 := bstep (se 1 (by rfl) ⟨1720100, by rfl⟩ : syracuseStep 2293467 = 3440201) B3440201
theorem B4354013 : Blo 2293435 4354013 := bbase (se 3 (by rfl) ⟨816377, by rfl⟩ : syracuseStep 4354013 = 1632755) (by norm_num)
theorem B11610701 : Blo 2293435 11610701 := bstep (se 3 (by rfl) ⟨2177006, by rfl⟩ : syracuseStep 11610701 = 4354013) B4354013
theorem B7740467 : Blo 2293435 7740467 := bstep (se 1 (by rfl) ⟨5805350, by rfl⟩ : syracuseStep 7740467 = 11610701) B11610701
theorem B5160311 : Blo 2293435 5160311 := bstep (se 1 (by rfl) ⟨3870233, by rfl⟩ : syracuseStep 5160311 = 7740467) B7740467
theorem B3440207 : Blo 2293435 3440207 := bstep (se 1 (by rfl) ⟨2580155, by rfl⟩ : syracuseStep 3440207 = 5160311) B5160311
theorem B2293471 : Blo 2293435 2293471 := bstep (se 1 (by rfl) ⟨1720103, by rfl⟩ : syracuseStep 2293471 = 3440207) B3440207
theorem B3440213 : Blo 2293435 3440213 := bbase (se 8 (by rfl) ⟨20157, by rfl⟩ : syracuseStep 3440213 = 40315) (by norm_num)
theorem B2293475 : Blo 2293435 2293475 := bstep (se 1 (by rfl) ⟨1720106, by rfl⟩ : syracuseStep 2293475 = 3440213) B3440213
theorem B9796565 : Blo 2293435 9796565 := bbase (se 7 (by rfl) ⟨114803, by rfl⟩ : syracuseStep 9796565 = 229607) (by norm_num)
theorem B6531043 : Blo 2293435 6531043 := bstep (se 1 (by rfl) ⟨4898282, by rfl⟩ : syracuseStep 6531043 = 9796565) B9796565
theorem B8708057 : Blo 2293435 8708057 := bstep (se 2 (by rfl) ⟨3265521, by rfl⟩ : syracuseStep 8708057 = 6531043) B6531043
theorem B5805371 : Blo 2293435 5805371 := bstep (se 1 (by rfl) ⟨4354028, by rfl⟩ : syracuseStep 5805371 = 8708057) B8708057
theorem B3870247 : Blo 2293435 3870247 := bstep (se 1 (by rfl) ⟨2902685, by rfl⟩ : syracuseStep 3870247 = 5805371) B5805371
theorem B5160329 : Blo 2293435 5160329 := bstep (se 2 (by rfl) ⟨1935123, by rfl⟩ : syracuseStep 5160329 = 3870247) B3870247
theorem B3440219 : Blo 2293435 3440219 := bstep (se 1 (by rfl) ⟨2580164, by rfl⟩ : syracuseStep 3440219 = 5160329) B5160329
theorem B2293479 : Blo 2293435 2293479 := bstep (se 1 (by rfl) ⟨1720109, by rfl⟩ : syracuseStep 2293479 = 3440219) B3440219
theorem B2580169 : Blo 2293435 2580169 := bbase (se 2 (by rfl) ⟨967563, by rfl⟩ : syracuseStep 2580169 = 1935127) (by norm_num)
theorem B3440225 : Blo 2293435 3440225 := bstep (se 2 (by rfl) ⟨1290084, by rfl⟩ : syracuseStep 3440225 = 2580169) B2580169
theorem B2293483 : Blo 2293435 2293483 := bstep (se 1 (by rfl) ⟨1720112, by rfl⟩ : syracuseStep 2293483 = 3440225) B3440225
theorem B2615377 : Blo 2293435 2615377 := bbase (se 2 (by rfl) ⟨980766, by rfl⟩ : syracuseStep 2615377 = 1961533) (by norm_num)
theorem B3487169 : Blo 2293435 3487169 := bstep (se 2 (by rfl) ⟨1307688, by rfl⟩ : syracuseStep 3487169 = 2615377) B2615377
theorem B9299117 : Blo 2293435 9299117 := bstep (se 3 (by rfl) ⟨1743584, by rfl⟩ : syracuseStep 9299117 = 3487169) B3487169
theorem B6199411 : Blo 2293435 6199411 := bstep (se 1 (by rfl) ⟨4649558, by rfl⟩ : syracuseStep 6199411 = 9299117) B9299117
theorem B8265881 : Blo 2293435 8265881 := bstep (se 2 (by rfl) ⟨3099705, by rfl⟩ : syracuseStep 8265881 = 6199411) B6199411
theorem B5510587 : Blo 2293435 5510587 := bstep (se 1 (by rfl) ⟨4132940, by rfl⟩ : syracuseStep 5510587 = 8265881) B8265881
theorem B7347449 : Blo 2293435 7347449 := bstep (se 2 (by rfl) ⟨2755293, by rfl⟩ : syracuseStep 7347449 = 5510587) B5510587
theorem B19593197 : Blo 2293435 19593197 := bstep (se 3 (by rfl) ⟨3673724, by rfl⟩ : syracuseStep 19593197 = 7347449) B7347449
theorem B13062131 : Blo 2293435 13062131 := bstep (se 1 (by rfl) ⟨9796598, by rfl⟩ : syracuseStep 13062131 = 19593197) B19593197
theorem B8708087 : Blo 2293435 8708087 := bstep (se 1 (by rfl) ⟨6531065, by rfl⟩ : syracuseStep 8708087 = 13062131) B13062131
theorem B5805391 : Blo 2293435 5805391 := bstep (se 1 (by rfl) ⟨4354043, by rfl⟩ : syracuseStep 5805391 = 8708087) B8708087
theorem B7740521 : Blo 2293435 7740521 := bstep (se 2 (by rfl) ⟨2902695, by rfl⟩ : syracuseStep 7740521 = 5805391) B5805391
theorem B5160347 : Blo 2293435 5160347 := bstep (se 1 (by rfl) ⟨3870260, by rfl⟩ : syracuseStep 5160347 = 7740521) B7740521
theorem B3440231 : Blo 2293435 3440231 := bstep (se 1 (by rfl) ⟨2580173, by rfl⟩ : syracuseStep 3440231 = 5160347) B5160347
theorem B2293487 : Blo 2293435 2293487 := bstep (se 1 (by rfl) ⟨1720115, by rfl⟩ : syracuseStep 2293487 = 3440231) B3440231
theorem B3440237 : Blo 2293435 3440237 := bbase (se 3 (by rfl) ⟨645044, by rfl⟩ : syracuseStep 3440237 = 1290089) (by norm_num)
theorem B2293491 : Blo 2293435 2293491 := bstep (se 1 (by rfl) ⟨1720118, by rfl⟩ : syracuseStep 2293491 = 3440237) B3440237
theorem B5160365 : Blo 2293435 5160365 := bbase (se 3 (by rfl) ⟨967568, by rfl⟩ : syracuseStep 5160365 = 1935137) (by norm_num)
theorem B3440243 : Blo 2293435 3440243 := bstep (se 1 (by rfl) ⟨2580182, by rfl⟩ : syracuseStep 3440243 = 5160365) B5160365
theorem B2293495 : Blo 2293435 2293495 := bstep (se 1 (by rfl) ⟨1720121, by rfl⟩ : syracuseStep 2293495 = 3440243) B3440243
theorem B2755309 : Blo 2293435 2755309 := bbase (se 3 (by rfl) ⟨516620, by rfl⟩ : syracuseStep 2755309 = 1033241) (by norm_num)
theorem B3673745 : Blo 2293435 3673745 := bstep (se 2 (by rfl) ⟨1377654, by rfl⟩ : syracuseStep 3673745 = 2755309) B2755309
theorem B2449163 : Blo 2293435 2449163 := bstep (se 1 (by rfl) ⟨1836872, by rfl⟩ : syracuseStep 2449163 = 3673745) B3673745
theorem B6531101 : Blo 2293435 6531101 := bstep (se 3 (by rfl) ⟨1224581, by rfl⟩ : syracuseStep 6531101 = 2449163) B2449163
theorem B4354067 : Blo 2293435 4354067 := bstep (se 1 (by rfl) ⟨3265550, by rfl⟩ : syracuseStep 4354067 = 6531101) B6531101
theorem B2902711 : Blo 2293435 2902711 := bstep (se 1 (by rfl) ⟨2177033, by rfl⟩ : syracuseStep 2902711 = 4354067) B4354067
theorem B3870281 : Blo 2293435 3870281 := bstep (se 2 (by rfl) ⟨1451355, by rfl⟩ : syracuseStep 3870281 = 2902711) B2902711
theorem B2580187 : Blo 2293435 2580187 := bstep (se 1 (by rfl) ⟨1935140, by rfl⟩ : syracuseStep 2580187 = 3870281) B3870281
theorem B3440249 : Blo 2293435 3440249 := bstep (se 2 (by rfl) ⟨1290093, by rfl⟩ : syracuseStep 3440249 = 2580187) B2580187
theorem B2293499 : Blo 2293435 2293499 := bstep (se 1 (by rfl) ⟨1720124, by rfl⟩ : syracuseStep 2293499 = 3440249) B3440249
theorem B4189357 : Blo 2293435 4189357 := bbase (se 3 (by rfl) ⟨785504, by rfl⟩ : syracuseStep 4189357 = 1571009) (by norm_num)
theorem B5585809 : Blo 2293435 5585809 := bstep (se 2 (by rfl) ⟨2094678, by rfl⟩ : syracuseStep 5585809 = 4189357) B4189357
theorem B7447745 : Blo 2293435 7447745 := bstep (se 2 (by rfl) ⟨2792904, by rfl⟩ : syracuseStep 7447745 = 5585809) B5585809
theorem B19860653 : Blo 2293435 19860653 := bstep (se 3 (by rfl) ⟨3723872, by rfl⟩ : syracuseStep 19860653 = 7447745) B7447745
theorem B13240435 : Blo 2293435 13240435 := bstep (se 1 (by rfl) ⟨9930326, by rfl⟩ : syracuseStep 13240435 = 19860653) B19860653
theorem B17653913 : Blo 2293435 17653913 := bstep (se 2 (by rfl) ⟨6620217, by rfl⟩ : syracuseStep 17653913 = 13240435) B13240435
theorem B11769275 : Blo 2293435 11769275 := bstep (se 1 (by rfl) ⟨8826956, by rfl⟩ : syracuseStep 11769275 = 17653913) B17653913
theorem B7846183 : Blo 2293435 7846183 := bstep (se 1 (by rfl) ⟨5884637, by rfl⟩ : syracuseStep 7846183 = 11769275) B11769275
theorem B41846309 : Blo 2293435 41846309 := bstep (se 4 (by rfl) ⟨3923091, by rfl⟩ : syracuseStep 41846309 = 7846183) B7846183
theorem B27897539 : Blo 2293435 27897539 := bstep (se 1 (by rfl) ⟨20923154, by rfl⟩ : syracuseStep 27897539 = 41846309) B41846309
theorem B74393437 : Blo 2293435 74393437 := bstep (se 3 (by rfl) ⟨13948769, by rfl⟩ : syracuseStep 74393437 = 27897539) B27897539
theorem B99191249 : Blo 2293435 99191249 := bstep (se 2 (by rfl) ⟨37196718, by rfl⟩ : syracuseStep 99191249 = 74393437) B74393437
theorem B66127499 : Blo 2293435 66127499 := bstep (se 1 (by rfl) ⟨49595624, by rfl⟩ : syracuseStep 66127499 = 99191249) B99191249
theorem B44084999 : Blo 2293435 44084999 := bstep (se 1 (by rfl) ⟨33063749, by rfl⟩ : syracuseStep 44084999 = 66127499) B66127499
theorem B29389999 : Blo 2293435 29389999 := bstep (se 1 (by rfl) ⟨22042499, by rfl⟩ : syracuseStep 29389999 = 44084999) B44084999
theorem B39186665 : Blo 2293435 39186665 := bstep (se 2 (by rfl) ⟨14694999, by rfl⟩ : syracuseStep 39186665 = 29389999) B29389999
theorem B26124443 : Blo 2293435 26124443 := bstep (se 1 (by rfl) ⟨19593332, by rfl⟩ : syracuseStep 26124443 = 39186665) B39186665
theorem B17416295 : Blo 2293435 17416295 := bstep (se 1 (by rfl) ⟨13062221, by rfl⟩ : syracuseStep 17416295 = 26124443) B26124443
theorem B11610863 : Blo 2293435 11610863 := bstep (se 1 (by rfl) ⟨8708147, by rfl⟩ : syracuseStep 11610863 = 17416295) B17416295
theorem B7740575 : Blo 2293435 7740575 := bstep (se 1 (by rfl) ⟨5805431, by rfl⟩ : syracuseStep 7740575 = 11610863) B11610863
theorem B5160383 : Blo 2293435 5160383 := bstep (se 1 (by rfl) ⟨3870287, by rfl⟩ : syracuseStep 5160383 = 7740575) B7740575
theorem B3440255 : Blo 2293435 3440255 := bstep (se 1 (by rfl) ⟨2580191, by rfl⟩ : syracuseStep 3440255 = 5160383) B5160383
theorem B2293503 : Blo 2293435 2293503 := bstep (se 1 (by rfl) ⟨1720127, by rfl⟩ : syracuseStep 2293503 = 3440255) B3440255
theorem B3440261 : Blo 2293435 3440261 := bbase (se 4 (by rfl) ⟨322524, by rfl⟩ : syracuseStep 3440261 = 645049) (by norm_num)
theorem B2293507 : Blo 2293435 2293507 := bstep (se 1 (by rfl) ⟨1720130, by rfl⟩ : syracuseStep 2293507 = 3440261) B3440261
theorem B3870301 : Blo 2293435 3870301 := bbase (se 3 (by rfl) ⟨725681, by rfl⟩ : syracuseStep 3870301 = 1451363) (by norm_num)
theorem B5160401 : Blo 2293435 5160401 := bstep (se 2 (by rfl) ⟨1935150, by rfl⟩ : syracuseStep 5160401 = 3870301) B3870301
theorem B3440267 : Blo 2293435 3440267 := bstep (se 1 (by rfl) ⟨2580200, by rfl⟩ : syracuseStep 3440267 = 5160401) B5160401
theorem B2293511 : Blo 2293435 2293511 := bstep (se 1 (by rfl) ⟨1720133, by rfl⟩ : syracuseStep 2293511 = 3440267) B3440267
theorem B2580205 : Blo 2293435 2580205 := bbase (se 3 (by rfl) ⟨483788, by rfl⟩ : syracuseStep 2580205 = 967577) (by norm_num)
theorem B3440273 : Blo 2293435 3440273 := bstep (se 2 (by rfl) ⟨1290102, by rfl⟩ : syracuseStep 3440273 = 2580205) B2580205
theorem B2293515 : Blo 2293435 2293515 := bstep (se 1 (by rfl) ⟨1720136, by rfl⟩ : syracuseStep 2293515 = 3440273) B3440273
theorem B7740629 : Blo 2293435 7740629 := bbase (se 7 (by rfl) ⟨90710, by rfl⟩ : syracuseStep 7740629 = 181421) (by norm_num)
theorem B5160419 : Blo 2293435 5160419 := bstep (se 1 (by rfl) ⟨3870314, by rfl⟩ : syracuseStep 5160419 = 7740629) B7740629
theorem B3440279 : Blo 2293435 3440279 := bstep (se 1 (by rfl) ⟨2580209, by rfl⟩ : syracuseStep 3440279 = 5160419) B5160419
theorem B2293519 : Blo 2293435 2293519 := bstep (se 1 (by rfl) ⟨1720139, by rfl⟩ : syracuseStep 2293519 = 3440279) B3440279
theorem B3440285 : Blo 2293435 3440285 := bbase (se 3 (by rfl) ⟨645053, by rfl⟩ : syracuseStep 3440285 = 1290107) (by norm_num)
theorem B2293523 : Blo 2293435 2293523 := bstep (se 1 (by rfl) ⟨1720142, by rfl⟩ : syracuseStep 2293523 = 3440285) B3440285
theorem B5160437 : Blo 2293435 5160437 := bbase (se 5 (by rfl) ⟨241895, by rfl⟩ : syracuseStep 5160437 = 483791) (by norm_num)
theorem B3440291 : Blo 2293435 3440291 := bstep (se 1 (by rfl) ⟨2580218, by rfl⟩ : syracuseStep 3440291 = 5160437) B5160437
theorem B2293527 : Blo 2293435 2293527 := bstep (se 1 (by rfl) ⟨1720145, by rfl⟩ : syracuseStep 2293527 = 3440291) B3440291
theorem B10065941 : Blo 2293435 10065941 := bbase (se 6 (by rfl) ⟨235920, by rfl⟩ : syracuseStep 10065941 = 471841) (by norm_num)
theorem B6710627 : Blo 2293435 6710627 := bstep (se 1 (by rfl) ⟨5032970, by rfl⟩ : syracuseStep 6710627 = 10065941) B10065941
theorem B17895005 : Blo 2293435 17895005 := bstep (se 3 (by rfl) ⟨3355313, by rfl⟩ : syracuseStep 17895005 = 6710627) B6710627
theorem B11930003 : Blo 2293435 11930003 := bstep (se 1 (by rfl) ⟨8947502, by rfl⟩ : syracuseStep 11930003 = 17895005) B17895005
theorem B7953335 : Blo 2293435 7953335 := bstep (se 1 (by rfl) ⟨5965001, by rfl⟩ : syracuseStep 7953335 = 11930003) B11930003
theorem B5302223 : Blo 2293435 5302223 := bstep (se 1 (by rfl) ⟨3976667, by rfl⟩ : syracuseStep 5302223 = 7953335) B7953335
theorem B3534815 : Blo 2293435 3534815 := bstep (se 1 (by rfl) ⟨2651111, by rfl⟩ : syracuseStep 3534815 = 5302223) B5302223
theorem B2356543 : Blo 2293435 2356543 := bstep (se 1 (by rfl) ⟨1767407, by rfl⟩ : syracuseStep 2356543 = 3534815) B3534815
theorem B3142057 : Blo 2293435 3142057 := bstep (se 2 (by rfl) ⟨1178271, by rfl⟩ : syracuseStep 3142057 = 2356543) B2356543
theorem B4189409 : Blo 2293435 4189409 := bstep (se 2 (by rfl) ⟨1571028, by rfl⟩ : syracuseStep 4189409 = 3142057) B3142057
theorem B2792939 : Blo 2293435 2792939 := bstep (se 1 (by rfl) ⟨2094704, by rfl⟩ : syracuseStep 2792939 = 4189409) B4189409
theorem B7447837 : Blo 2293435 7447837 := bstep (se 3 (by rfl) ⟨1396469, by rfl⟩ : syracuseStep 7447837 = 2792939) B2792939
theorem B9930449 : Blo 2293435 9930449 := bstep (se 2 (by rfl) ⟨3723918, by rfl⟩ : syracuseStep 9930449 = 7447837) B7447837
theorem B6620299 : Blo 2293435 6620299 := bstep (se 1 (by rfl) ⟨4965224, by rfl⟩ : syracuseStep 6620299 = 9930449) B9930449
theorem B35308261 : Blo 2293435 35308261 := bstep (se 4 (by rfl) ⟨3310149, by rfl⟩ : syracuseStep 35308261 = 6620299) B6620299
theorem B47077681 : Blo 2293435 47077681 := bstep (se 2 (by rfl) ⟨17654130, by rfl⟩ : syracuseStep 47077681 = 35308261) B35308261
theorem B62770241 : Blo 2293435 62770241 := bstep (se 2 (by rfl) ⟨23538840, by rfl⟩ : syracuseStep 62770241 = 47077681) B47077681
theorem B167387309 : Blo 2293435 167387309 := bstep (se 3 (by rfl) ⟨31385120, by rfl⟩ : syracuseStep 167387309 = 62770241) B62770241
theorem B111591539 : Blo 2293435 111591539 := bstep (se 1 (by rfl) ⟨83693654, by rfl⟩ : syracuseStep 111591539 = 167387309) B167387309
theorem B74394359 : Blo 2293435 74394359 := bstep (se 1 (by rfl) ⟨55795769, by rfl⟩ : syracuseStep 74394359 = 111591539) B111591539
theorem B49596239 : Blo 2293435 49596239 := bstep (se 1 (by rfl) ⟨37197179, by rfl⟩ : syracuseStep 49596239 = 74394359) B74394359
theorem B33064159 : Blo 2293435 33064159 := bstep (se 1 (by rfl) ⟨24798119, by rfl⟩ : syracuseStep 33064159 = 49596239) B49596239
theorem B44085545 : Blo 2293435 44085545 := bstep (se 2 (by rfl) ⟨16532079, by rfl⟩ : syracuseStep 44085545 = 33064159) B33064159
theorem B29390363 : Blo 2293435 29390363 := bstep (se 1 (by rfl) ⟨22042772, by rfl⟩ : syracuseStep 29390363 = 44085545) B44085545
theorem B19593575 : Blo 2293435 19593575 := bstep (se 1 (by rfl) ⟨14695181, by rfl⟩ : syracuseStep 19593575 = 29390363) B29390363
theorem B13062383 : Blo 2293435 13062383 := bstep (se 1 (by rfl) ⟨9796787, by rfl⟩ : syracuseStep 13062383 = 19593575) B19593575
theorem B8708255 : Blo 2293435 8708255 := bstep (se 1 (by rfl) ⟨6531191, by rfl⟩ : syracuseStep 8708255 = 13062383) B13062383
theorem B5805503 : Blo 2293435 5805503 := bstep (se 1 (by rfl) ⟨4354127, by rfl⟩ : syracuseStep 5805503 = 8708255) B8708255
theorem B3870335 : Blo 2293435 3870335 := bstep (se 1 (by rfl) ⟨2902751, by rfl⟩ : syracuseStep 3870335 = 5805503) B5805503
theorem B2580223 : Blo 2293435 2580223 := bstep (se 1 (by rfl) ⟨1935167, by rfl⟩ : syracuseStep 2580223 = 3870335) B3870335
theorem B3440297 : Blo 2293435 3440297 := bstep (se 2 (by rfl) ⟨1290111, by rfl⟩ : syracuseStep 3440297 = 2580223) B2580223
theorem B2293531 : Blo 2293435 2293531 := bstep (se 1 (by rfl) ⟨1720148, by rfl⟩ : syracuseStep 2293531 = 3440297) B3440297
theorem B2449201 : Blo 2293435 2449201 := bbase (se 2 (by rfl) ⟨918450, by rfl⟩ : syracuseStep 2449201 = 1836901) (by norm_num)
theorem B3265601 : Blo 2293435 3265601 := bstep (se 2 (by rfl) ⟨1224600, by rfl⟩ : syracuseStep 3265601 = 2449201) B2449201
theorem B8708269 : Blo 2293435 8708269 := bstep (se 3 (by rfl) ⟨1632800, by rfl⟩ : syracuseStep 8708269 = 3265601) B3265601
theorem B11611025 : Blo 2293435 11611025 := bstep (se 2 (by rfl) ⟨4354134, by rfl⟩ : syracuseStep 11611025 = 8708269) B8708269
theorem B7740683 : Blo 2293435 7740683 := bstep (se 1 (by rfl) ⟨5805512, by rfl⟩ : syracuseStep 7740683 = 11611025) B11611025
theorem B5160455 : Blo 2293435 5160455 := bstep (se 1 (by rfl) ⟨3870341, by rfl⟩ : syracuseStep 5160455 = 7740683) B7740683
theorem B3440303 : Blo 2293435 3440303 := bstep (se 1 (by rfl) ⟨2580227, by rfl⟩ : syracuseStep 3440303 = 5160455) B5160455
theorem B2293535 : Blo 2293435 2293535 := bstep (se 1 (by rfl) ⟨1720151, by rfl⟩ : syracuseStep 2293535 = 3440303) B3440303
theorem B3440309 : Blo 2293435 3440309 := bbase (se 5 (by rfl) ⟨161264, by rfl⟩ : syracuseStep 3440309 = 322529) (by norm_num)
theorem B2293539 : Blo 2293435 2293539 := bstep (se 1 (by rfl) ⟨1720154, by rfl⟩ : syracuseStep 2293539 = 3440309) B3440309
theorem B5805533 : Blo 2293435 5805533 := bbase (se 3 (by rfl) ⟨1088537, by rfl⟩ : syracuseStep 5805533 = 2177075) (by norm_num)
theorem B3870355 : Blo 2293435 3870355 := bstep (se 1 (by rfl) ⟨2902766, by rfl⟩ : syracuseStep 3870355 = 5805533) B5805533
theorem B5160473 : Blo 2293435 5160473 := bstep (se 2 (by rfl) ⟨1935177, by rfl⟩ : syracuseStep 5160473 = 3870355) B3870355
theorem B3440315 : Blo 2293435 3440315 := bstep (se 1 (by rfl) ⟨2580236, by rfl⟩ : syracuseStep 3440315 = 5160473) B5160473
theorem B2293543 : Blo 2293435 2293543 := bstep (se 1 (by rfl) ⟨1720157, by rfl⟩ : syracuseStep 2293543 = 3440315) B3440315
theorem B2580241 : Blo 2293435 2580241 := bbase (se 2 (by rfl) ⟨967590, by rfl⟩ : syracuseStep 2580241 = 1935181) (by norm_num)
theorem B3440321 : Blo 2293435 3440321 := bstep (se 2 (by rfl) ⟨1290120, by rfl⟩ : syracuseStep 3440321 = 2580241) B2580241
theorem B2293547 : Blo 2293435 2293547 := bstep (se 1 (by rfl) ⟨1720160, by rfl⟩ : syracuseStep 2293547 = 3440321) B3440321
theorem B4354165 : Blo 2293435 4354165 := bbase (se 5 (by rfl) ⟨204101, by rfl⟩ : syracuseStep 4354165 = 408203) (by norm_num)
theorem B5805553 : Blo 2293435 5805553 := bstep (se 2 (by rfl) ⟨2177082, by rfl⟩ : syracuseStep 5805553 = 4354165) B4354165
theorem B7740737 : Blo 2293435 7740737 := bstep (se 2 (by rfl) ⟨2902776, by rfl⟩ : syracuseStep 7740737 = 5805553) B5805553
theorem B5160491 : Blo 2293435 5160491 := bstep (se 1 (by rfl) ⟨3870368, by rfl⟩ : syracuseStep 5160491 = 7740737) B7740737
theorem B3440327 : Blo 2293435 3440327 := bstep (se 1 (by rfl) ⟨2580245, by rfl⟩ : syracuseStep 3440327 = 5160491) B5160491
theorem B2293551 : Blo 2293435 2293551 := bstep (se 1 (by rfl) ⟨1720163, by rfl⟩ : syracuseStep 2293551 = 3440327) B3440327
theorem B3440333 : Blo 2293435 3440333 := bbase (se 3 (by rfl) ⟨645062, by rfl⟩ : syracuseStep 3440333 = 1290125) (by norm_num)
theorem B2293555 : Blo 2293435 2293555 := bstep (se 1 (by rfl) ⟨1720166, by rfl⟩ : syracuseStep 2293555 = 3440333) B3440333
theorem B5160509 : Blo 2293435 5160509 := bbase (se 3 (by rfl) ⟨967595, by rfl⟩ : syracuseStep 5160509 = 1935191) (by norm_num)
theorem B3440339 : Blo 2293435 3440339 := bstep (se 1 (by rfl) ⟨2580254, by rfl⟩ : syracuseStep 3440339 = 5160509) B5160509
theorem B2293559 : Blo 2293435 2293559 := bstep (se 1 (by rfl) ⟨1720169, by rfl⟩ : syracuseStep 2293559 = 3440339) B3440339
theorem B3870389 : Blo 2293435 3870389 := bbase (se 5 (by rfl) ⟨181424, by rfl⟩ : syracuseStep 3870389 = 362849) (by norm_num)
theorem B2580259 : Blo 2293435 2580259 := bstep (se 1 (by rfl) ⟨1935194, by rfl⟩ : syracuseStep 2580259 = 3870389) B3870389
theorem B3440345 : Blo 2293435 3440345 := bstep (se 2 (by rfl) ⟨1290129, by rfl⟩ : syracuseStep 3440345 = 2580259) B2580259
theorem B2293563 : Blo 2293435 2293563 := bstep (se 1 (by rfl) ⟨1720172, by rfl⟩ : syracuseStep 2293563 = 3440345) B3440345
theorem B3673853 : Blo 2293435 3673853 := bbase (se 3 (by rfl) ⟨688847, by rfl⟩ : syracuseStep 3673853 = 1377695) (by norm_num)
theorem B2449235 : Blo 2293435 2449235 := bstep (se 1 (by rfl) ⟨1836926, by rfl⟩ : syracuseStep 2449235 = 3673853) B3673853
theorem B6531293 : Blo 2293435 6531293 := bstep (se 3 (by rfl) ⟨1224617, by rfl⟩ : syracuseStep 6531293 = 2449235) B2449235
theorem B17416781 : Blo 2293435 17416781 := bstep (se 3 (by rfl) ⟨3265646, by rfl⟩ : syracuseStep 17416781 = 6531293) B6531293
theorem B11611187 : Blo 2293435 11611187 := bstep (se 1 (by rfl) ⟨8708390, by rfl⟩ : syracuseStep 11611187 = 17416781) B17416781
theorem B7740791 : Blo 2293435 7740791 := bstep (se 1 (by rfl) ⟨5805593, by rfl⟩ : syracuseStep 7740791 = 11611187) B11611187
theorem B5160527 : Blo 2293435 5160527 := bstep (se 1 (by rfl) ⟨3870395, by rfl⟩ : syracuseStep 5160527 = 7740791) B7740791
theorem B3440351 : Blo 2293435 3440351 := bstep (se 1 (by rfl) ⟨2580263, by rfl⟩ : syracuseStep 3440351 = 5160527) B5160527
theorem B2293567 : Blo 2293435 2293567 := bstep (se 1 (by rfl) ⟨1720175, by rfl⟩ : syracuseStep 2293567 = 3440351) B3440351
theorem B3440357 : Blo 2293435 3440357 := bbase (se 4 (by rfl) ⟨322533, by rfl⟩ : syracuseStep 3440357 = 645067) (by norm_num)
theorem B2293571 : Blo 2293435 2293571 := bstep (se 1 (by rfl) ⟨1720178, by rfl⟩ : syracuseStep 2293571 = 3440357) B3440357
theorem B6531317 : Blo 2293435 6531317 := bbase (se 5 (by rfl) ⟨306155, by rfl⟩ : syracuseStep 6531317 = 612311) (by norm_num)
theorem B4354211 : Blo 2293435 4354211 := bstep (se 1 (by rfl) ⟨3265658, by rfl⟩ : syracuseStep 4354211 = 6531317) B6531317
theorem B2902807 : Blo 2293435 2902807 := bstep (se 1 (by rfl) ⟨2177105, by rfl⟩ : syracuseStep 2902807 = 4354211) B4354211
theorem B3870409 : Blo 2293435 3870409 := bstep (se 2 (by rfl) ⟨1451403, by rfl⟩ : syracuseStep 3870409 = 2902807) B2902807
theorem B5160545 : Blo 2293435 5160545 := bstep (se 2 (by rfl) ⟨1935204, by rfl⟩ : syracuseStep 5160545 = 3870409) B3870409
theorem B3440363 : Blo 2293435 3440363 := bstep (se 1 (by rfl) ⟨2580272, by rfl⟩ : syracuseStep 3440363 = 5160545) B5160545
theorem B2293575 : Blo 2293435 2293575 := bstep (se 1 (by rfl) ⟨1720181, by rfl⟩ : syracuseStep 2293575 = 3440363) B3440363
theorem B2580277 : Blo 2293435 2580277 := bbase (se 5 (by rfl) ⟨120950, by rfl⟩ : syracuseStep 2580277 = 241901) (by norm_num)
theorem B3440369 : Blo 2293435 3440369 := bstep (se 2 (by rfl) ⟨1290138, by rfl⟩ : syracuseStep 3440369 = 2580277) B2580277
theorem B2293579 : Blo 2293435 2293579 := bstep (se 1 (by rfl) ⟨1720184, by rfl⟩ : syracuseStep 2293579 = 3440369) B3440369
theorem B2902817 : Blo 2293435 2902817 := bbase (se 2 (by rfl) ⟨1088556, by rfl⟩ : syracuseStep 2902817 = 2177113) (by norm_num)
theorem B7740845 : Blo 2293435 7740845 := bstep (se 3 (by rfl) ⟨1451408, by rfl⟩ : syracuseStep 7740845 = 2902817) B2902817
theorem B5160563 : Blo 2293435 5160563 := bstep (se 1 (by rfl) ⟨3870422, by rfl⟩ : syracuseStep 5160563 = 7740845) B7740845
theorem B3440375 : Blo 2293435 3440375 := bstep (se 1 (by rfl) ⟨2580281, by rfl⟩ : syracuseStep 3440375 = 5160563) B5160563
theorem B2293583 : Blo 2293435 2293583 := bstep (se 1 (by rfl) ⟨1720187, by rfl⟩ : syracuseStep 2293583 = 3440375) B3440375
theorem B3440381 : Blo 2293435 3440381 := bbase (se 3 (by rfl) ⟨645071, by rfl⟩ : syracuseStep 3440381 = 1290143) (by norm_num)
theorem B2293587 : Blo 2293435 2293587 := bstep (se 1 (by rfl) ⟨1720190, by rfl⟩ : syracuseStep 2293587 = 3440381) B3440381
theorem B5160581 : Blo 2293435 5160581 := bbase (se 4 (by rfl) ⟨483804, by rfl⟩ : syracuseStep 5160581 = 967609) (by norm_num)
theorem B3440387 : Blo 2293435 3440387 := bstep (se 1 (by rfl) ⟨2580290, by rfl⟩ : syracuseStep 3440387 = 5160581) B5160581
theorem B2293591 : Blo 2293435 2293591 := bstep (se 1 (by rfl) ⟨1720193, by rfl⟩ : syracuseStep 2293591 = 3440387) B3440387
theorem B7347797 : Blo 2293435 7347797 := bbase (se 8 (by rfl) ⟨43053, by rfl⟩ : syracuseStep 7347797 = 86107) (by norm_num)
theorem B4898531 : Blo 2293435 4898531 := bstep (se 1 (by rfl) ⟨3673898, by rfl⟩ : syracuseStep 4898531 = 7347797) B7347797
theorem B3265687 : Blo 2293435 3265687 := bstep (se 1 (by rfl) ⟨2449265, by rfl⟩ : syracuseStep 3265687 = 4898531) B4898531
theorem B4354249 : Blo 2293435 4354249 := bstep (se 2 (by rfl) ⟨1632843, by rfl⟩ : syracuseStep 4354249 = 3265687) B3265687
theorem B5805665 : Blo 2293435 5805665 := bstep (se 2 (by rfl) ⟨2177124, by rfl⟩ : syracuseStep 5805665 = 4354249) B4354249
theorem B3870443 : Blo 2293435 3870443 := bstep (se 1 (by rfl) ⟨2902832, by rfl⟩ : syracuseStep 3870443 = 5805665) B5805665
theorem B2580295 : Blo 2293435 2580295 := bstep (se 1 (by rfl) ⟨1935221, by rfl⟩ : syracuseStep 2580295 = 3870443) B3870443
theorem B3440393 : Blo 2293435 3440393 := bstep (se 2 (by rfl) ⟨1290147, by rfl⟩ : syracuseStep 3440393 = 2580295) B2580295
theorem B2293595 : Blo 2293435 2293595 := bstep (se 1 (by rfl) ⟨1720196, by rfl⟩ : syracuseStep 2293595 = 3440393) B3440393
theorem B11611349 : Blo 2293435 11611349 := bbase (se 7 (by rfl) ⟨136070, by rfl⟩ : syracuseStep 11611349 = 272141) (by norm_num)
theorem B7740899 : Blo 2293435 7740899 := bstep (se 1 (by rfl) ⟨5805674, by rfl⟩ : syracuseStep 7740899 = 11611349) B11611349
theorem B5160599 : Blo 2293435 5160599 := bstep (se 1 (by rfl) ⟨3870449, by rfl⟩ : syracuseStep 5160599 = 7740899) B7740899
theorem B3440399 : Blo 2293435 3440399 := bstep (se 1 (by rfl) ⟨2580299, by rfl⟩ : syracuseStep 3440399 = 5160599) B5160599
theorem B2293599 : Blo 2293435 2293599 := bstep (se 1 (by rfl) ⟨1720199, by rfl⟩ : syracuseStep 2293599 = 3440399) B3440399
theorem B3440405 : Blo 2293435 3440405 := bbase (se 6 (by rfl) ⟨80634, by rfl⟩ : syracuseStep 3440405 = 161269) (by norm_num)
theorem B2293603 : Blo 2293435 2293603 := bstep (se 1 (by rfl) ⟨1720202, by rfl⟩ : syracuseStep 2293603 = 3440405) B3440405
theorem B4965389 : Blo 2293435 4965389 := bbase (se 3 (by rfl) ⟨931010, by rfl⟩ : syracuseStep 4965389 = 1862021) (by norm_num)
theorem B3310259 : Blo 2293435 3310259 := bstep (se 1 (by rfl) ⟨2482694, by rfl⟩ : syracuseStep 3310259 = 4965389) B4965389
theorem B35309429 : Blo 2293435 35309429 := bstep (se 5 (by rfl) ⟨1655129, by rfl⟩ : syracuseStep 35309429 = 3310259) B3310259
theorem B23539619 : Blo 2293435 23539619 := bstep (se 1 (by rfl) ⟨17654714, by rfl⟩ : syracuseStep 23539619 = 35309429) B35309429
theorem B62772317 : Blo 2293435 62772317 := bstep (se 3 (by rfl) ⟨11769809, by rfl⟩ : syracuseStep 62772317 = 23539619) B23539619
theorem B41848211 : Blo 2293435 41848211 := bstep (se 1 (by rfl) ⟨31386158, by rfl⟩ : syracuseStep 41848211 = 62772317) B62772317
theorem B111595229 : Blo 2293435 111595229 := bstep (se 3 (by rfl) ⟨20924105, by rfl⟩ : syracuseStep 111595229 = 41848211) B41848211
theorem B74396819 : Blo 2293435 74396819 := bstep (se 1 (by rfl) ⟨55797614, by rfl⟩ : syracuseStep 74396819 = 111595229) B111595229
theorem B49597879 : Blo 2293435 49597879 := bstep (se 1 (by rfl) ⟨37198409, by rfl⟩ : syracuseStep 49597879 = 74396819) B74396819
theorem B66130505 : Blo 2293435 66130505 := bstep (se 2 (by rfl) ⟨24798939, by rfl⟩ : syracuseStep 66130505 = 49597879) B49597879
theorem B44087003 : Blo 2293435 44087003 := bstep (se 1 (by rfl) ⟨33065252, by rfl⟩ : syracuseStep 44087003 = 66130505) B66130505
theorem B29391335 : Blo 2293435 29391335 := bstep (se 1 (by rfl) ⟨22043501, by rfl⟩ : syracuseStep 29391335 = 44087003) B44087003
theorem B19594223 : Blo 2293435 19594223 := bstep (se 1 (by rfl) ⟨14695667, by rfl⟩ : syracuseStep 19594223 = 29391335) B29391335
theorem B13062815 : Blo 2293435 13062815 := bstep (se 1 (by rfl) ⟨9797111, by rfl⟩ : syracuseStep 13062815 = 19594223) B19594223
theorem B8708543 : Blo 2293435 8708543 := bstep (se 1 (by rfl) ⟨6531407, by rfl⟩ : syracuseStep 8708543 = 13062815) B13062815
theorem B5805695 : Blo 2293435 5805695 := bstep (se 1 (by rfl) ⟨4354271, by rfl⟩ : syracuseStep 5805695 = 8708543) B8708543
theorem B3870463 : Blo 2293435 3870463 := bstep (se 1 (by rfl) ⟨2902847, by rfl⟩ : syracuseStep 3870463 = 5805695) B5805695
theorem B5160617 : Blo 2293435 5160617 := bstep (se 2 (by rfl) ⟨1935231, by rfl⟩ : syracuseStep 5160617 = 3870463) B3870463
theorem B3440411 : Blo 2293435 3440411 := bstep (se 1 (by rfl) ⟨2580308, by rfl⟩ : syracuseStep 3440411 = 5160617) B5160617
theorem B2293607 : Blo 2293435 2293607 := bstep (se 1 (by rfl) ⟨1720205, by rfl⟩ : syracuseStep 2293607 = 3440411) B3440411
theorem B2580313 : Blo 2293435 2580313 := bbase (se 2 (by rfl) ⟨967617, by rfl⟩ : syracuseStep 2580313 = 1935235) (by norm_num)
theorem B3440417 : Blo 2293435 3440417 := bstep (se 2 (by rfl) ⟨1290156, by rfl⟩ : syracuseStep 3440417 = 2580313) B2580313
theorem B2293611 : Blo 2293435 2293611 := bstep (se 1 (by rfl) ⟨1720208, by rfl⟩ : syracuseStep 2293611 = 3440417) B3440417
theorem B4898573 : Blo 2293435 4898573 := bbase (se 3 (by rfl) ⟨918482, by rfl⟩ : syracuseStep 4898573 = 1836965) (by norm_num)
theorem B3265715 : Blo 2293435 3265715 := bstep (se 1 (by rfl) ⟨2449286, by rfl⟩ : syracuseStep 3265715 = 4898573) B4898573
theorem B8708573 : Blo 2293435 8708573 := bstep (se 3 (by rfl) ⟨1632857, by rfl⟩ : syracuseStep 8708573 = 3265715) B3265715
theorem B5805715 : Blo 2293435 5805715 := bstep (se 1 (by rfl) ⟨4354286, by rfl⟩ : syracuseStep 5805715 = 8708573) B8708573
theorem B7740953 : Blo 2293435 7740953 := bstep (se 2 (by rfl) ⟨2902857, by rfl⟩ : syracuseStep 7740953 = 5805715) B5805715
theorem B5160635 : Blo 2293435 5160635 := bstep (se 1 (by rfl) ⟨3870476, by rfl⟩ : syracuseStep 5160635 = 7740953) B7740953
theorem B3440423 : Blo 2293435 3440423 := bstep (se 1 (by rfl) ⟨2580317, by rfl⟩ : syracuseStep 3440423 = 5160635) B5160635
theorem B2293615 : Blo 2293435 2293615 := bstep (se 1 (by rfl) ⟨1720211, by rfl⟩ : syracuseStep 2293615 = 3440423) B3440423
theorem B3440429 : Blo 2293435 3440429 := bbase (se 3 (by rfl) ⟨645080, by rfl⟩ : syracuseStep 3440429 = 1290161) (by norm_num)
theorem B2293619 : Blo 2293435 2293619 := bstep (se 1 (by rfl) ⟨1720214, by rfl⟩ : syracuseStep 2293619 = 3440429) B3440429
theorem B5160653 : Blo 2293435 5160653 := bbase (se 3 (by rfl) ⟨967622, by rfl⟩ : syracuseStep 5160653 = 1935245) (by norm_num)
theorem B3440435 : Blo 2293435 3440435 := bstep (se 1 (by rfl) ⟨2580326, by rfl⟩ : syracuseStep 3440435 = 5160653) B5160653
theorem B2293623 : Blo 2293435 2293623 := bstep (se 1 (by rfl) ⟨1720217, by rfl⟩ : syracuseStep 2293623 = 3440435) B3440435
theorem B2902873 : Blo 2293435 2902873 := bbase (se 2 (by rfl) ⟨1088577, by rfl⟩ : syracuseStep 2902873 = 2177155) (by norm_num)
theorem B3870497 : Blo 2293435 3870497 := bstep (se 2 (by rfl) ⟨1451436, by rfl⟩ : syracuseStep 3870497 = 2902873) B2902873
theorem B2580331 : Blo 2293435 2580331 := bstep (se 1 (by rfl) ⟨1935248, by rfl⟩ : syracuseStep 2580331 = 3870497) B3870497
theorem B3440441 : Blo 2293435 3440441 := bstep (se 2 (by rfl) ⟨1290165, by rfl⟩ : syracuseStep 3440441 = 2580331) B2580331
theorem B2293627 : Blo 2293435 2293627 := bstep (se 1 (by rfl) ⟨1720220, by rfl⟩ : syracuseStep 2293627 = 3440441) B3440441
theorem B5510933 : Blo 2293435 5510933 := bbase (se 6 (by rfl) ⟨129162, by rfl⟩ : syracuseStep 5510933 = 258325) (by norm_num)
theorem B3673955 : Blo 2293435 3673955 := bstep (se 1 (by rfl) ⟨2755466, by rfl⟩ : syracuseStep 3673955 = 5510933) B5510933
theorem B9797213 : Blo 2293435 9797213 := bstep (se 3 (by rfl) ⟨1836977, by rfl⟩ : syracuseStep 9797213 = 3673955) B3673955
theorem B26125901 : Blo 2293435 26125901 := bstep (se 3 (by rfl) ⟨4898606, by rfl⟩ : syracuseStep 26125901 = 9797213) B9797213
theorem B17417267 : Blo 2293435 17417267 := bstep (se 1 (by rfl) ⟨13062950, by rfl⟩ : syracuseStep 17417267 = 26125901) B26125901
theorem B11611511 : Blo 2293435 11611511 := bstep (se 1 (by rfl) ⟨8708633, by rfl⟩ : syracuseStep 11611511 = 17417267) B17417267
theorem B7741007 : Blo 2293435 7741007 := bstep (se 1 (by rfl) ⟨5805755, by rfl⟩ : syracuseStep 7741007 = 11611511) B11611511
theorem B5160671 : Blo 2293435 5160671 := bstep (se 1 (by rfl) ⟨3870503, by rfl⟩ : syracuseStep 5160671 = 7741007) B7741007
theorem B3440447 : Blo 2293435 3440447 := bstep (se 1 (by rfl) ⟨2580335, by rfl⟩ : syracuseStep 3440447 = 5160671) B5160671
theorem B2293631 : Blo 2293435 2293631 := bstep (se 1 (by rfl) ⟨1720223, by rfl⟩ : syracuseStep 2293631 = 3440447) B3440447
theorem B3440453 : Blo 2293435 3440453 := bbase (se 4 (by rfl) ⟨322542, by rfl⟩ : syracuseStep 3440453 = 645085) (by norm_num)
theorem B2293635 : Blo 2293435 2293635 := bstep (se 1 (by rfl) ⟨1720226, by rfl⟩ : syracuseStep 2293635 = 3440453) B3440453
theorem B3870517 : Blo 2293435 3870517 := bbase (se 5 (by rfl) ⟨181430, by rfl⟩ : syracuseStep 3870517 = 362861) (by norm_num)
theorem B5160689 : Blo 2293435 5160689 := bstep (se 2 (by rfl) ⟨1935258, by rfl⟩ : syracuseStep 5160689 = 3870517) B3870517
theorem B3440459 : Blo 2293435 3440459 := bstep (se 1 (by rfl) ⟨2580344, by rfl⟩ : syracuseStep 3440459 = 5160689) B5160689
theorem B2293639 : Blo 2293435 2293639 := bstep (se 1 (by rfl) ⟨1720229, by rfl⟩ : syracuseStep 2293639 = 3440459) B3440459
theorem B2580349 : Blo 2293435 2580349 := bbase (se 3 (by rfl) ⟨483815, by rfl⟩ : syracuseStep 2580349 = 967631) (by norm_num)
theorem B3440465 : Blo 2293435 3440465 := bstep (se 2 (by rfl) ⟨1290174, by rfl⟩ : syracuseStep 3440465 = 2580349) B2580349
theorem B2293643 : Blo 2293435 2293643 := bstep (se 1 (by rfl) ⟨1720232, by rfl⟩ : syracuseStep 2293643 = 3440465) B3440465
theorem B7741061 : Blo 2293435 7741061 := bbase (se 4 (by rfl) ⟨725724, by rfl⟩ : syracuseStep 7741061 = 1451449) (by norm_num)
theorem B5160707 : Blo 2293435 5160707 := bstep (se 1 (by rfl) ⟨3870530, by rfl⟩ : syracuseStep 5160707 = 7741061) B7741061
theorem B3440471 : Blo 2293435 3440471 := bstep (se 1 (by rfl) ⟨2580353, by rfl⟩ : syracuseStep 3440471 = 5160707) B5160707
theorem B2293647 : Blo 2293435 2293647 := bstep (se 1 (by rfl) ⟨1720235, by rfl⟩ : syracuseStep 2293647 = 3440471) B3440471
theorem B3440477 : Blo 2293435 3440477 := bbase (se 3 (by rfl) ⟨645089, by rfl⟩ : syracuseStep 3440477 = 1290179) (by norm_num)
theorem B2293651 : Blo 2293435 2293651 := bstep (se 1 (by rfl) ⟨1720238, by rfl⟩ : syracuseStep 2293651 = 3440477) B3440477
theorem B5160725 : Blo 2293435 5160725 := bbase (se 6 (by rfl) ⟨120954, by rfl⟩ : syracuseStep 5160725 = 241909) (by norm_num)
theorem B3440483 : Blo 2293435 3440483 := bstep (se 1 (by rfl) ⟨2580362, by rfl⟩ : syracuseStep 3440483 = 5160725) B5160725
theorem B2293655 : Blo 2293435 2293655 := bstep (se 1 (by rfl) ⟨1720241, by rfl⟩ : syracuseStep 2293655 = 3440483) B3440483
theorem B8708741 : Blo 2293435 8708741 := bbase (se 4 (by rfl) ⟨816444, by rfl⟩ : syracuseStep 8708741 = 1632889) (by norm_num)
theorem B5805827 : Blo 2293435 5805827 := bstep (se 1 (by rfl) ⟨4354370, by rfl⟩ : syracuseStep 5805827 = 8708741) B8708741
theorem B3870551 : Blo 2293435 3870551 := bstep (se 1 (by rfl) ⟨2902913, by rfl⟩ : syracuseStep 3870551 = 5805827) B5805827
theorem B2580367 : Blo 2293435 2580367 := bstep (se 1 (by rfl) ⟨1935275, by rfl⟩ : syracuseStep 2580367 = 3870551) B3870551
theorem B3440489 : Blo 2293435 3440489 := bstep (se 2 (by rfl) ⟨1290183, by rfl⟩ : syracuseStep 3440489 = 2580367) B2580367
theorem B2293659 : Blo 2293435 2293659 := bstep (se 1 (by rfl) ⟨1720244, by rfl⟩ : syracuseStep 2293659 = 3440489) B3440489
theorem B2755505 : Blo 2293435 2755505 := bbase (se 2 (by rfl) ⟨1033314, by rfl⟩ : syracuseStep 2755505 = 2066629) (by norm_num)
theorem B7348013 : Blo 2293435 7348013 := bstep (se 3 (by rfl) ⟨1377752, by rfl⟩ : syracuseStep 7348013 = 2755505) B2755505
theorem B4898675 : Blo 2293435 4898675 := bstep (se 1 (by rfl) ⟨3674006, by rfl⟩ : syracuseStep 4898675 = 7348013) B7348013
theorem B13063133 : Blo 2293435 13063133 := bstep (se 3 (by rfl) ⟨2449337, by rfl⟩ : syracuseStep 13063133 = 4898675) B4898675
theorem B8708755 : Blo 2293435 8708755 := bstep (se 1 (by rfl) ⟨6531566, by rfl⟩ : syracuseStep 8708755 = 13063133) B13063133
theorem B11611673 : Blo 2293435 11611673 := bstep (se 2 (by rfl) ⟨4354377, by rfl⟩ : syracuseStep 11611673 = 8708755) B8708755
theorem B7741115 : Blo 2293435 7741115 := bstep (se 1 (by rfl) ⟨5805836, by rfl⟩ : syracuseStep 7741115 = 11611673) B11611673
theorem B5160743 : Blo 2293435 5160743 := bstep (se 1 (by rfl) ⟨3870557, by rfl⟩ : syracuseStep 5160743 = 7741115) B7741115
theorem B3440495 : Blo 2293435 3440495 := bstep (se 1 (by rfl) ⟨2580371, by rfl⟩ : syracuseStep 3440495 = 5160743) B5160743
theorem B2293663 : Blo 2293435 2293663 := bstep (se 1 (by rfl) ⟨1720247, by rfl⟩ : syracuseStep 2293663 = 3440495) B3440495
theorem B3440501 : Blo 2293435 3440501 := bbase (se 5 (by rfl) ⟨161273, by rfl⟩ : syracuseStep 3440501 = 322547) (by norm_num)
theorem B2293667 : Blo 2293435 2293667 := bstep (se 1 (by rfl) ⟨1720250, by rfl⟩ : syracuseStep 2293667 = 3440501) B3440501
theorem B4898693 : Blo 2293435 4898693 := bbase (se 4 (by rfl) ⟨459252, by rfl⟩ : syracuseStep 4898693 = 918505) (by norm_num)
theorem B3265795 : Blo 2293435 3265795 := bstep (se 1 (by rfl) ⟨2449346, by rfl⟩ : syracuseStep 3265795 = 4898693) B4898693
theorem B4354393 : Blo 2293435 4354393 := bstep (se 2 (by rfl) ⟨1632897, by rfl⟩ : syracuseStep 4354393 = 3265795) B3265795
theorem B5805857 : Blo 2293435 5805857 := bstep (se 2 (by rfl) ⟨2177196, by rfl⟩ : syracuseStep 5805857 = 4354393) B4354393
theorem B3870571 : Blo 2293435 3870571 := bstep (se 1 (by rfl) ⟨2902928, by rfl⟩ : syracuseStep 3870571 = 5805857) B5805857
theorem B5160761 : Blo 2293435 5160761 := bstep (se 2 (by rfl) ⟨1935285, by rfl⟩ : syracuseStep 5160761 = 3870571) B3870571
theorem B3440507 : Blo 2293435 3440507 := bstep (se 1 (by rfl) ⟨2580380, by rfl⟩ : syracuseStep 3440507 = 5160761) B5160761
theorem B2293671 : Blo 2293435 2293671 := bstep (se 1 (by rfl) ⟨1720253, by rfl⟩ : syracuseStep 2293671 = 3440507) B3440507
theorem B2580385 : Blo 2293435 2580385 := bbase (se 2 (by rfl) ⟨967644, by rfl⟩ : syracuseStep 2580385 = 1935289) (by norm_num)
theorem B3440513 : Blo 2293435 3440513 := bstep (se 2 (by rfl) ⟨1290192, by rfl⟩ : syracuseStep 3440513 = 2580385) B2580385
theorem B2293675 : Blo 2293435 2293675 := bstep (se 1 (by rfl) ⟨1720256, by rfl⟩ : syracuseStep 2293675 = 3440513) B3440513
theorem B5805877 : Blo 2293435 5805877 := bbase (se 5 (by rfl) ⟨272150, by rfl⟩ : syracuseStep 5805877 = 544301) (by norm_num)
theorem B7741169 : Blo 2293435 7741169 := bstep (se 2 (by rfl) ⟨2902938, by rfl⟩ : syracuseStep 7741169 = 5805877) B5805877
theorem B5160779 : Blo 2293435 5160779 := bstep (se 1 (by rfl) ⟨3870584, by rfl⟩ : syracuseStep 5160779 = 7741169) B7741169
theorem B3440519 : Blo 2293435 3440519 := bstep (se 1 (by rfl) ⟨2580389, by rfl⟩ : syracuseStep 3440519 = 5160779) B5160779
theorem B2293679 : Blo 2293435 2293679 := bstep (se 1 (by rfl) ⟨1720259, by rfl⟩ : syracuseStep 2293679 = 3440519) B3440519
theorem B3440525 : Blo 2293435 3440525 := bbase (se 3 (by rfl) ⟨645098, by rfl⟩ : syracuseStep 3440525 = 1290197) (by norm_num)
theorem B2293683 : Blo 2293435 2293683 := bstep (se 1 (by rfl) ⟨1720262, by rfl⟩ : syracuseStep 2293683 = 3440525) B3440525
theorem B5160797 : Blo 2293435 5160797 := bbase (se 3 (by rfl) ⟨967649, by rfl⟩ : syracuseStep 5160797 = 1935299) (by norm_num)
theorem B3440531 : Blo 2293435 3440531 := bstep (se 1 (by rfl) ⟨2580398, by rfl⟩ : syracuseStep 3440531 = 5160797) B5160797
theorem B2293687 : Blo 2293435 2293687 := bstep (se 1 (by rfl) ⟨1720265, by rfl⟩ : syracuseStep 2293687 = 3440531) B3440531
theorem B3870605 : Blo 2293435 3870605 := bbase (se 3 (by rfl) ⟨725738, by rfl⟩ : syracuseStep 3870605 = 1451477) (by norm_num)
theorem B2580403 : Blo 2293435 2580403 := bstep (se 1 (by rfl) ⟨1935302, by rfl⟩ : syracuseStep 2580403 = 3870605) B3870605
theorem B3440537 : Blo 2293435 3440537 := bstep (se 2 (by rfl) ⟨1290201, by rfl⟩ : syracuseStep 3440537 = 2580403) B2580403
theorem B2293691 : Blo 2293435 2293691 := bstep (se 1 (by rfl) ⟨1720268, by rfl⟩ : syracuseStep 2293691 = 3440537) B3440537
theorem B6199973 : Blo 2293435 6199973 := bbase (se 4 (by rfl) ⟨581247, by rfl⟩ : syracuseStep 6199973 = 1162495) (by norm_num)
theorem B4133315 : Blo 2293435 4133315 := bstep (se 1 (by rfl) ⟨3099986, by rfl⟩ : syracuseStep 4133315 = 6199973) B6199973
theorem B11022173 : Blo 2293435 11022173 := bstep (se 3 (by rfl) ⟨2066657, by rfl⟩ : syracuseStep 11022173 = 4133315) B4133315
theorem B7348115 : Blo 2293435 7348115 := bstep (se 1 (by rfl) ⟨5511086, by rfl⟩ : syracuseStep 7348115 = 11022173) B11022173
theorem B19594973 : Blo 2293435 19594973 := bstep (se 3 (by rfl) ⟨3674057, by rfl⟩ : syracuseStep 19594973 = 7348115) B7348115
theorem B13063315 : Blo 2293435 13063315 := bstep (se 1 (by rfl) ⟨9797486, by rfl⟩ : syracuseStep 13063315 = 19594973) B19594973
theorem B17417753 : Blo 2293435 17417753 := bstep (se 2 (by rfl) ⟨6531657, by rfl⟩ : syracuseStep 17417753 = 13063315) B13063315
theorem B11611835 : Blo 2293435 11611835 := bstep (se 1 (by rfl) ⟨8708876, by rfl⟩ : syracuseStep 11611835 = 17417753) B17417753
theorem B7741223 : Blo 2293435 7741223 := bstep (se 1 (by rfl) ⟨5805917, by rfl⟩ : syracuseStep 7741223 = 11611835) B11611835
theorem B5160815 : Blo 2293435 5160815 := bstep (se 1 (by rfl) ⟨3870611, by rfl⟩ : syracuseStep 5160815 = 7741223) B7741223
theorem B3440543 : Blo 2293435 3440543 := bstep (se 1 (by rfl) ⟨2580407, by rfl⟩ : syracuseStep 3440543 = 5160815) B5160815
theorem B2293695 : Blo 2293435 2293695 := bstep (se 1 (by rfl) ⟨1720271, by rfl⟩ : syracuseStep 2293695 = 3440543) B3440543
theorem B3440549 : Blo 2293435 3440549 := bbase (se 4 (by rfl) ⟨322551, by rfl⟩ : syracuseStep 3440549 = 645103) (by norm_num)
theorem B2293699 : Blo 2293435 2293699 := bstep (se 1 (by rfl) ⟨1720274, by rfl⟩ : syracuseStep 2293699 = 3440549) B3440549
theorem B2902969 : Blo 2293435 2902969 := bbase (se 2 (by rfl) ⟨1088613, by rfl⟩ : syracuseStep 2902969 = 2177227) (by norm_num)
theorem B3870625 : Blo 2293435 3870625 := bstep (se 2 (by rfl) ⟨1451484, by rfl⟩ : syracuseStep 3870625 = 2902969) B2902969
theorem B5160833 : Blo 2293435 5160833 := bstep (se 2 (by rfl) ⟨1935312, by rfl⟩ : syracuseStep 5160833 = 3870625) B3870625
theorem B3440555 : Blo 2293435 3440555 := bstep (se 1 (by rfl) ⟨2580416, by rfl⟩ : syracuseStep 3440555 = 5160833) B5160833
theorem B2293703 : Blo 2293435 2293703 := bstep (se 1 (by rfl) ⟨1720277, by rfl⟩ : syracuseStep 2293703 = 3440555) B3440555
theorem B2580421 : Blo 2293435 2580421 := bbase (se 4 (by rfl) ⟨241914, by rfl⟩ : syracuseStep 2580421 = 483829) (by norm_num)
theorem B3440561 : Blo 2293435 3440561 := bstep (se 2 (by rfl) ⟨1290210, by rfl⟩ : syracuseStep 3440561 = 2580421) B2580421
theorem B2293707 : Blo 2293435 2293707 := bstep (se 1 (by rfl) ⟨1720280, by rfl⟩ : syracuseStep 2293707 = 3440561) B3440561
theorem B4354469 : Blo 2293435 4354469 := bbase (se 4 (by rfl) ⟨408231, by rfl⟩ : syracuseStep 4354469 = 816463) (by norm_num)
theorem B2902979 : Blo 2293435 2902979 := bstep (se 1 (by rfl) ⟨2177234, by rfl⟩ : syracuseStep 2902979 = 4354469) B4354469
theorem B7741277 : Blo 2293435 7741277 := bstep (se 3 (by rfl) ⟨1451489, by rfl⟩ : syracuseStep 7741277 = 2902979) B2902979
theorem B5160851 : Blo 2293435 5160851 := bstep (se 1 (by rfl) ⟨3870638, by rfl⟩ : syracuseStep 5160851 = 7741277) B7741277
theorem B3440567 : Blo 2293435 3440567 := bstep (se 1 (by rfl) ⟨2580425, by rfl⟩ : syracuseStep 3440567 = 5160851) B5160851
theorem B2293711 : Blo 2293435 2293711 := bstep (se 1 (by rfl) ⟨1720283, by rfl⟩ : syracuseStep 2293711 = 3440567) B3440567
theorem B3440573 : Blo 2293435 3440573 := bbase (se 3 (by rfl) ⟨645107, by rfl⟩ : syracuseStep 3440573 = 1290215) (by norm_num)
theorem B2293715 : Blo 2293435 2293715 := bstep (se 1 (by rfl) ⟨1720286, by rfl⟩ : syracuseStep 2293715 = 3440573) B3440573
theorem B5160869 : Blo 2293435 5160869 := bbase (se 4 (by rfl) ⟨483831, by rfl⟩ : syracuseStep 5160869 = 967663) (by norm_num)
theorem B3440579 : Blo 2293435 3440579 := bstep (se 1 (by rfl) ⟨2580434, by rfl⟩ : syracuseStep 3440579 = 5160869) B5160869
theorem B2293719 : Blo 2293435 2293719 := bstep (se 1 (by rfl) ⟨1720289, by rfl⟩ : syracuseStep 2293719 = 3440579) B3440579
theorem B5805989 : Blo 2293435 5805989 := bbase (se 4 (by rfl) ⟨544311, by rfl⟩ : syracuseStep 5805989 = 1088623) (by norm_num)
theorem B3870659 : Blo 2293435 3870659 := bstep (se 1 (by rfl) ⟨2902994, by rfl⟩ : syracuseStep 3870659 = 5805989) B5805989
theorem B2580439 : Blo 2293435 2580439 := bstep (se 1 (by rfl) ⟨1935329, by rfl⟩ : syracuseStep 2580439 = 3870659) B3870659
theorem B3440585 : Blo 2293435 3440585 := bstep (se 2 (by rfl) ⟨1290219, by rfl⟩ : syracuseStep 3440585 = 2580439) B2580439
theorem B2293723 : Blo 2293435 2293723 := bstep (se 1 (by rfl) ⟨1720292, by rfl⟩ : syracuseStep 2293723 = 3440585) B3440585
theorem B6531749 : Blo 2293435 6531749 := bbase (se 4 (by rfl) ⟨612351, by rfl⟩ : syracuseStep 6531749 = 1224703) (by norm_num)
theorem B4354499 : Blo 2293435 4354499 := bstep (se 1 (by rfl) ⟨3265874, by rfl⟩ : syracuseStep 4354499 = 6531749) B6531749
theorem B11611997 : Blo 2293435 11611997 := bstep (se 3 (by rfl) ⟨2177249, by rfl⟩ : syracuseStep 11611997 = 4354499) B4354499
theorem B7741331 : Blo 2293435 7741331 := bstep (se 1 (by rfl) ⟨5805998, by rfl⟩ : syracuseStep 7741331 = 11611997) B11611997
theorem B5160887 : Blo 2293435 5160887 := bstep (se 1 (by rfl) ⟨3870665, by rfl⟩ : syracuseStep 5160887 = 7741331) B7741331
theorem B3440591 : Blo 2293435 3440591 := bstep (se 1 (by rfl) ⟨2580443, by rfl⟩ : syracuseStep 3440591 = 5160887) B5160887
theorem B2293727 : Blo 2293435 2293727 := bstep (se 1 (by rfl) ⟨1720295, by rfl⟩ : syracuseStep 2293727 = 3440591) B3440591
theorem B3440597 : Blo 2293435 3440597 := bbase (se 7 (by rfl) ⟨40319, by rfl⟩ : syracuseStep 3440597 = 80639) (by norm_num)
theorem B2293731 : Blo 2293435 2293731 := bstep (se 1 (by rfl) ⟨1720298, by rfl⟩ : syracuseStep 2293731 = 3440597) B3440597
theorem B8709029 : Blo 2293435 8709029 := bbase (se 4 (by rfl) ⟨816471, by rfl⟩ : syracuseStep 8709029 = 1632943) (by norm_num)
theorem B5806019 : Blo 2293435 5806019 := bstep (se 1 (by rfl) ⟨4354514, by rfl⟩ : syracuseStep 5806019 = 8709029) B8709029
theorem B3870679 : Blo 2293435 3870679 := bstep (se 1 (by rfl) ⟨2903009, by rfl⟩ : syracuseStep 3870679 = 5806019) B5806019
theorem B5160905 : Blo 2293435 5160905 := bstep (se 2 (by rfl) ⟨1935339, by rfl⟩ : syracuseStep 5160905 = 3870679) B3870679
theorem B3440603 : Blo 2293435 3440603 := bstep (se 1 (by rfl) ⟨2580452, by rfl⟩ : syracuseStep 3440603 = 5160905) B5160905
theorem B2293735 : Blo 2293435 2293735 := bstep (se 1 (by rfl) ⟨1720301, by rfl⟩ : syracuseStep 2293735 = 3440603) B3440603
theorem B2580457 : Blo 2293435 2580457 := bbase (se 2 (by rfl) ⟨967671, by rfl⟩ : syracuseStep 2580457 = 1935343) (by norm_num)
theorem B3440609 : Blo 2293435 3440609 := bstep (se 2 (by rfl) ⟨1290228, by rfl⟩ : syracuseStep 3440609 = 2580457) B2580457
theorem B2293739 : Blo 2293435 2293739 := bstep (se 1 (by rfl) ⟨1720304, by rfl⟩ : syracuseStep 2293739 = 3440609) B3440609
theorem B8266805 : Blo 2293435 8266805 := bbase (se 5 (by rfl) ⟨387506, by rfl⟩ : syracuseStep 8266805 = 775013) (by norm_num)
theorem B5511203 : Blo 2293435 5511203 := bstep (se 1 (by rfl) ⟨4133402, by rfl⟩ : syracuseStep 5511203 = 8266805) B8266805
theorem B3674135 : Blo 2293435 3674135 := bstep (se 1 (by rfl) ⟨2755601, by rfl⟩ : syracuseStep 3674135 = 5511203) B5511203
theorem B2449423 : Blo 2293435 2449423 := bstep (se 1 (by rfl) ⟨1837067, by rfl⟩ : syracuseStep 2449423 = 3674135) B3674135
theorem B13063589 : Blo 2293435 13063589 := bstep (se 4 (by rfl) ⟨1224711, by rfl⟩ : syracuseStep 13063589 = 2449423) B2449423
theorem B8709059 : Blo 2293435 8709059 := bstep (se 1 (by rfl) ⟨6531794, by rfl⟩ : syracuseStep 8709059 = 13063589) B13063589
theorem B5806039 : Blo 2293435 5806039 := bstep (se 1 (by rfl) ⟨4354529, by rfl⟩ : syracuseStep 5806039 = 8709059) B8709059
theorem B7741385 : Blo 2293435 7741385 := bstep (se 2 (by rfl) ⟨2903019, by rfl⟩ : syracuseStep 7741385 = 5806039) B5806039
theorem B5160923 : Blo 2293435 5160923 := bstep (se 1 (by rfl) ⟨3870692, by rfl⟩ : syracuseStep 5160923 = 7741385) B7741385
theorem B3440615 : Blo 2293435 3440615 := bstep (se 1 (by rfl) ⟨2580461, by rfl⟩ : syracuseStep 3440615 = 5160923) B5160923
theorem B2293743 : Blo 2293435 2293743 := bstep (se 1 (by rfl) ⟨1720307, by rfl⟩ : syracuseStep 2293743 = 3440615) B3440615
theorem B3440621 : Blo 2293435 3440621 := bbase (se 3 (by rfl) ⟨645116, by rfl⟩ : syracuseStep 3440621 = 1290233) (by norm_num)
theorem B2293747 : Blo 2293435 2293747 := bstep (se 1 (by rfl) ⟨1720310, by rfl⟩ : syracuseStep 2293747 = 3440621) B3440621
theorem B5160941 : Blo 2293435 5160941 := bbase (se 3 (by rfl) ⟨967676, by rfl⟩ : syracuseStep 5160941 = 1935353) (by norm_num)
theorem B3440627 : Blo 2293435 3440627 := bstep (se 1 (by rfl) ⟨2580470, by rfl⟩ : syracuseStep 3440627 = 5160941) B5160941
theorem B2293751 : Blo 2293435 2293751 := bstep (se 1 (by rfl) ⟨1720313, by rfl⟩ : syracuseStep 2293751 = 3440627) B3440627
theorem B3100069 : Blo 2293435 3100069 := bbase (se 4 (by rfl) ⟨290631, by rfl⟩ : syracuseStep 3100069 = 581263) (by norm_num)
theorem B4133425 : Blo 2293435 4133425 := bstep (se 2 (by rfl) ⟨1550034, by rfl⟩ : syracuseStep 4133425 = 3100069) B3100069
theorem B5511233 : Blo 2293435 5511233 := bstep (se 2 (by rfl) ⟨2066712, by rfl⟩ : syracuseStep 5511233 = 4133425) B4133425
theorem B3674155 : Blo 2293435 3674155 := bstep (se 1 (by rfl) ⟨2755616, by rfl⟩ : syracuseStep 3674155 = 5511233) B5511233
theorem B4898873 : Blo 2293435 4898873 := bstep (se 2 (by rfl) ⟨1837077, by rfl⟩ : syracuseStep 4898873 = 3674155) B3674155
theorem B3265915 : Blo 2293435 3265915 := bstep (se 1 (by rfl) ⟨2449436, by rfl⟩ : syracuseStep 3265915 = 4898873) B4898873
theorem B4354553 : Blo 2293435 4354553 := bstep (se 2 (by rfl) ⟨1632957, by rfl⟩ : syracuseStep 4354553 = 3265915) B3265915
theorem B2903035 : Blo 2293435 2903035 := bstep (se 1 (by rfl) ⟨2177276, by rfl⟩ : syracuseStep 2903035 = 4354553) B4354553
theorem B3870713 : Blo 2293435 3870713 := bstep (se 2 (by rfl) ⟨1451517, by rfl⟩ : syracuseStep 3870713 = 2903035) B2903035
theorem B2580475 : Blo 2293435 2580475 := bstep (se 1 (by rfl) ⟨1935356, by rfl⟩ : syracuseStep 2580475 = 3870713) B3870713
theorem B3440633 : Blo 2293435 3440633 := bstep (se 2 (by rfl) ⟨1290237, by rfl⟩ : syracuseStep 3440633 = 2580475) B2580475
theorem B2293755 : Blo 2293435 2293755 := bstep (se 1 (by rfl) ⟨1720316, by rfl⟩ : syracuseStep 2293755 = 3440633) B3440633
theorem B5375093 : Blo 2293435 5375093 := bbase (se 5 (by rfl) ⟨251957, by rfl⟩ : syracuseStep 5375093 = 503915) (by norm_num)
theorem B14333581 : Blo 2293435 14333581 := bstep (se 3 (by rfl) ⟨2687546, by rfl⟩ : syracuseStep 14333581 = 5375093) B5375093
theorem B19111441 : Blo 2293435 19111441 := bstep (se 2 (by rfl) ⟨7166790, by rfl⟩ : syracuseStep 19111441 = 14333581) B14333581
theorem B407710741 : Blo 2293435 407710741 := bstep (se 6 (by rfl) ⟨9555720, by rfl⟩ : syracuseStep 407710741 = 19111441) B19111441
theorem B543614321 : Blo 2293435 543614321 := bstep (se 2 (by rfl) ⟨203855370, by rfl⟩ : syracuseStep 543614321 = 407710741) B407710741
theorem B362409547 : Blo 2293435 362409547 := bstep (se 1 (by rfl) ⟨271807160, by rfl⟩ : syracuseStep 362409547 = 543614321) B543614321
theorem B483212729 : Blo 2293435 483212729 := bstep (se 2 (by rfl) ⟨181204773, by rfl⟩ : syracuseStep 483212729 = 362409547) B362409547
theorem B322141819 : Blo 2293435 322141819 := bstep (se 1 (by rfl) ⟨241606364, by rfl⟩ : syracuseStep 322141819 = 483212729) B483212729
theorem B429522425 : Blo 2293435 429522425 := bstep (se 2 (by rfl) ⟨161070909, by rfl⟩ : syracuseStep 429522425 = 322141819) B322141819
theorem B286348283 : Blo 2293435 286348283 := bstep (se 1 (by rfl) ⟨214761212, by rfl⟩ : syracuseStep 286348283 = 429522425) B429522425
theorem B190898855 : Blo 2293435 190898855 := bstep (se 1 (by rfl) ⟨143174141, by rfl⟩ : syracuseStep 190898855 = 286348283) B286348283
theorem B127265903 : Blo 2293435 127265903 := bstep (se 1 (by rfl) ⟨95449427, by rfl⟩ : syracuseStep 127265903 = 190898855) B190898855
theorem B84843935 : Blo 2293435 84843935 := bstep (se 1 (by rfl) ⟨63632951, by rfl⟩ : syracuseStep 84843935 = 127265903) B127265903
theorem B56562623 : Blo 2293435 56562623 := bstep (se 1 (by rfl) ⟨42421967, by rfl⟩ : syracuseStep 56562623 = 84843935) B84843935
theorem B37708415 : Blo 2293435 37708415 := bstep (se 1 (by rfl) ⟨28281311, by rfl⟩ : syracuseStep 37708415 = 56562623) B56562623
theorem B25138943 : Blo 2293435 25138943 := bstep (se 1 (by rfl) ⟨18854207, by rfl⟩ : syracuseStep 25138943 = 37708415) B37708415
theorem B16759295 : Blo 2293435 16759295 := bstep (se 1 (by rfl) ⟨12569471, by rfl⟩ : syracuseStep 16759295 = 25138943) B25138943
theorem B11172863 : Blo 2293435 11172863 := bstep (se 1 (by rfl) ⟨8379647, by rfl⟩ : syracuseStep 11172863 = 16759295) B16759295
theorem B29794301 : Blo 2293435 29794301 := bstep (se 3 (by rfl) ⟨5586431, by rfl⟩ : syracuseStep 29794301 = 11172863) B11172863
theorem B19862867 : Blo 2293435 19862867 := bstep (se 1 (by rfl) ⟨14897150, by rfl⟩ : syracuseStep 19862867 = 29794301) B29794301
theorem B52967645 : Blo 2293435 52967645 := bstep (se 3 (by rfl) ⟨9931433, by rfl⟩ : syracuseStep 52967645 = 19862867) B19862867
theorem B564988213 : Blo 2293435 564988213 := bstep (se 5 (by rfl) ⟨26483822, by rfl⟩ : syracuseStep 564988213 = 52967645) B52967645
theorem B753317617 : Blo 2293435 753317617 := bstep (se 2 (by rfl) ⟨282494106, by rfl⟩ : syracuseStep 753317617 = 564988213) B564988213
theorem B1004423489 : Blo 2293435 1004423489 := bstep (se 2 (by rfl) ⟨376658808, by rfl⟩ : syracuseStep 1004423489 = 753317617) B753317617
theorem B669615659 : Blo 2293435 669615659 := bstep (se 1 (by rfl) ⟨502211744, by rfl⟩ : syracuseStep 669615659 = 1004423489) B1004423489
theorem B446410439 : Blo 2293435 446410439 := bstep (se 1 (by rfl) ⟨334807829, by rfl⟩ : syracuseStep 446410439 = 669615659) B669615659
theorem B297606959 : Blo 2293435 297606959 := bstep (se 1 (by rfl) ⟨223205219, by rfl⟩ : syracuseStep 297606959 = 446410439) B446410439
theorem B198404639 : Blo 2293435 198404639 := bstep (se 1 (by rfl) ⟨148803479, by rfl⟩ : syracuseStep 198404639 = 297606959) B297606959
theorem B132269759 : Blo 2293435 132269759 := bstep (se 1 (by rfl) ⟨99202319, by rfl⟩ : syracuseStep 132269759 = 198404639) B198404639
theorem B88179839 : Blo 2293435 88179839 := bstep (se 1 (by rfl) ⟨66134879, by rfl⟩ : syracuseStep 88179839 = 132269759) B132269759
theorem B58786559 : Blo 2293435 58786559 := bstep (se 1 (by rfl) ⟨44089919, by rfl⟩ : syracuseStep 58786559 = 88179839) B88179839
theorem B39191039 : Blo 2293435 39191039 := bstep (se 1 (by rfl) ⟨29393279, by rfl⟩ : syracuseStep 39191039 = 58786559) B58786559
theorem B26127359 : Blo 2293435 26127359 := bstep (se 1 (by rfl) ⟨19595519, by rfl⟩ : syracuseStep 26127359 = 39191039) B39191039
theorem B17418239 : Blo 2293435 17418239 := bstep (se 1 (by rfl) ⟨13063679, by rfl⟩ : syracuseStep 17418239 = 26127359) B26127359
theorem B11612159 : Blo 2293435 11612159 := bstep (se 1 (by rfl) ⟨8709119, by rfl⟩ : syracuseStep 11612159 = 17418239) B17418239
theorem B7741439 : Blo 2293435 7741439 := bstep (se 1 (by rfl) ⟨5806079, by rfl⟩ : syracuseStep 7741439 = 11612159) B11612159
theorem B5160959 : Blo 2293435 5160959 := bstep (se 1 (by rfl) ⟨3870719, by rfl⟩ : syracuseStep 5160959 = 7741439) B7741439
theorem B3440639 : Blo 2293435 3440639 := bstep (se 1 (by rfl) ⟨2580479, by rfl⟩ : syracuseStep 3440639 = 5160959) B5160959
theorem B2293759 : Blo 2293435 2293759 := bstep (se 1 (by rfl) ⟨1720319, by rfl⟩ : syracuseStep 2293759 = 3440639) B3440639
theorem B3440645 : Blo 2293435 3440645 := bbase (se 4 (by rfl) ⟨322560, by rfl⟩ : syracuseStep 3440645 = 645121) (by norm_num)
theorem B2293763 : Blo 2293435 2293763 := bstep (se 1 (by rfl) ⟨1720322, by rfl⟩ : syracuseStep 2293763 = 3440645) B3440645
theorem B3870733 : Blo 2293435 3870733 := bbase (se 3 (by rfl) ⟨725762, by rfl⟩ : syracuseStep 3870733 = 1451525) (by norm_num)
theorem B5160977 : Blo 2293435 5160977 := bstep (se 2 (by rfl) ⟨1935366, by rfl⟩ : syracuseStep 5160977 = 3870733) B3870733
theorem B3440651 : Blo 2293435 3440651 := bstep (se 1 (by rfl) ⟨2580488, by rfl⟩ : syracuseStep 3440651 = 5160977) B5160977
theorem B2293767 : Blo 2293435 2293767 := bstep (se 1 (by rfl) ⟨1720325, by rfl⟩ : syracuseStep 2293767 = 3440651) B3440651
theorem B2580493 : Blo 2293435 2580493 := bbase (se 3 (by rfl) ⟨483842, by rfl⟩ : syracuseStep 2580493 = 967685) (by norm_num)
theorem B3440657 : Blo 2293435 3440657 := bstep (se 2 (by rfl) ⟨1290246, by rfl⟩ : syracuseStep 3440657 = 2580493) B2580493
theorem B2293771 : Blo 2293435 2293771 := bstep (se 1 (by rfl) ⟨1720328, by rfl⟩ : syracuseStep 2293771 = 3440657) B3440657
theorem B7741493 : Blo 2293435 7741493 := bbase (se 5 (by rfl) ⟨362882, by rfl⟩ : syracuseStep 7741493 = 725765) (by norm_num)
theorem B5160995 : Blo 2293435 5160995 := bstep (se 1 (by rfl) ⟨3870746, by rfl⟩ : syracuseStep 5160995 = 7741493) B7741493
theorem B3440663 : Blo 2293435 3440663 := bstep (se 1 (by rfl) ⟨2580497, by rfl⟩ : syracuseStep 3440663 = 5160995) B5160995
theorem B2293775 : Blo 2293435 2293775 := bstep (se 1 (by rfl) ⟨1720331, by rfl⟩ : syracuseStep 2293775 = 3440663) B3440663
theorem B3440669 : Blo 2293435 3440669 := bbase (se 3 (by rfl) ⟨645125, by rfl⟩ : syracuseStep 3440669 = 1290251) (by norm_num)
theorem B2293779 : Blo 2293435 2293779 := bstep (se 1 (by rfl) ⟨1720334, by rfl⟩ : syracuseStep 2293779 = 3440669) B3440669
theorem B5161013 : Blo 2293435 5161013 := bbase (se 5 (by rfl) ⟨241922, by rfl⟩ : syracuseStep 5161013 = 483845) (by norm_num)
theorem B3440675 : Blo 2293435 3440675 := bstep (se 1 (by rfl) ⟨2580506, by rfl⟩ : syracuseStep 3440675 = 5161013) B5161013
theorem B2293783 : Blo 2293435 2293783 := bstep (se 1 (by rfl) ⟨1720337, by rfl⟩ : syracuseStep 2293783 = 3440675) B3440675
theorem B4965781 : Blo 2293435 4965781 := bbase (se 6 (by rfl) ⟨116385, by rfl⟩ : syracuseStep 4965781 = 232771) (by norm_num)
theorem B6621041 : Blo 2293435 6621041 := bstep (se 2 (by rfl) ⟨2482890, by rfl⟩ : syracuseStep 6621041 = 4965781) B4965781
theorem B4414027 : Blo 2293435 4414027 := bstep (se 1 (by rfl) ⟨3310520, by rfl⟩ : syracuseStep 4414027 = 6621041) B6621041
theorem B5885369 : Blo 2293435 5885369 := bstep (se 2 (by rfl) ⟨2207013, by rfl⟩ : syracuseStep 5885369 = 4414027) B4414027
theorem B3923579 : Blo 2293435 3923579 := bstep (se 1 (by rfl) ⟨2942684, by rfl⟩ : syracuseStep 3923579 = 5885369) B5885369
theorem B10462877 : Blo 2293435 10462877 := bstep (se 3 (by rfl) ⟨1961789, by rfl⟩ : syracuseStep 10462877 = 3923579) B3923579
theorem B6975251 : Blo 2293435 6975251 := bstep (se 1 (by rfl) ⟨5231438, by rfl⟩ : syracuseStep 6975251 = 10462877) B10462877
theorem B4650167 : Blo 2293435 4650167 := bstep (se 1 (by rfl) ⟨3487625, by rfl⟩ : syracuseStep 4650167 = 6975251) B6975251
theorem B12400445 : Blo 2293435 12400445 := bstep (se 3 (by rfl) ⟨2325083, by rfl⟩ : syracuseStep 12400445 = 4650167) B4650167
theorem B8266963 : Blo 2293435 8266963 := bstep (se 1 (by rfl) ⟨6200222, by rfl⟩ : syracuseStep 8266963 = 12400445) B12400445
theorem B11022617 : Blo 2293435 11022617 := bstep (se 2 (by rfl) ⟨4133481, by rfl⟩ : syracuseStep 11022617 = 8266963) B8266963
theorem B7348411 : Blo 2293435 7348411 := bstep (se 1 (by rfl) ⟨5511308, by rfl⟩ : syracuseStep 7348411 = 11022617) B11022617
theorem B9797881 : Blo 2293435 9797881 := bstep (se 2 (by rfl) ⟨3674205, by rfl⟩ : syracuseStep 9797881 = 7348411) B7348411
theorem B13063841 : Blo 2293435 13063841 := bstep (se 2 (by rfl) ⟨4898940, by rfl⟩ : syracuseStep 13063841 = 9797881) B9797881
theorem B8709227 : Blo 2293435 8709227 := bstep (se 1 (by rfl) ⟨6531920, by rfl⟩ : syracuseStep 8709227 = 13063841) B13063841
theorem B5806151 : Blo 2293435 5806151 := bstep (se 1 (by rfl) ⟨4354613, by rfl⟩ : syracuseStep 5806151 = 8709227) B8709227
theorem B3870767 : Blo 2293435 3870767 := bstep (se 1 (by rfl) ⟨2903075, by rfl⟩ : syracuseStep 3870767 = 5806151) B5806151
theorem B2580511 : Blo 2293435 2580511 := bstep (se 1 (by rfl) ⟨1935383, by rfl⟩ : syracuseStep 2580511 = 3870767) B3870767
theorem B3440681 : Blo 2293435 3440681 := bstep (se 2 (by rfl) ⟨1290255, by rfl⟩ : syracuseStep 3440681 = 2580511) B2580511
theorem B2293787 : Blo 2293435 2293787 := bstep (se 1 (by rfl) ⟨1720340, by rfl⟩ : syracuseStep 2293787 = 3440681) B3440681
theorem B11770757 : Blo 2293435 11770757 := bbase (se 4 (by rfl) ⟨1103508, by rfl⟩ : syracuseStep 11770757 = 2207017) (by norm_num)
theorem B7847171 : Blo 2293435 7847171 := bstep (se 1 (by rfl) ⟨5885378, by rfl⟩ : syracuseStep 7847171 = 11770757) B11770757
theorem B5231447 : Blo 2293435 5231447 := bstep (se 1 (by rfl) ⟨3923585, by rfl⟩ : syracuseStep 5231447 = 7847171) B7847171
theorem B3487631 : Blo 2293435 3487631 := bstep (se 1 (by rfl) ⟨2615723, by rfl⟩ : syracuseStep 3487631 = 5231447) B5231447
theorem B9300349 : Blo 2293435 9300349 := bstep (se 3 (by rfl) ⟨1743815, by rfl⟩ : syracuseStep 9300349 = 3487631) B3487631
theorem B12400465 : Blo 2293435 12400465 := bstep (se 2 (by rfl) ⟨4650174, by rfl⟩ : syracuseStep 12400465 = 9300349) B9300349
theorem B16533953 : Blo 2293435 16533953 := bstep (se 2 (by rfl) ⟨6200232, by rfl⟩ : syracuseStep 16533953 = 12400465) B12400465
theorem B11022635 : Blo 2293435 11022635 := bstep (se 1 (by rfl) ⟨8266976, by rfl⟩ : syracuseStep 11022635 = 16533953) B16533953
theorem B7348423 : Blo 2293435 7348423 := bstep (se 1 (by rfl) ⟨5511317, by rfl⟩ : syracuseStep 7348423 = 11022635) B11022635
theorem B9797897 : Blo 2293435 9797897 := bstep (se 2 (by rfl) ⟨3674211, by rfl⟩ : syracuseStep 9797897 = 7348423) B7348423
theorem B6531931 : Blo 2293435 6531931 := bstep (se 1 (by rfl) ⟨4898948, by rfl⟩ : syracuseStep 6531931 = 9797897) B9797897
theorem B8709241 : Blo 2293435 8709241 := bstep (se 2 (by rfl) ⟨3265965, by rfl⟩ : syracuseStep 8709241 = 6531931) B6531931
theorem B11612321 : Blo 2293435 11612321 := bstep (se 2 (by rfl) ⟨4354620, by rfl⟩ : syracuseStep 11612321 = 8709241) B8709241
theorem B7741547 : Blo 2293435 7741547 := bstep (se 1 (by rfl) ⟨5806160, by rfl⟩ : syracuseStep 7741547 = 11612321) B11612321
theorem B5161031 : Blo 2293435 5161031 := bstep (se 1 (by rfl) ⟨3870773, by rfl⟩ : syracuseStep 5161031 = 7741547) B7741547
theorem B3440687 : Blo 2293435 3440687 := bstep (se 1 (by rfl) ⟨2580515, by rfl⟩ : syracuseStep 3440687 = 5161031) B5161031
theorem B2293791 : Blo 2293435 2293791 := bstep (se 1 (by rfl) ⟨1720343, by rfl⟩ : syracuseStep 2293791 = 3440687) B3440687
theorem B3440693 : Blo 2293435 3440693 := bbase (se 5 (by rfl) ⟨161282, by rfl⟩ : syracuseStep 3440693 = 322565) (by norm_num)
theorem B2293795 : Blo 2293435 2293795 := bstep (se 1 (by rfl) ⟨1720346, by rfl⟩ : syracuseStep 2293795 = 3440693) B3440693
theorem B5806181 : Blo 2293435 5806181 := bbase (se 4 (by rfl) ⟨544329, by rfl⟩ : syracuseStep 5806181 = 1088659) (by norm_num)
theorem B3870787 : Blo 2293435 3870787 := bstep (se 1 (by rfl) ⟨2903090, by rfl⟩ : syracuseStep 3870787 = 5806181) B5806181
theorem B5161049 : Blo 2293435 5161049 := bstep (se 2 (by rfl) ⟨1935393, by rfl⟩ : syracuseStep 5161049 = 3870787) B3870787
theorem B3440699 : Blo 2293435 3440699 := bstep (se 1 (by rfl) ⟨2580524, by rfl⟩ : syracuseStep 3440699 = 5161049) B5161049
theorem B2293799 : Blo 2293435 2293799 := bstep (se 1 (by rfl) ⟨1720349, by rfl⟩ : syracuseStep 2293799 = 3440699) B3440699
theorem B2580529 : Blo 2293435 2580529 := bbase (se 2 (by rfl) ⟨967698, by rfl⟩ : syracuseStep 2580529 = 1935397) (by norm_num)
theorem B3440705 : Blo 2293435 3440705 := bstep (se 2 (by rfl) ⟨1290264, by rfl⟩ : syracuseStep 3440705 = 2580529) B2580529
theorem B2293803 : Blo 2293435 2293803 := bstep (se 1 (by rfl) ⟨1720352, by rfl⟩ : syracuseStep 2293803 = 3440705) B3440705
theorem B42422869 : Blo 2293435 42422869 := bbase (se 8 (by rfl) ⟨248571, by rfl⟩ : syracuseStep 42422869 = 497143) (by norm_num)
theorem B226255301 : Blo 2293435 226255301 := bstep (se 4 (by rfl) ⟨21211434, by rfl⟩ : syracuseStep 226255301 = 42422869) B42422869
theorem B150836867 : Blo 2293435 150836867 := bstep (se 1 (by rfl) ⟨113127650, by rfl⟩ : syracuseStep 150836867 = 226255301) B226255301
theorem B100557911 : Blo 2293435 100557911 := bstep (se 1 (by rfl) ⟨75418433, by rfl⟩ : syracuseStep 100557911 = 150836867) B150836867
theorem B67038607 : Blo 2293435 67038607 := bstep (se 1 (by rfl) ⟨50278955, by rfl⟩ : syracuseStep 67038607 = 100557911) B100557911
theorem B89384809 : Blo 2293435 89384809 := bstep (se 2 (by rfl) ⟨33519303, by rfl⟩ : syracuseStep 89384809 = 67038607) B67038607
theorem B119179745 : Blo 2293435 119179745 := bstep (se 2 (by rfl) ⟨44692404, by rfl⟩ : syracuseStep 119179745 = 89384809) B89384809
theorem B79453163 : Blo 2293435 79453163 := bstep (se 1 (by rfl) ⟨59589872, by rfl⟩ : syracuseStep 79453163 = 119179745) B119179745
theorem B52968775 : Blo 2293435 52968775 := bstep (se 1 (by rfl) ⟨39726581, by rfl⟩ : syracuseStep 52968775 = 79453163) B79453163
theorem B70625033 : Blo 2293435 70625033 := bstep (se 2 (by rfl) ⟨26484387, by rfl⟩ : syracuseStep 70625033 = 52968775) B52968775
theorem B47083355 : Blo 2293435 47083355 := bstep (se 1 (by rfl) ⟨35312516, by rfl⟩ : syracuseStep 47083355 = 70625033) B70625033
theorem B31388903 : Blo 2293435 31388903 := bstep (se 1 (by rfl) ⟨23541677, by rfl⟩ : syracuseStep 31388903 = 47083355) B47083355
theorem B20925935 : Blo 2293435 20925935 := bstep (se 1 (by rfl) ⟨15694451, by rfl⟩ : syracuseStep 20925935 = 31388903) B31388903
theorem B13950623 : Blo 2293435 13950623 := bstep (se 1 (by rfl) ⟨10462967, by rfl⟩ : syracuseStep 13950623 = 20925935) B20925935
theorem B9300415 : Blo 2293435 9300415 := bstep (se 1 (by rfl) ⟨6975311, by rfl⟩ : syracuseStep 9300415 = 13950623) B13950623
theorem B12400553 : Blo 2293435 12400553 := bstep (se 2 (by rfl) ⟨4650207, by rfl⟩ : syracuseStep 12400553 = 9300415) B9300415
theorem B8267035 : Blo 2293435 8267035 := bstep (se 1 (by rfl) ⟨6200276, by rfl⟩ : syracuseStep 8267035 = 12400553) B12400553
theorem B11022713 : Blo 2293435 11022713 := bstep (se 2 (by rfl) ⟨4133517, by rfl⟩ : syracuseStep 11022713 = 8267035) B8267035
theorem B7348475 : Blo 2293435 7348475 := bstep (se 1 (by rfl) ⟨5511356, by rfl⟩ : syracuseStep 7348475 = 11022713) B11022713
theorem B4898983 : Blo 2293435 4898983 := bstep (se 1 (by rfl) ⟨3674237, by rfl⟩ : syracuseStep 4898983 = 7348475) B7348475
theorem B6531977 : Blo 2293435 6531977 := bstep (se 2 (by rfl) ⟨2449491, by rfl⟩ : syracuseStep 6531977 = 4898983) B4898983
theorem B4354651 : Blo 2293435 4354651 := bstep (se 1 (by rfl) ⟨3265988, by rfl⟩ : syracuseStep 4354651 = 6531977) B6531977
theorem B5806201 : Blo 2293435 5806201 := bstep (se 2 (by rfl) ⟨2177325, by rfl⟩ : syracuseStep 5806201 = 4354651) B4354651
theorem B7741601 : Blo 2293435 7741601 := bstep (se 2 (by rfl) ⟨2903100, by rfl⟩ : syracuseStep 7741601 = 5806201) B5806201
theorem B5161067 : Blo 2293435 5161067 := bstep (se 1 (by rfl) ⟨3870800, by rfl⟩ : syracuseStep 5161067 = 7741601) B7741601
theorem B3440711 : Blo 2293435 3440711 := bstep (se 1 (by rfl) ⟨2580533, by rfl⟩ : syracuseStep 3440711 = 5161067) B5161067
theorem B2293807 : Blo 2293435 2293807 := bstep (se 1 (by rfl) ⟨1720355, by rfl⟩ : syracuseStep 2293807 = 3440711) B3440711
theorem B3440717 : Blo 2293435 3440717 := bbase (se 3 (by rfl) ⟨645134, by rfl⟩ : syracuseStep 3440717 = 1290269) (by norm_num)
theorem B2293811 : Blo 2293435 2293811 := bstep (se 1 (by rfl) ⟨1720358, by rfl⟩ : syracuseStep 2293811 = 3440717) B3440717
theorem B5161085 : Blo 2293435 5161085 := bbase (se 3 (by rfl) ⟨967703, by rfl⟩ : syracuseStep 5161085 = 1935407) (by norm_num)
theorem B3440723 : Blo 2293435 3440723 := bstep (se 1 (by rfl) ⟨2580542, by rfl⟩ : syracuseStep 3440723 = 5161085) B5161085
theorem B2293815 : Blo 2293435 2293815 := bstep (se 1 (by rfl) ⟨1720361, by rfl⟩ : syracuseStep 2293815 = 3440723) B3440723
theorem B3870821 : Blo 2293435 3870821 := bbase (se 4 (by rfl) ⟨362889, by rfl⟩ : syracuseStep 3870821 = 725779) (by norm_num)
theorem B2580547 : Blo 2293435 2580547 := bstep (se 1 (by rfl) ⟨1935410, by rfl⟩ : syracuseStep 2580547 = 3870821) B3870821
theorem B3440729 : Blo 2293435 3440729 := bstep (se 2 (by rfl) ⟨1290273, by rfl⟩ : syracuseStep 3440729 = 2580547) B2580547
theorem B2293819 : Blo 2293435 2293819 := bstep (se 1 (by rfl) ⟨1720364, by rfl⟩ : syracuseStep 2293819 = 3440729) B3440729
theorem B8267093 : Blo 2293435 8267093 := bbase (se 12 (by rfl) ⟨3027, by rfl⟩ : syracuseStep 8267093 = 6055) (by norm_num)
theorem B5511395 : Blo 2293435 5511395 := bstep (se 1 (by rfl) ⟨4133546, by rfl⟩ : syracuseStep 5511395 = 8267093) B8267093
theorem B3674263 : Blo 2293435 3674263 := bstep (se 1 (by rfl) ⟨2755697, by rfl⟩ : syracuseStep 3674263 = 5511395) B5511395
theorem B4899017 : Blo 2293435 4899017 := bstep (se 2 (by rfl) ⟨1837131, by rfl⟩ : syracuseStep 4899017 = 3674263) B3674263
theorem B3266011 : Blo 2293435 3266011 := bstep (se 1 (by rfl) ⟨2449508, by rfl⟩ : syracuseStep 3266011 = 4899017) B4899017
theorem B17418725 : Blo 2293435 17418725 := bstep (se 4 (by rfl) ⟨1633005, by rfl⟩ : syracuseStep 17418725 = 3266011) B3266011
theorem B11612483 : Blo 2293435 11612483 := bstep (se 1 (by rfl) ⟨8709362, by rfl⟩ : syracuseStep 11612483 = 17418725) B17418725
theorem B7741655 : Blo 2293435 7741655 := bstep (se 1 (by rfl) ⟨5806241, by rfl⟩ : syracuseStep 7741655 = 11612483) B11612483
theorem B5161103 : Blo 2293435 5161103 := bstep (se 1 (by rfl) ⟨3870827, by rfl⟩ : syracuseStep 5161103 = 7741655) B7741655
theorem B3440735 : Blo 2293435 3440735 := bstep (se 1 (by rfl) ⟨2580551, by rfl⟩ : syracuseStep 3440735 = 5161103) B5161103
theorem B2293823 : Blo 2293435 2293823 := bstep (se 1 (by rfl) ⟨1720367, by rfl⟩ : syracuseStep 2293823 = 3440735) B3440735
theorem B3440741 : Blo 2293435 3440741 := bbase (se 4 (by rfl) ⟨322569, by rfl⟩ : syracuseStep 3440741 = 645139) (by norm_num)
theorem B2293827 : Blo 2293435 2293827 := bstep (se 1 (by rfl) ⟨1720370, by rfl⟩ : syracuseStep 2293827 = 3440741) B3440741
theorem B3487693 : Blo 2293435 3487693 := bbase (se 3 (by rfl) ⟨653942, by rfl⟩ : syracuseStep 3487693 = 1307885) (by norm_num)
theorem B4650257 : Blo 2293435 4650257 := bstep (se 2 (by rfl) ⟨1743846, by rfl⟩ : syracuseStep 4650257 = 3487693) B3487693
theorem B12400685 : Blo 2293435 12400685 := bstep (se 3 (by rfl) ⟨2325128, by rfl⟩ : syracuseStep 12400685 = 4650257) B4650257
theorem B8267123 : Blo 2293435 8267123 := bstep (se 1 (by rfl) ⟨6200342, by rfl⟩ : syracuseStep 8267123 = 12400685) B12400685
theorem B5511415 : Blo 2293435 5511415 := bstep (se 1 (by rfl) ⟨4133561, by rfl⟩ : syracuseStep 5511415 = 8267123) B8267123
theorem B7348553 : Blo 2293435 7348553 := bstep (se 2 (by rfl) ⟨2755707, by rfl⟩ : syracuseStep 7348553 = 5511415) B5511415
theorem B4899035 : Blo 2293435 4899035 := bstep (se 1 (by rfl) ⟨3674276, by rfl⟩ : syracuseStep 4899035 = 7348553) B7348553
theorem B3266023 : Blo 2293435 3266023 := bstep (se 1 (by rfl) ⟨2449517, by rfl⟩ : syracuseStep 3266023 = 4899035) B4899035
theorem B4354697 : Blo 2293435 4354697 := bstep (se 2 (by rfl) ⟨1633011, by rfl⟩ : syracuseStep 4354697 = 3266023) B3266023
theorem B2903131 : Blo 2293435 2903131 := bstep (se 1 (by rfl) ⟨2177348, by rfl⟩ : syracuseStep 2903131 = 4354697) B4354697
theorem B3870841 : Blo 2293435 3870841 := bstep (se 2 (by rfl) ⟨1451565, by rfl⟩ : syracuseStep 3870841 = 2903131) B2903131
theorem B5161121 : Blo 2293435 5161121 := bstep (se 2 (by rfl) ⟨1935420, by rfl⟩ : syracuseStep 5161121 = 3870841) B3870841
theorem B3440747 : Blo 2293435 3440747 := bstep (se 1 (by rfl) ⟨2580560, by rfl⟩ : syracuseStep 3440747 = 5161121) B5161121
theorem B2293831 : Blo 2293435 2293831 := bstep (se 1 (by rfl) ⟨1720373, by rfl⟩ : syracuseStep 2293831 = 3440747) B3440747
theorem B2580565 : Blo 2293435 2580565 := bbase (se 8 (by rfl) ⟨15120, by rfl⟩ : syracuseStep 2580565 = 30241) (by norm_num)
theorem B3440753 : Blo 2293435 3440753 := bstep (se 2 (by rfl) ⟨1290282, by rfl⟩ : syracuseStep 3440753 = 2580565) B2580565
theorem B2293835 : Blo 2293435 2293835 := bstep (se 1 (by rfl) ⟨1720376, by rfl⟩ : syracuseStep 2293835 = 3440753) B3440753
theorem B2903141 : Blo 2293435 2903141 := bbase (se 4 (by rfl) ⟨272169, by rfl⟩ : syracuseStep 2903141 = 544339) (by norm_num)
theorem B7741709 : Blo 2293435 7741709 := bstep (se 3 (by rfl) ⟨1451570, by rfl⟩ : syracuseStep 7741709 = 2903141) B2903141
theorem B5161139 : Blo 2293435 5161139 := bstep (se 1 (by rfl) ⟨3870854, by rfl⟩ : syracuseStep 5161139 = 7741709) B7741709
theorem B3440759 : Blo 2293435 3440759 := bstep (se 1 (by rfl) ⟨2580569, by rfl⟩ : syracuseStep 3440759 = 5161139) B5161139
theorem B2293839 : Blo 2293435 2293839 := bstep (se 1 (by rfl) ⟨1720379, by rfl⟩ : syracuseStep 2293839 = 3440759) B3440759
theorem B3440765 : Blo 2293435 3440765 := bbase (se 3 (by rfl) ⟨645143, by rfl⟩ : syracuseStep 3440765 = 1290287) (by norm_num)
theorem B2293843 : Blo 2293435 2293843 := bstep (se 1 (by rfl) ⟨1720382, by rfl⟩ : syracuseStep 2293843 = 3440765) B3440765
theorem B5161157 : Blo 2293435 5161157 := bbase (se 4 (by rfl) ⟨483858, by rfl⟩ : syracuseStep 5161157 = 967717) (by norm_num)
theorem B3440771 : Blo 2293435 3440771 := bstep (se 1 (by rfl) ⟨2580578, by rfl⟩ : syracuseStep 3440771 = 5161157) B5161157
theorem B2293847 : Blo 2293435 2293847 := bstep (se 1 (by rfl) ⟨1720385, by rfl⟩ : syracuseStep 2293847 = 3440771) B3440771
theorem B4133597 : Blo 2293435 4133597 := bbase (se 3 (by rfl) ⟨775049, by rfl⟩ : syracuseStep 4133597 = 1550099) (by norm_num)
theorem B11022925 : Blo 2293435 11022925 := bstep (se 3 (by rfl) ⟨2066798, by rfl⟩ : syracuseStep 11022925 = 4133597) B4133597
theorem B14697233 : Blo 2293435 14697233 := bstep (se 2 (by rfl) ⟨5511462, by rfl⟩ : syracuseStep 14697233 = 11022925) B11022925
theorem B9798155 : Blo 2293435 9798155 := bstep (se 1 (by rfl) ⟨7348616, by rfl⟩ : syracuseStep 9798155 = 14697233) B14697233
theorem B6532103 : Blo 2293435 6532103 := bstep (se 1 (by rfl) ⟨4899077, by rfl⟩ : syracuseStep 6532103 = 9798155) B9798155
theorem B4354735 : Blo 2293435 4354735 := bstep (se 1 (by rfl) ⟨3266051, by rfl⟩ : syracuseStep 4354735 = 6532103) B6532103
theorem B5806313 : Blo 2293435 5806313 := bstep (se 2 (by rfl) ⟨2177367, by rfl⟩ : syracuseStep 5806313 = 4354735) B4354735
theorem B3870875 : Blo 2293435 3870875 := bstep (se 1 (by rfl) ⟨2903156, by rfl⟩ : syracuseStep 3870875 = 5806313) B5806313
theorem B2580583 : Blo 2293435 2580583 := bstep (se 1 (by rfl) ⟨1935437, by rfl⟩ : syracuseStep 2580583 = 3870875) B3870875
theorem B3440777 : Blo 2293435 3440777 := bstep (se 2 (by rfl) ⟨1290291, by rfl⟩ : syracuseStep 3440777 = 2580583) B2580583
theorem B2293851 : Blo 2293435 2293851 := bstep (se 1 (by rfl) ⟨1720388, by rfl⟩ : syracuseStep 2293851 = 3440777) B3440777
theorem B11612645 : Blo 2293435 11612645 := bbase (se 4 (by rfl) ⟨1088685, by rfl⟩ : syracuseStep 11612645 = 2177371) (by norm_num)
theorem B7741763 : Blo 2293435 7741763 := bstep (se 1 (by rfl) ⟨5806322, by rfl⟩ : syracuseStep 7741763 = 11612645) B11612645
theorem B5161175 : Blo 2293435 5161175 := bstep (se 1 (by rfl) ⟨3870881, by rfl⟩ : syracuseStep 5161175 = 7741763) B7741763
theorem B3440783 : Blo 2293435 3440783 := bstep (se 1 (by rfl) ⟨2580587, by rfl⟩ : syracuseStep 3440783 = 5161175) B5161175
theorem B2293855 : Blo 2293435 2293855 := bstep (se 1 (by rfl) ⟨1720391, by rfl⟩ : syracuseStep 2293855 = 3440783) B3440783
theorem B3440789 : Blo 2293435 3440789 := bbase (se 6 (by rfl) ⟨80643, by rfl⟩ : syracuseStep 3440789 = 161287) (by norm_num)
theorem B2293859 : Blo 2293435 2293859 := bstep (se 1 (by rfl) ⟨1720394, by rfl⟩ : syracuseStep 2293859 = 3440789) B3440789
theorem B8267237 : Blo 2293435 8267237 := bbase (se 4 (by rfl) ⟨775053, by rfl⟩ : syracuseStep 8267237 = 1550107) (by norm_num)
theorem B5511491 : Blo 2293435 5511491 := bstep (se 1 (by rfl) ⟨4133618, by rfl⟩ : syracuseStep 5511491 = 8267237) B8267237
theorem B3674327 : Blo 2293435 3674327 := bstep (se 1 (by rfl) ⟨2755745, by rfl⟩ : syracuseStep 3674327 = 5511491) B5511491
theorem B9798205 : Blo 2293435 9798205 := bstep (se 3 (by rfl) ⟨1837163, by rfl⟩ : syracuseStep 9798205 = 3674327) B3674327
theorem B13064273 : Blo 2293435 13064273 := bstep (se 2 (by rfl) ⟨4899102, by rfl⟩ : syracuseStep 13064273 = 9798205) B9798205
theorem B8709515 : Blo 2293435 8709515 := bstep (se 1 (by rfl) ⟨6532136, by rfl⟩ : syracuseStep 8709515 = 13064273) B13064273
theorem B5806343 : Blo 2293435 5806343 := bstep (se 1 (by rfl) ⟨4354757, by rfl⟩ : syracuseStep 5806343 = 8709515) B8709515
theorem B3870895 : Blo 2293435 3870895 := bstep (se 1 (by rfl) ⟨2903171, by rfl⟩ : syracuseStep 3870895 = 5806343) B5806343
theorem B5161193 : Blo 2293435 5161193 := bstep (se 2 (by rfl) ⟨1935447, by rfl⟩ : syracuseStep 5161193 = 3870895) B3870895
theorem B3440795 : Blo 2293435 3440795 := bstep (se 1 (by rfl) ⟨2580596, by rfl⟩ : syracuseStep 3440795 = 5161193) B5161193
theorem B2293863 : Blo 2293435 2293863 := bstep (se 1 (by rfl) ⟨1720397, by rfl⟩ : syracuseStep 2293863 = 3440795) B3440795
theorem B2580601 : Blo 2293435 2580601 := bbase (se 2 (by rfl) ⟨967725, by rfl⟩ : syracuseStep 2580601 = 1935451) (by norm_num)
theorem B3440801 : Blo 2293435 3440801 := bstep (se 2 (by rfl) ⟨1290300, by rfl⟩ : syracuseStep 3440801 = 2580601) B2580601
theorem B2293867 : Blo 2293435 2293867 := bstep (se 1 (by rfl) ⟨1720400, by rfl⟩ : syracuseStep 2293867 = 3440801) B3440801
theorem B5231629 : Blo 2293435 5231629 := bbase (se 3 (by rfl) ⟨980930, by rfl⟩ : syracuseStep 5231629 = 1961861) (by norm_num)
theorem B6975505 : Blo 2293435 6975505 := bstep (se 2 (by rfl) ⟨2615814, by rfl⟩ : syracuseStep 6975505 = 5231629) B5231629
theorem B9300673 : Blo 2293435 9300673 := bstep (se 2 (by rfl) ⟨3487752, by rfl⟩ : syracuseStep 9300673 = 6975505) B6975505
theorem B49603589 : Blo 2293435 49603589 := bstep (se 4 (by rfl) ⟨4650336, by rfl⟩ : syracuseStep 49603589 = 9300673) B9300673
theorem B33069059 : Blo 2293435 33069059 := bstep (se 1 (by rfl) ⟨24801794, by rfl⟩ : syracuseStep 33069059 = 49603589) B49603589
theorem B22046039 : Blo 2293435 22046039 := bstep (se 1 (by rfl) ⟨16534529, by rfl⟩ : syracuseStep 22046039 = 33069059) B33069059
theorem B14697359 : Blo 2293435 14697359 := bstep (se 1 (by rfl) ⟨11023019, by rfl⟩ : syracuseStep 14697359 = 22046039) B22046039
theorem B9798239 : Blo 2293435 9798239 := bstep (se 1 (by rfl) ⟨7348679, by rfl⟩ : syracuseStep 9798239 = 14697359) B14697359
theorem B6532159 : Blo 2293435 6532159 := bstep (se 1 (by rfl) ⟨4899119, by rfl⟩ : syracuseStep 6532159 = 9798239) B9798239
theorem B8709545 : Blo 2293435 8709545 := bstep (se 2 (by rfl) ⟨3266079, by rfl⟩ : syracuseStep 8709545 = 6532159) B6532159
theorem B5806363 : Blo 2293435 5806363 := bstep (se 1 (by rfl) ⟨4354772, by rfl⟩ : syracuseStep 5806363 = 8709545) B8709545
theorem B7741817 : Blo 2293435 7741817 := bstep (se 2 (by rfl) ⟨2903181, by rfl⟩ : syracuseStep 7741817 = 5806363) B5806363
theorem B5161211 : Blo 2293435 5161211 := bstep (se 1 (by rfl) ⟨3870908, by rfl⟩ : syracuseStep 5161211 = 7741817) B7741817
theorem B3440807 : Blo 2293435 3440807 := bstep (se 1 (by rfl) ⟨2580605, by rfl⟩ : syracuseStep 3440807 = 5161211) B5161211
theorem B2293871 : Blo 2293435 2293871 := bstep (se 1 (by rfl) ⟨1720403, by rfl⟩ : syracuseStep 2293871 = 3440807) B3440807
theorem B3440813 : Blo 2293435 3440813 := bbase (se 3 (by rfl) ⟨645152, by rfl⟩ : syracuseStep 3440813 = 1290305) (by norm_num)
theorem B2293875 : Blo 2293435 2293875 := bstep (se 1 (by rfl) ⟨1720406, by rfl⟩ : syracuseStep 2293875 = 3440813) B3440813
theorem B5161229 : Blo 2293435 5161229 := bbase (se 3 (by rfl) ⟨967730, by rfl⟩ : syracuseStep 5161229 = 1935461) (by norm_num)
theorem B3440819 : Blo 2293435 3440819 := bstep (se 1 (by rfl) ⟨2580614, by rfl⟩ : syracuseStep 3440819 = 5161229) B5161229
theorem B2293879 : Blo 2293435 2293879 := bstep (se 1 (by rfl) ⟨1720409, by rfl⟩ : syracuseStep 2293879 = 3440819) B3440819
theorem B2903197 : Blo 2293435 2903197 := bbase (se 3 (by rfl) ⟨544349, by rfl⟩ : syracuseStep 2903197 = 1088699) (by norm_num)
theorem B3870929 : Blo 2293435 3870929 := bstep (se 2 (by rfl) ⟨1451598, by rfl⟩ : syracuseStep 3870929 = 2903197) B2903197
theorem B2580619 : Blo 2293435 2580619 := bstep (se 1 (by rfl) ⟨1935464, by rfl⟩ : syracuseStep 2580619 = 3870929) B3870929
theorem B3440825 : Blo 2293435 3440825 := bstep (se 2 (by rfl) ⟨1290309, by rfl⟩ : syracuseStep 3440825 = 2580619) B2580619
theorem B2293883 : Blo 2293435 2293883 := bstep (se 1 (by rfl) ⟨1720412, by rfl⟩ : syracuseStep 2293883 = 3440825) B3440825
theorem B3674365 : Blo 2293435 3674365 := bbase (se 3 (by rfl) ⟨688943, by rfl⟩ : syracuseStep 3674365 = 1377887) (by norm_num)
theorem B19596613 : Blo 2293435 19596613 := bstep (se 4 (by rfl) ⟨1837182, by rfl⟩ : syracuseStep 19596613 = 3674365) B3674365
theorem B26128817 : Blo 2293435 26128817 := bstep (se 2 (by rfl) ⟨9798306, by rfl⟩ : syracuseStep 26128817 = 19596613) B19596613
theorem B17419211 : Blo 2293435 17419211 := bstep (se 1 (by rfl) ⟨13064408, by rfl⟩ : syracuseStep 17419211 = 26128817) B26128817
theorem B11612807 : Blo 2293435 11612807 := bstep (se 1 (by rfl) ⟨8709605, by rfl⟩ : syracuseStep 11612807 = 17419211) B17419211
theorem B7741871 : Blo 2293435 7741871 := bstep (se 1 (by rfl) ⟨5806403, by rfl⟩ : syracuseStep 7741871 = 11612807) B11612807
theorem B5161247 : Blo 2293435 5161247 := bstep (se 1 (by rfl) ⟨3870935, by rfl⟩ : syracuseStep 5161247 = 7741871) B7741871
theorem B3440831 : Blo 2293435 3440831 := bstep (se 1 (by rfl) ⟨2580623, by rfl⟩ : syracuseStep 3440831 = 5161247) B5161247
theorem B2293887 : Blo 2293435 2293887 := bstep (se 1 (by rfl) ⟨1720415, by rfl⟩ : syracuseStep 2293887 = 3440831) B3440831
theorem B3440837 : Blo 2293435 3440837 := bbase (se 4 (by rfl) ⟨322578, by rfl⟩ : syracuseStep 3440837 = 645157) (by norm_num)
theorem B2293891 : Blo 2293435 2293891 := bstep (se 1 (by rfl) ⟨1720418, by rfl⟩ : syracuseStep 2293891 = 3440837) B3440837
theorem B3870949 : Blo 2293435 3870949 := bbase (se 4 (by rfl) ⟨362901, by rfl⟩ : syracuseStep 3870949 = 725803) (by norm_num)
theorem B5161265 : Blo 2293435 5161265 := bstep (se 2 (by rfl) ⟨1935474, by rfl⟩ : syracuseStep 5161265 = 3870949) B3870949
theorem B3440843 : Blo 2293435 3440843 := bstep (se 1 (by rfl) ⟨2580632, by rfl⟩ : syracuseStep 3440843 = 5161265) B5161265
theorem B2293895 : Blo 2293435 2293895 := bstep (se 1 (by rfl) ⟨1720421, by rfl⟩ : syracuseStep 2293895 = 3440843) B3440843
theorem B2580637 : Blo 2293435 2580637 := bbase (se 3 (by rfl) ⟨483869, by rfl⟩ : syracuseStep 2580637 = 967739) (by norm_num)
theorem B3440849 : Blo 2293435 3440849 := bstep (se 2 (by rfl) ⟨1290318, by rfl⟩ : syracuseStep 3440849 = 2580637) B2580637
theorem B2293899 : Blo 2293435 2293899 := bstep (se 1 (by rfl) ⟨1720424, by rfl⟩ : syracuseStep 2293899 = 3440849) B3440849
theorem B7741925 : Blo 2293435 7741925 := bbase (se 4 (by rfl) ⟨725805, by rfl⟩ : syracuseStep 7741925 = 1451611) (by norm_num)
theorem B5161283 : Blo 2293435 5161283 := bstep (se 1 (by rfl) ⟨3870962, by rfl⟩ : syracuseStep 5161283 = 7741925) B7741925
theorem B3440855 : Blo 2293435 3440855 := bstep (se 1 (by rfl) ⟨2580641, by rfl⟩ : syracuseStep 3440855 = 5161283) B5161283
theorem B2293903 : Blo 2293435 2293903 := bstep (se 1 (by rfl) ⟨1720427, by rfl⟩ : syracuseStep 2293903 = 3440855) B3440855
theorem B3440861 : Blo 2293435 3440861 := bbase (se 3 (by rfl) ⟨645161, by rfl⟩ : syracuseStep 3440861 = 1290323) (by norm_num)
theorem B2293907 : Blo 2293435 2293907 := bstep (se 1 (by rfl) ⟨1720430, by rfl⟩ : syracuseStep 2293907 = 3440861) B3440861
theorem B5161301 : Blo 2293435 5161301 := bbase (se 10 (by rfl) ⟨7560, by rfl⟩ : syracuseStep 5161301 = 15121) (by norm_num)
theorem B3440867 : Blo 2293435 3440867 := bstep (se 1 (by rfl) ⟨2580650, by rfl⟩ : syracuseStep 3440867 = 5161301) B5161301
theorem B2293911 : Blo 2293435 2293911 := bstep (se 1 (by rfl) ⟨1720433, by rfl⟩ : syracuseStep 2293911 = 3440867) B3440867
theorem B3100285 : Blo 2293435 3100285 := bbase (se 3 (by rfl) ⟨581303, by rfl⟩ : syracuseStep 3100285 = 1162607) (by norm_num)
theorem B4133713 : Blo 2293435 4133713 := bstep (se 2 (by rfl) ⟨1550142, by rfl⟩ : syracuseStep 4133713 = 3100285) B3100285
theorem B5511617 : Blo 2293435 5511617 := bstep (se 2 (by rfl) ⟨2066856, by rfl⟩ : syracuseStep 5511617 = 4133713) B4133713
theorem B3674411 : Blo 2293435 3674411 := bstep (se 1 (by rfl) ⟨2755808, by rfl⟩ : syracuseStep 3674411 = 5511617) B5511617
theorem B2449607 : Blo 2293435 2449607 := bstep (se 1 (by rfl) ⟨1837205, by rfl⟩ : syracuseStep 2449607 = 3674411) B3674411
theorem B6532285 : Blo 2293435 6532285 := bstep (se 3 (by rfl) ⟨1224803, by rfl⟩ : syracuseStep 6532285 = 2449607) B2449607
theorem B8709713 : Blo 2293435 8709713 := bstep (se 2 (by rfl) ⟨3266142, by rfl⟩ : syracuseStep 8709713 = 6532285) B6532285
theorem B5806475 : Blo 2293435 5806475 := bstep (se 1 (by rfl) ⟨4354856, by rfl⟩ : syracuseStep 5806475 = 8709713) B8709713
theorem B3870983 : Blo 2293435 3870983 := bstep (se 1 (by rfl) ⟨2903237, by rfl⟩ : syracuseStep 3870983 = 5806475) B5806475
theorem B2580655 : Blo 2293435 2580655 := bstep (se 1 (by rfl) ⟨1935491, by rfl⟩ : syracuseStep 2580655 = 3870983) B3870983
theorem B3440873 : Blo 2293435 3440873 := bstep (se 2 (by rfl) ⟨1290327, by rfl⟩ : syracuseStep 3440873 = 2580655) B2580655
theorem B2293915 : Blo 2293435 2293915 := bstep (se 1 (by rfl) ⟨1720436, by rfl⟩ : syracuseStep 2293915 = 3440873) B3440873
theorem B2325217 : Blo 2293435 2325217 := bbase (se 2 (by rfl) ⟨871956, by rfl⟩ : syracuseStep 2325217 = 1743913) (by norm_num)
theorem B3100289 : Blo 2293435 3100289 := bstep (se 2 (by rfl) ⟨1162608, by rfl⟩ : syracuseStep 3100289 = 2325217) B2325217
theorem B8267437 : Blo 2293435 8267437 := bstep (se 3 (by rfl) ⟨1550144, by rfl⟩ : syracuseStep 8267437 = 3100289) B3100289
theorem B44092997 : Blo 2293435 44092997 := bstep (se 4 (by rfl) ⟨4133718, by rfl⟩ : syracuseStep 44092997 = 8267437) B8267437
theorem B29395331 : Blo 2293435 29395331 := bstep (se 1 (by rfl) ⟨22046498, by rfl⟩ : syracuseStep 29395331 = 44092997) B44092997
theorem B19596887 : Blo 2293435 19596887 := bstep (se 1 (by rfl) ⟨14697665, by rfl⟩ : syracuseStep 19596887 = 29395331) B29395331
theorem B13064591 : Blo 2293435 13064591 := bstep (se 1 (by rfl) ⟨9798443, by rfl⟩ : syracuseStep 13064591 = 19596887) B19596887
theorem B8709727 : Blo 2293435 8709727 := bstep (se 1 (by rfl) ⟨6532295, by rfl⟩ : syracuseStep 8709727 = 13064591) B13064591
theorem B11612969 : Blo 2293435 11612969 := bstep (se 2 (by rfl) ⟨4354863, by rfl⟩ : syracuseStep 11612969 = 8709727) B8709727
theorem B7741979 : Blo 2293435 7741979 := bstep (se 1 (by rfl) ⟨5806484, by rfl⟩ : syracuseStep 7741979 = 11612969) B11612969
theorem B5161319 : Blo 2293435 5161319 := bstep (se 1 (by rfl) ⟨3870989, by rfl⟩ : syracuseStep 5161319 = 7741979) B7741979
theorem B3440879 : Blo 2293435 3440879 := bstep (se 1 (by rfl) ⟨2580659, by rfl⟩ : syracuseStep 3440879 = 5161319) B5161319
theorem B2293919 : Blo 2293435 2293919 := bstep (se 1 (by rfl) ⟨1720439, by rfl⟩ : syracuseStep 2293919 = 3440879) B3440879
theorem B3440885 : Blo 2293435 3440885 := bbase (se 5 (by rfl) ⟨161291, by rfl⟩ : syracuseStep 3440885 = 322583) (by norm_num)
theorem B2293923 : Blo 2293435 2293923 := bstep (se 1 (by rfl) ⟨1720442, by rfl⟩ : syracuseStep 2293923 = 3440885) B3440885
theorem B9300901 : Blo 2293435 9300901 := bbase (se 4 (by rfl) ⟨871959, by rfl⟩ : syracuseStep 9300901 = 1743919) (by norm_num)
theorem B12401201 : Blo 2293435 12401201 := bstep (se 2 (by rfl) ⟨4650450, by rfl⟩ : syracuseStep 12401201 = 9300901) B9300901
theorem B33069869 : Blo 2293435 33069869 := bstep (se 3 (by rfl) ⟨6200600, by rfl⟩ : syracuseStep 33069869 = 12401201) B12401201
theorem B22046579 : Blo 2293435 22046579 := bstep (se 1 (by rfl) ⟨16534934, by rfl⟩ : syracuseStep 22046579 = 33069869) B33069869
theorem B14697719 : Blo 2293435 14697719 := bstep (se 1 (by rfl) ⟨11023289, by rfl⟩ : syracuseStep 14697719 = 22046579) B22046579
theorem B9798479 : Blo 2293435 9798479 := bstep (se 1 (by rfl) ⟨7348859, by rfl⟩ : syracuseStep 9798479 = 14697719) B14697719
theorem B6532319 : Blo 2293435 6532319 := bstep (se 1 (by rfl) ⟨4899239, by rfl⟩ : syracuseStep 6532319 = 9798479) B9798479
theorem B4354879 : Blo 2293435 4354879 := bstep (se 1 (by rfl) ⟨3266159, by rfl⟩ : syracuseStep 4354879 = 6532319) B6532319
theorem B5806505 : Blo 2293435 5806505 := bstep (se 2 (by rfl) ⟨2177439, by rfl⟩ : syracuseStep 5806505 = 4354879) B4354879
theorem B3871003 : Blo 2293435 3871003 := bstep (se 1 (by rfl) ⟨2903252, by rfl⟩ : syracuseStep 3871003 = 5806505) B5806505
theorem B5161337 : Blo 2293435 5161337 := bstep (se 2 (by rfl) ⟨1935501, by rfl⟩ : syracuseStep 5161337 = 3871003) B3871003
theorem B3440891 : Blo 2293435 3440891 := bstep (se 1 (by rfl) ⟨2580668, by rfl⟩ : syracuseStep 3440891 = 5161337) B5161337
theorem B2293927 : Blo 2293435 2293927 := bstep (se 1 (by rfl) ⟨1720445, by rfl⟩ : syracuseStep 2293927 = 3440891) B3440891
theorem B2580673 : Blo 2293435 2580673 := bbase (se 2 (by rfl) ⟨967752, by rfl⟩ : syracuseStep 2580673 = 1935505) (by norm_num)
theorem B3440897 : Blo 2293435 3440897 := bstep (se 2 (by rfl) ⟨1290336, by rfl⟩ : syracuseStep 3440897 = 2580673) B2580673
theorem B2293931 : Blo 2293435 2293931 := bstep (se 1 (by rfl) ⟨1720448, by rfl⟩ : syracuseStep 2293931 = 3440897) B3440897
theorem B5806525 : Blo 2293435 5806525 := bbase (se 3 (by rfl) ⟨1088723, by rfl⟩ : syracuseStep 5806525 = 2177447) (by norm_num)
theorem B7742033 : Blo 2293435 7742033 := bstep (se 2 (by rfl) ⟨2903262, by rfl⟩ : syracuseStep 7742033 = 5806525) B5806525
theorem B5161355 : Blo 2293435 5161355 := bstep (se 1 (by rfl) ⟨3871016, by rfl⟩ : syracuseStep 5161355 = 7742033) B7742033
theorem B3440903 : Blo 2293435 3440903 := bstep (se 1 (by rfl) ⟨2580677, by rfl⟩ : syracuseStep 3440903 = 5161355) B5161355
theorem B2293935 : Blo 2293435 2293935 := bstep (se 1 (by rfl) ⟨1720451, by rfl⟩ : syracuseStep 2293935 = 3440903) B3440903
theorem B3440909 : Blo 2293435 3440909 := bbase (se 3 (by rfl) ⟨645170, by rfl⟩ : syracuseStep 3440909 = 1290341) (by norm_num)
theorem B2293939 : Blo 2293435 2293939 := bstep (se 1 (by rfl) ⟨1720454, by rfl⟩ : syracuseStep 2293939 = 3440909) B3440909
theorem B5161373 : Blo 2293435 5161373 := bbase (se 3 (by rfl) ⟨967757, by rfl⟩ : syracuseStep 5161373 = 1935515) (by norm_num)
theorem B3440915 : Blo 2293435 3440915 := bstep (se 1 (by rfl) ⟨2580686, by rfl⟩ : syracuseStep 3440915 = 5161373) B5161373
theorem B2293943 : Blo 2293435 2293943 := bstep (se 1 (by rfl) ⟨1720457, by rfl⟩ : syracuseStep 2293943 = 3440915) B3440915
theorem B3871037 : Blo 2293435 3871037 := bbase (se 3 (by rfl) ⟨725819, by rfl⟩ : syracuseStep 3871037 = 1451639) (by norm_num)
theorem B2580691 : Blo 2293435 2580691 := bstep (se 1 (by rfl) ⟨1935518, by rfl⟩ : syracuseStep 2580691 = 3871037) B3871037
theorem B3440921 : Blo 2293435 3440921 := bstep (se 2 (by rfl) ⟨1290345, by rfl⟩ : syracuseStep 3440921 = 2580691) B2580691
theorem B2293947 : Blo 2293435 2293947 := bstep (se 1 (by rfl) ⟨1720460, by rfl⟩ : syracuseStep 2293947 = 3440921) B3440921
theorem B2449645 : Blo 2293435 2449645 := bbase (se 3 (by rfl) ⟨459308, by rfl⟩ : syracuseStep 2449645 = 918617) (by norm_num)
theorem B13064773 : Blo 2293435 13064773 := bstep (se 4 (by rfl) ⟨1224822, by rfl⟩ : syracuseStep 13064773 = 2449645) B2449645
theorem B17419697 : Blo 2293435 17419697 := bstep (se 2 (by rfl) ⟨6532386, by rfl⟩ : syracuseStep 17419697 = 13064773) B13064773
theorem B11613131 : Blo 2293435 11613131 := bstep (se 1 (by rfl) ⟨8709848, by rfl⟩ : syracuseStep 11613131 = 17419697) B17419697
theorem B7742087 : Blo 2293435 7742087 := bstep (se 1 (by rfl) ⟨5806565, by rfl⟩ : syracuseStep 7742087 = 11613131) B11613131
theorem B5161391 : Blo 2293435 5161391 := bstep (se 1 (by rfl) ⟨3871043, by rfl⟩ : syracuseStep 5161391 = 7742087) B7742087
theorem B3440927 : Blo 2293435 3440927 := bstep (se 1 (by rfl) ⟨2580695, by rfl⟩ : syracuseStep 3440927 = 5161391) B5161391
theorem B2293951 : Blo 2293435 2293951 := bstep (se 1 (by rfl) ⟨1720463, by rfl⟩ : syracuseStep 2293951 = 3440927) B3440927
theorem B3440933 : Blo 2293435 3440933 := bbase (se 4 (by rfl) ⟨322587, by rfl⟩ : syracuseStep 3440933 = 645175) (by norm_num)
theorem B2293955 : Blo 2293435 2293955 := bstep (se 1 (by rfl) ⟨1720466, by rfl⟩ : syracuseStep 2293955 = 3440933) B3440933
theorem B2903293 : Blo 2293435 2903293 := bbase (se 3 (by rfl) ⟨544367, by rfl⟩ : syracuseStep 2903293 = 1088735) (by norm_num)
theorem B3871057 : Blo 2293435 3871057 := bstep (se 2 (by rfl) ⟨1451646, by rfl⟩ : syracuseStep 3871057 = 2903293) B2903293
theorem B5161409 : Blo 2293435 5161409 := bstep (se 2 (by rfl) ⟨1935528, by rfl⟩ : syracuseStep 5161409 = 3871057) B3871057
theorem B3440939 : Blo 2293435 3440939 := bstep (se 1 (by rfl) ⟨2580704, by rfl⟩ : syracuseStep 3440939 = 5161409) B5161409
theorem B2293959 : Blo 2293435 2293959 := bstep (se 1 (by rfl) ⟨1720469, by rfl⟩ : syracuseStep 2293959 = 3440939) B3440939
theorem B2580709 : Blo 2293435 2580709 := bbase (se 4 (by rfl) ⟨241941, by rfl⟩ : syracuseStep 2580709 = 483883) (by norm_num)
theorem B3440945 : Blo 2293435 3440945 := bstep (se 2 (by rfl) ⟨1290354, by rfl⟩ : syracuseStep 3440945 = 2580709) B2580709
theorem B2293963 : Blo 2293435 2293963 := bstep (se 1 (by rfl) ⟨1720472, by rfl⟩ : syracuseStep 2293963 = 3440945) B3440945
theorem B4899325 : Blo 2293435 4899325 := bbase (se 3 (by rfl) ⟨918623, by rfl⟩ : syracuseStep 4899325 = 1837247) (by norm_num)
theorem B6532433 : Blo 2293435 6532433 := bstep (se 2 (by rfl) ⟨2449662, by rfl⟩ : syracuseStep 6532433 = 4899325) B4899325
theorem B4354955 : Blo 2293435 4354955 := bstep (se 1 (by rfl) ⟨3266216, by rfl⟩ : syracuseStep 4354955 = 6532433) B6532433
theorem B2903303 : Blo 2293435 2903303 := bstep (se 1 (by rfl) ⟨2177477, by rfl⟩ : syracuseStep 2903303 = 4354955) B4354955
theorem B7742141 : Blo 2293435 7742141 := bstep (se 3 (by rfl) ⟨1451651, by rfl⟩ : syracuseStep 7742141 = 2903303) B2903303
theorem B5161427 : Blo 2293435 5161427 := bstep (se 1 (by rfl) ⟨3871070, by rfl⟩ : syracuseStep 5161427 = 7742141) B7742141
theorem B3440951 : Blo 2293435 3440951 := bstep (se 1 (by rfl) ⟨2580713, by rfl⟩ : syracuseStep 3440951 = 5161427) B5161427
theorem B2293967 : Blo 2293435 2293967 := bstep (se 1 (by rfl) ⟨1720475, by rfl⟩ : syracuseStep 2293967 = 3440951) B3440951
theorem B3440957 : Blo 2293435 3440957 := bbase (se 3 (by rfl) ⟨645179, by rfl⟩ : syracuseStep 3440957 = 1290359) (by norm_num)
theorem B2293971 : Blo 2293435 2293971 := bstep (se 1 (by rfl) ⟨1720478, by rfl⟩ : syracuseStep 2293971 = 3440957) B3440957
theorem B5161445 : Blo 2293435 5161445 := bbase (se 4 (by rfl) ⟨483885, by rfl⟩ : syracuseStep 5161445 = 967771) (by norm_num)
theorem B3440963 : Blo 2293435 3440963 := bstep (se 1 (by rfl) ⟨2580722, by rfl⟩ : syracuseStep 3440963 = 5161445) B5161445
theorem B2293975 : Blo 2293435 2293975 := bstep (se 1 (by rfl) ⟨1720481, by rfl⟩ : syracuseStep 2293975 = 3440963) B3440963
theorem B5806637 : Blo 2293435 5806637 := bbase (se 3 (by rfl) ⟨1088744, by rfl⟩ : syracuseStep 5806637 = 2177489) (by norm_num)
theorem B3871091 : Blo 2293435 3871091 := bstep (se 1 (by rfl) ⟨2903318, by rfl⟩ : syracuseStep 3871091 = 5806637) B5806637
theorem B2580727 : Blo 2293435 2580727 := bstep (se 1 (by rfl) ⟨1935545, by rfl⟩ : syracuseStep 2580727 = 3871091) B3871091
theorem B3440969 : Blo 2293435 3440969 := bstep (se 2 (by rfl) ⟨1290363, by rfl⟩ : syracuseStep 3440969 = 2580727) B2580727
theorem B2293979 : Blo 2293435 2293979 := bstep (se 1 (by rfl) ⟨1720484, by rfl⟩ : syracuseStep 2293979 = 3440969) B3440969
theorem B5231885 : Blo 2293435 5231885 := bbase (se 3 (by rfl) ⟨980978, by rfl⟩ : syracuseStep 5231885 = 1961957) (by norm_num)
theorem B13951693 : Blo 2293435 13951693 := bstep (se 3 (by rfl) ⟨2615942, by rfl⟩ : syracuseStep 13951693 = 5231885) B5231885
theorem B18602257 : Blo 2293435 18602257 := bstep (se 2 (by rfl) ⟨6975846, by rfl⟩ : syracuseStep 18602257 = 13951693) B13951693
theorem B24803009 : Blo 2293435 24803009 := bstep (se 2 (by rfl) ⟨9301128, by rfl⟩ : syracuseStep 24803009 = 18602257) B18602257
theorem B16535339 : Blo 2293435 16535339 := bstep (se 1 (by rfl) ⟨12401504, by rfl⟩ : syracuseStep 16535339 = 24803009) B24803009
theorem B11023559 : Blo 2293435 11023559 := bstep (se 1 (by rfl) ⟨8267669, by rfl⟩ : syracuseStep 11023559 = 16535339) B16535339
theorem B7349039 : Blo 2293435 7349039 := bstep (se 1 (by rfl) ⟨5511779, by rfl⟩ : syracuseStep 7349039 = 11023559) B11023559
theorem B4899359 : Blo 2293435 4899359 := bstep (se 1 (by rfl) ⟨3674519, by rfl⟩ : syracuseStep 4899359 = 7349039) B7349039
theorem B3266239 : Blo 2293435 3266239 := bstep (se 1 (by rfl) ⟨2449679, by rfl⟩ : syracuseStep 3266239 = 4899359) B4899359
theorem B4354985 : Blo 2293435 4354985 := bstep (se 2 (by rfl) ⟨1633119, by rfl⟩ : syracuseStep 4354985 = 3266239) B3266239
theorem B11613293 : Blo 2293435 11613293 := bstep (se 3 (by rfl) ⟨2177492, by rfl⟩ : syracuseStep 11613293 = 4354985) B4354985
theorem B7742195 : Blo 2293435 7742195 := bstep (se 1 (by rfl) ⟨5806646, by rfl⟩ : syracuseStep 7742195 = 11613293) B11613293
theorem B5161463 : Blo 2293435 5161463 := bstep (se 1 (by rfl) ⟨3871097, by rfl⟩ : syracuseStep 5161463 = 7742195) B7742195
theorem B3440975 : Blo 2293435 3440975 := bstep (se 1 (by rfl) ⟨2580731, by rfl⟩ : syracuseStep 3440975 = 5161463) B5161463
theorem B2293983 : Blo 2293435 2293983 := bstep (se 1 (by rfl) ⟨1720487, by rfl⟩ : syracuseStep 2293983 = 3440975) B3440975
theorem B3440981 : Blo 2293435 3440981 := bbase (se 10 (by rfl) ⟨5040, by rfl⟩ : syracuseStep 3440981 = 10081) (by norm_num)
theorem B2293987 : Blo 2293435 2293987 := bstep (se 1 (by rfl) ⟨1720490, by rfl⟩ : syracuseStep 2293987 = 3440981) B3440981
theorem B6532501 : Blo 2293435 6532501 := bbase (se 6 (by rfl) ⟨153105, by rfl⟩ : syracuseStep 6532501 = 306211) (by norm_num)
theorem B8710001 : Blo 2293435 8710001 := bstep (se 2 (by rfl) ⟨3266250, by rfl⟩ : syracuseStep 8710001 = 6532501) B6532501
theorem B5806667 : Blo 2293435 5806667 := bstep (se 1 (by rfl) ⟨4355000, by rfl⟩ : syracuseStep 5806667 = 8710001) B8710001
theorem B3871111 : Blo 2293435 3871111 := bstep (se 1 (by rfl) ⟨2903333, by rfl⟩ : syracuseStep 3871111 = 5806667) B5806667
theorem B5161481 : Blo 2293435 5161481 := bstep (se 2 (by rfl) ⟨1935555, by rfl⟩ : syracuseStep 5161481 = 3871111) B3871111
theorem B3440987 : Blo 2293435 3440987 := bstep (se 1 (by rfl) ⟨2580740, by rfl⟩ : syracuseStep 3440987 = 5161481) B5161481
theorem B2293991 : Blo 2293435 2293991 := bstep (se 1 (by rfl) ⟨1720493, by rfl⟩ : syracuseStep 2293991 = 3440987) B3440987
theorem B2580745 : Blo 2293435 2580745 := bbase (se 2 (by rfl) ⟨967779, by rfl⟩ : syracuseStep 2580745 = 1935559) (by norm_num)
theorem B3440993 : Blo 2293435 3440993 := bstep (se 2 (by rfl) ⟨1290372, by rfl⟩ : syracuseStep 3440993 = 2580745) B2580745
theorem B2293995 : Blo 2293435 2293995 := bstep (se 1 (by rfl) ⟨1720496, by rfl⟩ : syracuseStep 2293995 = 3440993) B3440993
theorem B15695765 : Blo 2293435 15695765 := bbase (se 6 (by rfl) ⟨367869, by rfl⟩ : syracuseStep 15695765 = 735739) (by norm_num)
theorem B10463843 : Blo 2293435 10463843 := bstep (se 1 (by rfl) ⟨7847882, by rfl⟩ : syracuseStep 10463843 = 15695765) B15695765
theorem B6975895 : Blo 2293435 6975895 := bstep (se 1 (by rfl) ⟨5231921, by rfl⟩ : syracuseStep 6975895 = 10463843) B10463843
theorem B9301193 : Blo 2293435 9301193 := bstep (se 2 (by rfl) ⟨3487947, by rfl⟩ : syracuseStep 9301193 = 6975895) B6975895
theorem B6200795 : Blo 2293435 6200795 := bstep (se 1 (by rfl) ⟨4650596, by rfl⟩ : syracuseStep 6200795 = 9301193) B9301193
theorem B4133863 : Blo 2293435 4133863 := bstep (se 1 (by rfl) ⟨3100397, by rfl⟩ : syracuseStep 4133863 = 6200795) B6200795
theorem B5511817 : Blo 2293435 5511817 := bstep (se 2 (by rfl) ⟨2066931, by rfl⟩ : syracuseStep 5511817 = 4133863) B4133863
theorem B29396357 : Blo 2293435 29396357 := bstep (se 4 (by rfl) ⟨2755908, by rfl⟩ : syracuseStep 29396357 = 5511817) B5511817
theorem B19597571 : Blo 2293435 19597571 := bstep (se 1 (by rfl) ⟨14698178, by rfl⟩ : syracuseStep 19597571 = 29396357) B29396357
theorem B13065047 : Blo 2293435 13065047 := bstep (se 1 (by rfl) ⟨9798785, by rfl⟩ : syracuseStep 13065047 = 19597571) B19597571
theorem B8710031 : Blo 2293435 8710031 := bstep (se 1 (by rfl) ⟨6532523, by rfl⟩ : syracuseStep 8710031 = 13065047) B13065047
theorem B5806687 : Blo 2293435 5806687 := bstep (se 1 (by rfl) ⟨4355015, by rfl⟩ : syracuseStep 5806687 = 8710031) B8710031
theorem B7742249 : Blo 2293435 7742249 := bstep (se 2 (by rfl) ⟨2903343, by rfl⟩ : syracuseStep 7742249 = 5806687) B5806687
theorem B5161499 : Blo 2293435 5161499 := bstep (se 1 (by rfl) ⟨3871124, by rfl⟩ : syracuseStep 5161499 = 7742249) B7742249
theorem B3440999 : Blo 2293435 3440999 := bstep (se 1 (by rfl) ⟨2580749, by rfl⟩ : syracuseStep 3440999 = 5161499) B5161499
theorem B2293999 : Blo 2293435 2293999 := bstep (se 1 (by rfl) ⟨1720499, by rfl⟩ : syracuseStep 2293999 = 3440999) B3440999
theorem B3441005 : Blo 2293435 3441005 := bbase (se 3 (by rfl) ⟨645188, by rfl⟩ : syracuseStep 3441005 = 1290377) (by norm_num)
theorem B2294003 : Blo 2293435 2294003 := bstep (se 1 (by rfl) ⟨1720502, by rfl⟩ : syracuseStep 2294003 = 3441005) B3441005
theorem B5161517 : Blo 2293435 5161517 := bbase (se 3 (by rfl) ⟨967784, by rfl⟩ : syracuseStep 5161517 = 1935569) (by norm_num)
theorem B3441011 : Blo 2293435 3441011 := bstep (se 1 (by rfl) ⟨2580758, by rfl⟩ : syracuseStep 3441011 = 5161517) B5161517
theorem B2294007 : Blo 2293435 2294007 := bstep (se 1 (by rfl) ⟨1720505, by rfl⟩ : syracuseStep 2294007 = 3441011) B3441011
theorem B4778389 : Blo 2293435 4778389 := bbase (se 6 (by rfl) ⟨111993, by rfl⟩ : syracuseStep 4778389 = 223987) (by norm_num)
theorem B6371185 : Blo 2293435 6371185 := bstep (se 2 (by rfl) ⟨2389194, by rfl⟩ : syracuseStep 6371185 = 4778389) B4778389
theorem B8494913 : Blo 2293435 8494913 := bstep (se 2 (by rfl) ⟨3185592, by rfl⟩ : syracuseStep 8494913 = 6371185) B6371185
theorem B22653101 : Blo 2293435 22653101 := bstep (se 3 (by rfl) ⟨4247456, by rfl⟩ : syracuseStep 22653101 = 8494913) B8494913
theorem B15102067 : Blo 2293435 15102067 := bstep (se 1 (by rfl) ⟨11326550, by rfl⟩ : syracuseStep 15102067 = 22653101) B22653101
theorem B20136089 : Blo 2293435 20136089 := bstep (se 2 (by rfl) ⟨7551033, by rfl⟩ : syracuseStep 20136089 = 15102067) B15102067
theorem B13424059 : Blo 2293435 13424059 := bstep (se 1 (by rfl) ⟨10068044, by rfl⟩ : syracuseStep 13424059 = 20136089) B20136089
theorem B17898745 : Blo 2293435 17898745 := bstep (se 2 (by rfl) ⟨6712029, by rfl⟩ : syracuseStep 17898745 = 13424059) B13424059
theorem B23864993 : Blo 2293435 23864993 := bstep (se 2 (by rfl) ⟨8949372, by rfl⟩ : syracuseStep 23864993 = 17898745) B17898745
theorem B15909995 : Blo 2293435 15909995 := bstep (se 1 (by rfl) ⟨11932496, by rfl⟩ : syracuseStep 15909995 = 23864993) B23864993
theorem B10606663 : Blo 2293435 10606663 := bstep (se 1 (by rfl) ⟨7954997, by rfl⟩ : syracuseStep 10606663 = 15909995) B15909995
theorem B14142217 : Blo 2293435 14142217 := bstep (se 2 (by rfl) ⟨5303331, by rfl⟩ : syracuseStep 14142217 = 10606663) B10606663
theorem B18856289 : Blo 2293435 18856289 := bstep (se 2 (by rfl) ⟨7071108, by rfl⟩ : syracuseStep 18856289 = 14142217) B14142217
theorem B12570859 : Blo 2293435 12570859 := bstep (se 1 (by rfl) ⟨9428144, by rfl⟩ : syracuseStep 12570859 = 18856289) B18856289
theorem B67044581 : Blo 2293435 67044581 := bstep (se 4 (by rfl) ⟨6285429, by rfl⟩ : syracuseStep 67044581 = 12570859) B12570859
theorem B44696387 : Blo 2293435 44696387 := bstep (se 1 (by rfl) ⟨33522290, by rfl⟩ : syracuseStep 44696387 = 67044581) B67044581
theorem B29797591 : Blo 2293435 29797591 := bstep (se 1 (by rfl) ⟨22348193, by rfl⟩ : syracuseStep 29797591 = 44696387) B44696387
theorem B39730121 : Blo 2293435 39730121 := bstep (se 2 (by rfl) ⟨14898795, by rfl⟩ : syracuseStep 39730121 = 29797591) B29797591
theorem B26486747 : Blo 2293435 26486747 := bstep (se 1 (by rfl) ⟨19865060, by rfl⟩ : syracuseStep 26486747 = 39730121) B39730121
theorem B17657831 : Blo 2293435 17657831 := bstep (se 1 (by rfl) ⟨13243373, by rfl⟩ : syracuseStep 17657831 = 26486747) B26486747
theorem B11771887 : Blo 2293435 11771887 := bstep (se 1 (by rfl) ⟨8828915, by rfl⟩ : syracuseStep 11771887 = 17657831) B17657831
theorem B15695849 : Blo 2293435 15695849 := bstep (se 2 (by rfl) ⟨5885943, by rfl⟩ : syracuseStep 15695849 = 11771887) B11771887
theorem B10463899 : Blo 2293435 10463899 := bstep (se 1 (by rfl) ⟨7847924, by rfl⟩ : syracuseStep 10463899 = 15695849) B15695849
theorem B13951865 : Blo 2293435 13951865 := bstep (se 2 (by rfl) ⟨5231949, by rfl⟩ : syracuseStep 13951865 = 10463899) B10463899
theorem B9301243 : Blo 2293435 9301243 := bstep (se 1 (by rfl) ⟨6975932, by rfl⟩ : syracuseStep 9301243 = 13951865) B13951865
theorem B12401657 : Blo 2293435 12401657 := bstep (se 2 (by rfl) ⟨4650621, by rfl⟩ : syracuseStep 12401657 = 9301243) B9301243
theorem B8267771 : Blo 2293435 8267771 := bstep (se 1 (by rfl) ⟨6200828, by rfl⟩ : syracuseStep 8267771 = 12401657) B12401657
theorem B22047389 : Blo 2293435 22047389 := bstep (se 3 (by rfl) ⟨4133885, by rfl⟩ : syracuseStep 22047389 = 8267771) B8267771
theorem B14698259 : Blo 2293435 14698259 := bstep (se 1 (by rfl) ⟨11023694, by rfl⟩ : syracuseStep 14698259 = 22047389) B22047389
theorem B9798839 : Blo 2293435 9798839 := bstep (se 1 (by rfl) ⟨7349129, by rfl⟩ : syracuseStep 9798839 = 14698259) B14698259
theorem B6532559 : Blo 2293435 6532559 := bstep (se 1 (by rfl) ⟨4899419, by rfl⟩ : syracuseStep 6532559 = 9798839) B9798839
theorem B4355039 : Blo 2293435 4355039 := bstep (se 1 (by rfl) ⟨3266279, by rfl⟩ : syracuseStep 4355039 = 6532559) B6532559
theorem B2903359 : Blo 2293435 2903359 := bstep (se 1 (by rfl) ⟨2177519, by rfl⟩ : syracuseStep 2903359 = 4355039) B4355039
theorem B3871145 : Blo 2293435 3871145 := bstep (se 2 (by rfl) ⟨1451679, by rfl⟩ : syracuseStep 3871145 = 2903359) B2903359
theorem B2580763 : Blo 2293435 2580763 := bstep (se 1 (by rfl) ⟨1935572, by rfl⟩ : syracuseStep 2580763 = 3871145) B3871145
theorem B3441017 : Blo 2293435 3441017 := bstep (se 2 (by rfl) ⟨1290381, by rfl⟩ : syracuseStep 3441017 = 2580763) B2580763
theorem B2294011 : Blo 2293435 2294011 := bstep (se 1 (by rfl) ⟨1720508, by rfl⟩ : syracuseStep 2294011 = 3441017) B3441017
theorem B39195413 : Blo 2293435 39195413 := bbase (se 6 (by rfl) ⟨918642, by rfl⟩ : syracuseStep 39195413 = 1837285) (by norm_num)
theorem B26130275 : Blo 2293435 26130275 := bstep (se 1 (by rfl) ⟨19597706, by rfl⟩ : syracuseStep 26130275 = 39195413) B39195413
theorem B17420183 : Blo 2293435 17420183 := bstep (se 1 (by rfl) ⟨13065137, by rfl⟩ : syracuseStep 17420183 = 26130275) B26130275
theorem B11613455 : Blo 2293435 11613455 := bstep (se 1 (by rfl) ⟨8710091, by rfl⟩ : syracuseStep 11613455 = 17420183) B17420183
theorem B7742303 : Blo 2293435 7742303 := bstep (se 1 (by rfl) ⟨5806727, by rfl⟩ : syracuseStep 7742303 = 11613455) B11613455
theorem B5161535 : Blo 2293435 5161535 := bstep (se 1 (by rfl) ⟨3871151, by rfl⟩ : syracuseStep 5161535 = 7742303) B7742303
theorem B3441023 : Blo 2293435 3441023 := bstep (se 1 (by rfl) ⟨2580767, by rfl⟩ : syracuseStep 3441023 = 5161535) B5161535
theorem B2294015 : Blo 2293435 2294015 := bstep (se 1 (by rfl) ⟨1720511, by rfl⟩ : syracuseStep 2294015 = 3441023) B3441023
theorem B3441029 : Blo 2293435 3441029 := bbase (se 4 (by rfl) ⟨322596, by rfl⟩ : syracuseStep 3441029 = 645193) (by norm_num)
theorem B2294019 : Blo 2293435 2294019 := bstep (se 1 (by rfl) ⟨1720514, by rfl⟩ : syracuseStep 2294019 = 3441029) B3441029
theorem B3871165 : Blo 2293435 3871165 := bbase (se 3 (by rfl) ⟨725843, by rfl⟩ : syracuseStep 3871165 = 1451687) (by norm_num)
theorem B5161553 : Blo 2293435 5161553 := bstep (se 2 (by rfl) ⟨1935582, by rfl⟩ : syracuseStep 5161553 = 3871165) B3871165
theorem B3441035 : Blo 2293435 3441035 := bstep (se 1 (by rfl) ⟨2580776, by rfl⟩ : syracuseStep 3441035 = 5161553) B5161553
theorem B2294023 : Blo 2293435 2294023 := bstep (se 1 (by rfl) ⟨1720517, by rfl⟩ : syracuseStep 2294023 = 3441035) B3441035
theorem B2580781 : Blo 2293435 2580781 := bbase (se 3 (by rfl) ⟨483896, by rfl⟩ : syracuseStep 2580781 = 967793) (by norm_num)
theorem B3441041 : Blo 2293435 3441041 := bstep (se 2 (by rfl) ⟨1290390, by rfl⟩ : syracuseStep 3441041 = 2580781) B2580781
theorem B2294027 : Blo 2293435 2294027 := bstep (se 1 (by rfl) ⟨1720520, by rfl⟩ : syracuseStep 2294027 = 3441041) B3441041
theorem B7742357 : Blo 2293435 7742357 := bbase (se 6 (by rfl) ⟨181461, by rfl⟩ : syracuseStep 7742357 = 362923) (by norm_num)
theorem B5161571 : Blo 2293435 5161571 := bstep (se 1 (by rfl) ⟨3871178, by rfl⟩ : syracuseStep 5161571 = 7742357) B7742357
theorem B3441047 : Blo 2293435 3441047 := bstep (se 1 (by rfl) ⟨2580785, by rfl⟩ : syracuseStep 3441047 = 5161571) B5161571
theorem B2294031 : Blo 2293435 2294031 := bstep (se 1 (by rfl) ⟨1720523, by rfl⟩ : syracuseStep 2294031 = 3441047) B3441047
theorem B3441053 : Blo 2293435 3441053 := bbase (se 3 (by rfl) ⟨645197, by rfl⟩ : syracuseStep 3441053 = 1290395) (by norm_num)
theorem B2294035 : Blo 2293435 2294035 := bstep (se 1 (by rfl) ⟨1720526, by rfl⟩ : syracuseStep 2294035 = 3441053) B3441053
theorem B5161589 : Blo 2293435 5161589 := bbase (se 5 (by rfl) ⟨241949, by rfl⟩ : syracuseStep 5161589 = 483899) (by norm_num)
theorem B3441059 : Blo 2293435 3441059 := bstep (se 1 (by rfl) ⟨2580794, by rfl⟩ : syracuseStep 3441059 = 5161589) B5161589
theorem B2294039 : Blo 2293435 2294039 := bstep (se 1 (by rfl) ⟨1720529, by rfl⟩ : syracuseStep 2294039 = 3441059) B3441059
theorem B16990069 : Blo 2293435 16990069 := bbase (se 5 (by rfl) ⟨796409, by rfl⟩ : syracuseStep 16990069 = 1592819) (by norm_num)
theorem B22653425 : Blo 2293435 22653425 := bstep (se 2 (by rfl) ⟨8495034, by rfl⟩ : syracuseStep 22653425 = 16990069) B16990069
theorem B15102283 : Blo 2293435 15102283 := bstep (se 1 (by rfl) ⟨11326712, by rfl⟩ : syracuseStep 15102283 = 22653425) B22653425
theorem B20136377 : Blo 2293435 20136377 := bstep (se 2 (by rfl) ⟨7551141, by rfl⟩ : syracuseStep 20136377 = 15102283) B15102283
theorem B13424251 : Blo 2293435 13424251 := bstep (se 1 (by rfl) ⟨10068188, by rfl⟩ : syracuseStep 13424251 = 20136377) B20136377
theorem B17899001 : Blo 2293435 17899001 := bstep (se 2 (by rfl) ⟨6712125, by rfl⟩ : syracuseStep 17899001 = 13424251) B13424251
theorem B11932667 : Blo 2293435 11932667 := bstep (se 1 (by rfl) ⟨8949500, by rfl⟩ : syracuseStep 11932667 = 17899001) B17899001
theorem B7955111 : Blo 2293435 7955111 := bstep (se 1 (by rfl) ⟨5966333, by rfl⟩ : syracuseStep 7955111 = 11932667) B11932667
theorem B5303407 : Blo 2293435 5303407 := bstep (se 1 (by rfl) ⟨3977555, by rfl⟩ : syracuseStep 5303407 = 7955111) B7955111
theorem B7071209 : Blo 2293435 7071209 := bstep (se 2 (by rfl) ⟨2651703, by rfl⟩ : syracuseStep 7071209 = 5303407) B5303407
theorem B4714139 : Blo 2293435 4714139 := bstep (se 1 (by rfl) ⟨3535604, by rfl⟩ : syracuseStep 4714139 = 7071209) B7071209
theorem B12571037 : Blo 2293435 12571037 := bstep (se 3 (by rfl) ⟨2357069, by rfl⟩ : syracuseStep 12571037 = 4714139) B4714139
theorem B8380691 : Blo 2293435 8380691 := bstep (se 1 (by rfl) ⟨6285518, by rfl⟩ : syracuseStep 8380691 = 12571037) B12571037
theorem B5587127 : Blo 2293435 5587127 := bstep (se 1 (by rfl) ⟨4190345, by rfl⟩ : syracuseStep 5587127 = 8380691) B8380691
theorem B3724751 : Blo 2293435 3724751 := bstep (se 1 (by rfl) ⟨2793563, by rfl⟩ : syracuseStep 3724751 = 5587127) B5587127
theorem B2483167 : Blo 2293435 2483167 := bstep (se 1 (by rfl) ⟨1862375, by rfl⟩ : syracuseStep 2483167 = 3724751) B3724751
theorem B3310889 : Blo 2293435 3310889 := bstep (se 2 (by rfl) ⟨1241583, by rfl⟩ : syracuseStep 3310889 = 2483167) B2483167
theorem B8829037 : Blo 2293435 8829037 := bstep (se 3 (by rfl) ⟨1655444, by rfl⟩ : syracuseStep 8829037 = 3310889) B3310889
theorem B11772049 : Blo 2293435 11772049 := bstep (se 2 (by rfl) ⟨4414518, by rfl⟩ : syracuseStep 11772049 = 8829037) B8829037
theorem B15696065 : Blo 2293435 15696065 := bstep (se 2 (by rfl) ⟨5886024, by rfl⟩ : syracuseStep 15696065 = 11772049) B11772049
theorem B41856173 : Blo 2293435 41856173 := bstep (se 3 (by rfl) ⟨7848032, by rfl⟩ : syracuseStep 41856173 = 15696065) B15696065
theorem B27904115 : Blo 2293435 27904115 := bstep (se 1 (by rfl) ⟨20928086, by rfl⟩ : syracuseStep 27904115 = 41856173) B41856173
theorem B18602743 : Blo 2293435 18602743 := bstep (se 1 (by rfl) ⟨13952057, by rfl⟩ : syracuseStep 18602743 = 27904115) B27904115
theorem B24803657 : Blo 2293435 24803657 := bstep (se 2 (by rfl) ⟨9301371, by rfl⟩ : syracuseStep 24803657 = 18602743) B18602743
theorem B16535771 : Blo 2293435 16535771 := bstep (se 1 (by rfl) ⟨12401828, by rfl⟩ : syracuseStep 16535771 = 24803657) B24803657
theorem B11023847 : Blo 2293435 11023847 := bstep (se 1 (by rfl) ⟨8267885, by rfl⟩ : syracuseStep 11023847 = 16535771) B16535771
theorem B7349231 : Blo 2293435 7349231 := bstep (se 1 (by rfl) ⟨5511923, by rfl⟩ : syracuseStep 7349231 = 11023847) B11023847
theorem B19597949 : Blo 2293435 19597949 := bstep (se 3 (by rfl) ⟨3674615, by rfl⟩ : syracuseStep 19597949 = 7349231) B7349231
theorem B13065299 : Blo 2293435 13065299 := bstep (se 1 (by rfl) ⟨9798974, by rfl⟩ : syracuseStep 13065299 = 19597949) B19597949
theorem B8710199 : Blo 2293435 8710199 := bstep (se 1 (by rfl) ⟨6532649, by rfl⟩ : syracuseStep 8710199 = 13065299) B13065299
theorem B5806799 : Blo 2293435 5806799 := bstep (se 1 (by rfl) ⟨4355099, by rfl⟩ : syracuseStep 5806799 = 8710199) B8710199
theorem B3871199 : Blo 2293435 3871199 := bstep (se 1 (by rfl) ⟨2903399, by rfl⟩ : syracuseStep 3871199 = 5806799) B5806799
theorem B2580799 : Blo 2293435 2580799 := bstep (se 1 (by rfl) ⟨1935599, by rfl⟩ : syracuseStep 2580799 = 3871199) B3871199
theorem B3441065 : Blo 2293435 3441065 := bstep (se 2 (by rfl) ⟨1290399, by rfl⟩ : syracuseStep 3441065 = 2580799) B2580799
theorem B2294043 : Blo 2293435 2294043 := bstep (se 1 (by rfl) ⟨1720532, by rfl⟩ : syracuseStep 2294043 = 3441065) B3441065
theorem B8710213 : Blo 2293435 8710213 := bbase (se 4 (by rfl) ⟨816582, by rfl⟩ : syracuseStep 8710213 = 1633165) (by norm_num)
theorem B11613617 : Blo 2293435 11613617 := bstep (se 2 (by rfl) ⟨4355106, by rfl⟩ : syracuseStep 11613617 = 8710213) B8710213
theorem B7742411 : Blo 2293435 7742411 := bstep (se 1 (by rfl) ⟨5806808, by rfl⟩ : syracuseStep 7742411 = 11613617) B11613617
theorem B5161607 : Blo 2293435 5161607 := bstep (se 1 (by rfl) ⟨3871205, by rfl⟩ : syracuseStep 5161607 = 7742411) B7742411
theorem B3441071 : Blo 2293435 3441071 := bstep (se 1 (by rfl) ⟨2580803, by rfl⟩ : syracuseStep 3441071 = 5161607) B5161607
theorem B2294047 : Blo 2293435 2294047 := bstep (se 1 (by rfl) ⟨1720535, by rfl⟩ : syracuseStep 2294047 = 3441071) B3441071
theorem B3441077 : Blo 2293435 3441077 := bbase (se 5 (by rfl) ⟨161300, by rfl⟩ : syracuseStep 3441077 = 322601) (by norm_num)
theorem B2294051 : Blo 2293435 2294051 := bstep (se 1 (by rfl) ⟨1720538, by rfl⟩ : syracuseStep 2294051 = 3441077) B3441077
theorem B5806829 : Blo 2293435 5806829 := bbase (se 3 (by rfl) ⟨1088780, by rfl⟩ : syracuseStep 5806829 = 2177561) (by norm_num)
theorem B3871219 : Blo 2293435 3871219 := bstep (se 1 (by rfl) ⟨2903414, by rfl⟩ : syracuseStep 3871219 = 5806829) B5806829
theorem B5161625 : Blo 2293435 5161625 := bstep (se 2 (by rfl) ⟨1935609, by rfl⟩ : syracuseStep 5161625 = 3871219) B3871219
theorem B3441083 : Blo 2293435 3441083 := bstep (se 1 (by rfl) ⟨2580812, by rfl⟩ : syracuseStep 3441083 = 5161625) B5161625
theorem B2294055 : Blo 2293435 2294055 := bstep (se 1 (by rfl) ⟨1720541, by rfl⟩ : syracuseStep 2294055 = 3441083) B3441083
theorem B2580817 : Blo 2293435 2580817 := bbase (se 2 (by rfl) ⟨967806, by rfl⟩ : syracuseStep 2580817 = 1935613) (by norm_num)
theorem B3441089 : Blo 2293435 3441089 := bstep (se 2 (by rfl) ⟨1290408, by rfl⟩ : syracuseStep 3441089 = 2580817) B2580817
theorem B2294059 : Blo 2293435 2294059 := bstep (se 1 (by rfl) ⟨1720544, by rfl⟩ : syracuseStep 2294059 = 3441089) B3441089
theorem B2449765 : Blo 2293435 2449765 := bbase (se 4 (by rfl) ⟨229665, by rfl⟩ : syracuseStep 2449765 = 459331) (by norm_num)
theorem B3266353 : Blo 2293435 3266353 := bstep (se 2 (by rfl) ⟨1224882, by rfl⟩ : syracuseStep 3266353 = 2449765) B2449765
theorem B4355137 : Blo 2293435 4355137 := bstep (se 2 (by rfl) ⟨1633176, by rfl⟩ : syracuseStep 4355137 = 3266353) B3266353
theorem B5806849 : Blo 2293435 5806849 := bstep (se 2 (by rfl) ⟨2177568, by rfl⟩ : syracuseStep 5806849 = 4355137) B4355137
theorem B7742465 : Blo 2293435 7742465 := bstep (se 2 (by rfl) ⟨2903424, by rfl⟩ : syracuseStep 7742465 = 5806849) B5806849
theorem B5161643 : Blo 2293435 5161643 := bstep (se 1 (by rfl) ⟨3871232, by rfl⟩ : syracuseStep 5161643 = 7742465) B7742465
theorem B3441095 : Blo 2293435 3441095 := bstep (se 1 (by rfl) ⟨2580821, by rfl⟩ : syracuseStep 3441095 = 5161643) B5161643
theorem B2294063 : Blo 2293435 2294063 := bstep (se 1 (by rfl) ⟨1720547, by rfl⟩ : syracuseStep 2294063 = 3441095) B3441095
theorem B3441101 : Blo 2293435 3441101 := bbase (se 3 (by rfl) ⟨645206, by rfl⟩ : syracuseStep 3441101 = 1290413) (by norm_num)
theorem B2294067 : Blo 2293435 2294067 := bstep (se 1 (by rfl) ⟨1720550, by rfl⟩ : syracuseStep 2294067 = 3441101) B3441101
theorem B5161661 : Blo 2293435 5161661 := bbase (se 3 (by rfl) ⟨967811, by rfl⟩ : syracuseStep 5161661 = 1935623) (by norm_num)
theorem B3441107 : Blo 2293435 3441107 := bstep (se 1 (by rfl) ⟨2580830, by rfl⟩ : syracuseStep 3441107 = 5161661) B5161661
theorem B2294071 : Blo 2293435 2294071 := bstep (se 1 (by rfl) ⟨1720553, by rfl⟩ : syracuseStep 2294071 = 3441107) B3441107
theorem B3871253 : Blo 2293435 3871253 := bbase (se 6 (by rfl) ⟨90732, by rfl⟩ : syracuseStep 3871253 = 181465) (by norm_num)
theorem B2580835 : Blo 2293435 2580835 := bstep (se 1 (by rfl) ⟨1935626, by rfl⟩ : syracuseStep 2580835 = 3871253) B3871253
theorem B3441113 : Blo 2293435 3441113 := bstep (se 2 (by rfl) ⟨1290417, by rfl⟩ : syracuseStep 3441113 = 2580835) B2580835
theorem B2294075 : Blo 2293435 2294075 := bstep (se 1 (by rfl) ⟨1720556, by rfl⟩ : syracuseStep 2294075 = 3441113) B3441113
theorem B3488069 : Blo 2293435 3488069 := bbase (se 4 (by rfl) ⟨327006, by rfl⟩ : syracuseStep 3488069 = 654013) (by norm_num)
theorem B9301517 : Blo 2293435 9301517 := bstep (se 3 (by rfl) ⟨1744034, by rfl⟩ : syracuseStep 9301517 = 3488069) B3488069
theorem B6201011 : Blo 2293435 6201011 := bstep (se 1 (by rfl) ⟨4650758, by rfl⟩ : syracuseStep 6201011 = 9301517) B9301517
theorem B4134007 : Blo 2293435 4134007 := bstep (se 1 (by rfl) ⟨3100505, by rfl⟩ : syracuseStep 4134007 = 6201011) B6201011
theorem B22048037 : Blo 2293435 22048037 := bstep (se 4 (by rfl) ⟨2067003, by rfl⟩ : syracuseStep 22048037 = 4134007) B4134007
theorem B14698691 : Blo 2293435 14698691 := bstep (se 1 (by rfl) ⟨11024018, by rfl⟩ : syracuseStep 14698691 = 22048037) B22048037
theorem B9799127 : Blo 2293435 9799127 := bstep (se 1 (by rfl) ⟨7349345, by rfl⟩ : syracuseStep 9799127 = 14698691) B14698691
theorem B6532751 : Blo 2293435 6532751 := bstep (se 1 (by rfl) ⟨4899563, by rfl⟩ : syracuseStep 6532751 = 9799127) B9799127
theorem B17420669 : Blo 2293435 17420669 := bstep (se 3 (by rfl) ⟨3266375, by rfl⟩ : syracuseStep 17420669 = 6532751) B6532751
theorem B11613779 : Blo 2293435 11613779 := bstep (se 1 (by rfl) ⟨8710334, by rfl⟩ : syracuseStep 11613779 = 17420669) B17420669
theorem B7742519 : Blo 2293435 7742519 := bstep (se 1 (by rfl) ⟨5806889, by rfl⟩ : syracuseStep 7742519 = 11613779) B11613779
theorem B5161679 : Blo 2293435 5161679 := bstep (se 1 (by rfl) ⟨3871259, by rfl⟩ : syracuseStep 5161679 = 7742519) B7742519
theorem B3441119 : Blo 2293435 3441119 := bstep (se 1 (by rfl) ⟨2580839, by rfl⟩ : syracuseStep 3441119 = 5161679) B5161679
theorem B2294079 : Blo 2293435 2294079 := bstep (se 1 (by rfl) ⟨1720559, by rfl⟩ : syracuseStep 2294079 = 3441119) B3441119
theorem B3441125 : Blo 2293435 3441125 := bbase (se 4 (by rfl) ⟨322605, by rfl⟩ : syracuseStep 3441125 = 645211) (by norm_num)
theorem B2294083 : Blo 2293435 2294083 := bstep (se 1 (by rfl) ⟨1720562, by rfl⟩ : syracuseStep 2294083 = 3441125) B3441125
theorem B10464245 : Blo 2293435 10464245 := bbase (se 5 (by rfl) ⟨490511, by rfl⟩ : syracuseStep 10464245 = 981023) (by norm_num)
theorem B6976163 : Blo 2293435 6976163 := bstep (se 1 (by rfl) ⟨5232122, by rfl⟩ : syracuseStep 6976163 = 10464245) B10464245
theorem B18603101 : Blo 2293435 18603101 := bstep (se 3 (by rfl) ⟨3488081, by rfl⟩ : syracuseStep 18603101 = 6976163) B6976163
theorem B12402067 : Blo 2293435 12402067 := bstep (se 1 (by rfl) ⟨9301550, by rfl⟩ : syracuseStep 12402067 = 18603101) B18603101
theorem B16536089 : Blo 2293435 16536089 := bstep (se 2 (by rfl) ⟨6201033, by rfl⟩ : syracuseStep 16536089 = 12402067) B12402067
theorem B11024059 : Blo 2293435 11024059 := bstep (se 1 (by rfl) ⟨8268044, by rfl⟩ : syracuseStep 11024059 = 16536089) B16536089
theorem B14698745 : Blo 2293435 14698745 := bstep (se 2 (by rfl) ⟨5512029, by rfl⟩ : syracuseStep 14698745 = 11024059) B11024059
theorem B9799163 : Blo 2293435 9799163 := bstep (se 1 (by rfl) ⟨7349372, by rfl⟩ : syracuseStep 9799163 = 14698745) B14698745
theorem B6532775 : Blo 2293435 6532775 := bstep (se 1 (by rfl) ⟨4899581, by rfl⟩ : syracuseStep 6532775 = 9799163) B9799163
theorem B4355183 : Blo 2293435 4355183 := bstep (se 1 (by rfl) ⟨3266387, by rfl⟩ : syracuseStep 4355183 = 6532775) B6532775
theorem B2903455 : Blo 2293435 2903455 := bstep (se 1 (by rfl) ⟨2177591, by rfl⟩ : syracuseStep 2903455 = 4355183) B4355183
theorem B3871273 : Blo 2293435 3871273 := bstep (se 2 (by rfl) ⟨1451727, by rfl⟩ : syracuseStep 3871273 = 2903455) B2903455
theorem B5161697 : Blo 2293435 5161697 := bstep (se 2 (by rfl) ⟨1935636, by rfl⟩ : syracuseStep 5161697 = 3871273) B3871273
theorem B3441131 : Blo 2293435 3441131 := bstep (se 1 (by rfl) ⟨2580848, by rfl⟩ : syracuseStep 3441131 = 5161697) B5161697
theorem B2294087 : Blo 2293435 2294087 := bstep (se 1 (by rfl) ⟨1720565, by rfl⟩ : syracuseStep 2294087 = 3441131) B3441131
theorem B2580853 : Blo 2293435 2580853 := bbase (se 5 (by rfl) ⟨120977, by rfl⟩ : syracuseStep 2580853 = 241955) (by norm_num)
theorem B3441137 : Blo 2293435 3441137 := bstep (se 2 (by rfl) ⟨1290426, by rfl⟩ : syracuseStep 3441137 = 2580853) B2580853
theorem B2294091 : Blo 2293435 2294091 := bstep (se 1 (by rfl) ⟨1720568, by rfl⟩ : syracuseStep 2294091 = 3441137) B3441137
theorem B2903465 : Blo 2293435 2903465 := bbase (se 2 (by rfl) ⟨1088799, by rfl⟩ : syracuseStep 2903465 = 2177599) (by norm_num)
theorem B7742573 : Blo 2293435 7742573 := bstep (se 3 (by rfl) ⟨1451732, by rfl⟩ : syracuseStep 7742573 = 2903465) B2903465
theorem B5161715 : Blo 2293435 5161715 := bstep (se 1 (by rfl) ⟨3871286, by rfl⟩ : syracuseStep 5161715 = 7742573) B7742573
theorem B3441143 : Blo 2293435 3441143 := bstep (se 1 (by rfl) ⟨2580857, by rfl⟩ : syracuseStep 3441143 = 5161715) B5161715
theorem B2294095 : Blo 2293435 2294095 := bstep (se 1 (by rfl) ⟨1720571, by rfl⟩ : syracuseStep 2294095 = 3441143) B3441143
theorem B3441149 : Blo 2293435 3441149 := bbase (se 3 (by rfl) ⟨645215, by rfl⟩ : syracuseStep 3441149 = 1290431) (by norm_num)
theorem B2294099 : Blo 2293435 2294099 := bstep (se 1 (by rfl) ⟨1720574, by rfl⟩ : syracuseStep 2294099 = 3441149) B3441149
theorem B5161733 : Blo 2293435 5161733 := bbase (se 4 (by rfl) ⟨483912, by rfl⟩ : syracuseStep 5161733 = 967825) (by norm_num)
theorem B3441155 : Blo 2293435 3441155 := bstep (se 1 (by rfl) ⟨2580866, by rfl⟩ : syracuseStep 3441155 = 5161733) B5161733
theorem B2294103 : Blo 2293435 2294103 := bstep (se 1 (by rfl) ⟨1720577, by rfl⟩ : syracuseStep 2294103 = 3441155) B3441155
theorem B4355221 : Blo 2293435 4355221 := bbase (se 6 (by rfl) ⟨102075, by rfl⟩ : syracuseStep 4355221 = 204151) (by norm_num)
theorem B5806961 : Blo 2293435 5806961 := bstep (se 2 (by rfl) ⟨2177610, by rfl⟩ : syracuseStep 5806961 = 4355221) B4355221
theorem B3871307 : Blo 2293435 3871307 := bstep (se 1 (by rfl) ⟨2903480, by rfl⟩ : syracuseStep 3871307 = 5806961) B5806961
theorem B2580871 : Blo 2293435 2580871 := bstep (se 1 (by rfl) ⟨1935653, by rfl⟩ : syracuseStep 2580871 = 3871307) B3871307
theorem B3441161 : Blo 2293435 3441161 := bstep (se 2 (by rfl) ⟨1290435, by rfl⟩ : syracuseStep 3441161 = 2580871) B2580871
theorem B2294107 : Blo 2293435 2294107 := bstep (se 1 (by rfl) ⟨1720580, by rfl⟩ : syracuseStep 2294107 = 3441161) B3441161
theorem B11613941 : Blo 2293435 11613941 := bbase (se 5 (by rfl) ⟨544403, by rfl⟩ : syracuseStep 11613941 = 1088807) (by norm_num)
theorem B7742627 : Blo 2293435 7742627 := bstep (se 1 (by rfl) ⟨5806970, by rfl⟩ : syracuseStep 7742627 = 11613941) B11613941
theorem B5161751 : Blo 2293435 5161751 := bstep (se 1 (by rfl) ⟨3871313, by rfl⟩ : syracuseStep 5161751 = 7742627) B7742627
theorem B3441167 : Blo 2293435 3441167 := bstep (se 1 (by rfl) ⟨2580875, by rfl⟩ : syracuseStep 3441167 = 5161751) B5161751
theorem B2294111 : Blo 2293435 2294111 := bstep (se 1 (by rfl) ⟨1720583, by rfl⟩ : syracuseStep 2294111 = 3441167) B3441167
theorem B3441173 : Blo 2293435 3441173 := bbase (se 6 (by rfl) ⟨80652, by rfl⟩ : syracuseStep 3441173 = 161305) (by norm_num)
theorem B2294115 : Blo 2293435 2294115 := bstep (se 1 (by rfl) ⟨1720586, by rfl⟩ : syracuseStep 2294115 = 3441173) B3441173
theorem B2756053 : Blo 2293435 2756053 := bbase (se 7 (by rfl) ⟨32297, by rfl⟩ : syracuseStep 2756053 = 64595) (by norm_num)
theorem B3674737 : Blo 2293435 3674737 := bstep (se 2 (by rfl) ⟨1378026, by rfl⟩ : syracuseStep 3674737 = 2756053) B2756053
theorem B19598597 : Blo 2293435 19598597 := bstep (se 4 (by rfl) ⟨1837368, by rfl⟩ : syracuseStep 19598597 = 3674737) B3674737
theorem B13065731 : Blo 2293435 13065731 := bstep (se 1 (by rfl) ⟨9799298, by rfl⟩ : syracuseStep 13065731 = 19598597) B19598597
theorem B8710487 : Blo 2293435 8710487 := bstep (se 1 (by rfl) ⟨6532865, by rfl⟩ : syracuseStep 8710487 = 13065731) B13065731
theorem B5806991 : Blo 2293435 5806991 := bstep (se 1 (by rfl) ⟨4355243, by rfl⟩ : syracuseStep 5806991 = 8710487) B8710487
theorem B3871327 : Blo 2293435 3871327 := bstep (se 1 (by rfl) ⟨2903495, by rfl⟩ : syracuseStep 3871327 = 5806991) B5806991
theorem B5161769 : Blo 2293435 5161769 := bstep (se 2 (by rfl) ⟨1935663, by rfl⟩ : syracuseStep 5161769 = 3871327) B3871327
theorem B3441179 : Blo 2293435 3441179 := bstep (se 1 (by rfl) ⟨2580884, by rfl⟩ : syracuseStep 3441179 = 5161769) B5161769
theorem B2294119 : Blo 2293435 2294119 := bstep (se 1 (by rfl) ⟨1720589, by rfl⟩ : syracuseStep 2294119 = 3441179) B3441179
theorem B2580889 : Blo 2293435 2580889 := bbase (se 2 (by rfl) ⟨967833, by rfl⟩ : syracuseStep 2580889 = 1935667) (by norm_num)
theorem B3441185 : Blo 2293435 3441185 := bstep (se 2 (by rfl) ⟨1290444, by rfl⟩ : syracuseStep 3441185 = 2580889) B2580889
theorem B2294123 : Blo 2293435 2294123 := bstep (se 1 (by rfl) ⟨1720592, by rfl⟩ : syracuseStep 2294123 = 3441185) B3441185
theorem B8710517 : Blo 2293435 8710517 := bbase (se 5 (by rfl) ⟨408305, by rfl⟩ : syracuseStep 8710517 = 816611) (by norm_num)
theorem B5807011 : Blo 2293435 5807011 := bstep (se 1 (by rfl) ⟨4355258, by rfl⟩ : syracuseStep 5807011 = 8710517) B8710517
theorem B7742681 : Blo 2293435 7742681 := bstep (se 2 (by rfl) ⟨2903505, by rfl⟩ : syracuseStep 7742681 = 5807011) B5807011
theorem B5161787 : Blo 2293435 5161787 := bstep (se 1 (by rfl) ⟨3871340, by rfl⟩ : syracuseStep 5161787 = 7742681) B7742681
theorem B3441191 : Blo 2293435 3441191 := bstep (se 1 (by rfl) ⟨2580893, by rfl⟩ : syracuseStep 3441191 = 5161787) B5161787
theorem B2294127 : Blo 2293435 2294127 := bstep (se 1 (by rfl) ⟨1720595, by rfl⟩ : syracuseStep 2294127 = 3441191) B3441191
theorem B3441197 : Blo 2293435 3441197 := bbase (se 3 (by rfl) ⟨645224, by rfl⟩ : syracuseStep 3441197 = 1290449) (by norm_num)
theorem B2294131 : Blo 2293435 2294131 := bstep (se 1 (by rfl) ⟨1720598, by rfl⟩ : syracuseStep 2294131 = 3441197) B3441197
theorem B5161805 : Blo 2293435 5161805 := bbase (se 3 (by rfl) ⟨967838, by rfl⟩ : syracuseStep 5161805 = 1935677) (by norm_num)
theorem B3441203 : Blo 2293435 3441203 := bstep (se 1 (by rfl) ⟨2580902, by rfl⟩ : syracuseStep 3441203 = 5161805) B5161805
theorem B2294135 : Blo 2293435 2294135 := bstep (se 1 (by rfl) ⟨1720601, by rfl⟩ : syracuseStep 2294135 = 3441203) B3441203
theorem B2903521 : Blo 2293435 2903521 := bbase (se 2 (by rfl) ⟨1088820, by rfl⟩ : syracuseStep 2903521 = 2177641) (by norm_num)
theorem B3871361 : Blo 2293435 3871361 := bstep (se 2 (by rfl) ⟨1451760, by rfl⟩ : syracuseStep 3871361 = 2903521) B2903521
theorem B2580907 : Blo 2293435 2580907 := bstep (se 1 (by rfl) ⟨1935680, by rfl⟩ : syracuseStep 2580907 = 3871361) B3871361
theorem B3441209 : Blo 2293435 3441209 := bstep (se 2 (by rfl) ⟨1290453, by rfl⟩ : syracuseStep 3441209 = 2580907) B2580907
theorem B2294139 : Blo 2293435 2294139 := bstep (se 1 (by rfl) ⟨1720604, by rfl⟩ : syracuseStep 2294139 = 3441209) B3441209
theorem B26131733 : Blo 2293435 26131733 := bbase (se 6 (by rfl) ⟨612462, by rfl⟩ : syracuseStep 26131733 = 1224925) (by norm_num)
theorem B17421155 : Blo 2293435 17421155 := bstep (se 1 (by rfl) ⟨13065866, by rfl⟩ : syracuseStep 17421155 = 26131733) B26131733
theorem B11614103 : Blo 2293435 11614103 := bstep (se 1 (by rfl) ⟨8710577, by rfl⟩ : syracuseStep 11614103 = 17421155) B17421155
theorem B7742735 : Blo 2293435 7742735 := bstep (se 1 (by rfl) ⟨5807051, by rfl⟩ : syracuseStep 7742735 = 11614103) B11614103
theorem B5161823 : Blo 2293435 5161823 := bstep (se 1 (by rfl) ⟨3871367, by rfl⟩ : syracuseStep 5161823 = 7742735) B7742735
theorem B3441215 : Blo 2293435 3441215 := bstep (se 1 (by rfl) ⟨2580911, by rfl⟩ : syracuseStep 3441215 = 5161823) B5161823
theorem B2294143 : Blo 2293435 2294143 := bstep (se 1 (by rfl) ⟨1720607, by rfl⟩ : syracuseStep 2294143 = 3441215) B3441215
theorem B3441221 : Blo 2293435 3441221 := bbase (se 4 (by rfl) ⟨322614, by rfl⟩ : syracuseStep 3441221 = 645229) (by norm_num)
theorem B2294147 : Blo 2293435 2294147 := bstep (se 1 (by rfl) ⟨1720610, by rfl⟩ : syracuseStep 2294147 = 3441221) B3441221
theorem B3871381 : Blo 2293435 3871381 := bbase (se 6 (by rfl) ⟨90735, by rfl⟩ : syracuseStep 3871381 = 181471) (by norm_num)
theorem B5161841 : Blo 2293435 5161841 := bstep (se 2 (by rfl) ⟨1935690, by rfl⟩ : syracuseStep 5161841 = 3871381) B3871381
theorem B3441227 : Blo 2293435 3441227 := bstep (se 1 (by rfl) ⟨2580920, by rfl⟩ : syracuseStep 3441227 = 5161841) B5161841
theorem B2294151 : Blo 2293435 2294151 := bstep (se 1 (by rfl) ⟨1720613, by rfl⟩ : syracuseStep 2294151 = 3441227) B3441227
theorem B2580925 : Blo 2293435 2580925 := bbase (se 3 (by rfl) ⟨483923, by rfl⟩ : syracuseStep 2580925 = 967847) (by norm_num)
theorem B3441233 : Blo 2293435 3441233 := bstep (se 2 (by rfl) ⟨1290462, by rfl⟩ : syracuseStep 3441233 = 2580925) B2580925
theorem B2294155 : Blo 2293435 2294155 := bstep (se 1 (by rfl) ⟨1720616, by rfl⟩ : syracuseStep 2294155 = 3441233) B3441233
theorem B7742789 : Blo 2293435 7742789 := bbase (se 4 (by rfl) ⟨725886, by rfl⟩ : syracuseStep 7742789 = 1451773) (by norm_num)
theorem B5161859 : Blo 2293435 5161859 := bstep (se 1 (by rfl) ⟨3871394, by rfl⟩ : syracuseStep 5161859 = 7742789) B7742789
theorem B3441239 : Blo 2293435 3441239 := bstep (se 1 (by rfl) ⟨2580929, by rfl⟩ : syracuseStep 3441239 = 5161859) B5161859
theorem B2294159 : Blo 2293435 2294159 := bstep (se 1 (by rfl) ⟨1720619, by rfl⟩ : syracuseStep 2294159 = 3441239) B3441239
theorem B3441245 : Blo 2293435 3441245 := bbase (se 3 (by rfl) ⟨645233, by rfl⟩ : syracuseStep 3441245 = 1290467) (by norm_num)
theorem B2294163 : Blo 2293435 2294163 := bstep (se 1 (by rfl) ⟨1720622, by rfl⟩ : syracuseStep 2294163 = 3441245) B3441245
theorem B5161877 : Blo 2293435 5161877 := bbase (se 6 (by rfl) ⟨120981, by rfl⟩ : syracuseStep 5161877 = 241963) (by norm_num)
theorem B3441251 : Blo 2293435 3441251 := bstep (se 1 (by rfl) ⟨2580938, by rfl⟩ : syracuseStep 3441251 = 5161877) B5161877
theorem B2294167 : Blo 2293435 2294167 := bstep (se 1 (by rfl) ⟨1720625, by rfl⟩ : syracuseStep 2294167 = 3441251) B3441251
theorem B3674821 : Blo 2293435 3674821 := bbase (se 4 (by rfl) ⟨344514, by rfl⟩ : syracuseStep 3674821 = 689029) (by norm_num)
theorem B4899761 : Blo 2293435 4899761 := bstep (se 2 (by rfl) ⟨1837410, by rfl⟩ : syracuseStep 4899761 = 3674821) B3674821
theorem B3266507 : Blo 2293435 3266507 := bstep (se 1 (by rfl) ⟨2449880, by rfl⟩ : syracuseStep 3266507 = 4899761) B4899761
theorem B8710685 : Blo 2293435 8710685 := bstep (se 3 (by rfl) ⟨1633253, by rfl⟩ : syracuseStep 8710685 = 3266507) B3266507
theorem B5807123 : Blo 2293435 5807123 := bstep (se 1 (by rfl) ⟨4355342, by rfl⟩ : syracuseStep 5807123 = 8710685) B8710685
theorem B3871415 : Blo 2293435 3871415 := bstep (se 1 (by rfl) ⟨2903561, by rfl⟩ : syracuseStep 3871415 = 5807123) B5807123
theorem B2580943 : Blo 2293435 2580943 := bstep (se 1 (by rfl) ⟨1935707, by rfl⟩ : syracuseStep 2580943 = 3871415) B3871415
theorem B3441257 : Blo 2293435 3441257 := bstep (se 2 (by rfl) ⟨1290471, by rfl⟩ : syracuseStep 3441257 = 2580943) B2580943
theorem B2294171 : Blo 2293435 2294171 := bstep (se 1 (by rfl) ⟨1720628, by rfl⟩ : syracuseStep 2294171 = 3441257) B3441257
theorem B7349653 : Blo 2293435 7349653 := bbase (se 6 (by rfl) ⟨172257, by rfl⟩ : syracuseStep 7349653 = 344515) (by norm_num)
theorem B9799537 : Blo 2293435 9799537 := bstep (se 2 (by rfl) ⟨3674826, by rfl⟩ : syracuseStep 9799537 = 7349653) B7349653
theorem B13066049 : Blo 2293435 13066049 := bstep (se 2 (by rfl) ⟨4899768, by rfl⟩ : syracuseStep 13066049 = 9799537) B9799537
theorem B8710699 : Blo 2293435 8710699 := bstep (se 1 (by rfl) ⟨6533024, by rfl⟩ : syracuseStep 8710699 = 13066049) B13066049
theorem B11614265 : Blo 2293435 11614265 := bstep (se 2 (by rfl) ⟨4355349, by rfl⟩ : syracuseStep 11614265 = 8710699) B8710699
theorem B7742843 : Blo 2293435 7742843 := bstep (se 1 (by rfl) ⟨5807132, by rfl⟩ : syracuseStep 7742843 = 11614265) B11614265
theorem B5161895 : Blo 2293435 5161895 := bstep (se 1 (by rfl) ⟨3871421, by rfl⟩ : syracuseStep 5161895 = 7742843) B7742843
theorem B3441263 : Blo 2293435 3441263 := bstep (se 1 (by rfl) ⟨2580947, by rfl⟩ : syracuseStep 3441263 = 5161895) B5161895
theorem B2294175 : Blo 2293435 2294175 := bstep (se 1 (by rfl) ⟨1720631, by rfl⟩ : syracuseStep 2294175 = 3441263) B3441263
theorem B3441269 : Blo 2293435 3441269 := bbase (se 5 (by rfl) ⟨161309, by rfl⟩ : syracuseStep 3441269 = 322619) (by norm_num)
theorem B2294179 : Blo 2293435 2294179 := bstep (se 1 (by rfl) ⟨1720634, by rfl⟩ : syracuseStep 2294179 = 3441269) B3441269
theorem B4355365 : Blo 2293435 4355365 := bbase (se 4 (by rfl) ⟨408315, by rfl⟩ : syracuseStep 4355365 = 816631) (by norm_num)
theorem B5807153 : Blo 2293435 5807153 := bstep (se 2 (by rfl) ⟨2177682, by rfl⟩ : syracuseStep 5807153 = 4355365) B4355365
theorem B3871435 : Blo 2293435 3871435 := bstep (se 1 (by rfl) ⟨2903576, by rfl⟩ : syracuseStep 3871435 = 5807153) B5807153
theorem B5161913 : Blo 2293435 5161913 := bstep (se 2 (by rfl) ⟨1935717, by rfl⟩ : syracuseStep 5161913 = 3871435) B3871435
theorem B3441275 : Blo 2293435 3441275 := bstep (se 1 (by rfl) ⟨2580956, by rfl⟩ : syracuseStep 3441275 = 5161913) B5161913
theorem B2294183 : Blo 2293435 2294183 := bstep (se 1 (by rfl) ⟨1720637, by rfl⟩ : syracuseStep 2294183 = 3441275) B3441275
theorem B2580961 : Blo 2293435 2580961 := bbase (se 2 (by rfl) ⟨967860, by rfl⟩ : syracuseStep 2580961 = 1935721) (by norm_num)
theorem B3441281 : Blo 2293435 3441281 := bstep (se 2 (by rfl) ⟨1290480, by rfl⟩ : syracuseStep 3441281 = 2580961) B2580961
theorem B2294187 : Blo 2293435 2294187 := bstep (se 1 (by rfl) ⟨1720640, by rfl⟩ : syracuseStep 2294187 = 3441281) B3441281
theorem B5807173 : Blo 2293435 5807173 := bbase (se 4 (by rfl) ⟨544422, by rfl⟩ : syracuseStep 5807173 = 1088845) (by norm_num)
theorem B7742897 : Blo 2293435 7742897 := bstep (se 2 (by rfl) ⟨2903586, by rfl⟩ : syracuseStep 7742897 = 5807173) B5807173
theorem B5161931 : Blo 2293435 5161931 := bstep (se 1 (by rfl) ⟨3871448, by rfl⟩ : syracuseStep 5161931 = 7742897) B7742897
theorem B3441287 : Blo 2293435 3441287 := bstep (se 1 (by rfl) ⟨2580965, by rfl⟩ : syracuseStep 3441287 = 5161931) B5161931
theorem B2294191 : Blo 2293435 2294191 := bstep (se 1 (by rfl) ⟨1720643, by rfl⟩ : syracuseStep 2294191 = 3441287) B3441287
theorem B3441293 : Blo 2293435 3441293 := bbase (se 3 (by rfl) ⟨645242, by rfl⟩ : syracuseStep 3441293 = 1290485) (by norm_num)
theorem B2294195 : Blo 2293435 2294195 := bstep (se 1 (by rfl) ⟨1720646, by rfl⟩ : syracuseStep 2294195 = 3441293) B3441293
theorem B5161949 : Blo 2293435 5161949 := bbase (se 3 (by rfl) ⟨967865, by rfl⟩ : syracuseStep 5161949 = 1935731) (by norm_num)
theorem B3441299 : Blo 2293435 3441299 := bstep (se 1 (by rfl) ⟨2580974, by rfl⟩ : syracuseStep 3441299 = 5161949) B5161949
theorem B2294199 : Blo 2293435 2294199 := bstep (se 1 (by rfl) ⟨1720649, by rfl⟩ : syracuseStep 2294199 = 3441299) B3441299
theorem B3871469 : Blo 2293435 3871469 := bbase (se 3 (by rfl) ⟨725900, by rfl⟩ : syracuseStep 3871469 = 1451801) (by norm_num)
theorem B2580979 : Blo 2293435 2580979 := bstep (se 1 (by rfl) ⟨1935734, by rfl⟩ : syracuseStep 2580979 = 3871469) B3871469
theorem B3441305 : Blo 2293435 3441305 := bstep (se 2 (by rfl) ⟨1290489, by rfl⟩ : syracuseStep 3441305 = 2580979) B2580979
theorem B2294203 : Blo 2293435 2294203 := bstep (se 1 (by rfl) ⟨1720652, by rfl⟩ : syracuseStep 2294203 = 3441305) B3441305
theorem B5886445 : Blo 2293435 5886445 := bbase (se 3 (by rfl) ⟨1103708, by rfl⟩ : syracuseStep 5886445 = 2207417) (by norm_num)
theorem B7848593 : Blo 2293435 7848593 := bstep (se 2 (by rfl) ⟨2943222, by rfl⟩ : syracuseStep 7848593 = 5886445) B5886445
theorem B5232395 : Blo 2293435 5232395 := bstep (se 1 (by rfl) ⟨3924296, by rfl⟩ : syracuseStep 5232395 = 7848593) B7848593
theorem B13953053 : Blo 2293435 13953053 := bstep (se 3 (by rfl) ⟨2616197, by rfl⟩ : syracuseStep 13953053 = 5232395) B5232395
theorem B9302035 : Blo 2293435 9302035 := bstep (se 1 (by rfl) ⟨6976526, by rfl⟩ : syracuseStep 9302035 = 13953053) B13953053
theorem B12402713 : Blo 2293435 12402713 := bstep (se 2 (by rfl) ⟨4651017, by rfl⟩ : syracuseStep 12402713 = 9302035) B9302035
theorem B8268475 : Blo 2293435 8268475 := bstep (se 1 (by rfl) ⟨6201356, by rfl⟩ : syracuseStep 8268475 = 12402713) B12402713
theorem B11024633 : Blo 2293435 11024633 := bstep (se 2 (by rfl) ⟨4134237, by rfl⟩ : syracuseStep 11024633 = 8268475) B8268475
theorem B29399021 : Blo 2293435 29399021 := bstep (se 3 (by rfl) ⟨5512316, by rfl⟩ : syracuseStep 29399021 = 11024633) B11024633
theorem B19599347 : Blo 2293435 19599347 := bstep (se 1 (by rfl) ⟨14699510, by rfl⟩ : syracuseStep 19599347 = 29399021) B29399021
theorem B13066231 : Blo 2293435 13066231 := bstep (se 1 (by rfl) ⟨9799673, by rfl⟩ : syracuseStep 13066231 = 19599347) B19599347
theorem B17421641 : Blo 2293435 17421641 := bstep (se 2 (by rfl) ⟨6533115, by rfl⟩ : syracuseStep 17421641 = 13066231) B13066231
theorem B11614427 : Blo 2293435 11614427 := bstep (se 1 (by rfl) ⟨8710820, by rfl⟩ : syracuseStep 11614427 = 17421641) B17421641
theorem B7742951 : Blo 2293435 7742951 := bstep (se 1 (by rfl) ⟨5807213, by rfl⟩ : syracuseStep 7742951 = 11614427) B11614427
theorem B5161967 : Blo 2293435 5161967 := bstep (se 1 (by rfl) ⟨3871475, by rfl⟩ : syracuseStep 5161967 = 7742951) B7742951
theorem B3441311 : Blo 2293435 3441311 := bstep (se 1 (by rfl) ⟨2580983, by rfl⟩ : syracuseStep 3441311 = 5161967) B5161967
theorem B2294207 : Blo 2293435 2294207 := bstep (se 1 (by rfl) ⟨1720655, by rfl⟩ : syracuseStep 2294207 = 3441311) B3441311
theorem B3441317 : Blo 2293435 3441317 := bbase (se 4 (by rfl) ⟨322623, by rfl⟩ : syracuseStep 3441317 = 645247) (by norm_num)
theorem B2294211 : Blo 2293435 2294211 := bstep (se 1 (by rfl) ⟨1720658, by rfl⟩ : syracuseStep 2294211 = 3441317) B3441317
theorem B2903617 : Blo 2293435 2903617 := bbase (se 2 (by rfl) ⟨1088856, by rfl⟩ : syracuseStep 2903617 = 2177713) (by norm_num)
theorem B3871489 : Blo 2293435 3871489 := bstep (se 2 (by rfl) ⟨1451808, by rfl⟩ : syracuseStep 3871489 = 2903617) B2903617
theorem B5161985 : Blo 2293435 5161985 := bstep (se 2 (by rfl) ⟨1935744, by rfl⟩ : syracuseStep 5161985 = 3871489) B3871489
theorem B3441323 : Blo 2293435 3441323 := bstep (se 1 (by rfl) ⟨2580992, by rfl⟩ : syracuseStep 3441323 = 5161985) B5161985
theorem B2294215 : Blo 2293435 2294215 := bstep (se 1 (by rfl) ⟨1720661, by rfl⟩ : syracuseStep 2294215 = 3441323) B3441323
theorem B2580997 : Blo 2293435 2580997 := bbase (se 4 (by rfl) ⟨241968, by rfl⟩ : syracuseStep 2580997 = 483937) (by norm_num)
theorem B3441329 : Blo 2293435 3441329 := bstep (se 2 (by rfl) ⟨1290498, by rfl⟩ : syracuseStep 3441329 = 2580997) B2580997
theorem B2294219 : Blo 2293435 2294219 := bstep (se 1 (by rfl) ⟨1720664, by rfl⟩ : syracuseStep 2294219 = 3441329) B3441329
theorem B3266581 : Blo 2293435 3266581 := bbase (se 6 (by rfl) ⟨76560, by rfl⟩ : syracuseStep 3266581 = 153121) (by norm_num)
theorem B4355441 : Blo 2293435 4355441 := bstep (se 2 (by rfl) ⟨1633290, by rfl⟩ : syracuseStep 4355441 = 3266581) B3266581
theorem B2903627 : Blo 2293435 2903627 := bstep (se 1 (by rfl) ⟨2177720, by rfl⟩ : syracuseStep 2903627 = 4355441) B4355441
theorem B7743005 : Blo 2293435 7743005 := bstep (se 3 (by rfl) ⟨1451813, by rfl⟩ : syracuseStep 7743005 = 2903627) B2903627
theorem B5162003 : Blo 2293435 5162003 := bstep (se 1 (by rfl) ⟨3871502, by rfl⟩ : syracuseStep 5162003 = 7743005) B7743005
theorem B3441335 : Blo 2293435 3441335 := bstep (se 1 (by rfl) ⟨2581001, by rfl⟩ : syracuseStep 3441335 = 5162003) B5162003
theorem B2294223 : Blo 2293435 2294223 := bstep (se 1 (by rfl) ⟨1720667, by rfl⟩ : syracuseStep 2294223 = 3441335) B3441335
theorem B3441341 : Blo 2293435 3441341 := bbase (se 3 (by rfl) ⟨645251, by rfl⟩ : syracuseStep 3441341 = 1290503) (by norm_num)
theorem B2294227 : Blo 2293435 2294227 := bstep (se 1 (by rfl) ⟨1720670, by rfl⟩ : syracuseStep 2294227 = 3441341) B3441341
theorem B5162021 : Blo 2293435 5162021 := bbase (se 4 (by rfl) ⟨483939, by rfl⟩ : syracuseStep 5162021 = 967879) (by norm_num)
theorem B3441347 : Blo 2293435 3441347 := bstep (se 1 (by rfl) ⟨2581010, by rfl⟩ : syracuseStep 3441347 = 5162021) B5162021
theorem B2294231 : Blo 2293435 2294231 := bstep (se 1 (by rfl) ⟨1720673, by rfl⟩ : syracuseStep 2294231 = 3441347) B3441347
theorem B5807285 : Blo 2293435 5807285 := bbase (se 5 (by rfl) ⟨272216, by rfl⟩ : syracuseStep 5807285 = 544433) (by norm_num)
theorem B3871523 : Blo 2293435 3871523 := bstep (se 1 (by rfl) ⟨2903642, by rfl⟩ : syracuseStep 3871523 = 5807285) B5807285
theorem B2581015 : Blo 2293435 2581015 := bstep (se 1 (by rfl) ⟨1935761, by rfl⟩ : syracuseStep 2581015 = 3871523) B3871523
theorem B3441353 : Blo 2293435 3441353 := bstep (se 2 (by rfl) ⟨1290507, by rfl⟩ : syracuseStep 3441353 = 2581015) B2581015
theorem B2294235 : Blo 2293435 2294235 := bstep (se 1 (by rfl) ⟨1720676, by rfl⟩ : syracuseStep 2294235 = 3441353) B3441353
theorem B2756197 : Blo 2293435 2756197 := bbase (se 4 (by rfl) ⟨258393, by rfl⟩ : syracuseStep 2756197 = 516787) (by norm_num)
theorem B14699717 : Blo 2293435 14699717 := bstep (se 4 (by rfl) ⟨1378098, by rfl⟩ : syracuseStep 14699717 = 2756197) B2756197
theorem B9799811 : Blo 2293435 9799811 := bstep (se 1 (by rfl) ⟨7349858, by rfl⟩ : syracuseStep 9799811 = 14699717) B14699717
theorem B6533207 : Blo 2293435 6533207 := bstep (se 1 (by rfl) ⟨4899905, by rfl⟩ : syracuseStep 6533207 = 9799811) B9799811
theorem B4355471 : Blo 2293435 4355471 := bstep (se 1 (by rfl) ⟨3266603, by rfl⟩ : syracuseStep 4355471 = 6533207) B6533207
theorem B11614589 : Blo 2293435 11614589 := bstep (se 3 (by rfl) ⟨2177735, by rfl⟩ : syracuseStep 11614589 = 4355471) B4355471
theorem B7743059 : Blo 2293435 7743059 := bstep (se 1 (by rfl) ⟨5807294, by rfl⟩ : syracuseStep 7743059 = 11614589) B11614589
theorem B5162039 : Blo 2293435 5162039 := bstep (se 1 (by rfl) ⟨3871529, by rfl⟩ : syracuseStep 5162039 = 7743059) B7743059
theorem B3441359 : Blo 2293435 3441359 := bstep (se 1 (by rfl) ⟨2581019, by rfl⟩ : syracuseStep 3441359 = 5162039) B5162039
theorem B2294239 : Blo 2293435 2294239 := bstep (se 1 (by rfl) ⟨1720679, by rfl⟩ : syracuseStep 2294239 = 3441359) B3441359
theorem B3441365 : Blo 2293435 3441365 := bbase (se 7 (by rfl) ⟨40328, by rfl⟩ : syracuseStep 3441365 = 80657) (by norm_num)
theorem B2294243 : Blo 2293435 2294243 := bstep (se 1 (by rfl) ⟨1720682, by rfl⟩ : syracuseStep 2294243 = 3441365) B3441365
theorem B2483389 : Blo 2293435 2483389 := bbase (se 3 (by rfl) ⟨465635, by rfl⟩ : syracuseStep 2483389 = 931271) (by norm_num)
theorem B3311185 : Blo 2293435 3311185 := bstep (se 2 (by rfl) ⟨1241694, by rfl⟩ : syracuseStep 3311185 = 2483389) B2483389
theorem B4414913 : Blo 2293435 4414913 := bstep (se 2 (by rfl) ⟨1655592, by rfl⟩ : syracuseStep 4414913 = 3311185) B3311185
theorem B2943275 : Blo 2293435 2943275 := bstep (se 1 (by rfl) ⟨2207456, by rfl⟩ : syracuseStep 2943275 = 4414913) B4414913
theorem B7848733 : Blo 2293435 7848733 := bstep (se 3 (by rfl) ⟨1471637, by rfl⟩ : syracuseStep 7848733 = 2943275) B2943275
theorem B10464977 : Blo 2293435 10464977 := bstep (se 2 (by rfl) ⟨3924366, by rfl⟩ : syracuseStep 10464977 = 7848733) B7848733
theorem B6976651 : Blo 2293435 6976651 := bstep (se 1 (by rfl) ⟨5232488, by rfl⟩ : syracuseStep 6976651 = 10464977) B10464977
theorem B9302201 : Blo 2293435 9302201 := bstep (se 2 (by rfl) ⟨3488325, by rfl⟩ : syracuseStep 9302201 = 6976651) B6976651
theorem B6201467 : Blo 2293435 6201467 := bstep (se 1 (by rfl) ⟨4651100, by rfl⟩ : syracuseStep 6201467 = 9302201) B9302201
theorem B4134311 : Blo 2293435 4134311 := bstep (se 1 (by rfl) ⟨3100733, by rfl⟩ : syracuseStep 4134311 = 6201467) B6201467
theorem B2756207 : Blo 2293435 2756207 := bstep (se 1 (by rfl) ⟨2067155, by rfl⟩ : syracuseStep 2756207 = 4134311) B4134311
theorem B7349885 : Blo 2293435 7349885 := bstep (se 3 (by rfl) ⟨1378103, by rfl⟩ : syracuseStep 7349885 = 2756207) B2756207
theorem B4899923 : Blo 2293435 4899923 := bstep (se 1 (by rfl) ⟨3674942, by rfl⟩ : syracuseStep 4899923 = 7349885) B7349885
theorem B3266615 : Blo 2293435 3266615 := bstep (se 1 (by rfl) ⟨2449961, by rfl⟩ : syracuseStep 3266615 = 4899923) B4899923
theorem B8710973 : Blo 2293435 8710973 := bstep (se 3 (by rfl) ⟨1633307, by rfl⟩ : syracuseStep 8710973 = 3266615) B3266615
theorem B5807315 : Blo 2293435 5807315 := bstep (se 1 (by rfl) ⟨4355486, by rfl⟩ : syracuseStep 5807315 = 8710973) B8710973
theorem B3871543 : Blo 2293435 3871543 := bstep (se 1 (by rfl) ⟨2903657, by rfl⟩ : syracuseStep 3871543 = 5807315) B5807315
theorem B5162057 : Blo 2293435 5162057 := bstep (se 2 (by rfl) ⟨1935771, by rfl⟩ : syracuseStep 5162057 = 3871543) B3871543
theorem B3441371 : Blo 2293435 3441371 := bstep (se 1 (by rfl) ⟨2581028, by rfl⟩ : syracuseStep 3441371 = 5162057) B5162057
theorem B2294247 : Blo 2293435 2294247 := bstep (se 1 (by rfl) ⟨1720685, by rfl⟩ : syracuseStep 2294247 = 3441371) B3441371
theorem B2581033 : Blo 2293435 2581033 := bbase (se 2 (by rfl) ⟨967887, by rfl⟩ : syracuseStep 2581033 = 1935775) (by norm_num)
theorem B3441377 : Blo 2293435 3441377 := bstep (se 2 (by rfl) ⟨1290516, by rfl⟩ : syracuseStep 3441377 = 2581033) B2581033
theorem B2294251 : Blo 2293435 2294251 := bstep (se 1 (by rfl) ⟨1720688, by rfl⟩ : syracuseStep 2294251 = 3441377) B3441377
theorem B5966885 : Blo 2293435 5966885 := bbase (se 4 (by rfl) ⟨559395, by rfl⟩ : syracuseStep 5966885 = 1118791) (by norm_num)
theorem B3977923 : Blo 2293435 3977923 := bstep (se 1 (by rfl) ⟨2983442, by rfl⟩ : syracuseStep 3977923 = 5966885) B5966885
theorem B5303897 : Blo 2293435 5303897 := bstep (se 2 (by rfl) ⟨1988961, by rfl⟩ : syracuseStep 5303897 = 3977923) B3977923
theorem B3535931 : Blo 2293435 3535931 := bstep (se 1 (by rfl) ⟨2651948, by rfl⟩ : syracuseStep 3535931 = 5303897) B5303897
theorem B9429149 : Blo 2293435 9429149 := bstep (se 3 (by rfl) ⟨1767965, by rfl⟩ : syracuseStep 9429149 = 3535931) B3535931
theorem B6286099 : Blo 2293435 6286099 := bstep (se 1 (by rfl) ⟨4714574, by rfl⟩ : syracuseStep 6286099 = 9429149) B9429149
theorem B8381465 : Blo 2293435 8381465 := bstep (se 2 (by rfl) ⟨3143049, by rfl⟩ : syracuseStep 8381465 = 6286099) B6286099
theorem B5587643 : Blo 2293435 5587643 := bstep (se 1 (by rfl) ⟨4190732, by rfl⟩ : syracuseStep 5587643 = 8381465) B8381465
theorem B14900381 : Blo 2293435 14900381 := bstep (se 3 (by rfl) ⟨2793821, by rfl⟩ : syracuseStep 14900381 = 5587643) B5587643
theorem B9933587 : Blo 2293435 9933587 := bstep (se 1 (by rfl) ⟨7450190, by rfl⟩ : syracuseStep 9933587 = 14900381) B14900381
theorem B6622391 : Blo 2293435 6622391 := bstep (se 1 (by rfl) ⟨4966793, by rfl⟩ : syracuseStep 6622391 = 9933587) B9933587
theorem B4414927 : Blo 2293435 4414927 := bstep (se 1 (by rfl) ⟨3311195, by rfl⟩ : syracuseStep 4414927 = 6622391) B6622391
theorem B5886569 : Blo 2293435 5886569 := bstep (se 2 (by rfl) ⟨2207463, by rfl⟩ : syracuseStep 5886569 = 4414927) B4414927
theorem B3924379 : Blo 2293435 3924379 := bstep (se 1 (by rfl) ⟨2943284, by rfl⟩ : syracuseStep 3924379 = 5886569) B5886569
theorem B5232505 : Blo 2293435 5232505 := bstep (se 2 (by rfl) ⟨1962189, by rfl⟩ : syracuseStep 5232505 = 3924379) B3924379
theorem B6976673 : Blo 2293435 6976673 := bstep (se 2 (by rfl) ⟨2616252, by rfl⟩ : syracuseStep 6976673 = 5232505) B5232505
theorem B4651115 : Blo 2293435 4651115 := bstep (se 1 (by rfl) ⟨3488336, by rfl⟩ : syracuseStep 4651115 = 6976673) B6976673
theorem B12402973 : Blo 2293435 12402973 := bstep (se 3 (by rfl) ⟨2325557, by rfl⟩ : syracuseStep 12402973 = 4651115) B4651115
theorem B16537297 : Blo 2293435 16537297 := bstep (se 2 (by rfl) ⟨6201486, by rfl⟩ : syracuseStep 16537297 = 12402973) B12402973
theorem B22049729 : Blo 2293435 22049729 := bstep (se 2 (by rfl) ⟨8268648, by rfl⟩ : syracuseStep 22049729 = 16537297) B16537297
theorem B14699819 : Blo 2293435 14699819 := bstep (se 1 (by rfl) ⟨11024864, by rfl⟩ : syracuseStep 14699819 = 22049729) B22049729
theorem B9799879 : Blo 2293435 9799879 := bstep (se 1 (by rfl) ⟨7349909, by rfl⟩ : syracuseStep 9799879 = 14699819) B14699819
theorem B13066505 : Blo 2293435 13066505 := bstep (se 2 (by rfl) ⟨4899939, by rfl⟩ : syracuseStep 13066505 = 9799879) B9799879
theorem B8711003 : Blo 2293435 8711003 := bstep (se 1 (by rfl) ⟨6533252, by rfl⟩ : syracuseStep 8711003 = 13066505) B13066505
theorem B5807335 : Blo 2293435 5807335 := bstep (se 1 (by rfl) ⟨4355501, by rfl⟩ : syracuseStep 5807335 = 8711003) B8711003
theorem B7743113 : Blo 2293435 7743113 := bstep (se 2 (by rfl) ⟨2903667, by rfl⟩ : syracuseStep 7743113 = 5807335) B5807335
theorem B5162075 : Blo 2293435 5162075 := bstep (se 1 (by rfl) ⟨3871556, by rfl⟩ : syracuseStep 5162075 = 7743113) B7743113
theorem B3441383 : Blo 2293435 3441383 := bstep (se 1 (by rfl) ⟨2581037, by rfl⟩ : syracuseStep 3441383 = 5162075) B5162075
theorem B2294255 : Blo 2293435 2294255 := bstep (se 1 (by rfl) ⟨1720691, by rfl⟩ : syracuseStep 2294255 = 3441383) B3441383
theorem B3441389 : Blo 2293435 3441389 := bbase (se 3 (by rfl) ⟨645260, by rfl⟩ : syracuseStep 3441389 = 1290521) (by norm_num)
theorem B2294259 : Blo 2293435 2294259 := bstep (se 1 (by rfl) ⟨1720694, by rfl⟩ : syracuseStep 2294259 = 3441389) B3441389
theorem B5162093 : Blo 2293435 5162093 := bbase (se 3 (by rfl) ⟨967892, by rfl⟩ : syracuseStep 5162093 = 1935785) (by norm_num)
theorem B3441395 : Blo 2293435 3441395 := bstep (se 1 (by rfl) ⟨2581046, by rfl⟩ : syracuseStep 3441395 = 5162093) B5162093
theorem B2294263 : Blo 2293435 2294263 := bstep (se 1 (by rfl) ⟨1720697, by rfl⟩ : syracuseStep 2294263 = 3441395) B3441395
theorem B4355525 : Blo 2293435 4355525 := bbase (se 4 (by rfl) ⟨408330, by rfl⟩ : syracuseStep 4355525 = 816661) (by norm_num)
theorem B2903683 : Blo 2293435 2903683 := bstep (se 1 (by rfl) ⟨2177762, by rfl⟩ : syracuseStep 2903683 = 4355525) B4355525
theorem B3871577 : Blo 2293435 3871577 := bstep (se 2 (by rfl) ⟨1451841, by rfl⟩ : syracuseStep 3871577 = 2903683) B2903683
theorem B2581051 : Blo 2293435 2581051 := bstep (se 1 (by rfl) ⟨1935788, by rfl⟩ : syracuseStep 2581051 = 3871577) B3871577
theorem B3441401 : Blo 2293435 3441401 := bstep (se 2 (by rfl) ⟨1290525, by rfl⟩ : syracuseStep 3441401 = 2581051) B2581051
theorem B2294267 : Blo 2293435 2294267 := bstep (se 1 (by rfl) ⟨1720700, by rfl⟩ : syracuseStep 2294267 = 3441401) B3441401
theorem B5232541 : Blo 2293435 5232541 := bbase (se 3 (by rfl) ⟨981101, by rfl⟩ : syracuseStep 5232541 = 1962203) (by norm_num)
theorem B6976721 : Blo 2293435 6976721 := bstep (se 2 (by rfl) ⟨2616270, by rfl⟩ : syracuseStep 6976721 = 5232541) B5232541
theorem B4651147 : Blo 2293435 4651147 := bstep (se 1 (by rfl) ⟨3488360, by rfl⟩ : syracuseStep 4651147 = 6976721) B6976721
theorem B6201529 : Blo 2293435 6201529 := bstep (se 2 (by rfl) ⟨2325573, by rfl⟩ : syracuseStep 6201529 = 4651147) B4651147
theorem B33074821 : Blo 2293435 33074821 := bstep (se 4 (by rfl) ⟨3100764, by rfl⟩ : syracuseStep 33074821 = 6201529) B6201529
theorem B44099761 : Blo 2293435 44099761 := bstep (se 2 (by rfl) ⟨16537410, by rfl⟩ : syracuseStep 44099761 = 33074821) B33074821
theorem B58799681 : Blo 2293435 58799681 := bstep (se 2 (by rfl) ⟨22049880, by rfl⟩ : syracuseStep 58799681 = 44099761) B44099761
theorem B39199787 : Blo 2293435 39199787 := bstep (se 1 (by rfl) ⟨29399840, by rfl⟩ : syracuseStep 39199787 = 58799681) B58799681
theorem B26133191 : Blo 2293435 26133191 := bstep (se 1 (by rfl) ⟨19599893, by rfl⟩ : syracuseStep 26133191 = 39199787) B39199787
theorem B17422127 : Blo 2293435 17422127 := bstep (se 1 (by rfl) ⟨13066595, by rfl⟩ : syracuseStep 17422127 = 26133191) B26133191
theorem B11614751 : Blo 2293435 11614751 := bstep (se 1 (by rfl) ⟨8711063, by rfl⟩ : syracuseStep 11614751 = 17422127) B17422127
theorem B7743167 : Blo 2293435 7743167 := bstep (se 1 (by rfl) ⟨5807375, by rfl⟩ : syracuseStep 7743167 = 11614751) B11614751
theorem B5162111 : Blo 2293435 5162111 := bstep (se 1 (by rfl) ⟨3871583, by rfl⟩ : syracuseStep 5162111 = 7743167) B7743167
theorem B3441407 : Blo 2293435 3441407 := bstep (se 1 (by rfl) ⟨2581055, by rfl⟩ : syracuseStep 3441407 = 5162111) B5162111
theorem B2294271 : Blo 2293435 2294271 := bstep (se 1 (by rfl) ⟨1720703, by rfl⟩ : syracuseStep 2294271 = 3441407) B3441407
theorem B3441413 : Blo 2293435 3441413 := bbase (se 4 (by rfl) ⟨322632, by rfl⟩ : syracuseStep 3441413 = 645265) (by norm_num)
theorem B2294275 : Blo 2293435 2294275 := bstep (se 1 (by rfl) ⟨1720706, by rfl⟩ : syracuseStep 2294275 = 3441413) B3441413
theorem B3871597 : Blo 2293435 3871597 := bbase (se 3 (by rfl) ⟨725924, by rfl⟩ : syracuseStep 3871597 = 1451849) (by norm_num)
theorem B5162129 : Blo 2293435 5162129 := bstep (se 2 (by rfl) ⟨1935798, by rfl⟩ : syracuseStep 5162129 = 3871597) B3871597
theorem B3441419 : Blo 2293435 3441419 := bstep (se 1 (by rfl) ⟨2581064, by rfl⟩ : syracuseStep 3441419 = 5162129) B5162129
theorem B2294279 : Blo 2293435 2294279 := bstep (se 1 (by rfl) ⟨1720709, by rfl⟩ : syracuseStep 2294279 = 3441419) B3441419
theorem B2581069 : Blo 2293435 2581069 := bbase (se 3 (by rfl) ⟨483950, by rfl⟩ : syracuseStep 2581069 = 967901) (by norm_num)
theorem B3441425 : Blo 2293435 3441425 := bstep (se 2 (by rfl) ⟨1290534, by rfl⟩ : syracuseStep 3441425 = 2581069) B2581069
theorem B2294283 : Blo 2293435 2294283 := bstep (se 1 (by rfl) ⟨1720712, by rfl⟩ : syracuseStep 2294283 = 3441425) B3441425
theorem B7743221 : Blo 2293435 7743221 := bbase (se 5 (by rfl) ⟨362963, by rfl⟩ : syracuseStep 7743221 = 725927) (by norm_num)
theorem B5162147 : Blo 2293435 5162147 := bstep (se 1 (by rfl) ⟨3871610, by rfl⟩ : syracuseStep 5162147 = 7743221) B7743221
theorem B3441431 : Blo 2293435 3441431 := bstep (se 1 (by rfl) ⟨2581073, by rfl⟩ : syracuseStep 3441431 = 5162147) B5162147
theorem B2294287 : Blo 2293435 2294287 := bstep (se 1 (by rfl) ⟨1720715, by rfl⟩ : syracuseStep 2294287 = 3441431) B3441431
theorem B3441437 : Blo 2293435 3441437 := bbase (se 3 (by rfl) ⟨645269, by rfl⟩ : syracuseStep 3441437 = 1290539) (by norm_num)
theorem B2294291 : Blo 2293435 2294291 := bstep (se 1 (by rfl) ⟨1720718, by rfl⟩ : syracuseStep 2294291 = 3441437) B3441437
theorem B5162165 : Blo 2293435 5162165 := bbase (se 5 (by rfl) ⟨241976, by rfl⟩ : syracuseStep 5162165 = 483953) (by norm_num)
theorem B3441443 : Blo 2293435 3441443 := bstep (se 1 (by rfl) ⟨2581082, by rfl⟩ : syracuseStep 3441443 = 5162165) B5162165
theorem B2294295 : Blo 2293435 2294295 := bstep (se 1 (by rfl) ⟨1720721, by rfl⟩ : syracuseStep 2294295 = 3441443) B3441443
theorem B2450017 : Blo 2293435 2450017 := bbase (se 2 (by rfl) ⟨918756, by rfl⟩ : syracuseStep 2450017 = 1837513) (by norm_num)
theorem B13066757 : Blo 2293435 13066757 := bstep (se 4 (by rfl) ⟨1225008, by rfl⟩ : syracuseStep 13066757 = 2450017) B2450017
theorem B8711171 : Blo 2293435 8711171 := bstep (se 1 (by rfl) ⟨6533378, by rfl⟩ : syracuseStep 8711171 = 13066757) B13066757
theorem B5807447 : Blo 2293435 5807447 := bstep (se 1 (by rfl) ⟨4355585, by rfl⟩ : syracuseStep 5807447 = 8711171) B8711171
theorem B3871631 : Blo 2293435 3871631 := bstep (se 1 (by rfl) ⟨2903723, by rfl⟩ : syracuseStep 3871631 = 5807447) B5807447
theorem B2581087 : Blo 2293435 2581087 := bstep (se 1 (by rfl) ⟨1935815, by rfl⟩ : syracuseStep 2581087 = 3871631) B3871631
theorem B3441449 : Blo 2293435 3441449 := bstep (se 2 (by rfl) ⟨1290543, by rfl⟩ : syracuseStep 3441449 = 2581087) B2581087
theorem B2294299 : Blo 2293435 2294299 := bstep (se 1 (by rfl) ⟨1720724, by rfl⟩ : syracuseStep 2294299 = 3441449) B3441449
theorem B2450021 : Blo 2293435 2450021 := bbase (se 4 (by rfl) ⟨229689, by rfl⟩ : syracuseStep 2450021 = 459379) (by norm_num)
theorem B6533389 : Blo 2293435 6533389 := bstep (se 3 (by rfl) ⟨1225010, by rfl⟩ : syracuseStep 6533389 = 2450021) B2450021
theorem B8711185 : Blo 2293435 8711185 := bstep (se 2 (by rfl) ⟨3266694, by rfl⟩ : syracuseStep 8711185 = 6533389) B6533389
theorem B11614913 : Blo 2293435 11614913 := bstep (se 2 (by rfl) ⟨4355592, by rfl⟩ : syracuseStep 11614913 = 8711185) B8711185
theorem B7743275 : Blo 2293435 7743275 := bstep (se 1 (by rfl) ⟨5807456, by rfl⟩ : syracuseStep 7743275 = 11614913) B11614913
theorem B5162183 : Blo 2293435 5162183 := bstep (se 1 (by rfl) ⟨3871637, by rfl⟩ : syracuseStep 5162183 = 7743275) B7743275
theorem B3441455 : Blo 2293435 3441455 := bstep (se 1 (by rfl) ⟨2581091, by rfl⟩ : syracuseStep 3441455 = 5162183) B5162183
theorem B2294303 : Blo 2293435 2294303 := bstep (se 1 (by rfl) ⟨1720727, by rfl⟩ : syracuseStep 2294303 = 3441455) B3441455
theorem B3441461 : Blo 2293435 3441461 := bbase (se 5 (by rfl) ⟨161318, by rfl⟩ : syracuseStep 3441461 = 322637) (by norm_num)
theorem B2294307 : Blo 2293435 2294307 := bstep (se 1 (by rfl) ⟨1720730, by rfl⟩ : syracuseStep 2294307 = 3441461) B3441461
theorem B5807477 : Blo 2293435 5807477 := bbase (se 5 (by rfl) ⟨272225, by rfl⟩ : syracuseStep 5807477 = 544451) (by norm_num)
theorem B3871651 : Blo 2293435 3871651 := bstep (se 1 (by rfl) ⟨2903738, by rfl⟩ : syracuseStep 3871651 = 5807477) B5807477
theorem B5162201 : Blo 2293435 5162201 := bstep (se 2 (by rfl) ⟨1935825, by rfl⟩ : syracuseStep 5162201 = 3871651) B3871651
theorem B3441467 : Blo 2293435 3441467 := bstep (se 1 (by rfl) ⟨2581100, by rfl⟩ : syracuseStep 3441467 = 5162201) B5162201
theorem B2294311 : Blo 2293435 2294311 := bstep (se 1 (by rfl) ⟨1720733, by rfl⟩ : syracuseStep 2294311 = 3441467) B3441467
theorem B2581105 : Blo 2293435 2581105 := bbase (se 2 (by rfl) ⟨967914, by rfl⟩ : syracuseStep 2581105 = 1935829) (by norm_num)
theorem B3441473 : Blo 2293435 3441473 := bstep (se 2 (by rfl) ⟨1290552, by rfl⟩ : syracuseStep 3441473 = 2581105) B2581105
theorem B2294315 : Blo 2293435 2294315 := bstep (se 1 (by rfl) ⟨1720736, by rfl⟩ : syracuseStep 2294315 = 3441473) B3441473
theorem B11025173 : Blo 2293435 11025173 := bbase (se 6 (by rfl) ⟨258402, by rfl⟩ : syracuseStep 11025173 = 516805) (by norm_num)
theorem B7350115 : Blo 2293435 7350115 := bstep (se 1 (by rfl) ⟨5512586, by rfl⟩ : syracuseStep 7350115 = 11025173) B11025173
theorem B9800153 : Blo 2293435 9800153 := bstep (se 2 (by rfl) ⟨3675057, by rfl⟩ : syracuseStep 9800153 = 7350115) B7350115
theorem B6533435 : Blo 2293435 6533435 := bstep (se 1 (by rfl) ⟨4900076, by rfl⟩ : syracuseStep 6533435 = 9800153) B9800153
theorem B4355623 : Blo 2293435 4355623 := bstep (se 1 (by rfl) ⟨3266717, by rfl⟩ : syracuseStep 4355623 = 6533435) B6533435
theorem B5807497 : Blo 2293435 5807497 := bstep (se 2 (by rfl) ⟨2177811, by rfl⟩ : syracuseStep 5807497 = 4355623) B4355623
theorem B7743329 : Blo 2293435 7743329 := bstep (se 2 (by rfl) ⟨2903748, by rfl⟩ : syracuseStep 7743329 = 5807497) B5807497
theorem B5162219 : Blo 2293435 5162219 := bstep (se 1 (by rfl) ⟨3871664, by rfl⟩ : syracuseStep 5162219 = 7743329) B7743329
theorem B3441479 : Blo 2293435 3441479 := bstep (se 1 (by rfl) ⟨2581109, by rfl⟩ : syracuseStep 3441479 = 5162219) B5162219
theorem B2294319 : Blo 2293435 2294319 := bstep (se 1 (by rfl) ⟨1720739, by rfl⟩ : syracuseStep 2294319 = 3441479) B3441479
theorem B3441485 : Blo 2293435 3441485 := bbase (se 3 (by rfl) ⟨645278, by rfl⟩ : syracuseStep 3441485 = 1290557) (by norm_num)
theorem B2294323 : Blo 2293435 2294323 := bstep (se 1 (by rfl) ⟨1720742, by rfl⟩ : syracuseStep 2294323 = 3441485) B3441485
theorem B5162237 : Blo 2293435 5162237 := bbase (se 3 (by rfl) ⟨967919, by rfl⟩ : syracuseStep 5162237 = 1935839) (by norm_num)
theorem B3441491 : Blo 2293435 3441491 := bstep (se 1 (by rfl) ⟨2581118, by rfl⟩ : syracuseStep 3441491 = 5162237) B5162237
theorem B2294327 : Blo 2293435 2294327 := bstep (se 1 (by rfl) ⟨1720745, by rfl⟩ : syracuseStep 2294327 = 3441491) B3441491
theorem B3871685 : Blo 2293435 3871685 := bbase (se 4 (by rfl) ⟨362970, by rfl⟩ : syracuseStep 3871685 = 725941) (by norm_num)
theorem B2581123 : Blo 2293435 2581123 := bstep (se 1 (by rfl) ⟨1935842, by rfl⟩ : syracuseStep 2581123 = 3871685) B3871685
theorem B3441497 : Blo 2293435 3441497 := bstep (se 2 (by rfl) ⟨1290561, by rfl⟩ : syracuseStep 3441497 = 2581123) B2581123
theorem B2294331 : Blo 2293435 2294331 := bstep (se 1 (by rfl) ⟨1720748, by rfl⟩ : syracuseStep 2294331 = 3441497) B3441497
theorem B17422613 : Blo 2293435 17422613 := bbase (se 6 (by rfl) ⟨408342, by rfl⟩ : syracuseStep 17422613 = 816685) (by norm_num)
theorem B11615075 : Blo 2293435 11615075 := bstep (se 1 (by rfl) ⟨8711306, by rfl⟩ : syracuseStep 11615075 = 17422613) B17422613
theorem B7743383 : Blo 2293435 7743383 := bstep (se 1 (by rfl) ⟨5807537, by rfl⟩ : syracuseStep 7743383 = 11615075) B11615075
theorem B5162255 : Blo 2293435 5162255 := bstep (se 1 (by rfl) ⟨3871691, by rfl⟩ : syracuseStep 5162255 = 7743383) B7743383
theorem B3441503 : Blo 2293435 3441503 := bstep (se 1 (by rfl) ⟨2581127, by rfl⟩ : syracuseStep 3441503 = 5162255) B5162255
theorem B2294335 : Blo 2293435 2294335 := bstep (se 1 (by rfl) ⟨1720751, by rfl⟩ : syracuseStep 2294335 = 3441503) B3441503
theorem B3441509 : Blo 2293435 3441509 := bbase (se 4 (by rfl) ⟨322641, by rfl⟩ : syracuseStep 3441509 = 645283) (by norm_num)
theorem B2294339 : Blo 2293435 2294339 := bstep (se 1 (by rfl) ⟨1720754, by rfl⟩ : syracuseStep 2294339 = 3441509) B3441509
theorem B4355669 : Blo 2293435 4355669 := bbase (se 8 (by rfl) ⟨25521, by rfl⟩ : syracuseStep 4355669 = 51043) (by norm_num)
theorem B2903779 : Blo 2293435 2903779 := bstep (se 1 (by rfl) ⟨2177834, by rfl⟩ : syracuseStep 2903779 = 4355669) B4355669
theorem B3871705 : Blo 2293435 3871705 := bstep (se 2 (by rfl) ⟨1451889, by rfl⟩ : syracuseStep 3871705 = 2903779) B2903779
theorem B5162273 : Blo 2293435 5162273 := bstep (se 2 (by rfl) ⟨1935852, by rfl⟩ : syracuseStep 5162273 = 3871705) B3871705
theorem B3441515 : Blo 2293435 3441515 := bstep (se 1 (by rfl) ⟨2581136, by rfl⟩ : syracuseStep 3441515 = 5162273) B5162273
theorem B2294343 : Blo 2293435 2294343 := bstep (se 1 (by rfl) ⟨1720757, by rfl⟩ : syracuseStep 2294343 = 3441515) B3441515
theorem B2581141 : Blo 2293435 2581141 := bbase (se 6 (by rfl) ⟨60495, by rfl⟩ : syracuseStep 2581141 = 120991) (by norm_num)
theorem B3441521 : Blo 2293435 3441521 := bstep (se 2 (by rfl) ⟨1290570, by rfl⟩ : syracuseStep 3441521 = 2581141) B2581141
theorem B2294347 : Blo 2293435 2294347 := bstep (se 1 (by rfl) ⟨1720760, by rfl⟩ : syracuseStep 2294347 = 3441521) B3441521
theorem B2903789 : Blo 2293435 2903789 := bbase (se 3 (by rfl) ⟨544460, by rfl⟩ : syracuseStep 2903789 = 1088921) (by norm_num)
theorem B7743437 : Blo 2293435 7743437 := bstep (se 3 (by rfl) ⟨1451894, by rfl⟩ : syracuseStep 7743437 = 2903789) B2903789
theorem B5162291 : Blo 2293435 5162291 := bstep (se 1 (by rfl) ⟨3871718, by rfl⟩ : syracuseStep 5162291 = 7743437) B7743437
theorem B3441527 : Blo 2293435 3441527 := bstep (se 1 (by rfl) ⟨2581145, by rfl⟩ : syracuseStep 3441527 = 5162291) B5162291
theorem B2294351 : Blo 2293435 2294351 := bstep (se 1 (by rfl) ⟨1720763, by rfl⟩ : syracuseStep 2294351 = 3441527) B3441527
theorem B3441533 : Blo 2293435 3441533 := bbase (se 3 (by rfl) ⟨645287, by rfl⟩ : syracuseStep 3441533 = 1290575) (by norm_num)
theorem B2294355 : Blo 2293435 2294355 := bstep (se 1 (by rfl) ⟨1720766, by rfl⟩ : syracuseStep 2294355 = 3441533) B3441533
theorem B5162309 : Blo 2293435 5162309 := bbase (se 4 (by rfl) ⟨483966, by rfl⟩ : syracuseStep 5162309 = 967933) (by norm_num)
theorem B3441539 : Blo 2293435 3441539 := bstep (se 1 (by rfl) ⟨2581154, by rfl⟩ : syracuseStep 3441539 = 5162309) B5162309
theorem B2294359 : Blo 2293435 2294359 := bstep (se 1 (by rfl) ⟨1720769, by rfl⟩ : syracuseStep 2294359 = 3441539) B3441539
theorem B5512693 : Blo 2293435 5512693 := bbase (se 5 (by rfl) ⟨258407, by rfl⟩ : syracuseStep 5512693 = 516815) (by norm_num)
theorem B7350257 : Blo 2293435 7350257 := bstep (se 2 (by rfl) ⟨2756346, by rfl⟩ : syracuseStep 7350257 = 5512693) B5512693
theorem B4900171 : Blo 2293435 4900171 := bstep (se 1 (by rfl) ⟨3675128, by rfl⟩ : syracuseStep 4900171 = 7350257) B7350257
theorem B6533561 : Blo 2293435 6533561 := bstep (se 2 (by rfl) ⟨2450085, by rfl⟩ : syracuseStep 6533561 = 4900171) B4900171
theorem B4355707 : Blo 2293435 4355707 := bstep (se 1 (by rfl) ⟨3266780, by rfl⟩ : syracuseStep 4355707 = 6533561) B6533561
theorem B5807609 : Blo 2293435 5807609 := bstep (se 2 (by rfl) ⟨2177853, by rfl⟩ : syracuseStep 5807609 = 4355707) B4355707
theorem B3871739 : Blo 2293435 3871739 := bstep (se 1 (by rfl) ⟨2903804, by rfl⟩ : syracuseStep 3871739 = 5807609) B5807609
theorem B2581159 : Blo 2293435 2581159 := bstep (se 1 (by rfl) ⟨1935869, by rfl⟩ : syracuseStep 2581159 = 3871739) B3871739
theorem B3441545 : Blo 2293435 3441545 := bstep (se 2 (by rfl) ⟨1290579, by rfl⟩ : syracuseStep 3441545 = 2581159) B2581159
theorem B2294363 : Blo 2293435 2294363 := bstep (se 1 (by rfl) ⟨1720772, by rfl⟩ : syracuseStep 2294363 = 3441545) B3441545
theorem B11615237 : Blo 2293435 11615237 := bbase (se 4 (by rfl) ⟨1088928, by rfl⟩ : syracuseStep 11615237 = 2177857) (by norm_num)
theorem B7743491 : Blo 2293435 7743491 := bstep (se 1 (by rfl) ⟨5807618, by rfl⟩ : syracuseStep 7743491 = 11615237) B11615237
theorem B5162327 : Blo 2293435 5162327 := bstep (se 1 (by rfl) ⟨3871745, by rfl⟩ : syracuseStep 5162327 = 7743491) B7743491
theorem B3441551 : Blo 2293435 3441551 := bstep (se 1 (by rfl) ⟨2581163, by rfl⟩ : syracuseStep 3441551 = 5162327) B5162327
theorem B2294367 : Blo 2293435 2294367 := bstep (se 1 (by rfl) ⟨1720775, by rfl⟩ : syracuseStep 2294367 = 3441551) B3441551
theorem B3441557 : Blo 2293435 3441557 := bbase (se 6 (by rfl) ⟨80661, by rfl⟩ : syracuseStep 3441557 = 161323) (by norm_num)
theorem B2294371 : Blo 2293435 2294371 := bstep (se 1 (by rfl) ⟨1720778, by rfl⟩ : syracuseStep 2294371 = 3441557) B3441557
theorem B13067189 : Blo 2293435 13067189 := bbase (se 5 (by rfl) ⟨612524, by rfl⟩ : syracuseStep 13067189 = 1225049) (by norm_num)
theorem B8711459 : Blo 2293435 8711459 := bstep (se 1 (by rfl) ⟨6533594, by rfl⟩ : syracuseStep 8711459 = 13067189) B13067189
theorem B5807639 : Blo 2293435 5807639 := bstep (se 1 (by rfl) ⟨4355729, by rfl⟩ : syracuseStep 5807639 = 8711459) B8711459
theorem B3871759 : Blo 2293435 3871759 := bstep (se 1 (by rfl) ⟨2903819, by rfl⟩ : syracuseStep 3871759 = 5807639) B5807639
theorem B5162345 : Blo 2293435 5162345 := bstep (se 2 (by rfl) ⟨1935879, by rfl⟩ : syracuseStep 5162345 = 3871759) B3871759
theorem B3441563 : Blo 2293435 3441563 := bstep (se 1 (by rfl) ⟨2581172, by rfl⟩ : syracuseStep 3441563 = 5162345) B5162345
theorem B2294375 : Blo 2293435 2294375 := bstep (se 1 (by rfl) ⟨1720781, by rfl⟩ : syracuseStep 2294375 = 3441563) B3441563
theorem B2581177 : Blo 2293435 2581177 := bbase (se 2 (by rfl) ⟨967941, by rfl⟩ : syracuseStep 2581177 = 1935883) (by norm_num)
theorem B3441569 : Blo 2293435 3441569 := bstep (se 2 (by rfl) ⟨1290588, by rfl⟩ : syracuseStep 3441569 = 2581177) B2581177
theorem B2294379 : Blo 2293435 2294379 := bstep (se 1 (by rfl) ⟨1720784, by rfl⟩ : syracuseStep 2294379 = 3441569) B3441569
theorem B4900213 : Blo 2293435 4900213 := bbase (se 5 (by rfl) ⟨229697, by rfl⟩ : syracuseStep 4900213 = 459395) (by norm_num)
theorem B6533617 : Blo 2293435 6533617 := bstep (se 2 (by rfl) ⟨2450106, by rfl⟩ : syracuseStep 6533617 = 4900213) B4900213
theorem B8711489 : Blo 2293435 8711489 := bstep (se 2 (by rfl) ⟨3266808, by rfl⟩ : syracuseStep 8711489 = 6533617) B6533617
theorem B5807659 : Blo 2293435 5807659 := bstep (se 1 (by rfl) ⟨4355744, by rfl⟩ : syracuseStep 5807659 = 8711489) B8711489
theorem B7743545 : Blo 2293435 7743545 := bstep (se 2 (by rfl) ⟨2903829, by rfl⟩ : syracuseStep 7743545 = 5807659) B5807659
theorem B5162363 : Blo 2293435 5162363 := bstep (se 1 (by rfl) ⟨3871772, by rfl⟩ : syracuseStep 5162363 = 7743545) B7743545
theorem B3441575 : Blo 2293435 3441575 := bstep (se 1 (by rfl) ⟨2581181, by rfl⟩ : syracuseStep 3441575 = 5162363) B5162363
theorem B2294383 : Blo 2293435 2294383 := bstep (se 1 (by rfl) ⟨1720787, by rfl⟩ : syracuseStep 2294383 = 3441575) B3441575
theorem B3441581 : Blo 2293435 3441581 := bbase (se 3 (by rfl) ⟨645296, by rfl⟩ : syracuseStep 3441581 = 1290593) (by norm_num)
theorem B2294387 : Blo 2293435 2294387 := bstep (se 1 (by rfl) ⟨1720790, by rfl⟩ : syracuseStep 2294387 = 3441581) B3441581
theorem B5162381 : Blo 2293435 5162381 := bbase (se 3 (by rfl) ⟨967946, by rfl⟩ : syracuseStep 5162381 = 1935893) (by norm_num)
theorem B3441587 : Blo 2293435 3441587 := bstep (se 1 (by rfl) ⟨2581190, by rfl⟩ : syracuseStep 3441587 = 5162381) B5162381
theorem B2294391 : Blo 2293435 2294391 := bstep (se 1 (by rfl) ⟨1720793, by rfl⟩ : syracuseStep 2294391 = 3441587) B3441587
theorem B2903845 : Blo 2293435 2903845 := bbase (se 4 (by rfl) ⟨272235, by rfl⟩ : syracuseStep 2903845 = 544471) (by norm_num)
theorem B3871793 : Blo 2293435 3871793 := bstep (se 2 (by rfl) ⟨1451922, by rfl⟩ : syracuseStep 3871793 = 2903845) B2903845
theorem B2581195 : Blo 2293435 2581195 := bstep (se 1 (by rfl) ⟨1935896, by rfl⟩ : syracuseStep 2581195 = 3871793) B3871793
theorem B3441593 : Blo 2293435 3441593 := bstep (se 2 (by rfl) ⟨1290597, by rfl⟩ : syracuseStep 3441593 = 2581195) B2581195
theorem B2294395 : Blo 2293435 2294395 := bstep (se 1 (by rfl) ⟨1720796, by rfl⟩ : syracuseStep 2294395 = 3441593) B3441593
theorem B8830405 : Blo 2293435 8830405 := bbase (se 4 (by rfl) ⟨827850, by rfl⟩ : syracuseStep 8830405 = 1655701) (by norm_num)
theorem B11773873 : Blo 2293435 11773873 := bstep (se 2 (by rfl) ⟨4415202, by rfl⟩ : syracuseStep 11773873 = 8830405) B8830405
theorem B15698497 : Blo 2293435 15698497 := bstep (se 2 (by rfl) ⟨5886936, by rfl⟩ : syracuseStep 15698497 = 11773873) B11773873
theorem B20931329 : Blo 2293435 20931329 := bstep (se 2 (by rfl) ⟨7849248, by rfl⟩ : syracuseStep 20931329 = 15698497) B15698497
theorem B55816877 : Blo 2293435 55816877 := bstep (se 3 (by rfl) ⟨10465664, by rfl⟩ : syracuseStep 55816877 = 20931329) B20931329
theorem B37211251 : Blo 2293435 37211251 := bstep (se 1 (by rfl) ⟨27908438, by rfl⟩ : syracuseStep 37211251 = 55816877) B55816877
theorem B49615001 : Blo 2293435 49615001 := bstep (se 2 (by rfl) ⟨18605625, by rfl⟩ : syracuseStep 49615001 = 37211251) B37211251
theorem B33076667 : Blo 2293435 33076667 := bstep (se 1 (by rfl) ⟨24807500, by rfl⟩ : syracuseStep 33076667 = 49615001) B49615001
theorem B22051111 : Blo 2293435 22051111 := bstep (se 1 (by rfl) ⟨16538333, by rfl⟩ : syracuseStep 22051111 = 33076667) B33076667
theorem B29401481 : Blo 2293435 29401481 := bstep (se 2 (by rfl) ⟨11025555, by rfl⟩ : syracuseStep 29401481 = 22051111) B22051111
theorem B19600987 : Blo 2293435 19600987 := bstep (se 1 (by rfl) ⟨14700740, by rfl⟩ : syracuseStep 19600987 = 29401481) B29401481
theorem B26134649 : Blo 2293435 26134649 := bstep (se 2 (by rfl) ⟨9800493, by rfl⟩ : syracuseStep 26134649 = 19600987) B19600987
theorem B17423099 : Blo 2293435 17423099 := bstep (se 1 (by rfl) ⟨13067324, by rfl⟩ : syracuseStep 17423099 = 26134649) B26134649
theorem B11615399 : Blo 2293435 11615399 := bstep (se 1 (by rfl) ⟨8711549, by rfl⟩ : syracuseStep 11615399 = 17423099) B17423099
theorem B7743599 : Blo 2293435 7743599 := bstep (se 1 (by rfl) ⟨5807699, by rfl⟩ : syracuseStep 7743599 = 11615399) B11615399
theorem B5162399 : Blo 2293435 5162399 := bstep (se 1 (by rfl) ⟨3871799, by rfl⟩ : syracuseStep 5162399 = 7743599) B7743599
theorem B3441599 : Blo 2293435 3441599 := bstep (se 1 (by rfl) ⟨2581199, by rfl⟩ : syracuseStep 3441599 = 5162399) B5162399
theorem B2294399 : Blo 2293435 2294399 := bstep (se 1 (by rfl) ⟨1720799, by rfl⟩ : syracuseStep 2294399 = 3441599) B3441599
theorem B3441605 : Blo 2293435 3441605 := bbase (se 4 (by rfl) ⟨322650, by rfl⟩ : syracuseStep 3441605 = 645301) (by norm_num)
theorem B2294403 : Blo 2293435 2294403 := bstep (se 1 (by rfl) ⟨1720802, by rfl⟩ : syracuseStep 2294403 = 3441605) B3441605
theorem B3871813 : Blo 2293435 3871813 := bbase (se 4 (by rfl) ⟨362982, by rfl⟩ : syracuseStep 3871813 = 725965) (by norm_num)
theorem B5162417 : Blo 2293435 5162417 := bstep (se 2 (by rfl) ⟨1935906, by rfl⟩ : syracuseStep 5162417 = 3871813) B3871813
theorem B3441611 : Blo 2293435 3441611 := bstep (se 1 (by rfl) ⟨2581208, by rfl⟩ : syracuseStep 3441611 = 5162417) B5162417
theorem B2294407 : Blo 2293435 2294407 := bstep (se 1 (by rfl) ⟨1720805, by rfl⟩ : syracuseStep 2294407 = 3441611) B3441611
theorem B2581213 : Blo 2293435 2581213 := bbase (se 3 (by rfl) ⟨483977, by rfl⟩ : syracuseStep 2581213 = 967955) (by norm_num)
theorem B3441617 : Blo 2293435 3441617 := bstep (se 2 (by rfl) ⟨1290606, by rfl⟩ : syracuseStep 3441617 = 2581213) B2581213
theorem B2294411 : Blo 2293435 2294411 := bstep (se 1 (by rfl) ⟨1720808, by rfl⟩ : syracuseStep 2294411 = 3441617) B3441617
theorem B7743653 : Blo 2293435 7743653 := bbase (se 4 (by rfl) ⟨725967, by rfl⟩ : syracuseStep 7743653 = 1451935) (by norm_num)
theorem B5162435 : Blo 2293435 5162435 := bstep (se 1 (by rfl) ⟨3871826, by rfl⟩ : syracuseStep 5162435 = 7743653) B7743653
theorem B3441623 : Blo 2293435 3441623 := bstep (se 1 (by rfl) ⟨2581217, by rfl⟩ : syracuseStep 3441623 = 5162435) B5162435
theorem B2294415 : Blo 2293435 2294415 := bstep (se 1 (by rfl) ⟨1720811, by rfl⟩ : syracuseStep 2294415 = 3441623) B3441623
theorem B3441629 : Blo 2293435 3441629 := bbase (se 3 (by rfl) ⟨645305, by rfl⟩ : syracuseStep 3441629 = 1290611) (by norm_num)
theorem B2294419 : Blo 2293435 2294419 := bstep (se 1 (by rfl) ⟨1720814, by rfl⟩ : syracuseStep 2294419 = 3441629) B3441629
theorem B5162453 : Blo 2293435 5162453 := bbase (se 7 (by rfl) ⟨60497, by rfl⟩ : syracuseStep 5162453 = 120995) (by norm_num)
theorem B3441635 : Blo 2293435 3441635 := bstep (se 1 (by rfl) ⟨2581226, by rfl⟩ : syracuseStep 3441635 = 5162453) B5162453
theorem B2294423 : Blo 2293435 2294423 := bstep (se 1 (by rfl) ⟨1720817, by rfl⟩ : syracuseStep 2294423 = 3441635) B3441635
theorem B2943505 : Blo 2293435 2943505 := bbase (se 2 (by rfl) ⟨1103814, by rfl⟩ : syracuseStep 2943505 = 2207629) (by norm_num)
theorem B15698693 : Blo 2293435 15698693 := bstep (se 4 (by rfl) ⟨1471752, by rfl⟩ : syracuseStep 15698693 = 2943505) B2943505
theorem B10465795 : Blo 2293435 10465795 := bstep (se 1 (by rfl) ⟨7849346, by rfl⟩ : syracuseStep 10465795 = 15698693) B15698693
theorem B13954393 : Blo 2293435 13954393 := bstep (se 2 (by rfl) ⟨5232897, by rfl⟩ : syracuseStep 13954393 = 10465795) B10465795
theorem B18605857 : Blo 2293435 18605857 := bstep (se 2 (by rfl) ⟨6977196, by rfl⟩ : syracuseStep 18605857 = 13954393) B13954393
theorem B24807809 : Blo 2293435 24807809 := bstep (se 2 (by rfl) ⟨9302928, by rfl⟩ : syracuseStep 24807809 = 18605857) B18605857
theorem B16538539 : Blo 2293435 16538539 := bstep (se 1 (by rfl) ⟨12403904, by rfl⟩ : syracuseStep 16538539 = 24807809) B24807809
theorem B22051385 : Blo 2293435 22051385 := bstep (se 2 (by rfl) ⟨8269269, by rfl⟩ : syracuseStep 22051385 = 16538539) B16538539
theorem B14700923 : Blo 2293435 14700923 := bstep (se 1 (by rfl) ⟨11025692, by rfl⟩ : syracuseStep 14700923 = 22051385) B22051385
theorem B9800615 : Blo 2293435 9800615 := bstep (se 1 (by rfl) ⟨7350461, by rfl⟩ : syracuseStep 9800615 = 14700923) B14700923
theorem B6533743 : Blo 2293435 6533743 := bstep (se 1 (by rfl) ⟨4900307, by rfl⟩ : syracuseStep 6533743 = 9800615) B9800615
theorem B8711657 : Blo 2293435 8711657 := bstep (se 2 (by rfl) ⟨3266871, by rfl⟩ : syracuseStep 8711657 = 6533743) B6533743
theorem B5807771 : Blo 2293435 5807771 := bstep (se 1 (by rfl) ⟨4355828, by rfl⟩ : syracuseStep 5807771 = 8711657) B8711657
theorem B3871847 : Blo 2293435 3871847 := bstep (se 1 (by rfl) ⟨2903885, by rfl⟩ : syracuseStep 3871847 = 5807771) B5807771
theorem B2581231 : Blo 2293435 2581231 := bstep (se 1 (by rfl) ⟨1935923, by rfl⟩ : syracuseStep 2581231 = 3871847) B3871847
theorem B3441641 : Blo 2293435 3441641 := bstep (se 2 (by rfl) ⟨1290615, by rfl⟩ : syracuseStep 3441641 = 2581231) B2581231
theorem B2294427 : Blo 2293435 2294427 := bstep (se 1 (by rfl) ⟨1720820, by rfl⟩ : syracuseStep 2294427 = 3441641) B3441641
theorem B12403925 : Blo 2293435 12403925 := bbase (se 7 (by rfl) ⟨145358, by rfl⟩ : syracuseStep 12403925 = 290717) (by norm_num)
theorem B8269283 : Blo 2293435 8269283 := bstep (se 1 (by rfl) ⟨6201962, by rfl⟩ : syracuseStep 8269283 = 12403925) B12403925
theorem B5512855 : Blo 2293435 5512855 := bstep (se 1 (by rfl) ⟨4134641, by rfl⟩ : syracuseStep 5512855 = 8269283) B8269283
theorem B7350473 : Blo 2293435 7350473 := bstep (se 2 (by rfl) ⟨2756427, by rfl⟩ : syracuseStep 7350473 = 5512855) B5512855
theorem B19601261 : Blo 2293435 19601261 := bstep (se 3 (by rfl) ⟨3675236, by rfl⟩ : syracuseStep 19601261 = 7350473) B7350473
theorem B13067507 : Blo 2293435 13067507 := bstep (se 1 (by rfl) ⟨9800630, by rfl⟩ : syracuseStep 13067507 = 19601261) B19601261
theorem B8711671 : Blo 2293435 8711671 := bstep (se 1 (by rfl) ⟨6533753, by rfl⟩ : syracuseStep 8711671 = 13067507) B13067507
theorem B11615561 : Blo 2293435 11615561 := bstep (se 2 (by rfl) ⟨4355835, by rfl⟩ : syracuseStep 11615561 = 8711671) B8711671
theorem B7743707 : Blo 2293435 7743707 := bstep (se 1 (by rfl) ⟨5807780, by rfl⟩ : syracuseStep 7743707 = 11615561) B11615561
theorem B5162471 : Blo 2293435 5162471 := bstep (se 1 (by rfl) ⟨3871853, by rfl⟩ : syracuseStep 5162471 = 7743707) B7743707
theorem B3441647 : Blo 2293435 3441647 := bstep (se 1 (by rfl) ⟨2581235, by rfl⟩ : syracuseStep 3441647 = 5162471) B5162471
theorem B2294431 : Blo 2293435 2294431 := bstep (se 1 (by rfl) ⟨1720823, by rfl⟩ : syracuseStep 2294431 = 3441647) B3441647
theorem B3441653 : Blo 2293435 3441653 := bbase (se 5 (by rfl) ⟨161327, by rfl⟩ : syracuseStep 3441653 = 322655) (by norm_num)
theorem B2294435 : Blo 2293435 2294435 := bstep (se 1 (by rfl) ⟨1720826, by rfl⟩ : syracuseStep 2294435 = 3441653) B3441653
theorem B4900333 : Blo 2293435 4900333 := bbase (se 3 (by rfl) ⟨918812, by rfl⟩ : syracuseStep 4900333 = 1837625) (by norm_num)
theorem B6533777 : Blo 2293435 6533777 := bstep (se 2 (by rfl) ⟨2450166, by rfl⟩ : syracuseStep 6533777 = 4900333) B4900333
theorem B4355851 : Blo 2293435 4355851 := bstep (se 1 (by rfl) ⟨3266888, by rfl⟩ : syracuseStep 4355851 = 6533777) B6533777
theorem B5807801 : Blo 2293435 5807801 := bstep (se 2 (by rfl) ⟨2177925, by rfl⟩ : syracuseStep 5807801 = 4355851) B4355851
theorem B3871867 : Blo 2293435 3871867 := bstep (se 1 (by rfl) ⟨2903900, by rfl⟩ : syracuseStep 3871867 = 5807801) B5807801
theorem B5162489 : Blo 2293435 5162489 := bstep (se 2 (by rfl) ⟨1935933, by rfl⟩ : syracuseStep 5162489 = 3871867) B3871867
theorem B3441659 : Blo 2293435 3441659 := bstep (se 1 (by rfl) ⟨2581244, by rfl⟩ : syracuseStep 3441659 = 5162489) B5162489
theorem B2294439 : Blo 2293435 2294439 := bstep (se 1 (by rfl) ⟨1720829, by rfl⟩ : syracuseStep 2294439 = 3441659) B3441659
theorem B2581249 : Blo 2293435 2581249 := bbase (se 2 (by rfl) ⟨967968, by rfl⟩ : syracuseStep 2581249 = 1935937) (by norm_num)
theorem B3441665 : Blo 2293435 3441665 := bstep (se 2 (by rfl) ⟨1290624, by rfl⟩ : syracuseStep 3441665 = 2581249) B2581249
theorem B2294443 : Blo 2293435 2294443 := bstep (se 1 (by rfl) ⟨1720832, by rfl⟩ : syracuseStep 2294443 = 3441665) B3441665
theorem B5807821 : Blo 2293435 5807821 := bbase (se 3 (by rfl) ⟨1088966, by rfl⟩ : syracuseStep 5807821 = 2177933) (by norm_num)
theorem B7743761 : Blo 2293435 7743761 := bstep (se 2 (by rfl) ⟨2903910, by rfl⟩ : syracuseStep 7743761 = 5807821) B5807821
theorem B5162507 : Blo 2293435 5162507 := bstep (se 1 (by rfl) ⟨3871880, by rfl⟩ : syracuseStep 5162507 = 7743761) B7743761
theorem B3441671 : Blo 2293435 3441671 := bstep (se 1 (by rfl) ⟨2581253, by rfl⟩ : syracuseStep 3441671 = 5162507) B5162507
theorem B2294447 : Blo 2293435 2294447 := bstep (se 1 (by rfl) ⟨1720835, by rfl⟩ : syracuseStep 2294447 = 3441671) B3441671
theorem B3441677 : Blo 2293435 3441677 := bbase (se 3 (by rfl) ⟨645314, by rfl⟩ : syracuseStep 3441677 = 1290629) (by norm_num)
theorem B2294451 : Blo 2293435 2294451 := bstep (se 1 (by rfl) ⟨1720838, by rfl⟩ : syracuseStep 2294451 = 3441677) B3441677
theorem B5162525 : Blo 2293435 5162525 := bbase (se 3 (by rfl) ⟨967973, by rfl⟩ : syracuseStep 5162525 = 1935947) (by norm_num)
theorem B3441683 : Blo 2293435 3441683 := bstep (se 1 (by rfl) ⟨2581262, by rfl⟩ : syracuseStep 3441683 = 5162525) B5162525
theorem B2294455 : Blo 2293435 2294455 := bstep (se 1 (by rfl) ⟨1720841, by rfl⟩ : syracuseStep 2294455 = 3441683) B3441683
theorem B3871901 : Blo 2293435 3871901 := bbase (se 3 (by rfl) ⟨725981, by rfl⟩ : syracuseStep 3871901 = 1451963) (by norm_num)
theorem B2581267 : Blo 2293435 2581267 := bstep (se 1 (by rfl) ⟨1935950, by rfl⟩ : syracuseStep 2581267 = 3871901) B3871901
theorem B3441689 : Blo 2293435 3441689 := bstep (se 2 (by rfl) ⟨1290633, by rfl⟩ : syracuseStep 3441689 = 2581267) B2581267
theorem B2294459 : Blo 2293435 2294459 := bstep (se 1 (by rfl) ⟨1720844, by rfl⟩ : syracuseStep 2294459 = 3441689) B3441689
theorem B10465957 : Blo 2293435 10465957 := bbase (se 4 (by rfl) ⟨981183, by rfl⟩ : syracuseStep 10465957 = 1962367) (by norm_num)
theorem B13954609 : Blo 2293435 13954609 := bstep (se 2 (by rfl) ⟨5232978, by rfl⟩ : syracuseStep 13954609 = 10465957) B10465957
theorem B74424581 : Blo 2293435 74424581 := bstep (se 4 (by rfl) ⟨6977304, by rfl⟩ : syracuseStep 74424581 = 13954609) B13954609
theorem B49616387 : Blo 2293435 49616387 := bstep (se 1 (by rfl) ⟨37212290, by rfl⟩ : syracuseStep 49616387 = 74424581) B74424581
theorem B33077591 : Blo 2293435 33077591 := bstep (se 1 (by rfl) ⟨24808193, by rfl⟩ : syracuseStep 33077591 = 49616387) B49616387
theorem B22051727 : Blo 2293435 22051727 := bstep (se 1 (by rfl) ⟨16538795, by rfl⟩ : syracuseStep 22051727 = 33077591) B33077591
theorem B14701151 : Blo 2293435 14701151 := bstep (se 1 (by rfl) ⟨11025863, by rfl⟩ : syracuseStep 14701151 = 22051727) B22051727
theorem B9800767 : Blo 2293435 9800767 := bstep (se 1 (by rfl) ⟨7350575, by rfl⟩ : syracuseStep 9800767 = 14701151) B14701151
theorem B13067689 : Blo 2293435 13067689 := bstep (se 2 (by rfl) ⟨4900383, by rfl⟩ : syracuseStep 13067689 = 9800767) B9800767
theorem B17423585 : Blo 2293435 17423585 := bstep (se 2 (by rfl) ⟨6533844, by rfl⟩ : syracuseStep 17423585 = 13067689) B13067689
theorem B11615723 : Blo 2293435 11615723 := bstep (se 1 (by rfl) ⟨8711792, by rfl⟩ : syracuseStep 11615723 = 17423585) B17423585
theorem B7743815 : Blo 2293435 7743815 := bstep (se 1 (by rfl) ⟨5807861, by rfl⟩ : syracuseStep 7743815 = 11615723) B11615723
theorem B5162543 : Blo 2293435 5162543 := bstep (se 1 (by rfl) ⟨3871907, by rfl⟩ : syracuseStep 5162543 = 7743815) B7743815
theorem B3441695 : Blo 2293435 3441695 := bstep (se 1 (by rfl) ⟨2581271, by rfl⟩ : syracuseStep 3441695 = 5162543) B5162543
theorem B2294463 : Blo 2293435 2294463 := bstep (se 1 (by rfl) ⟨1720847, by rfl⟩ : syracuseStep 2294463 = 3441695) B3441695
theorem B3441701 : Blo 2293435 3441701 := bbase (se 4 (by rfl) ⟨322659, by rfl⟩ : syracuseStep 3441701 = 645319) (by norm_num)
theorem B2294467 : Blo 2293435 2294467 := bstep (se 1 (by rfl) ⟨1720850, by rfl⟩ : syracuseStep 2294467 = 3441701) B3441701
theorem B2903941 : Blo 2293435 2903941 := bbase (se 4 (by rfl) ⟨272244, by rfl⟩ : syracuseStep 2903941 = 544489) (by norm_num)
theorem B3871921 : Blo 2293435 3871921 := bstep (se 2 (by rfl) ⟨1451970, by rfl⟩ : syracuseStep 3871921 = 2903941) B2903941
theorem B5162561 : Blo 2293435 5162561 := bstep (se 2 (by rfl) ⟨1935960, by rfl⟩ : syracuseStep 5162561 = 3871921) B3871921
theorem B3441707 : Blo 2293435 3441707 := bstep (se 1 (by rfl) ⟨2581280, by rfl⟩ : syracuseStep 3441707 = 5162561) B5162561
theorem B2294471 : Blo 2293435 2294471 := bstep (se 1 (by rfl) ⟨1720853, by rfl⟩ : syracuseStep 2294471 = 3441707) B3441707
theorem B2581285 : Blo 2293435 2581285 := bbase (se 4 (by rfl) ⟨241995, by rfl⟩ : syracuseStep 2581285 = 483991) (by norm_num)
theorem B3441713 : Blo 2293435 3441713 := bstep (se 2 (by rfl) ⟨1290642, by rfl⟩ : syracuseStep 3441713 = 2581285) B2581285
theorem B2294475 : Blo 2293435 2294475 := bstep (se 1 (by rfl) ⟨1720856, by rfl⟩ : syracuseStep 2294475 = 3441713) B3441713
theorem B9800837 : Blo 2293435 9800837 := bbase (se 4 (by rfl) ⟨918828, by rfl⟩ : syracuseStep 9800837 = 1837657) (by norm_num)
theorem B6533891 : Blo 2293435 6533891 := bstep (se 1 (by rfl) ⟨4900418, by rfl⟩ : syracuseStep 6533891 = 9800837) B9800837
theorem B4355927 : Blo 2293435 4355927 := bstep (se 1 (by rfl) ⟨3266945, by rfl⟩ : syracuseStep 4355927 = 6533891) B6533891
theorem B2903951 : Blo 2293435 2903951 := bstep (se 1 (by rfl) ⟨2177963, by rfl⟩ : syracuseStep 2903951 = 4355927) B4355927
theorem B7743869 : Blo 2293435 7743869 := bstep (se 3 (by rfl) ⟨1451975, by rfl⟩ : syracuseStep 7743869 = 2903951) B2903951
theorem B5162579 : Blo 2293435 5162579 := bstep (se 1 (by rfl) ⟨3871934, by rfl⟩ : syracuseStep 5162579 = 7743869) B7743869
theorem B3441719 : Blo 2293435 3441719 := bstep (se 1 (by rfl) ⟨2581289, by rfl⟩ : syracuseStep 3441719 = 5162579) B5162579
theorem B2294479 : Blo 2293435 2294479 := bstep (se 1 (by rfl) ⟨1720859, by rfl⟩ : syracuseStep 2294479 = 3441719) B3441719
theorem B3441725 : Blo 2293435 3441725 := bbase (se 3 (by rfl) ⟨645323, by rfl⟩ : syracuseStep 3441725 = 1290647) (by norm_num)
theorem B2294483 : Blo 2293435 2294483 := bstep (se 1 (by rfl) ⟨1720862, by rfl⟩ : syracuseStep 2294483 = 3441725) B3441725
theorem B5162597 : Blo 2293435 5162597 := bbase (se 4 (by rfl) ⟨483993, by rfl⟩ : syracuseStep 5162597 = 967987) (by norm_num)
theorem B3441731 : Blo 2293435 3441731 := bstep (se 1 (by rfl) ⟨2581298, by rfl⟩ : syracuseStep 3441731 = 5162597) B5162597
theorem B2294487 : Blo 2293435 2294487 := bstep (se 1 (by rfl) ⟨1720865, by rfl⟩ : syracuseStep 2294487 = 3441731) B3441731
theorem B5807933 : Blo 2293435 5807933 := bbase (se 3 (by rfl) ⟨1088987, by rfl⟩ : syracuseStep 5807933 = 2177975) (by norm_num)
theorem B3871955 : Blo 2293435 3871955 := bstep (se 1 (by rfl) ⟨2903966, by rfl⟩ : syracuseStep 3871955 = 5807933) B5807933
theorem B2581303 : Blo 2293435 2581303 := bstep (se 1 (by rfl) ⟨1935977, by rfl⟩ : syracuseStep 2581303 = 3871955) B3871955
theorem B3441737 : Blo 2293435 3441737 := bstep (se 2 (by rfl) ⟨1290651, by rfl⟩ : syracuseStep 3441737 = 2581303) B2581303
theorem B2294491 : Blo 2293435 2294491 := bstep (se 1 (by rfl) ⟨1720868, by rfl⟩ : syracuseStep 2294491 = 3441737) B3441737
theorem B4355957 : Blo 2293435 4355957 := bbase (se 5 (by rfl) ⟨204185, by rfl⟩ : syracuseStep 4355957 = 408371) (by norm_num)
theorem B11615885 : Blo 2293435 11615885 := bstep (se 3 (by rfl) ⟨2177978, by rfl⟩ : syracuseStep 11615885 = 4355957) B4355957
theorem B7743923 : Blo 2293435 7743923 := bstep (se 1 (by rfl) ⟨5807942, by rfl⟩ : syracuseStep 7743923 = 11615885) B11615885
theorem B5162615 : Blo 2293435 5162615 := bstep (se 1 (by rfl) ⟨3871961, by rfl⟩ : syracuseStep 5162615 = 7743923) B7743923
theorem B3441743 : Blo 2293435 3441743 := bstep (se 1 (by rfl) ⟨2581307, by rfl⟩ : syracuseStep 3441743 = 5162615) B5162615
theorem B2294495 : Blo 2293435 2294495 := bstep (se 1 (by rfl) ⟨1720871, by rfl⟩ : syracuseStep 2294495 = 3441743) B3441743
theorem B3441749 : Blo 2293435 3441749 := bbase (se 8 (by rfl) ⟨20166, by rfl⟩ : syracuseStep 3441749 = 40333) (by norm_num)
theorem B2294499 : Blo 2293435 2294499 := bstep (se 1 (by rfl) ⟨1720874, by rfl⟩ : syracuseStep 2294499 = 3441749) B3441749
theorem B3143389 : Blo 2293435 3143389 := bbase (se 3 (by rfl) ⟨589385, by rfl⟩ : syracuseStep 3143389 = 1178771) (by norm_num)
theorem B4191185 : Blo 2293435 4191185 := bstep (se 2 (by rfl) ⟨1571694, by rfl⟩ : syracuseStep 4191185 = 3143389) B3143389
theorem B2794123 : Blo 2293435 2794123 := bstep (se 1 (by rfl) ⟨2095592, by rfl⟩ : syracuseStep 2794123 = 4191185) B4191185
theorem B3725497 : Blo 2293435 3725497 := bstep (se 2 (by rfl) ⟨1397061, by rfl⟩ : syracuseStep 3725497 = 2794123) B2794123
theorem B19869317 : Blo 2293435 19869317 := bstep (se 4 (by rfl) ⟨1862748, by rfl⟩ : syracuseStep 19869317 = 3725497) B3725497
theorem B13246211 : Blo 2293435 13246211 := bstep (se 1 (by rfl) ⟨9934658, by rfl⟩ : syracuseStep 13246211 = 19869317) B19869317
theorem B35323229 : Blo 2293435 35323229 := bstep (se 3 (by rfl) ⟨6623105, by rfl⟩ : syracuseStep 35323229 = 13246211) B13246211
theorem B23548819 : Blo 2293435 23548819 := bstep (se 1 (by rfl) ⟨17661614, by rfl⟩ : syracuseStep 23548819 = 35323229) B35323229
theorem B31398425 : Blo 2293435 31398425 := bstep (se 2 (by rfl) ⟨11774409, by rfl⟩ : syracuseStep 31398425 = 23548819) B23548819
theorem B20932283 : Blo 2293435 20932283 := bstep (se 1 (by rfl) ⟨15699212, by rfl⟩ : syracuseStep 20932283 = 31398425) B31398425
theorem B13954855 : Blo 2293435 13954855 := bstep (se 1 (by rfl) ⟨10466141, by rfl⟩ : syracuseStep 13954855 = 20932283) B20932283
theorem B18606473 : Blo 2293435 18606473 := bstep (se 2 (by rfl) ⟨6977427, by rfl⟩ : syracuseStep 18606473 = 13954855) B13954855
theorem B12404315 : Blo 2293435 12404315 := bstep (se 1 (by rfl) ⟨9303236, by rfl⟩ : syracuseStep 12404315 = 18606473) B18606473
theorem B8269543 : Blo 2293435 8269543 := bstep (se 1 (by rfl) ⟨6202157, by rfl⟩ : syracuseStep 8269543 = 12404315) B12404315
theorem B11026057 : Blo 2293435 11026057 := bstep (se 2 (by rfl) ⟨4134771, by rfl⟩ : syracuseStep 11026057 = 8269543) B8269543
theorem B14701409 : Blo 2293435 14701409 := bstep (se 2 (by rfl) ⟨5513028, by rfl⟩ : syracuseStep 14701409 = 11026057) B11026057
theorem B9800939 : Blo 2293435 9800939 := bstep (se 1 (by rfl) ⟨7350704, by rfl⟩ : syracuseStep 9800939 = 14701409) B14701409
theorem B6533959 : Blo 2293435 6533959 := bstep (se 1 (by rfl) ⟨4900469, by rfl⟩ : syracuseStep 6533959 = 9800939) B9800939
theorem B8711945 : Blo 2293435 8711945 := bstep (se 2 (by rfl) ⟨3266979, by rfl⟩ : syracuseStep 8711945 = 6533959) B6533959
theorem B5807963 : Blo 2293435 5807963 := bstep (se 1 (by rfl) ⟨4355972, by rfl⟩ : syracuseStep 5807963 = 8711945) B8711945
theorem B3871975 : Blo 2293435 3871975 := bstep (se 1 (by rfl) ⟨2903981, by rfl⟩ : syracuseStep 3871975 = 5807963) B5807963
theorem B5162633 : Blo 2293435 5162633 := bstep (se 2 (by rfl) ⟨1935987, by rfl⟩ : syracuseStep 5162633 = 3871975) B3871975
theorem B3441755 : Blo 2293435 3441755 := bstep (se 1 (by rfl) ⟨2581316, by rfl⟩ : syracuseStep 3441755 = 5162633) B5162633
theorem B2294503 : Blo 2293435 2294503 := bstep (se 1 (by rfl) ⟨1720877, by rfl⟩ : syracuseStep 2294503 = 3441755) B3441755
theorem B2581321 : Blo 2293435 2581321 := bbase (se 2 (by rfl) ⟨967995, by rfl⟩ : syracuseStep 2581321 = 1935991) (by norm_num)
theorem B3441761 : Blo 2293435 3441761 := bstep (se 2 (by rfl) ⟨1290660, by rfl⟩ : syracuseStep 3441761 = 2581321) B2581321
theorem B2294507 : Blo 2293435 2294507 := bstep (se 1 (by rfl) ⟨1720880, by rfl⟩ : syracuseStep 2294507 = 3441761) B3441761
theorem B2325817 : Blo 2293435 2325817 := bbase (se 2 (by rfl) ⟨872181, by rfl⟩ : syracuseStep 2325817 = 1744363) (by norm_num)
theorem B12404357 : Blo 2293435 12404357 := bstep (se 4 (by rfl) ⟨1162908, by rfl⟩ : syracuseStep 12404357 = 2325817) B2325817
theorem B8269571 : Blo 2293435 8269571 := bstep (se 1 (by rfl) ⟨6202178, by rfl⟩ : syracuseStep 8269571 = 12404357) B12404357
theorem B22052189 : Blo 2293435 22052189 := bstep (se 3 (by rfl) ⟨4134785, by rfl⟩ : syracuseStep 22052189 = 8269571) B8269571
theorem B14701459 : Blo 2293435 14701459 := bstep (se 1 (by rfl) ⟨11026094, by rfl⟩ : syracuseStep 14701459 = 22052189) B22052189
theorem B19601945 : Blo 2293435 19601945 := bstep (se 2 (by rfl) ⟨7350729, by rfl⟩ : syracuseStep 19601945 = 14701459) B14701459
theorem B13067963 : Blo 2293435 13067963 := bstep (se 1 (by rfl) ⟨9800972, by rfl⟩ : syracuseStep 13067963 = 19601945) B19601945
theorem B8711975 : Blo 2293435 8711975 := bstep (se 1 (by rfl) ⟨6533981, by rfl⟩ : syracuseStep 8711975 = 13067963) B13067963
theorem B5807983 : Blo 2293435 5807983 := bstep (se 1 (by rfl) ⟨4355987, by rfl⟩ : syracuseStep 5807983 = 8711975) B8711975
theorem B7743977 : Blo 2293435 7743977 := bstep (se 2 (by rfl) ⟨2903991, by rfl⟩ : syracuseStep 7743977 = 5807983) B5807983
theorem B5162651 : Blo 2293435 5162651 := bstep (se 1 (by rfl) ⟨3871988, by rfl⟩ : syracuseStep 5162651 = 7743977) B7743977
theorem B3441767 : Blo 2293435 3441767 := bstep (se 1 (by rfl) ⟨2581325, by rfl⟩ : syracuseStep 3441767 = 5162651) B5162651
theorem B2294511 : Blo 2293435 2294511 := bstep (se 1 (by rfl) ⟨1720883, by rfl⟩ : syracuseStep 2294511 = 3441767) B3441767
theorem B3441773 : Blo 2293435 3441773 := bbase (se 3 (by rfl) ⟨645332, by rfl⟩ : syracuseStep 3441773 = 1290665) (by norm_num)
theorem B2294515 : Blo 2293435 2294515 := bstep (se 1 (by rfl) ⟨1720886, by rfl⟩ : syracuseStep 2294515 = 3441773) B3441773
theorem B5162669 : Blo 2293435 5162669 := bbase (se 3 (by rfl) ⟨968000, by rfl⟩ : syracuseStep 5162669 = 1936001) (by norm_num)
theorem B3441779 : Blo 2293435 3441779 := bstep (se 1 (by rfl) ⟨2581334, by rfl⟩ : syracuseStep 3441779 = 5162669) B5162669
theorem B2294519 : Blo 2293435 2294519 := bstep (se 1 (by rfl) ⟨1720889, by rfl⟩ : syracuseStep 2294519 = 3441779) B3441779
theorem B4651661 : Blo 2293435 4651661 := bbase (se 3 (by rfl) ⟨872186, by rfl⟩ : syracuseStep 4651661 = 1744373) (by norm_num)
theorem B3101107 : Blo 2293435 3101107 := bstep (se 1 (by rfl) ⟨2325830, by rfl⟩ : syracuseStep 3101107 = 4651661) B4651661
theorem B4134809 : Blo 2293435 4134809 := bstep (se 2 (by rfl) ⟨1550553, by rfl⟩ : syracuseStep 4134809 = 3101107) B3101107
theorem B2756539 : Blo 2293435 2756539 := bstep (se 1 (by rfl) ⟨2067404, by rfl⟩ : syracuseStep 2756539 = 4134809) B4134809
theorem B3675385 : Blo 2293435 3675385 := bstep (se 2 (by rfl) ⟨1378269, by rfl⟩ : syracuseStep 3675385 = 2756539) B2756539
theorem B4900513 : Blo 2293435 4900513 := bstep (se 2 (by rfl) ⟨1837692, by rfl⟩ : syracuseStep 4900513 = 3675385) B3675385
theorem B6534017 : Blo 2293435 6534017 := bstep (se 2 (by rfl) ⟨2450256, by rfl⟩ : syracuseStep 6534017 = 4900513) B4900513
theorem B4356011 : Blo 2293435 4356011 := bstep (se 1 (by rfl) ⟨3267008, by rfl⟩ : syracuseStep 4356011 = 6534017) B6534017
theorem B2904007 : Blo 2293435 2904007 := bstep (se 1 (by rfl) ⟨2178005, by rfl⟩ : syracuseStep 2904007 = 4356011) B4356011
theorem B3872009 : Blo 2293435 3872009 := bstep (se 2 (by rfl) ⟨1452003, by rfl⟩ : syracuseStep 3872009 = 2904007) B2904007
theorem B2581339 : Blo 2293435 2581339 := bstep (se 1 (by rfl) ⟨1936004, by rfl⟩ : syracuseStep 2581339 = 3872009) B3872009
theorem B3441785 : Blo 2293435 3441785 := bstep (se 2 (by rfl) ⟨1290669, by rfl⟩ : syracuseStep 3441785 = 2581339) B2581339
theorem B2294523 : Blo 2293435 2294523 := bstep (se 1 (by rfl) ⟨1720892, by rfl⟩ : syracuseStep 2294523 = 3441785) B3441785
theorem B22052341 : Blo 2293435 22052341 := bbase (se 5 (by rfl) ⟨1033703, by rfl⟩ : syracuseStep 22052341 = 2067407) (by norm_num)
theorem B29403121 : Blo 2293435 29403121 := bstep (se 2 (by rfl) ⟨11026170, by rfl⟩ : syracuseStep 29403121 = 22052341) B22052341
theorem B39204161 : Blo 2293435 39204161 := bstep (se 2 (by rfl) ⟨14701560, by rfl⟩ : syracuseStep 39204161 = 29403121) B29403121
theorem B26136107 : Blo 2293435 26136107 := bstep (se 1 (by rfl) ⟨19602080, by rfl⟩ : syracuseStep 26136107 = 39204161) B39204161
theorem B17424071 : Blo 2293435 17424071 := bstep (se 1 (by rfl) ⟨13068053, by rfl⟩ : syracuseStep 17424071 = 26136107) B26136107
theorem B11616047 : Blo 2293435 11616047 := bstep (se 1 (by rfl) ⟨8712035, by rfl⟩ : syracuseStep 11616047 = 17424071) B17424071
theorem B7744031 : Blo 2293435 7744031 := bstep (se 1 (by rfl) ⟨5808023, by rfl⟩ : syracuseStep 7744031 = 11616047) B11616047
theorem B5162687 : Blo 2293435 5162687 := bstep (se 1 (by rfl) ⟨3872015, by rfl⟩ : syracuseStep 5162687 = 7744031) B7744031
theorem B3441791 : Blo 2293435 3441791 := bstep (se 1 (by rfl) ⟨2581343, by rfl⟩ : syracuseStep 3441791 = 5162687) B5162687
theorem B2294527 : Blo 2293435 2294527 := bstep (se 1 (by rfl) ⟨1720895, by rfl⟩ : syracuseStep 2294527 = 3441791) B3441791
theorem B3441797 : Blo 2293435 3441797 := bbase (se 4 (by rfl) ⟨322668, by rfl⟩ : syracuseStep 3441797 = 645337) (by norm_num)
theorem B2294531 : Blo 2293435 2294531 := bstep (se 1 (by rfl) ⟨1720898, by rfl⟩ : syracuseStep 2294531 = 3441797) B3441797
theorem B3872029 : Blo 2293435 3872029 := bbase (se 3 (by rfl) ⟨726005, by rfl⟩ : syracuseStep 3872029 = 1452011) (by norm_num)
theorem B5162705 : Blo 2293435 5162705 := bstep (se 2 (by rfl) ⟨1936014, by rfl⟩ : syracuseStep 5162705 = 3872029) B3872029
theorem B3441803 : Blo 2293435 3441803 := bstep (se 1 (by rfl) ⟨2581352, by rfl⟩ : syracuseStep 3441803 = 5162705) B5162705
theorem B2294535 : Blo 2293435 2294535 := bstep (se 1 (by rfl) ⟨1720901, by rfl⟩ : syracuseStep 2294535 = 3441803) B3441803
theorem B2581357 : Blo 2293435 2581357 := bbase (se 3 (by rfl) ⟨484004, by rfl⟩ : syracuseStep 2581357 = 968009) (by norm_num)
theorem B3441809 : Blo 2293435 3441809 := bstep (se 2 (by rfl) ⟨1290678, by rfl⟩ : syracuseStep 3441809 = 2581357) B2581357
theorem B2294539 : Blo 2293435 2294539 := bstep (se 1 (by rfl) ⟨1720904, by rfl⟩ : syracuseStep 2294539 = 3441809) B3441809
theorem B7744085 : Blo 2293435 7744085 := bbase (se 8 (by rfl) ⟨45375, by rfl⟩ : syracuseStep 7744085 = 90751) (by norm_num)
theorem B5162723 : Blo 2293435 5162723 := bstep (se 1 (by rfl) ⟨3872042, by rfl⟩ : syracuseStep 5162723 = 7744085) B7744085
theorem B3441815 : Blo 2293435 3441815 := bstep (se 1 (by rfl) ⟨2581361, by rfl⟩ : syracuseStep 3441815 = 5162723) B5162723
theorem B2294543 : Blo 2293435 2294543 := bstep (se 1 (by rfl) ⟨1720907, by rfl⟩ : syracuseStep 2294543 = 3441815) B3441815
theorem B3441821 : Blo 2293435 3441821 := bbase (se 3 (by rfl) ⟨645341, by rfl⟩ : syracuseStep 3441821 = 1290683) (by norm_num)
theorem B2294547 : Blo 2293435 2294547 := bstep (se 1 (by rfl) ⟨1720910, by rfl⟩ : syracuseStep 2294547 = 3441821) B3441821
theorem B5162741 : Blo 2293435 5162741 := bbase (se 5 (by rfl) ⟨242003, by rfl⟩ : syracuseStep 5162741 = 484007) (by norm_num)
theorem B3441827 : Blo 2293435 3441827 := bstep (se 1 (by rfl) ⟨2581370, by rfl⟩ : syracuseStep 3441827 = 5162741) B5162741
theorem B2294551 : Blo 2293435 2294551 := bstep (se 1 (by rfl) ⟨1720913, by rfl⟩ : syracuseStep 2294551 = 3441827) B3441827
theorem B3101149 : Blo 2293435 3101149 := bbase (se 3 (by rfl) ⟨581465, by rfl⟩ : syracuseStep 3101149 = 1162931) (by norm_num)
theorem B16539461 : Blo 2293435 16539461 := bstep (se 4 (by rfl) ⟨1550574, by rfl⟩ : syracuseStep 16539461 = 3101149) B3101149
theorem B11026307 : Blo 2293435 11026307 := bstep (se 1 (by rfl) ⟨8269730, by rfl⟩ : syracuseStep 11026307 = 16539461) B16539461
theorem B29403485 : Blo 2293435 29403485 := bstep (se 3 (by rfl) ⟨5513153, by rfl⟩ : syracuseStep 29403485 = 11026307) B11026307
theorem B19602323 : Blo 2293435 19602323 := bstep (se 1 (by rfl) ⟨14701742, by rfl⟩ : syracuseStep 19602323 = 29403485) B29403485
theorem B13068215 : Blo 2293435 13068215 := bstep (se 1 (by rfl) ⟨9801161, by rfl⟩ : syracuseStep 13068215 = 19602323) B19602323
theorem B8712143 : Blo 2293435 8712143 := bstep (se 1 (by rfl) ⟨6534107, by rfl⟩ : syracuseStep 8712143 = 13068215) B13068215
theorem B5808095 : Blo 2293435 5808095 := bstep (se 1 (by rfl) ⟨4356071, by rfl⟩ : syracuseStep 5808095 = 8712143) B8712143
theorem B3872063 : Blo 2293435 3872063 := bstep (se 1 (by rfl) ⟨2904047, by rfl⟩ : syracuseStep 3872063 = 5808095) B5808095
theorem B2581375 : Blo 2293435 2581375 := bstep (se 1 (by rfl) ⟨1936031, by rfl⟩ : syracuseStep 2581375 = 3872063) B3872063
theorem B3441833 : Blo 2293435 3441833 := bstep (se 2 (by rfl) ⟨1290687, by rfl⟩ : syracuseStep 3441833 = 2581375) B2581375
theorem B2294555 : Blo 2293435 2294555 := bstep (se 1 (by rfl) ⟨1720916, by rfl⟩ : syracuseStep 2294555 = 3441833) B3441833
theorem B4900589 : Blo 2293435 4900589 := bbase (se 3 (by rfl) ⟨918860, by rfl⟩ : syracuseStep 4900589 = 1837721) (by norm_num)
theorem B3267059 : Blo 2293435 3267059 := bstep (se 1 (by rfl) ⟨2450294, by rfl⟩ : syracuseStep 3267059 = 4900589) B4900589
theorem B8712157 : Blo 2293435 8712157 := bstep (se 3 (by rfl) ⟨1633529, by rfl⟩ : syracuseStep 8712157 = 3267059) B3267059
theorem B11616209 : Blo 2293435 11616209 := bstep (se 2 (by rfl) ⟨4356078, by rfl⟩ : syracuseStep 11616209 = 8712157) B8712157
theorem B7744139 : Blo 2293435 7744139 := bstep (se 1 (by rfl) ⟨5808104, by rfl⟩ : syracuseStep 7744139 = 11616209) B11616209
theorem B5162759 : Blo 2293435 5162759 := bstep (se 1 (by rfl) ⟨3872069, by rfl⟩ : syracuseStep 5162759 = 7744139) B7744139
theorem B3441839 : Blo 2293435 3441839 := bstep (se 1 (by rfl) ⟨2581379, by rfl⟩ : syracuseStep 3441839 = 5162759) B5162759
theorem B2294559 : Blo 2293435 2294559 := bstep (se 1 (by rfl) ⟨1720919, by rfl⟩ : syracuseStep 2294559 = 3441839) B3441839
theorem B3441845 : Blo 2293435 3441845 := bbase (se 5 (by rfl) ⟨161336, by rfl⟩ : syracuseStep 3441845 = 322673) (by norm_num)
theorem B2294563 : Blo 2293435 2294563 := bstep (se 1 (by rfl) ⟨1720922, by rfl⟩ : syracuseStep 2294563 = 3441845) B3441845
theorem B5808125 : Blo 2293435 5808125 := bbase (se 3 (by rfl) ⟨1089023, by rfl⟩ : syracuseStep 5808125 = 2178047) (by norm_num)
theorem B3872083 : Blo 2293435 3872083 := bstep (se 1 (by rfl) ⟨2904062, by rfl⟩ : syracuseStep 3872083 = 5808125) B5808125
theorem B5162777 : Blo 2293435 5162777 := bstep (se 2 (by rfl) ⟨1936041, by rfl⟩ : syracuseStep 5162777 = 3872083) B3872083
theorem B3441851 : Blo 2293435 3441851 := bstep (se 1 (by rfl) ⟨2581388, by rfl⟩ : syracuseStep 3441851 = 5162777) B5162777
theorem B2294567 : Blo 2293435 2294567 := bstep (se 1 (by rfl) ⟨1720925, by rfl⟩ : syracuseStep 2294567 = 3441851) B3441851
theorem B2581393 : Blo 2293435 2581393 := bbase (se 2 (by rfl) ⟨968022, by rfl⟩ : syracuseStep 2581393 = 1936045) (by norm_num)
theorem B3441857 : Blo 2293435 3441857 := bstep (se 2 (by rfl) ⟨1290696, by rfl⟩ : syracuseStep 3441857 = 2581393) B2581393
theorem B2294571 : Blo 2293435 2294571 := bstep (se 1 (by rfl) ⟨1720928, by rfl⟩ : syracuseStep 2294571 = 3441857) B3441857
theorem B4356109 : Blo 2293435 4356109 := bbase (se 3 (by rfl) ⟨816770, by rfl⟩ : syracuseStep 4356109 = 1633541) (by norm_num)
theorem B5808145 : Blo 2293435 5808145 := bstep (se 2 (by rfl) ⟨2178054, by rfl⟩ : syracuseStep 5808145 = 4356109) B4356109
theorem B7744193 : Blo 2293435 7744193 := bstep (se 2 (by rfl) ⟨2904072, by rfl⟩ : syracuseStep 7744193 = 5808145) B5808145
theorem B5162795 : Blo 2293435 5162795 := bstep (se 1 (by rfl) ⟨3872096, by rfl⟩ : syracuseStep 5162795 = 7744193) B7744193
theorem B3441863 : Blo 2293435 3441863 := bstep (se 1 (by rfl) ⟨2581397, by rfl⟩ : syracuseStep 3441863 = 5162795) B5162795
theorem B2294575 : Blo 2293435 2294575 := bstep (se 1 (by rfl) ⟨1720931, by rfl⟩ : syracuseStep 2294575 = 3441863) B3441863
theorem B3441869 : Blo 2293435 3441869 := bbase (se 3 (by rfl) ⟨645350, by rfl⟩ : syracuseStep 3441869 = 1290701) (by norm_num)
theorem B2294579 : Blo 2293435 2294579 := bstep (se 1 (by rfl) ⟨1720934, by rfl⟩ : syracuseStep 2294579 = 3441869) B3441869
theorem B5162813 : Blo 2293435 5162813 := bbase (se 3 (by rfl) ⟨968027, by rfl⟩ : syracuseStep 5162813 = 1936055) (by norm_num)
theorem B3441875 : Blo 2293435 3441875 := bstep (se 1 (by rfl) ⟨2581406, by rfl⟩ : syracuseStep 3441875 = 5162813) B5162813
theorem B2294583 : Blo 2293435 2294583 := bstep (se 1 (by rfl) ⟨1720937, by rfl⟩ : syracuseStep 2294583 = 3441875) B3441875
theorem B3872117 : Blo 2293435 3872117 := bbase (se 5 (by rfl) ⟨181505, by rfl⟩ : syracuseStep 3872117 = 363011) (by norm_num)
theorem B2581411 : Blo 2293435 2581411 := bstep (se 1 (by rfl) ⟨1936058, by rfl⟩ : syracuseStep 2581411 = 3872117) B3872117
theorem B3441881 : Blo 2293435 3441881 := bstep (se 2 (by rfl) ⟨1290705, by rfl⟩ : syracuseStep 3441881 = 2581411) B2581411
theorem B2294587 : Blo 2293435 2294587 := bstep (se 1 (by rfl) ⟨1720940, by rfl⟩ : syracuseStep 2294587 = 3441881) B3441881
theorem B3675493 : Blo 2293435 3675493 := bbase (se 4 (by rfl) ⟨344577, by rfl⟩ : syracuseStep 3675493 = 689155) (by norm_num)
theorem B4900657 : Blo 2293435 4900657 := bstep (se 2 (by rfl) ⟨1837746, by rfl⟩ : syracuseStep 4900657 = 3675493) B3675493
theorem B6534209 : Blo 2293435 6534209 := bstep (se 2 (by rfl) ⟨2450328, by rfl⟩ : syracuseStep 6534209 = 4900657) B4900657
theorem B17424557 : Blo 2293435 17424557 := bstep (se 3 (by rfl) ⟨3267104, by rfl⟩ : syracuseStep 17424557 = 6534209) B6534209
theorem B11616371 : Blo 2293435 11616371 := bstep (se 1 (by rfl) ⟨8712278, by rfl⟩ : syracuseStep 11616371 = 17424557) B17424557
theorem B7744247 : Blo 2293435 7744247 := bstep (se 1 (by rfl) ⟨5808185, by rfl⟩ : syracuseStep 7744247 = 11616371) B11616371
theorem B5162831 : Blo 2293435 5162831 := bstep (se 1 (by rfl) ⟨3872123, by rfl⟩ : syracuseStep 5162831 = 7744247) B7744247
theorem B3441887 : Blo 2293435 3441887 := bstep (se 1 (by rfl) ⟨2581415, by rfl⟩ : syracuseStep 3441887 = 5162831) B5162831
theorem B2294591 : Blo 2293435 2294591 := bstep (se 1 (by rfl) ⟨1720943, by rfl⟩ : syracuseStep 2294591 = 3441887) B3441887
theorem B3441893 : Blo 2293435 3441893 := bbase (se 4 (by rfl) ⟨322677, by rfl⟩ : syracuseStep 3441893 = 645355) (by norm_num)
theorem B2294595 : Blo 2293435 2294595 := bstep (se 1 (by rfl) ⟨1720946, by rfl⟩ : syracuseStep 2294595 = 3441893) B3441893
theorem B7351013 : Blo 2293435 7351013 := bbase (se 4 (by rfl) ⟨689157, by rfl⟩ : syracuseStep 7351013 = 1378315) (by norm_num)
theorem B4900675 : Blo 2293435 4900675 := bstep (se 1 (by rfl) ⟨3675506, by rfl⟩ : syracuseStep 4900675 = 7351013) B7351013
theorem B6534233 : Blo 2293435 6534233 := bstep (se 2 (by rfl) ⟨2450337, by rfl⟩ : syracuseStep 6534233 = 4900675) B4900675
theorem B4356155 : Blo 2293435 4356155 := bstep (se 1 (by rfl) ⟨3267116, by rfl⟩ : syracuseStep 4356155 = 6534233) B6534233
theorem B2904103 : Blo 2293435 2904103 := bstep (se 1 (by rfl) ⟨2178077, by rfl⟩ : syracuseStep 2904103 = 4356155) B4356155
theorem B3872137 : Blo 2293435 3872137 := bstep (se 2 (by rfl) ⟨1452051, by rfl⟩ : syracuseStep 3872137 = 2904103) B2904103
theorem B5162849 : Blo 2293435 5162849 := bstep (se 2 (by rfl) ⟨1936068, by rfl⟩ : syracuseStep 5162849 = 3872137) B3872137
theorem B3441899 : Blo 2293435 3441899 := bstep (se 1 (by rfl) ⟨2581424, by rfl⟩ : syracuseStep 3441899 = 5162849) B5162849
theorem B2294599 : Blo 2293435 2294599 := bstep (se 1 (by rfl) ⟨1720949, by rfl⟩ : syracuseStep 2294599 = 3441899) B3441899
theorem B2581429 : Blo 2293435 2581429 := bbase (se 5 (by rfl) ⟨121004, by rfl⟩ : syracuseStep 2581429 = 242009) (by norm_num)
theorem B3441905 : Blo 2293435 3441905 := bstep (se 2 (by rfl) ⟨1290714, by rfl⟩ : syracuseStep 3441905 = 2581429) B2581429
theorem B2294603 : Blo 2293435 2294603 := bstep (se 1 (by rfl) ⟨1720952, by rfl⟩ : syracuseStep 2294603 = 3441905) B3441905
theorem B2904113 : Blo 2293435 2904113 := bbase (se 2 (by rfl) ⟨1089042, by rfl⟩ : syracuseStep 2904113 = 2178085) (by norm_num)
theorem B7744301 : Blo 2293435 7744301 := bstep (se 3 (by rfl) ⟨1452056, by rfl⟩ : syracuseStep 7744301 = 2904113) B2904113
theorem B5162867 : Blo 2293435 5162867 := bstep (se 1 (by rfl) ⟨3872150, by rfl⟩ : syracuseStep 5162867 = 7744301) B7744301
theorem B3441911 : Blo 2293435 3441911 := bstep (se 1 (by rfl) ⟨2581433, by rfl⟩ : syracuseStep 3441911 = 5162867) B5162867
theorem B2294607 : Blo 2293435 2294607 := bstep (se 1 (by rfl) ⟨1720955, by rfl⟩ : syracuseStep 2294607 = 3441911) B3441911
theorem B3441917 : Blo 2293435 3441917 := bbase (se 3 (by rfl) ⟨645359, by rfl⟩ : syracuseStep 3441917 = 1290719) (by norm_num)
theorem B2294611 : Blo 2293435 2294611 := bstep (se 1 (by rfl) ⟨1720958, by rfl⟩ : syracuseStep 2294611 = 3441917) B3441917
theorem B5162885 : Blo 2293435 5162885 := bbase (se 4 (by rfl) ⟨484020, by rfl⟩ : syracuseStep 5162885 = 968041) (by norm_num)
theorem B3441923 : Blo 2293435 3441923 := bstep (se 1 (by rfl) ⟨2581442, by rfl⟩ : syracuseStep 3441923 = 5162885) B5162885
theorem B2294615 : Blo 2293435 2294615 := bstep (se 1 (by rfl) ⟨1720961, by rfl⟩ : syracuseStep 2294615 = 3441923) B3441923
theorem B5513309 : Blo 2293435 5513309 := bbase (se 3 (by rfl) ⟨1033745, by rfl⟩ : syracuseStep 5513309 = 2067491) (by norm_num)
theorem B3675539 : Blo 2293435 3675539 := bstep (se 1 (by rfl) ⟨2756654, by rfl⟩ : syracuseStep 3675539 = 5513309) B5513309
theorem B2450359 : Blo 2293435 2450359 := bstep (se 1 (by rfl) ⟨1837769, by rfl⟩ : syracuseStep 2450359 = 3675539) B3675539
theorem B3267145 : Blo 2293435 3267145 := bstep (se 2 (by rfl) ⟨1225179, by rfl⟩ : syracuseStep 3267145 = 2450359) B2450359
theorem B4356193 : Blo 2293435 4356193 := bstep (se 2 (by rfl) ⟨1633572, by rfl⟩ : syracuseStep 4356193 = 3267145) B3267145
theorem B5808257 : Blo 2293435 5808257 := bstep (se 2 (by rfl) ⟨2178096, by rfl⟩ : syracuseStep 5808257 = 4356193) B4356193
theorem B3872171 : Blo 2293435 3872171 := bstep (se 1 (by rfl) ⟨2904128, by rfl⟩ : syracuseStep 3872171 = 5808257) B5808257
theorem B2581447 : Blo 2293435 2581447 := bstep (se 1 (by rfl) ⟨1936085, by rfl⟩ : syracuseStep 2581447 = 3872171) B3872171
theorem B3441929 : Blo 2293435 3441929 := bstep (se 2 (by rfl) ⟨1290723, by rfl⟩ : syracuseStep 3441929 = 2581447) B2581447
theorem B2294619 : Blo 2293435 2294619 := bstep (se 1 (by rfl) ⟨1720964, by rfl⟩ : syracuseStep 2294619 = 3441929) B3441929
theorem B11616533 : Blo 2293435 11616533 := bbase (se 6 (by rfl) ⟨272262, by rfl⟩ : syracuseStep 11616533 = 544525) (by norm_num)
theorem B7744355 : Blo 2293435 7744355 := bstep (se 1 (by rfl) ⟨5808266, by rfl⟩ : syracuseStep 7744355 = 11616533) B11616533
theorem B5162903 : Blo 2293435 5162903 := bstep (se 1 (by rfl) ⟨3872177, by rfl⟩ : syracuseStep 5162903 = 7744355) B7744355
theorem B3441935 : Blo 2293435 3441935 := bstep (se 1 (by rfl) ⟨2581451, by rfl⟩ : syracuseStep 3441935 = 5162903) B5162903
theorem B2294623 : Blo 2293435 2294623 := bstep (se 1 (by rfl) ⟨1720967, by rfl⟩ : syracuseStep 2294623 = 3441935) B3441935
theorem B3441941 : Blo 2293435 3441941 := bbase (se 6 (by rfl) ⟨80670, by rfl⟩ : syracuseStep 3441941 = 161341) (by norm_num)
theorem B2294627 : Blo 2293435 2294627 := bstep (se 1 (by rfl) ⟨1720970, by rfl⟩ : syracuseStep 2294627 = 3441941) B3441941
theorem B10609525 : Blo 2293435 10609525 := bbase (se 5 (by rfl) ⟨497321, by rfl⟩ : syracuseStep 10609525 = 994643) (by norm_num)
theorem B56584133 : Blo 2293435 56584133 := bstep (se 4 (by rfl) ⟨5304762, by rfl⟩ : syracuseStep 56584133 = 10609525) B10609525
theorem B37722755 : Blo 2293435 37722755 := bstep (se 1 (by rfl) ⟨28292066, by rfl⟩ : syracuseStep 37722755 = 56584133) B56584133
theorem B25148503 : Blo 2293435 25148503 := bstep (se 1 (by rfl) ⟨18861377, by rfl⟩ : syracuseStep 25148503 = 37722755) B37722755
theorem B33531337 : Blo 2293435 33531337 := bstep (se 2 (by rfl) ⟨12574251, by rfl⟩ : syracuseStep 33531337 = 25148503) B25148503
theorem B44708449 : Blo 2293435 44708449 := bstep (se 2 (by rfl) ⟨16765668, by rfl⟩ : syracuseStep 44708449 = 33531337) B33531337
theorem B59611265 : Blo 2293435 59611265 := bstep (se 2 (by rfl) ⟨22354224, by rfl⟩ : syracuseStep 59611265 = 44708449) B44708449
theorem B39740843 : Blo 2293435 39740843 := bstep (se 1 (by rfl) ⟨29805632, by rfl⟩ : syracuseStep 39740843 = 59611265) B59611265
theorem B26493895 : Blo 2293435 26493895 := bstep (se 1 (by rfl) ⟨19870421, by rfl⟩ : syracuseStep 26493895 = 39740843) B39740843
theorem B141300773 : Blo 2293435 141300773 := bstep (se 4 (by rfl) ⟨13246947, by rfl⟩ : syracuseStep 141300773 = 26493895) B26493895
theorem B94200515 : Blo 2293435 94200515 := bstep (se 1 (by rfl) ⟨70650386, by rfl⟩ : syracuseStep 94200515 = 141300773) B141300773
theorem B62800343 : Blo 2293435 62800343 := bstep (se 1 (by rfl) ⟨47100257, by rfl⟩ : syracuseStep 62800343 = 94200515) B94200515
theorem B41866895 : Blo 2293435 41866895 := bstep (se 1 (by rfl) ⟨31400171, by rfl⟩ : syracuseStep 41866895 = 62800343) B62800343
theorem B111645053 : Blo 2293435 111645053 := bstep (se 3 (by rfl) ⟨20933447, by rfl⟩ : syracuseStep 111645053 = 41866895) B41866895
theorem B74430035 : Blo 2293435 74430035 := bstep (se 1 (by rfl) ⟨55822526, by rfl⟩ : syracuseStep 74430035 = 111645053) B111645053
theorem B49620023 : Blo 2293435 49620023 := bstep (se 1 (by rfl) ⟨37215017, by rfl⟩ : syracuseStep 49620023 = 74430035) B74430035
theorem B33080015 : Blo 2293435 33080015 := bstep (se 1 (by rfl) ⟨24810011, by rfl⟩ : syracuseStep 33080015 = 49620023) B49620023
theorem B22053343 : Blo 2293435 22053343 := bstep (se 1 (by rfl) ⟨16540007, by rfl⟩ : syracuseStep 22053343 = 33080015) B33080015
theorem B29404457 : Blo 2293435 29404457 := bstep (se 2 (by rfl) ⟨11026671, by rfl⟩ : syracuseStep 29404457 = 22053343) B22053343
theorem B19602971 : Blo 2293435 19602971 := bstep (se 1 (by rfl) ⟨14702228, by rfl⟩ : syracuseStep 19602971 = 29404457) B29404457
theorem B13068647 : Blo 2293435 13068647 := bstep (se 1 (by rfl) ⟨9801485, by rfl⟩ : syracuseStep 13068647 = 19602971) B19602971
theorem B8712431 : Blo 2293435 8712431 := bstep (se 1 (by rfl) ⟨6534323, by rfl⟩ : syracuseStep 8712431 = 13068647) B13068647
theorem B5808287 : Blo 2293435 5808287 := bstep (se 1 (by rfl) ⟨4356215, by rfl⟩ : syracuseStep 5808287 = 8712431) B8712431
theorem B3872191 : Blo 2293435 3872191 := bstep (se 1 (by rfl) ⟨2904143, by rfl⟩ : syracuseStep 3872191 = 5808287) B5808287
theorem B5162921 : Blo 2293435 5162921 := bstep (se 2 (by rfl) ⟨1936095, by rfl⟩ : syracuseStep 5162921 = 3872191) B3872191
theorem B3441947 : Blo 2293435 3441947 := bstep (se 1 (by rfl) ⟨2581460, by rfl⟩ : syracuseStep 3441947 = 5162921) B5162921
theorem B2294631 : Blo 2293435 2294631 := bstep (se 1 (by rfl) ⟨1720973, by rfl⟩ : syracuseStep 2294631 = 3441947) B3441947
theorem B2581465 : Blo 2293435 2581465 := bbase (se 2 (by rfl) ⟨968049, by rfl⟩ : syracuseStep 2581465 = 1936099) (by norm_num)
theorem B3441953 : Blo 2293435 3441953 := bstep (se 2 (by rfl) ⟨1290732, by rfl⟩ : syracuseStep 3441953 = 2581465) B2581465
theorem B2294635 : Blo 2293435 2294635 := bstep (se 1 (by rfl) ⟨1720976, by rfl⟩ : syracuseStep 2294635 = 3441953) B3441953
theorem B3267173 : Blo 2293435 3267173 := bbase (se 4 (by rfl) ⟨306297, by rfl⟩ : syracuseStep 3267173 = 612595) (by norm_num)
theorem B8712461 : Blo 2293435 8712461 := bstep (se 3 (by rfl) ⟨1633586, by rfl⟩ : syracuseStep 8712461 = 3267173) B3267173
theorem B5808307 : Blo 2293435 5808307 := bstep (se 1 (by rfl) ⟨4356230, by rfl⟩ : syracuseStep 5808307 = 8712461) B8712461
theorem B7744409 : Blo 2293435 7744409 := bstep (se 2 (by rfl) ⟨2904153, by rfl⟩ : syracuseStep 7744409 = 5808307) B5808307
theorem B5162939 : Blo 2293435 5162939 := bstep (se 1 (by rfl) ⟨3872204, by rfl⟩ : syracuseStep 5162939 = 7744409) B7744409
theorem B3441959 : Blo 2293435 3441959 := bstep (se 1 (by rfl) ⟨2581469, by rfl⟩ : syracuseStep 3441959 = 5162939) B5162939
theorem B2294639 : Blo 2293435 2294639 := bstep (se 1 (by rfl) ⟨1720979, by rfl⟩ : syracuseStep 2294639 = 3441959) B3441959
theorem B3441965 : Blo 2293435 3441965 := bbase (se 3 (by rfl) ⟨645368, by rfl⟩ : syracuseStep 3441965 = 1290737) (by norm_num)
theorem B2294643 : Blo 2293435 2294643 := bstep (se 1 (by rfl) ⟨1720982, by rfl⟩ : syracuseStep 2294643 = 3441965) B3441965
theorem B5162957 : Blo 2293435 5162957 := bbase (se 3 (by rfl) ⟨968054, by rfl⟩ : syracuseStep 5162957 = 1936109) (by norm_num)
theorem B3441971 : Blo 2293435 3441971 := bstep (se 1 (by rfl) ⟨2581478, by rfl⟩ : syracuseStep 3441971 = 5162957) B5162957
theorem B2294647 : Blo 2293435 2294647 := bstep (se 1 (by rfl) ⟨1720985, by rfl⟩ : syracuseStep 2294647 = 3441971) B3441971
theorem B2904169 : Blo 2293435 2904169 := bbase (se 2 (by rfl) ⟨1089063, by rfl⟩ : syracuseStep 2904169 = 2178127) (by norm_num)
theorem B3872225 : Blo 2293435 3872225 := bstep (se 2 (by rfl) ⟨1452084, by rfl⟩ : syracuseStep 3872225 = 2904169) B2904169
theorem B2581483 : Blo 2293435 2581483 := bstep (se 1 (by rfl) ⟨1936112, by rfl⟩ : syracuseStep 2581483 = 3872225) B3872225
theorem B3441977 : Blo 2293435 3441977 := bstep (se 2 (by rfl) ⟨1290741, by rfl⟩ : syracuseStep 3441977 = 2581483) B2581483
theorem B2294651 : Blo 2293435 2294651 := bstep (se 1 (by rfl) ⟨1720988, by rfl⟩ : syracuseStep 2294651 = 3441977) B3441977
theorem B4135045 : Blo 2293435 4135045 := bbase (se 4 (by rfl) ⟨387660, by rfl⟩ : syracuseStep 4135045 = 775321) (by norm_num)
theorem B5513393 : Blo 2293435 5513393 := bstep (se 2 (by rfl) ⟨2067522, by rfl⟩ : syracuseStep 5513393 = 4135045) B4135045
theorem B14702381 : Blo 2293435 14702381 := bstep (se 3 (by rfl) ⟨2756696, by rfl⟩ : syracuseStep 14702381 = 5513393) B5513393
theorem B9801587 : Blo 2293435 9801587 := bstep (se 1 (by rfl) ⟨7351190, by rfl⟩ : syracuseStep 9801587 = 14702381) B14702381
theorem B26137565 : Blo 2293435 26137565 := bstep (se 3 (by rfl) ⟨4900793, by rfl⟩ : syracuseStep 26137565 = 9801587) B9801587
theorem B17425043 : Blo 2293435 17425043 := bstep (se 1 (by rfl) ⟨13068782, by rfl⟩ : syracuseStep 17425043 = 26137565) B26137565
theorem B11616695 : Blo 2293435 11616695 := bstep (se 1 (by rfl) ⟨8712521, by rfl⟩ : syracuseStep 11616695 = 17425043) B17425043
theorem B7744463 : Blo 2293435 7744463 := bstep (se 1 (by rfl) ⟨5808347, by rfl⟩ : syracuseStep 7744463 = 11616695) B11616695
theorem B5162975 : Blo 2293435 5162975 := bstep (se 1 (by rfl) ⟨3872231, by rfl⟩ : syracuseStep 5162975 = 7744463) B7744463
theorem B3441983 : Blo 2293435 3441983 := bstep (se 1 (by rfl) ⟨2581487, by rfl⟩ : syracuseStep 3441983 = 5162975) B5162975
theorem B2294655 : Blo 2293435 2294655 := bstep (se 1 (by rfl) ⟨1720991, by rfl⟩ : syracuseStep 2294655 = 3441983) B3441983
theorem B3441989 : Blo 2293435 3441989 := bbase (se 4 (by rfl) ⟨322686, by rfl⟩ : syracuseStep 3441989 = 645373) (by norm_num)
theorem B2294659 : Blo 2293435 2294659 := bstep (se 1 (by rfl) ⟨1720994, by rfl⟩ : syracuseStep 2294659 = 3441989) B3441989
theorem B3872245 : Blo 2293435 3872245 := bbase (se 5 (by rfl) ⟨181511, by rfl⟩ : syracuseStep 3872245 = 363023) (by norm_num)
theorem B5162993 : Blo 2293435 5162993 := bstep (se 2 (by rfl) ⟨1936122, by rfl⟩ : syracuseStep 5162993 = 3872245) B3872245
theorem B3441995 : Blo 2293435 3441995 := bstep (se 1 (by rfl) ⟨2581496, by rfl⟩ : syracuseStep 3441995 = 5162993) B5162993
theorem B2294663 : Blo 2293435 2294663 := bstep (se 1 (by rfl) ⟨1720997, by rfl⟩ : syracuseStep 2294663 = 3441995) B3441995
theorem B2581501 : Blo 2293435 2581501 := bbase (se 3 (by rfl) ⟨484031, by rfl⟩ : syracuseStep 2581501 = 968063) (by norm_num)
theorem B3442001 : Blo 2293435 3442001 := bstep (se 2 (by rfl) ⟨1290750, by rfl⟩ : syracuseStep 3442001 = 2581501) B2581501
theorem B2294667 : Blo 2293435 2294667 := bstep (se 1 (by rfl) ⟨1721000, by rfl⟩ : syracuseStep 2294667 = 3442001) B3442001
theorem B7744517 : Blo 2293435 7744517 := bbase (se 4 (by rfl) ⟨726048, by rfl⟩ : syracuseStep 7744517 = 1452097) (by norm_num)
theorem B5163011 : Blo 2293435 5163011 := bstep (se 1 (by rfl) ⟨3872258, by rfl⟩ : syracuseStep 5163011 = 7744517) B7744517
theorem B3442007 : Blo 2293435 3442007 := bstep (se 1 (by rfl) ⟨2581505, by rfl⟩ : syracuseStep 3442007 = 5163011) B5163011
theorem B2294671 : Blo 2293435 2294671 := bstep (se 1 (by rfl) ⟨1721003, by rfl⟩ : syracuseStep 2294671 = 3442007) B3442007
theorem B3442013 : Blo 2293435 3442013 := bbase (se 3 (by rfl) ⟨645377, by rfl⟩ : syracuseStep 3442013 = 1290755) (by norm_num)
theorem B2294675 : Blo 2293435 2294675 := bstep (se 1 (by rfl) ⟨1721006, by rfl⟩ : syracuseStep 2294675 = 3442013) B3442013
theorem B5163029 : Blo 2293435 5163029 := bbase (se 6 (by rfl) ⟨121008, by rfl⟩ : syracuseStep 5163029 = 242017) (by norm_num)
theorem B3442019 : Blo 2293435 3442019 := bstep (se 1 (by rfl) ⟨2581514, by rfl⟩ : syracuseStep 3442019 = 5163029) B5163029
theorem B2294679 : Blo 2293435 2294679 := bstep (se 1 (by rfl) ⟨1721009, by rfl⟩ : syracuseStep 2294679 = 3442019) B3442019
theorem B8712629 : Blo 2293435 8712629 := bbase (se 5 (by rfl) ⟨408404, by rfl⟩ : syracuseStep 8712629 = 816809) (by norm_num)
theorem B5808419 : Blo 2293435 5808419 := bstep (se 1 (by rfl) ⟨4356314, by rfl⟩ : syracuseStep 5808419 = 8712629) B8712629
theorem B3872279 : Blo 2293435 3872279 := bstep (se 1 (by rfl) ⟨2904209, by rfl⟩ : syracuseStep 3872279 = 5808419) B5808419
theorem B2581519 : Blo 2293435 2581519 := bstep (se 1 (by rfl) ⟨1936139, by rfl⟩ : syracuseStep 2581519 = 3872279) B3872279
theorem B3442025 : Blo 2293435 3442025 := bstep (se 2 (by rfl) ⟨1290759, by rfl⟩ : syracuseStep 3442025 = 2581519) B2581519
theorem B2294683 : Blo 2293435 2294683 := bstep (se 1 (by rfl) ⟨1721012, by rfl⟩ : syracuseStep 2294683 = 3442025) B3442025
theorem B94202837 : Blo 2293435 94202837 := bbase (se 7 (by rfl) ⟨1103939, by rfl⟩ : syracuseStep 94202837 = 2207879) (by norm_num)
theorem B62801891 : Blo 2293435 62801891 := bstep (se 1 (by rfl) ⟨47101418, by rfl⟩ : syracuseStep 62801891 = 94202837) B94202837
theorem B41867927 : Blo 2293435 41867927 := bstep (se 1 (by rfl) ⟨31400945, by rfl⟩ : syracuseStep 41867927 = 62801891) B62801891
theorem B27911951 : Blo 2293435 27911951 := bstep (se 1 (by rfl) ⟨20933963, by rfl⟩ : syracuseStep 27911951 = 41867927) B41867927
theorem B18607967 : Blo 2293435 18607967 := bstep (se 1 (by rfl) ⟨13955975, by rfl⟩ : syracuseStep 18607967 = 27911951) B27911951
theorem B12405311 : Blo 2293435 12405311 := bstep (se 1 (by rfl) ⟨9303983, by rfl⟩ : syracuseStep 12405311 = 18607967) B18607967
theorem B8270207 : Blo 2293435 8270207 := bstep (se 1 (by rfl) ⟨6202655, by rfl⟩ : syracuseStep 8270207 = 12405311) B12405311
theorem B5513471 : Blo 2293435 5513471 := bstep (se 1 (by rfl) ⟨4135103, by rfl⟩ : syracuseStep 5513471 = 8270207) B8270207
theorem B3675647 : Blo 2293435 3675647 := bstep (se 1 (by rfl) ⟨2756735, by rfl⟩ : syracuseStep 3675647 = 5513471) B5513471
theorem B2450431 : Blo 2293435 2450431 := bstep (se 1 (by rfl) ⟨1837823, by rfl⟩ : syracuseStep 2450431 = 3675647) B3675647
theorem B13068965 : Blo 2293435 13068965 := bstep (se 4 (by rfl) ⟨1225215, by rfl⟩ : syracuseStep 13068965 = 2450431) B2450431
theorem B8712643 : Blo 2293435 8712643 := bstep (se 1 (by rfl) ⟨6534482, by rfl⟩ : syracuseStep 8712643 = 13068965) B13068965
theorem B11616857 : Blo 2293435 11616857 := bstep (se 2 (by rfl) ⟨4356321, by rfl⟩ : syracuseStep 11616857 = 8712643) B8712643
theorem B7744571 : Blo 2293435 7744571 := bstep (se 1 (by rfl) ⟨5808428, by rfl⟩ : syracuseStep 7744571 = 11616857) B11616857
theorem B5163047 : Blo 2293435 5163047 := bstep (se 1 (by rfl) ⟨3872285, by rfl⟩ : syracuseStep 5163047 = 7744571) B7744571
theorem B3442031 : Blo 2293435 3442031 := bstep (se 1 (by rfl) ⟨2581523, by rfl⟩ : syracuseStep 3442031 = 5163047) B5163047
theorem B2294687 : Blo 2293435 2294687 := bstep (se 1 (by rfl) ⟨1721015, by rfl⟩ : syracuseStep 2294687 = 3442031) B3442031
theorem B3442037 : Blo 2293435 3442037 := bbase (se 5 (by rfl) ⟨161345, by rfl⟩ : syracuseStep 3442037 = 322691) (by norm_num)
theorem B2294691 : Blo 2293435 2294691 := bstep (se 1 (by rfl) ⟨1721018, by rfl⟩ : syracuseStep 2294691 = 3442037) B3442037
theorem B3267253 : Blo 2293435 3267253 := bbase (se 5 (by rfl) ⟨153152, by rfl⟩ : syracuseStep 3267253 = 306305) (by norm_num)
theorem B4356337 : Blo 2293435 4356337 := bstep (se 2 (by rfl) ⟨1633626, by rfl⟩ : syracuseStep 4356337 = 3267253) B3267253
theorem B5808449 : Blo 2293435 5808449 := bstep (se 2 (by rfl) ⟨2178168, by rfl⟩ : syracuseStep 5808449 = 4356337) B4356337
theorem B3872299 : Blo 2293435 3872299 := bstep (se 1 (by rfl) ⟨2904224, by rfl⟩ : syracuseStep 3872299 = 5808449) B5808449
theorem B5163065 : Blo 2293435 5163065 := bstep (se 2 (by rfl) ⟨1936149, by rfl⟩ : syracuseStep 5163065 = 3872299) B3872299
theorem B3442043 : Blo 2293435 3442043 := bstep (se 1 (by rfl) ⟨2581532, by rfl⟩ : syracuseStep 3442043 = 5163065) B5163065
theorem B2294695 : Blo 2293435 2294695 := bstep (se 1 (by rfl) ⟨1721021, by rfl⟩ : syracuseStep 2294695 = 3442043) B3442043
theorem B2581537 : Blo 2293435 2581537 := bbase (se 2 (by rfl) ⟨968076, by rfl⟩ : syracuseStep 2581537 = 1936153) (by norm_num)
theorem B3442049 : Blo 2293435 3442049 := bstep (se 2 (by rfl) ⟨1290768, by rfl⟩ : syracuseStep 3442049 = 2581537) B2581537
theorem B2294699 : Blo 2293435 2294699 := bstep (se 1 (by rfl) ⟨1721024, by rfl⟩ : syracuseStep 2294699 = 3442049) B3442049
theorem B5808469 : Blo 2293435 5808469 := bbase (se 10 (by rfl) ⟨8508, by rfl⟩ : syracuseStep 5808469 = 17017) (by norm_num)
theorem B7744625 : Blo 2293435 7744625 := bstep (se 2 (by rfl) ⟨2904234, by rfl⟩ : syracuseStep 7744625 = 5808469) B5808469
theorem B5163083 : Blo 2293435 5163083 := bstep (se 1 (by rfl) ⟨3872312, by rfl⟩ : syracuseStep 5163083 = 7744625) B7744625
theorem B3442055 : Blo 2293435 3442055 := bstep (se 1 (by rfl) ⟨2581541, by rfl⟩ : syracuseStep 3442055 = 5163083) B5163083
theorem B2294703 : Blo 2293435 2294703 := bstep (se 1 (by rfl) ⟨1721027, by rfl⟩ : syracuseStep 2294703 = 3442055) B3442055
theorem B3442061 : Blo 2293435 3442061 := bbase (se 3 (by rfl) ⟨645386, by rfl⟩ : syracuseStep 3442061 = 1290773) (by norm_num)
theorem B2294707 : Blo 2293435 2294707 := bstep (se 1 (by rfl) ⟨1721030, by rfl⟩ : syracuseStep 2294707 = 3442061) B3442061
theorem B5163101 : Blo 2293435 5163101 := bbase (se 3 (by rfl) ⟨968081, by rfl⟩ : syracuseStep 5163101 = 1936163) (by norm_num)
theorem B3442067 : Blo 2293435 3442067 := bstep (se 1 (by rfl) ⟨2581550, by rfl⟩ : syracuseStep 3442067 = 5163101) B5163101
theorem B2294711 : Blo 2293435 2294711 := bstep (se 1 (by rfl) ⟨1721033, by rfl⟩ : syracuseStep 2294711 = 3442067) B3442067
theorem B3872333 : Blo 2293435 3872333 := bbase (se 3 (by rfl) ⟨726062, by rfl⟩ : syracuseStep 3872333 = 1452125) (by norm_num)
theorem B2581555 : Blo 2293435 2581555 := bstep (se 1 (by rfl) ⟨1936166, by rfl⟩ : syracuseStep 2581555 = 3872333) B3872333
theorem B3442073 : Blo 2293435 3442073 := bstep (se 2 (by rfl) ⟨1290777, by rfl⟩ : syracuseStep 3442073 = 2581555) B2581555
theorem B2294715 : Blo 2293435 2294715 := bstep (se 1 (by rfl) ⟨1721036, by rfl⟩ : syracuseStep 2294715 = 3442073) B3442073
theorem B10467125 : Blo 2293435 10467125 := bbase (se 5 (by rfl) ⟨490646, by rfl⟩ : syracuseStep 10467125 = 981293) (by norm_num)
theorem B6978083 : Blo 2293435 6978083 := bstep (se 1 (by rfl) ⟨5233562, by rfl⟩ : syracuseStep 6978083 = 10467125) B10467125
theorem B18608221 : Blo 2293435 18608221 := bstep (se 3 (by rfl) ⟨3489041, by rfl⟩ : syracuseStep 18608221 = 6978083) B6978083
theorem B24810961 : Blo 2293435 24810961 := bstep (se 2 (by rfl) ⟨9304110, by rfl⟩ : syracuseStep 24810961 = 18608221) B18608221
theorem B33081281 : Blo 2293435 33081281 := bstep (se 2 (by rfl) ⟨12405480, by rfl⟩ : syracuseStep 33081281 = 24810961) B24810961
theorem B22054187 : Blo 2293435 22054187 := bstep (se 1 (by rfl) ⟨16540640, by rfl⟩ : syracuseStep 22054187 = 33081281) B33081281
theorem B14702791 : Blo 2293435 14702791 := bstep (se 1 (by rfl) ⟨11027093, by rfl⟩ : syracuseStep 14702791 = 22054187) B22054187
theorem B19603721 : Blo 2293435 19603721 := bstep (se 2 (by rfl) ⟨7351395, by rfl⟩ : syracuseStep 19603721 = 14702791) B14702791
theorem B13069147 : Blo 2293435 13069147 := bstep (se 1 (by rfl) ⟨9801860, by rfl⟩ : syracuseStep 13069147 = 19603721) B19603721
theorem B17425529 : Blo 2293435 17425529 := bstep (se 2 (by rfl) ⟨6534573, by rfl⟩ : syracuseStep 17425529 = 13069147) B13069147
theorem B11617019 : Blo 2293435 11617019 := bstep (se 1 (by rfl) ⟨8712764, by rfl⟩ : syracuseStep 11617019 = 17425529) B17425529
theorem B7744679 : Blo 2293435 7744679 := bstep (se 1 (by rfl) ⟨5808509, by rfl⟩ : syracuseStep 7744679 = 11617019) B11617019
theorem B5163119 : Blo 2293435 5163119 := bstep (se 1 (by rfl) ⟨3872339, by rfl⟩ : syracuseStep 5163119 = 7744679) B7744679
theorem B3442079 : Blo 2293435 3442079 := bstep (se 1 (by rfl) ⟨2581559, by rfl⟩ : syracuseStep 3442079 = 5163119) B5163119
theorem B2294719 : Blo 2293435 2294719 := bstep (se 1 (by rfl) ⟨1721039, by rfl⟩ : syracuseStep 2294719 = 3442079) B3442079
theorem B3442085 : Blo 2293435 3442085 := bbase (se 4 (by rfl) ⟨322695, by rfl⟩ : syracuseStep 3442085 = 645391) (by norm_num)
theorem B2294723 : Blo 2293435 2294723 := bstep (se 1 (by rfl) ⟨1721042, by rfl⟩ : syracuseStep 2294723 = 3442085) B3442085
theorem B2904265 : Blo 2293435 2904265 := bbase (se 2 (by rfl) ⟨1089099, by rfl⟩ : syracuseStep 2904265 = 2178199) (by norm_num)
theorem B3872353 : Blo 2293435 3872353 := bstep (se 2 (by rfl) ⟨1452132, by rfl⟩ : syracuseStep 3872353 = 2904265) B2904265
theorem B5163137 : Blo 2293435 5163137 := bstep (se 2 (by rfl) ⟨1936176, by rfl⟩ : syracuseStep 5163137 = 3872353) B3872353
theorem B3442091 : Blo 2293435 3442091 := bstep (se 1 (by rfl) ⟨2581568, by rfl⟩ : syracuseStep 3442091 = 5163137) B5163137
theorem B2294727 : Blo 2293435 2294727 := bstep (se 1 (by rfl) ⟨1721045, by rfl⟩ : syracuseStep 2294727 = 3442091) B3442091
theorem B2581573 : Blo 2293435 2581573 := bbase (se 4 (by rfl) ⟨242022, by rfl⟩ : syracuseStep 2581573 = 484045) (by norm_num)
theorem B3442097 : Blo 2293435 3442097 := bstep (se 2 (by rfl) ⟨1290786, by rfl⟩ : syracuseStep 3442097 = 2581573) B2581573
theorem B2294731 : Blo 2293435 2294731 := bstep (se 1 (by rfl) ⟨1721048, by rfl⟩ : syracuseStep 2294731 = 3442097) B3442097
theorem B4356413 : Blo 2293435 4356413 := bbase (se 3 (by rfl) ⟨816827, by rfl⟩ : syracuseStep 4356413 = 1633655) (by norm_num)
theorem B2904275 : Blo 2293435 2904275 := bstep (se 1 (by rfl) ⟨2178206, by rfl⟩ : syracuseStep 2904275 = 4356413) B4356413
theorem B7744733 : Blo 2293435 7744733 := bstep (se 3 (by rfl) ⟨1452137, by rfl⟩ : syracuseStep 7744733 = 2904275) B2904275
theorem B5163155 : Blo 2293435 5163155 := bstep (se 1 (by rfl) ⟨3872366, by rfl⟩ : syracuseStep 5163155 = 7744733) B7744733
theorem B3442103 : Blo 2293435 3442103 := bstep (se 1 (by rfl) ⟨2581577, by rfl⟩ : syracuseStep 3442103 = 5163155) B5163155
theorem B2294735 : Blo 2293435 2294735 := bstep (se 1 (by rfl) ⟨1721051, by rfl⟩ : syracuseStep 2294735 = 3442103) B3442103
theorem B3442109 : Blo 2293435 3442109 := bbase (se 3 (by rfl) ⟨645395, by rfl⟩ : syracuseStep 3442109 = 1290791) (by norm_num)
theorem B2294739 : Blo 2293435 2294739 := bstep (se 1 (by rfl) ⟨1721054, by rfl⟩ : syracuseStep 2294739 = 3442109) B3442109
theorem B5163173 : Blo 2293435 5163173 := bbase (se 4 (by rfl) ⟨484047, by rfl⟩ : syracuseStep 5163173 = 968095) (by norm_num)
theorem B3442115 : Blo 2293435 3442115 := bstep (se 1 (by rfl) ⟨2581586, by rfl⟩ : syracuseStep 3442115 = 5163173) B5163173
theorem B2294743 : Blo 2293435 2294743 := bstep (se 1 (by rfl) ⟨1721057, by rfl⟩ : syracuseStep 2294743 = 3442115) B3442115
theorem B5808581 : Blo 2293435 5808581 := bbase (se 4 (by rfl) ⟨544554, by rfl⟩ : syracuseStep 5808581 = 1089109) (by norm_num)
theorem B3872387 : Blo 2293435 3872387 := bstep (se 1 (by rfl) ⟨2904290, by rfl⟩ : syracuseStep 3872387 = 5808581) B5808581
theorem B2581591 : Blo 2293435 2581591 := bstep (se 1 (by rfl) ⟨1936193, by rfl⟩ : syracuseStep 2581591 = 3872387) B3872387
theorem B3442121 : Blo 2293435 3442121 := bstep (se 2 (by rfl) ⟨1290795, by rfl⟩ : syracuseStep 3442121 = 2581591) B2581591
theorem B2294747 : Blo 2293435 2294747 := bstep (se 1 (by rfl) ⟨1721060, by rfl⟩ : syracuseStep 2294747 = 3442121) B3442121
theorem B8270437 : Blo 2293435 8270437 := bbase (se 4 (by rfl) ⟨775353, by rfl⟩ : syracuseStep 8270437 = 1550707) (by norm_num)
theorem B11027249 : Blo 2293435 11027249 := bstep (se 2 (by rfl) ⟨4135218, by rfl⟩ : syracuseStep 11027249 = 8270437) B8270437
theorem B7351499 : Blo 2293435 7351499 := bstep (se 1 (by rfl) ⟨5513624, by rfl⟩ : syracuseStep 7351499 = 11027249) B11027249
theorem B4900999 : Blo 2293435 4900999 := bstep (se 1 (by rfl) ⟨3675749, by rfl⟩ : syracuseStep 4900999 = 7351499) B7351499
theorem B6534665 : Blo 2293435 6534665 := bstep (se 2 (by rfl) ⟨2450499, by rfl⟩ : syracuseStep 6534665 = 4900999) B4900999
theorem B4356443 : Blo 2293435 4356443 := bstep (se 1 (by rfl) ⟨3267332, by rfl⟩ : syracuseStep 4356443 = 6534665) B6534665
theorem B11617181 : Blo 2293435 11617181 := bstep (se 3 (by rfl) ⟨2178221, by rfl⟩ : syracuseStep 11617181 = 4356443) B4356443
theorem B7744787 : Blo 2293435 7744787 := bstep (se 1 (by rfl) ⟨5808590, by rfl⟩ : syracuseStep 7744787 = 11617181) B11617181
theorem B5163191 : Blo 2293435 5163191 := bstep (se 1 (by rfl) ⟨3872393, by rfl⟩ : syracuseStep 5163191 = 7744787) B7744787
theorem B3442127 : Blo 2293435 3442127 := bstep (se 1 (by rfl) ⟨2581595, by rfl⟩ : syracuseStep 3442127 = 5163191) B5163191
theorem B2294751 : Blo 2293435 2294751 := bstep (se 1 (by rfl) ⟨1721063, by rfl⟩ : syracuseStep 2294751 = 3442127) B3442127
theorem B3442133 : Blo 2293435 3442133 := bbase (se 7 (by rfl) ⟨40337, by rfl⟩ : syracuseStep 3442133 = 80675) (by norm_num)
theorem B2294755 : Blo 2293435 2294755 := bstep (se 1 (by rfl) ⟨1721066, by rfl⟩ : syracuseStep 2294755 = 3442133) B3442133
theorem B8712917 : Blo 2293435 8712917 := bbase (se 7 (by rfl) ⟨102104, by rfl⟩ : syracuseStep 8712917 = 204209) (by norm_num)
theorem B5808611 : Blo 2293435 5808611 := bstep (se 1 (by rfl) ⟨4356458, by rfl⟩ : syracuseStep 5808611 = 8712917) B8712917
theorem B3872407 : Blo 2293435 3872407 := bstep (se 1 (by rfl) ⟨2904305, by rfl⟩ : syracuseStep 3872407 = 5808611) B5808611
theorem B5163209 : Blo 2293435 5163209 := bstep (se 2 (by rfl) ⟨1936203, by rfl⟩ : syracuseStep 5163209 = 3872407) B3872407
theorem B3442139 : Blo 2293435 3442139 := bstep (se 1 (by rfl) ⟨2581604, by rfl⟩ : syracuseStep 3442139 = 5163209) B5163209
theorem B2294759 : Blo 2293435 2294759 := bstep (se 1 (by rfl) ⟨1721069, by rfl⟩ : syracuseStep 2294759 = 3442139) B3442139
theorem B2581609 : Blo 2293435 2581609 := bbase (se 2 (by rfl) ⟨968103, by rfl⟩ : syracuseStep 2581609 = 1936207) (by norm_num)
theorem B3442145 : Blo 2293435 3442145 := bstep (se 2 (by rfl) ⟨1290804, by rfl⟩ : syracuseStep 3442145 = 2581609) B2581609
theorem B2294763 : Blo 2293435 2294763 := bstep (se 1 (by rfl) ⟨1721072, by rfl⟩ : syracuseStep 2294763 = 3442145) B3442145
theorem B6637717 : Blo 2293435 6637717 := bbase (se 6 (by rfl) ⟨155571, by rfl⟩ : syracuseStep 6637717 = 311143) (by norm_num)
theorem B35401157 : Blo 2293435 35401157 := bstep (se 4 (by rfl) ⟨3318858, by rfl⟩ : syracuseStep 35401157 = 6637717) B6637717
theorem B23600771 : Blo 2293435 23600771 := bstep (se 1 (by rfl) ⟨17700578, by rfl⟩ : syracuseStep 23600771 = 35401157) B35401157
theorem B15733847 : Blo 2293435 15733847 := bstep (se 1 (by rfl) ⟨11800385, by rfl⟩ : syracuseStep 15733847 = 23600771) B23600771
theorem B10489231 : Blo 2293435 10489231 := bstep (se 1 (by rfl) ⟨7866923, by rfl⟩ : syracuseStep 10489231 = 15733847) B15733847
theorem B13985641 : Blo 2293435 13985641 := bstep (se 2 (by rfl) ⟨5244615, by rfl⟩ : syracuseStep 13985641 = 10489231) B10489231
theorem B18647521 : Blo 2293435 18647521 := bstep (se 2 (by rfl) ⟨6992820, by rfl⟩ : syracuseStep 18647521 = 13985641) B13985641
theorem B397813781 : Blo 2293435 397813781 := bstep (se 6 (by rfl) ⟨9323760, by rfl⟩ : syracuseStep 397813781 = 18647521) B18647521
theorem B265209187 : Blo 2293435 265209187 := bstep (se 1 (by rfl) ⟨198906890, by rfl⟩ : syracuseStep 265209187 = 397813781) B397813781
theorem B353612249 : Blo 2293435 353612249 := bstep (se 2 (by rfl) ⟨132604593, by rfl⟩ : syracuseStep 353612249 = 265209187) B265209187
theorem B235741499 : Blo 2293435 235741499 := bstep (se 1 (by rfl) ⟨176806124, by rfl⟩ : syracuseStep 235741499 = 353612249) B353612249
theorem B157160999 : Blo 2293435 157160999 := bstep (se 1 (by rfl) ⟨117870749, by rfl⟩ : syracuseStep 157160999 = 235741499) B235741499
theorem B104773999 : Blo 2293435 104773999 := bstep (se 1 (by rfl) ⟨78580499, by rfl⟩ : syracuseStep 104773999 = 157160999) B157160999
theorem B139698665 : Blo 2293435 139698665 := bstep (se 2 (by rfl) ⟨52386999, by rfl⟩ : syracuseStep 139698665 = 104773999) B104773999
theorem B93132443 : Blo 2293435 93132443 := bstep (se 1 (by rfl) ⟨69849332, by rfl⟩ : syracuseStep 93132443 = 139698665) B139698665
theorem B62088295 : Blo 2293435 62088295 := bstep (se 1 (by rfl) ⟨46566221, by rfl⟩ : syracuseStep 62088295 = 93132443) B93132443
theorem B82784393 : Blo 2293435 82784393 := bstep (se 2 (by rfl) ⟨31044147, by rfl⟩ : syracuseStep 82784393 = 62088295) B62088295
theorem B55189595 : Blo 2293435 55189595 := bstep (se 1 (by rfl) ⟨41392196, by rfl⟩ : syracuseStep 55189595 = 82784393) B82784393
theorem B36793063 : Blo 2293435 36793063 := bstep (se 1 (by rfl) ⟨27594797, by rfl⟩ : syracuseStep 36793063 = 55189595) B55189595
theorem B49057417 : Blo 2293435 49057417 := bstep (se 2 (by rfl) ⟨18396531, by rfl⟩ : syracuseStep 49057417 = 36793063) B36793063
theorem B65409889 : Blo 2293435 65409889 := bstep (se 2 (by rfl) ⟨24528708, by rfl⟩ : syracuseStep 65409889 = 49057417) B49057417
theorem B87213185 : Blo 2293435 87213185 := bstep (se 2 (by rfl) ⟨32704944, by rfl⟩ : syracuseStep 87213185 = 65409889) B65409889
theorem B58142123 : Blo 2293435 58142123 := bstep (se 1 (by rfl) ⟨43606592, by rfl⟩ : syracuseStep 58142123 = 87213185) B87213185
theorem B38761415 : Blo 2293435 38761415 := bstep (se 1 (by rfl) ⟨29071061, by rfl⟩ : syracuseStep 38761415 = 58142123) B58142123
theorem B25840943 : Blo 2293435 25840943 := bstep (se 1 (by rfl) ⟨19380707, by rfl⟩ : syracuseStep 25840943 = 38761415) B38761415
theorem B17227295 : Blo 2293435 17227295 := bstep (se 1 (by rfl) ⟨12920471, by rfl⟩ : syracuseStep 17227295 = 25840943) B25840943
theorem B11484863 : Blo 2293435 11484863 := bstep (se 1 (by rfl) ⟨8613647, by rfl⟩ : syracuseStep 11484863 = 17227295) B17227295
theorem B7656575 : Blo 2293435 7656575 := bstep (se 1 (by rfl) ⟨5742431, by rfl⟩ : syracuseStep 7656575 = 11484863) B11484863
theorem B81670133 : Blo 2293435 81670133 := bstep (se 5 (by rfl) ⟨3828287, by rfl⟩ : syracuseStep 81670133 = 7656575) B7656575
theorem B54446755 : Blo 2293435 54446755 := bstep (se 1 (by rfl) ⟨40835066, by rfl⟩ : syracuseStep 54446755 = 81670133) B81670133
theorem B72595673 : Blo 2293435 72595673 := bstep (se 2 (by rfl) ⟨27223377, by rfl⟩ : syracuseStep 72595673 = 54446755) B54446755
theorem B48397115 : Blo 2293435 48397115 := bstep (se 1 (by rfl) ⟨36297836, by rfl⟩ : syracuseStep 48397115 = 72595673) B72595673
theorem B32264743 : Blo 2293435 32264743 := bstep (se 1 (by rfl) ⟨24198557, by rfl⟩ : syracuseStep 32264743 = 48397115) B48397115
theorem B43019657 : Blo 2293435 43019657 := bstep (se 2 (by rfl) ⟨16132371, by rfl⟩ : syracuseStep 43019657 = 32264743) B32264743
theorem B28679771 : Blo 2293435 28679771 := bstep (se 1 (by rfl) ⟨21509828, by rfl⟩ : syracuseStep 28679771 = 43019657) B43019657
theorem B76479389 : Blo 2293435 76479389 := bstep (se 3 (by rfl) ⟨14339885, by rfl⟩ : syracuseStep 76479389 = 28679771) B28679771
theorem B50986259 : Blo 2293435 50986259 := bstep (se 1 (by rfl) ⟨38239694, by rfl⟩ : syracuseStep 50986259 = 76479389) B76479389
theorem B33990839 : Blo 2293435 33990839 := bstep (se 1 (by rfl) ⟨25493129, by rfl⟩ : syracuseStep 33990839 = 50986259) B50986259
theorem B22660559 : Blo 2293435 22660559 := bstep (se 1 (by rfl) ⟨16995419, by rfl⟩ : syracuseStep 22660559 = 33990839) B33990839
theorem B15107039 : Blo 2293435 15107039 := bstep (se 1 (by rfl) ⟨11330279, by rfl⟩ : syracuseStep 15107039 = 22660559) B22660559
theorem B10071359 : Blo 2293435 10071359 := bstep (se 1 (by rfl) ⟨7553519, by rfl⟩ : syracuseStep 10071359 = 15107039) B15107039
theorem B107427829 : Blo 2293435 107427829 := bstep (se 5 (by rfl) ⟨5035679, by rfl⟩ : syracuseStep 107427829 = 10071359) B10071359
theorem B143237105 : Blo 2293435 143237105 := bstep (se 2 (by rfl) ⟨53713914, by rfl⟩ : syracuseStep 143237105 = 107427829) B107427829
theorem B95491403 : Blo 2293435 95491403 := bstep (se 1 (by rfl) ⟨71618552, by rfl⟩ : syracuseStep 95491403 = 143237105) B143237105
theorem B63660935 : Blo 2293435 63660935 := bstep (se 1 (by rfl) ⟨47745701, by rfl⟩ : syracuseStep 63660935 = 95491403) B95491403
theorem B169762493 : Blo 2293435 169762493 := bstep (se 3 (by rfl) ⟨31830467, by rfl⟩ : syracuseStep 169762493 = 63660935) B63660935
theorem B113174995 : Blo 2293435 113174995 := bstep (se 1 (by rfl) ⟨84881246, by rfl⟩ : syracuseStep 113174995 = 169762493) B169762493
theorem B150899993 : Blo 2293435 150899993 := bstep (se 2 (by rfl) ⟨56587497, by rfl⟩ : syracuseStep 150899993 = 113174995) B113174995
theorem B100599995 : Blo 2293435 100599995 := bstep (se 1 (by rfl) ⟨75449996, by rfl⟩ : syracuseStep 100599995 = 150899993) B150899993
theorem B67066663 : Blo 2293435 67066663 := bstep (se 1 (by rfl) ⟨50299997, by rfl⟩ : syracuseStep 67066663 = 100599995) B100599995
theorem B89422217 : Blo 2293435 89422217 := bstep (se 2 (by rfl) ⟨33533331, by rfl⟩ : syracuseStep 89422217 = 67066663) B67066663
theorem B59614811 : Blo 2293435 59614811 := bstep (se 1 (by rfl) ⟨44711108, by rfl⟩ : syracuseStep 59614811 = 89422217) B89422217
theorem B39743207 : Blo 2293435 39743207 := bstep (se 1 (by rfl) ⟨29807405, by rfl⟩ : syracuseStep 39743207 = 59614811) B59614811
theorem B26495471 : Blo 2293435 26495471 := bstep (se 1 (by rfl) ⟨19871603, by rfl⟩ : syracuseStep 26495471 = 39743207) B39743207
theorem B70654589 : Blo 2293435 70654589 := bstep (se 3 (by rfl) ⟨13247735, by rfl⟩ : syracuseStep 70654589 = 26495471) B26495471
theorem B47103059 : Blo 2293435 47103059 := bstep (se 1 (by rfl) ⟨35327294, by rfl⟩ : syracuseStep 47103059 = 70654589) B70654589
theorem B31402039 : Blo 2293435 31402039 := bstep (se 1 (by rfl) ⟨23551529, by rfl⟩ : syracuseStep 31402039 = 47103059) B47103059
theorem B41869385 : Blo 2293435 41869385 := bstep (se 2 (by rfl) ⟨15701019, by rfl⟩ : syracuseStep 41869385 = 31402039) B31402039
theorem B27912923 : Blo 2293435 27912923 := bstep (se 1 (by rfl) ⟨20934692, by rfl⟩ : syracuseStep 27912923 = 41869385) B41869385
theorem B18608615 : Blo 2293435 18608615 := bstep (se 1 (by rfl) ⟨13956461, by rfl⟩ : syracuseStep 18608615 = 27912923) B27912923
theorem B12405743 : Blo 2293435 12405743 := bstep (se 1 (by rfl) ⟨9304307, by rfl⟩ : syracuseStep 12405743 = 18608615) B18608615
theorem B8270495 : Blo 2293435 8270495 := bstep (se 1 (by rfl) ⟨6202871, by rfl⟩ : syracuseStep 8270495 = 12405743) B12405743
theorem B5513663 : Blo 2293435 5513663 := bstep (se 1 (by rfl) ⟨4135247, by rfl⟩ : syracuseStep 5513663 = 8270495) B8270495
theorem B3675775 : Blo 2293435 3675775 := bstep (se 1 (by rfl) ⟨2756831, by rfl⟩ : syracuseStep 3675775 = 5513663) B5513663
theorem B4901033 : Blo 2293435 4901033 := bstep (se 2 (by rfl) ⟨1837887, by rfl⟩ : syracuseStep 4901033 = 3675775) B3675775
theorem B13069421 : Blo 2293435 13069421 := bstep (se 3 (by rfl) ⟨2450516, by rfl⟩ : syracuseStep 13069421 = 4901033) B4901033
theorem B8712947 : Blo 2293435 8712947 := bstep (se 1 (by rfl) ⟨6534710, by rfl⟩ : syracuseStep 8712947 = 13069421) B13069421
theorem B5808631 : Blo 2293435 5808631 := bstep (se 1 (by rfl) ⟨4356473, by rfl⟩ : syracuseStep 5808631 = 8712947) B8712947
theorem B7744841 : Blo 2293435 7744841 := bstep (se 2 (by rfl) ⟨2904315, by rfl⟩ : syracuseStep 7744841 = 5808631) B5808631
theorem B5163227 : Blo 2293435 5163227 := bstep (se 1 (by rfl) ⟨3872420, by rfl⟩ : syracuseStep 5163227 = 7744841) B7744841
theorem B3442151 : Blo 2293435 3442151 := bstep (se 1 (by rfl) ⟨2581613, by rfl⟩ : syracuseStep 3442151 = 5163227) B5163227
theorem B2294767 : Blo 2293435 2294767 := bstep (se 1 (by rfl) ⟨1721075, by rfl⟩ : syracuseStep 2294767 = 3442151) B3442151
theorem B3442157 : Blo 2293435 3442157 := bbase (se 3 (by rfl) ⟨645404, by rfl⟩ : syracuseStep 3442157 = 1290809) (by norm_num)
theorem B2294771 : Blo 2293435 2294771 := bstep (se 1 (by rfl) ⟨1721078, by rfl⟩ : syracuseStep 2294771 = 3442157) B3442157
theorem B5163245 : Blo 2293435 5163245 := bbase (se 3 (by rfl) ⟨968108, by rfl⟩ : syracuseStep 5163245 = 1936217) (by norm_num)
theorem B3442163 : Blo 2293435 3442163 := bstep (se 1 (by rfl) ⟨2581622, by rfl⟩ : syracuseStep 3442163 = 5163245) B5163245
theorem B2294775 : Blo 2293435 2294775 := bstep (se 1 (by rfl) ⟨1721081, by rfl⟩ : syracuseStep 2294775 = 3442163) B3442163
theorem B3267373 : Blo 2293435 3267373 := bbase (se 3 (by rfl) ⟨612632, by rfl⟩ : syracuseStep 3267373 = 1225265) (by norm_num)
theorem B4356497 : Blo 2293435 4356497 := bstep (se 2 (by rfl) ⟨1633686, by rfl⟩ : syracuseStep 4356497 = 3267373) B3267373
theorem B2904331 : Blo 2293435 2904331 := bstep (se 1 (by rfl) ⟨2178248, by rfl⟩ : syracuseStep 2904331 = 4356497) B4356497
theorem B3872441 : Blo 2293435 3872441 := bstep (se 2 (by rfl) ⟨1452165, by rfl⟩ : syracuseStep 3872441 = 2904331) B2904331
theorem B2581627 : Blo 2293435 2581627 := bstep (se 1 (by rfl) ⟨1936220, by rfl⟩ : syracuseStep 2581627 = 3872441) B3872441
theorem B3442169 : Blo 2293435 3442169 := bstep (se 2 (by rfl) ⟨1290813, by rfl⟩ : syracuseStep 3442169 = 2581627) B2581627
theorem B2294779 : Blo 2293435 2294779 := bstep (se 1 (by rfl) ⟨1721084, by rfl⟩ : syracuseStep 2294779 = 3442169) B3442169
theorem B5233709 : Blo 2293435 5233709 := bbase (se 3 (by rfl) ⟨981320, by rfl⟩ : syracuseStep 5233709 = 1962641) (by norm_num)
theorem B3489139 : Blo 2293435 3489139 := bstep (se 1 (by rfl) ⟨2616854, by rfl⟩ : syracuseStep 3489139 = 5233709) B5233709
theorem B4652185 : Blo 2293435 4652185 := bstep (se 2 (by rfl) ⟨1744569, by rfl⟩ : syracuseStep 4652185 = 3489139) B3489139
theorem B6202913 : Blo 2293435 6202913 := bstep (se 2 (by rfl) ⟨2326092, by rfl⟩ : syracuseStep 6202913 = 4652185) B4652185
theorem B16541101 : Blo 2293435 16541101 := bstep (se 3 (by rfl) ⟨3101456, by rfl⟩ : syracuseStep 16541101 = 6202913) B6202913
theorem B88219205 : Blo 2293435 88219205 := bstep (se 4 (by rfl) ⟨8270550, by rfl⟩ : syracuseStep 88219205 = 16541101) B16541101
theorem B58812803 : Blo 2293435 58812803 := bstep (se 1 (by rfl) ⟨44109602, by rfl⟩ : syracuseStep 58812803 = 88219205) B88219205
theorem B39208535 : Blo 2293435 39208535 := bstep (se 1 (by rfl) ⟨29406401, by rfl⟩ : syracuseStep 39208535 = 58812803) B58812803
theorem B26139023 : Blo 2293435 26139023 := bstep (se 1 (by rfl) ⟨19604267, by rfl⟩ : syracuseStep 26139023 = 39208535) B39208535
theorem B17426015 : Blo 2293435 17426015 := bstep (se 1 (by rfl) ⟨13069511, by rfl⟩ : syracuseStep 17426015 = 26139023) B26139023
theorem B11617343 : Blo 2293435 11617343 := bstep (se 1 (by rfl) ⟨8713007, by rfl⟩ : syracuseStep 11617343 = 17426015) B17426015
theorem B7744895 : Blo 2293435 7744895 := bstep (se 1 (by rfl) ⟨5808671, by rfl⟩ : syracuseStep 7744895 = 11617343) B11617343
theorem B5163263 : Blo 2293435 5163263 := bstep (se 1 (by rfl) ⟨3872447, by rfl⟩ : syracuseStep 5163263 = 7744895) B7744895
theorem B3442175 : Blo 2293435 3442175 := bstep (se 1 (by rfl) ⟨2581631, by rfl⟩ : syracuseStep 3442175 = 5163263) B5163263
theorem B2294783 : Blo 2293435 2294783 := bstep (se 1 (by rfl) ⟨1721087, by rfl⟩ : syracuseStep 2294783 = 3442175) B3442175
theorem B3442181 : Blo 2293435 3442181 := bbase (se 4 (by rfl) ⟨322704, by rfl⟩ : syracuseStep 3442181 = 645409) (by norm_num)
theorem B2294787 : Blo 2293435 2294787 := bstep (se 1 (by rfl) ⟨1721090, by rfl⟩ : syracuseStep 2294787 = 3442181) B3442181
theorem B3872461 : Blo 2293435 3872461 := bbase (se 3 (by rfl) ⟨726086, by rfl⟩ : syracuseStep 3872461 = 1452173) (by norm_num)
theorem B5163281 : Blo 2293435 5163281 := bstep (se 2 (by rfl) ⟨1936230, by rfl⟩ : syracuseStep 5163281 = 3872461) B3872461
theorem B3442187 : Blo 2293435 3442187 := bstep (se 1 (by rfl) ⟨2581640, by rfl⟩ : syracuseStep 3442187 = 5163281) B5163281
theorem B2294791 : Blo 2293435 2294791 := bstep (se 1 (by rfl) ⟨1721093, by rfl⟩ : syracuseStep 2294791 = 3442187) B3442187
theorem B2581645 : Blo 2293435 2581645 := bbase (se 3 (by rfl) ⟨484058, by rfl⟩ : syracuseStep 2581645 = 968117) (by norm_num)
theorem B3442193 : Blo 2293435 3442193 := bstep (se 2 (by rfl) ⟨1290822, by rfl⟩ : syracuseStep 3442193 = 2581645) B2581645
theorem B2294795 : Blo 2293435 2294795 := bstep (se 1 (by rfl) ⟨1721096, by rfl⟩ : syracuseStep 2294795 = 3442193) B3442193
theorem B7744949 : Blo 2293435 7744949 := bbase (se 5 (by rfl) ⟨363044, by rfl⟩ : syracuseStep 7744949 = 726089) (by norm_num)
theorem B5163299 : Blo 2293435 5163299 := bstep (se 1 (by rfl) ⟨3872474, by rfl⟩ : syracuseStep 5163299 = 7744949) B7744949
theorem B3442199 : Blo 2293435 3442199 := bstep (se 1 (by rfl) ⟨2581649, by rfl⟩ : syracuseStep 3442199 = 5163299) B5163299
theorem B2294799 : Blo 2293435 2294799 := bstep (se 1 (by rfl) ⟨1721099, by rfl⟩ : syracuseStep 2294799 = 3442199) B3442199
theorem B3442205 : Blo 2293435 3442205 := bbase (se 3 (by rfl) ⟨645413, by rfl⟩ : syracuseStep 3442205 = 1290827) (by norm_num)
theorem B2294803 : Blo 2293435 2294803 := bstep (se 1 (by rfl) ⟨1721102, by rfl⟩ : syracuseStep 2294803 = 3442205) B3442205
theorem B5163317 : Blo 2293435 5163317 := bbase (se 5 (by rfl) ⟨242030, by rfl⟩ : syracuseStep 5163317 = 484061) (by norm_num)
theorem B3442211 : Blo 2293435 3442211 := bstep (se 1 (by rfl) ⟨2581658, by rfl⟩ : syracuseStep 3442211 = 5163317) B5163317
theorem B2294807 : Blo 2293435 2294807 := bstep (se 1 (by rfl) ⟨1721105, by rfl⟩ : syracuseStep 2294807 = 3442211) B3442211
theorem B5887997 : Blo 2293435 5887997 := bbase (se 3 (by rfl) ⟨1103999, by rfl⟩ : syracuseStep 5887997 = 2207999) (by norm_num)
theorem B3925331 : Blo 2293435 3925331 := bstep (se 1 (by rfl) ⟨2943998, by rfl⟩ : syracuseStep 3925331 = 5887997) B5887997
theorem B2616887 : Blo 2293435 2616887 := bstep (se 1 (by rfl) ⟨1962665, by rfl⟩ : syracuseStep 2616887 = 3925331) B3925331
theorem B6978365 : Blo 2293435 6978365 := bstep (se 3 (by rfl) ⟨1308443, by rfl⟩ : syracuseStep 6978365 = 2616887) B2616887
theorem B4652243 : Blo 2293435 4652243 := bstep (se 1 (by rfl) ⟨3489182, by rfl⟩ : syracuseStep 4652243 = 6978365) B6978365
theorem B3101495 : Blo 2293435 3101495 := bstep (se 1 (by rfl) ⟨2326121, by rfl⟩ : syracuseStep 3101495 = 4652243) B4652243
theorem B33082613 : Blo 2293435 33082613 := bstep (se 5 (by rfl) ⟨1550747, by rfl⟩ : syracuseStep 33082613 = 3101495) B3101495
theorem B22055075 : Blo 2293435 22055075 := bstep (se 1 (by rfl) ⟨16541306, by rfl⟩ : syracuseStep 22055075 = 33082613) B33082613
theorem B14703383 : Blo 2293435 14703383 := bstep (se 1 (by rfl) ⟨11027537, by rfl⟩ : syracuseStep 14703383 = 22055075) B22055075
theorem B9802255 : Blo 2293435 9802255 := bstep (se 1 (by rfl) ⟨7351691, by rfl⟩ : syracuseStep 9802255 = 14703383) B14703383
theorem B13069673 : Blo 2293435 13069673 := bstep (se 2 (by rfl) ⟨4901127, by rfl⟩ : syracuseStep 13069673 = 9802255) B9802255
theorem B8713115 : Blo 2293435 8713115 := bstep (se 1 (by rfl) ⟨6534836, by rfl⟩ : syracuseStep 8713115 = 13069673) B13069673
theorem B5808743 : Blo 2293435 5808743 := bstep (se 1 (by rfl) ⟨4356557, by rfl⟩ : syracuseStep 5808743 = 8713115) B8713115
theorem B3872495 : Blo 2293435 3872495 := bstep (se 1 (by rfl) ⟨2904371, by rfl⟩ : syracuseStep 3872495 = 5808743) B5808743
theorem B2581663 : Blo 2293435 2581663 := bstep (se 1 (by rfl) ⟨1936247, by rfl⟩ : syracuseStep 2581663 = 3872495) B3872495
theorem B3442217 : Blo 2293435 3442217 := bstep (se 2 (by rfl) ⟨1290831, by rfl⟩ : syracuseStep 3442217 = 2581663) B2581663
theorem B2294811 : Blo 2293435 2294811 := bstep (se 1 (by rfl) ⟨1721108, by rfl⟩ : syracuseStep 2294811 = 3442217) B3442217
theorem B5589005 : Blo 2293435 5589005 := bbase (se 3 (by rfl) ⟨1047938, by rfl⟩ : syracuseStep 5589005 = 2095877) (by norm_num)
theorem B14904013 : Blo 2293435 14904013 := bstep (se 3 (by rfl) ⟨2794502, by rfl⟩ : syracuseStep 14904013 = 5589005) B5589005
theorem B19872017 : Blo 2293435 19872017 := bstep (se 2 (by rfl) ⟨7452006, by rfl⟩ : syracuseStep 19872017 = 14904013) B14904013
theorem B13248011 : Blo 2293435 13248011 := bstep (se 1 (by rfl) ⟨9936008, by rfl⟩ : syracuseStep 13248011 = 19872017) B19872017
theorem B8832007 : Blo 2293435 8832007 := bstep (se 1 (by rfl) ⟨6624005, by rfl⟩ : syracuseStep 8832007 = 13248011) B13248011
theorem B11776009 : Blo 2293435 11776009 := bstep (se 2 (by rfl) ⟨4416003, by rfl⟩ : syracuseStep 11776009 = 8832007) B8832007
theorem B15701345 : Blo 2293435 15701345 := bstep (se 2 (by rfl) ⟨5888004, by rfl⟩ : syracuseStep 15701345 = 11776009) B11776009
theorem B10467563 : Blo 2293435 10467563 := bstep (se 1 (by rfl) ⟨7850672, by rfl⟩ : syracuseStep 10467563 = 15701345) B15701345
theorem B27913501 : Blo 2293435 27913501 := bstep (se 3 (by rfl) ⟨5233781, by rfl⟩ : syracuseStep 27913501 = 10467563) B10467563
theorem B37218001 : Blo 2293435 37218001 := bstep (se 2 (by rfl) ⟨13956750, by rfl⟩ : syracuseStep 37218001 = 27913501) B27913501
theorem B49624001 : Blo 2293435 49624001 := bstep (se 2 (by rfl) ⟨18609000, by rfl⟩ : syracuseStep 49624001 = 37218001) B37218001
theorem B33082667 : Blo 2293435 33082667 := bstep (se 1 (by rfl) ⟨24812000, by rfl⟩ : syracuseStep 33082667 = 49624001) B49624001
theorem B22055111 : Blo 2293435 22055111 := bstep (se 1 (by rfl) ⟨16541333, by rfl⟩ : syracuseStep 22055111 = 33082667) B33082667
theorem B14703407 : Blo 2293435 14703407 := bstep (se 1 (by rfl) ⟨11027555, by rfl⟩ : syracuseStep 14703407 = 22055111) B22055111
theorem B9802271 : Blo 2293435 9802271 := bstep (se 1 (by rfl) ⟨7351703, by rfl⟩ : syracuseStep 9802271 = 14703407) B14703407
theorem B6534847 : Blo 2293435 6534847 := bstep (se 1 (by rfl) ⟨4901135, by rfl⟩ : syracuseStep 6534847 = 9802271) B9802271
theorem B8713129 : Blo 2293435 8713129 := bstep (se 2 (by rfl) ⟨3267423, by rfl⟩ : syracuseStep 8713129 = 6534847) B6534847
theorem B11617505 : Blo 2293435 11617505 := bstep (se 2 (by rfl) ⟨4356564, by rfl⟩ : syracuseStep 11617505 = 8713129) B8713129
theorem B7745003 : Blo 2293435 7745003 := bstep (se 1 (by rfl) ⟨5808752, by rfl⟩ : syracuseStep 7745003 = 11617505) B11617505
theorem B5163335 : Blo 2293435 5163335 := bstep (se 1 (by rfl) ⟨3872501, by rfl⟩ : syracuseStep 5163335 = 7745003) B7745003
theorem B3442223 : Blo 2293435 3442223 := bstep (se 1 (by rfl) ⟨2581667, by rfl⟩ : syracuseStep 3442223 = 5163335) B5163335
theorem B2294815 : Blo 2293435 2294815 := bstep (se 1 (by rfl) ⟨1721111, by rfl⟩ : syracuseStep 2294815 = 3442223) B3442223
theorem B3442229 : Blo 2293435 3442229 := bbase (se 5 (by rfl) ⟨161354, by rfl⟩ : syracuseStep 3442229 = 322709) (by norm_num)
theorem B2294819 : Blo 2293435 2294819 := bstep (se 1 (by rfl) ⟨1721114, by rfl⟩ : syracuseStep 2294819 = 3442229) B3442229
theorem B5808773 : Blo 2293435 5808773 := bbase (se 4 (by rfl) ⟨544572, by rfl⟩ : syracuseStep 5808773 = 1089145) (by norm_num)
theorem B3872515 : Blo 2293435 3872515 := bstep (se 1 (by rfl) ⟨2904386, by rfl⟩ : syracuseStep 3872515 = 5808773) B5808773
theorem B5163353 : Blo 2293435 5163353 := bstep (se 2 (by rfl) ⟨1936257, by rfl⟩ : syracuseStep 5163353 = 3872515) B3872515
theorem B3442235 : Blo 2293435 3442235 := bstep (se 1 (by rfl) ⟨2581676, by rfl⟩ : syracuseStep 3442235 = 5163353) B5163353
theorem B2294823 : Blo 2293435 2294823 := bstep (se 1 (by rfl) ⟨1721117, by rfl⟩ : syracuseStep 2294823 = 3442235) B3442235
theorem B2581681 : Blo 2293435 2581681 := bbase (se 2 (by rfl) ⟨968130, by rfl⟩ : syracuseStep 2581681 = 1936261) (by norm_num)
theorem B3442241 : Blo 2293435 3442241 := bstep (se 2 (by rfl) ⟨1290840, by rfl⟩ : syracuseStep 3442241 = 2581681) B2581681
theorem B2294827 : Blo 2293435 2294827 := bstep (se 1 (by rfl) ⟨1721120, by rfl⟩ : syracuseStep 2294827 = 3442241) B3442241
theorem B2450585 : Blo 2293435 2450585 := bbase (se 2 (by rfl) ⟨918969, by rfl⟩ : syracuseStep 2450585 = 1837939) (by norm_num)
theorem B6534893 : Blo 2293435 6534893 := bstep (se 3 (by rfl) ⟨1225292, by rfl⟩ : syracuseStep 6534893 = 2450585) B2450585
theorem B4356595 : Blo 2293435 4356595 := bstep (se 1 (by rfl) ⟨3267446, by rfl⟩ : syracuseStep 4356595 = 6534893) B6534893
theorem B5808793 : Blo 2293435 5808793 := bstep (se 2 (by rfl) ⟨2178297, by rfl⟩ : syracuseStep 5808793 = 4356595) B4356595
theorem B7745057 : Blo 2293435 7745057 := bstep (se 2 (by rfl) ⟨2904396, by rfl⟩ : syracuseStep 7745057 = 5808793) B5808793
theorem B5163371 : Blo 2293435 5163371 := bstep (se 1 (by rfl) ⟨3872528, by rfl⟩ : syracuseStep 5163371 = 7745057) B7745057
theorem B3442247 : Blo 2293435 3442247 := bstep (se 1 (by rfl) ⟨2581685, by rfl⟩ : syracuseStep 3442247 = 5163371) B5163371
theorem B2294831 : Blo 2293435 2294831 := bstep (se 1 (by rfl) ⟨1721123, by rfl⟩ : syracuseStep 2294831 = 3442247) B3442247
theorem B3442253 : Blo 2293435 3442253 := bbase (se 3 (by rfl) ⟨645422, by rfl⟩ : syracuseStep 3442253 = 1290845) (by norm_num)
theorem B2294835 : Blo 2293435 2294835 := bstep (se 1 (by rfl) ⟨1721126, by rfl⟩ : syracuseStep 2294835 = 3442253) B3442253
theorem B5163389 : Blo 2293435 5163389 := bbase (se 3 (by rfl) ⟨968135, by rfl⟩ : syracuseStep 5163389 = 1936271) (by norm_num)
theorem B3442259 : Blo 2293435 3442259 := bstep (se 1 (by rfl) ⟨2581694, by rfl⟩ : syracuseStep 3442259 = 5163389) B5163389
theorem B2294839 : Blo 2293435 2294839 := bstep (se 1 (by rfl) ⟨1721129, by rfl⟩ : syracuseStep 2294839 = 3442259) B3442259
theorem B3872549 : Blo 2293435 3872549 := bbase (se 4 (by rfl) ⟨363051, by rfl⟩ : syracuseStep 3872549 = 726103) (by norm_num)
theorem B2581699 : Blo 2293435 2581699 := bstep (se 1 (by rfl) ⟨1936274, by rfl⟩ : syracuseStep 2581699 = 3872549) B3872549
theorem B3442265 : Blo 2293435 3442265 := bstep (se 2 (by rfl) ⟨1290849, by rfl⟩ : syracuseStep 3442265 = 2581699) B2581699
theorem B2294843 : Blo 2293435 2294843 := bstep (se 1 (by rfl) ⟨1721132, by rfl⟩ : syracuseStep 2294843 = 3442265) B3442265
theorem B3267469 : Blo 2293435 3267469 := bbase (se 3 (by rfl) ⟨612650, by rfl⟩ : syracuseStep 3267469 = 1225301) (by norm_num)
theorem B17426501 : Blo 2293435 17426501 := bstep (se 4 (by rfl) ⟨1633734, by rfl⟩ : syracuseStep 17426501 = 3267469) B3267469
theorem B11617667 : Blo 2293435 11617667 := bstep (se 1 (by rfl) ⟨8713250, by rfl⟩ : syracuseStep 11617667 = 17426501) B17426501
theorem B7745111 : Blo 2293435 7745111 := bstep (se 1 (by rfl) ⟨5808833, by rfl⟩ : syracuseStep 7745111 = 11617667) B11617667
theorem B5163407 : Blo 2293435 5163407 := bstep (se 1 (by rfl) ⟨3872555, by rfl⟩ : syracuseStep 5163407 = 7745111) B7745111
theorem B3442271 : Blo 2293435 3442271 := bstep (se 1 (by rfl) ⟨2581703, by rfl⟩ : syracuseStep 3442271 = 5163407) B5163407
theorem B2294847 : Blo 2293435 2294847 := bstep (se 1 (by rfl) ⟨1721135, by rfl⟩ : syracuseStep 2294847 = 3442271) B3442271
theorem B3442277 : Blo 2293435 3442277 := bbase (se 4 (by rfl) ⟨322713, by rfl⟩ : syracuseStep 3442277 = 645427) (by norm_num)
theorem B2294851 : Blo 2293435 2294851 := bstep (se 1 (by rfl) ⟨1721138, by rfl⟩ : syracuseStep 2294851 = 3442277) B3442277
theorem B3675917 : Blo 2293435 3675917 := bbase (se 3 (by rfl) ⟨689234, by rfl⟩ : syracuseStep 3675917 = 1378469) (by norm_num)
theorem B2450611 : Blo 2293435 2450611 := bstep (se 1 (by rfl) ⟨1837958, by rfl⟩ : syracuseStep 2450611 = 3675917) B3675917
theorem B3267481 : Blo 2293435 3267481 := bstep (se 2 (by rfl) ⟨1225305, by rfl⟩ : syracuseStep 3267481 = 2450611) B2450611
theorem B4356641 : Blo 2293435 4356641 := bstep (se 2 (by rfl) ⟨1633740, by rfl⟩ : syracuseStep 4356641 = 3267481) B3267481
theorem B2904427 : Blo 2293435 2904427 := bstep (se 1 (by rfl) ⟨2178320, by rfl⟩ : syracuseStep 2904427 = 4356641) B4356641
theorem B3872569 : Blo 2293435 3872569 := bstep (se 2 (by rfl) ⟨1452213, by rfl⟩ : syracuseStep 3872569 = 2904427) B2904427
theorem B5163425 : Blo 2293435 5163425 := bstep (se 2 (by rfl) ⟨1936284, by rfl⟩ : syracuseStep 5163425 = 3872569) B3872569
theorem B3442283 : Blo 2293435 3442283 := bstep (se 1 (by rfl) ⟨2581712, by rfl⟩ : syracuseStep 3442283 = 5163425) B5163425
theorem B2294855 : Blo 2293435 2294855 := bstep (se 1 (by rfl) ⟨1721141, by rfl⟩ : syracuseStep 2294855 = 3442283) B3442283
theorem B2581717 : Blo 2293435 2581717 := bbase (se 7 (by rfl) ⟨30254, by rfl⟩ : syracuseStep 2581717 = 60509) (by norm_num)
theorem B3442289 : Blo 2293435 3442289 := bstep (se 2 (by rfl) ⟨1290858, by rfl⟩ : syracuseStep 3442289 = 2581717) B2581717
theorem B2294859 : Blo 2293435 2294859 := bstep (se 1 (by rfl) ⟨1721144, by rfl⟩ : syracuseStep 2294859 = 3442289) B3442289
theorem B2904437 : Blo 2293435 2904437 := bbase (se 5 (by rfl) ⟨136145, by rfl⟩ : syracuseStep 2904437 = 272291) (by norm_num)
theorem B7745165 : Blo 2293435 7745165 := bstep (se 3 (by rfl) ⟨1452218, by rfl⟩ : syracuseStep 7745165 = 2904437) B2904437
theorem B5163443 : Blo 2293435 5163443 := bstep (se 1 (by rfl) ⟨3872582, by rfl⟩ : syracuseStep 5163443 = 7745165) B7745165
theorem B3442295 : Blo 2293435 3442295 := bstep (se 1 (by rfl) ⟨2581721, by rfl⟩ : syracuseStep 3442295 = 5163443) B5163443
theorem B2294863 : Blo 2293435 2294863 := bstep (se 1 (by rfl) ⟨1721147, by rfl⟩ : syracuseStep 2294863 = 3442295) B3442295
theorem B3442301 : Blo 2293435 3442301 := bbase (se 3 (by rfl) ⟨645431, by rfl⟩ : syracuseStep 3442301 = 1290863) (by norm_num)
theorem B2294867 : Blo 2293435 2294867 := bstep (se 1 (by rfl) ⟨1721150, by rfl⟩ : syracuseStep 2294867 = 3442301) B3442301
theorem B5163461 : Blo 2293435 5163461 := bbase (se 4 (by rfl) ⟨484074, by rfl⟩ : syracuseStep 5163461 = 968149) (by norm_num)
theorem B3442307 : Blo 2293435 3442307 := bstep (se 1 (by rfl) ⟨2581730, by rfl⟩ : syracuseStep 3442307 = 5163461) B5163461
theorem B2294871 : Blo 2293435 2294871 := bstep (se 1 (by rfl) ⟨1721153, by rfl⟩ : syracuseStep 2294871 = 3442307) B3442307
theorem B8270885 : Blo 2293435 8270885 := bbase (se 4 (by rfl) ⟨775395, by rfl⟩ : syracuseStep 8270885 = 1550791) (by norm_num)
theorem B5513923 : Blo 2293435 5513923 := bstep (se 1 (by rfl) ⟨4135442, by rfl⟩ : syracuseStep 5513923 = 8270885) B8270885
theorem B7351897 : Blo 2293435 7351897 := bstep (se 2 (by rfl) ⟨2756961, by rfl⟩ : syracuseStep 7351897 = 5513923) B5513923
theorem B9802529 : Blo 2293435 9802529 := bstep (se 2 (by rfl) ⟨3675948, by rfl⟩ : syracuseStep 9802529 = 7351897) B7351897
theorem B6535019 : Blo 2293435 6535019 := bstep (se 1 (by rfl) ⟨4901264, by rfl⟩ : syracuseStep 6535019 = 9802529) B9802529
theorem B4356679 : Blo 2293435 4356679 := bstep (se 1 (by rfl) ⟨3267509, by rfl⟩ : syracuseStep 4356679 = 6535019) B6535019
theorem B5808905 : Blo 2293435 5808905 := bstep (se 2 (by rfl) ⟨2178339, by rfl⟩ : syracuseStep 5808905 = 4356679) B4356679
theorem B3872603 : Blo 2293435 3872603 := bstep (se 1 (by rfl) ⟨2904452, by rfl⟩ : syracuseStep 3872603 = 5808905) B5808905
theorem B2581735 : Blo 2293435 2581735 := bstep (se 1 (by rfl) ⟨1936301, by rfl⟩ : syracuseStep 2581735 = 3872603) B3872603
theorem B3442313 : Blo 2293435 3442313 := bstep (se 2 (by rfl) ⟨1290867, by rfl⟩ : syracuseStep 3442313 = 2581735) B2581735
theorem B2294875 : Blo 2293435 2294875 := bstep (se 1 (by rfl) ⟨1721156, by rfl⟩ : syracuseStep 2294875 = 3442313) B3442313
theorem B11617829 : Blo 2293435 11617829 := bbase (se 4 (by rfl) ⟨1089171, by rfl⟩ : syracuseStep 11617829 = 2178343) (by norm_num)
theorem B7745219 : Blo 2293435 7745219 := bstep (se 1 (by rfl) ⟨5808914, by rfl⟩ : syracuseStep 7745219 = 11617829) B11617829
theorem B5163479 : Blo 2293435 5163479 := bstep (se 1 (by rfl) ⟨3872609, by rfl⟩ : syracuseStep 5163479 = 7745219) B7745219
theorem B3442319 : Blo 2293435 3442319 := bstep (se 1 (by rfl) ⟨2581739, by rfl⟩ : syracuseStep 3442319 = 5163479) B5163479
theorem B2294879 : Blo 2293435 2294879 := bstep (se 1 (by rfl) ⟨1721159, by rfl⟩ : syracuseStep 2294879 = 3442319) B3442319
theorem B3442325 : Blo 2293435 3442325 := bbase (se 6 (by rfl) ⟨80679, by rfl⟩ : syracuseStep 3442325 = 161359) (by norm_num)
theorem B2294883 : Blo 2293435 2294883 := bstep (se 1 (by rfl) ⟨1721162, by rfl⟩ : syracuseStep 2294883 = 3442325) B3442325
theorem B10467893 : Blo 2293435 10467893 := bbase (se 5 (by rfl) ⟨490682, by rfl⟩ : syracuseStep 10467893 = 981365) (by norm_num)
theorem B27914381 : Blo 2293435 27914381 := bstep (se 3 (by rfl) ⟨5233946, by rfl⟩ : syracuseStep 27914381 = 10467893) B10467893
theorem B18609587 : Blo 2293435 18609587 := bstep (se 1 (by rfl) ⟨13957190, by rfl⟩ : syracuseStep 18609587 = 27914381) B27914381
theorem B12406391 : Blo 2293435 12406391 := bstep (se 1 (by rfl) ⟨9304793, by rfl⟩ : syracuseStep 12406391 = 18609587) B18609587
theorem B8270927 : Blo 2293435 8270927 := bstep (se 1 (by rfl) ⟨6203195, by rfl⟩ : syracuseStep 8270927 = 12406391) B12406391
theorem B5513951 : Blo 2293435 5513951 := bstep (se 1 (by rfl) ⟨4135463, by rfl⟩ : syracuseStep 5513951 = 8270927) B8270927
theorem B14703869 : Blo 2293435 14703869 := bstep (se 3 (by rfl) ⟨2756975, by rfl⟩ : syracuseStep 14703869 = 5513951) B5513951
theorem B9802579 : Blo 2293435 9802579 := bstep (se 1 (by rfl) ⟨7351934, by rfl⟩ : syracuseStep 9802579 = 14703869) B14703869
theorem B13070105 : Blo 2293435 13070105 := bstep (se 2 (by rfl) ⟨4901289, by rfl⟩ : syracuseStep 13070105 = 9802579) B9802579
theorem B8713403 : Blo 2293435 8713403 := bstep (se 1 (by rfl) ⟨6535052, by rfl⟩ : syracuseStep 8713403 = 13070105) B13070105
theorem B5808935 : Blo 2293435 5808935 := bstep (se 1 (by rfl) ⟨4356701, by rfl⟩ : syracuseStep 5808935 = 8713403) B8713403
theorem B3872623 : Blo 2293435 3872623 := bstep (se 1 (by rfl) ⟨2904467, by rfl⟩ : syracuseStep 3872623 = 5808935) B5808935
theorem B5163497 : Blo 2293435 5163497 := bstep (se 2 (by rfl) ⟨1936311, by rfl⟩ : syracuseStep 5163497 = 3872623) B3872623
theorem B3442331 : Blo 2293435 3442331 := bstep (se 1 (by rfl) ⟨2581748, by rfl⟩ : syracuseStep 3442331 = 5163497) B5163497
theorem B2294887 : Blo 2293435 2294887 := bstep (se 1 (by rfl) ⟨1721165, by rfl⟩ : syracuseStep 2294887 = 3442331) B3442331
theorem B2581753 : Blo 2293435 2581753 := bbase (se 2 (by rfl) ⟨968157, by rfl⟩ : syracuseStep 2581753 = 1936315) (by norm_num)
theorem B3442337 : Blo 2293435 3442337 := bstep (se 2 (by rfl) ⟨1290876, by rfl⟩ : syracuseStep 3442337 = 2581753) B2581753
theorem B2294891 : Blo 2293435 2294891 := bstep (se 1 (by rfl) ⟨1721168, by rfl⟩ : syracuseStep 2294891 = 3442337) B3442337
theorem B9802613 : Blo 2293435 9802613 := bbase (se 5 (by rfl) ⟨459497, by rfl⟩ : syracuseStep 9802613 = 918995) (by norm_num)
theorem B6535075 : Blo 2293435 6535075 := bstep (se 1 (by rfl) ⟨4901306, by rfl⟩ : syracuseStep 6535075 = 9802613) B9802613
theorem B8713433 : Blo 2293435 8713433 := bstep (se 2 (by rfl) ⟨3267537, by rfl⟩ : syracuseStep 8713433 = 6535075) B6535075
theorem B5808955 : Blo 2293435 5808955 := bstep (se 1 (by rfl) ⟨4356716, by rfl⟩ : syracuseStep 5808955 = 8713433) B8713433
theorem B7745273 : Blo 2293435 7745273 := bstep (se 2 (by rfl) ⟨2904477, by rfl⟩ : syracuseStep 7745273 = 5808955) B5808955
theorem B5163515 : Blo 2293435 5163515 := bstep (se 1 (by rfl) ⟨3872636, by rfl⟩ : syracuseStep 5163515 = 7745273) B7745273
theorem B3442343 : Blo 2293435 3442343 := bstep (se 1 (by rfl) ⟨2581757, by rfl⟩ : syracuseStep 3442343 = 5163515) B5163515
theorem B2294895 : Blo 2293435 2294895 := bstep (se 1 (by rfl) ⟨1721171, by rfl⟩ : syracuseStep 2294895 = 3442343) B3442343
theorem B3442349 : Blo 2293435 3442349 := bbase (se 3 (by rfl) ⟨645440, by rfl⟩ : syracuseStep 3442349 = 1290881) (by norm_num)
theorem B2294899 : Blo 2293435 2294899 := bstep (se 1 (by rfl) ⟨1721174, by rfl⟩ : syracuseStep 2294899 = 3442349) B3442349
theorem B5163533 : Blo 2293435 5163533 := bbase (se 3 (by rfl) ⟨968162, by rfl⟩ : syracuseStep 5163533 = 1936325) (by norm_num)
theorem B3442355 : Blo 2293435 3442355 := bstep (se 1 (by rfl) ⟨2581766, by rfl⟩ : syracuseStep 3442355 = 5163533) B5163533
theorem B2294903 : Blo 2293435 2294903 := bstep (se 1 (by rfl) ⟨1721177, by rfl⟩ : syracuseStep 2294903 = 3442355) B3442355
theorem B2904493 : Blo 2293435 2904493 := bbase (se 3 (by rfl) ⟨544592, by rfl⟩ : syracuseStep 2904493 = 1089185) (by norm_num)
theorem B3872657 : Blo 2293435 3872657 := bstep (se 2 (by rfl) ⟨1452246, by rfl⟩ : syracuseStep 3872657 = 2904493) B2904493
theorem B2581771 : Blo 2293435 2581771 := bstep (se 1 (by rfl) ⟨1936328, by rfl⟩ : syracuseStep 2581771 = 3872657) B3872657
theorem B3442361 : Blo 2293435 3442361 := bstep (se 2 (by rfl) ⟨1290885, by rfl⟩ : syracuseStep 3442361 = 2581771) B2581771
theorem B2294907 : Blo 2293435 2294907 := bstep (se 1 (by rfl) ⟨1721180, by rfl⟩ : syracuseStep 2294907 = 3442361) B3442361
theorem B14704021 : Blo 2293435 14704021 := bbase (se 6 (by rfl) ⟨344625, by rfl⟩ : syracuseStep 14704021 = 689251) (by norm_num)
theorem B19605361 : Blo 2293435 19605361 := bstep (se 2 (by rfl) ⟨7352010, by rfl⟩ : syracuseStep 19605361 = 14704021) B14704021
theorem B26140481 : Blo 2293435 26140481 := bstep (se 2 (by rfl) ⟨9802680, by rfl⟩ : syracuseStep 26140481 = 19605361) B19605361
theorem B17426987 : Blo 2293435 17426987 := bstep (se 1 (by rfl) ⟨13070240, by rfl⟩ : syracuseStep 17426987 = 26140481) B26140481
theorem B11617991 : Blo 2293435 11617991 := bstep (se 1 (by rfl) ⟨8713493, by rfl⟩ : syracuseStep 11617991 = 17426987) B17426987
theorem B7745327 : Blo 2293435 7745327 := bstep (se 1 (by rfl) ⟨5808995, by rfl⟩ : syracuseStep 7745327 = 11617991) B11617991
theorem B5163551 : Blo 2293435 5163551 := bstep (se 1 (by rfl) ⟨3872663, by rfl⟩ : syracuseStep 5163551 = 7745327) B7745327
theorem B3442367 : Blo 2293435 3442367 := bstep (se 1 (by rfl) ⟨2581775, by rfl⟩ : syracuseStep 3442367 = 5163551) B5163551
theorem B2294911 : Blo 2293435 2294911 := bstep (se 1 (by rfl) ⟨1721183, by rfl⟩ : syracuseStep 2294911 = 3442367) B3442367
theorem B3442373 : Blo 2293435 3442373 := bbase (se 4 (by rfl) ⟨322722, by rfl⟩ : syracuseStep 3442373 = 645445) (by norm_num)
theorem B2294915 : Blo 2293435 2294915 := bstep (se 1 (by rfl) ⟨1721186, by rfl⟩ : syracuseStep 2294915 = 3442373) B3442373
theorem B3872677 : Blo 2293435 3872677 := bbase (se 4 (by rfl) ⟨363063, by rfl⟩ : syracuseStep 3872677 = 726127) (by norm_num)
theorem B5163569 : Blo 2293435 5163569 := bstep (se 2 (by rfl) ⟨1936338, by rfl⟩ : syracuseStep 5163569 = 3872677) B3872677
theorem B3442379 : Blo 2293435 3442379 := bstep (se 1 (by rfl) ⟨2581784, by rfl⟩ : syracuseStep 3442379 = 5163569) B5163569
theorem B2294919 : Blo 2293435 2294919 := bstep (se 1 (by rfl) ⟨1721189, by rfl⟩ : syracuseStep 2294919 = 3442379) B3442379
theorem B2581789 : Blo 2293435 2581789 := bbase (se 3 (by rfl) ⟨484085, by rfl⟩ : syracuseStep 2581789 = 968171) (by norm_num)
theorem B3442385 : Blo 2293435 3442385 := bstep (se 2 (by rfl) ⟨1290894, by rfl⟩ : syracuseStep 3442385 = 2581789) B2581789
theorem B2294923 : Blo 2293435 2294923 := bstep (se 1 (by rfl) ⟨1721192, by rfl⟩ : syracuseStep 2294923 = 3442385) B3442385
theorem B7745381 : Blo 2293435 7745381 := bbase (se 4 (by rfl) ⟨726129, by rfl⟩ : syracuseStep 7745381 = 1452259) (by norm_num)
theorem B5163587 : Blo 2293435 5163587 := bstep (se 1 (by rfl) ⟨3872690, by rfl⟩ : syracuseStep 5163587 = 7745381) B7745381
theorem B3442391 : Blo 2293435 3442391 := bstep (se 1 (by rfl) ⟨2581793, by rfl⟩ : syracuseStep 3442391 = 5163587) B5163587
theorem B2294927 : Blo 2293435 2294927 := bstep (se 1 (by rfl) ⟨1721195, by rfl⟩ : syracuseStep 2294927 = 3442391) B3442391
theorem B3442397 : Blo 2293435 3442397 := bbase (se 3 (by rfl) ⟨645449, by rfl⟩ : syracuseStep 3442397 = 1290899) (by norm_num)
theorem B2294931 : Blo 2293435 2294931 := bstep (se 1 (by rfl) ⟨1721198, by rfl⟩ : syracuseStep 2294931 = 3442397) B3442397
theorem B5163605 : Blo 2293435 5163605 := bbase (se 8 (by rfl) ⟨30255, by rfl⟩ : syracuseStep 5163605 = 60511) (by norm_num)
theorem B3442403 : Blo 2293435 3442403 := bstep (se 1 (by rfl) ⟨2581802, by rfl⟩ : syracuseStep 3442403 = 5163605) B5163605
theorem B2294935 : Blo 2293435 2294935 := bstep (se 1 (by rfl) ⟨1721201, by rfl⟩ : syracuseStep 2294935 = 3442403) B3442403
theorem B5514077 : Blo 2293435 5514077 := bbase (se 3 (by rfl) ⟨1033889, by rfl⟩ : syracuseStep 5514077 = 2067779) (by norm_num)
theorem B3676051 : Blo 2293435 3676051 := bstep (se 1 (by rfl) ⟨2757038, by rfl⟩ : syracuseStep 3676051 = 5514077) B5514077
theorem B4901401 : Blo 2293435 4901401 := bstep (se 2 (by rfl) ⟨1838025, by rfl⟩ : syracuseStep 4901401 = 3676051) B3676051
theorem B6535201 : Blo 2293435 6535201 := bstep (se 2 (by rfl) ⟨2450700, by rfl⟩ : syracuseStep 6535201 = 4901401) B4901401
theorem B8713601 : Blo 2293435 8713601 := bstep (se 2 (by rfl) ⟨3267600, by rfl⟩ : syracuseStep 8713601 = 6535201) B6535201
theorem B5809067 : Blo 2293435 5809067 := bstep (se 1 (by rfl) ⟨4356800, by rfl⟩ : syracuseStep 5809067 = 8713601) B8713601
theorem B3872711 : Blo 2293435 3872711 := bstep (se 1 (by rfl) ⟨2904533, by rfl⟩ : syracuseStep 3872711 = 5809067) B5809067
theorem B2581807 : Blo 2293435 2581807 := bstep (se 1 (by rfl) ⟨1936355, by rfl⟩ : syracuseStep 2581807 = 3872711) B3872711
theorem B3442409 : Blo 2293435 3442409 := bstep (se 2 (by rfl) ⟨1290903, by rfl⟩ : syracuseStep 3442409 = 2581807) B2581807
theorem B2294939 : Blo 2293435 2294939 := bstep (se 1 (by rfl) ⟨1721204, by rfl⟩ : syracuseStep 2294939 = 3442409) B3442409
theorem B5514085 : Blo 2293435 5514085 := bbase (se 4 (by rfl) ⟨516945, by rfl⟩ : syracuseStep 5514085 = 1033891) (by norm_num)
theorem B29408453 : Blo 2293435 29408453 := bstep (se 4 (by rfl) ⟨2757042, by rfl⟩ : syracuseStep 29408453 = 5514085) B5514085
theorem B19605635 : Blo 2293435 19605635 := bstep (se 1 (by rfl) ⟨14704226, by rfl⟩ : syracuseStep 19605635 = 29408453) B29408453
theorem B13070423 : Blo 2293435 13070423 := bstep (se 1 (by rfl) ⟨9802817, by rfl⟩ : syracuseStep 13070423 = 19605635) B19605635
theorem B8713615 : Blo 2293435 8713615 := bstep (se 1 (by rfl) ⟨6535211, by rfl⟩ : syracuseStep 8713615 = 13070423) B13070423
theorem B11618153 : Blo 2293435 11618153 := bstep (se 2 (by rfl) ⟨4356807, by rfl⟩ : syracuseStep 11618153 = 8713615) B8713615
theorem B7745435 : Blo 2293435 7745435 := bstep (se 1 (by rfl) ⟨5809076, by rfl⟩ : syracuseStep 7745435 = 11618153) B11618153
theorem B5163623 : Blo 2293435 5163623 := bstep (se 1 (by rfl) ⟨3872717, by rfl⟩ : syracuseStep 5163623 = 7745435) B7745435
theorem B3442415 : Blo 2293435 3442415 := bstep (se 1 (by rfl) ⟨2581811, by rfl⟩ : syracuseStep 3442415 = 5163623) B5163623
theorem B2294943 : Blo 2293435 2294943 := bstep (se 1 (by rfl) ⟨1721207, by rfl⟩ : syracuseStep 2294943 = 3442415) B3442415
theorem B3442421 : Blo 2293435 3442421 := bbase (se 5 (by rfl) ⟨161363, by rfl⟩ : syracuseStep 3442421 = 322727) (by norm_num)
theorem B2294947 : Blo 2293435 2294947 := bstep (se 1 (by rfl) ⟨1721210, by rfl⟩ : syracuseStep 2294947 = 3442421) B3442421
theorem B9802853 : Blo 2293435 9802853 := bbase (se 4 (by rfl) ⟨919017, by rfl⟩ : syracuseStep 9802853 = 1838035) (by norm_num)
theorem B6535235 : Blo 2293435 6535235 := bstep (se 1 (by rfl) ⟨4901426, by rfl⟩ : syracuseStep 6535235 = 9802853) B9802853
theorem B4356823 : Blo 2293435 4356823 := bstep (se 1 (by rfl) ⟨3267617, by rfl⟩ : syracuseStep 4356823 = 6535235) B6535235
theorem B5809097 : Blo 2293435 5809097 := bstep (se 2 (by rfl) ⟨2178411, by rfl⟩ : syracuseStep 5809097 = 4356823) B4356823
theorem B3872731 : Blo 2293435 3872731 := bstep (se 1 (by rfl) ⟨2904548, by rfl⟩ : syracuseStep 3872731 = 5809097) B5809097
theorem B5163641 : Blo 2293435 5163641 := bstep (se 2 (by rfl) ⟨1936365, by rfl⟩ : syracuseStep 5163641 = 3872731) B3872731
theorem B3442427 : Blo 2293435 3442427 := bstep (se 1 (by rfl) ⟨2581820, by rfl⟩ : syracuseStep 3442427 = 5163641) B5163641
theorem B2294951 : Blo 2293435 2294951 := bstep (se 1 (by rfl) ⟨1721213, by rfl⟩ : syracuseStep 2294951 = 3442427) B3442427
theorem B2581825 : Blo 2293435 2581825 := bbase (se 2 (by rfl) ⟨968184, by rfl⟩ : syracuseStep 2581825 = 1936369) (by norm_num)
theorem B3442433 : Blo 2293435 3442433 := bstep (se 2 (by rfl) ⟨1290912, by rfl⟩ : syracuseStep 3442433 = 2581825) B2581825
theorem B2294955 : Blo 2293435 2294955 := bstep (se 1 (by rfl) ⟨1721216, by rfl⟩ : syracuseStep 2294955 = 3442433) B3442433
theorem B5809117 : Blo 2293435 5809117 := bbase (se 3 (by rfl) ⟨1089209, by rfl⟩ : syracuseStep 5809117 = 2178419) (by norm_num)
theorem B7745489 : Blo 2293435 7745489 := bstep (se 2 (by rfl) ⟨2904558, by rfl⟩ : syracuseStep 7745489 = 5809117) B5809117
theorem B5163659 : Blo 2293435 5163659 := bstep (se 1 (by rfl) ⟨3872744, by rfl⟩ : syracuseStep 5163659 = 7745489) B7745489
theorem B3442439 : Blo 2293435 3442439 := bstep (se 1 (by rfl) ⟨2581829, by rfl⟩ : syracuseStep 3442439 = 5163659) B5163659
theorem B2294959 : Blo 2293435 2294959 := bstep (se 1 (by rfl) ⟨1721219, by rfl⟩ : syracuseStep 2294959 = 3442439) B3442439
theorem B3442445 : Blo 2293435 3442445 := bbase (se 3 (by rfl) ⟨645458, by rfl⟩ : syracuseStep 3442445 = 1290917) (by norm_num)
theorem B2294963 : Blo 2293435 2294963 := bstep (se 1 (by rfl) ⟨1721222, by rfl⟩ : syracuseStep 2294963 = 3442445) B3442445
theorem B5163677 : Blo 2293435 5163677 := bbase (se 3 (by rfl) ⟨968189, by rfl⟩ : syracuseStep 5163677 = 1936379) (by norm_num)
theorem B3442451 : Blo 2293435 3442451 := bstep (se 1 (by rfl) ⟨2581838, by rfl⟩ : syracuseStep 3442451 = 5163677) B5163677
theorem B2294967 : Blo 2293435 2294967 := bstep (se 1 (by rfl) ⟨1721225, by rfl⟩ : syracuseStep 2294967 = 3442451) B3442451
theorem B3872765 : Blo 2293435 3872765 := bbase (se 3 (by rfl) ⟨726143, by rfl⟩ : syracuseStep 3872765 = 1452287) (by norm_num)
theorem B2581843 : Blo 2293435 2581843 := bstep (se 1 (by rfl) ⟨1936382, by rfl⟩ : syracuseStep 2581843 = 3872765) B3872765
theorem B3442457 : Blo 2293435 3442457 := bstep (se 2 (by rfl) ⟨1290921, by rfl⟩ : syracuseStep 3442457 = 2581843) B2581843
theorem B2294971 : Blo 2293435 2294971 := bstep (se 1 (by rfl) ⟨1721228, by rfl⟩ : syracuseStep 2294971 = 3442457) B3442457
theorem B4901477 : Blo 2293435 4901477 := bbase (se 4 (by rfl) ⟨459513, by rfl⟩ : syracuseStep 4901477 = 919027) (by norm_num)
theorem B13070605 : Blo 2293435 13070605 := bstep (se 3 (by rfl) ⟨2450738, by rfl⟩ : syracuseStep 13070605 = 4901477) B4901477
theorem B17427473 : Blo 2293435 17427473 := bstep (se 2 (by rfl) ⟨6535302, by rfl⟩ : syracuseStep 17427473 = 13070605) B13070605
theorem B11618315 : Blo 2293435 11618315 := bstep (se 1 (by rfl) ⟨8713736, by rfl⟩ : syracuseStep 11618315 = 17427473) B17427473
theorem B7745543 : Blo 2293435 7745543 := bstep (se 1 (by rfl) ⟨5809157, by rfl⟩ : syracuseStep 7745543 = 11618315) B11618315
theorem B5163695 : Blo 2293435 5163695 := bstep (se 1 (by rfl) ⟨3872771, by rfl⟩ : syracuseStep 5163695 = 7745543) B7745543
theorem B3442463 : Blo 2293435 3442463 := bstep (se 1 (by rfl) ⟨2581847, by rfl⟩ : syracuseStep 3442463 = 5163695) B5163695
theorem B2294975 : Blo 2293435 2294975 := bstep (se 1 (by rfl) ⟨1721231, by rfl⟩ : syracuseStep 2294975 = 3442463) B3442463
theorem B3442469 : Blo 2293435 3442469 := bbase (se 4 (by rfl) ⟨322731, by rfl⟩ : syracuseStep 3442469 = 645463) (by norm_num)
theorem B2294979 : Blo 2293435 2294979 := bstep (se 1 (by rfl) ⟨1721234, by rfl⟩ : syracuseStep 2294979 = 3442469) B3442469
theorem B2904589 : Blo 2293435 2904589 := bbase (se 3 (by rfl) ⟨544610, by rfl⟩ : syracuseStep 2904589 = 1089221) (by norm_num)
theorem B3872785 : Blo 2293435 3872785 := bstep (se 2 (by rfl) ⟨1452294, by rfl⟩ : syracuseStep 3872785 = 2904589) B2904589
theorem B5163713 : Blo 2293435 5163713 := bstep (se 2 (by rfl) ⟨1936392, by rfl⟩ : syracuseStep 5163713 = 3872785) B3872785
theorem B3442475 : Blo 2293435 3442475 := bstep (se 1 (by rfl) ⟨2581856, by rfl⟩ : syracuseStep 3442475 = 5163713) B5163713
theorem B2294983 : Blo 2293435 2294983 := bstep (se 1 (by rfl) ⟨1721237, by rfl⟩ : syracuseStep 2294983 = 3442475) B3442475
theorem B2581861 : Blo 2293435 2581861 := bbase (se 4 (by rfl) ⟨242049, by rfl⟩ : syracuseStep 2581861 = 484099) (by norm_num)
theorem B3442481 : Blo 2293435 3442481 := bstep (se 2 (by rfl) ⟨1290930, by rfl⟩ : syracuseStep 3442481 = 2581861) B2581861
theorem B2294987 : Blo 2293435 2294987 := bstep (se 1 (by rfl) ⟨1721240, by rfl⟩ : syracuseStep 2294987 = 3442481) B3442481
theorem B6535349 : Blo 2293435 6535349 := bbase (se 5 (by rfl) ⟨306344, by rfl⟩ : syracuseStep 6535349 = 612689) (by norm_num)
theorem B4356899 : Blo 2293435 4356899 := bstep (se 1 (by rfl) ⟨3267674, by rfl⟩ : syracuseStep 4356899 = 6535349) B6535349
theorem B2904599 : Blo 2293435 2904599 := bstep (se 1 (by rfl) ⟨2178449, by rfl⟩ : syracuseStep 2904599 = 4356899) B4356899
theorem B7745597 : Blo 2293435 7745597 := bstep (se 3 (by rfl) ⟨1452299, by rfl⟩ : syracuseStep 7745597 = 2904599) B2904599
theorem B5163731 : Blo 2293435 5163731 := bstep (se 1 (by rfl) ⟨3872798, by rfl⟩ : syracuseStep 5163731 = 7745597) B7745597
theorem B3442487 : Blo 2293435 3442487 := bstep (se 1 (by rfl) ⟨2581865, by rfl⟩ : syracuseStep 3442487 = 5163731) B5163731
theorem B2294991 : Blo 2293435 2294991 := bstep (se 1 (by rfl) ⟨1721243, by rfl⟩ : syracuseStep 2294991 = 3442487) B3442487
theorem B3442493 : Blo 2293435 3442493 := bbase (se 3 (by rfl) ⟨645467, by rfl⟩ : syracuseStep 3442493 = 1290935) (by norm_num)
theorem B2294995 : Blo 2293435 2294995 := bstep (se 1 (by rfl) ⟨1721246, by rfl⟩ : syracuseStep 2294995 = 3442493) B3442493
theorem B5163749 : Blo 2293435 5163749 := bbase (se 4 (by rfl) ⟨484101, by rfl⟩ : syracuseStep 5163749 = 968203) (by norm_num)
theorem B3442499 : Blo 2293435 3442499 := bstep (se 1 (by rfl) ⟨2581874, by rfl⟩ : syracuseStep 3442499 = 5163749) B5163749
theorem B2294999 : Blo 2293435 2294999 := bstep (se 1 (by rfl) ⟨1721249, by rfl⟩ : syracuseStep 2294999 = 3442499) B3442499
theorem B5809229 : Blo 2293435 5809229 := bbase (se 3 (by rfl) ⟨1089230, by rfl⟩ : syracuseStep 5809229 = 2178461) (by norm_num)
theorem B3872819 : Blo 2293435 3872819 := bstep (se 1 (by rfl) ⟨2904614, by rfl⟩ : syracuseStep 3872819 = 5809229) B5809229
theorem B2581879 : Blo 2293435 2581879 := bstep (se 1 (by rfl) ⟨1936409, by rfl⟩ : syracuseStep 2581879 = 3872819) B3872819
theorem B3442505 : Blo 2293435 3442505 := bstep (se 2 (by rfl) ⟨1290939, by rfl⟩ : syracuseStep 3442505 = 2581879) B2581879
theorem B2295003 : Blo 2293435 2295003 := bstep (se 1 (by rfl) ⟨1721252, by rfl⟩ : syracuseStep 2295003 = 3442505) B3442505
theorem B2450773 : Blo 2293435 2450773 := bbase (se 12 (by rfl) ⟨897, by rfl⟩ : syracuseStep 2450773 = 1795) (by norm_num)
theorem B3267697 : Blo 2293435 3267697 := bstep (se 2 (by rfl) ⟨1225386, by rfl⟩ : syracuseStep 3267697 = 2450773) B2450773
theorem B4356929 : Blo 2293435 4356929 := bstep (se 2 (by rfl) ⟨1633848, by rfl⟩ : syracuseStep 4356929 = 3267697) B3267697
theorem B11618477 : Blo 2293435 11618477 := bstep (se 3 (by rfl) ⟨2178464, by rfl⟩ : syracuseStep 11618477 = 4356929) B4356929
theorem B7745651 : Blo 2293435 7745651 := bstep (se 1 (by rfl) ⟨5809238, by rfl⟩ : syracuseStep 7745651 = 11618477) B11618477
theorem B5163767 : Blo 2293435 5163767 := bstep (se 1 (by rfl) ⟨3872825, by rfl⟩ : syracuseStep 5163767 = 7745651) B7745651
theorem B3442511 : Blo 2293435 3442511 := bstep (se 1 (by rfl) ⟨2581883, by rfl⟩ : syracuseStep 3442511 = 5163767) B5163767
theorem B2295007 : Blo 2293435 2295007 := bstep (se 1 (by rfl) ⟨1721255, by rfl⟩ : syracuseStep 2295007 = 3442511) B3442511
theorem B3442517 : Blo 2293435 3442517 := bbase (se 9 (by rfl) ⟨10085, by rfl⟩ : syracuseStep 3442517 = 20171) (by norm_num)
theorem B2295011 : Blo 2293435 2295011 := bstep (se 1 (by rfl) ⟨1721258, by rfl⟩ : syracuseStep 2295011 = 3442517) B3442517
theorem B3489493 : Blo 2293435 3489493 := bbase (se 7 (by rfl) ⟨40892, by rfl⟩ : syracuseStep 3489493 = 81785) (by norm_num)
theorem B4652657 : Blo 2293435 4652657 := bstep (se 2 (by rfl) ⟨1744746, by rfl⟩ : syracuseStep 4652657 = 3489493) B3489493
theorem B3101771 : Blo 2293435 3101771 := bstep (se 1 (by rfl) ⟨2326328, by rfl⟩ : syracuseStep 3101771 = 4652657) B4652657
theorem B8271389 : Blo 2293435 8271389 := bstep (se 3 (by rfl) ⟨1550885, by rfl⟩ : syracuseStep 8271389 = 3101771) B3101771
theorem B5514259 : Blo 2293435 5514259 := bstep (se 1 (by rfl) ⟨4135694, by rfl⟩ : syracuseStep 5514259 = 8271389) B8271389
theorem B7352345 : Blo 2293435 7352345 := bstep (se 2 (by rfl) ⟨2757129, by rfl⟩ : syracuseStep 7352345 = 5514259) B5514259
theorem B4901563 : Blo 2293435 4901563 := bstep (se 1 (by rfl) ⟨3676172, by rfl⟩ : syracuseStep 4901563 = 7352345) B7352345
theorem B6535417 : Blo 2293435 6535417 := bstep (se 2 (by rfl) ⟨2450781, by rfl⟩ : syracuseStep 6535417 = 4901563) B4901563
theorem B8713889 : Blo 2293435 8713889 := bstep (se 2 (by rfl) ⟨3267708, by rfl⟩ : syracuseStep 8713889 = 6535417) B6535417
theorem B5809259 : Blo 2293435 5809259 := bstep (se 1 (by rfl) ⟨4356944, by rfl⟩ : syracuseStep 5809259 = 8713889) B8713889
theorem B3872839 : Blo 2293435 3872839 := bstep (se 1 (by rfl) ⟨2904629, by rfl⟩ : syracuseStep 3872839 = 5809259) B5809259
theorem B5163785 : Blo 2293435 5163785 := bstep (se 2 (by rfl) ⟨1936419, by rfl⟩ : syracuseStep 5163785 = 3872839) B3872839
theorem B3442523 : Blo 2293435 3442523 := bstep (se 1 (by rfl) ⟨2581892, by rfl⟩ : syracuseStep 3442523 = 5163785) B5163785
theorem B2295015 : Blo 2293435 2295015 := bstep (se 1 (by rfl) ⟨1721261, by rfl⟩ : syracuseStep 2295015 = 3442523) B3442523
theorem B2581897 : Blo 2293435 2581897 := bbase (se 2 (by rfl) ⟨968211, by rfl⟩ : syracuseStep 2581897 = 1936423) (by norm_num)
theorem B3442529 : Blo 2293435 3442529 := bstep (se 2 (by rfl) ⟨1290948, by rfl⟩ : syracuseStep 3442529 = 2581897) B2581897
theorem B2295019 : Blo 2293435 2295019 := bstep (se 1 (by rfl) ⟨1721264, by rfl⟩ : syracuseStep 2295019 = 3442529) B3442529
theorem B3403301 : Blo 2293435 3403301 := bbase (se 4 (by rfl) ⟨319059, by rfl⟩ : syracuseStep 3403301 = 638119) (by norm_num)
theorem B9075469 : Blo 2293435 9075469 := bstep (se 3 (by rfl) ⟨1701650, by rfl⟩ : syracuseStep 9075469 = 3403301) B3403301
theorem B12100625 : Blo 2293435 12100625 := bstep (se 2 (by rfl) ⟨4537734, by rfl⟩ : syracuseStep 12100625 = 9075469) B9075469
theorem B8067083 : Blo 2293435 8067083 := bstep (se 1 (by rfl) ⟨6050312, by rfl⟩ : syracuseStep 8067083 = 12100625) B12100625
theorem B86048885 : Blo 2293435 86048885 := bstep (se 5 (by rfl) ⟨4033541, by rfl⟩ : syracuseStep 86048885 = 8067083) B8067083
theorem B57365923 : Blo 2293435 57365923 := bstep (se 1 (by rfl) ⟨43024442, by rfl⟩ : syracuseStep 57365923 = 86048885) B86048885
theorem B76487897 : Blo 2293435 76487897 := bstep (se 2 (by rfl) ⟨28682961, by rfl⟩ : syracuseStep 76487897 = 57365923) B57365923
theorem B50991931 : Blo 2293435 50991931 := bstep (se 1 (by rfl) ⟨38243948, by rfl⟩ : syracuseStep 50991931 = 76487897) B76487897
theorem B67989241 : Blo 2293435 67989241 := bstep (se 2 (by rfl) ⟨25495965, by rfl⟩ : syracuseStep 67989241 = 50991931) B50991931
theorem B90652321 : Blo 2293435 90652321 := bstep (se 2 (by rfl) ⟨33994620, by rfl⟩ : syracuseStep 90652321 = 67989241) B67989241
theorem B120869761 : Blo 2293435 120869761 := bstep (se 2 (by rfl) ⟨45326160, by rfl⟩ : syracuseStep 120869761 = 90652321) B90652321
theorem B161159681 : Blo 2293435 161159681 := bstep (se 2 (by rfl) ⟨60434880, by rfl⟩ : syracuseStep 161159681 = 120869761) B120869761
theorem B107439787 : Blo 2293435 107439787 := bstep (se 1 (by rfl) ⟨80579840, by rfl⟩ : syracuseStep 107439787 = 161159681) B161159681
theorem B143253049 : Blo 2293435 143253049 := bstep (se 2 (by rfl) ⟨53719893, by rfl⟩ : syracuseStep 143253049 = 107439787) B107439787
theorem B191004065 : Blo 2293435 191004065 := bstep (se 2 (by rfl) ⟨71626524, by rfl⟩ : syracuseStep 191004065 = 143253049) B143253049
theorem B127336043 : Blo 2293435 127336043 := bstep (se 1 (by rfl) ⟨95502032, by rfl⟩ : syracuseStep 127336043 = 191004065) B191004065
theorem B84890695 : Blo 2293435 84890695 := bstep (se 1 (by rfl) ⟨63668021, by rfl⟩ : syracuseStep 84890695 = 127336043) B127336043
theorem B113187593 : Blo 2293435 113187593 := bstep (se 2 (by rfl) ⟨42445347, by rfl⟩ : syracuseStep 113187593 = 84890695) B84890695
theorem B75458395 : Blo 2293435 75458395 := bstep (se 1 (by rfl) ⟨56593796, by rfl⟩ : syracuseStep 75458395 = 113187593) B113187593
theorem B100611193 : Blo 2293435 100611193 := bstep (se 2 (by rfl) ⟨37729197, by rfl⟩ : syracuseStep 100611193 = 75458395) B75458395
theorem B134148257 : Blo 2293435 134148257 := bstep (se 2 (by rfl) ⟨50305596, by rfl⟩ : syracuseStep 134148257 = 100611193) B100611193
theorem B89432171 : Blo 2293435 89432171 := bstep (se 1 (by rfl) ⟨67074128, by rfl⟩ : syracuseStep 89432171 = 134148257) B134148257
theorem B59621447 : Blo 2293435 59621447 := bstep (se 1 (by rfl) ⟨44716085, by rfl⟩ : syracuseStep 59621447 = 89432171) B89432171
theorem B158990525 : Blo 2293435 158990525 := bstep (se 3 (by rfl) ⟨29810723, by rfl⟩ : syracuseStep 158990525 = 59621447) B59621447
theorem B105993683 : Blo 2293435 105993683 := bstep (se 1 (by rfl) ⟨79495262, by rfl⟩ : syracuseStep 105993683 = 158990525) B158990525
theorem B70662455 : Blo 2293435 70662455 := bstep (se 1 (by rfl) ⟨52996841, by rfl⟩ : syracuseStep 70662455 = 105993683) B105993683
theorem B47108303 : Blo 2293435 47108303 := bstep (se 1 (by rfl) ⟨35331227, by rfl⟩ : syracuseStep 47108303 = 70662455) B70662455
theorem B31405535 : Blo 2293435 31405535 := bstep (se 1 (by rfl) ⟨23554151, by rfl⟩ : syracuseStep 31405535 = 47108303) B47108303
theorem B20937023 : Blo 2293435 20937023 := bstep (se 1 (by rfl) ⟨15702767, by rfl⟩ : syracuseStep 20937023 = 31405535) B31405535
theorem B13958015 : Blo 2293435 13958015 := bstep (se 1 (by rfl) ⟨10468511, by rfl⟩ : syracuseStep 13958015 = 20937023) B20937023
theorem B37221373 : Blo 2293435 37221373 := bstep (se 3 (by rfl) ⟨6979007, by rfl⟩ : syracuseStep 37221373 = 13958015) B13958015
theorem B49628497 : Blo 2293435 49628497 := bstep (se 2 (by rfl) ⟨18610686, by rfl⟩ : syracuseStep 49628497 = 37221373) B37221373
theorem B66171329 : Blo 2293435 66171329 := bstep (se 2 (by rfl) ⟨24814248, by rfl⟩ : syracuseStep 66171329 = 49628497) B49628497
theorem B44114219 : Blo 2293435 44114219 := bstep (se 1 (by rfl) ⟨33085664, by rfl⟩ : syracuseStep 44114219 = 66171329) B66171329
theorem B29409479 : Blo 2293435 29409479 := bstep (se 1 (by rfl) ⟨22057109, by rfl⟩ : syracuseStep 29409479 = 44114219) B44114219
theorem B19606319 : Blo 2293435 19606319 := bstep (se 1 (by rfl) ⟨14704739, by rfl⟩ : syracuseStep 19606319 = 29409479) B29409479
theorem B13070879 : Blo 2293435 13070879 := bstep (se 1 (by rfl) ⟨9803159, by rfl⟩ : syracuseStep 13070879 = 19606319) B19606319
theorem B8713919 : Blo 2293435 8713919 := bstep (se 1 (by rfl) ⟨6535439, by rfl⟩ : syracuseStep 8713919 = 13070879) B13070879
theorem B5809279 : Blo 2293435 5809279 := bstep (se 1 (by rfl) ⟨4356959, by rfl⟩ : syracuseStep 5809279 = 8713919) B8713919
theorem B7745705 : Blo 2293435 7745705 := bstep (se 2 (by rfl) ⟨2904639, by rfl⟩ : syracuseStep 7745705 = 5809279) B5809279
theorem B5163803 : Blo 2293435 5163803 := bstep (se 1 (by rfl) ⟨3872852, by rfl⟩ : syracuseStep 5163803 = 7745705) B7745705
theorem B3442535 : Blo 2293435 3442535 := bstep (se 1 (by rfl) ⟨2581901, by rfl⟩ : syracuseStep 3442535 = 5163803) B5163803
theorem B2295023 : Blo 2293435 2295023 := bstep (se 1 (by rfl) ⟨1721267, by rfl⟩ : syracuseStep 2295023 = 3442535) B3442535
theorem B3442541 : Blo 2293435 3442541 := bbase (se 3 (by rfl) ⟨645476, by rfl⟩ : syracuseStep 3442541 = 1290953) (by norm_num)
theorem B2295027 : Blo 2293435 2295027 := bstep (se 1 (by rfl) ⟨1721270, by rfl⟩ : syracuseStep 2295027 = 3442541) B3442541
theorem B5163821 : Blo 2293435 5163821 := bbase (se 3 (by rfl) ⟨968216, by rfl⟩ : syracuseStep 5163821 = 1936433) (by norm_num)
theorem B3442547 : Blo 2293435 3442547 := bstep (se 1 (by rfl) ⟨2581910, by rfl⟩ : syracuseStep 3442547 = 5163821) B5163821
theorem B2295031 : Blo 2293435 2295031 := bstep (se 1 (by rfl) ⟨1721273, by rfl⟩ : syracuseStep 2295031 = 3442547) B3442547
theorem B3676205 : Blo 2293435 3676205 := bbase (se 3 (by rfl) ⟨689288, by rfl⟩ : syracuseStep 3676205 = 1378577) (by norm_num)
theorem B9803213 : Blo 2293435 9803213 := bstep (se 3 (by rfl) ⟨1838102, by rfl⟩ : syracuseStep 9803213 = 3676205) B3676205
theorem B6535475 : Blo 2293435 6535475 := bstep (se 1 (by rfl) ⟨4901606, by rfl⟩ : syracuseStep 6535475 = 9803213) B9803213
theorem B4356983 : Blo 2293435 4356983 := bstep (se 1 (by rfl) ⟨3267737, by rfl⟩ : syracuseStep 4356983 = 6535475) B6535475
theorem B2904655 : Blo 2293435 2904655 := bstep (se 1 (by rfl) ⟨2178491, by rfl⟩ : syracuseStep 2904655 = 4356983) B4356983
theorem B3872873 : Blo 2293435 3872873 := bstep (se 2 (by rfl) ⟨1452327, by rfl⟩ : syracuseStep 3872873 = 2904655) B2904655
theorem B2581915 : Blo 2293435 2581915 := bstep (se 1 (by rfl) ⟨1936436, by rfl⟩ : syracuseStep 2581915 = 3872873) B3872873
theorem B3442553 : Blo 2293435 3442553 := bstep (se 2 (by rfl) ⟨1290957, by rfl⟩ : syracuseStep 3442553 = 2581915) B2581915
theorem B2295035 : Blo 2293435 2295035 := bstep (se 1 (by rfl) ⟨1721276, by rfl⟩ : syracuseStep 2295035 = 3442553) B3442553
theorem B24814421 : Blo 2293435 24814421 := bbase (se 9 (by rfl) ⟨72698, by rfl⟩ : syracuseStep 24814421 = 145397) (by norm_num)
theorem B16542947 : Blo 2293435 16542947 := bstep (se 1 (by rfl) ⟨12407210, by rfl⟩ : syracuseStep 16542947 = 24814421) B24814421
theorem B11028631 : Blo 2293435 11028631 := bstep (se 1 (by rfl) ⟨8271473, by rfl⟩ : syracuseStep 11028631 = 16542947) B16542947
theorem B14704841 : Blo 2293435 14704841 := bstep (se 2 (by rfl) ⟨5514315, by rfl⟩ : syracuseStep 14704841 = 11028631) B11028631
theorem B39212909 : Blo 2293435 39212909 := bstep (se 3 (by rfl) ⟨7352420, by rfl⟩ : syracuseStep 39212909 = 14704841) B14704841
theorem B26141939 : Blo 2293435 26141939 := bstep (se 1 (by rfl) ⟨19606454, by rfl⟩ : syracuseStep 26141939 = 39212909) B39212909
theorem B17427959 : Blo 2293435 17427959 := bstep (se 1 (by rfl) ⟨13070969, by rfl⟩ : syracuseStep 17427959 = 26141939) B26141939
theorem B11618639 : Blo 2293435 11618639 := bstep (se 1 (by rfl) ⟨8713979, by rfl⟩ : syracuseStep 11618639 = 17427959) B17427959
theorem B7745759 : Blo 2293435 7745759 := bstep (se 1 (by rfl) ⟨5809319, by rfl⟩ : syracuseStep 7745759 = 11618639) B11618639
theorem B5163839 : Blo 2293435 5163839 := bstep (se 1 (by rfl) ⟨3872879, by rfl⟩ : syracuseStep 5163839 = 7745759) B7745759
theorem B3442559 : Blo 2293435 3442559 := bstep (se 1 (by rfl) ⟨2581919, by rfl⟩ : syracuseStep 3442559 = 5163839) B5163839
theorem B2295039 : Blo 2293435 2295039 := bstep (se 1 (by rfl) ⟨1721279, by rfl⟩ : syracuseStep 2295039 = 3442559) B3442559
theorem B3442565 : Blo 2293435 3442565 := bbase (se 4 (by rfl) ⟨322740, by rfl⟩ : syracuseStep 3442565 = 645481) (by norm_num)
theorem B2295043 : Blo 2293435 2295043 := bstep (se 1 (by rfl) ⟨1721282, by rfl⟩ : syracuseStep 2295043 = 3442565) B3442565
theorem B3872893 : Blo 2293435 3872893 := bbase (se 3 (by rfl) ⟨726167, by rfl⟩ : syracuseStep 3872893 = 1452335) (by norm_num)
theorem B5163857 : Blo 2293435 5163857 := bstep (se 2 (by rfl) ⟨1936446, by rfl⟩ : syracuseStep 5163857 = 3872893) B3872893
theorem B3442571 : Blo 2293435 3442571 := bstep (se 1 (by rfl) ⟨2581928, by rfl⟩ : syracuseStep 3442571 = 5163857) B5163857
theorem B2295047 : Blo 2293435 2295047 := bstep (se 1 (by rfl) ⟨1721285, by rfl⟩ : syracuseStep 2295047 = 3442571) B3442571
theorem B2581933 : Blo 2293435 2581933 := bbase (se 3 (by rfl) ⟨484112, by rfl⟩ : syracuseStep 2581933 = 968225) (by norm_num)
theorem B3442577 : Blo 2293435 3442577 := bstep (se 2 (by rfl) ⟨1290966, by rfl⟩ : syracuseStep 3442577 = 2581933) B2581933
theorem B2295051 : Blo 2293435 2295051 := bstep (se 1 (by rfl) ⟨1721288, by rfl⟩ : syracuseStep 2295051 = 3442577) B3442577
theorem B7745813 : Blo 2293435 7745813 := bbase (se 6 (by rfl) ⟨181542, by rfl⟩ : syracuseStep 7745813 = 363085) (by norm_num)
theorem B5163875 : Blo 2293435 5163875 := bstep (se 1 (by rfl) ⟨3872906, by rfl⟩ : syracuseStep 5163875 = 7745813) B7745813
theorem B3442583 : Blo 2293435 3442583 := bstep (se 1 (by rfl) ⟨2581937, by rfl⟩ : syracuseStep 3442583 = 5163875) B5163875
theorem B2295055 : Blo 2293435 2295055 := bstep (se 1 (by rfl) ⟨1721291, by rfl⟩ : syracuseStep 2295055 = 3442583) B3442583
theorem B3442589 : Blo 2293435 3442589 := bbase (se 3 (by rfl) ⟨645485, by rfl⟩ : syracuseStep 3442589 = 1290971) (by norm_num)
theorem B2295059 : Blo 2293435 2295059 := bstep (se 1 (by rfl) ⟨1721294, by rfl⟩ : syracuseStep 2295059 = 3442589) B3442589
theorem B5163893 : Blo 2293435 5163893 := bbase (se 5 (by rfl) ⟨242057, by rfl⟩ : syracuseStep 5163893 = 484115) (by norm_num)
theorem B3442595 : Blo 2293435 3442595 := bstep (se 1 (by rfl) ⟨2581946, by rfl⟩ : syracuseStep 3442595 = 5163893) B5163893
theorem B2295063 : Blo 2293435 2295063 := bstep (se 1 (by rfl) ⟨1721297, by rfl⟩ : syracuseStep 2295063 = 3442595) B3442595
theorem B3726413 : Blo 2293435 3726413 := bbase (se 3 (by rfl) ⟨698702, by rfl⟩ : syracuseStep 3726413 = 1397405) (by norm_num)
theorem B2484275 : Blo 2293435 2484275 := bstep (se 1 (by rfl) ⟨1863206, by rfl⟩ : syracuseStep 2484275 = 3726413) B3726413
theorem B26498933 : Blo 2293435 26498933 := bstep (se 5 (by rfl) ⟨1242137, by rfl⟩ : syracuseStep 26498933 = 2484275) B2484275
theorem B17665955 : Blo 2293435 17665955 := bstep (se 1 (by rfl) ⟨13249466, by rfl⟩ : syracuseStep 17665955 = 26498933) B26498933
theorem B11777303 : Blo 2293435 11777303 := bstep (se 1 (by rfl) ⟨8832977, by rfl⟩ : syracuseStep 11777303 = 17665955) B17665955
theorem B7851535 : Blo 2293435 7851535 := bstep (se 1 (by rfl) ⟨5888651, by rfl⟩ : syracuseStep 7851535 = 11777303) B11777303
theorem B167499413 : Blo 2293435 167499413 := bstep (se 6 (by rfl) ⟨3925767, by rfl⟩ : syracuseStep 167499413 = 7851535) B7851535
theorem B111666275 : Blo 2293435 111666275 := bstep (se 1 (by rfl) ⟨83749706, by rfl⟩ : syracuseStep 111666275 = 167499413) B167499413
theorem B74444183 : Blo 2293435 74444183 := bstep (se 1 (by rfl) ⟨55833137, by rfl⟩ : syracuseStep 74444183 = 111666275) B111666275
theorem B49629455 : Blo 2293435 49629455 := bstep (se 1 (by rfl) ⟨37222091, by rfl⟩ : syracuseStep 49629455 = 74444183) B74444183
theorem B33086303 : Blo 2293435 33086303 := bstep (se 1 (by rfl) ⟨24814727, by rfl⟩ : syracuseStep 33086303 = 49629455) B49629455
theorem B22057535 : Blo 2293435 22057535 := bstep (se 1 (by rfl) ⟨16543151, by rfl⟩ : syracuseStep 22057535 = 33086303) B33086303
theorem B14705023 : Blo 2293435 14705023 := bstep (se 1 (by rfl) ⟨11028767, by rfl⟩ : syracuseStep 14705023 = 22057535) B22057535
theorem B19606697 : Blo 2293435 19606697 := bstep (se 2 (by rfl) ⟨7352511, by rfl⟩ : syracuseStep 19606697 = 14705023) B14705023
theorem B13071131 : Blo 2293435 13071131 := bstep (se 1 (by rfl) ⟨9803348, by rfl⟩ : syracuseStep 13071131 = 19606697) B19606697
theorem B8714087 : Blo 2293435 8714087 := bstep (se 1 (by rfl) ⟨6535565, by rfl⟩ : syracuseStep 8714087 = 13071131) B13071131
theorem B5809391 : Blo 2293435 5809391 := bstep (se 1 (by rfl) ⟨4357043, by rfl⟩ : syracuseStep 5809391 = 8714087) B8714087
theorem B3872927 : Blo 2293435 3872927 := bstep (se 1 (by rfl) ⟨2904695, by rfl⟩ : syracuseStep 3872927 = 5809391) B5809391
theorem B2581951 : Blo 2293435 2581951 := bstep (se 1 (by rfl) ⟨1936463, by rfl⟩ : syracuseStep 2581951 = 3872927) B3872927
theorem B3442601 : Blo 2293435 3442601 := bstep (se 2 (by rfl) ⟨1290975, by rfl⟩ : syracuseStep 3442601 = 2581951) B2581951
theorem B2295067 : Blo 2293435 2295067 := bstep (se 1 (by rfl) ⟨1721300, by rfl⟩ : syracuseStep 2295067 = 3442601) B3442601
theorem B8714101 : Blo 2293435 8714101 := bbase (se 5 (by rfl) ⟨408473, by rfl⟩ : syracuseStep 8714101 = 816947) (by norm_num)
theorem B11618801 : Blo 2293435 11618801 := bstep (se 2 (by rfl) ⟨4357050, by rfl⟩ : syracuseStep 11618801 = 8714101) B8714101
theorem B7745867 : Blo 2293435 7745867 := bstep (se 1 (by rfl) ⟨5809400, by rfl⟩ : syracuseStep 7745867 = 11618801) B11618801
theorem B5163911 : Blo 2293435 5163911 := bstep (se 1 (by rfl) ⟨3872933, by rfl⟩ : syracuseStep 5163911 = 7745867) B7745867
theorem B3442607 : Blo 2293435 3442607 := bstep (se 1 (by rfl) ⟨2581955, by rfl⟩ : syracuseStep 3442607 = 5163911) B5163911
theorem B2295071 : Blo 2293435 2295071 := bstep (se 1 (by rfl) ⟨1721303, by rfl⟩ : syracuseStep 2295071 = 3442607) B3442607
theorem B3442613 : Blo 2293435 3442613 := bbase (se 5 (by rfl) ⟨161372, by rfl⟩ : syracuseStep 3442613 = 322745) (by norm_num)
theorem B2295075 : Blo 2293435 2295075 := bstep (se 1 (by rfl) ⟨1721306, by rfl⟩ : syracuseStep 2295075 = 3442613) B3442613
theorem B5809421 : Blo 2293435 5809421 := bbase (se 3 (by rfl) ⟨1089266, by rfl⟩ : syracuseStep 5809421 = 2178533) (by norm_num)
theorem B3872947 : Blo 2293435 3872947 := bstep (se 1 (by rfl) ⟨2904710, by rfl⟩ : syracuseStep 3872947 = 5809421) B5809421
theorem B5163929 : Blo 2293435 5163929 := bstep (se 2 (by rfl) ⟨1936473, by rfl⟩ : syracuseStep 5163929 = 3872947) B3872947
theorem B3442619 : Blo 2293435 3442619 := bstep (se 1 (by rfl) ⟨2581964, by rfl⟩ : syracuseStep 3442619 = 5163929) B5163929
theorem B2295079 : Blo 2293435 2295079 := bstep (se 1 (by rfl) ⟨1721309, by rfl⟩ : syracuseStep 2295079 = 3442619) B3442619
theorem B2581969 : Blo 2293435 2581969 := bbase (se 2 (by rfl) ⟨968238, by rfl⟩ : syracuseStep 2581969 = 1936477) (by norm_num)
theorem B3442625 : Blo 2293435 3442625 := bstep (se 2 (by rfl) ⟨1290984, by rfl⟩ : syracuseStep 3442625 = 2581969) B2581969
theorem B2295083 : Blo 2293435 2295083 := bstep (se 1 (by rfl) ⟨1721312, by rfl⟩ : syracuseStep 2295083 = 3442625) B3442625
theorem B4901717 : Blo 2293435 4901717 := bbase (se 9 (by rfl) ⟨14360, by rfl⟩ : syracuseStep 4901717 = 28721) (by norm_num)
theorem B3267811 : Blo 2293435 3267811 := bstep (se 1 (by rfl) ⟨2450858, by rfl⟩ : syracuseStep 3267811 = 4901717) B4901717
theorem B4357081 : Blo 2293435 4357081 := bstep (se 2 (by rfl) ⟨1633905, by rfl⟩ : syracuseStep 4357081 = 3267811) B3267811
theorem B5809441 : Blo 2293435 5809441 := bstep (se 2 (by rfl) ⟨2178540, by rfl⟩ : syracuseStep 5809441 = 4357081) B4357081
theorem B7745921 : Blo 2293435 7745921 := bstep (se 2 (by rfl) ⟨2904720, by rfl⟩ : syracuseStep 7745921 = 5809441) B5809441
theorem B5163947 : Blo 2293435 5163947 := bstep (se 1 (by rfl) ⟨3872960, by rfl⟩ : syracuseStep 5163947 = 7745921) B7745921
theorem B3442631 : Blo 2293435 3442631 := bstep (se 1 (by rfl) ⟨2581973, by rfl⟩ : syracuseStep 3442631 = 5163947) B5163947
theorem B2295087 : Blo 2293435 2295087 := bstep (se 1 (by rfl) ⟨1721315, by rfl⟩ : syracuseStep 2295087 = 3442631) B3442631
theorem B3442637 : Blo 2293435 3442637 := bbase (se 3 (by rfl) ⟨645494, by rfl⟩ : syracuseStep 3442637 = 1290989) (by norm_num)
theorem B2295091 : Blo 2293435 2295091 := bstep (se 1 (by rfl) ⟨1721318, by rfl⟩ : syracuseStep 2295091 = 3442637) B3442637
theorem B5163965 : Blo 2293435 5163965 := bbase (se 3 (by rfl) ⟨968243, by rfl⟩ : syracuseStep 5163965 = 1936487) (by norm_num)
theorem B3442643 : Blo 2293435 3442643 := bstep (se 1 (by rfl) ⟨2581982, by rfl⟩ : syracuseStep 3442643 = 5163965) B5163965
theorem B2295095 : Blo 2293435 2295095 := bstep (se 1 (by rfl) ⟨1721321, by rfl⟩ : syracuseStep 2295095 = 3442643) B3442643
theorem B3872981 : Blo 2293435 3872981 := bbase (se 7 (by rfl) ⟨45386, by rfl⟩ : syracuseStep 3872981 = 90773) (by norm_num)
theorem B2581987 : Blo 2293435 2581987 := bstep (se 1 (by rfl) ⟨1936490, by rfl⟩ : syracuseStep 2581987 = 3872981) B3872981
theorem B3442649 : Blo 2293435 3442649 := bstep (se 2 (by rfl) ⟨1290993, by rfl⟩ : syracuseStep 3442649 = 2581987) B2581987
theorem B2295099 : Blo 2293435 2295099 := bstep (se 1 (by rfl) ⟨1721324, by rfl⟩ : syracuseStep 2295099 = 3442649) B3442649
theorem B4135853 : Blo 2293435 4135853 := bbase (se 3 (by rfl) ⟨775472, by rfl⟩ : syracuseStep 4135853 = 1550945) (by norm_num)
theorem B2757235 : Blo 2293435 2757235 := bstep (se 1 (by rfl) ⟨2067926, by rfl⟩ : syracuseStep 2757235 = 4135853) B4135853
theorem B3676313 : Blo 2293435 3676313 := bstep (se 2 (by rfl) ⟨1378617, by rfl⟩ : syracuseStep 3676313 = 2757235) B2757235
theorem B9803501 : Blo 2293435 9803501 := bstep (se 3 (by rfl) ⟨1838156, by rfl⟩ : syracuseStep 9803501 = 3676313) B3676313
theorem B6535667 : Blo 2293435 6535667 := bstep (se 1 (by rfl) ⟨4901750, by rfl⟩ : syracuseStep 6535667 = 9803501) B9803501
theorem B17428445 : Blo 2293435 17428445 := bstep (se 3 (by rfl) ⟨3267833, by rfl⟩ : syracuseStep 17428445 = 6535667) B6535667
theorem B11618963 : Blo 2293435 11618963 := bstep (se 1 (by rfl) ⟨8714222, by rfl⟩ : syracuseStep 11618963 = 17428445) B17428445
theorem B7745975 : Blo 2293435 7745975 := bstep (se 1 (by rfl) ⟨5809481, by rfl⟩ : syracuseStep 7745975 = 11618963) B11618963
theorem B5163983 : Blo 2293435 5163983 := bstep (se 1 (by rfl) ⟨3872987, by rfl⟩ : syracuseStep 5163983 = 7745975) B7745975
theorem B3442655 : Blo 2293435 3442655 := bstep (se 1 (by rfl) ⟨2581991, by rfl⟩ : syracuseStep 3442655 = 5163983) B5163983
theorem B2295103 : Blo 2293435 2295103 := bstep (se 1 (by rfl) ⟨1721327, by rfl⟩ : syracuseStep 2295103 = 3442655) B3442655
theorem B3442661 : Blo 2293435 3442661 := bbase (se 4 (by rfl) ⟨322749, by rfl⟩ : syracuseStep 3442661 = 645499) (by norm_num)
theorem B2295107 : Blo 2293435 2295107 := bstep (se 1 (by rfl) ⟨1721330, by rfl⟩ : syracuseStep 2295107 = 3442661) B3442661
theorem B2757245 : Blo 2293435 2757245 := bbase (se 3 (by rfl) ⟨516983, by rfl⟩ : syracuseStep 2757245 = 1033967) (by norm_num)
theorem B7352653 : Blo 2293435 7352653 := bstep (se 3 (by rfl) ⟨1378622, by rfl⟩ : syracuseStep 7352653 = 2757245) B2757245
theorem B9803537 : Blo 2293435 9803537 := bstep (se 2 (by rfl) ⟨3676326, by rfl⟩ : syracuseStep 9803537 = 7352653) B7352653
theorem B6535691 : Blo 2293435 6535691 := bstep (se 1 (by rfl) ⟨4901768, by rfl⟩ : syracuseStep 6535691 = 9803537) B9803537
theorem B4357127 : Blo 2293435 4357127 := bstep (se 1 (by rfl) ⟨3267845, by rfl⟩ : syracuseStep 4357127 = 6535691) B6535691
theorem B2904751 : Blo 2293435 2904751 := bstep (se 1 (by rfl) ⟨2178563, by rfl⟩ : syracuseStep 2904751 = 4357127) B4357127
theorem B3873001 : Blo 2293435 3873001 := bstep (se 2 (by rfl) ⟨1452375, by rfl⟩ : syracuseStep 3873001 = 2904751) B2904751
theorem B5164001 : Blo 2293435 5164001 := bstep (se 2 (by rfl) ⟨1936500, by rfl⟩ : syracuseStep 5164001 = 3873001) B3873001
theorem B3442667 : Blo 2293435 3442667 := bstep (se 1 (by rfl) ⟨2582000, by rfl⟩ : syracuseStep 3442667 = 5164001) B5164001
theorem B2295111 : Blo 2293435 2295111 := bstep (se 1 (by rfl) ⟨1721333, by rfl⟩ : syracuseStep 2295111 = 3442667) B3442667
theorem B2582005 : Blo 2293435 2582005 := bbase (se 5 (by rfl) ⟨121031, by rfl⟩ : syracuseStep 2582005 = 242063) (by norm_num)
theorem B3442673 : Blo 2293435 3442673 := bstep (se 2 (by rfl) ⟨1291002, by rfl⟩ : syracuseStep 3442673 = 2582005) B2582005
theorem B2295115 : Blo 2293435 2295115 := bstep (se 1 (by rfl) ⟨1721336, by rfl⟩ : syracuseStep 2295115 = 3442673) B3442673
theorem B2904761 : Blo 2293435 2904761 := bbase (se 2 (by rfl) ⟨1089285, by rfl⟩ : syracuseStep 2904761 = 2178571) (by norm_num)
theorem B7746029 : Blo 2293435 7746029 := bstep (se 3 (by rfl) ⟨1452380, by rfl⟩ : syracuseStep 7746029 = 2904761) B2904761
theorem B5164019 : Blo 2293435 5164019 := bstep (se 1 (by rfl) ⟨3873014, by rfl⟩ : syracuseStep 5164019 = 7746029) B7746029
theorem B3442679 : Blo 2293435 3442679 := bstep (se 1 (by rfl) ⟨2582009, by rfl⟩ : syracuseStep 3442679 = 5164019) B5164019
theorem B2295119 : Blo 2293435 2295119 := bstep (se 1 (by rfl) ⟨1721339, by rfl⟩ : syracuseStep 2295119 = 3442679) B3442679
theorem B3442685 : Blo 2293435 3442685 := bbase (se 3 (by rfl) ⟨645503, by rfl⟩ : syracuseStep 3442685 = 1291007) (by norm_num)
theorem B2295123 : Blo 2293435 2295123 := bstep (se 1 (by rfl) ⟨1721342, by rfl⟩ : syracuseStep 2295123 = 3442685) B3442685
theorem B5164037 : Blo 2293435 5164037 := bbase (se 4 (by rfl) ⟨484128, by rfl⟩ : syracuseStep 5164037 = 968257) (by norm_num)
theorem B3442691 : Blo 2293435 3442691 := bstep (se 1 (by rfl) ⟨2582018, by rfl⟩ : syracuseStep 3442691 = 5164037) B5164037
theorem B2295127 : Blo 2293435 2295127 := bstep (se 1 (by rfl) ⟨1721345, by rfl⟩ : syracuseStep 2295127 = 3442691) B3442691
theorem B4357165 : Blo 2293435 4357165 := bbase (se 3 (by rfl) ⟨816968, by rfl⟩ : syracuseStep 4357165 = 1633937) (by norm_num)
theorem B5809553 : Blo 2293435 5809553 := bstep (se 2 (by rfl) ⟨2178582, by rfl⟩ : syracuseStep 5809553 = 4357165) B4357165
theorem B3873035 : Blo 2293435 3873035 := bstep (se 1 (by rfl) ⟨2904776, by rfl⟩ : syracuseStep 3873035 = 5809553) B5809553
theorem B2582023 : Blo 2293435 2582023 := bstep (se 1 (by rfl) ⟨1936517, by rfl⟩ : syracuseStep 2582023 = 3873035) B3873035
theorem B3442697 : Blo 2293435 3442697 := bstep (se 2 (by rfl) ⟨1291011, by rfl⟩ : syracuseStep 3442697 = 2582023) B2582023
theorem B2295131 : Blo 2293435 2295131 := bstep (se 1 (by rfl) ⟨1721348, by rfl⟩ : syracuseStep 2295131 = 3442697) B3442697
theorem B11619125 : Blo 2293435 11619125 := bbase (se 5 (by rfl) ⟨544646, by rfl⟩ : syracuseStep 11619125 = 1089293) (by norm_num)
theorem B7746083 : Blo 2293435 7746083 := bstep (se 1 (by rfl) ⟨5809562, by rfl⟩ : syracuseStep 7746083 = 11619125) B11619125
theorem B5164055 : Blo 2293435 5164055 := bstep (se 1 (by rfl) ⟨3873041, by rfl⟩ : syracuseStep 5164055 = 7746083) B7746083
theorem B3442703 : Blo 2293435 3442703 := bstep (se 1 (by rfl) ⟨2582027, by rfl⟩ : syracuseStep 3442703 = 5164055) B5164055
theorem B2295135 : Blo 2293435 2295135 := bstep (se 1 (by rfl) ⟨1721351, by rfl⟩ : syracuseStep 2295135 = 3442703) B3442703
theorem B3442709 : Blo 2293435 3442709 := bbase (se 6 (by rfl) ⟨80688, by rfl⟩ : syracuseStep 3442709 = 161377) (by norm_num)
theorem B2295139 : Blo 2293435 2295139 := bstep (se 1 (by rfl) ⟨1721354, by rfl⟩ : syracuseStep 2295139 = 3442709) B3442709
theorem B4135925 : Blo 2293435 4135925 := bbase (se 5 (by rfl) ⟨193871, by rfl⟩ : syracuseStep 4135925 = 387743) (by norm_num)
theorem B2757283 : Blo 2293435 2757283 := bstep (se 1 (by rfl) ⟨2067962, by rfl⟩ : syracuseStep 2757283 = 4135925) B4135925
theorem B14705509 : Blo 2293435 14705509 := bstep (se 4 (by rfl) ⟨1378641, by rfl⟩ : syracuseStep 14705509 = 2757283) B2757283
theorem B19607345 : Blo 2293435 19607345 := bstep (se 2 (by rfl) ⟨7352754, by rfl⟩ : syracuseStep 19607345 = 14705509) B14705509
theorem B13071563 : Blo 2293435 13071563 := bstep (se 1 (by rfl) ⟨9803672, by rfl⟩ : syracuseStep 13071563 = 19607345) B19607345
theorem B8714375 : Blo 2293435 8714375 := bstep (se 1 (by rfl) ⟨6535781, by rfl⟩ : syracuseStep 8714375 = 13071563) B13071563
theorem B5809583 : Blo 2293435 5809583 := bstep (se 1 (by rfl) ⟨4357187, by rfl⟩ : syracuseStep 5809583 = 8714375) B8714375
theorem B3873055 : Blo 2293435 3873055 := bstep (se 1 (by rfl) ⟨2904791, by rfl⟩ : syracuseStep 3873055 = 5809583) B5809583
theorem B5164073 : Blo 2293435 5164073 := bstep (se 2 (by rfl) ⟨1936527, by rfl⟩ : syracuseStep 5164073 = 3873055) B3873055
theorem B3442715 : Blo 2293435 3442715 := bstep (se 1 (by rfl) ⟨2582036, by rfl⟩ : syracuseStep 3442715 = 5164073) B5164073
theorem B2295143 : Blo 2293435 2295143 := bstep (se 1 (by rfl) ⟨1721357, by rfl⟩ : syracuseStep 2295143 = 3442715) B3442715
theorem B2582041 : Blo 2293435 2582041 := bbase (se 2 (by rfl) ⟨968265, by rfl⟩ : syracuseStep 2582041 = 1936531) (by norm_num)
theorem B3442721 : Blo 2293435 3442721 := bstep (se 2 (by rfl) ⟨1291020, by rfl⟩ : syracuseStep 3442721 = 2582041) B2582041
theorem B2295147 : Blo 2293435 2295147 := bstep (se 1 (by rfl) ⟨1721360, by rfl⟩ : syracuseStep 2295147 = 3442721) B3442721
theorem B8714405 : Blo 2293435 8714405 := bbase (se 4 (by rfl) ⟨816975, by rfl⟩ : syracuseStep 8714405 = 1633951) (by norm_num)
theorem B5809603 : Blo 2293435 5809603 := bstep (se 1 (by rfl) ⟨4357202, by rfl⟩ : syracuseStep 5809603 = 8714405) B8714405
theorem B7746137 : Blo 2293435 7746137 := bstep (se 2 (by rfl) ⟨2904801, by rfl⟩ : syracuseStep 7746137 = 5809603) B5809603
theorem B5164091 : Blo 2293435 5164091 := bstep (se 1 (by rfl) ⟨3873068, by rfl⟩ : syracuseStep 5164091 = 7746137) B7746137
theorem B3442727 : Blo 2293435 3442727 := bstep (se 1 (by rfl) ⟨2582045, by rfl⟩ : syracuseStep 3442727 = 5164091) B5164091
theorem B2295151 : Blo 2293435 2295151 := bstep (se 1 (by rfl) ⟨1721363, by rfl⟩ : syracuseStep 2295151 = 3442727) B3442727
theorem B3442733 : Blo 2293435 3442733 := bbase (se 3 (by rfl) ⟨645512, by rfl⟩ : syracuseStep 3442733 = 1291025) (by norm_num)
theorem B2295155 : Blo 2293435 2295155 := bstep (se 1 (by rfl) ⟨1721366, by rfl⟩ : syracuseStep 2295155 = 3442733) B3442733
theorem B5164109 : Blo 2293435 5164109 := bbase (se 3 (by rfl) ⟨968270, by rfl⟩ : syracuseStep 5164109 = 1936541) (by norm_num)
theorem B3442739 : Blo 2293435 3442739 := bstep (se 1 (by rfl) ⟨2582054, by rfl⟩ : syracuseStep 3442739 = 5164109) B5164109
theorem B2295159 : Blo 2293435 2295159 := bstep (se 1 (by rfl) ⟨1721369, by rfl⟩ : syracuseStep 2295159 = 3442739) B3442739
theorem B2904817 : Blo 2293435 2904817 := bbase (se 2 (by rfl) ⟨1089306, by rfl⟩ : syracuseStep 2904817 = 2178613) (by norm_num)
theorem B3873089 : Blo 2293435 3873089 := bstep (se 2 (by rfl) ⟨1452408, by rfl⟩ : syracuseStep 3873089 = 2904817) B2904817
theorem B2582059 : Blo 2293435 2582059 := bstep (se 1 (by rfl) ⟨1936544, by rfl⟩ : syracuseStep 2582059 = 3873089) B3873089
theorem B3442745 : Blo 2293435 3442745 := bstep (se 2 (by rfl) ⟨1291029, by rfl⟩ : syracuseStep 3442745 = 2582059) B2582059
theorem B2295163 : Blo 2293435 2295163 := bstep (se 1 (by rfl) ⟨1721372, by rfl⟩ : syracuseStep 2295163 = 3442745) B3442745
theorem B4249597 : Blo 2293435 4249597 := bbase (se 3 (by rfl) ⟨796799, by rfl⟩ : syracuseStep 4249597 = 1593599) (by norm_num)
theorem B5666129 : Blo 2293435 5666129 := bstep (se 2 (by rfl) ⟨2124798, by rfl⟩ : syracuseStep 5666129 = 4249597) B4249597
theorem B3777419 : Blo 2293435 3777419 := bstep (se 1 (by rfl) ⟨2833064, by rfl⟩ : syracuseStep 3777419 = 5666129) B5666129
theorem B10073117 : Blo 2293435 10073117 := bstep (se 3 (by rfl) ⟨1888709, by rfl⟩ : syracuseStep 10073117 = 3777419) B3777419
theorem B26861645 : Blo 2293435 26861645 := bstep (se 3 (by rfl) ⟨5036558, by rfl⟩ : syracuseStep 26861645 = 10073117) B10073117
theorem B71631053 : Blo 2293435 71631053 := bstep (se 3 (by rfl) ⟨13430822, by rfl⟩ : syracuseStep 71631053 = 26861645) B26861645
theorem B47754035 : Blo 2293435 47754035 := bstep (se 1 (by rfl) ⟨35815526, by rfl⟩ : syracuseStep 47754035 = 71631053) B71631053
theorem B31836023 : Blo 2293435 31836023 := bstep (se 1 (by rfl) ⟨23877017, by rfl⟩ : syracuseStep 31836023 = 47754035) B47754035
theorem B21224015 : Blo 2293435 21224015 := bstep (se 1 (by rfl) ⟨15918011, by rfl⟩ : syracuseStep 21224015 = 31836023) B31836023
theorem B14149343 : Blo 2293435 14149343 := bstep (se 1 (by rfl) ⟨10612007, by rfl⟩ : syracuseStep 14149343 = 21224015) B21224015
theorem B9432895 : Blo 2293435 9432895 := bstep (se 1 (by rfl) ⟨7074671, by rfl⟩ : syracuseStep 9432895 = 14149343) B14149343
theorem B12577193 : Blo 2293435 12577193 := bstep (se 2 (by rfl) ⟨4716447, by rfl⟩ : syracuseStep 12577193 = 9432895) B9432895
theorem B8384795 : Blo 2293435 8384795 := bstep (se 1 (by rfl) ⟨6288596, by rfl⟩ : syracuseStep 8384795 = 12577193) B12577193
theorem B5589863 : Blo 2293435 5589863 := bstep (se 1 (by rfl) ⟨4192397, by rfl⟩ : syracuseStep 5589863 = 8384795) B8384795
theorem B3726575 : Blo 2293435 3726575 := bstep (se 1 (by rfl) ⟨2794931, by rfl⟩ : syracuseStep 3726575 = 5589863) B5589863
theorem B2484383 : Blo 2293435 2484383 := bstep (se 1 (by rfl) ⟨1863287, by rfl⟩ : syracuseStep 2484383 = 3726575) B3726575
theorem B6625021 : Blo 2293435 6625021 := bstep (se 3 (by rfl) ⟨1242191, by rfl⟩ : syracuseStep 6625021 = 2484383) B2484383
theorem B141333781 : Blo 2293435 141333781 := bstep (se 6 (by rfl) ⟨3312510, by rfl⟩ : syracuseStep 141333781 = 6625021) B6625021
theorem B188445041 : Blo 2293435 188445041 := bstep (se 2 (by rfl) ⟨70666890, by rfl⟩ : syracuseStep 188445041 = 141333781) B141333781
theorem B125630027 : Blo 2293435 125630027 := bstep (se 1 (by rfl) ⟨94222520, by rfl⟩ : syracuseStep 125630027 = 188445041) B188445041
theorem B83753351 : Blo 2293435 83753351 := bstep (se 1 (by rfl) ⟨62815013, by rfl⟩ : syracuseStep 83753351 = 125630027) B125630027
theorem B55835567 : Blo 2293435 55835567 := bstep (se 1 (by rfl) ⟨41876675, by rfl⟩ : syracuseStep 55835567 = 83753351) B83753351
theorem B37223711 : Blo 2293435 37223711 := bstep (se 1 (by rfl) ⟨27917783, by rfl⟩ : syracuseStep 37223711 = 55835567) B55835567
theorem B24815807 : Blo 2293435 24815807 := bstep (se 1 (by rfl) ⟨18611855, by rfl⟩ : syracuseStep 24815807 = 37223711) B37223711
theorem B16543871 : Blo 2293435 16543871 := bstep (se 1 (by rfl) ⟨12407903, by rfl⟩ : syracuseStep 16543871 = 24815807) B24815807
theorem B11029247 : Blo 2293435 11029247 := bstep (se 1 (by rfl) ⟨8271935, by rfl⟩ : syracuseStep 11029247 = 16543871) B16543871
theorem B7352831 : Blo 2293435 7352831 := bstep (se 1 (by rfl) ⟨5514623, by rfl⟩ : syracuseStep 7352831 = 11029247) B11029247
theorem B4901887 : Blo 2293435 4901887 := bstep (se 1 (by rfl) ⟨3676415, by rfl⟩ : syracuseStep 4901887 = 7352831) B7352831
theorem B26143397 : Blo 2293435 26143397 := bstep (se 4 (by rfl) ⟨2450943, by rfl⟩ : syracuseStep 26143397 = 4901887) B4901887
theorem B17428931 : Blo 2293435 17428931 := bstep (se 1 (by rfl) ⟨13071698, by rfl⟩ : syracuseStep 17428931 = 26143397) B26143397
theorem B11619287 : Blo 2293435 11619287 := bstep (se 1 (by rfl) ⟨8714465, by rfl⟩ : syracuseStep 11619287 = 17428931) B17428931
theorem B7746191 : Blo 2293435 7746191 := bstep (se 1 (by rfl) ⟨5809643, by rfl⟩ : syracuseStep 7746191 = 11619287) B11619287
theorem B5164127 : Blo 2293435 5164127 := bstep (se 1 (by rfl) ⟨3873095, by rfl⟩ : syracuseStep 5164127 = 7746191) B7746191
theorem B3442751 : Blo 2293435 3442751 := bstep (se 1 (by rfl) ⟨2582063, by rfl⟩ : syracuseStep 3442751 = 5164127) B5164127
theorem B2295167 : Blo 2293435 2295167 := bstep (se 1 (by rfl) ⟨1721375, by rfl⟩ : syracuseStep 2295167 = 3442751) B3442751
theorem B3442757 : Blo 2293435 3442757 := bbase (se 4 (by rfl) ⟨322758, by rfl⟩ : syracuseStep 3442757 = 645517) (by norm_num)
theorem B2295171 : Blo 2293435 2295171 := bstep (se 1 (by rfl) ⟨1721378, by rfl⟩ : syracuseStep 2295171 = 3442757) B3442757
theorem B3873109 : Blo 2293435 3873109 := bbase (se 10 (by rfl) ⟨5673, by rfl⟩ : syracuseStep 3873109 = 11347) (by norm_num)
theorem B5164145 : Blo 2293435 5164145 := bstep (se 2 (by rfl) ⟨1936554, by rfl⟩ : syracuseStep 5164145 = 3873109) B3873109
theorem B3442763 : Blo 2293435 3442763 := bstep (se 1 (by rfl) ⟨2582072, by rfl⟩ : syracuseStep 3442763 = 5164145) B5164145
theorem B2295175 : Blo 2293435 2295175 := bstep (se 1 (by rfl) ⟨1721381, by rfl⟩ : syracuseStep 2295175 = 3442763) B3442763
theorem B2582077 : Blo 2293435 2582077 := bbase (se 3 (by rfl) ⟨484139, by rfl⟩ : syracuseStep 2582077 = 968279) (by norm_num)
theorem B3442769 : Blo 2293435 3442769 := bstep (se 2 (by rfl) ⟨1291038, by rfl⟩ : syracuseStep 3442769 = 2582077) B2582077
theorem B2295179 : Blo 2293435 2295179 := bstep (se 1 (by rfl) ⟨1721384, by rfl⟩ : syracuseStep 2295179 = 3442769) B3442769
theorem B7746245 : Blo 2293435 7746245 := bbase (se 4 (by rfl) ⟨726210, by rfl⟩ : syracuseStep 7746245 = 1452421) (by norm_num)
theorem B5164163 : Blo 2293435 5164163 := bstep (se 1 (by rfl) ⟨3873122, by rfl⟩ : syracuseStep 5164163 = 7746245) B7746245
theorem B3442775 : Blo 2293435 3442775 := bstep (se 1 (by rfl) ⟨2582081, by rfl⟩ : syracuseStep 3442775 = 5164163) B5164163
theorem B2295183 : Blo 2293435 2295183 := bstep (se 1 (by rfl) ⟨1721387, by rfl⟩ : syracuseStep 2295183 = 3442775) B3442775
theorem B3442781 : Blo 2293435 3442781 := bbase (se 3 (by rfl) ⟨645521, by rfl⟩ : syracuseStep 3442781 = 1291043) (by norm_num)
theorem B2295187 : Blo 2293435 2295187 := bstep (se 1 (by rfl) ⟨1721390, by rfl⟩ : syracuseStep 2295187 = 3442781) B3442781
theorem B5164181 : Blo 2293435 5164181 := bbase (se 6 (by rfl) ⟨121035, by rfl⟩ : syracuseStep 5164181 = 242071) (by norm_num)
theorem B3442787 : Blo 2293435 3442787 := bstep (se 1 (by rfl) ⟨2582090, by rfl⟩ : syracuseStep 3442787 = 5164181) B5164181
theorem B2295191 : Blo 2293435 2295191 := bstep (se 1 (by rfl) ⟨1721393, by rfl⟩ : syracuseStep 2295191 = 3442787) B3442787
theorem B3267965 : Blo 2293435 3267965 := bbase (se 3 (by rfl) ⟨612743, by rfl⟩ : syracuseStep 3267965 = 1225487) (by norm_num)
theorem B8714573 : Blo 2293435 8714573 := bstep (se 3 (by rfl) ⟨1633982, by rfl⟩ : syracuseStep 8714573 = 3267965) B3267965
theorem B5809715 : Blo 2293435 5809715 := bstep (se 1 (by rfl) ⟨4357286, by rfl⟩ : syracuseStep 5809715 = 8714573) B8714573
theorem B3873143 : Blo 2293435 3873143 := bstep (se 1 (by rfl) ⟨2904857, by rfl⟩ : syracuseStep 3873143 = 5809715) B5809715
theorem B2582095 : Blo 2293435 2582095 := bstep (se 1 (by rfl) ⟨1936571, by rfl⟩ : syracuseStep 2582095 = 3873143) B3873143
theorem B3442793 : Blo 2293435 3442793 := bstep (se 2 (by rfl) ⟨1291047, by rfl⟩ : syracuseStep 3442793 = 2582095) B2582095
theorem B2295195 : Blo 2293435 2295195 := bstep (se 1 (by rfl) ⟨1721396, by rfl⟩ : syracuseStep 2295195 = 3442793) B3442793
theorem B4653029 : Blo 2293435 4653029 := bbase (se 4 (by rfl) ⟨436221, by rfl⟩ : syracuseStep 4653029 = 872443) (by norm_num)
theorem B3102019 : Blo 2293435 3102019 := bstep (se 1 (by rfl) ⟨2326514, by rfl⟩ : syracuseStep 3102019 = 4653029) B4653029
theorem B16544101 : Blo 2293435 16544101 := bstep (se 4 (by rfl) ⟨1551009, by rfl⟩ : syracuseStep 16544101 = 3102019) B3102019
theorem B22058801 : Blo 2293435 22058801 := bstep (se 2 (by rfl) ⟨8272050, by rfl⟩ : syracuseStep 22058801 = 16544101) B16544101
theorem B14705867 : Blo 2293435 14705867 := bstep (se 1 (by rfl) ⟨11029400, by rfl⟩ : syracuseStep 14705867 = 22058801) B22058801
theorem B9803911 : Blo 2293435 9803911 := bstep (se 1 (by rfl) ⟨7352933, by rfl⟩ : syracuseStep 9803911 = 14705867) B14705867
theorem B13071881 : Blo 2293435 13071881 := bstep (se 2 (by rfl) ⟨4901955, by rfl⟩ : syracuseStep 13071881 = 9803911) B9803911
theorem B8714587 : Blo 2293435 8714587 := bstep (se 1 (by rfl) ⟨6535940, by rfl⟩ : syracuseStep 8714587 = 13071881) B13071881
theorem B11619449 : Blo 2293435 11619449 := bstep (se 2 (by rfl) ⟨4357293, by rfl⟩ : syracuseStep 11619449 = 8714587) B8714587
theorem B7746299 : Blo 2293435 7746299 := bstep (se 1 (by rfl) ⟨5809724, by rfl⟩ : syracuseStep 7746299 = 11619449) B11619449
theorem B5164199 : Blo 2293435 5164199 := bstep (se 1 (by rfl) ⟨3873149, by rfl⟩ : syracuseStep 5164199 = 7746299) B7746299
theorem B3442799 : Blo 2293435 3442799 := bstep (se 1 (by rfl) ⟨2582099, by rfl⟩ : syracuseStep 3442799 = 5164199) B5164199
theorem B2295199 : Blo 2293435 2295199 := bstep (se 1 (by rfl) ⟨1721399, by rfl⟩ : syracuseStep 2295199 = 3442799) B3442799
theorem B3442805 : Blo 2293435 3442805 := bbase (se 5 (by rfl) ⟨161381, by rfl⟩ : syracuseStep 3442805 = 322763) (by norm_num)
theorem B2295203 : Blo 2293435 2295203 := bstep (se 1 (by rfl) ⟨1721402, by rfl⟩ : syracuseStep 2295203 = 3442805) B3442805
theorem B4357309 : Blo 2293435 4357309 := bbase (se 3 (by rfl) ⟨816995, by rfl⟩ : syracuseStep 4357309 = 1633991) (by norm_num)
theorem B5809745 : Blo 2293435 5809745 := bstep (se 2 (by rfl) ⟨2178654, by rfl⟩ : syracuseStep 5809745 = 4357309) B4357309
theorem B3873163 : Blo 2293435 3873163 := bstep (se 1 (by rfl) ⟨2904872, by rfl⟩ : syracuseStep 3873163 = 5809745) B5809745
theorem B5164217 : Blo 2293435 5164217 := bstep (se 2 (by rfl) ⟨1936581, by rfl⟩ : syracuseStep 5164217 = 3873163) B3873163
theorem B3442811 : Blo 2293435 3442811 := bstep (se 1 (by rfl) ⟨2582108, by rfl⟩ : syracuseStep 3442811 = 5164217) B5164217
theorem B2295207 : Blo 2293435 2295207 := bstep (se 1 (by rfl) ⟨1721405, by rfl⟩ : syracuseStep 2295207 = 3442811) B3442811
theorem B2582113 : Blo 2293435 2582113 := bbase (se 2 (by rfl) ⟨968292, by rfl⟩ : syracuseStep 2582113 = 1936585) (by norm_num)
theorem B3442817 : Blo 2293435 3442817 := bstep (se 2 (by rfl) ⟨1291056, by rfl⟩ : syracuseStep 3442817 = 2582113) B2582113
theorem B2295211 : Blo 2293435 2295211 := bstep (se 1 (by rfl) ⟨1721408, by rfl⟩ : syracuseStep 2295211 = 3442817) B3442817
theorem B5809765 : Blo 2293435 5809765 := bbase (se 4 (by rfl) ⟨544665, by rfl⟩ : syracuseStep 5809765 = 1089331) (by norm_num)
theorem B7746353 : Blo 2293435 7746353 := bstep (se 2 (by rfl) ⟨2904882, by rfl⟩ : syracuseStep 7746353 = 5809765) B5809765
theorem B5164235 : Blo 2293435 5164235 := bstep (se 1 (by rfl) ⟨3873176, by rfl⟩ : syracuseStep 5164235 = 7746353) B7746353
theorem B3442823 : Blo 2293435 3442823 := bstep (se 1 (by rfl) ⟨2582117, by rfl⟩ : syracuseStep 3442823 = 5164235) B5164235
theorem B2295215 : Blo 2293435 2295215 := bstep (se 1 (by rfl) ⟨1721411, by rfl⟩ : syracuseStep 2295215 = 3442823) B3442823
theorem B3442829 : Blo 2293435 3442829 := bbase (se 3 (by rfl) ⟨645530, by rfl⟩ : syracuseStep 3442829 = 1291061) (by norm_num)
theorem B2295219 : Blo 2293435 2295219 := bstep (se 1 (by rfl) ⟨1721414, by rfl⟩ : syracuseStep 2295219 = 3442829) B3442829
theorem B5164253 : Blo 2293435 5164253 := bbase (se 3 (by rfl) ⟨968297, by rfl⟩ : syracuseStep 5164253 = 1936595) (by norm_num)
theorem B3442835 : Blo 2293435 3442835 := bstep (se 1 (by rfl) ⟨2582126, by rfl⟩ : syracuseStep 3442835 = 5164253) B5164253
theorem B2295223 : Blo 2293435 2295223 := bstep (se 1 (by rfl) ⟨1721417, by rfl⟩ : syracuseStep 2295223 = 3442835) B3442835
theorem B3873197 : Blo 2293435 3873197 := bbase (se 3 (by rfl) ⟨726224, by rfl⟩ : syracuseStep 3873197 = 1452449) (by norm_num)
theorem B2582131 : Blo 2293435 2582131 := bstep (se 1 (by rfl) ⟨1936598, by rfl⟩ : syracuseStep 2582131 = 3873197) B3873197
theorem B3442841 : Blo 2293435 3442841 := bstep (se 2 (by rfl) ⟨1291065, by rfl⟩ : syracuseStep 3442841 = 2582131) B2582131
theorem B2295227 : Blo 2293435 2295227 := bstep (se 1 (by rfl) ⟨1721420, by rfl⟩ : syracuseStep 2295227 = 3442841) B3442841
theorem B5306149 : Blo 2293435 5306149 := bbase (se 4 (by rfl) ⟨497451, by rfl⟩ : syracuseStep 5306149 = 994903) (by norm_num)
theorem B28299461 : Blo 2293435 28299461 := bstep (se 4 (by rfl) ⟨2653074, by rfl⟩ : syracuseStep 28299461 = 5306149) B5306149
theorem B301860917 : Blo 2293435 301860917 := bstep (se 5 (by rfl) ⟨14149730, by rfl⟩ : syracuseStep 301860917 = 28299461) B28299461
theorem B201240611 : Blo 2293435 201240611 := bstep (se 1 (by rfl) ⟨150930458, by rfl⟩ : syracuseStep 201240611 = 301860917) B301860917
theorem B134160407 : Blo 2293435 134160407 := bstep (se 1 (by rfl) ⟨100620305, by rfl⟩ : syracuseStep 134160407 = 201240611) B201240611
theorem B89440271 : Blo 2293435 89440271 := bstep (se 1 (by rfl) ⟨67080203, by rfl⟩ : syracuseStep 89440271 = 134160407) B134160407
theorem B59626847 : Blo 2293435 59626847 := bstep (se 1 (by rfl) ⟨44720135, by rfl⟩ : syracuseStep 59626847 = 89440271) B89440271
theorem B39751231 : Blo 2293435 39751231 := bstep (se 1 (by rfl) ⟨29813423, by rfl⟩ : syracuseStep 39751231 = 59626847) B59626847
theorem B53001641 : Blo 2293435 53001641 := bstep (se 2 (by rfl) ⟨19875615, by rfl⟩ : syracuseStep 53001641 = 39751231) B39751231
theorem B35334427 : Blo 2293435 35334427 := bstep (se 1 (by rfl) ⟨26500820, by rfl⟩ : syracuseStep 35334427 = 53001641) B53001641
theorem B47112569 : Blo 2293435 47112569 := bstep (se 2 (by rfl) ⟨17667213, by rfl⟩ : syracuseStep 47112569 = 35334427) B35334427
theorem B31408379 : Blo 2293435 31408379 := bstep (se 1 (by rfl) ⟨23556284, by rfl⟩ : syracuseStep 31408379 = 47112569) B47112569
theorem B20938919 : Blo 2293435 20938919 := bstep (se 1 (by rfl) ⟨15704189, by rfl⟩ : syracuseStep 20938919 = 31408379) B31408379
theorem B55837117 : Blo 2293435 55837117 := bstep (se 3 (by rfl) ⟨10469459, by rfl⟩ : syracuseStep 55837117 = 20938919) B20938919
theorem B74449489 : Blo 2293435 74449489 := bstep (se 2 (by rfl) ⟨27918558, by rfl⟩ : syracuseStep 74449489 = 55837117) B55837117
theorem B99265985 : Blo 2293435 99265985 := bstep (se 2 (by rfl) ⟨37224744, by rfl⟩ : syracuseStep 99265985 = 74449489) B74449489
theorem B66177323 : Blo 2293435 66177323 := bstep (se 1 (by rfl) ⟨49632992, by rfl⟩ : syracuseStep 66177323 = 99265985) B99265985
theorem B44118215 : Blo 2293435 44118215 := bstep (se 1 (by rfl) ⟨33088661, by rfl⟩ : syracuseStep 44118215 = 66177323) B66177323
theorem B29412143 : Blo 2293435 29412143 := bstep (se 1 (by rfl) ⟨22059107, by rfl⟩ : syracuseStep 29412143 = 44118215) B44118215
theorem B19608095 : Blo 2293435 19608095 := bstep (se 1 (by rfl) ⟨14706071, by rfl⟩ : syracuseStep 19608095 = 29412143) B29412143
theorem B13072063 : Blo 2293435 13072063 := bstep (se 1 (by rfl) ⟨9804047, by rfl⟩ : syracuseStep 13072063 = 19608095) B19608095
theorem B17429417 : Blo 2293435 17429417 := bstep (se 2 (by rfl) ⟨6536031, by rfl⟩ : syracuseStep 17429417 = 13072063) B13072063
theorem B11619611 : Blo 2293435 11619611 := bstep (se 1 (by rfl) ⟨8714708, by rfl⟩ : syracuseStep 11619611 = 17429417) B17429417
theorem B7746407 : Blo 2293435 7746407 := bstep (se 1 (by rfl) ⟨5809805, by rfl⟩ : syracuseStep 7746407 = 11619611) B11619611
theorem B5164271 : Blo 2293435 5164271 := bstep (se 1 (by rfl) ⟨3873203, by rfl⟩ : syracuseStep 5164271 = 7746407) B7746407
theorem B3442847 : Blo 2293435 3442847 := bstep (se 1 (by rfl) ⟨2582135, by rfl⟩ : syracuseStep 3442847 = 5164271) B5164271
theorem B2295231 : Blo 2293435 2295231 := bstep (se 1 (by rfl) ⟨1721423, by rfl⟩ : syracuseStep 2295231 = 3442847) B3442847
theorem B3442853 : Blo 2293435 3442853 := bbase (se 4 (by rfl) ⟨322767, by rfl⟩ : syracuseStep 3442853 = 645535) (by norm_num)
theorem B2295235 : Blo 2293435 2295235 := bstep (se 1 (by rfl) ⟨1721426, by rfl⟩ : syracuseStep 2295235 = 3442853) B3442853
theorem B2904913 : Blo 2293435 2904913 := bbase (se 2 (by rfl) ⟨1089342, by rfl⟩ : syracuseStep 2904913 = 2178685) (by norm_num)
theorem B3873217 : Blo 2293435 3873217 := bstep (se 2 (by rfl) ⟨1452456, by rfl⟩ : syracuseStep 3873217 = 2904913) B2904913
theorem B5164289 : Blo 2293435 5164289 := bstep (se 2 (by rfl) ⟨1936608, by rfl⟩ : syracuseStep 5164289 = 3873217) B3873217
theorem B3442859 : Blo 2293435 3442859 := bstep (se 1 (by rfl) ⟨2582144, by rfl⟩ : syracuseStep 3442859 = 5164289) B5164289
theorem B2295239 : Blo 2293435 2295239 := bstep (se 1 (by rfl) ⟨1721429, by rfl⟩ : syracuseStep 2295239 = 3442859) B3442859
theorem B2582149 : Blo 2293435 2582149 := bbase (se 4 (by rfl) ⟨242076, by rfl⟩ : syracuseStep 2582149 = 484153) (by norm_num)
theorem B3442865 : Blo 2293435 3442865 := bstep (se 2 (by rfl) ⟨1291074, by rfl⟩ : syracuseStep 3442865 = 2582149) B2582149
theorem B2295243 : Blo 2293435 2295243 := bstep (se 1 (by rfl) ⟨1721432, by rfl⟩ : syracuseStep 2295243 = 3442865) B3442865
theorem B3102085 : Blo 2293435 3102085 := bbase (se 4 (by rfl) ⟨290820, by rfl⟩ : syracuseStep 3102085 = 581641) (by norm_num)
theorem B4136113 : Blo 2293435 4136113 := bstep (se 2 (by rfl) ⟨1551042, by rfl⟩ : syracuseStep 4136113 = 3102085) B3102085
theorem B5514817 : Blo 2293435 5514817 := bstep (se 2 (by rfl) ⟨2068056, by rfl⟩ : syracuseStep 5514817 = 4136113) B4136113
theorem B7353089 : Blo 2293435 7353089 := bstep (se 2 (by rfl) ⟨2757408, by rfl⟩ : syracuseStep 7353089 = 5514817) B5514817
theorem B4902059 : Blo 2293435 4902059 := bstep (se 1 (by rfl) ⟨3676544, by rfl⟩ : syracuseStep 4902059 = 7353089) B7353089
theorem B3268039 : Blo 2293435 3268039 := bstep (se 1 (by rfl) ⟨2451029, by rfl⟩ : syracuseStep 3268039 = 4902059) B4902059
theorem B4357385 : Blo 2293435 4357385 := bstep (se 2 (by rfl) ⟨1634019, by rfl⟩ : syracuseStep 4357385 = 3268039) B3268039
theorem B2904923 : Blo 2293435 2904923 := bstep (se 1 (by rfl) ⟨2178692, by rfl⟩ : syracuseStep 2904923 = 4357385) B4357385
theorem B7746461 : Blo 2293435 7746461 := bstep (se 3 (by rfl) ⟨1452461, by rfl⟩ : syracuseStep 7746461 = 2904923) B2904923
theorem B5164307 : Blo 2293435 5164307 := bstep (se 1 (by rfl) ⟨3873230, by rfl⟩ : syracuseStep 5164307 = 7746461) B7746461
theorem B3442871 : Blo 2293435 3442871 := bstep (se 1 (by rfl) ⟨2582153, by rfl⟩ : syracuseStep 3442871 = 5164307) B5164307
theorem B2295247 : Blo 2293435 2295247 := bstep (se 1 (by rfl) ⟨1721435, by rfl⟩ : syracuseStep 2295247 = 3442871) B3442871
theorem B3442877 : Blo 2293435 3442877 := bbase (se 3 (by rfl) ⟨645539, by rfl⟩ : syracuseStep 3442877 = 1291079) (by norm_num)
theorem B2295251 : Blo 2293435 2295251 := bstep (se 1 (by rfl) ⟨1721438, by rfl⟩ : syracuseStep 2295251 = 3442877) B3442877
theorem B5164325 : Blo 2293435 5164325 := bbase (se 4 (by rfl) ⟨484155, by rfl⟩ : syracuseStep 5164325 = 968311) (by norm_num)
theorem B3442883 : Blo 2293435 3442883 := bstep (se 1 (by rfl) ⟨2582162, by rfl⟩ : syracuseStep 3442883 = 5164325) B5164325
theorem B2295255 : Blo 2293435 2295255 := bstep (se 1 (by rfl) ⟨1721441, by rfl⟩ : syracuseStep 2295255 = 3442883) B3442883
theorem B5809877 : Blo 2293435 5809877 := bbase (se 7 (by rfl) ⟨68084, by rfl⟩ : syracuseStep 5809877 = 136169) (by norm_num)
theorem B3873251 : Blo 2293435 3873251 := bstep (se 1 (by rfl) ⟨2904938, by rfl⟩ : syracuseStep 3873251 = 5809877) B5809877
theorem B2582167 : Blo 2293435 2582167 := bstep (se 1 (by rfl) ⟨1936625, by rfl⟩ : syracuseStep 2582167 = 3873251) B3873251
theorem B3442889 : Blo 2293435 3442889 := bstep (se 2 (by rfl) ⟨1291083, by rfl⟩ : syracuseStep 3442889 = 2582167) B2582167
theorem B2295259 : Blo 2293435 2295259 := bstep (se 1 (by rfl) ⟨1721444, by rfl⟩ : syracuseStep 2295259 = 3442889) B3442889
theorem B4136141 : Blo 2293435 4136141 := bbase (se 3 (by rfl) ⟨775526, by rfl⟩ : syracuseStep 4136141 = 1551053) (by norm_num)
theorem B11029709 : Blo 2293435 11029709 := bstep (se 3 (by rfl) ⟨2068070, by rfl⟩ : syracuseStep 11029709 = 4136141) B4136141
theorem B7353139 : Blo 2293435 7353139 := bstep (se 1 (by rfl) ⟨5514854, by rfl⟩ : syracuseStep 7353139 = 11029709) B11029709
theorem B9804185 : Blo 2293435 9804185 := bstep (se 2 (by rfl) ⟨3676569, by rfl⟩ : syracuseStep 9804185 = 7353139) B7353139
theorem B6536123 : Blo 2293435 6536123 := bstep (se 1 (by rfl) ⟨4902092, by rfl⟩ : syracuseStep 6536123 = 9804185) B9804185
theorem B4357415 : Blo 2293435 4357415 := bstep (se 1 (by rfl) ⟨3268061, by rfl⟩ : syracuseStep 4357415 = 6536123) B6536123
theorem B11619773 : Blo 2293435 11619773 := bstep (se 3 (by rfl) ⟨2178707, by rfl⟩ : syracuseStep 11619773 = 4357415) B4357415
theorem B7746515 : Blo 2293435 7746515 := bstep (se 1 (by rfl) ⟨5809886, by rfl⟩ : syracuseStep 7746515 = 11619773) B11619773
theorem B5164343 : Blo 2293435 5164343 := bstep (se 1 (by rfl) ⟨3873257, by rfl⟩ : syracuseStep 5164343 = 7746515) B7746515
theorem B3442895 : Blo 2293435 3442895 := bstep (se 1 (by rfl) ⟨2582171, by rfl⟩ : syracuseStep 3442895 = 5164343) B5164343
theorem B2295263 : Blo 2293435 2295263 := bstep (se 1 (by rfl) ⟨1721447, by rfl⟩ : syracuseStep 2295263 = 3442895) B3442895
theorem B3442901 : Blo 2293435 3442901 := bbase (se 7 (by rfl) ⟨40346, by rfl⟩ : syracuseStep 3442901 = 80693) (by norm_num)
theorem B2295267 : Blo 2293435 2295267 := bstep (se 1 (by rfl) ⟨1721450, by rfl⟩ : syracuseStep 2295267 = 3442901) B3442901
theorem B6979765 : Blo 2293435 6979765 := bbase (se 5 (by rfl) ⟨327176, by rfl⟩ : syracuseStep 6979765 = 654353) (by norm_num)
theorem B9306353 : Blo 2293435 9306353 := bstep (se 2 (by rfl) ⟨3489882, by rfl⟩ : syracuseStep 9306353 = 6979765) B6979765
theorem B6204235 : Blo 2293435 6204235 := bstep (se 1 (by rfl) ⟨4653176, by rfl⟩ : syracuseStep 6204235 = 9306353) B9306353
theorem B8272313 : Blo 2293435 8272313 := bstep (se 2 (by rfl) ⟨3102117, by rfl⟩ : syracuseStep 8272313 = 6204235) B6204235
theorem B5514875 : Blo 2293435 5514875 := bstep (se 1 (by rfl) ⟨4136156, by rfl⟩ : syracuseStep 5514875 = 8272313) B8272313
theorem B3676583 : Blo 2293435 3676583 := bstep (se 1 (by rfl) ⟨2757437, by rfl⟩ : syracuseStep 3676583 = 5514875) B5514875
theorem B2451055 : Blo 2293435 2451055 := bstep (se 1 (by rfl) ⟨1838291, by rfl⟩ : syracuseStep 2451055 = 3676583) B3676583
theorem B3268073 : Blo 2293435 3268073 := bstep (se 2 (by rfl) ⟨1225527, by rfl⟩ : syracuseStep 3268073 = 2451055) B2451055
theorem B8714861 : Blo 2293435 8714861 := bstep (se 3 (by rfl) ⟨1634036, by rfl⟩ : syracuseStep 8714861 = 3268073) B3268073
theorem B5809907 : Blo 2293435 5809907 := bstep (se 1 (by rfl) ⟨4357430, by rfl⟩ : syracuseStep 5809907 = 8714861) B8714861
theorem B3873271 : Blo 2293435 3873271 := bstep (se 1 (by rfl) ⟨2904953, by rfl⟩ : syracuseStep 3873271 = 5809907) B5809907
theorem B5164361 : Blo 2293435 5164361 := bstep (se 2 (by rfl) ⟨1936635, by rfl⟩ : syracuseStep 5164361 = 3873271) B3873271
theorem B3442907 : Blo 2293435 3442907 := bstep (se 1 (by rfl) ⟨2582180, by rfl⟩ : syracuseStep 3442907 = 5164361) B5164361
theorem B2295271 : Blo 2293435 2295271 := bstep (se 1 (by rfl) ⟨1721453, by rfl⟩ : syracuseStep 2295271 = 3442907) B3442907
theorem B2582185 : Blo 2293435 2582185 := bbase (se 2 (by rfl) ⟨968319, by rfl⟩ : syracuseStep 2582185 = 1936639) (by norm_num)
theorem B3442913 : Blo 2293435 3442913 := bstep (se 2 (by rfl) ⟨1291092, by rfl⟩ : syracuseStep 3442913 = 2582185) B2582185
theorem B2295275 : Blo 2293435 2295275 := bstep (se 1 (by rfl) ⟨1721456, by rfl⟩ : syracuseStep 2295275 = 3442913) B3442913
theorem B5514893 : Blo 2293435 5514893 := bbase (se 3 (by rfl) ⟨1034042, by rfl⟩ : syracuseStep 5514893 = 2068085) (by norm_num)
theorem B3676595 : Blo 2293435 3676595 := bstep (se 1 (by rfl) ⟨2757446, by rfl⟩ : syracuseStep 3676595 = 5514893) B5514893
theorem B9804253 : Blo 2293435 9804253 := bstep (se 3 (by rfl) ⟨1838297, by rfl⟩ : syracuseStep 9804253 = 3676595) B3676595
theorem B13072337 : Blo 2293435 13072337 := bstep (se 2 (by rfl) ⟨4902126, by rfl⟩ : syracuseStep 13072337 = 9804253) B9804253
theorem B8714891 : Blo 2293435 8714891 := bstep (se 1 (by rfl) ⟨6536168, by rfl⟩ : syracuseStep 8714891 = 13072337) B13072337
theorem B5809927 : Blo 2293435 5809927 := bstep (se 1 (by rfl) ⟨4357445, by rfl⟩ : syracuseStep 5809927 = 8714891) B8714891
theorem B7746569 : Blo 2293435 7746569 := bstep (se 2 (by rfl) ⟨2904963, by rfl⟩ : syracuseStep 7746569 = 5809927) B5809927
theorem B5164379 : Blo 2293435 5164379 := bstep (se 1 (by rfl) ⟨3873284, by rfl⟩ : syracuseStep 5164379 = 7746569) B7746569
theorem B3442919 : Blo 2293435 3442919 := bstep (se 1 (by rfl) ⟨2582189, by rfl⟩ : syracuseStep 3442919 = 5164379) B5164379
theorem B2295279 : Blo 2293435 2295279 := bstep (se 1 (by rfl) ⟨1721459, by rfl⟩ : syracuseStep 2295279 = 3442919) B3442919
theorem B3442925 : Blo 2293435 3442925 := bbase (se 3 (by rfl) ⟨645548, by rfl⟩ : syracuseStep 3442925 = 1291097) (by norm_num)
theorem B2295283 : Blo 2293435 2295283 := bstep (se 1 (by rfl) ⟨1721462, by rfl⟩ : syracuseStep 2295283 = 3442925) B3442925
theorem B5164397 : Blo 2293435 5164397 := bbase (se 3 (by rfl) ⟨968324, by rfl⟩ : syracuseStep 5164397 = 1936649) (by norm_num)
theorem B3442931 : Blo 2293435 3442931 := bstep (se 1 (by rfl) ⟨2582198, by rfl⟩ : syracuseStep 3442931 = 5164397) B5164397
theorem B2295287 : Blo 2293435 2295287 := bstep (se 1 (by rfl) ⟨1721465, by rfl⟩ : syracuseStep 2295287 = 3442931) B3442931
theorem B4357469 : Blo 2293435 4357469 := bbase (se 3 (by rfl) ⟨817025, by rfl⟩ : syracuseStep 4357469 = 1634051) (by norm_num)
theorem B2904979 : Blo 2293435 2904979 := bstep (se 1 (by rfl) ⟨2178734, by rfl⟩ : syracuseStep 2904979 = 4357469) B4357469
theorem B3873305 : Blo 2293435 3873305 := bstep (se 2 (by rfl) ⟨1452489, by rfl⟩ : syracuseStep 3873305 = 2904979) B2904979
theorem B2582203 : Blo 2293435 2582203 := bstep (se 1 (by rfl) ⟨1936652, by rfl⟩ : syracuseStep 2582203 = 3873305) B3873305
theorem B3442937 : Blo 2293435 3442937 := bstep (se 2 (by rfl) ⟨1291101, by rfl⟩ : syracuseStep 3442937 = 2582203) B2582203
theorem B2295291 : Blo 2293435 2295291 := bstep (se 1 (by rfl) ⟨1721468, by rfl⟩ : syracuseStep 2295291 = 3442937) B3442937
theorem B11029861 : Blo 2293435 11029861 := bbase (se 4 (by rfl) ⟨1034049, by rfl⟩ : syracuseStep 11029861 = 2068099) (by norm_num)
theorem B58825925 : Blo 2293435 58825925 := bstep (se 4 (by rfl) ⟨5514930, by rfl⟩ : syracuseStep 58825925 = 11029861) B11029861
theorem B39217283 : Blo 2293435 39217283 := bstep (se 1 (by rfl) ⟨29412962, by rfl⟩ : syracuseStep 39217283 = 58825925) B58825925
theorem B26144855 : Blo 2293435 26144855 := bstep (se 1 (by rfl) ⟨19608641, by rfl⟩ : syracuseStep 26144855 = 39217283) B39217283
theorem B17429903 : Blo 2293435 17429903 := bstep (se 1 (by rfl) ⟨13072427, by rfl⟩ : syracuseStep 17429903 = 26144855) B26144855
theorem B11619935 : Blo 2293435 11619935 := bstep (se 1 (by rfl) ⟨8714951, by rfl⟩ : syracuseStep 11619935 = 17429903) B17429903
theorem B7746623 : Blo 2293435 7746623 := bstep (se 1 (by rfl) ⟨5809967, by rfl⟩ : syracuseStep 7746623 = 11619935) B11619935
theorem B5164415 : Blo 2293435 5164415 := bstep (se 1 (by rfl) ⟨3873311, by rfl⟩ : syracuseStep 5164415 = 7746623) B7746623
theorem B3442943 : Blo 2293435 3442943 := bstep (se 1 (by rfl) ⟨2582207, by rfl⟩ : syracuseStep 3442943 = 5164415) B5164415
theorem B2295295 : Blo 2293435 2295295 := bstep (se 1 (by rfl) ⟨1721471, by rfl⟩ : syracuseStep 2295295 = 3442943) B3442943
theorem B3442949 : Blo 2293435 3442949 := bbase (se 4 (by rfl) ⟨322776, by rfl⟩ : syracuseStep 3442949 = 645553) (by norm_num)
theorem B2295299 : Blo 2293435 2295299 := bstep (se 1 (by rfl) ⟨1721474, by rfl⟩ : syracuseStep 2295299 = 3442949) B3442949
theorem B3873325 : Blo 2293435 3873325 := bbase (se 3 (by rfl) ⟨726248, by rfl⟩ : syracuseStep 3873325 = 1452497) (by norm_num)
theorem B5164433 : Blo 2293435 5164433 := bstep (se 2 (by rfl) ⟨1936662, by rfl⟩ : syracuseStep 5164433 = 3873325) B3873325
theorem B3442955 : Blo 2293435 3442955 := bstep (se 1 (by rfl) ⟨2582216, by rfl⟩ : syracuseStep 3442955 = 5164433) B5164433
theorem B2295303 : Blo 2293435 2295303 := bstep (se 1 (by rfl) ⟨1721477, by rfl⟩ : syracuseStep 2295303 = 3442955) B3442955
theorem B2582221 : Blo 2293435 2582221 := bbase (se 3 (by rfl) ⟨484166, by rfl⟩ : syracuseStep 2582221 = 968333) (by norm_num)
theorem B3442961 : Blo 2293435 3442961 := bstep (se 2 (by rfl) ⟨1291110, by rfl⟩ : syracuseStep 3442961 = 2582221) B2582221
theorem B2295307 : Blo 2293435 2295307 := bstep (se 1 (by rfl) ⟨1721480, by rfl⟩ : syracuseStep 2295307 = 3442961) B3442961
theorem B7746677 : Blo 2293435 7746677 := bbase (se 5 (by rfl) ⟨363125, by rfl⟩ : syracuseStep 7746677 = 726251) (by norm_num)
theorem B5164451 : Blo 2293435 5164451 := bstep (se 1 (by rfl) ⟨3873338, by rfl⟩ : syracuseStep 5164451 = 7746677) B7746677
theorem B3442967 : Blo 2293435 3442967 := bstep (se 1 (by rfl) ⟨2582225, by rfl⟩ : syracuseStep 3442967 = 5164451) B5164451
theorem B2295311 : Blo 2293435 2295311 := bstep (se 1 (by rfl) ⟨1721483, by rfl⟩ : syracuseStep 2295311 = 3442967) B3442967
theorem B3442973 : Blo 2293435 3442973 := bbase (se 3 (by rfl) ⟨645557, by rfl⟩ : syracuseStep 3442973 = 1291115) (by norm_num)
theorem B2295315 : Blo 2293435 2295315 := bstep (se 1 (by rfl) ⟨1721486, by rfl⟩ : syracuseStep 2295315 = 3442973) B3442973
theorem B5164469 : Blo 2293435 5164469 := bbase (se 5 (by rfl) ⟨242084, by rfl⟩ : syracuseStep 5164469 = 484169) (by norm_num)
theorem B3442979 : Blo 2293435 3442979 := bstep (se 1 (by rfl) ⟨2582234, by rfl⟩ : syracuseStep 3442979 = 5164469) B5164469
theorem B2295319 : Blo 2293435 2295319 := bstep (se 1 (by rfl) ⟨1721489, by rfl⟩ : syracuseStep 2295319 = 3442979) B3442979
theorem B4902221 : Blo 2293435 4902221 := bbase (se 3 (by rfl) ⟨919166, by rfl⟩ : syracuseStep 4902221 = 1838333) (by norm_num)
theorem B13072589 : Blo 2293435 13072589 := bstep (se 3 (by rfl) ⟨2451110, by rfl⟩ : syracuseStep 13072589 = 4902221) B4902221
theorem B8715059 : Blo 2293435 8715059 := bstep (se 1 (by rfl) ⟨6536294, by rfl⟩ : syracuseStep 8715059 = 13072589) B13072589
theorem B5810039 : Blo 2293435 5810039 := bstep (se 1 (by rfl) ⟨4357529, by rfl⟩ : syracuseStep 5810039 = 8715059) B8715059
theorem B3873359 : Blo 2293435 3873359 := bstep (se 1 (by rfl) ⟨2905019, by rfl⟩ : syracuseStep 3873359 = 5810039) B5810039
theorem B2582239 : Blo 2293435 2582239 := bstep (se 1 (by rfl) ⟨1936679, by rfl⟩ : syracuseStep 2582239 = 3873359) B3873359
theorem B3442985 : Blo 2293435 3442985 := bstep (se 2 (by rfl) ⟨1291119, by rfl⟩ : syracuseStep 3442985 = 2582239) B2582239
theorem B2295323 : Blo 2293435 2295323 := bstep (se 1 (by rfl) ⟨1721492, by rfl⟩ : syracuseStep 2295323 = 3442985) B3442985
theorem B4902229 : Blo 2293435 4902229 := bbase (se 11 (by rfl) ⟨3590, by rfl⟩ : syracuseStep 4902229 = 7181) (by norm_num)
theorem B6536305 : Blo 2293435 6536305 := bstep (se 2 (by rfl) ⟨2451114, by rfl⟩ : syracuseStep 6536305 = 4902229) B4902229
theorem B8715073 : Blo 2293435 8715073 := bstep (se 2 (by rfl) ⟨3268152, by rfl⟩ : syracuseStep 8715073 = 6536305) B6536305
theorem B11620097 : Blo 2293435 11620097 := bstep (se 2 (by rfl) ⟨4357536, by rfl⟩ : syracuseStep 11620097 = 8715073) B8715073
theorem B7746731 : Blo 2293435 7746731 := bstep (se 1 (by rfl) ⟨5810048, by rfl⟩ : syracuseStep 7746731 = 11620097) B11620097
theorem B5164487 : Blo 2293435 5164487 := bstep (se 1 (by rfl) ⟨3873365, by rfl⟩ : syracuseStep 5164487 = 7746731) B7746731
theorem B3442991 : Blo 2293435 3442991 := bstep (se 1 (by rfl) ⟨2582243, by rfl⟩ : syracuseStep 3442991 = 5164487) B5164487
theorem B2295327 : Blo 2293435 2295327 := bstep (se 1 (by rfl) ⟨1721495, by rfl⟩ : syracuseStep 2295327 = 3442991) B3442991
theorem B3442997 : Blo 2293435 3442997 := bbase (se 5 (by rfl) ⟨161390, by rfl⟩ : syracuseStep 3442997 = 322781) (by norm_num)
theorem B2295331 : Blo 2293435 2295331 := bstep (se 1 (by rfl) ⟨1721498, by rfl⟩ : syracuseStep 2295331 = 3442997) B3442997
theorem B5810069 : Blo 2293435 5810069 := bbase (se 6 (by rfl) ⟨136173, by rfl⟩ : syracuseStep 5810069 = 272347) (by norm_num)
theorem B3873379 : Blo 2293435 3873379 := bstep (se 1 (by rfl) ⟨2905034, by rfl⟩ : syracuseStep 3873379 = 5810069) B5810069
theorem B5164505 : Blo 2293435 5164505 := bstep (se 2 (by rfl) ⟨1936689, by rfl⟩ : syracuseStep 5164505 = 3873379) B3873379
theorem B3443003 : Blo 2293435 3443003 := bstep (se 1 (by rfl) ⟨2582252, by rfl⟩ : syracuseStep 3443003 = 5164505) B5164505
theorem B2295335 : Blo 2293435 2295335 := bstep (se 1 (by rfl) ⟨1721501, by rfl⟩ : syracuseStep 2295335 = 3443003) B3443003
theorem B2582257 : Blo 2293435 2582257 := bbase (se 2 (by rfl) ⟨968346, by rfl⟩ : syracuseStep 2582257 = 1936693) (by norm_num)
theorem B3443009 : Blo 2293435 3443009 := bstep (se 2 (by rfl) ⟨1291128, by rfl⟩ : syracuseStep 3443009 = 2582257) B2582257
theorem B2295339 : Blo 2293435 2295339 := bstep (se 1 (by rfl) ⟨1721504, by rfl⟩ : syracuseStep 2295339 = 3443009) B3443009
theorem B11180581 : Blo 2293435 11180581 := bbase (se 4 (by rfl) ⟨1048179, by rfl⟩ : syracuseStep 11180581 = 2096359) (by norm_num)
theorem B59629765 : Blo 2293435 59629765 := bstep (se 4 (by rfl) ⟨5590290, by rfl⟩ : syracuseStep 59629765 = 11180581) B11180581
theorem B79506353 : Blo 2293435 79506353 := bstep (se 2 (by rfl) ⟨29814882, by rfl⟩ : syracuseStep 79506353 = 59629765) B59629765
theorem B53004235 : Blo 2293435 53004235 := bstep (se 1 (by rfl) ⟨39753176, by rfl⟩ : syracuseStep 53004235 = 79506353) B79506353
theorem B70672313 : Blo 2293435 70672313 := bstep (se 2 (by rfl) ⟨26502117, by rfl⟩ : syracuseStep 70672313 = 53004235) B53004235
theorem B47114875 : Blo 2293435 47114875 := bstep (se 1 (by rfl) ⟨35336156, by rfl⟩ : syracuseStep 47114875 = 70672313) B70672313
theorem B62819833 : Blo 2293435 62819833 := bstep (se 2 (by rfl) ⟨23557437, by rfl⟩ : syracuseStep 62819833 = 47114875) B47114875
theorem B83759777 : Blo 2293435 83759777 := bstep (se 2 (by rfl) ⟨31409916, by rfl⟩ : syracuseStep 83759777 = 62819833) B62819833
theorem B55839851 : Blo 2293435 55839851 := bstep (se 1 (by rfl) ⟨41879888, by rfl⟩ : syracuseStep 55839851 = 83759777) B83759777
theorem B37226567 : Blo 2293435 37226567 := bstep (se 1 (by rfl) ⟨27919925, by rfl⟩ : syracuseStep 37226567 = 55839851) B55839851
theorem B24817711 : Blo 2293435 24817711 := bstep (se 1 (by rfl) ⟨18613283, by rfl⟩ : syracuseStep 24817711 = 37226567) B37226567
theorem B33090281 : Blo 2293435 33090281 := bstep (se 2 (by rfl) ⟨12408855, by rfl⟩ : syracuseStep 33090281 = 24817711) B24817711
theorem B22060187 : Blo 2293435 22060187 := bstep (se 1 (by rfl) ⟨16545140, by rfl⟩ : syracuseStep 22060187 = 33090281) B33090281
theorem B14706791 : Blo 2293435 14706791 := bstep (se 1 (by rfl) ⟨11030093, by rfl⟩ : syracuseStep 14706791 = 22060187) B22060187
theorem B9804527 : Blo 2293435 9804527 := bstep (se 1 (by rfl) ⟨7353395, by rfl⟩ : syracuseStep 9804527 = 14706791) B14706791
theorem B6536351 : Blo 2293435 6536351 := bstep (se 1 (by rfl) ⟨4902263, by rfl⟩ : syracuseStep 6536351 = 9804527) B9804527
theorem B4357567 : Blo 2293435 4357567 := bstep (se 1 (by rfl) ⟨3268175, by rfl⟩ : syracuseStep 4357567 = 6536351) B6536351
theorem B5810089 : Blo 2293435 5810089 := bstep (se 2 (by rfl) ⟨2178783, by rfl⟩ : syracuseStep 5810089 = 4357567) B4357567
theorem B7746785 : Blo 2293435 7746785 := bstep (se 2 (by rfl) ⟨2905044, by rfl⟩ : syracuseStep 7746785 = 5810089) B5810089
theorem B5164523 : Blo 2293435 5164523 := bstep (se 1 (by rfl) ⟨3873392, by rfl⟩ : syracuseStep 5164523 = 7746785) B7746785
theorem B3443015 : Blo 2293435 3443015 := bstep (se 1 (by rfl) ⟨2582261, by rfl⟩ : syracuseStep 3443015 = 5164523) B5164523
theorem B2295343 : Blo 2293435 2295343 := bstep (se 1 (by rfl) ⟨1721507, by rfl⟩ : syracuseStep 2295343 = 3443015) B3443015
theorem B3443021 : Blo 2293435 3443021 := bbase (se 3 (by rfl) ⟨645566, by rfl⟩ : syracuseStep 3443021 = 1291133) (by norm_num)
theorem B2295347 : Blo 2293435 2295347 := bstep (se 1 (by rfl) ⟨1721510, by rfl⟩ : syracuseStep 2295347 = 3443021) B3443021
theorem B5164541 : Blo 2293435 5164541 := bbase (se 3 (by rfl) ⟨968351, by rfl⟩ : syracuseStep 5164541 = 1936703) (by norm_num)
theorem B3443027 : Blo 2293435 3443027 := bstep (se 1 (by rfl) ⟨2582270, by rfl⟩ : syracuseStep 3443027 = 5164541) B5164541
theorem B2295351 : Blo 2293435 2295351 := bstep (se 1 (by rfl) ⟨1721513, by rfl⟩ : syracuseStep 2295351 = 3443027) B3443027
theorem B3873413 : Blo 2293435 3873413 := bbase (se 4 (by rfl) ⟨363132, by rfl⟩ : syracuseStep 3873413 = 726265) (by norm_num)
theorem B2582275 : Blo 2293435 2582275 := bstep (se 1 (by rfl) ⟨1936706, by rfl⟩ : syracuseStep 2582275 = 3873413) B3873413
theorem B3443033 : Blo 2293435 3443033 := bstep (se 2 (by rfl) ⟨1291137, by rfl⟩ : syracuseStep 3443033 = 2582275) B2582275
theorem B2295355 : Blo 2293435 2295355 := bstep (se 1 (by rfl) ⟨1721516, by rfl⟩ : syracuseStep 2295355 = 3443033) B3443033
theorem B17430389 : Blo 2293435 17430389 := bbase (se 5 (by rfl) ⟨817049, by rfl⟩ : syracuseStep 17430389 = 1634099) (by norm_num)
theorem B11620259 : Blo 2293435 11620259 := bstep (se 1 (by rfl) ⟨8715194, by rfl⟩ : syracuseStep 11620259 = 17430389) B17430389
theorem B7746839 : Blo 2293435 7746839 := bstep (se 1 (by rfl) ⟨5810129, by rfl⟩ : syracuseStep 7746839 = 11620259) B11620259
theorem B5164559 : Blo 2293435 5164559 := bstep (se 1 (by rfl) ⟨3873419, by rfl⟩ : syracuseStep 5164559 = 7746839) B7746839
theorem B3443039 : Blo 2293435 3443039 := bstep (se 1 (by rfl) ⟨2582279, by rfl⟩ : syracuseStep 3443039 = 5164559) B5164559
theorem B2295359 : Blo 2293435 2295359 := bstep (se 1 (by rfl) ⟨1721519, by rfl⟩ : syracuseStep 2295359 = 3443039) B3443039
theorem B3443045 : Blo 2293435 3443045 := bbase (se 4 (by rfl) ⟨322785, by rfl⟩ : syracuseStep 3443045 = 645571) (by norm_num)
theorem B2295363 : Blo 2293435 2295363 := bstep (se 1 (by rfl) ⟨1721522, by rfl⟩ : syracuseStep 2295363 = 3443045) B3443045
theorem B4357613 : Blo 2293435 4357613 := bbase (se 3 (by rfl) ⟨817052, by rfl⟩ : syracuseStep 4357613 = 1634105) (by norm_num)
theorem B2905075 : Blo 2293435 2905075 := bstep (se 1 (by rfl) ⟨2178806, by rfl⟩ : syracuseStep 2905075 = 4357613) B4357613
theorem B3873433 : Blo 2293435 3873433 := bstep (se 2 (by rfl) ⟨1452537, by rfl⟩ : syracuseStep 3873433 = 2905075) B2905075
theorem B5164577 : Blo 2293435 5164577 := bstep (se 2 (by rfl) ⟨1936716, by rfl⟩ : syracuseStep 5164577 = 3873433) B3873433
theorem B3443051 : Blo 2293435 3443051 := bstep (se 1 (by rfl) ⟨2582288, by rfl⟩ : syracuseStep 3443051 = 5164577) B5164577
theorem B2295367 : Blo 2293435 2295367 := bstep (se 1 (by rfl) ⟨1721525, by rfl⟩ : syracuseStep 2295367 = 3443051) B3443051
theorem B2582293 : Blo 2293435 2582293 := bbase (se 6 (by rfl) ⟨60522, by rfl⟩ : syracuseStep 2582293 = 121045) (by norm_num)
theorem B3443057 : Blo 2293435 3443057 := bstep (se 2 (by rfl) ⟨1291146, by rfl⟩ : syracuseStep 3443057 = 2582293) B2582293
theorem B2295371 : Blo 2293435 2295371 := bstep (se 1 (by rfl) ⟨1721528, by rfl⟩ : syracuseStep 2295371 = 3443057) B3443057
theorem B2905085 : Blo 2293435 2905085 := bbase (se 3 (by rfl) ⟨544703, by rfl⟩ : syracuseStep 2905085 = 1089407) (by norm_num)
theorem B7746893 : Blo 2293435 7746893 := bstep (se 3 (by rfl) ⟨1452542, by rfl⟩ : syracuseStep 7746893 = 2905085) B2905085
theorem B5164595 : Blo 2293435 5164595 := bstep (se 1 (by rfl) ⟨3873446, by rfl⟩ : syracuseStep 5164595 = 7746893) B7746893
theorem B3443063 : Blo 2293435 3443063 := bstep (se 1 (by rfl) ⟨2582297, by rfl⟩ : syracuseStep 3443063 = 5164595) B5164595
theorem B2295375 : Blo 2293435 2295375 := bstep (se 1 (by rfl) ⟨1721531, by rfl⟩ : syracuseStep 2295375 = 3443063) B3443063
theorem B3443069 : Blo 2293435 3443069 := bbase (se 3 (by rfl) ⟨645575, by rfl⟩ : syracuseStep 3443069 = 1291151) (by norm_num)
theorem B2295379 : Blo 2293435 2295379 := bstep (se 1 (by rfl) ⟨1721534, by rfl⟩ : syracuseStep 2295379 = 3443069) B3443069
theorem B5164613 : Blo 2293435 5164613 := bbase (se 4 (by rfl) ⟨484182, by rfl⟩ : syracuseStep 5164613 = 968365) (by norm_num)
theorem B3443075 : Blo 2293435 3443075 := bstep (se 1 (by rfl) ⟨2582306, by rfl⟩ : syracuseStep 3443075 = 5164613) B5164613
theorem B2295383 : Blo 2293435 2295383 := bstep (se 1 (by rfl) ⟨1721537, by rfl⟩ : syracuseStep 2295383 = 3443075) B3443075
theorem B2757577 : Blo 2293435 2757577 := bbase (se 2 (by rfl) ⟨1034091, by rfl⟩ : syracuseStep 2757577 = 2068183) (by norm_num)
theorem B3676769 : Blo 2293435 3676769 := bstep (se 2 (by rfl) ⟨1378788, by rfl⟩ : syracuseStep 3676769 = 2757577) B2757577
theorem B2451179 : Blo 2293435 2451179 := bstep (se 1 (by rfl) ⟨1838384, by rfl⟩ : syracuseStep 2451179 = 3676769) B3676769
theorem B6536477 : Blo 2293435 6536477 := bstep (se 3 (by rfl) ⟨1225589, by rfl⟩ : syracuseStep 6536477 = 2451179) B2451179
theorem B4357651 : Blo 2293435 4357651 := bstep (se 1 (by rfl) ⟨3268238, by rfl⟩ : syracuseStep 4357651 = 6536477) B6536477
theorem B5810201 : Blo 2293435 5810201 := bstep (se 2 (by rfl) ⟨2178825, by rfl⟩ : syracuseStep 5810201 = 4357651) B4357651
theorem B3873467 : Blo 2293435 3873467 := bstep (se 1 (by rfl) ⟨2905100, by rfl⟩ : syracuseStep 3873467 = 5810201) B5810201
theorem B2582311 : Blo 2293435 2582311 := bstep (se 1 (by rfl) ⟨1936733, by rfl⟩ : syracuseStep 2582311 = 3873467) B3873467
theorem B3443081 : Blo 2293435 3443081 := bstep (se 2 (by rfl) ⟨1291155, by rfl⟩ : syracuseStep 3443081 = 2582311) B2582311
theorem B2295387 : Blo 2293435 2295387 := bstep (se 1 (by rfl) ⟨1721540, by rfl⟩ : syracuseStep 2295387 = 3443081) B3443081
theorem B11620421 : Blo 2293435 11620421 := bbase (se 4 (by rfl) ⟨1089414, by rfl⟩ : syracuseStep 11620421 = 2178829) (by norm_num)
theorem B7746947 : Blo 2293435 7746947 := bstep (se 1 (by rfl) ⟨5810210, by rfl⟩ : syracuseStep 7746947 = 11620421) B11620421
theorem B5164631 : Blo 2293435 5164631 := bstep (se 1 (by rfl) ⟨3873473, by rfl⟩ : syracuseStep 5164631 = 7746947) B7746947
theorem B3443087 : Blo 2293435 3443087 := bstep (se 1 (by rfl) ⟨2582315, by rfl⟩ : syracuseStep 3443087 = 5164631) B5164631
theorem B2295391 : Blo 2293435 2295391 := bstep (se 1 (by rfl) ⟨1721543, by rfl⟩ : syracuseStep 2295391 = 3443087) B3443087
theorem B3443093 : Blo 2293435 3443093 := bbase (se 6 (by rfl) ⟨80697, by rfl⟩ : syracuseStep 3443093 = 161395) (by norm_num)
theorem B2295395 : Blo 2293435 2295395 := bstep (se 1 (by rfl) ⟨1721546, by rfl⟩ : syracuseStep 2295395 = 3443093) B3443093
theorem B3358045 : Blo 2293435 3358045 := bbase (se 3 (by rfl) ⟨629633, by rfl⟩ : syracuseStep 3358045 = 1259267) (by norm_num)
theorem B4477393 : Blo 2293435 4477393 := bstep (se 2 (by rfl) ⟨1679022, by rfl⟩ : syracuseStep 4477393 = 3358045) B3358045
theorem B5969857 : Blo 2293435 5969857 := bstep (se 2 (by rfl) ⟨2238696, by rfl⟩ : syracuseStep 5969857 = 4477393) B4477393
theorem B7959809 : Blo 2293435 7959809 := bstep (se 2 (by rfl) ⟨2984928, by rfl⟩ : syracuseStep 7959809 = 5969857) B5969857
theorem B5306539 : Blo 2293435 5306539 := bstep (se 1 (by rfl) ⟨3979904, by rfl⟩ : syracuseStep 5306539 = 7959809) B7959809
theorem B7075385 : Blo 2293435 7075385 := bstep (se 2 (by rfl) ⟨2653269, by rfl⟩ : syracuseStep 7075385 = 5306539) B5306539
theorem B75470773 : Blo 2293435 75470773 := bstep (se 5 (by rfl) ⟨3537692, by rfl⟩ : syracuseStep 75470773 = 7075385) B7075385
theorem B100627697 : Blo 2293435 100627697 := bstep (se 2 (by rfl) ⟨37735386, by rfl⟩ : syracuseStep 100627697 = 75470773) B75470773
theorem B268340525 : Blo 2293435 268340525 := bstep (se 3 (by rfl) ⟨50313848, by rfl⟩ : syracuseStep 268340525 = 100627697) B100627697
theorem B178893683 : Blo 2293435 178893683 := bstep (se 1 (by rfl) ⟨134170262, by rfl⟩ : syracuseStep 178893683 = 268340525) B268340525
theorem B119262455 : Blo 2293435 119262455 := bstep (se 1 (by rfl) ⟨89446841, by rfl⟩ : syracuseStep 119262455 = 178893683) B178893683
theorem B79508303 : Blo 2293435 79508303 := bstep (se 1 (by rfl) ⟨59631227, by rfl⟩ : syracuseStep 79508303 = 119262455) B119262455
theorem B53005535 : Blo 2293435 53005535 := bstep (se 1 (by rfl) ⟨39754151, by rfl⟩ : syracuseStep 53005535 = 79508303) B79508303
theorem B35337023 : Blo 2293435 35337023 := bstep (se 1 (by rfl) ⟨26502767, by rfl⟩ : syracuseStep 35337023 = 53005535) B53005535
theorem B23558015 : Blo 2293435 23558015 := bstep (se 1 (by rfl) ⟨17668511, by rfl⟩ : syracuseStep 23558015 = 35337023) B35337023
theorem B15705343 : Blo 2293435 15705343 := bstep (se 1 (by rfl) ⟨11779007, by rfl⟩ : syracuseStep 15705343 = 23558015) B23558015
theorem B20940457 : Blo 2293435 20940457 := bstep (se 2 (by rfl) ⟨7852671, by rfl⟩ : syracuseStep 20940457 = 15705343) B15705343
theorem B27920609 : Blo 2293435 27920609 := bstep (se 2 (by rfl) ⟨10470228, by rfl⟩ : syracuseStep 27920609 = 20940457) B20940457
theorem B18613739 : Blo 2293435 18613739 := bstep (se 1 (by rfl) ⟨13960304, by rfl⟩ : syracuseStep 18613739 = 27920609) B27920609
theorem B12409159 : Blo 2293435 12409159 := bstep (se 1 (by rfl) ⟨9306869, by rfl⟩ : syracuseStep 12409159 = 18613739) B18613739
theorem B16545545 : Blo 2293435 16545545 := bstep (se 2 (by rfl) ⟨6204579, by rfl⟩ : syracuseStep 16545545 = 12409159) B12409159
theorem B11030363 : Blo 2293435 11030363 := bstep (se 1 (by rfl) ⟨8272772, by rfl⟩ : syracuseStep 11030363 = 16545545) B16545545
theorem B7353575 : Blo 2293435 7353575 := bstep (se 1 (by rfl) ⟨5515181, by rfl⟩ : syracuseStep 7353575 = 11030363) B11030363
theorem B4902383 : Blo 2293435 4902383 := bstep (se 1 (by rfl) ⟨3676787, by rfl⟩ : syracuseStep 4902383 = 7353575) B7353575
theorem B13073021 : Blo 2293435 13073021 := bstep (se 3 (by rfl) ⟨2451191, by rfl⟩ : syracuseStep 13073021 = 4902383) B4902383
theorem B8715347 : Blo 2293435 8715347 := bstep (se 1 (by rfl) ⟨6536510, by rfl⟩ : syracuseStep 8715347 = 13073021) B13073021
theorem B5810231 : Blo 2293435 5810231 := bstep (se 1 (by rfl) ⟨4357673, by rfl⟩ : syracuseStep 5810231 = 8715347) B8715347
theorem B3873487 : Blo 2293435 3873487 := bstep (se 1 (by rfl) ⟨2905115, by rfl⟩ : syracuseStep 3873487 = 5810231) B5810231
theorem B5164649 : Blo 2293435 5164649 := bstep (se 2 (by rfl) ⟨1936743, by rfl⟩ : syracuseStep 5164649 = 3873487) B3873487
theorem B3443099 : Blo 2293435 3443099 := bstep (se 1 (by rfl) ⟨2582324, by rfl⟩ : syracuseStep 3443099 = 5164649) B5164649
theorem B2295399 : Blo 2293435 2295399 := bstep (se 1 (by rfl) ⟨1721549, by rfl⟩ : syracuseStep 2295399 = 3443099) B3443099
theorem B2582329 : Blo 2293435 2582329 := bbase (se 2 (by rfl) ⟨968373, by rfl⟩ : syracuseStep 2582329 = 1936747) (by norm_num)
theorem B3443105 : Blo 2293435 3443105 := bstep (se 2 (by rfl) ⟨1291164, by rfl⟩ : syracuseStep 3443105 = 2582329) B2582329
theorem B2295403 : Blo 2293435 2295403 := bstep (se 1 (by rfl) ⟨1721552, by rfl⟩ : syracuseStep 2295403 = 3443105) B3443105
theorem B6536533 : Blo 2293435 6536533 := bbase (se 11 (by rfl) ⟨4787, by rfl⟩ : syracuseStep 6536533 = 9575) (by norm_num)
theorem B8715377 : Blo 2293435 8715377 := bstep (se 2 (by rfl) ⟨3268266, by rfl⟩ : syracuseStep 8715377 = 6536533) B6536533
theorem B5810251 : Blo 2293435 5810251 := bstep (se 1 (by rfl) ⟨4357688, by rfl⟩ : syracuseStep 5810251 = 8715377) B8715377
theorem B7747001 : Blo 2293435 7747001 := bstep (se 2 (by rfl) ⟨2905125, by rfl⟩ : syracuseStep 7747001 = 5810251) B5810251
theorem B5164667 : Blo 2293435 5164667 := bstep (se 1 (by rfl) ⟨3873500, by rfl⟩ : syracuseStep 5164667 = 7747001) B7747001
theorem B3443111 : Blo 2293435 3443111 := bstep (se 1 (by rfl) ⟨2582333, by rfl⟩ : syracuseStep 3443111 = 5164667) B5164667
theorem B2295407 : Blo 2293435 2295407 := bstep (se 1 (by rfl) ⟨1721555, by rfl⟩ : syracuseStep 2295407 = 3443111) B3443111
theorem B3443117 : Blo 2293435 3443117 := bbase (se 3 (by rfl) ⟨645584, by rfl⟩ : syracuseStep 3443117 = 1291169) (by norm_num)
theorem B2295411 : Blo 2293435 2295411 := bstep (se 1 (by rfl) ⟨1721558, by rfl⟩ : syracuseStep 2295411 = 3443117) B3443117
theorem B5164685 : Blo 2293435 5164685 := bbase (se 3 (by rfl) ⟨968378, by rfl⟩ : syracuseStep 5164685 = 1936757) (by norm_num)
theorem B3443123 : Blo 2293435 3443123 := bstep (se 1 (by rfl) ⟨2582342, by rfl⟩ : syracuseStep 3443123 = 5164685) B5164685
theorem B2295415 : Blo 2293435 2295415 := bstep (se 1 (by rfl) ⟨1721561, by rfl⟩ : syracuseStep 2295415 = 3443123) B3443123
theorem B2905141 : Blo 2293435 2905141 := bbase (se 5 (by rfl) ⟨136178, by rfl⟩ : syracuseStep 2905141 = 272357) (by norm_num)
theorem B3873521 : Blo 2293435 3873521 := bstep (se 2 (by rfl) ⟨1452570, by rfl⟩ : syracuseStep 3873521 = 2905141) B2905141
theorem B2582347 : Blo 2293435 2582347 := bstep (se 1 (by rfl) ⟨1936760, by rfl⟩ : syracuseStep 2582347 = 3873521) B3873521
theorem B3443129 : Blo 2293435 3443129 := bstep (se 2 (by rfl) ⟨1291173, by rfl⟩ : syracuseStep 3443129 = 2582347) B2582347
theorem B2295419 : Blo 2293435 2295419 := bstep (se 1 (by rfl) ⟨1721564, by rfl⟩ : syracuseStep 2295419 = 3443129) B3443129
theorem B9306965 : Blo 2293435 9306965 := bbase (se 9 (by rfl) ⟨27266, by rfl⟩ : syracuseStep 9306965 = 54533) (by norm_num)
theorem B6204643 : Blo 2293435 6204643 := bstep (se 1 (by rfl) ⟨4653482, by rfl⟩ : syracuseStep 6204643 = 9306965) B9306965
theorem B33091429 : Blo 2293435 33091429 := bstep (se 4 (by rfl) ⟨3102321, by rfl⟩ : syracuseStep 33091429 = 6204643) B6204643
theorem B44121905 : Blo 2293435 44121905 := bstep (se 2 (by rfl) ⟨16545714, by rfl⟩ : syracuseStep 44121905 = 33091429) B33091429
theorem B29414603 : Blo 2293435 29414603 := bstep (se 1 (by rfl) ⟨22060952, by rfl⟩ : syracuseStep 29414603 = 44121905) B44121905
theorem B19609735 : Blo 2293435 19609735 := bstep (se 1 (by rfl) ⟨14707301, by rfl⟩ : syracuseStep 19609735 = 29414603) B29414603
theorem B26146313 : Blo 2293435 26146313 := bstep (se 2 (by rfl) ⟨9804867, by rfl⟩ : syracuseStep 26146313 = 19609735) B19609735
theorem B17430875 : Blo 2293435 17430875 := bstep (se 1 (by rfl) ⟨13073156, by rfl⟩ : syracuseStep 17430875 = 26146313) B26146313
theorem B11620583 : Blo 2293435 11620583 := bstep (se 1 (by rfl) ⟨8715437, by rfl⟩ : syracuseStep 11620583 = 17430875) B17430875
theorem B7747055 : Blo 2293435 7747055 := bstep (se 1 (by rfl) ⟨5810291, by rfl⟩ : syracuseStep 7747055 = 11620583) B11620583
theorem B5164703 : Blo 2293435 5164703 := bstep (se 1 (by rfl) ⟨3873527, by rfl⟩ : syracuseStep 5164703 = 7747055) B7747055
theorem B3443135 : Blo 2293435 3443135 := bstep (se 1 (by rfl) ⟨2582351, by rfl⟩ : syracuseStep 3443135 = 5164703) B5164703
theorem B2295423 : Blo 2293435 2295423 := bstep (se 1 (by rfl) ⟨1721567, by rfl⟩ : syracuseStep 2295423 = 3443135) B3443135
theorem B3443141 : Blo 2293435 3443141 := bbase (se 4 (by rfl) ⟨322794, by rfl⟩ : syracuseStep 3443141 = 645589) (by norm_num)
theorem B2295427 : Blo 2293435 2295427 := bstep (se 1 (by rfl) ⟨1721570, by rfl⟩ : syracuseStep 2295427 = 3443141) B3443141
theorem B3873541 : Blo 2293435 3873541 := bbase (se 4 (by rfl) ⟨363144, by rfl⟩ : syracuseStep 3873541 = 726289) (by norm_num)
theorem B5164721 : Blo 2293435 5164721 := bstep (se 2 (by rfl) ⟨1936770, by rfl⟩ : syracuseStep 5164721 = 3873541) B3873541
theorem B3443147 : Blo 2293435 3443147 := bstep (se 1 (by rfl) ⟨2582360, by rfl⟩ : syracuseStep 3443147 = 5164721) B5164721
theorem B2295431 : Blo 2293435 2295431 := bstep (se 1 (by rfl) ⟨1721573, by rfl⟩ : syracuseStep 2295431 = 3443147) B3443147
theorem B2582365 : Blo 2293435 2582365 := bbase (se 3 (by rfl) ⟨484193, by rfl⟩ : syracuseStep 2582365 = 968387) (by norm_num)
theorem B3443153 : Blo 2293435 3443153 := bstep (se 2 (by rfl) ⟨1291182, by rfl⟩ : syracuseStep 3443153 = 2582365) B2582365
theorem B2295435 : Blo 2293435 2295435 := bstep (se 1 (by rfl) ⟨1721576, by rfl⟩ : syracuseStep 2295435 = 3443153) B3443153
theorem C0 (j : ℕ) (h1 : 573358 ≤ j) (h2 : j ≤ 573858) : Blo 2293435 (4 * j + 3) := by
  interval_cases j
  · exact B2293435
  · exact B2293439
  · exact B2293443
  · exact B2293447
  · exact B2293451
  · exact B2293455
  · exact B2293459
  · exact B2293463
  · exact B2293467
  · exact B2293471
  · exact B2293475
  · exact B2293479
  · exact B2293483
  · exact B2293487
  · exact B2293491
  · exact B2293495
  · exact B2293499
  · exact B2293503
  · exact B2293507
  · exact B2293511
  · exact B2293515
  · exact B2293519
  · exact B2293523
  · exact B2293527
  · exact B2293531
  · exact B2293535
  · exact B2293539
  · exact B2293543
  · exact B2293547
  · exact B2293551
  · exact B2293555
  · exact B2293559
  · exact B2293563
  · exact B2293567
  · exact B2293571
  · exact B2293575
  · exact B2293579
  · exact B2293583
  · exact B2293587
  · exact B2293591
  · exact B2293595
  · exact B2293599
  · exact B2293603
  · exact B2293607
  · exact B2293611
  · exact B2293615
  · exact B2293619
  · exact B2293623
  · exact B2293627
  · exact B2293631
  · exact B2293635
  · exact B2293639
  · exact B2293643
  · exact B2293647
  · exact B2293651
  · exact B2293655
  · exact B2293659
  · exact B2293663
  · exact B2293667
  · exact B2293671
  · exact B2293675
  · exact B2293679
  · exact B2293683
  · exact B2293687
  · exact B2293691
  · exact B2293695
  · exact B2293699
  · exact B2293703
  · exact B2293707
  · exact B2293711
  · exact B2293715
  · exact B2293719
  · exact B2293723
  · exact B2293727
  · exact B2293731
  · exact B2293735
  · exact B2293739
  · exact B2293743
  · exact B2293747
  · exact B2293751
  · exact B2293755
  · exact B2293759
  · exact B2293763
  · exact B2293767
  · exact B2293771
  · exact B2293775
  · exact B2293779
  · exact B2293783
  · exact B2293787
  · exact B2293791
  · exact B2293795
  · exact B2293799
  · exact B2293803
  · exact B2293807
  · exact B2293811
  · exact B2293815
  · exact B2293819
  · exact B2293823
  · exact B2293827
  · exact B2293831
  · exact B2293835
  · exact B2293839
  · exact B2293843
  · exact B2293847
  · exact B2293851
  · exact B2293855
  · exact B2293859
  · exact B2293863
  · exact B2293867
  · exact B2293871
  · exact B2293875
  · exact B2293879
  · exact B2293883
  · exact B2293887
  · exact B2293891
  · exact B2293895
  · exact B2293899
  · exact B2293903
  · exact B2293907
  · exact B2293911
  · exact B2293915
  · exact B2293919
  · exact B2293923
  · exact B2293927
  · exact B2293931
  · exact B2293935
  · exact B2293939
  · exact B2293943
  · exact B2293947
  · exact B2293951
  · exact B2293955
  · exact B2293959
  · exact B2293963
  · exact B2293967
  · exact B2293971
  · exact B2293975
  · exact B2293979
  · exact B2293983
  · exact B2293987
  · exact B2293991
  · exact B2293995
  · exact B2293999
  · exact B2294003
  · exact B2294007
  · exact B2294011
  · exact B2294015
  · exact B2294019
  · exact B2294023
  · exact B2294027
  · exact B2294031
  · exact B2294035
  · exact B2294039
  · exact B2294043
  · exact B2294047
  · exact B2294051
  · exact B2294055
  · exact B2294059
  · exact B2294063
  · exact B2294067
  · exact B2294071
  · exact B2294075
  · exact B2294079
  · exact B2294083
  · exact B2294087
  · exact B2294091
  · exact B2294095
  · exact B2294099
  · exact B2294103
  · exact B2294107
  · exact B2294111
  · exact B2294115
  · exact B2294119
  · exact B2294123
  · exact B2294127
  · exact B2294131
  · exact B2294135
  · exact B2294139
  · exact B2294143
  · exact B2294147
  · exact B2294151
  · exact B2294155
  · exact B2294159
  · exact B2294163
  · exact B2294167
  · exact B2294171
  · exact B2294175
  · exact B2294179
  · exact B2294183
  · exact B2294187
  · exact B2294191
  · exact B2294195
  · exact B2294199
  · exact B2294203
  · exact B2294207
  · exact B2294211
  · exact B2294215
  · exact B2294219
  · exact B2294223
  · exact B2294227
  · exact B2294231
  · exact B2294235
  · exact B2294239
  · exact B2294243
  · exact B2294247
  · exact B2294251
  · exact B2294255
  · exact B2294259
  · exact B2294263
  · exact B2294267
  · exact B2294271
  · exact B2294275
  · exact B2294279
  · exact B2294283
  · exact B2294287
  · exact B2294291
  · exact B2294295
  · exact B2294299
  · exact B2294303
  · exact B2294307
  · exact B2294311
  · exact B2294315
  · exact B2294319
  · exact B2294323
  · exact B2294327
  · exact B2294331
  · exact B2294335
  · exact B2294339
  · exact B2294343
  · exact B2294347
  · exact B2294351
  · exact B2294355
  · exact B2294359
  · exact B2294363
  · exact B2294367
  · exact B2294371
  · exact B2294375
  · exact B2294379
  · exact B2294383
  · exact B2294387
  · exact B2294391
  · exact B2294395
  · exact B2294399
  · exact B2294403
  · exact B2294407
  · exact B2294411
  · exact B2294415
  · exact B2294419
  · exact B2294423
  · exact B2294427
  · exact B2294431
  · exact B2294435
  · exact B2294439
  · exact B2294443
  · exact B2294447
  · exact B2294451
  · exact B2294455
  · exact B2294459
  · exact B2294463
  · exact B2294467
  · exact B2294471
  · exact B2294475
  · exact B2294479
  · exact B2294483
  · exact B2294487
  · exact B2294491
  · exact B2294495
  · exact B2294499
  · exact B2294503
  · exact B2294507
  · exact B2294511
  · exact B2294515
  · exact B2294519
  · exact B2294523
  · exact B2294527
  · exact B2294531
  · exact B2294535
  · exact B2294539
  · exact B2294543
  · exact B2294547
  · exact B2294551
  · exact B2294555
  · exact B2294559
  · exact B2294563
  · exact B2294567
  · exact B2294571
  · exact B2294575
  · exact B2294579
  · exact B2294583
  · exact B2294587
  · exact B2294591
  · exact B2294595
  · exact B2294599
  · exact B2294603
  · exact B2294607
  · exact B2294611
  · exact B2294615
  · exact B2294619
  · exact B2294623
  · exact B2294627
  · exact B2294631
  · exact B2294635
  · exact B2294639
  · exact B2294643
  · exact B2294647
  · exact B2294651
  · exact B2294655
  · exact B2294659
  · exact B2294663
  · exact B2294667
  · exact B2294671
  · exact B2294675
  · exact B2294679
  · exact B2294683
  · exact B2294687
  · exact B2294691
  · exact B2294695
  · exact B2294699
  · exact B2294703
  · exact B2294707
  · exact B2294711
  · exact B2294715
  · exact B2294719
  · exact B2294723
  · exact B2294727
  · exact B2294731
  · exact B2294735
  · exact B2294739
  · exact B2294743
  · exact B2294747
  · exact B2294751
  · exact B2294755
  · exact B2294759
  · exact B2294763
  · exact B2294767
  · exact B2294771
  · exact B2294775
  · exact B2294779
  · exact B2294783
  · exact B2294787
  · exact B2294791
  · exact B2294795
  · exact B2294799
  · exact B2294803
  · exact B2294807
  · exact B2294811
  · exact B2294815
  · exact B2294819
  · exact B2294823
  · exact B2294827
  · exact B2294831
  · exact B2294835
  · exact B2294839
  · exact B2294843
  · exact B2294847
  · exact B2294851
  · exact B2294855
  · exact B2294859
  · exact B2294863
  · exact B2294867
  · exact B2294871
  · exact B2294875
  · exact B2294879
  · exact B2294883
  · exact B2294887
  · exact B2294891
  · exact B2294895
  · exact B2294899
  · exact B2294903
  · exact B2294907
  · exact B2294911
  · exact B2294915
  · exact B2294919
  · exact B2294923
  · exact B2294927
  · exact B2294931
  · exact B2294935
  · exact B2294939
  · exact B2294943
  · exact B2294947
  · exact B2294951
  · exact B2294955
  · exact B2294959
  · exact B2294963
  · exact B2294967
  · exact B2294971
  · exact B2294975
  · exact B2294979
  · exact B2294983
  · exact B2294987
  · exact B2294991
  · exact B2294995
  · exact B2294999
  · exact B2295003
  · exact B2295007
  · exact B2295011
  · exact B2295015
  · exact B2295019
  · exact B2295023
  · exact B2295027
  · exact B2295031
  · exact B2295035
  · exact B2295039
  · exact B2295043
  · exact B2295047
  · exact B2295051
  · exact B2295055
  · exact B2295059
  · exact B2295063
  · exact B2295067
  · exact B2295071
  · exact B2295075
  · exact B2295079
  · exact B2295083
  · exact B2295087
  · exact B2295091
  · exact B2295095
  · exact B2295099
  · exact B2295103
  · exact B2295107
  · exact B2295111
  · exact B2295115
  · exact B2295119
  · exact B2295123
  · exact B2295127
  · exact B2295131
  · exact B2295135
  · exact B2295139
  · exact B2295143
  · exact B2295147
  · exact B2295151
  · exact B2295155
  · exact B2295159
  · exact B2295163
  · exact B2295167
  · exact B2295171
  · exact B2295175
  · exact B2295179
  · exact B2295183
  · exact B2295187
  · exact B2295191
  · exact B2295195
  · exact B2295199
  · exact B2295203
  · exact B2295207
  · exact B2295211
  · exact B2295215
  · exact B2295219
  · exact B2295223
  · exact B2295227
  · exact B2295231
  · exact B2295235
  · exact B2295239
  · exact B2295243
  · exact B2295247
  · exact B2295251
  · exact B2295255
  · exact B2295259
  · exact B2295263
  · exact B2295267
  · exact B2295271
  · exact B2295275
  · exact B2295279
  · exact B2295283
  · exact B2295287
  · exact B2295291
  · exact B2295295
  · exact B2295299
  · exact B2295303
  · exact B2295307
  · exact B2295311
  · exact B2295315
  · exact B2295319
  · exact B2295323
  · exact B2295327
  · exact B2295331
  · exact B2295335
  · exact B2295339
  · exact B2295343
  · exact B2295347
  · exact B2295351
  · exact B2295355
  · exact B2295359
  · exact B2295363
  · exact B2295367
  · exact B2295371
  · exact B2295375
  · exact B2295379
  · exact B2295383
  · exact B2295387
  · exact B2295391
  · exact B2295395
  · exact B2295399
  · exact B2295403
  · exact B2295407
  · exact B2295411
  · exact B2295415
  · exact B2295419
  · exact B2295423
  · exact B2295427
  · exact B2295431
  · exact B2295435
theorem solution (m : ℕ) (hlo : 2293435 ≤ m) (hhi : m ≤ 2295435) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 573358 ≤ j := by omega
    have hj2 : j ≤ 573858 := by omega
    have hb : Blo 2293435 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
