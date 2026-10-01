-- Prove2me | solution 1 for syracuse_descends_range_2087435_2089435
-- status  : ACCEPTED   (prove)
-- author  : @chstdu
-- created : 2026-09-23T17:16:22.56541+00:00
-- url     : https://prove2.me/submissions/f05f569b-63d5-4127-a287-a00b1b927a99

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

theorem B2348365 : Blo 2087435 2348365 := bbase (se 3 (by rfl) ⟨440318, by rfl⟩ : syracuseStep 2348365 = 880637) (by norm_num)
theorem B3131153 : Blo 2087435 3131153 := bstep (se 2 (by rfl) ⟨1174182, by rfl⟩ : syracuseStep 3131153 = 2348365) B2348365
theorem B2087435 : Blo 2087435 2087435 := bstep (se 1 (by rfl) ⟨1565576, by rfl⟩ : syracuseStep 2087435 = 3131153) B3131153
theorem B7045109 : Blo 2087435 7045109 := bbase (se 5 (by rfl) ⟨330239, by rfl⟩ : syracuseStep 7045109 = 660479) (by norm_num)
theorem B4696739 : Blo 2087435 4696739 := bstep (se 1 (by rfl) ⟨3522554, by rfl⟩ : syracuseStep 4696739 = 7045109) B7045109
theorem B3131159 : Blo 2087435 3131159 := bstep (se 1 (by rfl) ⟨2348369, by rfl⟩ : syracuseStep 3131159 = 4696739) B4696739
theorem B2087439 : Blo 2087435 2087439 := bstep (se 1 (by rfl) ⟨1565579, by rfl⟩ : syracuseStep 2087439 = 3131159) B3131159
theorem B3131165 : Blo 2087435 3131165 := bbase (se 3 (by rfl) ⟨587093, by rfl⟩ : syracuseStep 3131165 = 1174187) (by norm_num)
theorem B2087443 : Blo 2087435 2087443 := bstep (se 1 (by rfl) ⟨1565582, by rfl⟩ : syracuseStep 2087443 = 3131165) B3131165
theorem B4696757 : Blo 2087435 4696757 := bbase (se 5 (by rfl) ⟨220160, by rfl⟩ : syracuseStep 4696757 = 440321) (by norm_num)
theorem B3131171 : Blo 2087435 3131171 := bstep (se 1 (by rfl) ⟨2348378, by rfl⟩ : syracuseStep 3131171 = 4696757) B4696757
theorem B2087447 : Blo 2087435 2087447 := bstep (se 1 (by rfl) ⟨1565585, by rfl⟩ : syracuseStep 2087447 = 3131171) B3131171
theorem B11888693 : Blo 2087435 11888693 := bbase (se 5 (by rfl) ⟨557282, by rfl⟩ : syracuseStep 11888693 = 1114565) (by norm_num)
theorem B7925795 : Blo 2087435 7925795 := bstep (se 1 (by rfl) ⟨5944346, by rfl⟩ : syracuseStep 7925795 = 11888693) B11888693
theorem B5283863 : Blo 2087435 5283863 := bstep (se 1 (by rfl) ⟨3962897, by rfl⟩ : syracuseStep 5283863 = 7925795) B7925795
theorem B3522575 : Blo 2087435 3522575 := bstep (se 1 (by rfl) ⟨2641931, by rfl⟩ : syracuseStep 3522575 = 5283863) B5283863
theorem B2348383 : Blo 2087435 2348383 := bstep (se 1 (by rfl) ⟨1761287, by rfl⟩ : syracuseStep 2348383 = 3522575) B3522575
theorem B3131177 : Blo 2087435 3131177 := bstep (se 2 (by rfl) ⟨1174191, by rfl⟩ : syracuseStep 3131177 = 2348383) B2348383
theorem B2087451 : Blo 2087435 2087451 := bstep (se 1 (by rfl) ⟨1565588, by rfl⟩ : syracuseStep 2087451 = 3131177) B3131177
theorem B5944357 : Blo 2087435 5944357 := bbase (se 4 (by rfl) ⟨557283, by rfl⟩ : syracuseStep 5944357 = 1114567) (by norm_num)
theorem B7925809 : Blo 2087435 7925809 := bstep (se 2 (by rfl) ⟨2972178, by rfl⟩ : syracuseStep 7925809 = 5944357) B5944357
theorem B10567745 : Blo 2087435 10567745 := bstep (se 2 (by rfl) ⟨3962904, by rfl⟩ : syracuseStep 10567745 = 7925809) B7925809
theorem B7045163 : Blo 2087435 7045163 := bstep (se 1 (by rfl) ⟨5283872, by rfl⟩ : syracuseStep 7045163 = 10567745) B10567745
theorem B4696775 : Blo 2087435 4696775 := bstep (se 1 (by rfl) ⟨3522581, by rfl⟩ : syracuseStep 4696775 = 7045163) B7045163
theorem B3131183 : Blo 2087435 3131183 := bstep (se 1 (by rfl) ⟨2348387, by rfl⟩ : syracuseStep 3131183 = 4696775) B4696775
theorem B2087455 : Blo 2087435 2087455 := bstep (se 1 (by rfl) ⟨1565591, by rfl⟩ : syracuseStep 2087455 = 3131183) B3131183
theorem B3131189 : Blo 2087435 3131189 := bbase (se 5 (by rfl) ⟨146774, by rfl⟩ : syracuseStep 3131189 = 293549) (by norm_num)
theorem B2087459 : Blo 2087435 2087459 := bstep (se 1 (by rfl) ⟨1565594, by rfl⟩ : syracuseStep 2087459 = 3131189) B3131189
theorem B5283893 : Blo 2087435 5283893 := bbase (se 5 (by rfl) ⟨247682, by rfl⟩ : syracuseStep 5283893 = 495365) (by norm_num)
theorem B3522595 : Blo 2087435 3522595 := bstep (se 1 (by rfl) ⟨2641946, by rfl⟩ : syracuseStep 3522595 = 5283893) B5283893
theorem B4696793 : Blo 2087435 4696793 := bstep (se 2 (by rfl) ⟨1761297, by rfl⟩ : syracuseStep 4696793 = 3522595) B3522595
theorem B3131195 : Blo 2087435 3131195 := bstep (se 1 (by rfl) ⟨2348396, by rfl⟩ : syracuseStep 3131195 = 4696793) B4696793
theorem B2087463 : Blo 2087435 2087463 := bstep (se 1 (by rfl) ⟨1565597, by rfl⟩ : syracuseStep 2087463 = 3131195) B3131195
theorem B2348401 : Blo 2087435 2348401 := bbase (se 2 (by rfl) ⟨880650, by rfl⟩ : syracuseStep 2348401 = 1761301) (by norm_num)
theorem B3131201 : Blo 2087435 3131201 := bstep (se 2 (by rfl) ⟨1174200, by rfl⟩ : syracuseStep 3131201 = 2348401) B2348401
theorem B2087467 : Blo 2087435 2087467 := bstep (se 1 (by rfl) ⟨1565600, by rfl⟩ : syracuseStep 2087467 = 3131201) B3131201
theorem B4289645 : Blo 2087435 4289645 := bbase (se 3 (by rfl) ⟨804308, by rfl⟩ : syracuseStep 4289645 = 1608617) (by norm_num)
theorem B11439053 : Blo 2087435 11439053 := bstep (se 3 (by rfl) ⟨2144822, by rfl⟩ : syracuseStep 11439053 = 4289645) B4289645
theorem B7626035 : Blo 2087435 7626035 := bstep (se 1 (by rfl) ⟨5719526, by rfl⟩ : syracuseStep 7626035 = 11439053) B11439053
theorem B20336093 : Blo 2087435 20336093 := bstep (se 3 (by rfl) ⟨3813017, by rfl⟩ : syracuseStep 20336093 = 7626035) B7626035
theorem B13557395 : Blo 2087435 13557395 := bstep (se 1 (by rfl) ⟨10168046, by rfl⟩ : syracuseStep 13557395 = 20336093) B20336093
theorem B9038263 : Blo 2087435 9038263 := bstep (se 1 (by rfl) ⟨6778697, by rfl⟩ : syracuseStep 9038263 = 13557395) B13557395
theorem B12051017 : Blo 2087435 12051017 := bstep (se 2 (by rfl) ⟨4519131, by rfl⟩ : syracuseStep 12051017 = 9038263) B9038263
theorem B8034011 : Blo 2087435 8034011 := bstep (se 1 (by rfl) ⟨6025508, by rfl⟩ : syracuseStep 8034011 = 12051017) B12051017
theorem B5356007 : Blo 2087435 5356007 := bstep (se 1 (by rfl) ⟨4017005, by rfl⟩ : syracuseStep 5356007 = 8034011) B8034011
theorem B3570671 : Blo 2087435 3570671 := bstep (se 1 (by rfl) ⟨2678003, by rfl⟩ : syracuseStep 3570671 = 5356007) B5356007
theorem B2380447 : Blo 2087435 2380447 := bstep (se 1 (by rfl) ⟨1785335, by rfl⟩ : syracuseStep 2380447 = 3570671) B3570671
theorem B12695717 : Blo 2087435 12695717 := bstep (se 4 (by rfl) ⟨1190223, by rfl⟩ : syracuseStep 12695717 = 2380447) B2380447
theorem B8463811 : Blo 2087435 8463811 := bstep (se 1 (by rfl) ⟨6347858, by rfl⟩ : syracuseStep 8463811 = 12695717) B12695717
theorem B11285081 : Blo 2087435 11285081 := bstep (se 2 (by rfl) ⟨4231905, by rfl⟩ : syracuseStep 11285081 = 8463811) B8463811
theorem B7523387 : Blo 2087435 7523387 := bstep (se 1 (by rfl) ⟨5642540, by rfl⟩ : syracuseStep 7523387 = 11285081) B11285081
theorem B5015591 : Blo 2087435 5015591 := bstep (se 1 (by rfl) ⟨3761693, by rfl⟩ : syracuseStep 5015591 = 7523387) B7523387
theorem B3343727 : Blo 2087435 3343727 := bstep (se 1 (by rfl) ⟨2507795, by rfl⟩ : syracuseStep 3343727 = 5015591) B5015591
theorem B8916605 : Blo 2087435 8916605 := bstep (se 3 (by rfl) ⟨1671863, by rfl⟩ : syracuseStep 8916605 = 3343727) B3343727
theorem B5944403 : Blo 2087435 5944403 := bstep (se 1 (by rfl) ⟨4458302, by rfl⟩ : syracuseStep 5944403 = 8916605) B8916605
theorem B3962935 : Blo 2087435 3962935 := bstep (se 1 (by rfl) ⟨2972201, by rfl⟩ : syracuseStep 3962935 = 5944403) B5944403
theorem B5283913 : Blo 2087435 5283913 := bstep (se 2 (by rfl) ⟨1981467, by rfl⟩ : syracuseStep 5283913 = 3962935) B3962935
theorem B7045217 : Blo 2087435 7045217 := bstep (se 2 (by rfl) ⟨2641956, by rfl⟩ : syracuseStep 7045217 = 5283913) B5283913
theorem B4696811 : Blo 2087435 4696811 := bstep (se 1 (by rfl) ⟨3522608, by rfl⟩ : syracuseStep 4696811 = 7045217) B7045217
theorem B3131207 : Blo 2087435 3131207 := bstep (se 1 (by rfl) ⟨2348405, by rfl⟩ : syracuseStep 3131207 = 4696811) B4696811
theorem B2087471 : Blo 2087435 2087471 := bstep (se 1 (by rfl) ⟨1565603, by rfl⟩ : syracuseStep 2087471 = 3131207) B3131207
theorem B3131213 : Blo 2087435 3131213 := bbase (se 3 (by rfl) ⟨587102, by rfl⟩ : syracuseStep 3131213 = 1174205) (by norm_num)
theorem B2087475 : Blo 2087435 2087475 := bstep (se 1 (by rfl) ⟨1565606, by rfl⟩ : syracuseStep 2087475 = 3131213) B3131213
theorem B4696829 : Blo 2087435 4696829 := bbase (se 3 (by rfl) ⟨880655, by rfl⟩ : syracuseStep 4696829 = 1761311) (by norm_num)
theorem B3131219 : Blo 2087435 3131219 := bstep (se 1 (by rfl) ⟨2348414, by rfl⟩ : syracuseStep 3131219 = 4696829) B4696829
theorem B2087479 : Blo 2087435 2087479 := bstep (se 1 (by rfl) ⟨1565609, by rfl⟩ : syracuseStep 2087479 = 3131219) B3131219
theorem B3522629 : Blo 2087435 3522629 := bbase (se 4 (by rfl) ⟨330246, by rfl⟩ : syracuseStep 3522629 = 660493) (by norm_num)
theorem B2348419 : Blo 2087435 2348419 := bstep (se 1 (by rfl) ⟨1761314, by rfl⟩ : syracuseStep 2348419 = 3522629) B3522629
theorem B3131225 : Blo 2087435 3131225 := bstep (se 2 (by rfl) ⟨1174209, by rfl⟩ : syracuseStep 3131225 = 2348419) B2348419
theorem B2087483 : Blo 2087435 2087483 := bstep (se 1 (by rfl) ⟨1565612, by rfl⟩ : syracuseStep 2087483 = 3131225) B3131225
theorem B15851861 : Blo 2087435 15851861 := bbase (se 10 (by rfl) ⟨23220, by rfl⟩ : syracuseStep 15851861 = 46441) (by norm_num)
theorem B10567907 : Blo 2087435 10567907 := bstep (se 1 (by rfl) ⟨7925930, by rfl⟩ : syracuseStep 10567907 = 15851861) B15851861
theorem B7045271 : Blo 2087435 7045271 := bstep (se 1 (by rfl) ⟨5283953, by rfl⟩ : syracuseStep 7045271 = 10567907) B10567907
theorem B4696847 : Blo 2087435 4696847 := bstep (se 1 (by rfl) ⟨3522635, by rfl⟩ : syracuseStep 4696847 = 7045271) B7045271
theorem B3131231 : Blo 2087435 3131231 := bstep (se 1 (by rfl) ⟨2348423, by rfl⟩ : syracuseStep 3131231 = 4696847) B4696847
theorem B2087487 : Blo 2087435 2087487 := bstep (se 1 (by rfl) ⟨1565615, by rfl⟩ : syracuseStep 2087487 = 3131231) B3131231
theorem B3131237 : Blo 2087435 3131237 := bbase (se 4 (by rfl) ⟨293553, by rfl⟩ : syracuseStep 3131237 = 587107) (by norm_num)
theorem B2087491 : Blo 2087435 2087491 := bstep (se 1 (by rfl) ⟨1565618, by rfl⟩ : syracuseStep 2087491 = 3131237) B3131237
theorem B3962981 : Blo 2087435 3962981 := bbase (se 4 (by rfl) ⟨371529, by rfl⟩ : syracuseStep 3962981 = 743059) (by norm_num)
theorem B2641987 : Blo 2087435 2641987 := bstep (se 1 (by rfl) ⟨1981490, by rfl⟩ : syracuseStep 2641987 = 3962981) B3962981
theorem B3522649 : Blo 2087435 3522649 := bstep (se 2 (by rfl) ⟨1320993, by rfl⟩ : syracuseStep 3522649 = 2641987) B2641987
theorem B4696865 : Blo 2087435 4696865 := bstep (se 2 (by rfl) ⟨1761324, by rfl⟩ : syracuseStep 4696865 = 3522649) B3522649
theorem B3131243 : Blo 2087435 3131243 := bstep (se 1 (by rfl) ⟨2348432, by rfl⟩ : syracuseStep 3131243 = 4696865) B4696865
theorem B2087495 : Blo 2087435 2087495 := bstep (se 1 (by rfl) ⟨1565621, by rfl⟩ : syracuseStep 2087495 = 3131243) B3131243
theorem B2348437 : Blo 2087435 2348437 := bbase (se 6 (by rfl) ⟨55041, by rfl⟩ : syracuseStep 2348437 = 110083) (by norm_num)
theorem B3131249 : Blo 2087435 3131249 := bstep (se 2 (by rfl) ⟨1174218, by rfl⟩ : syracuseStep 3131249 = 2348437) B2348437
theorem B2087499 : Blo 2087435 2087499 := bstep (se 1 (by rfl) ⟨1565624, by rfl⟩ : syracuseStep 2087499 = 3131249) B3131249
theorem B2641997 : Blo 2087435 2641997 := bbase (se 3 (by rfl) ⟨495374, by rfl⟩ : syracuseStep 2641997 = 990749) (by norm_num)
theorem B7045325 : Blo 2087435 7045325 := bstep (se 3 (by rfl) ⟨1320998, by rfl⟩ : syracuseStep 7045325 = 2641997) B2641997
theorem B4696883 : Blo 2087435 4696883 := bstep (se 1 (by rfl) ⟨3522662, by rfl⟩ : syracuseStep 4696883 = 7045325) B7045325
theorem B3131255 : Blo 2087435 3131255 := bstep (se 1 (by rfl) ⟨2348441, by rfl⟩ : syracuseStep 3131255 = 4696883) B4696883
theorem B2087503 : Blo 2087435 2087503 := bstep (se 1 (by rfl) ⟨1565627, by rfl⟩ : syracuseStep 2087503 = 3131255) B3131255
theorem B3131261 : Blo 2087435 3131261 := bbase (se 3 (by rfl) ⟨587111, by rfl⟩ : syracuseStep 3131261 = 1174223) (by norm_num)
theorem B2087507 : Blo 2087435 2087507 := bstep (se 1 (by rfl) ⟨1565630, by rfl⟩ : syracuseStep 2087507 = 3131261) B3131261
theorem B4696901 : Blo 2087435 4696901 := bbase (se 4 (by rfl) ⟨440334, by rfl⟩ : syracuseStep 4696901 = 880669) (by norm_num)
theorem B3131267 : Blo 2087435 3131267 := bstep (se 1 (by rfl) ⟨2348450, by rfl⟩ : syracuseStep 3131267 = 4696901) B4696901
theorem B2087511 : Blo 2087435 2087511 := bstep (se 1 (by rfl) ⟨1565633, by rfl⟩ : syracuseStep 2087511 = 3131267) B3131267
theorem B4458397 : Blo 2087435 4458397 := bbase (se 3 (by rfl) ⟨835949, by rfl⟩ : syracuseStep 4458397 = 1671899) (by norm_num)
theorem B5944529 : Blo 2087435 5944529 := bstep (se 2 (by rfl) ⟨2229198, by rfl⟩ : syracuseStep 5944529 = 4458397) B4458397
theorem B3963019 : Blo 2087435 3963019 := bstep (se 1 (by rfl) ⟨2972264, by rfl⟩ : syracuseStep 3963019 = 5944529) B5944529
theorem B5284025 : Blo 2087435 5284025 := bstep (se 2 (by rfl) ⟨1981509, by rfl⟩ : syracuseStep 5284025 = 3963019) B3963019
theorem B3522683 : Blo 2087435 3522683 := bstep (se 1 (by rfl) ⟨2642012, by rfl⟩ : syracuseStep 3522683 = 5284025) B5284025
theorem B2348455 : Blo 2087435 2348455 := bstep (se 1 (by rfl) ⟨1761341, by rfl⟩ : syracuseStep 2348455 = 3522683) B3522683
theorem B3131273 : Blo 2087435 3131273 := bstep (se 2 (by rfl) ⟨1174227, by rfl⟩ : syracuseStep 3131273 = 2348455) B2348455
theorem B2087515 : Blo 2087435 2087515 := bstep (se 1 (by rfl) ⟨1565636, by rfl⟩ : syracuseStep 2087515 = 3131273) B3131273
theorem B10568069 : Blo 2087435 10568069 := bbase (se 4 (by rfl) ⟨990756, by rfl⟩ : syracuseStep 10568069 = 1981513) (by norm_num)
theorem B7045379 : Blo 2087435 7045379 := bstep (se 1 (by rfl) ⟨5284034, by rfl⟩ : syracuseStep 7045379 = 10568069) B10568069
theorem B4696919 : Blo 2087435 4696919 := bstep (se 1 (by rfl) ⟨3522689, by rfl⟩ : syracuseStep 4696919 = 7045379) B7045379
theorem B3131279 : Blo 2087435 3131279 := bstep (se 1 (by rfl) ⟨2348459, by rfl⟩ : syracuseStep 3131279 = 4696919) B4696919
theorem B2087519 : Blo 2087435 2087519 := bstep (se 1 (by rfl) ⟨1565639, by rfl⟩ : syracuseStep 2087519 = 3131279) B3131279
theorem B3131285 : Blo 2087435 3131285 := bbase (se 6 (by rfl) ⟨73389, by rfl⟩ : syracuseStep 3131285 = 146779) (by norm_num)
theorem B2087523 : Blo 2087435 2087523 := bstep (se 1 (by rfl) ⟨1565642, by rfl⟩ : syracuseStep 2087523 = 3131285) B3131285
theorem B5642693 : Blo 2087435 5642693 := bbase (se 4 (by rfl) ⟨529002, by rfl⟩ : syracuseStep 5642693 = 1058005) (by norm_num)
theorem B3761795 : Blo 2087435 3761795 := bstep (se 1 (by rfl) ⟨2821346, by rfl⟩ : syracuseStep 3761795 = 5642693) B5642693
theorem B2507863 : Blo 2087435 2507863 := bstep (se 1 (by rfl) ⟨1880897, by rfl⟩ : syracuseStep 2507863 = 3761795) B3761795
theorem B3343817 : Blo 2087435 3343817 := bstep (se 2 (by rfl) ⟨1253931, by rfl⟩ : syracuseStep 3343817 = 2507863) B2507863
theorem B2229211 : Blo 2087435 2229211 := bstep (se 1 (by rfl) ⟨1671908, by rfl⟩ : syracuseStep 2229211 = 3343817) B3343817
theorem B11889125 : Blo 2087435 11889125 := bstep (se 4 (by rfl) ⟨1114605, by rfl⟩ : syracuseStep 11889125 = 2229211) B2229211
theorem B7926083 : Blo 2087435 7926083 := bstep (se 1 (by rfl) ⟨5944562, by rfl⟩ : syracuseStep 7926083 = 11889125) B11889125
theorem B5284055 : Blo 2087435 5284055 := bstep (se 1 (by rfl) ⟨3963041, by rfl⟩ : syracuseStep 5284055 = 7926083) B7926083
theorem B3522703 : Blo 2087435 3522703 := bstep (se 1 (by rfl) ⟨2642027, by rfl⟩ : syracuseStep 3522703 = 5284055) B5284055
theorem B4696937 : Blo 2087435 4696937 := bstep (se 2 (by rfl) ⟨1761351, by rfl⟩ : syracuseStep 4696937 = 3522703) B3522703
theorem B3131291 : Blo 2087435 3131291 := bstep (se 1 (by rfl) ⟨2348468, by rfl⟩ : syracuseStep 3131291 = 4696937) B4696937
theorem B2087527 : Blo 2087435 2087527 := bstep (se 1 (by rfl) ⟨1565645, by rfl⟩ : syracuseStep 2087527 = 3131291) B3131291
theorem B2348473 : Blo 2087435 2348473 := bbase (se 2 (by rfl) ⟨880677, by rfl⟩ : syracuseStep 2348473 = 1761355) (by norm_num)
theorem B3131297 : Blo 2087435 3131297 := bstep (se 2 (by rfl) ⟨1174236, by rfl⟩ : syracuseStep 3131297 = 2348473) B2348473
theorem B2087531 : Blo 2087435 2087531 := bstep (se 1 (by rfl) ⟨1565648, by rfl⟩ : syracuseStep 2087531 = 3131297) B3131297
theorem B6348053 : Blo 2087435 6348053 := bbase (se 6 (by rfl) ⟨148782, by rfl⟩ : syracuseStep 6348053 = 297565) (by norm_num)
theorem B4232035 : Blo 2087435 4232035 := bstep (se 1 (by rfl) ⟨3174026, by rfl⟩ : syracuseStep 4232035 = 6348053) B6348053
theorem B5642713 : Blo 2087435 5642713 := bstep (se 2 (by rfl) ⟨2116017, by rfl⟩ : syracuseStep 5642713 = 4232035) B4232035
theorem B7523617 : Blo 2087435 7523617 := bstep (se 2 (by rfl) ⟨2821356, by rfl⟩ : syracuseStep 7523617 = 5642713) B5642713
theorem B10031489 : Blo 2087435 10031489 := bstep (se 2 (by rfl) ⟨3761808, by rfl⟩ : syracuseStep 10031489 = 7523617) B7523617
theorem B6687659 : Blo 2087435 6687659 := bstep (se 1 (by rfl) ⟨5015744, by rfl⟩ : syracuseStep 6687659 = 10031489) B10031489
theorem B4458439 : Blo 2087435 4458439 := bstep (se 1 (by rfl) ⟨3343829, by rfl⟩ : syracuseStep 4458439 = 6687659) B6687659
theorem B5944585 : Blo 2087435 5944585 := bstep (se 2 (by rfl) ⟨2229219, by rfl⟩ : syracuseStep 5944585 = 4458439) B4458439
theorem B7926113 : Blo 2087435 7926113 := bstep (se 2 (by rfl) ⟨2972292, by rfl⟩ : syracuseStep 7926113 = 5944585) B5944585
theorem B5284075 : Blo 2087435 5284075 := bstep (se 1 (by rfl) ⟨3963056, by rfl⟩ : syracuseStep 5284075 = 7926113) B7926113
theorem B7045433 : Blo 2087435 7045433 := bstep (se 2 (by rfl) ⟨2642037, by rfl⟩ : syracuseStep 7045433 = 5284075) B5284075
theorem B4696955 : Blo 2087435 4696955 := bstep (se 1 (by rfl) ⟨3522716, by rfl⟩ : syracuseStep 4696955 = 7045433) B7045433
theorem B3131303 : Blo 2087435 3131303 := bstep (se 1 (by rfl) ⟨2348477, by rfl⟩ : syracuseStep 3131303 = 4696955) B4696955
theorem B2087535 : Blo 2087435 2087535 := bstep (se 1 (by rfl) ⟨1565651, by rfl⟩ : syracuseStep 2087535 = 3131303) B3131303
theorem B3131309 : Blo 2087435 3131309 := bbase (se 3 (by rfl) ⟨587120, by rfl⟩ : syracuseStep 3131309 = 1174241) (by norm_num)
theorem B2087539 : Blo 2087435 2087539 := bstep (se 1 (by rfl) ⟨1565654, by rfl⟩ : syracuseStep 2087539 = 3131309) B3131309
theorem B4696973 : Blo 2087435 4696973 := bbase (se 3 (by rfl) ⟨880682, by rfl⟩ : syracuseStep 4696973 = 1761365) (by norm_num)
theorem B3131315 : Blo 2087435 3131315 := bstep (se 1 (by rfl) ⟨2348486, by rfl⟩ : syracuseStep 3131315 = 4696973) B4696973
theorem B2087543 : Blo 2087435 2087543 := bstep (se 1 (by rfl) ⟨1565657, by rfl⟩ : syracuseStep 2087543 = 3131315) B3131315
theorem B2642053 : Blo 2087435 2642053 := bbase (se 4 (by rfl) ⟨247692, by rfl⟩ : syracuseStep 2642053 = 495385) (by norm_num)
theorem B3522737 : Blo 2087435 3522737 := bstep (se 2 (by rfl) ⟨1321026, by rfl⟩ : syracuseStep 3522737 = 2642053) B2642053
theorem B2348491 : Blo 2087435 2348491 := bstep (se 1 (by rfl) ⟨1761368, by rfl⟩ : syracuseStep 2348491 = 3522737) B3522737
theorem B3131321 : Blo 2087435 3131321 := bstep (se 2 (by rfl) ⟨1174245, by rfl⟩ : syracuseStep 3131321 = 2348491) B2348491
theorem B2087547 : Blo 2087435 2087547 := bstep (se 1 (by rfl) ⟨1565660, by rfl⟩ : syracuseStep 2087547 = 3131321) B3131321
theorem B3761837 : Blo 2087435 3761837 := bbase (se 3 (by rfl) ⟨705344, by rfl⟩ : syracuseStep 3761837 = 1410689) (by norm_num)
theorem B2507891 : Blo 2087435 2507891 := bstep (se 1 (by rfl) ⟨1880918, by rfl⟩ : syracuseStep 2507891 = 3761837) B3761837
theorem B26750837 : Blo 2087435 26750837 := bstep (se 5 (by rfl) ⟨1253945, by rfl⟩ : syracuseStep 26750837 = 2507891) B2507891
theorem B17833891 : Blo 2087435 17833891 := bstep (se 1 (by rfl) ⟨13375418, by rfl⟩ : syracuseStep 17833891 = 26750837) B26750837
theorem B23778521 : Blo 2087435 23778521 := bstep (se 2 (by rfl) ⟨8916945, by rfl⟩ : syracuseStep 23778521 = 17833891) B17833891
theorem B15852347 : Blo 2087435 15852347 := bstep (se 1 (by rfl) ⟨11889260, by rfl⟩ : syracuseStep 15852347 = 23778521) B23778521
theorem B10568231 : Blo 2087435 10568231 := bstep (se 1 (by rfl) ⟨7926173, by rfl⟩ : syracuseStep 10568231 = 15852347) B15852347
theorem B7045487 : Blo 2087435 7045487 := bstep (se 1 (by rfl) ⟨5284115, by rfl⟩ : syracuseStep 7045487 = 10568231) B10568231
theorem B4696991 : Blo 2087435 4696991 := bstep (se 1 (by rfl) ⟨3522743, by rfl⟩ : syracuseStep 4696991 = 7045487) B7045487
theorem B3131327 : Blo 2087435 3131327 := bstep (se 1 (by rfl) ⟨2348495, by rfl⟩ : syracuseStep 3131327 = 4696991) B4696991
theorem B2087551 : Blo 2087435 2087551 := bstep (se 1 (by rfl) ⟨1565663, by rfl⟩ : syracuseStep 2087551 = 3131327) B3131327
theorem B3131333 : Blo 2087435 3131333 := bbase (se 4 (by rfl) ⟨293562, by rfl⟩ : syracuseStep 3131333 = 587125) (by norm_num)
theorem B2087555 : Blo 2087435 2087555 := bstep (se 1 (by rfl) ⟨1565666, by rfl⟩ : syracuseStep 2087555 = 3131333) B3131333
theorem B3522757 : Blo 2087435 3522757 := bbase (se 4 (by rfl) ⟨330258, by rfl⟩ : syracuseStep 3522757 = 660517) (by norm_num)
theorem B4697009 : Blo 2087435 4697009 := bstep (se 2 (by rfl) ⟨1761378, by rfl⟩ : syracuseStep 4697009 = 3522757) B3522757
theorem B3131339 : Blo 2087435 3131339 := bstep (se 1 (by rfl) ⟨2348504, by rfl⟩ : syracuseStep 3131339 = 4697009) B4697009
theorem B2087559 : Blo 2087435 2087559 := bstep (se 1 (by rfl) ⟨1565669, by rfl⟩ : syracuseStep 2087559 = 3131339) B3131339
theorem B2348509 : Blo 2087435 2348509 := bbase (se 3 (by rfl) ⟨440345, by rfl⟩ : syracuseStep 2348509 = 880691) (by norm_num)
theorem B3131345 : Blo 2087435 3131345 := bstep (se 2 (by rfl) ⟨1174254, by rfl⟩ : syracuseStep 3131345 = 2348509) B2348509
theorem B2087563 : Blo 2087435 2087563 := bstep (se 1 (by rfl) ⟨1565672, by rfl⟩ : syracuseStep 2087563 = 3131345) B3131345
theorem B7045541 : Blo 2087435 7045541 := bbase (se 4 (by rfl) ⟨660519, by rfl⟩ : syracuseStep 7045541 = 1321039) (by norm_num)
theorem B4697027 : Blo 2087435 4697027 := bstep (se 1 (by rfl) ⟨3522770, by rfl⟩ : syracuseStep 4697027 = 7045541) B7045541
theorem B3131351 : Blo 2087435 3131351 := bstep (se 1 (by rfl) ⟨2348513, by rfl⟩ : syracuseStep 3131351 = 4697027) B4697027
theorem B2087567 : Blo 2087435 2087567 := bstep (se 1 (by rfl) ⟨1565675, by rfl⟩ : syracuseStep 2087567 = 3131351) B3131351
theorem B3131357 : Blo 2087435 3131357 := bbase (se 3 (by rfl) ⟨587129, by rfl⟩ : syracuseStep 3131357 = 1174259) (by norm_num)
theorem B2087571 : Blo 2087435 2087571 := bstep (se 1 (by rfl) ⟨1565678, by rfl⟩ : syracuseStep 2087571 = 3131357) B3131357
theorem B4697045 : Blo 2087435 4697045 := bbase (se 7 (by rfl) ⟨55043, by rfl⟩ : syracuseStep 4697045 = 110087) (by norm_num)
theorem B3131363 : Blo 2087435 3131363 := bstep (se 1 (by rfl) ⟨2348522, by rfl⟩ : syracuseStep 3131363 = 4697045) B4697045
theorem B2087575 : Blo 2087435 2087575 := bstep (se 1 (by rfl) ⟨1565681, by rfl⟩ : syracuseStep 2087575 = 3131363) B3131363
theorem B10031701 : Blo 2087435 10031701 := bbase (se 8 (by rfl) ⟨58779, by rfl⟩ : syracuseStep 10031701 = 117559) (by norm_num)
theorem B13375601 : Blo 2087435 13375601 := bstep (se 2 (by rfl) ⟨5015850, by rfl⟩ : syracuseStep 13375601 = 10031701) B10031701
theorem B8917067 : Blo 2087435 8917067 := bstep (se 1 (by rfl) ⟨6687800, by rfl⟩ : syracuseStep 8917067 = 13375601) B13375601
theorem B5944711 : Blo 2087435 5944711 := bstep (se 1 (by rfl) ⟨4458533, by rfl⟩ : syracuseStep 5944711 = 8917067) B8917067
theorem B7926281 : Blo 2087435 7926281 := bstep (se 2 (by rfl) ⟨2972355, by rfl⟩ : syracuseStep 7926281 = 5944711) B5944711
theorem B5284187 : Blo 2087435 5284187 := bstep (se 1 (by rfl) ⟨3963140, by rfl⟩ : syracuseStep 5284187 = 7926281) B7926281
theorem B3522791 : Blo 2087435 3522791 := bstep (se 1 (by rfl) ⟨2642093, by rfl⟩ : syracuseStep 3522791 = 5284187) B5284187
theorem B2348527 : Blo 2087435 2348527 := bstep (se 1 (by rfl) ⟨1761395, by rfl⟩ : syracuseStep 2348527 = 3522791) B3522791
theorem B3131369 : Blo 2087435 3131369 := bstep (se 2 (by rfl) ⟨1174263, by rfl⟩ : syracuseStep 3131369 = 2348527) B2348527
theorem B2087579 : Blo 2087435 2087579 := bstep (se 1 (by rfl) ⟨1565684, by rfl⟩ : syracuseStep 2087579 = 3131369) B3131369
theorem B17834165 : Blo 2087435 17834165 := bbase (se 5 (by rfl) ⟨835976, by rfl⟩ : syracuseStep 17834165 = 1671953) (by norm_num)
theorem B11889443 : Blo 2087435 11889443 := bstep (se 1 (by rfl) ⟨8917082, by rfl⟩ : syracuseStep 11889443 = 17834165) B17834165
theorem B7926295 : Blo 2087435 7926295 := bstep (se 1 (by rfl) ⟨5944721, by rfl⟩ : syracuseStep 7926295 = 11889443) B11889443
theorem B10568393 : Blo 2087435 10568393 := bstep (se 2 (by rfl) ⟨3963147, by rfl⟩ : syracuseStep 10568393 = 7926295) B7926295
theorem B7045595 : Blo 2087435 7045595 := bstep (se 1 (by rfl) ⟨5284196, by rfl⟩ : syracuseStep 7045595 = 10568393) B10568393
theorem B4697063 : Blo 2087435 4697063 := bstep (se 1 (by rfl) ⟨3522797, by rfl⟩ : syracuseStep 4697063 = 7045595) B7045595
theorem B3131375 : Blo 2087435 3131375 := bstep (se 1 (by rfl) ⟨2348531, by rfl⟩ : syracuseStep 3131375 = 4697063) B4697063
theorem B2087583 : Blo 2087435 2087583 := bstep (se 1 (by rfl) ⟨1565687, by rfl⟩ : syracuseStep 2087583 = 3131375) B3131375
theorem B3131381 : Blo 2087435 3131381 := bbase (se 5 (by rfl) ⟨146783, by rfl⟩ : syracuseStep 3131381 = 293567) (by norm_num)
theorem B2087587 : Blo 2087435 2087587 := bstep (se 1 (by rfl) ⟨1565690, by rfl⟩ : syracuseStep 2087587 = 3131381) B3131381
theorem B11006933 : Blo 2087435 11006933 := bbase (se 7 (by rfl) ⟨128987, by rfl⟩ : syracuseStep 11006933 = 257975) (by norm_num)
theorem B117407285 : Blo 2087435 117407285 := bstep (se 5 (by rfl) ⟨5503466, by rfl⟩ : syracuseStep 117407285 = 11006933) B11006933
theorem B78271523 : Blo 2087435 78271523 := bstep (se 1 (by rfl) ⟨58703642, by rfl⟩ : syracuseStep 78271523 = 117407285) B117407285
theorem B52181015 : Blo 2087435 52181015 := bstep (se 1 (by rfl) ⟨39135761, by rfl⟩ : syracuseStep 52181015 = 78271523) B78271523
theorem B556597493 : Blo 2087435 556597493 := bstep (se 5 (by rfl) ⟨26090507, by rfl⟩ : syracuseStep 556597493 = 52181015) B52181015
theorem B371064995 : Blo 2087435 371064995 := bstep (se 1 (by rfl) ⟨278298746, by rfl⟩ : syracuseStep 371064995 = 556597493) B556597493
theorem B247376663 : Blo 2087435 247376663 := bstep (se 1 (by rfl) ⟨185532497, by rfl⟩ : syracuseStep 247376663 = 371064995) B371064995
theorem B164917775 : Blo 2087435 164917775 := bstep (se 1 (by rfl) ⟨123688331, by rfl⟩ : syracuseStep 164917775 = 247376663) B247376663
theorem B109945183 : Blo 2087435 109945183 := bstep (se 1 (by rfl) ⟨82458887, by rfl⟩ : syracuseStep 109945183 = 164917775) B164917775
theorem B146593577 : Blo 2087435 146593577 := bstep (se 2 (by rfl) ⟨54972591, by rfl⟩ : syracuseStep 146593577 = 109945183) B109945183
theorem B390916205 : Blo 2087435 390916205 := bstep (se 3 (by rfl) ⟨73296788, by rfl⟩ : syracuseStep 390916205 = 146593577) B146593577
theorem B260610803 : Blo 2087435 260610803 := bstep (se 1 (by rfl) ⟨195458102, by rfl⟩ : syracuseStep 260610803 = 390916205) B390916205
theorem B173740535 : Blo 2087435 173740535 := bstep (se 1 (by rfl) ⟨130305401, by rfl⟩ : syracuseStep 173740535 = 260610803) B260610803
theorem B115827023 : Blo 2087435 115827023 := bstep (se 1 (by rfl) ⟨86870267, by rfl⟩ : syracuseStep 115827023 = 173740535) B173740535
theorem B308872061 : Blo 2087435 308872061 := bstep (se 3 (by rfl) ⟨57913511, by rfl⟩ : syracuseStep 308872061 = 115827023) B115827023
theorem B205914707 : Blo 2087435 205914707 := bstep (se 1 (by rfl) ⟨154436030, by rfl⟩ : syracuseStep 205914707 = 308872061) B308872061
theorem B137276471 : Blo 2087435 137276471 := bstep (se 1 (by rfl) ⟨102957353, by rfl⟩ : syracuseStep 137276471 = 205914707) B205914707
theorem B91517647 : Blo 2087435 91517647 := bstep (se 1 (by rfl) ⟨68638235, by rfl⟩ : syracuseStep 91517647 = 137276471) B137276471
theorem B122023529 : Blo 2087435 122023529 := bstep (se 2 (by rfl) ⟨45758823, by rfl⟩ : syracuseStep 122023529 = 91517647) B91517647
theorem B81349019 : Blo 2087435 81349019 := bstep (se 1 (by rfl) ⟨61011764, by rfl⟩ : syracuseStep 81349019 = 122023529) B122023529
theorem B54232679 : Blo 2087435 54232679 := bstep (se 1 (by rfl) ⟨40674509, by rfl⟩ : syracuseStep 54232679 = 81349019) B81349019
theorem B36155119 : Blo 2087435 36155119 := bstep (se 1 (by rfl) ⟨27116339, by rfl⟩ : syracuseStep 36155119 = 54232679) B54232679
theorem B48206825 : Blo 2087435 48206825 := bstep (se 2 (by rfl) ⟨18077559, by rfl⟩ : syracuseStep 48206825 = 36155119) B36155119
theorem B32137883 : Blo 2087435 32137883 := bstep (se 1 (by rfl) ⟨24103412, by rfl⟩ : syracuseStep 32137883 = 48206825) B48206825
theorem B21425255 : Blo 2087435 21425255 := bstep (se 1 (by rfl) ⟨16068941, by rfl⟩ : syracuseStep 21425255 = 32137883) B32137883
theorem B14283503 : Blo 2087435 14283503 := bstep (se 1 (by rfl) ⟨10712627, by rfl⟩ : syracuseStep 14283503 = 21425255) B21425255
theorem B9522335 : Blo 2087435 9522335 := bstep (se 1 (by rfl) ⟨7141751, by rfl⟩ : syracuseStep 9522335 = 14283503) B14283503
theorem B6348223 : Blo 2087435 6348223 := bstep (se 1 (by rfl) ⟨4761167, by rfl⟩ : syracuseStep 6348223 = 9522335) B9522335
theorem B33857189 : Blo 2087435 33857189 := bstep (se 4 (by rfl) ⟨3174111, by rfl⟩ : syracuseStep 33857189 = 6348223) B6348223
theorem B22571459 : Blo 2087435 22571459 := bstep (se 1 (by rfl) ⟨16928594, by rfl⟩ : syracuseStep 22571459 = 33857189) B33857189
theorem B15047639 : Blo 2087435 15047639 := bstep (se 1 (by rfl) ⟨11285729, by rfl⟩ : syracuseStep 15047639 = 22571459) B22571459
theorem B10031759 : Blo 2087435 10031759 := bstep (se 1 (by rfl) ⟨7523819, by rfl⟩ : syracuseStep 10031759 = 15047639) B15047639
theorem B6687839 : Blo 2087435 6687839 := bstep (se 1 (by rfl) ⟨5015879, by rfl⟩ : syracuseStep 6687839 = 10031759) B10031759
theorem B4458559 : Blo 2087435 4458559 := bstep (se 1 (by rfl) ⟨3343919, by rfl⟩ : syracuseStep 4458559 = 6687839) B6687839
theorem B5944745 : Blo 2087435 5944745 := bstep (se 2 (by rfl) ⟨2229279, by rfl⟩ : syracuseStep 5944745 = 4458559) B4458559
theorem B3963163 : Blo 2087435 3963163 := bstep (se 1 (by rfl) ⟨2972372, by rfl⟩ : syracuseStep 3963163 = 5944745) B5944745
theorem B5284217 : Blo 2087435 5284217 := bstep (se 2 (by rfl) ⟨1981581, by rfl⟩ : syracuseStep 5284217 = 3963163) B3963163
theorem B3522811 : Blo 2087435 3522811 := bstep (se 1 (by rfl) ⟨2642108, by rfl⟩ : syracuseStep 3522811 = 5284217) B5284217
theorem B4697081 : Blo 2087435 4697081 := bstep (se 2 (by rfl) ⟨1761405, by rfl⟩ : syracuseStep 4697081 = 3522811) B3522811
theorem B3131387 : Blo 2087435 3131387 := bstep (se 1 (by rfl) ⟨2348540, by rfl⟩ : syracuseStep 3131387 = 4697081) B4697081
theorem B2087591 : Blo 2087435 2087591 := bstep (se 1 (by rfl) ⟨1565693, by rfl⟩ : syracuseStep 2087591 = 3131387) B3131387
theorem B2348545 : Blo 2087435 2348545 := bbase (se 2 (by rfl) ⟨880704, by rfl⟩ : syracuseStep 2348545 = 1761409) (by norm_num)
theorem B3131393 : Blo 2087435 3131393 := bstep (se 2 (by rfl) ⟨1174272, by rfl⟩ : syracuseStep 3131393 = 2348545) B2348545
theorem B2087595 : Blo 2087435 2087595 := bstep (se 1 (by rfl) ⟨1565696, by rfl⟩ : syracuseStep 2087595 = 3131393) B3131393
theorem B5284237 : Blo 2087435 5284237 := bbase (se 3 (by rfl) ⟨990794, by rfl⟩ : syracuseStep 5284237 = 1981589) (by norm_num)
theorem B7045649 : Blo 2087435 7045649 := bstep (se 2 (by rfl) ⟨2642118, by rfl⟩ : syracuseStep 7045649 = 5284237) B5284237
theorem B4697099 : Blo 2087435 4697099 := bstep (se 1 (by rfl) ⟨3522824, by rfl⟩ : syracuseStep 4697099 = 7045649) B7045649
theorem B3131399 : Blo 2087435 3131399 := bstep (se 1 (by rfl) ⟨2348549, by rfl⟩ : syracuseStep 3131399 = 4697099) B4697099
theorem B2087599 : Blo 2087435 2087599 := bstep (se 1 (by rfl) ⟨1565699, by rfl⟩ : syracuseStep 2087599 = 3131399) B3131399
theorem B3131405 : Blo 2087435 3131405 := bbase (se 3 (by rfl) ⟨587138, by rfl⟩ : syracuseStep 3131405 = 1174277) (by norm_num)
theorem B2087603 : Blo 2087435 2087603 := bstep (se 1 (by rfl) ⟨1565702, by rfl⟩ : syracuseStep 2087603 = 3131405) B3131405
theorem B4697117 : Blo 2087435 4697117 := bbase (se 3 (by rfl) ⟨880709, by rfl⟩ : syracuseStep 4697117 = 1761419) (by norm_num)
theorem B3131411 : Blo 2087435 3131411 := bstep (se 1 (by rfl) ⟨2348558, by rfl⟩ : syracuseStep 3131411 = 4697117) B4697117
theorem B2087607 : Blo 2087435 2087607 := bstep (se 1 (by rfl) ⟨1565705, by rfl⟩ : syracuseStep 2087607 = 3131411) B3131411
theorem B3522845 : Blo 2087435 3522845 := bbase (se 3 (by rfl) ⟨660533, by rfl⟩ : syracuseStep 3522845 = 1321067) (by norm_num)
theorem B2348563 : Blo 2087435 2348563 := bstep (se 1 (by rfl) ⟨1761422, by rfl⟩ : syracuseStep 2348563 = 3522845) B3522845
theorem B3131417 : Blo 2087435 3131417 := bstep (se 2 (by rfl) ⟨1174281, by rfl⟩ : syracuseStep 3131417 = 2348563) B2348563
theorem B2087611 : Blo 2087435 2087611 := bstep (se 1 (by rfl) ⟨1565708, by rfl⟩ : syracuseStep 2087611 = 3131417) B3131417
theorem B13375829 : Blo 2087435 13375829 := bbase (se 10 (by rfl) ⟨19593, by rfl⟩ : syracuseStep 13375829 = 39187) (by norm_num)
theorem B8917219 : Blo 2087435 8917219 := bstep (se 1 (by rfl) ⟨6687914, by rfl⟩ : syracuseStep 8917219 = 13375829) B13375829
theorem B11889625 : Blo 2087435 11889625 := bstep (se 2 (by rfl) ⟨4458609, by rfl⟩ : syracuseStep 11889625 = 8917219) B8917219
theorem B15852833 : Blo 2087435 15852833 := bstep (se 2 (by rfl) ⟨5944812, by rfl⟩ : syracuseStep 15852833 = 11889625) B11889625
theorem B10568555 : Blo 2087435 10568555 := bstep (se 1 (by rfl) ⟨7926416, by rfl⟩ : syracuseStep 10568555 = 15852833) B15852833
theorem B7045703 : Blo 2087435 7045703 := bstep (se 1 (by rfl) ⟨5284277, by rfl⟩ : syracuseStep 7045703 = 10568555) B10568555
theorem B4697135 : Blo 2087435 4697135 := bstep (se 1 (by rfl) ⟨3522851, by rfl⟩ : syracuseStep 4697135 = 7045703) B7045703
theorem B3131423 : Blo 2087435 3131423 := bstep (se 1 (by rfl) ⟨2348567, by rfl⟩ : syracuseStep 3131423 = 4697135) B4697135
theorem B2087615 : Blo 2087435 2087615 := bstep (se 1 (by rfl) ⟨1565711, by rfl⟩ : syracuseStep 2087615 = 3131423) B3131423
theorem B3131429 : Blo 2087435 3131429 := bbase (se 4 (by rfl) ⟨293571, by rfl⟩ : syracuseStep 3131429 = 587143) (by norm_num)
theorem B2087619 : Blo 2087435 2087619 := bstep (se 1 (by rfl) ⟨1565714, by rfl⟩ : syracuseStep 2087619 = 3131429) B3131429
theorem B2642149 : Blo 2087435 2642149 := bbase (se 4 (by rfl) ⟨247701, by rfl⟩ : syracuseStep 2642149 = 495403) (by norm_num)
theorem B3522865 : Blo 2087435 3522865 := bstep (se 2 (by rfl) ⟨1321074, by rfl⟩ : syracuseStep 3522865 = 2642149) B2642149
theorem B4697153 : Blo 2087435 4697153 := bstep (se 2 (by rfl) ⟨1761432, by rfl⟩ : syracuseStep 4697153 = 3522865) B3522865
theorem B3131435 : Blo 2087435 3131435 := bstep (se 1 (by rfl) ⟨2348576, by rfl⟩ : syracuseStep 3131435 = 4697153) B4697153
theorem B2087623 : Blo 2087435 2087623 := bstep (se 1 (by rfl) ⟨1565717, by rfl⟩ : syracuseStep 2087623 = 3131435) B3131435
theorem B2348581 : Blo 2087435 2348581 := bbase (se 4 (by rfl) ⟨220179, by rfl⟩ : syracuseStep 2348581 = 440359) (by norm_num)
theorem B3131441 : Blo 2087435 3131441 := bstep (se 2 (by rfl) ⟨1174290, by rfl⟩ : syracuseStep 3131441 = 2348581) B2348581
theorem B2087627 : Blo 2087435 2087627 := bstep (se 1 (by rfl) ⟨1565720, by rfl⟩ : syracuseStep 2087627 = 3131441) B3131441
theorem B9522517 : Blo 2087435 9522517 := bbase (se 11 (by rfl) ⟨6974, by rfl⟩ : syracuseStep 9522517 = 13949) (by norm_num)
theorem B12696689 : Blo 2087435 12696689 := bstep (se 2 (by rfl) ⟨4761258, by rfl⟩ : syracuseStep 12696689 = 9522517) B9522517
theorem B33857837 : Blo 2087435 33857837 := bstep (se 3 (by rfl) ⟨6348344, by rfl⟩ : syracuseStep 33857837 = 12696689) B12696689
theorem B22571891 : Blo 2087435 22571891 := bstep (se 1 (by rfl) ⟨16928918, by rfl⟩ : syracuseStep 22571891 = 33857837) B33857837
theorem B15047927 : Blo 2087435 15047927 := bstep (se 1 (by rfl) ⟨11285945, by rfl⟩ : syracuseStep 15047927 = 22571891) B22571891
theorem B10031951 : Blo 2087435 10031951 := bstep (se 1 (by rfl) ⟨7523963, by rfl⟩ : syracuseStep 10031951 = 15047927) B15047927
theorem B6687967 : Blo 2087435 6687967 := bstep (se 1 (by rfl) ⟨5015975, by rfl⟩ : syracuseStep 6687967 = 10031951) B10031951
theorem B8917289 : Blo 2087435 8917289 := bstep (se 2 (by rfl) ⟨3343983, by rfl⟩ : syracuseStep 8917289 = 6687967) B6687967
theorem B5944859 : Blo 2087435 5944859 := bstep (se 1 (by rfl) ⟨4458644, by rfl⟩ : syracuseStep 5944859 = 8917289) B8917289
theorem B3963239 : Blo 2087435 3963239 := bstep (se 1 (by rfl) ⟨2972429, by rfl⟩ : syracuseStep 3963239 = 5944859) B5944859
theorem B2642159 : Blo 2087435 2642159 := bstep (se 1 (by rfl) ⟨1981619, by rfl⟩ : syracuseStep 2642159 = 3963239) B3963239
theorem B7045757 : Blo 2087435 7045757 := bstep (se 3 (by rfl) ⟨1321079, by rfl⟩ : syracuseStep 7045757 = 2642159) B2642159
theorem B4697171 : Blo 2087435 4697171 := bstep (se 1 (by rfl) ⟨3522878, by rfl⟩ : syracuseStep 4697171 = 7045757) B7045757
theorem B3131447 : Blo 2087435 3131447 := bstep (se 1 (by rfl) ⟨2348585, by rfl⟩ : syracuseStep 3131447 = 4697171) B4697171
theorem B2087631 : Blo 2087435 2087631 := bstep (se 1 (by rfl) ⟨1565723, by rfl⟩ : syracuseStep 2087631 = 3131447) B3131447
theorem B3131453 : Blo 2087435 3131453 := bbase (se 3 (by rfl) ⟨587147, by rfl⟩ : syracuseStep 3131453 = 1174295) (by norm_num)
theorem B2087635 : Blo 2087435 2087635 := bstep (se 1 (by rfl) ⟨1565726, by rfl⟩ : syracuseStep 2087635 = 3131453) B3131453
theorem B4697189 : Blo 2087435 4697189 := bbase (se 4 (by rfl) ⟨440361, by rfl⟩ : syracuseStep 4697189 = 880723) (by norm_num)
theorem B3131459 : Blo 2087435 3131459 := bstep (se 1 (by rfl) ⟨2348594, by rfl⟩ : syracuseStep 3131459 = 4697189) B4697189
theorem B2087639 : Blo 2087435 2087639 := bstep (se 1 (by rfl) ⟨1565729, by rfl⟩ : syracuseStep 2087639 = 3131459) B3131459
theorem B5284349 : Blo 2087435 5284349 := bbase (se 3 (by rfl) ⟨990815, by rfl⟩ : syracuseStep 5284349 = 1981631) (by norm_num)
theorem B3522899 : Blo 2087435 3522899 := bstep (se 1 (by rfl) ⟨2642174, by rfl⟩ : syracuseStep 3522899 = 5284349) B5284349
theorem B2348599 : Blo 2087435 2348599 := bstep (se 1 (by rfl) ⟨1761449, by rfl⟩ : syracuseStep 2348599 = 3522899) B3522899
theorem B3131465 : Blo 2087435 3131465 := bstep (se 2 (by rfl) ⟨1174299, by rfl⟩ : syracuseStep 3131465 = 2348599) B2348599
theorem B2087643 : Blo 2087435 2087643 := bstep (se 1 (by rfl) ⟨1565732, by rfl⟩ : syracuseStep 2087643 = 3131465) B3131465
theorem B3963269 : Blo 2087435 3963269 := bbase (se 4 (by rfl) ⟨371556, by rfl⟩ : syracuseStep 3963269 = 743113) (by norm_num)
theorem B10568717 : Blo 2087435 10568717 := bstep (se 3 (by rfl) ⟨1981634, by rfl⟩ : syracuseStep 10568717 = 3963269) B3963269
theorem B7045811 : Blo 2087435 7045811 := bstep (se 1 (by rfl) ⟨5284358, by rfl⟩ : syracuseStep 7045811 = 10568717) B10568717
theorem B4697207 : Blo 2087435 4697207 := bstep (se 1 (by rfl) ⟨3522905, by rfl⟩ : syracuseStep 4697207 = 7045811) B7045811
theorem B3131471 : Blo 2087435 3131471 := bstep (se 1 (by rfl) ⟨2348603, by rfl⟩ : syracuseStep 3131471 = 4697207) B4697207
theorem B2087647 : Blo 2087435 2087647 := bstep (se 1 (by rfl) ⟨1565735, by rfl⟩ : syracuseStep 2087647 = 3131471) B3131471
theorem B3131477 : Blo 2087435 3131477 := bbase (se 8 (by rfl) ⟨18348, by rfl⟩ : syracuseStep 3131477 = 36697) (by norm_num)
theorem B2087651 : Blo 2087435 2087651 := bstep (se 1 (by rfl) ⟨1565738, by rfl⟩ : syracuseStep 2087651 = 3131477) B3131477
theorem B2380657 : Blo 2087435 2380657 := bbase (se 2 (by rfl) ⟨892746, by rfl⟩ : syracuseStep 2380657 = 1785493) (by norm_num)
theorem B3174209 : Blo 2087435 3174209 := bstep (se 2 (by rfl) ⟨1190328, by rfl⟩ : syracuseStep 3174209 = 2380657) B2380657
theorem B2116139 : Blo 2087435 2116139 := bstep (se 1 (by rfl) ⟨1587104, by rfl⟩ : syracuseStep 2116139 = 3174209) B3174209
theorem B5643037 : Blo 2087435 5643037 := bstep (se 3 (by rfl) ⟨1058069, by rfl⟩ : syracuseStep 5643037 = 2116139) B2116139
theorem B30096197 : Blo 2087435 30096197 := bstep (se 4 (by rfl) ⟨2821518, by rfl⟩ : syracuseStep 30096197 = 5643037) B5643037
theorem B20064131 : Blo 2087435 20064131 := bstep (se 1 (by rfl) ⟨15048098, by rfl⟩ : syracuseStep 20064131 = 30096197) B30096197
theorem B13376087 : Blo 2087435 13376087 := bstep (se 1 (by rfl) ⟨10032065, by rfl⟩ : syracuseStep 13376087 = 20064131) B20064131
theorem B8917391 : Blo 2087435 8917391 := bstep (se 1 (by rfl) ⟨6688043, by rfl⟩ : syracuseStep 8917391 = 13376087) B13376087
theorem B5944927 : Blo 2087435 5944927 := bstep (se 1 (by rfl) ⟨4458695, by rfl⟩ : syracuseStep 5944927 = 8917391) B8917391
theorem B7926569 : Blo 2087435 7926569 := bstep (se 2 (by rfl) ⟨2972463, by rfl⟩ : syracuseStep 7926569 = 5944927) B5944927
theorem B5284379 : Blo 2087435 5284379 := bstep (se 1 (by rfl) ⟨3963284, by rfl⟩ : syracuseStep 5284379 = 7926569) B7926569
theorem B3522919 : Blo 2087435 3522919 := bstep (se 1 (by rfl) ⟨2642189, by rfl⟩ : syracuseStep 3522919 = 5284379) B5284379
theorem B4697225 : Blo 2087435 4697225 := bstep (se 2 (by rfl) ⟨1761459, by rfl⟩ : syracuseStep 4697225 = 3522919) B3522919
theorem B3131483 : Blo 2087435 3131483 := bstep (se 1 (by rfl) ⟨2348612, by rfl⟩ : syracuseStep 3131483 = 4697225) B4697225
theorem B2087655 : Blo 2087435 2087655 := bstep (se 1 (by rfl) ⟨1565741, by rfl⟩ : syracuseStep 2087655 = 3131483) B3131483
theorem B2348617 : Blo 2087435 2348617 := bbase (se 2 (by rfl) ⟨880731, by rfl⟩ : syracuseStep 2348617 = 1761463) (by norm_num)
theorem B3131489 : Blo 2087435 3131489 := bstep (se 2 (by rfl) ⟨1174308, by rfl⟩ : syracuseStep 3131489 = 2348617) B2348617
theorem B2087659 : Blo 2087435 2087659 := bstep (se 1 (by rfl) ⟨1565744, by rfl⟩ : syracuseStep 2087659 = 3131489) B3131489
theorem B38090645 : Blo 2087435 38090645 := bbase (se 6 (by rfl) ⟨892749, by rfl⟩ : syracuseStep 38090645 = 1785499) (by norm_num)
theorem B25393763 : Blo 2087435 25393763 := bstep (se 1 (by rfl) ⟨19045322, by rfl⟩ : syracuseStep 25393763 = 38090645) B38090645
theorem B16929175 : Blo 2087435 16929175 := bstep (se 1 (by rfl) ⟨12696881, by rfl⟩ : syracuseStep 16929175 = 25393763) B25393763
theorem B22572233 : Blo 2087435 22572233 := bstep (se 2 (by rfl) ⟨8464587, by rfl⟩ : syracuseStep 22572233 = 16929175) B16929175
theorem B15048155 : Blo 2087435 15048155 := bstep (se 1 (by rfl) ⟨11286116, by rfl⟩ : syracuseStep 15048155 = 22572233) B22572233
theorem B10032103 : Blo 2087435 10032103 := bstep (se 1 (by rfl) ⟨7524077, by rfl⟩ : syracuseStep 10032103 = 15048155) B15048155
theorem B13376137 : Blo 2087435 13376137 := bstep (se 2 (by rfl) ⟨5016051, by rfl⟩ : syracuseStep 13376137 = 10032103) B10032103
theorem B17834849 : Blo 2087435 17834849 := bstep (se 2 (by rfl) ⟨6688068, by rfl⟩ : syracuseStep 17834849 = 13376137) B13376137
theorem B11889899 : Blo 2087435 11889899 := bstep (se 1 (by rfl) ⟨8917424, by rfl⟩ : syracuseStep 11889899 = 17834849) B17834849
theorem B7926599 : Blo 2087435 7926599 := bstep (se 1 (by rfl) ⟨5944949, by rfl⟩ : syracuseStep 7926599 = 11889899) B11889899
theorem B5284399 : Blo 2087435 5284399 := bstep (se 1 (by rfl) ⟨3963299, by rfl⟩ : syracuseStep 5284399 = 7926599) B7926599
theorem B7045865 : Blo 2087435 7045865 := bstep (se 2 (by rfl) ⟨2642199, by rfl⟩ : syracuseStep 7045865 = 5284399) B5284399
theorem B4697243 : Blo 2087435 4697243 := bstep (se 1 (by rfl) ⟨3522932, by rfl⟩ : syracuseStep 4697243 = 7045865) B7045865
theorem B3131495 : Blo 2087435 3131495 := bstep (se 1 (by rfl) ⟨2348621, by rfl⟩ : syracuseStep 3131495 = 4697243) B4697243
theorem B2087663 : Blo 2087435 2087663 := bstep (se 1 (by rfl) ⟨1565747, by rfl⟩ : syracuseStep 2087663 = 3131495) B3131495
theorem B3131501 : Blo 2087435 3131501 := bbase (se 3 (by rfl) ⟨587156, by rfl⟩ : syracuseStep 3131501 = 1174313) (by norm_num)
theorem B2087667 : Blo 2087435 2087667 := bstep (se 1 (by rfl) ⟨1565750, by rfl⟩ : syracuseStep 2087667 = 3131501) B3131501
theorem B4697261 : Blo 2087435 4697261 := bbase (se 3 (by rfl) ⟨880736, by rfl⟩ : syracuseStep 4697261 = 1761473) (by norm_num)
theorem B3131507 : Blo 2087435 3131507 := bstep (se 1 (by rfl) ⟨2348630, by rfl⟩ : syracuseStep 3131507 = 4697261) B4697261
theorem B2087671 : Blo 2087435 2087671 := bstep (se 1 (by rfl) ⟨1565753, by rfl⟩ : syracuseStep 2087671 = 3131507) B3131507
theorem B2508041 : Blo 2087435 2508041 := bbase (se 2 (by rfl) ⟨940515, by rfl⟩ : syracuseStep 2508041 = 1881031) (by norm_num)
theorem B6688109 : Blo 2087435 6688109 := bstep (se 3 (by rfl) ⟨1254020, by rfl⟩ : syracuseStep 6688109 = 2508041) B2508041
theorem B4458739 : Blo 2087435 4458739 := bstep (se 1 (by rfl) ⟨3344054, by rfl⟩ : syracuseStep 4458739 = 6688109) B6688109
theorem B5944985 : Blo 2087435 5944985 := bstep (se 2 (by rfl) ⟨2229369, by rfl⟩ : syracuseStep 5944985 = 4458739) B4458739
theorem B3963323 : Blo 2087435 3963323 := bstep (se 1 (by rfl) ⟨2972492, by rfl⟩ : syracuseStep 3963323 = 5944985) B5944985
theorem B2642215 : Blo 2087435 2642215 := bstep (se 1 (by rfl) ⟨1981661, by rfl⟩ : syracuseStep 2642215 = 3963323) B3963323
theorem B3522953 : Blo 2087435 3522953 := bstep (se 2 (by rfl) ⟨1321107, by rfl⟩ : syracuseStep 3522953 = 2642215) B2642215
theorem B2348635 : Blo 2087435 2348635 := bstep (se 1 (by rfl) ⟨1761476, by rfl⟩ : syracuseStep 2348635 = 3522953) B3522953
theorem B3131513 : Blo 2087435 3131513 := bstep (se 2 (by rfl) ⟨1174317, by rfl⟩ : syracuseStep 3131513 = 2348635) B2348635
theorem B2087675 : Blo 2087435 2087675 := bstep (se 1 (by rfl) ⟨1565756, by rfl⟩ : syracuseStep 2087675 = 3131513) B3131513
theorem B3174245 : Blo 2087435 3174245 := bbase (se 4 (by rfl) ⟨297585, by rfl⟩ : syracuseStep 3174245 = 595171) (by norm_num)
theorem B2116163 : Blo 2087435 2116163 := bstep (se 1 (by rfl) ⟨1587122, by rfl⟩ : syracuseStep 2116163 = 3174245) B3174245
theorem B5643101 : Blo 2087435 5643101 := bstep (se 3 (by rfl) ⟨1058081, by rfl⟩ : syracuseStep 5643101 = 2116163) B2116163
theorem B15048269 : Blo 2087435 15048269 := bstep (se 3 (by rfl) ⟨2821550, by rfl⟩ : syracuseStep 15048269 = 5643101) B5643101
theorem B10032179 : Blo 2087435 10032179 := bstep (se 1 (by rfl) ⟨7524134, by rfl⟩ : syracuseStep 10032179 = 15048269) B15048269
theorem B26752477 : Blo 2087435 26752477 := bstep (se 3 (by rfl) ⟨5016089, by rfl⟩ : syracuseStep 26752477 = 10032179) B10032179
theorem B35669969 : Blo 2087435 35669969 := bstep (se 2 (by rfl) ⟨13376238, by rfl⟩ : syracuseStep 35669969 = 26752477) B26752477
theorem B23779979 : Blo 2087435 23779979 := bstep (se 1 (by rfl) ⟨17834984, by rfl⟩ : syracuseStep 23779979 = 35669969) B35669969
theorem B15853319 : Blo 2087435 15853319 := bstep (se 1 (by rfl) ⟨11889989, by rfl⟩ : syracuseStep 15853319 = 23779979) B23779979
theorem B10568879 : Blo 2087435 10568879 := bstep (se 1 (by rfl) ⟨7926659, by rfl⟩ : syracuseStep 10568879 = 15853319) B15853319
theorem B7045919 : Blo 2087435 7045919 := bstep (se 1 (by rfl) ⟨5284439, by rfl⟩ : syracuseStep 7045919 = 10568879) B10568879
theorem B4697279 : Blo 2087435 4697279 := bstep (se 1 (by rfl) ⟨3522959, by rfl⟩ : syracuseStep 4697279 = 7045919) B7045919
theorem B3131519 : Blo 2087435 3131519 := bstep (se 1 (by rfl) ⟨2348639, by rfl⟩ : syracuseStep 3131519 = 4697279) B4697279
theorem B2087679 : Blo 2087435 2087679 := bstep (se 1 (by rfl) ⟨1565759, by rfl⟩ : syracuseStep 2087679 = 3131519) B3131519
theorem B3131525 : Blo 2087435 3131525 := bbase (se 4 (by rfl) ⟨293580, by rfl⟩ : syracuseStep 3131525 = 587161) (by norm_num)
theorem B2087683 : Blo 2087435 2087683 := bstep (se 1 (by rfl) ⟨1565762, by rfl⟩ : syracuseStep 2087683 = 3131525) B3131525
theorem B3522973 : Blo 2087435 3522973 := bbase (se 3 (by rfl) ⟨660557, by rfl⟩ : syracuseStep 3522973 = 1321115) (by norm_num)
theorem B4697297 : Blo 2087435 4697297 := bstep (se 2 (by rfl) ⟨1761486, by rfl⟩ : syracuseStep 4697297 = 3522973) B3522973
theorem B3131531 : Blo 2087435 3131531 := bstep (se 1 (by rfl) ⟨2348648, by rfl⟩ : syracuseStep 3131531 = 4697297) B4697297
theorem B2087687 : Blo 2087435 2087687 := bstep (se 1 (by rfl) ⟨1565765, by rfl⟩ : syracuseStep 2087687 = 3131531) B3131531
theorem B2348653 : Blo 2087435 2348653 := bbase (se 3 (by rfl) ⟨440372, by rfl⟩ : syracuseStep 2348653 = 880745) (by norm_num)
theorem B3131537 : Blo 2087435 3131537 := bstep (se 2 (by rfl) ⟨1174326, by rfl⟩ : syracuseStep 3131537 = 2348653) B2348653
theorem B2087691 : Blo 2087435 2087691 := bstep (se 1 (by rfl) ⟨1565768, by rfl⟩ : syracuseStep 2087691 = 3131537) B3131537
theorem B7045973 : Blo 2087435 7045973 := bbase (se 9 (by rfl) ⟨20642, by rfl⟩ : syracuseStep 7045973 = 41285) (by norm_num)
theorem B4697315 : Blo 2087435 4697315 := bstep (se 1 (by rfl) ⟨3522986, by rfl⟩ : syracuseStep 4697315 = 7045973) B7045973
theorem B3131543 : Blo 2087435 3131543 := bstep (se 1 (by rfl) ⟨2348657, by rfl⟩ : syracuseStep 3131543 = 4697315) B4697315
theorem B2087695 : Blo 2087435 2087695 := bstep (se 1 (by rfl) ⟨1565771, by rfl⟩ : syracuseStep 2087695 = 3131543) B3131543
theorem B3131549 : Blo 2087435 3131549 := bbase (se 3 (by rfl) ⟨587165, by rfl⟩ : syracuseStep 3131549 = 1174331) (by norm_num)
theorem B2087699 : Blo 2087435 2087699 := bstep (se 1 (by rfl) ⟨1565774, by rfl⟩ : syracuseStep 2087699 = 3131549) B3131549
theorem B4697333 : Blo 2087435 4697333 := bbase (se 5 (by rfl) ⟨220187, by rfl⟩ : syracuseStep 4697333 = 440375) (by norm_num)
theorem B3131555 : Blo 2087435 3131555 := bstep (se 1 (by rfl) ⟨2348666, by rfl⟩ : syracuseStep 3131555 = 4697333) B4697333
theorem B2087703 : Blo 2087435 2087703 := bstep (se 1 (by rfl) ⟨1565777, by rfl⟩ : syracuseStep 2087703 = 3131555) B3131555
theorem B6779461 : Blo 2087435 6779461 := bbase (se 4 (by rfl) ⟨635574, by rfl⟩ : syracuseStep 6779461 = 1271149) (by norm_num)
theorem B9039281 : Blo 2087435 9039281 := bstep (se 2 (by rfl) ⟨3389730, by rfl⟩ : syracuseStep 9039281 = 6779461) B6779461
theorem B24104749 : Blo 2087435 24104749 := bstep (se 3 (by rfl) ⟨4519640, by rfl⟩ : syracuseStep 24104749 = 9039281) B9039281
theorem B32139665 : Blo 2087435 32139665 := bstep (se 2 (by rfl) ⟨12052374, by rfl⟩ : syracuseStep 32139665 = 24104749) B24104749
theorem B21426443 : Blo 2087435 21426443 := bstep (se 1 (by rfl) ⟨16069832, by rfl⟩ : syracuseStep 21426443 = 32139665) B32139665
theorem B14284295 : Blo 2087435 14284295 := bstep (se 1 (by rfl) ⟨10713221, by rfl⟩ : syracuseStep 14284295 = 21426443) B21426443
theorem B9522863 : Blo 2087435 9522863 := bstep (se 1 (by rfl) ⟨7142147, by rfl⟩ : syracuseStep 9522863 = 14284295) B14284295
theorem B6348575 : Blo 2087435 6348575 := bstep (se 1 (by rfl) ⟨4761431, by rfl⟩ : syracuseStep 6348575 = 9522863) B9522863
theorem B16929533 : Blo 2087435 16929533 := bstep (se 3 (by rfl) ⟨3174287, by rfl⟩ : syracuseStep 16929533 = 6348575) B6348575
theorem B45145421 : Blo 2087435 45145421 := bstep (se 3 (by rfl) ⟨8464766, by rfl⟩ : syracuseStep 45145421 = 16929533) B16929533
theorem B30096947 : Blo 2087435 30096947 := bstep (se 1 (by rfl) ⟨22572710, by rfl⟩ : syracuseStep 30096947 = 45145421) B45145421
theorem B20064631 : Blo 2087435 20064631 := bstep (se 1 (by rfl) ⟨15048473, by rfl⟩ : syracuseStep 20064631 = 30096947) B30096947
theorem B26752841 : Blo 2087435 26752841 := bstep (se 2 (by rfl) ⟨10032315, by rfl⟩ : syracuseStep 26752841 = 20064631) B20064631
theorem B17835227 : Blo 2087435 17835227 := bstep (se 1 (by rfl) ⟨13376420, by rfl⟩ : syracuseStep 17835227 = 26752841) B26752841
theorem B11890151 : Blo 2087435 11890151 := bstep (se 1 (by rfl) ⟨8917613, by rfl⟩ : syracuseStep 11890151 = 17835227) B17835227
theorem B7926767 : Blo 2087435 7926767 := bstep (se 1 (by rfl) ⟨5945075, by rfl⟩ : syracuseStep 7926767 = 11890151) B11890151
theorem B5284511 : Blo 2087435 5284511 := bstep (se 1 (by rfl) ⟨3963383, by rfl⟩ : syracuseStep 5284511 = 7926767) B7926767
theorem B3523007 : Blo 2087435 3523007 := bstep (se 1 (by rfl) ⟨2642255, by rfl⟩ : syracuseStep 3523007 = 5284511) B5284511
theorem B2348671 : Blo 2087435 2348671 := bstep (se 1 (by rfl) ⟨1761503, by rfl⟩ : syracuseStep 2348671 = 3523007) B3523007
theorem B3131561 : Blo 2087435 3131561 := bstep (se 2 (by rfl) ⟨1174335, by rfl⟩ : syracuseStep 3131561 = 2348671) B2348671
theorem B2087707 : Blo 2087435 2087707 := bstep (se 1 (by rfl) ⟨1565780, by rfl⟩ : syracuseStep 2087707 = 3131561) B3131561
theorem B5356621 : Blo 2087435 5356621 := bbase (se 3 (by rfl) ⟨1004366, by rfl⟩ : syracuseStep 5356621 = 2008733) (by norm_num)
theorem B28568645 : Blo 2087435 28568645 := bstep (se 4 (by rfl) ⟨2678310, by rfl⟩ : syracuseStep 28568645 = 5356621) B5356621
theorem B19045763 : Blo 2087435 19045763 := bstep (se 1 (by rfl) ⟨14284322, by rfl⟩ : syracuseStep 19045763 = 28568645) B28568645
theorem B12697175 : Blo 2087435 12697175 := bstep (se 1 (by rfl) ⟨9522881, by rfl⟩ : syracuseStep 12697175 = 19045763) B19045763
theorem B33859133 : Blo 2087435 33859133 := bstep (se 3 (by rfl) ⟨6348587, by rfl⟩ : syracuseStep 33859133 = 12697175) B12697175
theorem B22572755 : Blo 2087435 22572755 := bstep (se 1 (by rfl) ⟨16929566, by rfl⟩ : syracuseStep 22572755 = 33859133) B33859133
theorem B15048503 : Blo 2087435 15048503 := bstep (se 1 (by rfl) ⟨11286377, by rfl⟩ : syracuseStep 15048503 = 22572755) B22572755
theorem B10032335 : Blo 2087435 10032335 := bstep (se 1 (by rfl) ⟨7524251, by rfl⟩ : syracuseStep 10032335 = 15048503) B15048503
theorem B6688223 : Blo 2087435 6688223 := bstep (se 1 (by rfl) ⟨5016167, by rfl⟩ : syracuseStep 6688223 = 10032335) B10032335
theorem B4458815 : Blo 2087435 4458815 := bstep (se 1 (by rfl) ⟨3344111, by rfl⟩ : syracuseStep 4458815 = 6688223) B6688223
theorem B2972543 : Blo 2087435 2972543 := bstep (se 1 (by rfl) ⟨2229407, by rfl⟩ : syracuseStep 2972543 = 4458815) B4458815
theorem B7926781 : Blo 2087435 7926781 := bstep (se 3 (by rfl) ⟨1486271, by rfl⟩ : syracuseStep 7926781 = 2972543) B2972543
theorem B10569041 : Blo 2087435 10569041 := bstep (se 2 (by rfl) ⟨3963390, by rfl⟩ : syracuseStep 10569041 = 7926781) B7926781
theorem B7046027 : Blo 2087435 7046027 := bstep (se 1 (by rfl) ⟨5284520, by rfl⟩ : syracuseStep 7046027 = 10569041) B10569041
theorem B4697351 : Blo 2087435 4697351 := bstep (se 1 (by rfl) ⟨3523013, by rfl⟩ : syracuseStep 4697351 = 7046027) B7046027
theorem B3131567 : Blo 2087435 3131567 := bstep (se 1 (by rfl) ⟨2348675, by rfl⟩ : syracuseStep 3131567 = 4697351) B4697351
theorem B2087711 : Blo 2087435 2087711 := bstep (se 1 (by rfl) ⟨1565783, by rfl⟩ : syracuseStep 2087711 = 3131567) B3131567
theorem B3131573 : Blo 2087435 3131573 := bbase (se 5 (by rfl) ⟨146792, by rfl⟩ : syracuseStep 3131573 = 293585) (by norm_num)
theorem B2087715 : Blo 2087435 2087715 := bstep (se 1 (by rfl) ⟨1565786, by rfl⟩ : syracuseStep 2087715 = 3131573) B3131573
theorem B5284541 : Blo 2087435 5284541 := bbase (se 3 (by rfl) ⟨990851, by rfl⟩ : syracuseStep 5284541 = 1981703) (by norm_num)
theorem B3523027 : Blo 2087435 3523027 := bstep (se 1 (by rfl) ⟨2642270, by rfl⟩ : syracuseStep 3523027 = 5284541) B5284541
theorem B4697369 : Blo 2087435 4697369 := bstep (se 2 (by rfl) ⟨1761513, by rfl⟩ : syracuseStep 4697369 = 3523027) B3523027
theorem B3131579 : Blo 2087435 3131579 := bstep (se 1 (by rfl) ⟨2348684, by rfl⟩ : syracuseStep 3131579 = 4697369) B4697369
theorem B2087719 : Blo 2087435 2087719 := bstep (se 1 (by rfl) ⟨1565789, by rfl⟩ : syracuseStep 2087719 = 3131579) B3131579
theorem B2348689 : Blo 2087435 2348689 := bbase (se 2 (by rfl) ⟨880758, by rfl⟩ : syracuseStep 2348689 = 1761517) (by norm_num)
theorem B3131585 : Blo 2087435 3131585 := bstep (se 2 (by rfl) ⟨1174344, by rfl⟩ : syracuseStep 3131585 = 2348689) B2348689
theorem B2087723 : Blo 2087435 2087723 := bstep (se 1 (by rfl) ⟨1565792, by rfl⟩ : syracuseStep 2087723 = 3131585) B3131585
theorem B3963421 : Blo 2087435 3963421 := bbase (se 3 (by rfl) ⟨743141, by rfl⟩ : syracuseStep 3963421 = 1486283) (by norm_num)
theorem B5284561 : Blo 2087435 5284561 := bstep (se 2 (by rfl) ⟨1981710, by rfl⟩ : syracuseStep 5284561 = 3963421) B3963421
theorem B7046081 : Blo 2087435 7046081 := bstep (se 2 (by rfl) ⟨2642280, by rfl⟩ : syracuseStep 7046081 = 5284561) B5284561
theorem B4697387 : Blo 2087435 4697387 := bstep (se 1 (by rfl) ⟨3523040, by rfl⟩ : syracuseStep 4697387 = 7046081) B7046081
theorem B3131591 : Blo 2087435 3131591 := bstep (se 1 (by rfl) ⟨2348693, by rfl⟩ : syracuseStep 3131591 = 4697387) B4697387
theorem B2087727 : Blo 2087435 2087727 := bstep (se 1 (by rfl) ⟨1565795, by rfl⟩ : syracuseStep 2087727 = 3131591) B3131591
theorem B3131597 : Blo 2087435 3131597 := bbase (se 3 (by rfl) ⟨587174, by rfl⟩ : syracuseStep 3131597 = 1174349) (by norm_num)
theorem B2087731 : Blo 2087435 2087731 := bstep (se 1 (by rfl) ⟨1565798, by rfl⟩ : syracuseStep 2087731 = 3131597) B3131597
theorem B4697405 : Blo 2087435 4697405 := bbase (se 3 (by rfl) ⟨880763, by rfl⟩ : syracuseStep 4697405 = 1761527) (by norm_num)
theorem B3131603 : Blo 2087435 3131603 := bstep (se 1 (by rfl) ⟨2348702, by rfl⟩ : syracuseStep 3131603 = 4697405) B4697405
theorem B2087735 : Blo 2087435 2087735 := bstep (se 1 (by rfl) ⟨1565801, by rfl⟩ : syracuseStep 2087735 = 3131603) B3131603
theorem B3523061 : Blo 2087435 3523061 := bbase (se 5 (by rfl) ⟨165143, by rfl⟩ : syracuseStep 3523061 = 330287) (by norm_num)
theorem B2348707 : Blo 2087435 2348707 := bstep (se 1 (by rfl) ⟨1761530, by rfl⟩ : syracuseStep 2348707 = 3523061) B3523061
theorem B3131609 : Blo 2087435 3131609 := bstep (se 2 (by rfl) ⟨1174353, by rfl⟩ : syracuseStep 3131609 = 2348707) B2348707
theorem B2087739 : Blo 2087435 2087739 := bstep (se 1 (by rfl) ⟨1565804, by rfl⟩ : syracuseStep 2087739 = 3131609) B3131609
theorem B6688325 : Blo 2087435 6688325 := bbase (se 4 (by rfl) ⟨627030, by rfl⟩ : syracuseStep 6688325 = 1254061) (by norm_num)
theorem B4458883 : Blo 2087435 4458883 := bstep (se 1 (by rfl) ⟨3344162, by rfl⟩ : syracuseStep 4458883 = 6688325) B6688325
theorem B5945177 : Blo 2087435 5945177 := bstep (se 2 (by rfl) ⟨2229441, by rfl⟩ : syracuseStep 5945177 = 4458883) B4458883
theorem B15853805 : Blo 2087435 15853805 := bstep (se 3 (by rfl) ⟨2972588, by rfl⟩ : syracuseStep 15853805 = 5945177) B5945177
theorem B10569203 : Blo 2087435 10569203 := bstep (se 1 (by rfl) ⟨7926902, by rfl⟩ : syracuseStep 10569203 = 15853805) B15853805
theorem B7046135 : Blo 2087435 7046135 := bstep (se 1 (by rfl) ⟨5284601, by rfl⟩ : syracuseStep 7046135 = 10569203) B10569203
theorem B4697423 : Blo 2087435 4697423 := bstep (se 1 (by rfl) ⟨3523067, by rfl⟩ : syracuseStep 4697423 = 7046135) B7046135
theorem B3131615 : Blo 2087435 3131615 := bstep (se 1 (by rfl) ⟨2348711, by rfl⟩ : syracuseStep 3131615 = 4697423) B4697423
theorem B2087743 : Blo 2087435 2087743 := bstep (se 1 (by rfl) ⟨1565807, by rfl⟩ : syracuseStep 2087743 = 3131615) B3131615
theorem B3131621 : Blo 2087435 3131621 := bbase (se 4 (by rfl) ⟨293589, by rfl⟩ : syracuseStep 3131621 = 587179) (by norm_num)
theorem B2087747 : Blo 2087435 2087747 := bstep (se 1 (by rfl) ⟨1565810, by rfl⟩ : syracuseStep 2087747 = 3131621) B3131621
theorem B4458901 : Blo 2087435 4458901 := bbase (se 6 (by rfl) ⟨104505, by rfl⟩ : syracuseStep 4458901 = 209011) (by norm_num)
theorem B5945201 : Blo 2087435 5945201 := bstep (se 2 (by rfl) ⟨2229450, by rfl⟩ : syracuseStep 5945201 = 4458901) B4458901
theorem B3963467 : Blo 2087435 3963467 := bstep (se 1 (by rfl) ⟨2972600, by rfl⟩ : syracuseStep 3963467 = 5945201) B5945201
theorem B2642311 : Blo 2087435 2642311 := bstep (se 1 (by rfl) ⟨1981733, by rfl⟩ : syracuseStep 2642311 = 3963467) B3963467
theorem B3523081 : Blo 2087435 3523081 := bstep (se 2 (by rfl) ⟨1321155, by rfl⟩ : syracuseStep 3523081 = 2642311) B2642311
theorem B4697441 : Blo 2087435 4697441 := bstep (se 2 (by rfl) ⟨1761540, by rfl⟩ : syracuseStep 4697441 = 3523081) B3523081
theorem B3131627 : Blo 2087435 3131627 := bstep (se 1 (by rfl) ⟨2348720, by rfl⟩ : syracuseStep 3131627 = 4697441) B4697441
theorem B2087751 : Blo 2087435 2087751 := bstep (se 1 (by rfl) ⟨1565813, by rfl⟩ : syracuseStep 2087751 = 3131627) B3131627
theorem B2348725 : Blo 2087435 2348725 := bbase (se 5 (by rfl) ⟨110096, by rfl⟩ : syracuseStep 2348725 = 220193) (by norm_num)
theorem B3131633 : Blo 2087435 3131633 := bstep (se 2 (by rfl) ⟨1174362, by rfl⟩ : syracuseStep 3131633 = 2348725) B2348725
theorem B2087755 : Blo 2087435 2087755 := bstep (se 1 (by rfl) ⟨1565816, by rfl⟩ : syracuseStep 2087755 = 3131633) B3131633
theorem B2642321 : Blo 2087435 2642321 := bbase (se 2 (by rfl) ⟨990870, by rfl⟩ : syracuseStep 2642321 = 1981741) (by norm_num)
theorem B7046189 : Blo 2087435 7046189 := bstep (se 3 (by rfl) ⟨1321160, by rfl⟩ : syracuseStep 7046189 = 2642321) B2642321
theorem B4697459 : Blo 2087435 4697459 := bstep (se 1 (by rfl) ⟨3523094, by rfl⟩ : syracuseStep 4697459 = 7046189) B7046189
theorem B3131639 : Blo 2087435 3131639 := bstep (se 1 (by rfl) ⟨2348729, by rfl⟩ : syracuseStep 3131639 = 4697459) B4697459
theorem B2087759 : Blo 2087435 2087759 := bstep (se 1 (by rfl) ⟨1565819, by rfl⟩ : syracuseStep 2087759 = 3131639) B3131639
theorem B3131645 : Blo 2087435 3131645 := bbase (se 3 (by rfl) ⟨587183, by rfl⟩ : syracuseStep 3131645 = 1174367) (by norm_num)
theorem B2087763 : Blo 2087435 2087763 := bstep (se 1 (by rfl) ⟨1565822, by rfl⟩ : syracuseStep 2087763 = 3131645) B3131645
theorem B4697477 : Blo 2087435 4697477 := bbase (se 4 (by rfl) ⟨440388, by rfl⟩ : syracuseStep 4697477 = 880777) (by norm_num)
theorem B3131651 : Blo 2087435 3131651 := bstep (se 1 (by rfl) ⟨2348738, by rfl⟩ : syracuseStep 3131651 = 4697477) B4697477
theorem B2087767 : Blo 2087435 2087767 := bstep (se 1 (by rfl) ⟨1565825, by rfl⟩ : syracuseStep 2087767 = 3131651) B3131651
theorem B2972629 : Blo 2087435 2972629 := bbase (se 7 (by rfl) ⟨34835, by rfl⟩ : syracuseStep 2972629 = 69671) (by norm_num)
theorem B3963505 : Blo 2087435 3963505 := bstep (se 2 (by rfl) ⟨1486314, by rfl⟩ : syracuseStep 3963505 = 2972629) B2972629
theorem B5284673 : Blo 2087435 5284673 := bstep (se 2 (by rfl) ⟨1981752, by rfl⟩ : syracuseStep 5284673 = 3963505) B3963505
theorem B3523115 : Blo 2087435 3523115 := bstep (se 1 (by rfl) ⟨2642336, by rfl⟩ : syracuseStep 3523115 = 5284673) B5284673
theorem B2348743 : Blo 2087435 2348743 := bstep (se 1 (by rfl) ⟨1761557, by rfl⟩ : syracuseStep 2348743 = 3523115) B3523115
theorem B3131657 : Blo 2087435 3131657 := bstep (se 2 (by rfl) ⟨1174371, by rfl⟩ : syracuseStep 3131657 = 2348743) B2348743
theorem B2087771 : Blo 2087435 2087771 := bstep (se 1 (by rfl) ⟨1565828, by rfl⟩ : syracuseStep 2087771 = 3131657) B3131657
theorem B10569365 : Blo 2087435 10569365 := bbase (se 6 (by rfl) ⟨247719, by rfl⟩ : syracuseStep 10569365 = 495439) (by norm_num)
theorem B7046243 : Blo 2087435 7046243 := bstep (se 1 (by rfl) ⟨5284682, by rfl⟩ : syracuseStep 7046243 = 10569365) B10569365
theorem B4697495 : Blo 2087435 4697495 := bstep (se 1 (by rfl) ⟨3523121, by rfl⟩ : syracuseStep 4697495 = 7046243) B7046243
theorem B3131663 : Blo 2087435 3131663 := bstep (se 1 (by rfl) ⟨2348747, by rfl⟩ : syracuseStep 3131663 = 4697495) B4697495
theorem B2087775 : Blo 2087435 2087775 := bstep (se 1 (by rfl) ⟨1565831, by rfl⟩ : syracuseStep 2087775 = 3131663) B3131663
theorem B3131669 : Blo 2087435 3131669 := bbase (se 6 (by rfl) ⟨73398, by rfl⟩ : syracuseStep 3131669 = 146797) (by norm_num)
theorem B2087779 : Blo 2087435 2087779 := bstep (se 1 (by rfl) ⟨1565834, by rfl⟩ : syracuseStep 2087779 = 3131669) B3131669
theorem B26753813 : Blo 2087435 26753813 := bbase (se 6 (by rfl) ⟨627042, by rfl⟩ : syracuseStep 26753813 = 1254085) (by norm_num)
theorem B17835875 : Blo 2087435 17835875 := bstep (se 1 (by rfl) ⟨13376906, by rfl⟩ : syracuseStep 17835875 = 26753813) B26753813
theorem B11890583 : Blo 2087435 11890583 := bstep (se 1 (by rfl) ⟨8917937, by rfl⟩ : syracuseStep 11890583 = 17835875) B17835875
theorem B7927055 : Blo 2087435 7927055 := bstep (se 1 (by rfl) ⟨5945291, by rfl⟩ : syracuseStep 7927055 = 11890583) B11890583
theorem B5284703 : Blo 2087435 5284703 := bstep (se 1 (by rfl) ⟨3963527, by rfl⟩ : syracuseStep 5284703 = 7927055) B7927055
theorem B3523135 : Blo 2087435 3523135 := bstep (se 1 (by rfl) ⟨2642351, by rfl⟩ : syracuseStep 3523135 = 5284703) B5284703
theorem B4697513 : Blo 2087435 4697513 := bstep (se 2 (by rfl) ⟨1761567, by rfl⟩ : syracuseStep 4697513 = 3523135) B3523135
theorem B3131675 : Blo 2087435 3131675 := bstep (se 1 (by rfl) ⟨2348756, by rfl⟩ : syracuseStep 3131675 = 4697513) B4697513
theorem B2087783 : Blo 2087435 2087783 := bstep (se 1 (by rfl) ⟨1565837, by rfl⟩ : syracuseStep 2087783 = 3131675) B3131675
theorem B2348761 : Blo 2087435 2348761 := bbase (se 2 (by rfl) ⟨880785, by rfl⟩ : syracuseStep 2348761 = 1761571) (by norm_num)
theorem B3131681 : Blo 2087435 3131681 := bstep (se 2 (by rfl) ⟨1174380, by rfl⟩ : syracuseStep 3131681 = 2348761) B2348761
theorem B2087787 : Blo 2087435 2087787 := bstep (se 1 (by rfl) ⟨1565840, by rfl⟩ : syracuseStep 2087787 = 3131681) B3131681
theorem B2229493 : Blo 2087435 2229493 := bbase (se 5 (by rfl) ⟨104507, by rfl⟩ : syracuseStep 2229493 = 209015) (by norm_num)
theorem B2972657 : Blo 2087435 2972657 := bstep (se 2 (by rfl) ⟨1114746, by rfl⟩ : syracuseStep 2972657 = 2229493) B2229493
theorem B7927085 : Blo 2087435 7927085 := bstep (se 3 (by rfl) ⟨1486328, by rfl⟩ : syracuseStep 7927085 = 2972657) B2972657
theorem B5284723 : Blo 2087435 5284723 := bstep (se 1 (by rfl) ⟨3963542, by rfl⟩ : syracuseStep 5284723 = 7927085) B7927085
theorem B7046297 : Blo 2087435 7046297 := bstep (se 2 (by rfl) ⟨2642361, by rfl⟩ : syracuseStep 7046297 = 5284723) B5284723
theorem B4697531 : Blo 2087435 4697531 := bstep (se 1 (by rfl) ⟨3523148, by rfl⟩ : syracuseStep 4697531 = 7046297) B7046297
theorem B3131687 : Blo 2087435 3131687 := bstep (se 1 (by rfl) ⟨2348765, by rfl⟩ : syracuseStep 3131687 = 4697531) B4697531
theorem B2087791 : Blo 2087435 2087791 := bstep (se 1 (by rfl) ⟨1565843, by rfl⟩ : syracuseStep 2087791 = 3131687) B3131687
theorem B3131693 : Blo 2087435 3131693 := bbase (se 3 (by rfl) ⟨587192, by rfl⟩ : syracuseStep 3131693 = 1174385) (by norm_num)
theorem B2087795 : Blo 2087435 2087795 := bstep (se 1 (by rfl) ⟨1565846, by rfl⟩ : syracuseStep 2087795 = 3131693) B3131693
theorem B4697549 : Blo 2087435 4697549 := bbase (se 3 (by rfl) ⟨880790, by rfl⟩ : syracuseStep 4697549 = 1761581) (by norm_num)
theorem B3131699 : Blo 2087435 3131699 := bstep (se 1 (by rfl) ⟨2348774, by rfl⟩ : syracuseStep 3131699 = 4697549) B4697549
theorem B2087799 : Blo 2087435 2087799 := bstep (se 1 (by rfl) ⟨1565849, by rfl⟩ : syracuseStep 2087799 = 3131699) B3131699
theorem B2642377 : Blo 2087435 2642377 := bbase (se 2 (by rfl) ⟨990891, by rfl⟩ : syracuseStep 2642377 = 1981783) (by norm_num)
theorem B3523169 : Blo 2087435 3523169 := bstep (se 2 (by rfl) ⟨1321188, by rfl⟩ : syracuseStep 3523169 = 2642377) B2642377
theorem B2348779 : Blo 2087435 2348779 := bstep (se 1 (by rfl) ⟨1761584, by rfl⟩ : syracuseStep 2348779 = 3523169) B3523169
theorem B3131705 : Blo 2087435 3131705 := bstep (se 2 (by rfl) ⟨1174389, by rfl⟩ : syracuseStep 3131705 = 2348779) B2348779
theorem B2087803 : Blo 2087435 2087803 := bstep (se 1 (by rfl) ⟨1565852, by rfl⟩ : syracuseStep 2087803 = 3131705) B3131705
theorem B20065589 : Blo 2087435 20065589 := bbase (se 5 (by rfl) ⟨940574, by rfl⟩ : syracuseStep 20065589 = 1881149) (by norm_num)
theorem B13377059 : Blo 2087435 13377059 := bstep (se 1 (by rfl) ⟨10032794, by rfl⟩ : syracuseStep 13377059 = 20065589) B20065589
theorem B8918039 : Blo 2087435 8918039 := bstep (se 1 (by rfl) ⟨6688529, by rfl⟩ : syracuseStep 8918039 = 13377059) B13377059
theorem B23781437 : Blo 2087435 23781437 := bstep (se 3 (by rfl) ⟨4459019, by rfl⟩ : syracuseStep 23781437 = 8918039) B8918039
theorem B15854291 : Blo 2087435 15854291 := bstep (se 1 (by rfl) ⟨11890718, by rfl⟩ : syracuseStep 15854291 = 23781437) B23781437
theorem B10569527 : Blo 2087435 10569527 := bstep (se 1 (by rfl) ⟨7927145, by rfl⟩ : syracuseStep 10569527 = 15854291) B15854291
theorem B7046351 : Blo 2087435 7046351 := bstep (se 1 (by rfl) ⟨5284763, by rfl⟩ : syracuseStep 7046351 = 10569527) B10569527
theorem B4697567 : Blo 2087435 4697567 := bstep (se 1 (by rfl) ⟨3523175, by rfl⟩ : syracuseStep 4697567 = 7046351) B7046351
theorem B3131711 : Blo 2087435 3131711 := bstep (se 1 (by rfl) ⟨2348783, by rfl⟩ : syracuseStep 3131711 = 4697567) B4697567
theorem B2087807 : Blo 2087435 2087807 := bstep (se 1 (by rfl) ⟨1565855, by rfl⟩ : syracuseStep 2087807 = 3131711) B3131711
theorem B3131717 : Blo 2087435 3131717 := bbase (se 4 (by rfl) ⟨293598, by rfl⟩ : syracuseStep 3131717 = 587197) (by norm_num)
theorem B2087811 : Blo 2087435 2087811 := bstep (se 1 (by rfl) ⟨1565858, by rfl⟩ : syracuseStep 2087811 = 3131717) B3131717
theorem B3523189 : Blo 2087435 3523189 := bbase (se 5 (by rfl) ⟨165149, by rfl⟩ : syracuseStep 3523189 = 330299) (by norm_num)
theorem B4697585 : Blo 2087435 4697585 := bstep (se 2 (by rfl) ⟨1761594, by rfl⟩ : syracuseStep 4697585 = 3523189) B3523189
theorem B3131723 : Blo 2087435 3131723 := bstep (se 1 (by rfl) ⟨2348792, by rfl⟩ : syracuseStep 3131723 = 4697585) B4697585
theorem B2087815 : Blo 2087435 2087815 := bstep (se 1 (by rfl) ⟨1565861, by rfl⟩ : syracuseStep 2087815 = 3131723) B3131723
theorem B2348797 : Blo 2087435 2348797 := bbase (se 3 (by rfl) ⟨440399, by rfl⟩ : syracuseStep 2348797 = 880799) (by norm_num)
theorem B3131729 : Blo 2087435 3131729 := bstep (se 2 (by rfl) ⟨1174398, by rfl⟩ : syracuseStep 3131729 = 2348797) B2348797
theorem B2087819 : Blo 2087435 2087819 := bstep (se 1 (by rfl) ⟨1565864, by rfl⟩ : syracuseStep 2087819 = 3131729) B3131729
theorem B7046405 : Blo 2087435 7046405 := bbase (se 4 (by rfl) ⟨660600, by rfl⟩ : syracuseStep 7046405 = 1321201) (by norm_num)
theorem B4697603 : Blo 2087435 4697603 := bstep (se 1 (by rfl) ⟨3523202, by rfl⟩ : syracuseStep 4697603 = 7046405) B7046405
theorem B3131735 : Blo 2087435 3131735 := bstep (se 1 (by rfl) ⟨2348801, by rfl⟩ : syracuseStep 3131735 = 4697603) B4697603
theorem B2087823 : Blo 2087435 2087823 := bstep (se 1 (by rfl) ⟨1565867, by rfl⟩ : syracuseStep 2087823 = 3131735) B3131735
theorem B3131741 : Blo 2087435 3131741 := bbase (se 3 (by rfl) ⟨587201, by rfl⟩ : syracuseStep 3131741 = 1174403) (by norm_num)
theorem B2087827 : Blo 2087435 2087827 := bstep (se 1 (by rfl) ⟨1565870, by rfl⟩ : syracuseStep 2087827 = 3131741) B3131741
theorem B4697621 : Blo 2087435 4697621 := bbase (se 6 (by rfl) ⟨110100, by rfl⟩ : syracuseStep 4697621 = 220201) (by norm_num)
theorem B3131747 : Blo 2087435 3131747 := bstep (se 1 (by rfl) ⟨2348810, by rfl⟩ : syracuseStep 3131747 = 4697621) B4697621
theorem B2087831 : Blo 2087435 2087831 := bstep (se 1 (by rfl) ⟨1565873, by rfl⟩ : syracuseStep 2087831 = 3131747) B3131747
theorem B7927253 : Blo 2087435 7927253 := bbase (se 7 (by rfl) ⟨92897, by rfl⟩ : syracuseStep 7927253 = 185795) (by norm_num)
theorem B5284835 : Blo 2087435 5284835 := bstep (se 1 (by rfl) ⟨3963626, by rfl⟩ : syracuseStep 5284835 = 7927253) B7927253
theorem B3523223 : Blo 2087435 3523223 := bstep (se 1 (by rfl) ⟨2642417, by rfl⟩ : syracuseStep 3523223 = 5284835) B5284835
theorem B2348815 : Blo 2087435 2348815 := bstep (se 1 (by rfl) ⟨1761611, by rfl⟩ : syracuseStep 2348815 = 3523223) B3523223
theorem B3131753 : Blo 2087435 3131753 := bstep (se 2 (by rfl) ⟨1174407, by rfl⟩ : syracuseStep 3131753 = 2348815) B2348815
theorem B2087835 : Blo 2087435 2087835 := bstep (se 1 (by rfl) ⟨1565876, by rfl⟩ : syracuseStep 2087835 = 3131753) B3131753
theorem B11890901 : Blo 2087435 11890901 := bbase (se 7 (by rfl) ⟨139346, by rfl⟩ : syracuseStep 11890901 = 278693) (by norm_num)
theorem B7927267 : Blo 2087435 7927267 := bstep (se 1 (by rfl) ⟨5945450, by rfl⟩ : syracuseStep 7927267 = 11890901) B11890901
theorem B10569689 : Blo 2087435 10569689 := bstep (se 2 (by rfl) ⟨3963633, by rfl⟩ : syracuseStep 10569689 = 7927267) B7927267
theorem B7046459 : Blo 2087435 7046459 := bstep (se 1 (by rfl) ⟨5284844, by rfl⟩ : syracuseStep 7046459 = 10569689) B10569689
theorem B4697639 : Blo 2087435 4697639 := bstep (se 1 (by rfl) ⟨3523229, by rfl⟩ : syracuseStep 4697639 = 7046459) B7046459
theorem B3131759 : Blo 2087435 3131759 := bstep (se 1 (by rfl) ⟨2348819, by rfl⟩ : syracuseStep 3131759 = 4697639) B4697639
theorem B2087839 : Blo 2087435 2087839 := bstep (se 1 (by rfl) ⟨1565879, by rfl⟩ : syracuseStep 2087839 = 3131759) B3131759
theorem B3131765 : Blo 2087435 3131765 := bbase (se 5 (by rfl) ⟨146801, by rfl⟩ : syracuseStep 3131765 = 293603) (by norm_num)
theorem B2087843 : Blo 2087435 2087843 := bstep (se 1 (by rfl) ⟨1565882, by rfl⟩ : syracuseStep 2087843 = 3131765) B3131765
theorem B2229553 : Blo 2087435 2229553 := bbase (se 2 (by rfl) ⟨836082, by rfl⟩ : syracuseStep 2229553 = 1672165) (by norm_num)
theorem B2972737 : Blo 2087435 2972737 := bstep (se 2 (by rfl) ⟨1114776, by rfl⟩ : syracuseStep 2972737 = 2229553) B2229553
theorem B3963649 : Blo 2087435 3963649 := bstep (se 2 (by rfl) ⟨1486368, by rfl⟩ : syracuseStep 3963649 = 2972737) B2972737
theorem B5284865 : Blo 2087435 5284865 := bstep (se 2 (by rfl) ⟨1981824, by rfl⟩ : syracuseStep 5284865 = 3963649) B3963649
theorem B3523243 : Blo 2087435 3523243 := bstep (se 1 (by rfl) ⟨2642432, by rfl⟩ : syracuseStep 3523243 = 5284865) B5284865
theorem B4697657 : Blo 2087435 4697657 := bstep (se 2 (by rfl) ⟨1761621, by rfl⟩ : syracuseStep 4697657 = 3523243) B3523243
theorem B3131771 : Blo 2087435 3131771 := bstep (se 1 (by rfl) ⟨2348828, by rfl⟩ : syracuseStep 3131771 = 4697657) B4697657
theorem B2087847 : Blo 2087435 2087847 := bstep (se 1 (by rfl) ⟨1565885, by rfl⟩ : syracuseStep 2087847 = 3131771) B3131771
theorem B2348833 : Blo 2087435 2348833 := bbase (se 2 (by rfl) ⟨880812, by rfl⟩ : syracuseStep 2348833 = 1761625) (by norm_num)
theorem B3131777 : Blo 2087435 3131777 := bstep (se 2 (by rfl) ⟨1174416, by rfl⟩ : syracuseStep 3131777 = 2348833) B2348833
theorem B2087851 : Blo 2087435 2087851 := bstep (se 1 (by rfl) ⟨1565888, by rfl⟩ : syracuseStep 2087851 = 3131777) B3131777
theorem B5284885 : Blo 2087435 5284885 := bbase (se 6 (by rfl) ⟨123864, by rfl⟩ : syracuseStep 5284885 = 247729) (by norm_num)
theorem B7046513 : Blo 2087435 7046513 := bstep (se 2 (by rfl) ⟨2642442, by rfl⟩ : syracuseStep 7046513 = 5284885) B5284885
theorem B4697675 : Blo 2087435 4697675 := bstep (se 1 (by rfl) ⟨3523256, by rfl⟩ : syracuseStep 4697675 = 7046513) B7046513
theorem B3131783 : Blo 2087435 3131783 := bstep (se 1 (by rfl) ⟨2348837, by rfl⟩ : syracuseStep 3131783 = 4697675) B4697675
theorem B2087855 : Blo 2087435 2087855 := bstep (se 1 (by rfl) ⟨1565891, by rfl⟩ : syracuseStep 2087855 = 3131783) B3131783
theorem B3131789 : Blo 2087435 3131789 := bbase (se 3 (by rfl) ⟨587210, by rfl⟩ : syracuseStep 3131789 = 1174421) (by norm_num)
theorem B2087859 : Blo 2087435 2087859 := bstep (se 1 (by rfl) ⟨1565894, by rfl⟩ : syracuseStep 2087859 = 3131789) B3131789
theorem B4697693 : Blo 2087435 4697693 := bbase (se 3 (by rfl) ⟨880817, by rfl⟩ : syracuseStep 4697693 = 1761635) (by norm_num)
theorem B3131795 : Blo 2087435 3131795 := bstep (se 1 (by rfl) ⟨2348846, by rfl⟩ : syracuseStep 3131795 = 4697693) B4697693
theorem B2087863 : Blo 2087435 2087863 := bstep (se 1 (by rfl) ⟨1565897, by rfl⟩ : syracuseStep 2087863 = 3131795) B3131795
theorem B3523277 : Blo 2087435 3523277 := bbase (se 3 (by rfl) ⟨660614, by rfl⟩ : syracuseStep 3523277 = 1321229) (by norm_num)
theorem B2348851 : Blo 2087435 2348851 := bstep (se 1 (by rfl) ⟨1761638, by rfl⟩ : syracuseStep 2348851 = 3523277) B3523277
theorem B3131801 : Blo 2087435 3131801 := bstep (se 2 (by rfl) ⟨1174425, by rfl⟩ : syracuseStep 3131801 = 2348851) B2348851
theorem B2087867 : Blo 2087435 2087867 := bstep (se 1 (by rfl) ⟨1565900, by rfl⟩ : syracuseStep 2087867 = 3131801) B3131801
theorem B19047221 : Blo 2087435 19047221 := bbase (se 5 (by rfl) ⟨892838, by rfl⟩ : syracuseStep 19047221 = 1785677) (by norm_num)
theorem B12698147 : Blo 2087435 12698147 := bstep (se 1 (by rfl) ⟨9523610, by rfl⟩ : syracuseStep 12698147 = 19047221) B19047221
theorem B8465431 : Blo 2087435 8465431 := bstep (se 1 (by rfl) ⟨6349073, by rfl⟩ : syracuseStep 8465431 = 12698147) B12698147
theorem B11287241 : Blo 2087435 11287241 := bstep (se 2 (by rfl) ⟨4232715, by rfl⟩ : syracuseStep 11287241 = 8465431) B8465431
theorem B7524827 : Blo 2087435 7524827 := bstep (se 1 (by rfl) ⟨5643620, by rfl⟩ : syracuseStep 7524827 = 11287241) B11287241
theorem B5016551 : Blo 2087435 5016551 := bstep (se 1 (by rfl) ⟨3762413, by rfl⟩ : syracuseStep 5016551 = 7524827) B7524827
theorem B13377469 : Blo 2087435 13377469 := bstep (se 3 (by rfl) ⟨2508275, by rfl⟩ : syracuseStep 13377469 = 5016551) B5016551
theorem B17836625 : Blo 2087435 17836625 := bstep (se 2 (by rfl) ⟨6688734, by rfl⟩ : syracuseStep 17836625 = 13377469) B13377469
theorem B11891083 : Blo 2087435 11891083 := bstep (se 1 (by rfl) ⟨8918312, by rfl⟩ : syracuseStep 11891083 = 17836625) B17836625
theorem B15854777 : Blo 2087435 15854777 := bstep (se 2 (by rfl) ⟨5945541, by rfl⟩ : syracuseStep 15854777 = 11891083) B11891083
theorem B10569851 : Blo 2087435 10569851 := bstep (se 1 (by rfl) ⟨7927388, by rfl⟩ : syracuseStep 10569851 = 15854777) B15854777
theorem B7046567 : Blo 2087435 7046567 := bstep (se 1 (by rfl) ⟨5284925, by rfl⟩ : syracuseStep 7046567 = 10569851) B10569851
theorem B4697711 : Blo 2087435 4697711 := bstep (se 1 (by rfl) ⟨3523283, by rfl⟩ : syracuseStep 4697711 = 7046567) B7046567
theorem B3131807 : Blo 2087435 3131807 := bstep (se 1 (by rfl) ⟨2348855, by rfl⟩ : syracuseStep 3131807 = 4697711) B4697711
theorem B2087871 : Blo 2087435 2087871 := bstep (se 1 (by rfl) ⟨1565903, by rfl⟩ : syracuseStep 2087871 = 3131807) B3131807
theorem B3131813 : Blo 2087435 3131813 := bbase (se 4 (by rfl) ⟨293607, by rfl⟩ : syracuseStep 3131813 = 587215) (by norm_num)
theorem B2087875 : Blo 2087435 2087875 := bstep (se 1 (by rfl) ⟨1565906, by rfl⟩ : syracuseStep 2087875 = 3131813) B3131813
theorem B2642473 : Blo 2087435 2642473 := bbase (se 2 (by rfl) ⟨990927, by rfl⟩ : syracuseStep 2642473 = 1981855) (by norm_num)
theorem B3523297 : Blo 2087435 3523297 := bstep (se 2 (by rfl) ⟨1321236, by rfl⟩ : syracuseStep 3523297 = 2642473) B2642473
theorem B4697729 : Blo 2087435 4697729 := bstep (se 2 (by rfl) ⟨1761648, by rfl⟩ : syracuseStep 4697729 = 3523297) B3523297
theorem B3131819 : Blo 2087435 3131819 := bstep (se 1 (by rfl) ⟨2348864, by rfl⟩ : syracuseStep 3131819 = 4697729) B4697729
theorem B2087879 : Blo 2087435 2087879 := bstep (se 1 (by rfl) ⟨1565909, by rfl⟩ : syracuseStep 2087879 = 3131819) B3131819
theorem B2348869 : Blo 2087435 2348869 := bbase (se 4 (by rfl) ⟨220206, by rfl⟩ : syracuseStep 2348869 = 440413) (by norm_num)
theorem B3131825 : Blo 2087435 3131825 := bstep (se 2 (by rfl) ⟨1174434, by rfl⟩ : syracuseStep 3131825 = 2348869) B2348869
theorem B2087883 : Blo 2087435 2087883 := bstep (se 1 (by rfl) ⟨1565912, by rfl⟩ : syracuseStep 2087883 = 3131825) B3131825
theorem B3963725 : Blo 2087435 3963725 := bbase (se 3 (by rfl) ⟨743198, by rfl⟩ : syracuseStep 3963725 = 1486397) (by norm_num)
theorem B2642483 : Blo 2087435 2642483 := bstep (se 1 (by rfl) ⟨1981862, by rfl⟩ : syracuseStep 2642483 = 3963725) B3963725
theorem B7046621 : Blo 2087435 7046621 := bstep (se 3 (by rfl) ⟨1321241, by rfl⟩ : syracuseStep 7046621 = 2642483) B2642483
theorem B4697747 : Blo 2087435 4697747 := bstep (se 1 (by rfl) ⟨3523310, by rfl⟩ : syracuseStep 4697747 = 7046621) B7046621
theorem B3131831 : Blo 2087435 3131831 := bstep (se 1 (by rfl) ⟨2348873, by rfl⟩ : syracuseStep 3131831 = 4697747) B4697747
theorem B2087887 : Blo 2087435 2087887 := bstep (se 1 (by rfl) ⟨1565915, by rfl⟩ : syracuseStep 2087887 = 3131831) B3131831
theorem B3131837 : Blo 2087435 3131837 := bbase (se 3 (by rfl) ⟨587219, by rfl⟩ : syracuseStep 3131837 = 1174439) (by norm_num)
theorem B2087891 : Blo 2087435 2087891 := bstep (se 1 (by rfl) ⟨1565918, by rfl⟩ : syracuseStep 2087891 = 3131837) B3131837
theorem B4697765 : Blo 2087435 4697765 := bbase (se 4 (by rfl) ⟨440415, by rfl⟩ : syracuseStep 4697765 = 880831) (by norm_num)
theorem B3131843 : Blo 2087435 3131843 := bstep (se 1 (by rfl) ⟨2348882, by rfl⟩ : syracuseStep 3131843 = 4697765) B4697765
theorem B2087895 : Blo 2087435 2087895 := bstep (se 1 (by rfl) ⟨1565921, by rfl⟩ : syracuseStep 2087895 = 3131843) B3131843
theorem B5284997 : Blo 2087435 5284997 := bbase (se 4 (by rfl) ⟨495468, by rfl⟩ : syracuseStep 5284997 = 990937) (by norm_num)
theorem B3523331 : Blo 2087435 3523331 := bstep (se 1 (by rfl) ⟨2642498, by rfl⟩ : syracuseStep 3523331 = 5284997) B5284997
theorem B2348887 : Blo 2087435 2348887 := bstep (se 1 (by rfl) ⟨1761665, by rfl⟩ : syracuseStep 2348887 = 3523331) B3523331
theorem B3131849 : Blo 2087435 3131849 := bstep (se 2 (by rfl) ⟨1174443, by rfl⟩ : syracuseStep 3131849 = 2348887) B2348887
theorem B2087899 : Blo 2087435 2087899 := bstep (se 1 (by rfl) ⟨1565924, by rfl⟩ : syracuseStep 2087899 = 3131849) B3131849
theorem B5016629 : Blo 2087435 5016629 := bbase (se 5 (by rfl) ⟨235154, by rfl⟩ : syracuseStep 5016629 = 470309) (by norm_num)
theorem B3344419 : Blo 2087435 3344419 := bstep (se 1 (by rfl) ⟨2508314, by rfl⟩ : syracuseStep 3344419 = 5016629) B5016629
theorem B4459225 : Blo 2087435 4459225 := bstep (se 2 (by rfl) ⟨1672209, by rfl⟩ : syracuseStep 4459225 = 3344419) B3344419
theorem B5945633 : Blo 2087435 5945633 := bstep (se 2 (by rfl) ⟨2229612, by rfl⟩ : syracuseStep 5945633 = 4459225) B4459225
theorem B3963755 : Blo 2087435 3963755 := bstep (se 1 (by rfl) ⟨2972816, by rfl⟩ : syracuseStep 3963755 = 5945633) B5945633
theorem B10570013 : Blo 2087435 10570013 := bstep (se 3 (by rfl) ⟨1981877, by rfl⟩ : syracuseStep 10570013 = 3963755) B3963755
theorem B7046675 : Blo 2087435 7046675 := bstep (se 1 (by rfl) ⟨5285006, by rfl⟩ : syracuseStep 7046675 = 10570013) B10570013
theorem B4697783 : Blo 2087435 4697783 := bstep (se 1 (by rfl) ⟨3523337, by rfl⟩ : syracuseStep 4697783 = 7046675) B7046675
theorem B3131855 : Blo 2087435 3131855 := bstep (se 1 (by rfl) ⟨2348891, by rfl⟩ : syracuseStep 3131855 = 4697783) B4697783
theorem B2087903 : Blo 2087435 2087903 := bstep (se 1 (by rfl) ⟨1565927, by rfl⟩ : syracuseStep 2087903 = 3131855) B3131855
theorem B3131861 : Blo 2087435 3131861 := bbase (se 7 (by rfl) ⟨36701, by rfl⟩ : syracuseStep 3131861 = 73403) (by norm_num)
theorem B2087907 : Blo 2087435 2087907 := bstep (se 1 (by rfl) ⟨1565930, by rfl⟩ : syracuseStep 2087907 = 3131861) B3131861
theorem B7927541 : Blo 2087435 7927541 := bbase (se 5 (by rfl) ⟨371603, by rfl⟩ : syracuseStep 7927541 = 743207) (by norm_num)
theorem B5285027 : Blo 2087435 5285027 := bstep (se 1 (by rfl) ⟨3963770, by rfl⟩ : syracuseStep 5285027 = 7927541) B7927541
theorem B3523351 : Blo 2087435 3523351 := bstep (se 1 (by rfl) ⟨2642513, by rfl⟩ : syracuseStep 3523351 = 5285027) B5285027
theorem B4697801 : Blo 2087435 4697801 := bstep (se 2 (by rfl) ⟨1761675, by rfl⟩ : syracuseStep 4697801 = 3523351) B3523351
theorem B3131867 : Blo 2087435 3131867 := bstep (se 1 (by rfl) ⟨2348900, by rfl⟩ : syracuseStep 3131867 = 4697801) B4697801
theorem B2087911 : Blo 2087435 2087911 := bstep (se 1 (by rfl) ⟨1565933, by rfl⟩ : syracuseStep 2087911 = 3131867) B3131867
theorem B2348905 : Blo 2087435 2348905 := bbase (se 2 (by rfl) ⟨880839, by rfl⟩ : syracuseStep 2348905 = 1761679) (by norm_num)
theorem B3131873 : Blo 2087435 3131873 := bstep (se 2 (by rfl) ⟨1174452, by rfl⟩ : syracuseStep 3131873 = 2348905) B2348905
theorem B2087915 : Blo 2087435 2087915 := bstep (se 1 (by rfl) ⟨1565936, by rfl⟩ : syracuseStep 2087915 = 3131873) B3131873
theorem B8035733 : Blo 2087435 8035733 := bbase (se 6 (by rfl) ⟨188337, by rfl⟩ : syracuseStep 8035733 = 376675) (by norm_num)
theorem B21428621 : Blo 2087435 21428621 := bstep (se 3 (by rfl) ⟨4017866, by rfl⟩ : syracuseStep 21428621 = 8035733) B8035733
theorem B14285747 : Blo 2087435 14285747 := bstep (se 1 (by rfl) ⟨10714310, by rfl⟩ : syracuseStep 14285747 = 21428621) B21428621
theorem B9523831 : Blo 2087435 9523831 := bstep (se 1 (by rfl) ⟨7142873, by rfl⟩ : syracuseStep 9523831 = 14285747) B14285747
theorem B12698441 : Blo 2087435 12698441 := bstep (se 2 (by rfl) ⟨4761915, by rfl⟩ : syracuseStep 12698441 = 9523831) B9523831
theorem B8465627 : Blo 2087435 8465627 := bstep (se 1 (by rfl) ⟨6349220, by rfl⟩ : syracuseStep 8465627 = 12698441) B12698441
theorem B5643751 : Blo 2087435 5643751 := bstep (se 1 (by rfl) ⟨4232813, by rfl⟩ : syracuseStep 5643751 = 8465627) B8465627
theorem B7525001 : Blo 2087435 7525001 := bstep (se 2 (by rfl) ⟨2821875, by rfl⟩ : syracuseStep 7525001 = 5643751) B5643751
theorem B5016667 : Blo 2087435 5016667 := bstep (se 1 (by rfl) ⟨3762500, by rfl⟩ : syracuseStep 5016667 = 7525001) B7525001
theorem B6688889 : Blo 2087435 6688889 := bstep (se 2 (by rfl) ⟨2508333, by rfl⟩ : syracuseStep 6688889 = 5016667) B5016667
theorem B4459259 : Blo 2087435 4459259 := bstep (se 1 (by rfl) ⟨3344444, by rfl⟩ : syracuseStep 4459259 = 6688889) B6688889
theorem B11891357 : Blo 2087435 11891357 := bstep (se 3 (by rfl) ⟨2229629, by rfl⟩ : syracuseStep 11891357 = 4459259) B4459259
theorem B7927571 : Blo 2087435 7927571 := bstep (se 1 (by rfl) ⟨5945678, by rfl⟩ : syracuseStep 7927571 = 11891357) B11891357
theorem B5285047 : Blo 2087435 5285047 := bstep (se 1 (by rfl) ⟨3963785, by rfl⟩ : syracuseStep 5285047 = 7927571) B7927571
theorem B7046729 : Blo 2087435 7046729 := bstep (se 2 (by rfl) ⟨2642523, by rfl⟩ : syracuseStep 7046729 = 5285047) B5285047
theorem B4697819 : Blo 2087435 4697819 := bstep (se 1 (by rfl) ⟨3523364, by rfl⟩ : syracuseStep 4697819 = 7046729) B7046729
theorem B3131879 : Blo 2087435 3131879 := bstep (se 1 (by rfl) ⟨2348909, by rfl⟩ : syracuseStep 3131879 = 4697819) B4697819
theorem B2087919 : Blo 2087435 2087919 := bstep (se 1 (by rfl) ⟨1565939, by rfl⟩ : syracuseStep 2087919 = 3131879) B3131879
theorem B3131885 : Blo 2087435 3131885 := bbase (se 3 (by rfl) ⟨587228, by rfl⟩ : syracuseStep 3131885 = 1174457) (by norm_num)
theorem B2087923 : Blo 2087435 2087923 := bstep (se 1 (by rfl) ⟨1565942, by rfl⟩ : syracuseStep 2087923 = 3131885) B3131885
theorem B4697837 : Blo 2087435 4697837 := bbase (se 3 (by rfl) ⟨880844, by rfl⟩ : syracuseStep 4697837 = 1761689) (by norm_num)
theorem B3131891 : Blo 2087435 3131891 := bstep (se 1 (by rfl) ⟨2348918, by rfl⟩ : syracuseStep 3131891 = 4697837) B4697837
theorem B2087927 : Blo 2087435 2087927 := bstep (se 1 (by rfl) ⟨1565945, by rfl⟩ : syracuseStep 2087927 = 3131891) B3131891
theorem B2508349 : Blo 2087435 2508349 := bbase (se 3 (by rfl) ⟨470315, by rfl⟩ : syracuseStep 2508349 = 940631) (by norm_num)
theorem B3344465 : Blo 2087435 3344465 := bstep (se 2 (by rfl) ⟨1254174, by rfl⟩ : syracuseStep 3344465 = 2508349) B2508349
theorem B2229643 : Blo 2087435 2229643 := bstep (se 1 (by rfl) ⟨1672232, by rfl⟩ : syracuseStep 2229643 = 3344465) B3344465
theorem B2972857 : Blo 2087435 2972857 := bstep (se 2 (by rfl) ⟨1114821, by rfl⟩ : syracuseStep 2972857 = 2229643) B2229643
theorem B3963809 : Blo 2087435 3963809 := bstep (se 2 (by rfl) ⟨1486428, by rfl⟩ : syracuseStep 3963809 = 2972857) B2972857
theorem B2642539 : Blo 2087435 2642539 := bstep (se 1 (by rfl) ⟨1981904, by rfl⟩ : syracuseStep 2642539 = 3963809) B3963809
theorem B3523385 : Blo 2087435 3523385 := bstep (se 2 (by rfl) ⟨1321269, by rfl⟩ : syracuseStep 3523385 = 2642539) B2642539
theorem B2348923 : Blo 2087435 2348923 := bstep (se 1 (by rfl) ⟨1761692, by rfl⟩ : syracuseStep 2348923 = 3523385) B3523385
theorem B3131897 : Blo 2087435 3131897 := bstep (se 2 (by rfl) ⟨1174461, by rfl⟩ : syracuseStep 3131897 = 2348923) B2348923
theorem B2087931 : Blo 2087435 2087931 := bstep (se 1 (by rfl) ⟨1565948, by rfl⟩ : syracuseStep 2087931 = 3131897) B3131897
theorem B2678597 : Blo 2087435 2678597 := bbase (se 4 (by rfl) ⟨251118, by rfl⟩ : syracuseStep 2678597 = 502237) (by norm_num)
theorem B28571701 : Blo 2087435 28571701 := bstep (se 5 (by rfl) ⟨1339298, by rfl⟩ : syracuseStep 28571701 = 2678597) B2678597
theorem B38095601 : Blo 2087435 38095601 := bstep (se 2 (by rfl) ⟨14285850, by rfl⟩ : syracuseStep 38095601 = 28571701) B28571701
theorem B101588269 : Blo 2087435 101588269 := bstep (se 3 (by rfl) ⟨19047800, by rfl⟩ : syracuseStep 101588269 = 38095601) B38095601
theorem B135451025 : Blo 2087435 135451025 := bstep (se 2 (by rfl) ⟨50794134, by rfl⟩ : syracuseStep 135451025 = 101588269) B101588269
theorem B90300683 : Blo 2087435 90300683 := bstep (se 1 (by rfl) ⟨67725512, by rfl⟩ : syracuseStep 90300683 = 135451025) B135451025
theorem B60200455 : Blo 2087435 60200455 := bstep (se 1 (by rfl) ⟨45150341, by rfl⟩ : syracuseStep 60200455 = 90300683) B90300683
theorem B80267273 : Blo 2087435 80267273 := bstep (se 2 (by rfl) ⟨30100227, by rfl⟩ : syracuseStep 80267273 = 60200455) B60200455
theorem B53511515 : Blo 2087435 53511515 := bstep (se 1 (by rfl) ⟨40133636, by rfl⟩ : syracuseStep 53511515 = 80267273) B80267273
theorem B35674343 : Blo 2087435 35674343 := bstep (se 1 (by rfl) ⟨26755757, by rfl⟩ : syracuseStep 35674343 = 53511515) B53511515
theorem B23782895 : Blo 2087435 23782895 := bstep (se 1 (by rfl) ⟨17837171, by rfl⟩ : syracuseStep 23782895 = 35674343) B35674343
theorem B15855263 : Blo 2087435 15855263 := bstep (se 1 (by rfl) ⟨11891447, by rfl⟩ : syracuseStep 15855263 = 23782895) B23782895
theorem B10570175 : Blo 2087435 10570175 := bstep (se 1 (by rfl) ⟨7927631, by rfl⟩ : syracuseStep 10570175 = 15855263) B15855263
theorem B7046783 : Blo 2087435 7046783 := bstep (se 1 (by rfl) ⟨5285087, by rfl⟩ : syracuseStep 7046783 = 10570175) B10570175
theorem B4697855 : Blo 2087435 4697855 := bstep (se 1 (by rfl) ⟨3523391, by rfl⟩ : syracuseStep 4697855 = 7046783) B7046783
theorem B3131903 : Blo 2087435 3131903 := bstep (se 1 (by rfl) ⟨2348927, by rfl⟩ : syracuseStep 3131903 = 4697855) B4697855
theorem B2087935 : Blo 2087435 2087935 := bstep (se 1 (by rfl) ⟨1565951, by rfl⟩ : syracuseStep 2087935 = 3131903) B3131903
theorem B3131909 : Blo 2087435 3131909 := bbase (se 4 (by rfl) ⟨293616, by rfl⟩ : syracuseStep 3131909 = 587233) (by norm_num)
theorem B2087939 : Blo 2087435 2087939 := bstep (se 1 (by rfl) ⟨1565954, by rfl⟩ : syracuseStep 2087939 = 3131909) B3131909
theorem B3523405 : Blo 2087435 3523405 := bbase (se 3 (by rfl) ⟨660638, by rfl⟩ : syracuseStep 3523405 = 1321277) (by norm_num)
theorem B4697873 : Blo 2087435 4697873 := bstep (se 2 (by rfl) ⟨1761702, by rfl⟩ : syracuseStep 4697873 = 3523405) B3523405
theorem B3131915 : Blo 2087435 3131915 := bstep (se 1 (by rfl) ⟨2348936, by rfl⟩ : syracuseStep 3131915 = 4697873) B4697873
theorem B2087943 : Blo 2087435 2087943 := bstep (se 1 (by rfl) ⟨1565957, by rfl⟩ : syracuseStep 2087943 = 3131915) B3131915
theorem B2348941 : Blo 2087435 2348941 := bbase (se 3 (by rfl) ⟨440426, by rfl⟩ : syracuseStep 2348941 = 880853) (by norm_num)
theorem B3131921 : Blo 2087435 3131921 := bstep (se 2 (by rfl) ⟨1174470, by rfl⟩ : syracuseStep 3131921 = 2348941) B2348941
theorem B2087947 : Blo 2087435 2087947 := bstep (se 1 (by rfl) ⟨1565960, by rfl⟩ : syracuseStep 2087947 = 3131921) B3131921
theorem B7046837 : Blo 2087435 7046837 := bbase (se 5 (by rfl) ⟨330320, by rfl⟩ : syracuseStep 7046837 = 660641) (by norm_num)
theorem B4697891 : Blo 2087435 4697891 := bstep (se 1 (by rfl) ⟨3523418, by rfl⟩ : syracuseStep 4697891 = 7046837) B7046837
theorem B3131927 : Blo 2087435 3131927 := bstep (se 1 (by rfl) ⟨2348945, by rfl⟩ : syracuseStep 3131927 = 4697891) B4697891
theorem B2087951 : Blo 2087435 2087951 := bstep (se 1 (by rfl) ⟨1565963, by rfl⟩ : syracuseStep 2087951 = 3131927) B3131927
theorem B3131933 : Blo 2087435 3131933 := bbase (se 3 (by rfl) ⟨587237, by rfl⟩ : syracuseStep 3131933 = 1174475) (by norm_num)
theorem B2087955 : Blo 2087435 2087955 := bstep (se 1 (by rfl) ⟨1565966, by rfl⟩ : syracuseStep 2087955 = 3131933) B3131933
theorem B4697909 : Blo 2087435 4697909 := bbase (se 5 (by rfl) ⟨220214, by rfl⟩ : syracuseStep 4697909 = 440429) (by norm_num)
theorem B3131939 : Blo 2087435 3131939 := bstep (se 1 (by rfl) ⟨2348954, by rfl⟩ : syracuseStep 3131939 = 4697909) B4697909
theorem B2087959 : Blo 2087435 2087959 := bstep (se 1 (by rfl) ⟨1565969, by rfl⟩ : syracuseStep 2087959 = 3131939) B3131939
theorem B5016773 : Blo 2087435 5016773 := bbase (se 4 (by rfl) ⟨470322, by rfl⟩ : syracuseStep 5016773 = 940645) (by norm_num)
theorem B13378061 : Blo 2087435 13378061 := bstep (se 3 (by rfl) ⟨2508386, by rfl⟩ : syracuseStep 13378061 = 5016773) B5016773
theorem B8918707 : Blo 2087435 8918707 := bstep (se 1 (by rfl) ⟨6689030, by rfl⟩ : syracuseStep 8918707 = 13378061) B13378061
theorem B11891609 : Blo 2087435 11891609 := bstep (se 2 (by rfl) ⟨4459353, by rfl⟩ : syracuseStep 11891609 = 8918707) B8918707
theorem B7927739 : Blo 2087435 7927739 := bstep (se 1 (by rfl) ⟨5945804, by rfl⟩ : syracuseStep 7927739 = 11891609) B11891609
theorem B5285159 : Blo 2087435 5285159 := bstep (se 1 (by rfl) ⟨3963869, by rfl⟩ : syracuseStep 5285159 = 7927739) B7927739
theorem B3523439 : Blo 2087435 3523439 := bstep (se 1 (by rfl) ⟨2642579, by rfl⟩ : syracuseStep 3523439 = 5285159) B5285159
theorem B2348959 : Blo 2087435 2348959 := bstep (se 1 (by rfl) ⟨1761719, by rfl⟩ : syracuseStep 2348959 = 3523439) B3523439
theorem B3131945 : Blo 2087435 3131945 := bstep (se 2 (by rfl) ⟨1174479, by rfl⟩ : syracuseStep 3131945 = 2348959) B2348959
theorem B2087963 : Blo 2087435 2087963 := bstep (se 1 (by rfl) ⟨1565972, by rfl⟩ : syracuseStep 2087963 = 3131945) B3131945
theorem B5720885 : Blo 2087435 5720885 := bbase (se 5 (by rfl) ⟨268166, by rfl⟩ : syracuseStep 5720885 = 536333) (by norm_num)
theorem B3813923 : Blo 2087435 3813923 := bstep (se 1 (by rfl) ⟨2860442, by rfl⟩ : syracuseStep 3813923 = 5720885) B5720885
theorem B10170461 : Blo 2087435 10170461 := bstep (se 3 (by rfl) ⟨1906961, by rfl⟩ : syracuseStep 10170461 = 3813923) B3813923
theorem B27121229 : Blo 2087435 27121229 := bstep (se 3 (by rfl) ⟨5085230, by rfl⟩ : syracuseStep 27121229 = 10170461) B10170461
theorem B18080819 : Blo 2087435 18080819 := bstep (se 1 (by rfl) ⟨13560614, by rfl⟩ : syracuseStep 18080819 = 27121229) B27121229
theorem B12053879 : Blo 2087435 12053879 := bstep (se 1 (by rfl) ⟨9040409, by rfl⟩ : syracuseStep 12053879 = 18080819) B18080819
theorem B8035919 : Blo 2087435 8035919 := bstep (se 1 (by rfl) ⟨6026939, by rfl⟩ : syracuseStep 8035919 = 12053879) B12053879
theorem B5357279 : Blo 2087435 5357279 := bstep (se 1 (by rfl) ⟨4017959, by rfl⟩ : syracuseStep 5357279 = 8035919) B8035919
theorem B14286077 : Blo 2087435 14286077 := bstep (se 3 (by rfl) ⟨2678639, by rfl⟩ : syracuseStep 14286077 = 5357279) B5357279
theorem B9524051 : Blo 2087435 9524051 := bstep (se 1 (by rfl) ⟨7143038, by rfl⟩ : syracuseStep 9524051 = 14286077) B14286077
theorem B6349367 : Blo 2087435 6349367 := bstep (se 1 (by rfl) ⟨4762025, by rfl⟩ : syracuseStep 6349367 = 9524051) B9524051
theorem B4232911 : Blo 2087435 4232911 := bstep (se 1 (by rfl) ⟨3174683, by rfl⟩ : syracuseStep 4232911 = 6349367) B6349367
theorem B5643881 : Blo 2087435 5643881 := bstep (se 2 (by rfl) ⟨2116455, by rfl⟩ : syracuseStep 5643881 = 4232911) B4232911
theorem B3762587 : Blo 2087435 3762587 := bstep (se 1 (by rfl) ⟨2821940, by rfl⟩ : syracuseStep 3762587 = 5643881) B5643881
theorem B2508391 : Blo 2087435 2508391 := bstep (se 1 (by rfl) ⟨1881293, by rfl⟩ : syracuseStep 2508391 = 3762587) B3762587
theorem B13378085 : Blo 2087435 13378085 := bstep (se 4 (by rfl) ⟨1254195, by rfl⟩ : syracuseStep 13378085 = 2508391) B2508391
theorem B8918723 : Blo 2087435 8918723 := bstep (se 1 (by rfl) ⟨6689042, by rfl⟩ : syracuseStep 8918723 = 13378085) B13378085
theorem B5945815 : Blo 2087435 5945815 := bstep (se 1 (by rfl) ⟨4459361, by rfl⟩ : syracuseStep 5945815 = 8918723) B8918723
theorem B7927753 : Blo 2087435 7927753 := bstep (se 2 (by rfl) ⟨2972907, by rfl⟩ : syracuseStep 7927753 = 5945815) B5945815
theorem B10570337 : Blo 2087435 10570337 := bstep (se 2 (by rfl) ⟨3963876, by rfl⟩ : syracuseStep 10570337 = 7927753) B7927753
theorem B7046891 : Blo 2087435 7046891 := bstep (se 1 (by rfl) ⟨5285168, by rfl⟩ : syracuseStep 7046891 = 10570337) B10570337
theorem B4697927 : Blo 2087435 4697927 := bstep (se 1 (by rfl) ⟨3523445, by rfl⟩ : syracuseStep 4697927 = 7046891) B7046891
theorem B3131951 : Blo 2087435 3131951 := bstep (se 1 (by rfl) ⟨2348963, by rfl⟩ : syracuseStep 3131951 = 4697927) B4697927
theorem B2087967 : Blo 2087435 2087967 := bstep (se 1 (by rfl) ⟨1565975, by rfl⟩ : syracuseStep 2087967 = 3131951) B3131951
theorem B3131957 : Blo 2087435 3131957 := bbase (se 5 (by rfl) ⟨146810, by rfl⟩ : syracuseStep 3131957 = 293621) (by norm_num)
theorem B2087971 : Blo 2087435 2087971 := bstep (se 1 (by rfl) ⟨1565978, by rfl⟩ : syracuseStep 2087971 = 3131957) B3131957
theorem B5285189 : Blo 2087435 5285189 := bbase (se 4 (by rfl) ⟨495486, by rfl⟩ : syracuseStep 5285189 = 990973) (by norm_num)
theorem B3523459 : Blo 2087435 3523459 := bstep (se 1 (by rfl) ⟨2642594, by rfl⟩ : syracuseStep 3523459 = 5285189) B5285189
theorem B4697945 : Blo 2087435 4697945 := bstep (se 2 (by rfl) ⟨1761729, by rfl⟩ : syracuseStep 4697945 = 3523459) B3523459
theorem B3131963 : Blo 2087435 3131963 := bstep (se 1 (by rfl) ⟨2348972, by rfl⟩ : syracuseStep 3131963 = 4697945) B4697945
theorem B2087975 : Blo 2087435 2087975 := bstep (se 1 (by rfl) ⟨1565981, by rfl⟩ : syracuseStep 2087975 = 3131963) B3131963
theorem B2348977 : Blo 2087435 2348977 := bbase (se 2 (by rfl) ⟨880866, by rfl⟩ : syracuseStep 2348977 = 1761733) (by norm_num)
theorem B3131969 : Blo 2087435 3131969 := bstep (se 2 (by rfl) ⟨1174488, by rfl⟩ : syracuseStep 3131969 = 2348977) B2348977
theorem B2087979 : Blo 2087435 2087979 := bstep (se 1 (by rfl) ⟨1565984, by rfl⟩ : syracuseStep 2087979 = 3131969) B3131969
theorem B5945861 : Blo 2087435 5945861 := bbase (se 4 (by rfl) ⟨557424, by rfl⟩ : syracuseStep 5945861 = 1114849) (by norm_num)
theorem B3963907 : Blo 2087435 3963907 := bstep (se 1 (by rfl) ⟨2972930, by rfl⟩ : syracuseStep 3963907 = 5945861) B5945861
theorem B5285209 : Blo 2087435 5285209 := bstep (se 2 (by rfl) ⟨1981953, by rfl⟩ : syracuseStep 5285209 = 3963907) B3963907
theorem B7046945 : Blo 2087435 7046945 := bstep (se 2 (by rfl) ⟨2642604, by rfl⟩ : syracuseStep 7046945 = 5285209) B5285209
theorem B4697963 : Blo 2087435 4697963 := bstep (se 1 (by rfl) ⟨3523472, by rfl⟩ : syracuseStep 4697963 = 7046945) B7046945
theorem B3131975 : Blo 2087435 3131975 := bstep (se 1 (by rfl) ⟨2348981, by rfl⟩ : syracuseStep 3131975 = 4697963) B4697963
theorem B2087983 : Blo 2087435 2087983 := bstep (se 1 (by rfl) ⟨1565987, by rfl⟩ : syracuseStep 2087983 = 3131975) B3131975
theorem B3131981 : Blo 2087435 3131981 := bbase (se 3 (by rfl) ⟨587246, by rfl⟩ : syracuseStep 3131981 = 1174493) (by norm_num)
theorem B2087987 : Blo 2087435 2087987 := bstep (se 1 (by rfl) ⟨1565990, by rfl⟩ : syracuseStep 2087987 = 3131981) B3131981
theorem B4697981 : Blo 2087435 4697981 := bbase (se 3 (by rfl) ⟨880871, by rfl⟩ : syracuseStep 4697981 = 1761743) (by norm_num)
theorem B3131987 : Blo 2087435 3131987 := bstep (se 1 (by rfl) ⟨2348990, by rfl⟩ : syracuseStep 3131987 = 4697981) B4697981
theorem B2087991 : Blo 2087435 2087991 := bstep (se 1 (by rfl) ⟨1565993, by rfl⟩ : syracuseStep 2087991 = 3131987) B3131987
theorem B3523493 : Blo 2087435 3523493 := bbase (se 4 (by rfl) ⟨330327, by rfl⟩ : syracuseStep 3523493 = 660655) (by norm_num)
theorem B2348995 : Blo 2087435 2348995 := bstep (se 1 (by rfl) ⟨1761746, by rfl⟩ : syracuseStep 2348995 = 3523493) B3523493
theorem B3131993 : Blo 2087435 3131993 := bstep (se 2 (by rfl) ⟨1174497, by rfl⟩ : syracuseStep 3131993 = 2348995) B2348995
theorem B2087995 : Blo 2087435 2087995 := bstep (se 1 (by rfl) ⟨1565996, by rfl⟩ : syracuseStep 2087995 = 3131993) B3131993
theorem B3344573 : Blo 2087435 3344573 := bbase (se 3 (by rfl) ⟨627107, by rfl⟩ : syracuseStep 3344573 = 1254215) (by norm_num)
theorem B2229715 : Blo 2087435 2229715 := bstep (se 1 (by rfl) ⟨1672286, by rfl⟩ : syracuseStep 2229715 = 3344573) B3344573
theorem B2972953 : Blo 2087435 2972953 := bstep (se 2 (by rfl) ⟨1114857, by rfl⟩ : syracuseStep 2972953 = 2229715) B2229715
theorem B15855749 : Blo 2087435 15855749 := bstep (se 4 (by rfl) ⟨1486476, by rfl⟩ : syracuseStep 15855749 = 2972953) B2972953
theorem B10570499 : Blo 2087435 10570499 := bstep (se 1 (by rfl) ⟨7927874, by rfl⟩ : syracuseStep 10570499 = 15855749) B15855749
theorem B7046999 : Blo 2087435 7046999 := bstep (se 1 (by rfl) ⟨5285249, by rfl⟩ : syracuseStep 7046999 = 10570499) B10570499
theorem B4697999 : Blo 2087435 4697999 := bstep (se 1 (by rfl) ⟨3523499, by rfl⟩ : syracuseStep 4697999 = 7046999) B7046999
theorem B3131999 : Blo 2087435 3131999 := bstep (se 1 (by rfl) ⟨2348999, by rfl⟩ : syracuseStep 3131999 = 4697999) B4697999
theorem B2087999 : Blo 2087435 2087999 := bstep (se 1 (by rfl) ⟨1565999, by rfl⟩ : syracuseStep 2087999 = 3131999) B3131999
theorem B3132005 : Blo 2087435 3132005 := bbase (se 4 (by rfl) ⟨293625, by rfl⟩ : syracuseStep 3132005 = 587251) (by norm_num)
theorem B2088003 : Blo 2087435 2088003 := bstep (se 1 (by rfl) ⟨1566002, by rfl⟩ : syracuseStep 2088003 = 3132005) B3132005
theorem B2972965 : Blo 2087435 2972965 := bbase (se 4 (by rfl) ⟨278715, by rfl⟩ : syracuseStep 2972965 = 557431) (by norm_num)
theorem B3963953 : Blo 2087435 3963953 := bstep (se 2 (by rfl) ⟨1486482, by rfl⟩ : syracuseStep 3963953 = 2972965) B2972965
theorem B2642635 : Blo 2087435 2642635 := bstep (se 1 (by rfl) ⟨1981976, by rfl⟩ : syracuseStep 2642635 = 3963953) B3963953
theorem B3523513 : Blo 2087435 3523513 := bstep (se 2 (by rfl) ⟨1321317, by rfl⟩ : syracuseStep 3523513 = 2642635) B2642635
theorem B4698017 : Blo 2087435 4698017 := bstep (se 2 (by rfl) ⟨1761756, by rfl⟩ : syracuseStep 4698017 = 3523513) B3523513
theorem B3132011 : Blo 2087435 3132011 := bstep (se 1 (by rfl) ⟨2349008, by rfl⟩ : syracuseStep 3132011 = 4698017) B4698017
theorem B2088007 : Blo 2087435 2088007 := bstep (se 1 (by rfl) ⟨1566005, by rfl⟩ : syracuseStep 2088007 = 3132011) B3132011
theorem B2349013 : Blo 2087435 2349013 := bbase (se 7 (by rfl) ⟨27527, by rfl⟩ : syracuseStep 2349013 = 55055) (by norm_num)
theorem B3132017 : Blo 2087435 3132017 := bstep (se 2 (by rfl) ⟨1174506, by rfl⟩ : syracuseStep 3132017 = 2349013) B2349013
theorem B2088011 : Blo 2087435 2088011 := bstep (se 1 (by rfl) ⟨1566008, by rfl⟩ : syracuseStep 2088011 = 3132017) B3132017
theorem B2642645 : Blo 2087435 2642645 := bbase (se 7 (by rfl) ⟨30968, by rfl⟩ : syracuseStep 2642645 = 61937) (by norm_num)
theorem B7047053 : Blo 2087435 7047053 := bstep (se 3 (by rfl) ⟨1321322, by rfl⟩ : syracuseStep 7047053 = 2642645) B2642645
theorem B4698035 : Blo 2087435 4698035 := bstep (se 1 (by rfl) ⟨3523526, by rfl⟩ : syracuseStep 4698035 = 7047053) B7047053
theorem B3132023 : Blo 2087435 3132023 := bstep (se 1 (by rfl) ⟨2349017, by rfl⟩ : syracuseStep 3132023 = 4698035) B4698035
theorem B2088015 : Blo 2087435 2088015 := bstep (se 1 (by rfl) ⟨1566011, by rfl⟩ : syracuseStep 2088015 = 3132023) B3132023
theorem B3132029 : Blo 2087435 3132029 := bbase (se 3 (by rfl) ⟨587255, by rfl⟩ : syracuseStep 3132029 = 1174511) (by norm_num)
theorem B2088019 : Blo 2087435 2088019 := bstep (se 1 (by rfl) ⟨1566014, by rfl⟩ : syracuseStep 2088019 = 3132029) B3132029
theorem B4698053 : Blo 2087435 4698053 := bbase (se 4 (by rfl) ⟨440442, by rfl⟩ : syracuseStep 4698053 = 880885) (by norm_num)
theorem B3132035 : Blo 2087435 3132035 := bstep (se 1 (by rfl) ⟨2349026, by rfl⟩ : syracuseStep 3132035 = 4698053) B4698053
theorem B2088023 : Blo 2087435 2088023 := bstep (se 1 (by rfl) ⟨1566017, by rfl⟩ : syracuseStep 2088023 = 3132035) B3132035
theorem B8918981 : Blo 2087435 8918981 := bbase (se 4 (by rfl) ⟨836154, by rfl⟩ : syracuseStep 8918981 = 1672309) (by norm_num)
theorem B5945987 : Blo 2087435 5945987 := bstep (se 1 (by rfl) ⟨4459490, by rfl⟩ : syracuseStep 5945987 = 8918981) B8918981
theorem B3963991 : Blo 2087435 3963991 := bstep (se 1 (by rfl) ⟨2972993, by rfl⟩ : syracuseStep 3963991 = 5945987) B5945987
theorem B5285321 : Blo 2087435 5285321 := bstep (se 2 (by rfl) ⟨1981995, by rfl⟩ : syracuseStep 5285321 = 3963991) B3963991
theorem B3523547 : Blo 2087435 3523547 := bstep (se 1 (by rfl) ⟨2642660, by rfl⟩ : syracuseStep 3523547 = 5285321) B5285321
theorem B2349031 : Blo 2087435 2349031 := bstep (se 1 (by rfl) ⟨1761773, by rfl⟩ : syracuseStep 2349031 = 3523547) B3523547
theorem B3132041 : Blo 2087435 3132041 := bstep (se 2 (by rfl) ⟨1174515, by rfl⟩ : syracuseStep 3132041 = 2349031) B2349031
theorem B2088027 : Blo 2087435 2088027 := bstep (se 1 (by rfl) ⟨1566020, by rfl⟩ : syracuseStep 2088027 = 3132041) B3132041
theorem B10570661 : Blo 2087435 10570661 := bbase (se 4 (by rfl) ⟨990999, by rfl⟩ : syracuseStep 10570661 = 1981999) (by norm_num)
theorem B7047107 : Blo 2087435 7047107 := bstep (se 1 (by rfl) ⟨5285330, by rfl⟩ : syracuseStep 7047107 = 10570661) B10570661
theorem B4698071 : Blo 2087435 4698071 := bstep (se 1 (by rfl) ⟨3523553, by rfl⟩ : syracuseStep 4698071 = 7047107) B7047107
theorem B3132047 : Blo 2087435 3132047 := bstep (se 1 (by rfl) ⟨2349035, by rfl⟩ : syracuseStep 3132047 = 4698071) B4698071
theorem B2088031 : Blo 2087435 2088031 := bstep (se 1 (by rfl) ⟨1566023, by rfl⟩ : syracuseStep 2088031 = 3132047) B3132047
theorem B3132053 : Blo 2087435 3132053 := bbase (se 6 (by rfl) ⟨73407, by rfl⟩ : syracuseStep 3132053 = 146815) (by norm_num)
theorem B2088035 : Blo 2087435 2088035 := bstep (se 1 (by rfl) ⟨1566026, by rfl⟩ : syracuseStep 2088035 = 3132053) B3132053
theorem B4762189 : Blo 2087435 4762189 := bbase (se 3 (by rfl) ⟨892910, by rfl⟩ : syracuseStep 4762189 = 1785821) (by norm_num)
theorem B6349585 : Blo 2087435 6349585 := bstep (se 2 (by rfl) ⟨2381094, by rfl⟩ : syracuseStep 6349585 = 4762189) B4762189
theorem B8466113 : Blo 2087435 8466113 := bstep (se 2 (by rfl) ⟨3174792, by rfl⟩ : syracuseStep 8466113 = 6349585) B6349585
theorem B5644075 : Blo 2087435 5644075 := bstep (se 1 (by rfl) ⟨4233056, by rfl⟩ : syracuseStep 5644075 = 8466113) B8466113
theorem B7525433 : Blo 2087435 7525433 := bstep (se 2 (by rfl) ⟨2822037, by rfl⟩ : syracuseStep 7525433 = 5644075) B5644075
theorem B20067821 : Blo 2087435 20067821 := bstep (se 3 (by rfl) ⟨3762716, by rfl⟩ : syracuseStep 20067821 = 7525433) B7525433
theorem B13378547 : Blo 2087435 13378547 := bstep (se 1 (by rfl) ⟨10033910, by rfl⟩ : syracuseStep 13378547 = 20067821) B20067821
theorem B8919031 : Blo 2087435 8919031 := bstep (se 1 (by rfl) ⟨6689273, by rfl⟩ : syracuseStep 8919031 = 13378547) B13378547
theorem B11892041 : Blo 2087435 11892041 := bstep (se 2 (by rfl) ⟨4459515, by rfl⟩ : syracuseStep 11892041 = 8919031) B8919031
theorem B7928027 : Blo 2087435 7928027 := bstep (se 1 (by rfl) ⟨5946020, by rfl⟩ : syracuseStep 7928027 = 11892041) B11892041
theorem B5285351 : Blo 2087435 5285351 := bstep (se 1 (by rfl) ⟨3964013, by rfl⟩ : syracuseStep 5285351 = 7928027) B7928027
theorem B3523567 : Blo 2087435 3523567 := bstep (se 1 (by rfl) ⟨2642675, by rfl⟩ : syracuseStep 3523567 = 5285351) B5285351
theorem B4698089 : Blo 2087435 4698089 := bstep (se 2 (by rfl) ⟨1761783, by rfl⟩ : syracuseStep 4698089 = 3523567) B3523567
theorem B3132059 : Blo 2087435 3132059 := bstep (se 1 (by rfl) ⟨2349044, by rfl⟩ : syracuseStep 3132059 = 4698089) B4698089
theorem B2088039 : Blo 2087435 2088039 := bstep (se 1 (by rfl) ⟨1566029, by rfl⟩ : syracuseStep 2088039 = 3132059) B3132059
theorem B2349049 : Blo 2087435 2349049 := bbase (se 2 (by rfl) ⟨880893, by rfl⟩ : syracuseStep 2349049 = 1761787) (by norm_num)
theorem B3132065 : Blo 2087435 3132065 := bstep (se 2 (by rfl) ⟨1174524, by rfl⟩ : syracuseStep 3132065 = 2349049) B2349049
theorem B2088043 : Blo 2087435 2088043 := bstep (se 1 (by rfl) ⟨1566032, by rfl⟩ : syracuseStep 2088043 = 3132065) B3132065
theorem B3174805 : Blo 2087435 3174805 := bbase (se 6 (by rfl) ⟨74409, by rfl⟩ : syracuseStep 3174805 = 148819) (by norm_num)
theorem B4233073 : Blo 2087435 4233073 := bstep (se 2 (by rfl) ⟨1587402, by rfl⟩ : syracuseStep 4233073 = 3174805) B3174805
theorem B5644097 : Blo 2087435 5644097 := bstep (se 2 (by rfl) ⟨2116536, by rfl⟩ : syracuseStep 5644097 = 4233073) B4233073
theorem B3762731 : Blo 2087435 3762731 := bstep (se 1 (by rfl) ⟨2822048, by rfl⟩ : syracuseStep 3762731 = 5644097) B5644097
theorem B10033949 : Blo 2087435 10033949 := bstep (se 3 (by rfl) ⟨1881365, by rfl⟩ : syracuseStep 10033949 = 3762731) B3762731
theorem B6689299 : Blo 2087435 6689299 := bstep (se 1 (by rfl) ⟨5016974, by rfl⟩ : syracuseStep 6689299 = 10033949) B10033949
theorem B8919065 : Blo 2087435 8919065 := bstep (se 2 (by rfl) ⟨3344649, by rfl⟩ : syracuseStep 8919065 = 6689299) B6689299
theorem B5946043 : Blo 2087435 5946043 := bstep (se 1 (by rfl) ⟨4459532, by rfl⟩ : syracuseStep 5946043 = 8919065) B8919065
theorem B7928057 : Blo 2087435 7928057 := bstep (se 2 (by rfl) ⟨2973021, by rfl⟩ : syracuseStep 7928057 = 5946043) B5946043
theorem B5285371 : Blo 2087435 5285371 := bstep (se 1 (by rfl) ⟨3964028, by rfl⟩ : syracuseStep 5285371 = 7928057) B7928057
theorem B7047161 : Blo 2087435 7047161 := bstep (se 2 (by rfl) ⟨2642685, by rfl⟩ : syracuseStep 7047161 = 5285371) B5285371
theorem B4698107 : Blo 2087435 4698107 := bstep (se 1 (by rfl) ⟨3523580, by rfl⟩ : syracuseStep 4698107 = 7047161) B7047161
theorem B3132071 : Blo 2087435 3132071 := bstep (se 1 (by rfl) ⟨2349053, by rfl⟩ : syracuseStep 3132071 = 4698107) B4698107
theorem B2088047 : Blo 2087435 2088047 := bstep (se 1 (by rfl) ⟨1566035, by rfl⟩ : syracuseStep 2088047 = 3132071) B3132071
theorem B3132077 : Blo 2087435 3132077 := bbase (se 3 (by rfl) ⟨587264, by rfl⟩ : syracuseStep 3132077 = 1174529) (by norm_num)
theorem B2088051 : Blo 2087435 2088051 := bstep (se 1 (by rfl) ⟨1566038, by rfl⟩ : syracuseStep 2088051 = 3132077) B3132077
theorem B4698125 : Blo 2087435 4698125 := bbase (se 3 (by rfl) ⟨880898, by rfl⟩ : syracuseStep 4698125 = 1761797) (by norm_num)
theorem B3132083 : Blo 2087435 3132083 := bstep (se 1 (by rfl) ⟨2349062, by rfl⟩ : syracuseStep 3132083 = 4698125) B4698125
theorem B2088055 : Blo 2087435 2088055 := bstep (se 1 (by rfl) ⟨1566041, by rfl⟩ : syracuseStep 2088055 = 3132083) B3132083
theorem B2642701 : Blo 2087435 2642701 := bbase (se 3 (by rfl) ⟨495506, by rfl⟩ : syracuseStep 2642701 = 991013) (by norm_num)
theorem B3523601 : Blo 2087435 3523601 := bstep (se 2 (by rfl) ⟨1321350, by rfl⟩ : syracuseStep 3523601 = 2642701) B2642701
theorem B2349067 : Blo 2087435 2349067 := bstep (se 1 (by rfl) ⟨1761800, by rfl⟩ : syracuseStep 2349067 = 3523601) B3523601
theorem B3132089 : Blo 2087435 3132089 := bstep (se 2 (by rfl) ⟨1174533, by rfl⟩ : syracuseStep 3132089 = 2349067) B2349067
theorem B2088059 : Blo 2087435 2088059 := bstep (se 1 (by rfl) ⟨1566044, by rfl⟩ : syracuseStep 2088059 = 3132089) B3132089
theorem B7143365 : Blo 2087435 7143365 := bbase (se 4 (by rfl) ⟨669690, by rfl⟩ : syracuseStep 7143365 = 1339381) (by norm_num)
theorem B4762243 : Blo 2087435 4762243 := bstep (se 1 (by rfl) ⟨3571682, by rfl⟩ : syracuseStep 4762243 = 7143365) B7143365
theorem B6349657 : Blo 2087435 6349657 := bstep (se 2 (by rfl) ⟨2381121, by rfl⟩ : syracuseStep 6349657 = 4762243) B4762243
theorem B8466209 : Blo 2087435 8466209 := bstep (se 2 (by rfl) ⟨3174828, by rfl⟩ : syracuseStep 8466209 = 6349657) B6349657
theorem B5644139 : Blo 2087435 5644139 := bstep (se 1 (by rfl) ⟨4233104, by rfl⟩ : syracuseStep 5644139 = 8466209) B8466209
theorem B15051037 : Blo 2087435 15051037 := bstep (se 3 (by rfl) ⟨2822069, by rfl⟩ : syracuseStep 15051037 = 5644139) B5644139
theorem B20068049 : Blo 2087435 20068049 := bstep (se 2 (by rfl) ⟨7525518, by rfl⟩ : syracuseStep 20068049 = 15051037) B15051037
theorem B13378699 : Blo 2087435 13378699 := bstep (se 1 (by rfl) ⟨10034024, by rfl⟩ : syracuseStep 13378699 = 20068049) B20068049
theorem B17838265 : Blo 2087435 17838265 := bstep (se 2 (by rfl) ⟨6689349, by rfl⟩ : syracuseStep 17838265 = 13378699) B13378699
theorem B23784353 : Blo 2087435 23784353 := bstep (se 2 (by rfl) ⟨8919132, by rfl⟩ : syracuseStep 23784353 = 17838265) B17838265
theorem B15856235 : Blo 2087435 15856235 := bstep (se 1 (by rfl) ⟨11892176, by rfl⟩ : syracuseStep 15856235 = 23784353) B23784353
theorem B10570823 : Blo 2087435 10570823 := bstep (se 1 (by rfl) ⟨7928117, by rfl⟩ : syracuseStep 10570823 = 15856235) B15856235
theorem B7047215 : Blo 2087435 7047215 := bstep (se 1 (by rfl) ⟨5285411, by rfl⟩ : syracuseStep 7047215 = 10570823) B10570823
theorem B4698143 : Blo 2087435 4698143 := bstep (se 1 (by rfl) ⟨3523607, by rfl⟩ : syracuseStep 4698143 = 7047215) B7047215
theorem B3132095 : Blo 2087435 3132095 := bstep (se 1 (by rfl) ⟨2349071, by rfl⟩ : syracuseStep 3132095 = 4698143) B4698143
theorem B2088063 : Blo 2087435 2088063 := bstep (se 1 (by rfl) ⟨1566047, by rfl⟩ : syracuseStep 2088063 = 3132095) B3132095
theorem B3132101 : Blo 2087435 3132101 := bbase (se 4 (by rfl) ⟨293634, by rfl⟩ : syracuseStep 3132101 = 587269) (by norm_num)
theorem B2088067 : Blo 2087435 2088067 := bstep (se 1 (by rfl) ⟨1566050, by rfl⟩ : syracuseStep 2088067 = 3132101) B3132101
theorem B3523621 : Blo 2087435 3523621 := bbase (se 4 (by rfl) ⟨330339, by rfl⟩ : syracuseStep 3523621 = 660679) (by norm_num)
theorem B4698161 : Blo 2087435 4698161 := bstep (se 2 (by rfl) ⟨1761810, by rfl⟩ : syracuseStep 4698161 = 3523621) B3523621
theorem B3132107 : Blo 2087435 3132107 := bstep (se 1 (by rfl) ⟨2349080, by rfl⟩ : syracuseStep 3132107 = 4698161) B4698161
theorem B2088071 : Blo 2087435 2088071 := bstep (se 1 (by rfl) ⟨1566053, by rfl⟩ : syracuseStep 2088071 = 3132107) B3132107
theorem B2349085 : Blo 2087435 2349085 := bbase (se 3 (by rfl) ⟨440453, by rfl⟩ : syracuseStep 2349085 = 880907) (by norm_num)
theorem B3132113 : Blo 2087435 3132113 := bstep (se 2 (by rfl) ⟨1174542, by rfl⟩ : syracuseStep 3132113 = 2349085) B2349085
theorem B2088075 : Blo 2087435 2088075 := bstep (se 1 (by rfl) ⟨1566056, by rfl⟩ : syracuseStep 2088075 = 3132113) B3132113
theorem B7047269 : Blo 2087435 7047269 := bbase (se 4 (by rfl) ⟨660681, by rfl⟩ : syracuseStep 7047269 = 1321363) (by norm_num)
theorem B4698179 : Blo 2087435 4698179 := bstep (se 1 (by rfl) ⟨3523634, by rfl⟩ : syracuseStep 4698179 = 7047269) B7047269
theorem B3132119 : Blo 2087435 3132119 := bstep (se 1 (by rfl) ⟨2349089, by rfl⟩ : syracuseStep 3132119 = 4698179) B4698179
theorem B2088079 : Blo 2087435 2088079 := bstep (se 1 (by rfl) ⟨1566059, by rfl⟩ : syracuseStep 2088079 = 3132119) B3132119
theorem B3132125 : Blo 2087435 3132125 := bbase (se 3 (by rfl) ⟨587273, by rfl⟩ : syracuseStep 3132125 = 1174547) (by norm_num)
theorem B2088083 : Blo 2087435 2088083 := bstep (se 1 (by rfl) ⟨1566062, by rfl⟩ : syracuseStep 2088083 = 3132125) B3132125
theorem B4698197 : Blo 2087435 4698197 := bbase (se 8 (by rfl) ⟨27528, by rfl⟩ : syracuseStep 4698197 = 55057) (by norm_num)
theorem B3132131 : Blo 2087435 3132131 := bstep (se 1 (by rfl) ⟨2349098, by rfl⟩ : syracuseStep 3132131 = 4698197) B4698197
theorem B2088087 : Blo 2087435 2088087 := bstep (se 1 (by rfl) ⟨1566065, by rfl⟩ : syracuseStep 2088087 = 3132131) B3132131
theorem B4762309 : Blo 2087435 4762309 := bbase (se 4 (by rfl) ⟨446466, by rfl⟩ : syracuseStep 4762309 = 892933) (by norm_num)
theorem B6349745 : Blo 2087435 6349745 := bstep (se 2 (by rfl) ⟨2381154, by rfl⟩ : syracuseStep 6349745 = 4762309) B4762309
theorem B4233163 : Blo 2087435 4233163 := bstep (se 1 (by rfl) ⟨3174872, by rfl⟩ : syracuseStep 4233163 = 6349745) B6349745
theorem B5644217 : Blo 2087435 5644217 := bstep (se 2 (by rfl) ⟨2116581, by rfl⟩ : syracuseStep 5644217 = 4233163) B4233163
theorem B3762811 : Blo 2087435 3762811 := bstep (se 1 (by rfl) ⟨2822108, by rfl⟩ : syracuseStep 3762811 = 5644217) B5644217
theorem B5017081 : Blo 2087435 5017081 := bstep (se 2 (by rfl) ⟨1881405, by rfl⟩ : syracuseStep 5017081 = 3762811) B3762811
theorem B6689441 : Blo 2087435 6689441 := bstep (se 2 (by rfl) ⟨2508540, by rfl⟩ : syracuseStep 6689441 = 5017081) B5017081
theorem B4459627 : Blo 2087435 4459627 := bstep (se 1 (by rfl) ⟨3344720, by rfl⟩ : syracuseStep 4459627 = 6689441) B6689441
theorem B5946169 : Blo 2087435 5946169 := bstep (se 2 (by rfl) ⟨2229813, by rfl⟩ : syracuseStep 5946169 = 4459627) B4459627
theorem B7928225 : Blo 2087435 7928225 := bstep (se 2 (by rfl) ⟨2973084, by rfl⟩ : syracuseStep 7928225 = 5946169) B5946169
theorem B5285483 : Blo 2087435 5285483 := bstep (se 1 (by rfl) ⟨3964112, by rfl⟩ : syracuseStep 5285483 = 7928225) B7928225
theorem B3523655 : Blo 2087435 3523655 := bstep (se 1 (by rfl) ⟨2642741, by rfl⟩ : syracuseStep 3523655 = 5285483) B5285483
theorem B2349103 : Blo 2087435 2349103 := bstep (se 1 (by rfl) ⟨1761827, by rfl⟩ : syracuseStep 2349103 = 3523655) B3523655
theorem B3132137 : Blo 2087435 3132137 := bstep (se 2 (by rfl) ⟨1174551, by rfl⟩ : syracuseStep 3132137 = 2349103) B2349103
theorem B2088091 : Blo 2087435 2088091 := bstep (se 1 (by rfl) ⟨1566068, by rfl⟩ : syracuseStep 2088091 = 3132137) B3132137
theorem B2116585 : Blo 2087435 2116585 := bbase (se 2 (by rfl) ⟨793719, by rfl⟩ : syracuseStep 2116585 = 1587439) (by norm_num)
theorem B2822113 : Blo 2087435 2822113 := bstep (se 2 (by rfl) ⟨1058292, by rfl⟩ : syracuseStep 2822113 = 2116585) B2116585
theorem B3762817 : Blo 2087435 3762817 := bstep (se 2 (by rfl) ⟨1411056, by rfl⟩ : syracuseStep 3762817 = 2822113) B2822113
theorem B20068357 : Blo 2087435 20068357 := bstep (se 4 (by rfl) ⟨1881408, by rfl⟩ : syracuseStep 20068357 = 3762817) B3762817
theorem B26757809 : Blo 2087435 26757809 := bstep (se 2 (by rfl) ⟨10034178, by rfl⟩ : syracuseStep 26757809 = 20068357) B20068357
theorem B17838539 : Blo 2087435 17838539 := bstep (se 1 (by rfl) ⟨13378904, by rfl⟩ : syracuseStep 17838539 = 26757809) B26757809
theorem B11892359 : Blo 2087435 11892359 := bstep (se 1 (by rfl) ⟨8919269, by rfl⟩ : syracuseStep 11892359 = 17838539) B17838539
theorem B7928239 : Blo 2087435 7928239 := bstep (se 1 (by rfl) ⟨5946179, by rfl⟩ : syracuseStep 7928239 = 11892359) B11892359
theorem B10570985 : Blo 2087435 10570985 := bstep (se 2 (by rfl) ⟨3964119, by rfl⟩ : syracuseStep 10570985 = 7928239) B7928239
theorem B7047323 : Blo 2087435 7047323 := bstep (se 1 (by rfl) ⟨5285492, by rfl⟩ : syracuseStep 7047323 = 10570985) B10570985
theorem B4698215 : Blo 2087435 4698215 := bstep (se 1 (by rfl) ⟨3523661, by rfl⟩ : syracuseStep 4698215 = 7047323) B7047323
theorem B3132143 : Blo 2087435 3132143 := bstep (se 1 (by rfl) ⟨2349107, by rfl⟩ : syracuseStep 3132143 = 4698215) B4698215
theorem B2088095 : Blo 2087435 2088095 := bstep (se 1 (by rfl) ⟨1566071, by rfl⟩ : syracuseStep 2088095 = 3132143) B3132143
theorem B3132149 : Blo 2087435 3132149 := bbase (se 5 (by rfl) ⟨146819, by rfl⟩ : syracuseStep 3132149 = 293639) (by norm_num)
theorem B2088099 : Blo 2087435 2088099 := bstep (se 1 (by rfl) ⟨1566074, by rfl⟩ : syracuseStep 2088099 = 3132149) B3132149
theorem B8466373 : Blo 2087435 8466373 := bbase (se 4 (by rfl) ⟨793722, by rfl⟩ : syracuseStep 8466373 = 1587445) (by norm_num)
theorem B11288497 : Blo 2087435 11288497 := bstep (se 2 (by rfl) ⟨4233186, by rfl⟩ : syracuseStep 11288497 = 8466373) B8466373
theorem B15051329 : Blo 2087435 15051329 := bstep (se 2 (by rfl) ⟨5644248, by rfl⟩ : syracuseStep 15051329 = 11288497) B11288497
theorem B10034219 : Blo 2087435 10034219 := bstep (se 1 (by rfl) ⟨7525664, by rfl⟩ : syracuseStep 10034219 = 15051329) B15051329
theorem B6689479 : Blo 2087435 6689479 := bstep (se 1 (by rfl) ⟨5017109, by rfl⟩ : syracuseStep 6689479 = 10034219) B10034219
theorem B8919305 : Blo 2087435 8919305 := bstep (se 2 (by rfl) ⟨3344739, by rfl⟩ : syracuseStep 8919305 = 6689479) B6689479
theorem B5946203 : Blo 2087435 5946203 := bstep (se 1 (by rfl) ⟨4459652, by rfl⟩ : syracuseStep 5946203 = 8919305) B8919305
theorem B3964135 : Blo 2087435 3964135 := bstep (se 1 (by rfl) ⟨2973101, by rfl⟩ : syracuseStep 3964135 = 5946203) B5946203
theorem B5285513 : Blo 2087435 5285513 := bstep (se 2 (by rfl) ⟨1982067, by rfl⟩ : syracuseStep 5285513 = 3964135) B3964135
theorem B3523675 : Blo 2087435 3523675 := bstep (se 1 (by rfl) ⟨2642756, by rfl⟩ : syracuseStep 3523675 = 5285513) B5285513
theorem B4698233 : Blo 2087435 4698233 := bstep (se 2 (by rfl) ⟨1761837, by rfl⟩ : syracuseStep 4698233 = 3523675) B3523675
theorem B3132155 : Blo 2087435 3132155 := bstep (se 1 (by rfl) ⟨2349116, by rfl⟩ : syracuseStep 3132155 = 4698233) B4698233
theorem B2088103 : Blo 2087435 2088103 := bstep (se 1 (by rfl) ⟨1566077, by rfl⟩ : syracuseStep 2088103 = 3132155) B3132155
theorem B2349121 : Blo 2087435 2349121 := bbase (se 2 (by rfl) ⟨880920, by rfl⟩ : syracuseStep 2349121 = 1761841) (by norm_num)
theorem B3132161 : Blo 2087435 3132161 := bstep (se 2 (by rfl) ⟨1174560, by rfl⟩ : syracuseStep 3132161 = 2349121) B2349121
theorem B2088107 : Blo 2087435 2088107 := bstep (se 1 (by rfl) ⟨1566080, by rfl⟩ : syracuseStep 2088107 = 3132161) B3132161
theorem B5285533 : Blo 2087435 5285533 := bbase (se 3 (by rfl) ⟨991037, by rfl⟩ : syracuseStep 5285533 = 1982075) (by norm_num)
theorem B7047377 : Blo 2087435 7047377 := bstep (se 2 (by rfl) ⟨2642766, by rfl⟩ : syracuseStep 7047377 = 5285533) B5285533
theorem B4698251 : Blo 2087435 4698251 := bstep (se 1 (by rfl) ⟨3523688, by rfl⟩ : syracuseStep 4698251 = 7047377) B7047377
theorem B3132167 : Blo 2087435 3132167 := bstep (se 1 (by rfl) ⟨2349125, by rfl⟩ : syracuseStep 3132167 = 4698251) B4698251
theorem B2088111 : Blo 2087435 2088111 := bstep (se 1 (by rfl) ⟨1566083, by rfl⟩ : syracuseStep 2088111 = 3132167) B3132167
theorem B3132173 : Blo 2087435 3132173 := bbase (se 3 (by rfl) ⟨587282, by rfl⟩ : syracuseStep 3132173 = 1174565) (by norm_num)
theorem B2088115 : Blo 2087435 2088115 := bstep (se 1 (by rfl) ⟨1566086, by rfl⟩ : syracuseStep 2088115 = 3132173) B3132173
theorem B4698269 : Blo 2087435 4698269 := bbase (se 3 (by rfl) ⟨880925, by rfl⟩ : syracuseStep 4698269 = 1761851) (by norm_num)
theorem B3132179 : Blo 2087435 3132179 := bstep (se 1 (by rfl) ⟨2349134, by rfl⟩ : syracuseStep 3132179 = 4698269) B4698269
theorem B2088119 : Blo 2087435 2088119 := bstep (se 1 (by rfl) ⟨1566089, by rfl⟩ : syracuseStep 2088119 = 3132179) B3132179
theorem B3523709 : Blo 2087435 3523709 := bbase (se 3 (by rfl) ⟨660695, by rfl⟩ : syracuseStep 3523709 = 1321391) (by norm_num)
theorem B2349139 : Blo 2087435 2349139 := bstep (se 1 (by rfl) ⟨1761854, by rfl⟩ : syracuseStep 2349139 = 3523709) B3523709
theorem B3132185 : Blo 2087435 3132185 := bstep (se 2 (by rfl) ⟨1174569, by rfl⟩ : syracuseStep 3132185 = 2349139) B2349139
theorem B2088123 : Blo 2087435 2088123 := bstep (se 1 (by rfl) ⟨1566092, by rfl⟩ : syracuseStep 2088123 = 3132185) B3132185
theorem B2678845 : Blo 2087435 2678845 := bbase (se 3 (by rfl) ⟨502283, by rfl⟩ : syracuseStep 2678845 = 1004567) (by norm_num)
theorem B3571793 : Blo 2087435 3571793 := bstep (se 2 (by rfl) ⟨1339422, by rfl⟩ : syracuseStep 3571793 = 2678845) B2678845
theorem B2381195 : Blo 2087435 2381195 := bstep (se 1 (by rfl) ⟨1785896, by rfl⟩ : syracuseStep 2381195 = 3571793) B3571793
theorem B6349853 : Blo 2087435 6349853 := bstep (se 3 (by rfl) ⟨1190597, by rfl⟩ : syracuseStep 6349853 = 2381195) B2381195
theorem B4233235 : Blo 2087435 4233235 := bstep (se 1 (by rfl) ⟨3174926, by rfl⟩ : syracuseStep 4233235 = 6349853) B6349853
theorem B5644313 : Blo 2087435 5644313 := bstep (se 2 (by rfl) ⟨2116617, by rfl⟩ : syracuseStep 5644313 = 4233235) B4233235
theorem B3762875 : Blo 2087435 3762875 := bstep (se 1 (by rfl) ⟨2822156, by rfl⟩ : syracuseStep 3762875 = 5644313) B5644313
theorem B10034333 : Blo 2087435 10034333 := bstep (se 3 (by rfl) ⟨1881437, by rfl⟩ : syracuseStep 10034333 = 3762875) B3762875
theorem B6689555 : Blo 2087435 6689555 := bstep (se 1 (by rfl) ⟨5017166, by rfl⟩ : syracuseStep 6689555 = 10034333) B10034333
theorem B4459703 : Blo 2087435 4459703 := bstep (se 1 (by rfl) ⟨3344777, by rfl⟩ : syracuseStep 4459703 = 6689555) B6689555
theorem B11892541 : Blo 2087435 11892541 := bstep (se 3 (by rfl) ⟨2229851, by rfl⟩ : syracuseStep 11892541 = 4459703) B4459703
theorem B15856721 : Blo 2087435 15856721 := bstep (se 2 (by rfl) ⟨5946270, by rfl⟩ : syracuseStep 15856721 = 11892541) B11892541
theorem B10571147 : Blo 2087435 10571147 := bstep (se 1 (by rfl) ⟨7928360, by rfl⟩ : syracuseStep 10571147 = 15856721) B15856721
theorem B7047431 : Blo 2087435 7047431 := bstep (se 1 (by rfl) ⟨5285573, by rfl⟩ : syracuseStep 7047431 = 10571147) B10571147
theorem B4698287 : Blo 2087435 4698287 := bstep (se 1 (by rfl) ⟨3523715, by rfl⟩ : syracuseStep 4698287 = 7047431) B7047431
theorem B3132191 : Blo 2087435 3132191 := bstep (se 1 (by rfl) ⟨2349143, by rfl⟩ : syracuseStep 3132191 = 4698287) B4698287
theorem B2088127 : Blo 2087435 2088127 := bstep (se 1 (by rfl) ⟨1566095, by rfl⟩ : syracuseStep 2088127 = 3132191) B3132191
theorem B3132197 : Blo 2087435 3132197 := bbase (se 4 (by rfl) ⟨293643, by rfl⟩ : syracuseStep 3132197 = 587287) (by norm_num)
theorem B2088131 : Blo 2087435 2088131 := bstep (se 1 (by rfl) ⟨1566098, by rfl⟩ : syracuseStep 2088131 = 3132197) B3132197
theorem B2642797 : Blo 2087435 2642797 := bbase (se 3 (by rfl) ⟨495524, by rfl⟩ : syracuseStep 2642797 = 991049) (by norm_num)
theorem B3523729 : Blo 2087435 3523729 := bstep (se 2 (by rfl) ⟨1321398, by rfl⟩ : syracuseStep 3523729 = 2642797) B2642797
theorem B4698305 : Blo 2087435 4698305 := bstep (se 2 (by rfl) ⟨1761864, by rfl⟩ : syracuseStep 4698305 = 3523729) B3523729
theorem B3132203 : Blo 2087435 3132203 := bstep (se 1 (by rfl) ⟨2349152, by rfl⟩ : syracuseStep 3132203 = 4698305) B4698305
theorem B2088135 : Blo 2087435 2088135 := bstep (se 1 (by rfl) ⟨1566101, by rfl⟩ : syracuseStep 2088135 = 3132203) B3132203
theorem B2349157 : Blo 2087435 2349157 := bbase (se 4 (by rfl) ⟨220233, by rfl⟩ : syracuseStep 2349157 = 440467) (by norm_num)
theorem B3132209 : Blo 2087435 3132209 := bstep (se 2 (by rfl) ⟨1174578, by rfl⟩ : syracuseStep 3132209 = 2349157) B2349157
theorem B2088139 : Blo 2087435 2088139 := bstep (se 1 (by rfl) ⟨1566104, by rfl⟩ : syracuseStep 2088139 = 3132209) B3132209
theorem B2229869 : Blo 2087435 2229869 := bbase (se 3 (by rfl) ⟨418100, by rfl⟩ : syracuseStep 2229869 = 836201) (by norm_num)
theorem B5946317 : Blo 2087435 5946317 := bstep (se 3 (by rfl) ⟨1114934, by rfl⟩ : syracuseStep 5946317 = 2229869) B2229869
theorem B3964211 : Blo 2087435 3964211 := bstep (se 1 (by rfl) ⟨2973158, by rfl⟩ : syracuseStep 3964211 = 5946317) B5946317
theorem B2642807 : Blo 2087435 2642807 := bstep (se 1 (by rfl) ⟨1982105, by rfl⟩ : syracuseStep 2642807 = 3964211) B3964211
theorem B7047485 : Blo 2087435 7047485 := bstep (se 3 (by rfl) ⟨1321403, by rfl⟩ : syracuseStep 7047485 = 2642807) B2642807
theorem B4698323 : Blo 2087435 4698323 := bstep (se 1 (by rfl) ⟨3523742, by rfl⟩ : syracuseStep 4698323 = 7047485) B7047485
theorem B3132215 : Blo 2087435 3132215 := bstep (se 1 (by rfl) ⟨2349161, by rfl⟩ : syracuseStep 3132215 = 4698323) B4698323
theorem B2088143 : Blo 2087435 2088143 := bstep (se 1 (by rfl) ⟨1566107, by rfl⟩ : syracuseStep 2088143 = 3132215) B3132215
theorem B3132221 : Blo 2087435 3132221 := bbase (se 3 (by rfl) ⟨587291, by rfl⟩ : syracuseStep 3132221 = 1174583) (by norm_num)
theorem B2088147 : Blo 2087435 2088147 := bstep (se 1 (by rfl) ⟨1566110, by rfl⟩ : syracuseStep 2088147 = 3132221) B3132221
theorem B4698341 : Blo 2087435 4698341 := bbase (se 4 (by rfl) ⟨440469, by rfl⟩ : syracuseStep 4698341 = 880939) (by norm_num)
theorem B3132227 : Blo 2087435 3132227 := bstep (se 1 (by rfl) ⟨2349170, by rfl⟩ : syracuseStep 3132227 = 4698341) B4698341
theorem B2088151 : Blo 2087435 2088151 := bstep (se 1 (by rfl) ⟨1566113, by rfl⟩ : syracuseStep 2088151 = 3132227) B3132227
theorem B5285645 : Blo 2087435 5285645 := bbase (se 3 (by rfl) ⟨991058, by rfl⟩ : syracuseStep 5285645 = 1982117) (by norm_num)
theorem B3523763 : Blo 2087435 3523763 := bstep (se 1 (by rfl) ⟨2642822, by rfl⟩ : syracuseStep 3523763 = 5285645) B5285645
theorem B2349175 : Blo 2087435 2349175 := bstep (se 1 (by rfl) ⟨1761881, by rfl⟩ : syracuseStep 2349175 = 3523763) B3523763
theorem B3132233 : Blo 2087435 3132233 := bstep (se 2 (by rfl) ⟨1174587, by rfl⟩ : syracuseStep 3132233 = 2349175) B2349175
theorem B2088155 : Blo 2087435 2088155 := bstep (se 1 (by rfl) ⟨1566116, by rfl⟩ : syracuseStep 2088155 = 3132233) B3132233
theorem B2973181 : Blo 2087435 2973181 := bbase (se 3 (by rfl) ⟨557471, by rfl⟩ : syracuseStep 2973181 = 1114943) (by norm_num)
theorem B3964241 : Blo 2087435 3964241 := bstep (se 2 (by rfl) ⟨1486590, by rfl⟩ : syracuseStep 3964241 = 2973181) B2973181
theorem B10571309 : Blo 2087435 10571309 := bstep (se 3 (by rfl) ⟨1982120, by rfl⟩ : syracuseStep 10571309 = 3964241) B3964241
theorem B7047539 : Blo 2087435 7047539 := bstep (se 1 (by rfl) ⟨5285654, by rfl⟩ : syracuseStep 7047539 = 10571309) B10571309
theorem B4698359 : Blo 2087435 4698359 := bstep (se 1 (by rfl) ⟨3523769, by rfl⟩ : syracuseStep 4698359 = 7047539) B7047539
theorem B3132239 : Blo 2087435 3132239 := bstep (se 1 (by rfl) ⟨2349179, by rfl⟩ : syracuseStep 3132239 = 4698359) B4698359
theorem B2088159 : Blo 2087435 2088159 := bstep (se 1 (by rfl) ⟨1566119, by rfl⟩ : syracuseStep 2088159 = 3132239) B3132239
theorem B3132245 : Blo 2087435 3132245 := bbase (se 9 (by rfl) ⟨9176, by rfl⟩ : syracuseStep 3132245 = 18353) (by norm_num)
theorem B2088163 : Blo 2087435 2088163 := bstep (se 1 (by rfl) ⟨1566122, by rfl⟩ : syracuseStep 2088163 = 3132245) B3132245
theorem B4459789 : Blo 2087435 4459789 := bbase (se 3 (by rfl) ⟨836210, by rfl⟩ : syracuseStep 4459789 = 1672421) (by norm_num)
theorem B5946385 : Blo 2087435 5946385 := bstep (se 2 (by rfl) ⟨2229894, by rfl⟩ : syracuseStep 5946385 = 4459789) B4459789
theorem B7928513 : Blo 2087435 7928513 := bstep (se 2 (by rfl) ⟨2973192, by rfl⟩ : syracuseStep 7928513 = 5946385) B5946385
theorem B5285675 : Blo 2087435 5285675 := bstep (se 1 (by rfl) ⟨3964256, by rfl⟩ : syracuseStep 5285675 = 7928513) B7928513
theorem B3523783 : Blo 2087435 3523783 := bstep (se 1 (by rfl) ⟨2642837, by rfl⟩ : syracuseStep 3523783 = 5285675) B5285675
theorem B4698377 : Blo 2087435 4698377 := bstep (se 2 (by rfl) ⟨1761891, by rfl⟩ : syracuseStep 4698377 = 3523783) B3523783
theorem B3132251 : Blo 2087435 3132251 := bstep (se 1 (by rfl) ⟨2349188, by rfl⟩ : syracuseStep 3132251 = 4698377) B4698377
theorem B2088167 : Blo 2087435 2088167 := bstep (se 1 (by rfl) ⟨1566125, by rfl⟩ : syracuseStep 2088167 = 3132251) B3132251
theorem B2349193 : Blo 2087435 2349193 := bbase (se 2 (by rfl) ⟨880947, by rfl⟩ : syracuseStep 2349193 = 1761895) (by norm_num)
theorem B3132257 : Blo 2087435 3132257 := bstep (se 2 (by rfl) ⟨1174596, by rfl⟩ : syracuseStep 3132257 = 2349193) B2349193
theorem B2088171 : Blo 2087435 2088171 := bstep (se 1 (by rfl) ⟨1566128, by rfl⟩ : syracuseStep 2088171 = 3132257) B3132257
theorem B2822221 : Blo 2087435 2822221 := bbase (se 3 (by rfl) ⟨529166, by rfl⟩ : syracuseStep 2822221 = 1058333) (by norm_num)
theorem B15051845 : Blo 2087435 15051845 := bstep (se 4 (by rfl) ⟨1411110, by rfl⟩ : syracuseStep 15051845 = 2822221) B2822221
theorem B40138253 : Blo 2087435 40138253 := bstep (se 3 (by rfl) ⟨7525922, by rfl⟩ : syracuseStep 40138253 = 15051845) B15051845
theorem B26758835 : Blo 2087435 26758835 := bstep (se 1 (by rfl) ⟨20069126, by rfl⟩ : syracuseStep 26758835 = 40138253) B40138253
theorem B17839223 : Blo 2087435 17839223 := bstep (se 1 (by rfl) ⟨13379417, by rfl⟩ : syracuseStep 17839223 = 26758835) B26758835
theorem B11892815 : Blo 2087435 11892815 := bstep (se 1 (by rfl) ⟨8919611, by rfl⟩ : syracuseStep 11892815 = 17839223) B17839223
theorem B7928543 : Blo 2087435 7928543 := bstep (se 1 (by rfl) ⟨5946407, by rfl⟩ : syracuseStep 7928543 = 11892815) B11892815
theorem B5285695 : Blo 2087435 5285695 := bstep (se 1 (by rfl) ⟨3964271, by rfl⟩ : syracuseStep 5285695 = 7928543) B7928543
theorem B7047593 : Blo 2087435 7047593 := bstep (se 2 (by rfl) ⟨2642847, by rfl⟩ : syracuseStep 7047593 = 5285695) B5285695
theorem B4698395 : Blo 2087435 4698395 := bstep (se 1 (by rfl) ⟨3523796, by rfl⟩ : syracuseStep 4698395 = 7047593) B7047593
theorem B3132263 : Blo 2087435 3132263 := bstep (se 1 (by rfl) ⟨2349197, by rfl⟩ : syracuseStep 3132263 = 4698395) B4698395
theorem B2088175 : Blo 2087435 2088175 := bstep (se 1 (by rfl) ⟨1566131, by rfl⟩ : syracuseStep 2088175 = 3132263) B3132263
theorem B3132269 : Blo 2087435 3132269 := bbase (se 3 (by rfl) ⟨587300, by rfl⟩ : syracuseStep 3132269 = 1174601) (by norm_num)
theorem B2088179 : Blo 2087435 2088179 := bstep (se 1 (by rfl) ⟨1566134, by rfl⟩ : syracuseStep 2088179 = 3132269) B3132269
theorem B4698413 : Blo 2087435 4698413 := bbase (se 3 (by rfl) ⟨880952, by rfl⟩ : syracuseStep 4698413 = 1761905) (by norm_num)
theorem B3132275 : Blo 2087435 3132275 := bstep (se 1 (by rfl) ⟨2349206, by rfl⟩ : syracuseStep 3132275 = 4698413) B4698413
theorem B2088183 : Blo 2087435 2088183 := bstep (se 1 (by rfl) ⟨1566137, by rfl⟩ : syracuseStep 2088183 = 3132275) B3132275
theorem B6689749 : Blo 2087435 6689749 := bbase (se 7 (by rfl) ⟨78395, by rfl⟩ : syracuseStep 6689749 = 156791) (by norm_num)
theorem B8919665 : Blo 2087435 8919665 := bstep (se 2 (by rfl) ⟨3344874, by rfl⟩ : syracuseStep 8919665 = 6689749) B6689749
theorem B5946443 : Blo 2087435 5946443 := bstep (se 1 (by rfl) ⟨4459832, by rfl⟩ : syracuseStep 5946443 = 8919665) B8919665
theorem B3964295 : Blo 2087435 3964295 := bstep (se 1 (by rfl) ⟨2973221, by rfl⟩ : syracuseStep 3964295 = 5946443) B5946443
theorem B2642863 : Blo 2087435 2642863 := bstep (se 1 (by rfl) ⟨1982147, by rfl⟩ : syracuseStep 2642863 = 3964295) B3964295
theorem B3523817 : Blo 2087435 3523817 := bstep (se 2 (by rfl) ⟨1321431, by rfl⟩ : syracuseStep 3523817 = 2642863) B2642863
theorem B2349211 : Blo 2087435 2349211 := bstep (se 1 (by rfl) ⟨1761908, by rfl⟩ : syracuseStep 2349211 = 3523817) B3523817
theorem B3132281 : Blo 2087435 3132281 := bstep (se 2 (by rfl) ⟨1174605, by rfl⟩ : syracuseStep 3132281 = 2349211) B2349211
theorem B2088187 : Blo 2087435 2088187 := bstep (se 1 (by rfl) ⟨1566140, by rfl⟩ : syracuseStep 2088187 = 3132281) B3132281
theorem B5799557 : Blo 2087435 5799557 := bbase (se 4 (by rfl) ⟨543708, by rfl⟩ : syracuseStep 5799557 = 1087417) (by norm_num)
theorem B15465485 : Blo 2087435 15465485 := bstep (se 3 (by rfl) ⟨2899778, by rfl⟩ : syracuseStep 15465485 = 5799557) B5799557
theorem B10310323 : Blo 2087435 10310323 := bstep (se 1 (by rfl) ⟨7732742, by rfl⟩ : syracuseStep 10310323 = 15465485) B15465485
theorem B13747097 : Blo 2087435 13747097 := bstep (se 2 (by rfl) ⟨5155161, by rfl⟩ : syracuseStep 13747097 = 10310323) B10310323
theorem B9164731 : Blo 2087435 9164731 := bstep (se 1 (by rfl) ⟨6873548, by rfl⟩ : syracuseStep 9164731 = 13747097) B13747097
theorem B12219641 : Blo 2087435 12219641 := bstep (se 2 (by rfl) ⟨4582365, by rfl⟩ : syracuseStep 12219641 = 9164731) B9164731
theorem B8146427 : Blo 2087435 8146427 := bstep (se 1 (by rfl) ⟨6109820, by rfl⟩ : syracuseStep 8146427 = 12219641) B12219641
theorem B21723805 : Blo 2087435 21723805 := bstep (se 3 (by rfl) ⟨4073213, by rfl⟩ : syracuseStep 21723805 = 8146427) B8146427
theorem B28965073 : Blo 2087435 28965073 := bstep (se 2 (by rfl) ⟨10861902, by rfl⟩ : syracuseStep 28965073 = 21723805) B21723805
theorem B38620097 : Blo 2087435 38620097 := bstep (se 2 (by rfl) ⟨14482536, by rfl⟩ : syracuseStep 38620097 = 28965073) B28965073
theorem B25746731 : Blo 2087435 25746731 := bstep (se 1 (by rfl) ⟨19310048, by rfl⟩ : syracuseStep 25746731 = 38620097) B38620097
theorem B17164487 : Blo 2087435 17164487 := bstep (se 1 (by rfl) ⟨12873365, by rfl⟩ : syracuseStep 17164487 = 25746731) B25746731
theorem B45771965 : Blo 2087435 45771965 := bstep (se 3 (by rfl) ⟨8582243, by rfl⟩ : syracuseStep 45771965 = 17164487) B17164487
theorem B30514643 : Blo 2087435 30514643 := bstep (se 1 (by rfl) ⟨22885982, by rfl⟩ : syracuseStep 30514643 = 45771965) B45771965
theorem B20343095 : Blo 2087435 20343095 := bstep (se 1 (by rfl) ⟨15257321, by rfl⟩ : syracuseStep 20343095 = 30514643) B30514643
theorem B13562063 : Blo 2087435 13562063 := bstep (se 1 (by rfl) ⟨10171547, by rfl⟩ : syracuseStep 13562063 = 20343095) B20343095
theorem B9041375 : Blo 2087435 9041375 := bstep (se 1 (by rfl) ⟨6781031, by rfl⟩ : syracuseStep 9041375 = 13562063) B13562063
theorem B6027583 : Blo 2087435 6027583 := bstep (se 1 (by rfl) ⟨4520687, by rfl⟩ : syracuseStep 6027583 = 9041375) B9041375
theorem B8036777 : Blo 2087435 8036777 := bstep (se 2 (by rfl) ⟨3013791, by rfl⟩ : syracuseStep 8036777 = 6027583) B6027583
theorem B5357851 : Blo 2087435 5357851 := bstep (se 1 (by rfl) ⟨4018388, by rfl⟩ : syracuseStep 5357851 = 8036777) B8036777
theorem B114300821 : Blo 2087435 114300821 := bstep (se 6 (by rfl) ⟨2678925, by rfl⟩ : syracuseStep 114300821 = 5357851) B5357851
theorem B76200547 : Blo 2087435 76200547 := bstep (se 1 (by rfl) ⟨57150410, by rfl⟩ : syracuseStep 76200547 = 114300821) B114300821
theorem B101600729 : Blo 2087435 101600729 := bstep (se 2 (by rfl) ⟨38100273, by rfl⟩ : syracuseStep 101600729 = 76200547) B76200547
theorem B67733819 : Blo 2087435 67733819 := bstep (se 1 (by rfl) ⟨50800364, by rfl⟩ : syracuseStep 67733819 = 101600729) B101600729
theorem B45155879 : Blo 2087435 45155879 := bstep (se 1 (by rfl) ⟨33866909, by rfl⟩ : syracuseStep 45155879 = 67733819) B67733819
theorem B30103919 : Blo 2087435 30103919 := bstep (se 1 (by rfl) ⟨22577939, by rfl⟩ : syracuseStep 30103919 = 45155879) B45155879
theorem B20069279 : Blo 2087435 20069279 := bstep (se 1 (by rfl) ⟨15051959, by rfl⟩ : syracuseStep 20069279 = 30103919) B30103919
theorem B13379519 : Blo 2087435 13379519 := bstep (se 1 (by rfl) ⟨10034639, by rfl⟩ : syracuseStep 13379519 = 20069279) B20069279
theorem B35678717 : Blo 2087435 35678717 := bstep (se 3 (by rfl) ⟨6689759, by rfl⟩ : syracuseStep 35678717 = 13379519) B13379519
theorem B23785811 : Blo 2087435 23785811 := bstep (se 1 (by rfl) ⟨17839358, by rfl⟩ : syracuseStep 23785811 = 35678717) B35678717
theorem B15857207 : Blo 2087435 15857207 := bstep (se 1 (by rfl) ⟨11892905, by rfl⟩ : syracuseStep 15857207 = 23785811) B23785811
theorem B10571471 : Blo 2087435 10571471 := bstep (se 1 (by rfl) ⟨7928603, by rfl⟩ : syracuseStep 10571471 = 15857207) B15857207
theorem B7047647 : Blo 2087435 7047647 := bstep (se 1 (by rfl) ⟨5285735, by rfl⟩ : syracuseStep 7047647 = 10571471) B10571471
theorem B4698431 : Blo 2087435 4698431 := bstep (se 1 (by rfl) ⟨3523823, by rfl⟩ : syracuseStep 4698431 = 7047647) B7047647
theorem B3132287 : Blo 2087435 3132287 := bstep (se 1 (by rfl) ⟨2349215, by rfl⟩ : syracuseStep 3132287 = 4698431) B4698431
theorem B2088191 : Blo 2087435 2088191 := bstep (se 1 (by rfl) ⟨1566143, by rfl⟩ : syracuseStep 2088191 = 3132287) B3132287
theorem B3132293 : Blo 2087435 3132293 := bbase (se 4 (by rfl) ⟨293652, by rfl⟩ : syracuseStep 3132293 = 587305) (by norm_num)
theorem B2088195 : Blo 2087435 2088195 := bstep (se 1 (by rfl) ⟨1566146, by rfl⟩ : syracuseStep 2088195 = 3132293) B3132293
theorem B3523837 : Blo 2087435 3523837 := bbase (se 3 (by rfl) ⟨660719, by rfl⟩ : syracuseStep 3523837 = 1321439) (by norm_num)
theorem B4698449 : Blo 2087435 4698449 := bstep (se 2 (by rfl) ⟨1761918, by rfl⟩ : syracuseStep 4698449 = 3523837) B3523837
theorem B3132299 : Blo 2087435 3132299 := bstep (se 1 (by rfl) ⟨2349224, by rfl⟩ : syracuseStep 3132299 = 4698449) B4698449
theorem B2088199 : Blo 2087435 2088199 := bstep (se 1 (by rfl) ⟨1566149, by rfl⟩ : syracuseStep 2088199 = 3132299) B3132299
theorem B2349229 : Blo 2087435 2349229 := bbase (se 3 (by rfl) ⟨440480, by rfl⟩ : syracuseStep 2349229 = 880961) (by norm_num)
theorem B3132305 : Blo 2087435 3132305 := bstep (se 2 (by rfl) ⟨1174614, by rfl⟩ : syracuseStep 3132305 = 2349229) B2349229
theorem B2088203 : Blo 2087435 2088203 := bstep (se 1 (by rfl) ⟨1566152, by rfl⟩ : syracuseStep 2088203 = 3132305) B3132305
theorem B7047701 : Blo 2087435 7047701 := bbase (se 6 (by rfl) ⟨165180, by rfl⟩ : syracuseStep 7047701 = 330361) (by norm_num)
theorem B4698467 : Blo 2087435 4698467 := bstep (se 1 (by rfl) ⟨3523850, by rfl⟩ : syracuseStep 4698467 = 7047701) B7047701
theorem B3132311 : Blo 2087435 3132311 := bstep (se 1 (by rfl) ⟨2349233, by rfl⟩ : syracuseStep 3132311 = 4698467) B4698467
theorem B2088207 : Blo 2087435 2088207 := bstep (se 1 (by rfl) ⟨1566155, by rfl⟩ : syracuseStep 2088207 = 3132311) B3132311
theorem B3132317 : Blo 2087435 3132317 := bbase (se 3 (by rfl) ⟨587309, by rfl⟩ : syracuseStep 3132317 = 1174619) (by norm_num)
theorem B2088211 : Blo 2087435 2088211 := bstep (se 1 (by rfl) ⟨1566158, by rfl⟩ : syracuseStep 2088211 = 3132317) B3132317
theorem B4698485 : Blo 2087435 4698485 := bbase (se 5 (by rfl) ⟨220241, by rfl⟩ : syracuseStep 4698485 = 440483) (by norm_num)
theorem B3132323 : Blo 2087435 3132323 := bstep (se 1 (by rfl) ⟨2349242, by rfl⟩ : syracuseStep 3132323 = 4698485) B4698485
theorem B2088215 : Blo 2087435 2088215 := bstep (se 1 (by rfl) ⟨1566161, by rfl⟩ : syracuseStep 2088215 = 3132323) B3132323
theorem B13379701 : Blo 2087435 13379701 := bbase (se 5 (by rfl) ⟨627173, by rfl⟩ : syracuseStep 13379701 = 1254347) (by norm_num)
theorem B17839601 : Blo 2087435 17839601 := bstep (se 2 (by rfl) ⟨6689850, by rfl⟩ : syracuseStep 17839601 = 13379701) B13379701
theorem B11893067 : Blo 2087435 11893067 := bstep (se 1 (by rfl) ⟨8919800, by rfl⟩ : syracuseStep 11893067 = 17839601) B17839601
theorem B7928711 : Blo 2087435 7928711 := bstep (se 1 (by rfl) ⟨5946533, by rfl⟩ : syracuseStep 7928711 = 11893067) B11893067
theorem B5285807 : Blo 2087435 5285807 := bstep (se 1 (by rfl) ⟨3964355, by rfl⟩ : syracuseStep 5285807 = 7928711) B7928711
theorem B3523871 : Blo 2087435 3523871 := bstep (se 1 (by rfl) ⟨2642903, by rfl⟩ : syracuseStep 3523871 = 5285807) B5285807
theorem B2349247 : Blo 2087435 2349247 := bstep (se 1 (by rfl) ⟨1761935, by rfl⟩ : syracuseStep 2349247 = 3523871) B3523871
theorem B3132329 : Blo 2087435 3132329 := bstep (se 2 (by rfl) ⟨1174623, by rfl⟩ : syracuseStep 3132329 = 2349247) B2349247
theorem B2088219 : Blo 2087435 2088219 := bstep (se 1 (by rfl) ⟨1566164, by rfl⟩ : syracuseStep 2088219 = 3132329) B3132329
theorem B7928725 : Blo 2087435 7928725 := bbase (se 6 (by rfl) ⟨185829, by rfl⟩ : syracuseStep 7928725 = 371659) (by norm_num)
theorem B10571633 : Blo 2087435 10571633 := bstep (se 2 (by rfl) ⟨3964362, by rfl⟩ : syracuseStep 10571633 = 7928725) B7928725
theorem B7047755 : Blo 2087435 7047755 := bstep (se 1 (by rfl) ⟨5285816, by rfl⟩ : syracuseStep 7047755 = 10571633) B10571633
theorem B4698503 : Blo 2087435 4698503 := bstep (se 1 (by rfl) ⟨3523877, by rfl⟩ : syracuseStep 4698503 = 7047755) B7047755
theorem B3132335 : Blo 2087435 3132335 := bstep (se 1 (by rfl) ⟨2349251, by rfl⟩ : syracuseStep 3132335 = 4698503) B4698503
theorem B2088223 : Blo 2087435 2088223 := bstep (se 1 (by rfl) ⟨1566167, by rfl⟩ : syracuseStep 2088223 = 3132335) B3132335
theorem B3132341 : Blo 2087435 3132341 := bbase (se 5 (by rfl) ⟨146828, by rfl⟩ : syracuseStep 3132341 = 293657) (by norm_num)
theorem B2088227 : Blo 2087435 2088227 := bstep (se 1 (by rfl) ⟨1566170, by rfl⟩ : syracuseStep 2088227 = 3132341) B3132341
theorem B5285837 : Blo 2087435 5285837 := bbase (se 3 (by rfl) ⟨991094, by rfl⟩ : syracuseStep 5285837 = 1982189) (by norm_num)
theorem B3523891 : Blo 2087435 3523891 := bstep (se 1 (by rfl) ⟨2642918, by rfl⟩ : syracuseStep 3523891 = 5285837) B5285837
theorem B4698521 : Blo 2087435 4698521 := bstep (se 2 (by rfl) ⟨1761945, by rfl⟩ : syracuseStep 4698521 = 3523891) B3523891
theorem B3132347 : Blo 2087435 3132347 := bstep (se 1 (by rfl) ⟨2349260, by rfl⟩ : syracuseStep 3132347 = 4698521) B4698521
theorem B2088231 : Blo 2087435 2088231 := bstep (se 1 (by rfl) ⟨1566173, by rfl⟩ : syracuseStep 2088231 = 3132347) B3132347
theorem B2349265 : Blo 2087435 2349265 := bbase (se 2 (by rfl) ⟨880974, by rfl⟩ : syracuseStep 2349265 = 1761949) (by norm_num)
theorem B3132353 : Blo 2087435 3132353 := bstep (se 2 (by rfl) ⟨1174632, by rfl⟩ : syracuseStep 3132353 = 2349265) B2349265
theorem B2088235 : Blo 2087435 2088235 := bstep (se 1 (by rfl) ⟨1566176, by rfl⟩ : syracuseStep 2088235 = 3132353) B3132353
theorem B2678989 : Blo 2087435 2678989 := bbase (se 3 (by rfl) ⟨502310, by rfl⟩ : syracuseStep 2678989 = 1004621) (by norm_num)
theorem B3571985 : Blo 2087435 3571985 := bstep (se 2 (by rfl) ⟨1339494, by rfl⟩ : syracuseStep 3571985 = 2678989) B2678989
theorem B2381323 : Blo 2087435 2381323 := bstep (se 1 (by rfl) ⟨1785992, by rfl⟩ : syracuseStep 2381323 = 3571985) B3571985
theorem B3175097 : Blo 2087435 3175097 := bstep (se 2 (by rfl) ⟨1190661, by rfl⟩ : syracuseStep 3175097 = 2381323) B2381323
theorem B8466925 : Blo 2087435 8466925 := bstep (se 3 (by rfl) ⟨1587548, by rfl⟩ : syracuseStep 8466925 = 3175097) B3175097
theorem B11289233 : Blo 2087435 11289233 := bstep (se 2 (by rfl) ⟨4233462, by rfl⟩ : syracuseStep 11289233 = 8466925) B8466925
theorem B7526155 : Blo 2087435 7526155 := bstep (se 1 (by rfl) ⟨5644616, by rfl⟩ : syracuseStep 7526155 = 11289233) B11289233
theorem B10034873 : Blo 2087435 10034873 := bstep (se 2 (by rfl) ⟨3763077, by rfl⟩ : syracuseStep 10034873 = 7526155) B7526155
theorem B6689915 : Blo 2087435 6689915 := bstep (se 1 (by rfl) ⟨5017436, by rfl⟩ : syracuseStep 6689915 = 10034873) B10034873
theorem B4459943 : Blo 2087435 4459943 := bstep (se 1 (by rfl) ⟨3344957, by rfl⟩ : syracuseStep 4459943 = 6689915) B6689915
theorem B2973295 : Blo 2087435 2973295 := bstep (se 1 (by rfl) ⟨2229971, by rfl⟩ : syracuseStep 2973295 = 4459943) B4459943
theorem B3964393 : Blo 2087435 3964393 := bstep (se 2 (by rfl) ⟨1486647, by rfl⟩ : syracuseStep 3964393 = 2973295) B2973295
theorem B5285857 : Blo 2087435 5285857 := bstep (se 2 (by rfl) ⟨1982196, by rfl⟩ : syracuseStep 5285857 = 3964393) B3964393
theorem B7047809 : Blo 2087435 7047809 := bstep (se 2 (by rfl) ⟨2642928, by rfl⟩ : syracuseStep 7047809 = 5285857) B5285857
theorem B4698539 : Blo 2087435 4698539 := bstep (se 1 (by rfl) ⟨3523904, by rfl⟩ : syracuseStep 4698539 = 7047809) B7047809
theorem B3132359 : Blo 2087435 3132359 := bstep (se 1 (by rfl) ⟨2349269, by rfl⟩ : syracuseStep 3132359 = 4698539) B4698539
theorem B2088239 : Blo 2087435 2088239 := bstep (se 1 (by rfl) ⟨1566179, by rfl⟩ : syracuseStep 2088239 = 3132359) B3132359
theorem B3132365 : Blo 2087435 3132365 := bbase (se 3 (by rfl) ⟨587318, by rfl⟩ : syracuseStep 3132365 = 1174637) (by norm_num)
theorem B2088243 : Blo 2087435 2088243 := bstep (se 1 (by rfl) ⟨1566182, by rfl⟩ : syracuseStep 2088243 = 3132365) B3132365
theorem B4698557 : Blo 2087435 4698557 := bbase (se 3 (by rfl) ⟨880979, by rfl⟩ : syracuseStep 4698557 = 1761959) (by norm_num)
theorem B3132371 : Blo 2087435 3132371 := bstep (se 1 (by rfl) ⟨2349278, by rfl⟩ : syracuseStep 3132371 = 4698557) B4698557
theorem B2088247 : Blo 2087435 2088247 := bstep (se 1 (by rfl) ⟨1566185, by rfl⟩ : syracuseStep 2088247 = 3132371) B3132371
theorem B3523925 : Blo 2087435 3523925 := bbase (se 12 (by rfl) ⟨1290, by rfl⟩ : syracuseStep 3523925 = 2581) (by norm_num)
theorem B2349283 : Blo 2087435 2349283 := bstep (se 1 (by rfl) ⟨1761962, by rfl⟩ : syracuseStep 2349283 = 3523925) B3523925
theorem B3132377 : Blo 2087435 3132377 := bstep (se 2 (by rfl) ⟨1174641, by rfl⟩ : syracuseStep 3132377 = 2349283) B2349283
theorem B2088251 : Blo 2087435 2088251 := bstep (se 1 (by rfl) ⟨1566188, by rfl⟩ : syracuseStep 2088251 = 3132377) B3132377
theorem B2508737 : Blo 2087435 2508737 := bbase (se 2 (by rfl) ⟨940776, by rfl⟩ : syracuseStep 2508737 = 1881553) (by norm_num)
theorem B6689965 : Blo 2087435 6689965 := bstep (se 3 (by rfl) ⟨1254368, by rfl⟩ : syracuseStep 6689965 = 2508737) B2508737
theorem B8919953 : Blo 2087435 8919953 := bstep (se 2 (by rfl) ⟨3344982, by rfl⟩ : syracuseStep 8919953 = 6689965) B6689965
theorem B5946635 : Blo 2087435 5946635 := bstep (se 1 (by rfl) ⟨4459976, by rfl⟩ : syracuseStep 5946635 = 8919953) B8919953
theorem B15857693 : Blo 2087435 15857693 := bstep (se 3 (by rfl) ⟨2973317, by rfl⟩ : syracuseStep 15857693 = 5946635) B5946635
theorem B10571795 : Blo 2087435 10571795 := bstep (se 1 (by rfl) ⟨7928846, by rfl⟩ : syracuseStep 10571795 = 15857693) B15857693
theorem B7047863 : Blo 2087435 7047863 := bstep (se 1 (by rfl) ⟨5285897, by rfl⟩ : syracuseStep 7047863 = 10571795) B10571795
theorem B4698575 : Blo 2087435 4698575 := bstep (se 1 (by rfl) ⟨3523931, by rfl⟩ : syracuseStep 4698575 = 7047863) B7047863
theorem B3132383 : Blo 2087435 3132383 := bstep (se 1 (by rfl) ⟨2349287, by rfl⟩ : syracuseStep 3132383 = 4698575) B4698575
theorem B2088255 : Blo 2087435 2088255 := bstep (se 1 (by rfl) ⟨1566191, by rfl⟩ : syracuseStep 2088255 = 3132383) B3132383
theorem B3132389 : Blo 2087435 3132389 := bbase (se 4 (by rfl) ⟨293661, by rfl⟩ : syracuseStep 3132389 = 587323) (by norm_num)
theorem B2088259 : Blo 2087435 2088259 := bstep (se 1 (by rfl) ⟨1566194, by rfl⟩ : syracuseStep 2088259 = 3132389) B3132389
theorem B8919989 : Blo 2087435 8919989 := bbase (se 5 (by rfl) ⟨418124, by rfl⟩ : syracuseStep 8919989 = 836249) (by norm_num)
theorem B5946659 : Blo 2087435 5946659 := bstep (se 1 (by rfl) ⟨4459994, by rfl⟩ : syracuseStep 5946659 = 8919989) B8919989
theorem B3964439 : Blo 2087435 3964439 := bstep (se 1 (by rfl) ⟨2973329, by rfl⟩ : syracuseStep 3964439 = 5946659) B5946659
theorem B2642959 : Blo 2087435 2642959 := bstep (se 1 (by rfl) ⟨1982219, by rfl⟩ : syracuseStep 2642959 = 3964439) B3964439
theorem B3523945 : Blo 2087435 3523945 := bstep (se 2 (by rfl) ⟨1321479, by rfl⟩ : syracuseStep 3523945 = 2642959) B2642959
theorem B4698593 : Blo 2087435 4698593 := bstep (se 2 (by rfl) ⟨1761972, by rfl⟩ : syracuseStep 4698593 = 3523945) B3523945
theorem B3132395 : Blo 2087435 3132395 := bstep (se 1 (by rfl) ⟨2349296, by rfl⟩ : syracuseStep 3132395 = 4698593) B4698593
theorem B2088263 : Blo 2087435 2088263 := bstep (se 1 (by rfl) ⟨1566197, by rfl⟩ : syracuseStep 2088263 = 3132395) B3132395
theorem B2349301 : Blo 2087435 2349301 := bbase (se 5 (by rfl) ⟨110123, by rfl⟩ : syracuseStep 2349301 = 220247) (by norm_num)
theorem B3132401 : Blo 2087435 3132401 := bstep (se 2 (by rfl) ⟨1174650, by rfl⟩ : syracuseStep 3132401 = 2349301) B2349301
theorem B2088267 : Blo 2087435 2088267 := bstep (se 1 (by rfl) ⟨1566200, by rfl⟩ : syracuseStep 2088267 = 3132401) B3132401
theorem B2642969 : Blo 2087435 2642969 := bbase (se 2 (by rfl) ⟨991113, by rfl⟩ : syracuseStep 2642969 = 1982227) (by norm_num)
theorem B7047917 : Blo 2087435 7047917 := bstep (se 3 (by rfl) ⟨1321484, by rfl⟩ : syracuseStep 7047917 = 2642969) B2642969
theorem B4698611 : Blo 2087435 4698611 := bstep (se 1 (by rfl) ⟨3523958, by rfl⟩ : syracuseStep 4698611 = 7047917) B7047917
theorem B3132407 : Blo 2087435 3132407 := bstep (se 1 (by rfl) ⟨2349305, by rfl⟩ : syracuseStep 3132407 = 4698611) B4698611
theorem B2088271 : Blo 2087435 2088271 := bstep (se 1 (by rfl) ⟨1566203, by rfl⟩ : syracuseStep 2088271 = 3132407) B3132407
theorem B3132413 : Blo 2087435 3132413 := bbase (se 3 (by rfl) ⟨587327, by rfl⟩ : syracuseStep 3132413 = 1174655) (by norm_num)
theorem B2088275 : Blo 2087435 2088275 := bstep (se 1 (by rfl) ⟨1566206, by rfl⟩ : syracuseStep 2088275 = 3132413) B3132413
theorem B4698629 : Blo 2087435 4698629 := bbase (se 4 (by rfl) ⟨440496, by rfl⟩ : syracuseStep 4698629 = 880993) (by norm_num)
theorem B3132419 : Blo 2087435 3132419 := bstep (se 1 (by rfl) ⟨2349314, by rfl⟩ : syracuseStep 3132419 = 4698629) B4698629
theorem B2088279 : Blo 2087435 2088279 := bstep (se 1 (by rfl) ⟨1566209, by rfl⟩ : syracuseStep 2088279 = 3132419) B3132419
theorem B3964477 : Blo 2087435 3964477 := bbase (se 3 (by rfl) ⟨743339, by rfl⟩ : syracuseStep 3964477 = 1486679) (by norm_num)
theorem B5285969 : Blo 2087435 5285969 := bstep (se 2 (by rfl) ⟨1982238, by rfl⟩ : syracuseStep 5285969 = 3964477) B3964477
theorem B3523979 : Blo 2087435 3523979 := bstep (se 1 (by rfl) ⟨2642984, by rfl⟩ : syracuseStep 3523979 = 5285969) B5285969
theorem B2349319 : Blo 2087435 2349319 := bstep (se 1 (by rfl) ⟨1761989, by rfl⟩ : syracuseStep 2349319 = 3523979) B3523979
theorem B3132425 : Blo 2087435 3132425 := bstep (se 2 (by rfl) ⟨1174659, by rfl⟩ : syracuseStep 3132425 = 2349319) B2349319
theorem B2088283 : Blo 2087435 2088283 := bstep (se 1 (by rfl) ⟨1566212, by rfl⟩ : syracuseStep 2088283 = 3132425) B3132425
theorem B10571957 : Blo 2087435 10571957 := bbase (se 5 (by rfl) ⟨495560, by rfl⟩ : syracuseStep 10571957 = 991121) (by norm_num)
theorem B7047971 : Blo 2087435 7047971 := bstep (se 1 (by rfl) ⟨5285978, by rfl⟩ : syracuseStep 7047971 = 10571957) B10571957
theorem B4698647 : Blo 2087435 4698647 := bstep (se 1 (by rfl) ⟨3523985, by rfl⟩ : syracuseStep 4698647 = 7047971) B7047971
theorem B3132431 : Blo 2087435 3132431 := bstep (se 1 (by rfl) ⟨2349323, by rfl⟩ : syracuseStep 3132431 = 4698647) B4698647
theorem B2088287 : Blo 2087435 2088287 := bstep (se 1 (by rfl) ⟨1566215, by rfl⟩ : syracuseStep 2088287 = 3132431) B3132431
theorem B3132437 : Blo 2087435 3132437 := bbase (se 6 (by rfl) ⟨73416, by rfl⟩ : syracuseStep 3132437 = 146833) (by norm_num)
theorem B2088291 : Blo 2087435 2088291 := bstep (se 1 (by rfl) ⟨1566218, by rfl⟩ : syracuseStep 2088291 = 3132437) B3132437
theorem B6873893 : Blo 2087435 6873893 := bbase (se 4 (by rfl) ⟨644427, by rfl⟩ : syracuseStep 6873893 = 1288855) (by norm_num)
theorem B4582595 : Blo 2087435 4582595 := bstep (se 1 (by rfl) ⟨3436946, by rfl⟩ : syracuseStep 4582595 = 6873893) B6873893
theorem B3055063 : Blo 2087435 3055063 := bstep (se 1 (by rfl) ⟨2291297, by rfl⟩ : syracuseStep 3055063 = 4582595) B4582595
theorem B4073417 : Blo 2087435 4073417 := bstep (se 2 (by rfl) ⟨1527531, by rfl⟩ : syracuseStep 4073417 = 3055063) B3055063
theorem B2715611 : Blo 2087435 2715611 := bstep (se 1 (by rfl) ⟨2036708, by rfl⟩ : syracuseStep 2715611 = 4073417) B4073417
theorem B28966517 : Blo 2087435 28966517 := bstep (se 5 (by rfl) ⟨1357805, by rfl⟩ : syracuseStep 28966517 = 2715611) B2715611
theorem B19311011 : Blo 2087435 19311011 := bstep (se 1 (by rfl) ⟨14483258, by rfl⟩ : syracuseStep 19311011 = 28966517) B28966517
theorem B12874007 : Blo 2087435 12874007 := bstep (se 1 (by rfl) ⟨9655505, by rfl⟩ : syracuseStep 12874007 = 19311011) B19311011
theorem B8582671 : Blo 2087435 8582671 := bstep (se 1 (by rfl) ⟨6437003, by rfl⟩ : syracuseStep 8582671 = 12874007) B12874007
theorem B11443561 : Blo 2087435 11443561 := bstep (se 2 (by rfl) ⟨4291335, by rfl⟩ : syracuseStep 11443561 = 8582671) B8582671
theorem B61032325 : Blo 2087435 61032325 := bstep (se 4 (by rfl) ⟨5721780, by rfl⟩ : syracuseStep 61032325 = 11443561) B11443561
theorem B81376433 : Blo 2087435 81376433 := bstep (se 2 (by rfl) ⟨30516162, by rfl⟩ : syracuseStep 81376433 = 61032325) B61032325
theorem B54250955 : Blo 2087435 54250955 := bstep (se 1 (by rfl) ⟨40688216, by rfl⟩ : syracuseStep 54250955 = 81376433) B81376433
theorem B36167303 : Blo 2087435 36167303 := bstep (se 1 (by rfl) ⟨27125477, by rfl⟩ : syracuseStep 36167303 = 54250955) B54250955
theorem B24111535 : Blo 2087435 24111535 := bstep (se 1 (by rfl) ⟨18083651, by rfl⟩ : syracuseStep 24111535 = 36167303) B36167303
theorem B32148713 : Blo 2087435 32148713 := bstep (se 2 (by rfl) ⟨12055767, by rfl⟩ : syracuseStep 32148713 = 24111535) B24111535
theorem B21432475 : Blo 2087435 21432475 := bstep (se 1 (by rfl) ⟨16074356, by rfl⟩ : syracuseStep 21432475 = 32148713) B32148713
theorem B28576633 : Blo 2087435 28576633 := bstep (se 2 (by rfl) ⟨10716237, by rfl⟩ : syracuseStep 28576633 = 21432475) B21432475
theorem B38102177 : Blo 2087435 38102177 := bstep (se 2 (by rfl) ⟨14288316, by rfl⟩ : syracuseStep 38102177 = 28576633) B28576633
theorem B25401451 : Blo 2087435 25401451 := bstep (se 1 (by rfl) ⟨19051088, by rfl⟩ : syracuseStep 25401451 = 38102177) B38102177
theorem B33868601 : Blo 2087435 33868601 := bstep (se 2 (by rfl) ⟨12700725, by rfl⟩ : syracuseStep 33868601 = 25401451) B25401451
theorem B22579067 : Blo 2087435 22579067 := bstep (se 1 (by rfl) ⟨16934300, by rfl⟩ : syracuseStep 22579067 = 33868601) B33868601
theorem B15052711 : Blo 2087435 15052711 := bstep (se 1 (by rfl) ⟨11289533, by rfl⟩ : syracuseStep 15052711 = 22579067) B22579067
theorem B20070281 : Blo 2087435 20070281 := bstep (se 2 (by rfl) ⟨7526355, by rfl⟩ : syracuseStep 20070281 = 15052711) B15052711
theorem B13380187 : Blo 2087435 13380187 := bstep (se 1 (by rfl) ⟨10035140, by rfl⟩ : syracuseStep 13380187 = 20070281) B20070281
theorem B17840249 : Blo 2087435 17840249 := bstep (se 2 (by rfl) ⟨6690093, by rfl⟩ : syracuseStep 17840249 = 13380187) B13380187
theorem B11893499 : Blo 2087435 11893499 := bstep (se 1 (by rfl) ⟨8920124, by rfl⟩ : syracuseStep 11893499 = 17840249) B17840249
theorem B7928999 : Blo 2087435 7928999 := bstep (se 1 (by rfl) ⟨5946749, by rfl⟩ : syracuseStep 7928999 = 11893499) B11893499
theorem B5285999 : Blo 2087435 5285999 := bstep (se 1 (by rfl) ⟨3964499, by rfl⟩ : syracuseStep 5285999 = 7928999) B7928999
theorem B3523999 : Blo 2087435 3523999 := bstep (se 1 (by rfl) ⟨2642999, by rfl⟩ : syracuseStep 3523999 = 5285999) B5285999
theorem B4698665 : Blo 2087435 4698665 := bstep (se 2 (by rfl) ⟨1761999, by rfl⟩ : syracuseStep 4698665 = 3523999) B3523999
theorem B3132443 : Blo 2087435 3132443 := bstep (se 1 (by rfl) ⟨2349332, by rfl⟩ : syracuseStep 3132443 = 4698665) B4698665
theorem B2088295 : Blo 2087435 2088295 := bstep (se 1 (by rfl) ⟨1566221, by rfl⟩ : syracuseStep 2088295 = 3132443) B3132443
theorem B2349337 : Blo 2087435 2349337 := bbase (se 2 (by rfl) ⟨881001, by rfl⟩ : syracuseStep 2349337 = 1762003) (by norm_num)
theorem B3132449 : Blo 2087435 3132449 := bstep (se 2 (by rfl) ⟨1174668, by rfl⟩ : syracuseStep 3132449 = 2349337) B2349337
theorem B2088299 : Blo 2087435 2088299 := bstep (se 1 (by rfl) ⟨1566224, by rfl⟩ : syracuseStep 2088299 = 3132449) B3132449
theorem B7929029 : Blo 2087435 7929029 := bbase (se 4 (by rfl) ⟨743346, by rfl⟩ : syracuseStep 7929029 = 1486693) (by norm_num)
theorem B5286019 : Blo 2087435 5286019 := bstep (se 1 (by rfl) ⟨3964514, by rfl⟩ : syracuseStep 5286019 = 7929029) B7929029
theorem B7048025 : Blo 2087435 7048025 := bstep (se 2 (by rfl) ⟨2643009, by rfl⟩ : syracuseStep 7048025 = 5286019) B5286019
theorem B4698683 : Blo 2087435 4698683 := bstep (se 1 (by rfl) ⟨3524012, by rfl⟩ : syracuseStep 4698683 = 7048025) B7048025
theorem B3132455 : Blo 2087435 3132455 := bstep (se 1 (by rfl) ⟨2349341, by rfl⟩ : syracuseStep 3132455 = 4698683) B4698683
theorem B2088303 : Blo 2087435 2088303 := bstep (se 1 (by rfl) ⟨1566227, by rfl⟩ : syracuseStep 2088303 = 3132455) B3132455
theorem B3132461 : Blo 2087435 3132461 := bbase (se 3 (by rfl) ⟨587336, by rfl⟩ : syracuseStep 3132461 = 1174673) (by norm_num)
theorem B2088307 : Blo 2087435 2088307 := bstep (se 1 (by rfl) ⟨1566230, by rfl⟩ : syracuseStep 2088307 = 3132461) B3132461
theorem B4698701 : Blo 2087435 4698701 := bbase (se 3 (by rfl) ⟨881006, by rfl⟩ : syracuseStep 4698701 = 1762013) (by norm_num)
theorem B3132467 : Blo 2087435 3132467 := bstep (se 1 (by rfl) ⟨2349350, by rfl⟩ : syracuseStep 3132467 = 4698701) B4698701
theorem B2088311 : Blo 2087435 2088311 := bstep (se 1 (by rfl) ⟨1566233, by rfl⟩ : syracuseStep 2088311 = 3132467) B3132467
theorem B2643025 : Blo 2087435 2643025 := bbase (se 2 (by rfl) ⟨991134, by rfl⟩ : syracuseStep 2643025 = 1982269) (by norm_num)
theorem B3524033 : Blo 2087435 3524033 := bstep (se 2 (by rfl) ⟨1321512, by rfl⟩ : syracuseStep 3524033 = 2643025) B2643025
theorem B2349355 : Blo 2087435 2349355 := bstep (se 1 (by rfl) ⟨1762016, by rfl⟩ : syracuseStep 2349355 = 3524033) B3524033
theorem B3132473 : Blo 2087435 3132473 := bstep (se 2 (by rfl) ⟨1174677, by rfl⟩ : syracuseStep 3132473 = 2349355) B2349355
theorem B2088315 : Blo 2087435 2088315 := bstep (se 1 (by rfl) ⟨1566236, by rfl⟩ : syracuseStep 2088315 = 3132473) B3132473
theorem B3345085 : Blo 2087435 3345085 := bbase (se 3 (by rfl) ⟨627203, by rfl⟩ : syracuseStep 3345085 = 1254407) (by norm_num)
theorem B4460113 : Blo 2087435 4460113 := bstep (se 2 (by rfl) ⟨1672542, by rfl⟩ : syracuseStep 4460113 = 3345085) B3345085
theorem B23787269 : Blo 2087435 23787269 := bstep (se 4 (by rfl) ⟨2230056, by rfl⟩ : syracuseStep 23787269 = 4460113) B4460113
theorem B15858179 : Blo 2087435 15858179 := bstep (se 1 (by rfl) ⟨11893634, by rfl⟩ : syracuseStep 15858179 = 23787269) B23787269
theorem B10572119 : Blo 2087435 10572119 := bstep (se 1 (by rfl) ⟨7929089, by rfl⟩ : syracuseStep 10572119 = 15858179) B15858179
theorem B7048079 : Blo 2087435 7048079 := bstep (se 1 (by rfl) ⟨5286059, by rfl⟩ : syracuseStep 7048079 = 10572119) B10572119
theorem B4698719 : Blo 2087435 4698719 := bstep (se 1 (by rfl) ⟨3524039, by rfl⟩ : syracuseStep 4698719 = 7048079) B7048079
theorem B3132479 : Blo 2087435 3132479 := bstep (se 1 (by rfl) ⟨2349359, by rfl⟩ : syracuseStep 3132479 = 4698719) B4698719
theorem B2088319 : Blo 2087435 2088319 := bstep (se 1 (by rfl) ⟨1566239, by rfl⟩ : syracuseStep 2088319 = 3132479) B3132479
theorem B3132485 : Blo 2087435 3132485 := bbase (se 4 (by rfl) ⟨293670, by rfl⟩ : syracuseStep 3132485 = 587341) (by norm_num)
theorem B2088323 : Blo 2087435 2088323 := bstep (se 1 (by rfl) ⟨1566242, by rfl⟩ : syracuseStep 2088323 = 3132485) B3132485
theorem B3524053 : Blo 2087435 3524053 := bbase (se 7 (by rfl) ⟨41297, by rfl⟩ : syracuseStep 3524053 = 82595) (by norm_num)
theorem B4698737 : Blo 2087435 4698737 := bstep (se 2 (by rfl) ⟨1762026, by rfl⟩ : syracuseStep 4698737 = 3524053) B3524053
theorem B3132491 : Blo 2087435 3132491 := bstep (se 1 (by rfl) ⟨2349368, by rfl⟩ : syracuseStep 3132491 = 4698737) B4698737
theorem B2088327 : Blo 2087435 2088327 := bstep (se 1 (by rfl) ⟨1566245, by rfl⟩ : syracuseStep 2088327 = 3132491) B3132491
theorem B2349373 : Blo 2087435 2349373 := bbase (se 3 (by rfl) ⟨440507, by rfl⟩ : syracuseStep 2349373 = 881015) (by norm_num)
theorem B3132497 : Blo 2087435 3132497 := bstep (se 2 (by rfl) ⟨1174686, by rfl⟩ : syracuseStep 3132497 = 2349373) B2349373
theorem B2088331 : Blo 2087435 2088331 := bstep (se 1 (by rfl) ⟨1566248, by rfl⟩ : syracuseStep 2088331 = 3132497) B3132497
theorem B7048133 : Blo 2087435 7048133 := bbase (se 4 (by rfl) ⟨660762, by rfl⟩ : syracuseStep 7048133 = 1321525) (by norm_num)
theorem B4698755 : Blo 2087435 4698755 := bstep (se 1 (by rfl) ⟨3524066, by rfl⟩ : syracuseStep 4698755 = 7048133) B7048133
theorem B3132503 : Blo 2087435 3132503 := bstep (se 1 (by rfl) ⟨2349377, by rfl⟩ : syracuseStep 3132503 = 4698755) B4698755
theorem B2088335 : Blo 2087435 2088335 := bstep (se 1 (by rfl) ⟨1566251, by rfl⟩ : syracuseStep 2088335 = 3132503) B3132503
theorem B3132509 : Blo 2087435 3132509 := bbase (se 3 (by rfl) ⟨587345, by rfl⟩ : syracuseStep 3132509 = 1174691) (by norm_num)
theorem B2088339 : Blo 2087435 2088339 := bstep (se 1 (by rfl) ⟨1566254, by rfl⟩ : syracuseStep 2088339 = 3132509) B3132509
theorem B4698773 : Blo 2087435 4698773 := bbase (se 6 (by rfl) ⟨110127, by rfl⟩ : syracuseStep 4698773 = 220255) (by norm_num)
theorem B3132515 : Blo 2087435 3132515 := bstep (se 1 (by rfl) ⟨2349386, by rfl⟩ : syracuseStep 3132515 = 4698773) B4698773
theorem B2088343 : Blo 2087435 2088343 := bstep (se 1 (by rfl) ⟨1566257, by rfl⟩ : syracuseStep 2088343 = 3132515) B3132515
theorem B4018693 : Blo 2087435 4018693 := bbase (se 4 (by rfl) ⟨376752, by rfl⟩ : syracuseStep 4018693 = 753505) (by norm_num)
theorem B5358257 : Blo 2087435 5358257 := bstep (se 2 (by rfl) ⟨2009346, by rfl⟩ : syracuseStep 5358257 = 4018693) B4018693
theorem B3572171 : Blo 2087435 3572171 := bstep (se 1 (by rfl) ⟨2679128, by rfl⟩ : syracuseStep 3572171 = 5358257) B5358257
theorem B2381447 : Blo 2087435 2381447 := bstep (se 1 (by rfl) ⟨1786085, by rfl⟩ : syracuseStep 2381447 = 3572171) B3572171
theorem B6350525 : Blo 2087435 6350525 := bstep (se 3 (by rfl) ⟨1190723, by rfl⟩ : syracuseStep 6350525 = 2381447) B2381447
theorem B4233683 : Blo 2087435 4233683 := bstep (se 1 (by rfl) ⟨3175262, by rfl⟩ : syracuseStep 4233683 = 6350525) B6350525
theorem B2822455 : Blo 2087435 2822455 := bstep (se 1 (by rfl) ⟨2116841, by rfl⟩ : syracuseStep 2822455 = 4233683) B4233683
theorem B3763273 : Blo 2087435 3763273 := bstep (se 2 (by rfl) ⟨1411227, by rfl⟩ : syracuseStep 3763273 = 2822455) B2822455
theorem B5017697 : Blo 2087435 5017697 := bstep (se 2 (by rfl) ⟨1881636, by rfl⟩ : syracuseStep 5017697 = 3763273) B3763273
theorem B3345131 : Blo 2087435 3345131 := bstep (se 1 (by rfl) ⟨2508848, by rfl⟩ : syracuseStep 3345131 = 5017697) B5017697
theorem B2230087 : Blo 2087435 2230087 := bstep (se 1 (by rfl) ⟨1672565, by rfl⟩ : syracuseStep 2230087 = 3345131) B3345131
theorem B2973449 : Blo 2087435 2973449 := bstep (se 2 (by rfl) ⟨1115043, by rfl⟩ : syracuseStep 2973449 = 2230087) B2230087
theorem B7929197 : Blo 2087435 7929197 := bstep (se 3 (by rfl) ⟨1486724, by rfl⟩ : syracuseStep 7929197 = 2973449) B2973449
theorem B5286131 : Blo 2087435 5286131 := bstep (se 1 (by rfl) ⟨3964598, by rfl⟩ : syracuseStep 5286131 = 7929197) B7929197
theorem B3524087 : Blo 2087435 3524087 := bstep (se 1 (by rfl) ⟨2643065, by rfl⟩ : syracuseStep 3524087 = 5286131) B5286131
theorem B2349391 : Blo 2087435 2349391 := bstep (se 1 (by rfl) ⟨1762043, by rfl⟩ : syracuseStep 2349391 = 3524087) B3524087
theorem B3132521 : Blo 2087435 3132521 := bstep (se 2 (by rfl) ⟨1174695, by rfl⟩ : syracuseStep 3132521 = 2349391) B2349391
theorem B2088347 : Blo 2087435 2088347 := bstep (se 1 (by rfl) ⟨1566260, by rfl⟩ : syracuseStep 2088347 = 3132521) B3132521
theorem B4762901 : Blo 2087435 4762901 := bbase (se 6 (by rfl) ⟨111630, by rfl⟩ : syracuseStep 4762901 = 223261) (by norm_num)
theorem B3175267 : Blo 2087435 3175267 := bstep (se 1 (by rfl) ⟨2381450, by rfl⟩ : syracuseStep 3175267 = 4762901) B4762901
theorem B4233689 : Blo 2087435 4233689 := bstep (se 2 (by rfl) ⟨1587633, by rfl⟩ : syracuseStep 4233689 = 3175267) B3175267
theorem B2822459 : Blo 2087435 2822459 := bstep (se 1 (by rfl) ⟨2116844, by rfl⟩ : syracuseStep 2822459 = 4233689) B4233689
theorem B7526557 : Blo 2087435 7526557 := bstep (se 3 (by rfl) ⟨1411229, by rfl⟩ : syracuseStep 7526557 = 2822459) B2822459
theorem B10035409 : Blo 2087435 10035409 := bstep (se 2 (by rfl) ⟨3763278, by rfl⟩ : syracuseStep 10035409 = 7526557) B7526557
theorem B13380545 : Blo 2087435 13380545 := bstep (se 2 (by rfl) ⟨5017704, by rfl⟩ : syracuseStep 13380545 = 10035409) B10035409
theorem B8920363 : Blo 2087435 8920363 := bstep (se 1 (by rfl) ⟨6690272, by rfl⟩ : syracuseStep 8920363 = 13380545) B13380545
theorem B11893817 : Blo 2087435 11893817 := bstep (se 2 (by rfl) ⟨4460181, by rfl⟩ : syracuseStep 11893817 = 8920363) B8920363
theorem B7929211 : Blo 2087435 7929211 := bstep (se 1 (by rfl) ⟨5946908, by rfl⟩ : syracuseStep 7929211 = 11893817) B11893817
theorem B10572281 : Blo 2087435 10572281 := bstep (se 2 (by rfl) ⟨3964605, by rfl⟩ : syracuseStep 10572281 = 7929211) B7929211
theorem B7048187 : Blo 2087435 7048187 := bstep (se 1 (by rfl) ⟨5286140, by rfl⟩ : syracuseStep 7048187 = 10572281) B10572281
theorem B4698791 : Blo 2087435 4698791 := bstep (se 1 (by rfl) ⟨3524093, by rfl⟩ : syracuseStep 4698791 = 7048187) B7048187
theorem B3132527 : Blo 2087435 3132527 := bstep (se 1 (by rfl) ⟨2349395, by rfl⟩ : syracuseStep 3132527 = 4698791) B4698791
theorem B2088351 : Blo 2087435 2088351 := bstep (se 1 (by rfl) ⟨1566263, by rfl⟩ : syracuseStep 2088351 = 3132527) B3132527
theorem B3132533 : Blo 2087435 3132533 := bbase (se 5 (by rfl) ⟨146837, by rfl⟩ : syracuseStep 3132533 = 293675) (by norm_num)
theorem B2088355 : Blo 2087435 2088355 := bstep (se 1 (by rfl) ⟨1566266, by rfl⟩ : syracuseStep 2088355 = 3132533) B3132533
theorem B3964621 : Blo 2087435 3964621 := bbase (se 3 (by rfl) ⟨743366, by rfl⟩ : syracuseStep 3964621 = 1486733) (by norm_num)
theorem B5286161 : Blo 2087435 5286161 := bstep (se 2 (by rfl) ⟨1982310, by rfl⟩ : syracuseStep 5286161 = 3964621) B3964621
theorem B3524107 : Blo 2087435 3524107 := bstep (se 1 (by rfl) ⟨2643080, by rfl⟩ : syracuseStep 3524107 = 5286161) B5286161
theorem B4698809 : Blo 2087435 4698809 := bstep (se 2 (by rfl) ⟨1762053, by rfl⟩ : syracuseStep 4698809 = 3524107) B3524107
theorem B3132539 : Blo 2087435 3132539 := bstep (se 1 (by rfl) ⟨2349404, by rfl⟩ : syracuseStep 3132539 = 4698809) B4698809
theorem B2088359 : Blo 2087435 2088359 := bstep (se 1 (by rfl) ⟨1566269, by rfl⟩ : syracuseStep 2088359 = 3132539) B3132539
theorem B2349409 : Blo 2087435 2349409 := bbase (se 2 (by rfl) ⟨881028, by rfl⟩ : syracuseStep 2349409 = 1762057) (by norm_num)
theorem B3132545 : Blo 2087435 3132545 := bstep (se 2 (by rfl) ⟨1174704, by rfl⟩ : syracuseStep 3132545 = 2349409) B2349409
theorem B2088363 : Blo 2087435 2088363 := bstep (se 1 (by rfl) ⟨1566272, by rfl⟩ : syracuseStep 2088363 = 3132545) B3132545
theorem B5286181 : Blo 2087435 5286181 := bbase (se 4 (by rfl) ⟨495579, by rfl⟩ : syracuseStep 5286181 = 991159) (by norm_num)
theorem B7048241 : Blo 2087435 7048241 := bstep (se 2 (by rfl) ⟨2643090, by rfl⟩ : syracuseStep 7048241 = 5286181) B5286181
theorem B4698827 : Blo 2087435 4698827 := bstep (se 1 (by rfl) ⟨3524120, by rfl⟩ : syracuseStep 4698827 = 7048241) B7048241
theorem B3132551 : Blo 2087435 3132551 := bstep (se 1 (by rfl) ⟨2349413, by rfl⟩ : syracuseStep 3132551 = 4698827) B4698827
theorem B2088367 : Blo 2087435 2088367 := bstep (se 1 (by rfl) ⟨1566275, by rfl⟩ : syracuseStep 2088367 = 3132551) B3132551
theorem B3132557 : Blo 2087435 3132557 := bbase (se 3 (by rfl) ⟨587354, by rfl⟩ : syracuseStep 3132557 = 1174709) (by norm_num)
theorem B2088371 : Blo 2087435 2088371 := bstep (se 1 (by rfl) ⟨1566278, by rfl⟩ : syracuseStep 2088371 = 3132557) B3132557
theorem B4698845 : Blo 2087435 4698845 := bbase (se 3 (by rfl) ⟨881033, by rfl⟩ : syracuseStep 4698845 = 1762067) (by norm_num)
theorem B3132563 : Blo 2087435 3132563 := bstep (se 1 (by rfl) ⟨2349422, by rfl⟩ : syracuseStep 3132563 = 4698845) B4698845
theorem B2088375 : Blo 2087435 2088375 := bstep (se 1 (by rfl) ⟨1566281, by rfl⟩ : syracuseStep 2088375 = 3132563) B3132563
theorem B3524141 : Blo 2087435 3524141 := bbase (se 3 (by rfl) ⟨660776, by rfl⟩ : syracuseStep 3524141 = 1321553) (by norm_num)
theorem B2349427 : Blo 2087435 2349427 := bstep (se 1 (by rfl) ⟨1762070, by rfl⟩ : syracuseStep 2349427 = 3524141) B3524141
theorem B3132569 : Blo 2087435 3132569 := bstep (se 2 (by rfl) ⟨1174713, by rfl⟩ : syracuseStep 3132569 = 2349427) B2349427
theorem B2088379 : Blo 2087435 2088379 := bstep (se 1 (by rfl) ⟨1566284, by rfl⟩ : syracuseStep 2088379 = 3132569) B3132569
theorem B4291517 : Blo 2087435 4291517 := bbase (se 3 (by rfl) ⟨804659, by rfl⟩ : syracuseStep 4291517 = 1609319) (by norm_num)
theorem B2861011 : Blo 2087435 2861011 := bstep (se 1 (by rfl) ⟨2145758, by rfl⟩ : syracuseStep 2861011 = 4291517) B4291517
theorem B3814681 : Blo 2087435 3814681 := bstep (se 2 (by rfl) ⟨1430505, by rfl⟩ : syracuseStep 3814681 = 2861011) B2861011
theorem B5086241 : Blo 2087435 5086241 := bstep (se 2 (by rfl) ⟨1907340, by rfl⟩ : syracuseStep 5086241 = 3814681) B3814681
theorem B3390827 : Blo 2087435 3390827 := bstep (se 1 (by rfl) ⟨2543120, by rfl⟩ : syracuseStep 3390827 = 5086241) B5086241
theorem B36168821 : Blo 2087435 36168821 := bstep (se 5 (by rfl) ⟨1695413, by rfl⟩ : syracuseStep 36168821 = 3390827) B3390827
theorem B24112547 : Blo 2087435 24112547 := bstep (se 1 (by rfl) ⟨18084410, by rfl⟩ : syracuseStep 24112547 = 36168821) B36168821
theorem B16075031 : Blo 2087435 16075031 := bstep (se 1 (by rfl) ⟨12056273, by rfl⟩ : syracuseStep 16075031 = 24112547) B24112547
theorem B42866749 : Blo 2087435 42866749 := bstep (se 3 (by rfl) ⟨8037515, by rfl⟩ : syracuseStep 42866749 = 16075031) B16075031
theorem B228622661 : Blo 2087435 228622661 := bstep (se 4 (by rfl) ⟨21433374, by rfl⟩ : syracuseStep 228622661 = 42866749) B42866749
theorem B152415107 : Blo 2087435 152415107 := bstep (se 1 (by rfl) ⟨114311330, by rfl⟩ : syracuseStep 152415107 = 228622661) B228622661
theorem B101610071 : Blo 2087435 101610071 := bstep (se 1 (by rfl) ⟨76207553, by rfl⟩ : syracuseStep 101610071 = 152415107) B152415107
theorem B67740047 : Blo 2087435 67740047 := bstep (se 1 (by rfl) ⟨50805035, by rfl⟩ : syracuseStep 67740047 = 101610071) B101610071
theorem B45160031 : Blo 2087435 45160031 := bstep (se 1 (by rfl) ⟨33870023, by rfl⟩ : syracuseStep 45160031 = 67740047) B67740047
theorem B30106687 : Blo 2087435 30106687 := bstep (se 1 (by rfl) ⟨22580015, by rfl⟩ : syracuseStep 30106687 = 45160031) B45160031
theorem B40142249 : Blo 2087435 40142249 := bstep (se 2 (by rfl) ⟨15053343, by rfl⟩ : syracuseStep 40142249 = 30106687) B30106687
theorem B26761499 : Blo 2087435 26761499 := bstep (se 1 (by rfl) ⟨20071124, by rfl⟩ : syracuseStep 26761499 = 40142249) B40142249
theorem B17840999 : Blo 2087435 17840999 := bstep (se 1 (by rfl) ⟨13380749, by rfl⟩ : syracuseStep 17840999 = 26761499) B26761499
theorem B11893999 : Blo 2087435 11893999 := bstep (se 1 (by rfl) ⟨8920499, by rfl⟩ : syracuseStep 11893999 = 17840999) B17840999
theorem B15858665 : Blo 2087435 15858665 := bstep (se 2 (by rfl) ⟨5946999, by rfl⟩ : syracuseStep 15858665 = 11893999) B11893999
theorem B10572443 : Blo 2087435 10572443 := bstep (se 1 (by rfl) ⟨7929332, by rfl⟩ : syracuseStep 10572443 = 15858665) B15858665
theorem B7048295 : Blo 2087435 7048295 := bstep (se 1 (by rfl) ⟨5286221, by rfl⟩ : syracuseStep 7048295 = 10572443) B10572443
theorem B4698863 : Blo 2087435 4698863 := bstep (se 1 (by rfl) ⟨3524147, by rfl⟩ : syracuseStep 4698863 = 7048295) B7048295
theorem B3132575 : Blo 2087435 3132575 := bstep (se 1 (by rfl) ⟨2349431, by rfl⟩ : syracuseStep 3132575 = 4698863) B4698863
theorem B2088383 : Blo 2087435 2088383 := bstep (se 1 (by rfl) ⟨1566287, by rfl⟩ : syracuseStep 2088383 = 3132575) B3132575
theorem B3132581 : Blo 2087435 3132581 := bbase (se 4 (by rfl) ⟨293679, by rfl⟩ : syracuseStep 3132581 = 587359) (by norm_num)
theorem B2088387 : Blo 2087435 2088387 := bstep (se 1 (by rfl) ⟨1566290, by rfl⟩ : syracuseStep 2088387 = 3132581) B3132581
theorem B2643121 : Blo 2087435 2643121 := bbase (se 2 (by rfl) ⟨991170, by rfl⟩ : syracuseStep 2643121 = 1982341) (by norm_num)
theorem B3524161 : Blo 2087435 3524161 := bstep (se 2 (by rfl) ⟨1321560, by rfl⟩ : syracuseStep 3524161 = 2643121) B2643121
theorem B4698881 : Blo 2087435 4698881 := bstep (se 2 (by rfl) ⟨1762080, by rfl⟩ : syracuseStep 4698881 = 3524161) B3524161
theorem B3132587 : Blo 2087435 3132587 := bstep (se 1 (by rfl) ⟨2349440, by rfl⟩ : syracuseStep 3132587 = 4698881) B4698881
theorem B2088391 : Blo 2087435 2088391 := bstep (se 1 (by rfl) ⟨1566293, by rfl⟩ : syracuseStep 2088391 = 3132587) B3132587
theorem B2349445 : Blo 2087435 2349445 := bbase (se 4 (by rfl) ⟨220260, by rfl⟩ : syracuseStep 2349445 = 440521) (by norm_num)
theorem B3132593 : Blo 2087435 3132593 := bstep (se 2 (by rfl) ⟨1174722, by rfl⟩ : syracuseStep 3132593 = 2349445) B2349445
theorem B2088395 : Blo 2087435 2088395 := bstep (se 1 (by rfl) ⟨1566296, by rfl⟩ : syracuseStep 2088395 = 3132593) B3132593
theorem B4460285 : Blo 2087435 4460285 := bbase (se 3 (by rfl) ⟨836303, by rfl⟩ : syracuseStep 4460285 = 1672607) (by norm_num)
theorem B2973523 : Blo 2087435 2973523 := bstep (se 1 (by rfl) ⟨2230142, by rfl⟩ : syracuseStep 2973523 = 4460285) B4460285
theorem B3964697 : Blo 2087435 3964697 := bstep (se 2 (by rfl) ⟨1486761, by rfl⟩ : syracuseStep 3964697 = 2973523) B2973523
theorem B2643131 : Blo 2087435 2643131 := bstep (se 1 (by rfl) ⟨1982348, by rfl⟩ : syracuseStep 2643131 = 3964697) B3964697
theorem B7048349 : Blo 2087435 7048349 := bstep (se 3 (by rfl) ⟨1321565, by rfl⟩ : syracuseStep 7048349 = 2643131) B2643131
theorem B4698899 : Blo 2087435 4698899 := bstep (se 1 (by rfl) ⟨3524174, by rfl⟩ : syracuseStep 4698899 = 7048349) B7048349
theorem B3132599 : Blo 2087435 3132599 := bstep (se 1 (by rfl) ⟨2349449, by rfl⟩ : syracuseStep 3132599 = 4698899) B4698899
theorem B2088399 : Blo 2087435 2088399 := bstep (se 1 (by rfl) ⟨1566299, by rfl⟩ : syracuseStep 2088399 = 3132599) B3132599
theorem B3132605 : Blo 2087435 3132605 := bbase (se 3 (by rfl) ⟨587363, by rfl⟩ : syracuseStep 3132605 = 1174727) (by norm_num)
theorem B2088403 : Blo 2087435 2088403 := bstep (se 1 (by rfl) ⟨1566302, by rfl⟩ : syracuseStep 2088403 = 3132605) B3132605
theorem B4698917 : Blo 2087435 4698917 := bbase (se 4 (by rfl) ⟨440523, by rfl⟩ : syracuseStep 4698917 = 881047) (by norm_num)
theorem B3132611 : Blo 2087435 3132611 := bstep (se 1 (by rfl) ⟨2349458, by rfl⟩ : syracuseStep 3132611 = 4698917) B4698917
theorem B2088407 : Blo 2087435 2088407 := bstep (se 1 (by rfl) ⟨1566305, by rfl⟩ : syracuseStep 2088407 = 3132611) B3132611
theorem B5286293 : Blo 2087435 5286293 := bbase (se 6 (by rfl) ⟨123897, by rfl⟩ : syracuseStep 5286293 = 247795) (by norm_num)
theorem B3524195 : Blo 2087435 3524195 := bstep (se 1 (by rfl) ⟨2643146, by rfl⟩ : syracuseStep 3524195 = 5286293) B5286293
theorem B2349463 : Blo 2087435 2349463 := bstep (se 1 (by rfl) ⟨1762097, by rfl⟩ : syracuseStep 2349463 = 3524195) B3524195
theorem B3132617 : Blo 2087435 3132617 := bstep (se 2 (by rfl) ⟨1174731, by rfl⟩ : syracuseStep 3132617 = 2349463) B2349463
theorem B2088411 : Blo 2087435 2088411 := bstep (se 1 (by rfl) ⟨1566308, by rfl⟩ : syracuseStep 2088411 = 3132617) B3132617
theorem B7526789 : Blo 2087435 7526789 := bbase (se 4 (by rfl) ⟨705636, by rfl⟩ : syracuseStep 7526789 = 1411273) (by norm_num)
theorem B5017859 : Blo 2087435 5017859 := bstep (se 1 (by rfl) ⟨3763394, by rfl⟩ : syracuseStep 5017859 = 7526789) B7526789
theorem B3345239 : Blo 2087435 3345239 := bstep (se 1 (by rfl) ⟨2508929, by rfl⟩ : syracuseStep 3345239 = 5017859) B5017859
theorem B8920637 : Blo 2087435 8920637 := bstep (se 3 (by rfl) ⟨1672619, by rfl⟩ : syracuseStep 8920637 = 3345239) B3345239
theorem B5947091 : Blo 2087435 5947091 := bstep (se 1 (by rfl) ⟨4460318, by rfl⟩ : syracuseStep 5947091 = 8920637) B8920637
theorem B3964727 : Blo 2087435 3964727 := bstep (se 1 (by rfl) ⟨2973545, by rfl⟩ : syracuseStep 3964727 = 5947091) B5947091
theorem B10572605 : Blo 2087435 10572605 := bstep (se 3 (by rfl) ⟨1982363, by rfl⟩ : syracuseStep 10572605 = 3964727) B3964727
theorem B7048403 : Blo 2087435 7048403 := bstep (se 1 (by rfl) ⟨5286302, by rfl⟩ : syracuseStep 7048403 = 10572605) B10572605
theorem B4698935 : Blo 2087435 4698935 := bstep (se 1 (by rfl) ⟨3524201, by rfl⟩ : syracuseStep 4698935 = 7048403) B7048403
theorem B3132623 : Blo 2087435 3132623 := bstep (se 1 (by rfl) ⟨2349467, by rfl⟩ : syracuseStep 3132623 = 4698935) B4698935
theorem B2088415 : Blo 2087435 2088415 := bstep (se 1 (by rfl) ⟨1566311, by rfl⟩ : syracuseStep 2088415 = 3132623) B3132623
theorem B3132629 : Blo 2087435 3132629 := bbase (se 7 (by rfl) ⟨36710, by rfl⟩ : syracuseStep 3132629 = 73421) (by norm_num)
theorem B2088419 : Blo 2087435 2088419 := bstep (se 1 (by rfl) ⟨1566314, by rfl⟩ : syracuseStep 2088419 = 3132629) B3132629
theorem B2973557 : Blo 2087435 2973557 := bbase (se 5 (by rfl) ⟨139385, by rfl⟩ : syracuseStep 2973557 = 278771) (by norm_num)
theorem B7929485 : Blo 2087435 7929485 := bstep (se 3 (by rfl) ⟨1486778, by rfl⟩ : syracuseStep 7929485 = 2973557) B2973557
theorem B5286323 : Blo 2087435 5286323 := bstep (se 1 (by rfl) ⟨3964742, by rfl⟩ : syracuseStep 5286323 = 7929485) B7929485
theorem B3524215 : Blo 2087435 3524215 := bstep (se 1 (by rfl) ⟨2643161, by rfl⟩ : syracuseStep 3524215 = 5286323) B5286323
theorem B4698953 : Blo 2087435 4698953 := bstep (se 2 (by rfl) ⟨1762107, by rfl⟩ : syracuseStep 4698953 = 3524215) B3524215
theorem B3132635 : Blo 2087435 3132635 := bstep (se 1 (by rfl) ⟨2349476, by rfl⟩ : syracuseStep 3132635 = 4698953) B4698953
theorem B2088423 : Blo 2087435 2088423 := bstep (se 1 (by rfl) ⟨1566317, by rfl⟩ : syracuseStep 2088423 = 3132635) B3132635
theorem B2349481 : Blo 2087435 2349481 := bbase (se 2 (by rfl) ⟨881055, by rfl⟩ : syracuseStep 2349481 = 1762111) (by norm_num)
theorem B3132641 : Blo 2087435 3132641 := bstep (se 2 (by rfl) ⟨1174740, by rfl⟩ : syracuseStep 3132641 = 2349481) B2349481
theorem B2088427 : Blo 2087435 2088427 := bstep (se 1 (by rfl) ⟨1566320, by rfl⟩ : syracuseStep 2088427 = 3132641) B3132641
theorem B5358469 : Blo 2087435 5358469 := bbase (se 4 (by rfl) ⟨502356, by rfl⟩ : syracuseStep 5358469 = 1004713) (by norm_num)
theorem B7144625 : Blo 2087435 7144625 := bstep (se 2 (by rfl) ⟨2679234, by rfl⟩ : syracuseStep 7144625 = 5358469) B5358469
theorem B19052333 : Blo 2087435 19052333 := bstep (se 3 (by rfl) ⟨3572312, by rfl⟩ : syracuseStep 19052333 = 7144625) B7144625
theorem B12701555 : Blo 2087435 12701555 := bstep (se 1 (by rfl) ⟨9526166, by rfl⟩ : syracuseStep 12701555 = 19052333) B19052333
theorem B8467703 : Blo 2087435 8467703 := bstep (se 1 (by rfl) ⟨6350777, by rfl⟩ : syracuseStep 8467703 = 12701555) B12701555
theorem B5645135 : Blo 2087435 5645135 := bstep (se 1 (by rfl) ⟨4233851, by rfl⟩ : syracuseStep 5645135 = 8467703) B8467703
theorem B3763423 : Blo 2087435 3763423 := bstep (se 1 (by rfl) ⟨2822567, by rfl⟩ : syracuseStep 3763423 = 5645135) B5645135
theorem B5017897 : Blo 2087435 5017897 := bstep (se 2 (by rfl) ⟨1881711, by rfl⟩ : syracuseStep 5017897 = 3763423) B3763423
theorem B6690529 : Blo 2087435 6690529 := bstep (se 2 (by rfl) ⟨2508948, by rfl⟩ : syracuseStep 6690529 = 5017897) B5017897
theorem B8920705 : Blo 2087435 8920705 := bstep (se 2 (by rfl) ⟨3345264, by rfl⟩ : syracuseStep 8920705 = 6690529) B6690529
theorem B11894273 : Blo 2087435 11894273 := bstep (se 2 (by rfl) ⟨4460352, by rfl⟩ : syracuseStep 11894273 = 8920705) B8920705
theorem B7929515 : Blo 2087435 7929515 := bstep (se 1 (by rfl) ⟨5947136, by rfl⟩ : syracuseStep 7929515 = 11894273) B11894273
theorem B5286343 : Blo 2087435 5286343 := bstep (se 1 (by rfl) ⟨3964757, by rfl⟩ : syracuseStep 5286343 = 7929515) B7929515
theorem B7048457 : Blo 2087435 7048457 := bstep (se 2 (by rfl) ⟨2643171, by rfl⟩ : syracuseStep 7048457 = 5286343) B5286343
theorem B4698971 : Blo 2087435 4698971 := bstep (se 1 (by rfl) ⟨3524228, by rfl⟩ : syracuseStep 4698971 = 7048457) B7048457
theorem B3132647 : Blo 2087435 3132647 := bstep (se 1 (by rfl) ⟨2349485, by rfl⟩ : syracuseStep 3132647 = 4698971) B4698971
theorem B2088431 : Blo 2087435 2088431 := bstep (se 1 (by rfl) ⟨1566323, by rfl⟩ : syracuseStep 2088431 = 3132647) B3132647
theorem B3132653 : Blo 2087435 3132653 := bbase (se 3 (by rfl) ⟨587372, by rfl⟩ : syracuseStep 3132653 = 1174745) (by norm_num)
theorem B2088435 : Blo 2087435 2088435 := bstep (se 1 (by rfl) ⟨1566326, by rfl⟩ : syracuseStep 2088435 = 3132653) B3132653
theorem B4698989 : Blo 2087435 4698989 := bbase (se 3 (by rfl) ⟨881060, by rfl⟩ : syracuseStep 4698989 = 1762121) (by norm_num)
theorem B3132659 : Blo 2087435 3132659 := bstep (se 1 (by rfl) ⟨2349494, by rfl⟩ : syracuseStep 3132659 = 4698989) B4698989
theorem B2088439 : Blo 2087435 2088439 := bstep (se 1 (by rfl) ⟨1566329, by rfl⟩ : syracuseStep 2088439 = 3132659) B3132659
theorem B3964781 : Blo 2087435 3964781 := bbase (se 3 (by rfl) ⟨743396, by rfl⟩ : syracuseStep 3964781 = 1486793) (by norm_num)
theorem B2643187 : Blo 2087435 2643187 := bstep (se 1 (by rfl) ⟨1982390, by rfl⟩ : syracuseStep 2643187 = 3964781) B3964781
theorem B3524249 : Blo 2087435 3524249 := bstep (se 2 (by rfl) ⟨1321593, by rfl⟩ : syracuseStep 3524249 = 2643187) B2643187
theorem B2349499 : Blo 2087435 2349499 := bstep (se 1 (by rfl) ⟨1762124, by rfl⟩ : syracuseStep 2349499 = 3524249) B3524249
theorem B3132665 : Blo 2087435 3132665 := bstep (se 2 (by rfl) ⟨1174749, by rfl⟩ : syracuseStep 3132665 = 2349499) B2349499
theorem B2088443 : Blo 2087435 2088443 := bstep (se 1 (by rfl) ⟨1566332, by rfl⟩ : syracuseStep 2088443 = 3132665) B3132665
theorem B33871061 : Blo 2087435 33871061 := bbase (se 7 (by rfl) ⟨396926, by rfl⟩ : syracuseStep 33871061 = 793853) (by norm_num)
theorem B22580707 : Blo 2087435 22580707 := bstep (se 1 (by rfl) ⟨16935530, by rfl⟩ : syracuseStep 22580707 = 33871061) B33871061
theorem B30107609 : Blo 2087435 30107609 := bstep (se 2 (by rfl) ⟨11290353, by rfl⟩ : syracuseStep 30107609 = 22580707) B22580707
theorem B20071739 : Blo 2087435 20071739 := bstep (se 1 (by rfl) ⟨15053804, by rfl⟩ : syracuseStep 20071739 = 30107609) B30107609
theorem B53524637 : Blo 2087435 53524637 := bstep (se 3 (by rfl) ⟨10035869, by rfl⟩ : syracuseStep 53524637 = 20071739) B20071739
theorem B35683091 : Blo 2087435 35683091 := bstep (se 1 (by rfl) ⟨26762318, by rfl⟩ : syracuseStep 35683091 = 53524637) B53524637
theorem B23788727 : Blo 2087435 23788727 := bstep (se 1 (by rfl) ⟨17841545, by rfl⟩ : syracuseStep 23788727 = 35683091) B35683091
theorem B15859151 : Blo 2087435 15859151 := bstep (se 1 (by rfl) ⟨11894363, by rfl⟩ : syracuseStep 15859151 = 23788727) B23788727
theorem B10572767 : Blo 2087435 10572767 := bstep (se 1 (by rfl) ⟨7929575, by rfl⟩ : syracuseStep 10572767 = 15859151) B15859151
theorem B7048511 : Blo 2087435 7048511 := bstep (se 1 (by rfl) ⟨5286383, by rfl⟩ : syracuseStep 7048511 = 10572767) B10572767
theorem B4699007 : Blo 2087435 4699007 := bstep (se 1 (by rfl) ⟨3524255, by rfl⟩ : syracuseStep 4699007 = 7048511) B7048511
theorem B3132671 : Blo 2087435 3132671 := bstep (se 1 (by rfl) ⟨2349503, by rfl⟩ : syracuseStep 3132671 = 4699007) B4699007
theorem B2088447 : Blo 2087435 2088447 := bstep (se 1 (by rfl) ⟨1566335, by rfl⟩ : syracuseStep 2088447 = 3132671) B3132671
theorem B3132677 : Blo 2087435 3132677 := bbase (se 4 (by rfl) ⟨293688, by rfl⟩ : syracuseStep 3132677 = 587377) (by norm_num)
theorem B2088451 : Blo 2087435 2088451 := bstep (se 1 (by rfl) ⟨1566338, by rfl⟩ : syracuseStep 2088451 = 3132677) B3132677
theorem B3524269 : Blo 2087435 3524269 := bbase (se 3 (by rfl) ⟨660800, by rfl⟩ : syracuseStep 3524269 = 1321601) (by norm_num)
theorem B4699025 : Blo 2087435 4699025 := bstep (se 2 (by rfl) ⟨1762134, by rfl⟩ : syracuseStep 4699025 = 3524269) B3524269
theorem B3132683 : Blo 2087435 3132683 := bstep (se 1 (by rfl) ⟨2349512, by rfl⟩ : syracuseStep 3132683 = 4699025) B4699025
theorem B2088455 : Blo 2087435 2088455 := bstep (se 1 (by rfl) ⟨1566341, by rfl⟩ : syracuseStep 2088455 = 3132683) B3132683
theorem B2349517 : Blo 2087435 2349517 := bbase (se 3 (by rfl) ⟨440534, by rfl⟩ : syracuseStep 2349517 = 881069) (by norm_num)
theorem B3132689 : Blo 2087435 3132689 := bstep (se 2 (by rfl) ⟨1174758, by rfl⟩ : syracuseStep 3132689 = 2349517) B2349517
theorem B2088459 : Blo 2087435 2088459 := bstep (se 1 (by rfl) ⟨1566344, by rfl⟩ : syracuseStep 2088459 = 3132689) B3132689
theorem B7048565 : Blo 2087435 7048565 := bbase (se 5 (by rfl) ⟨330401, by rfl⟩ : syracuseStep 7048565 = 660803) (by norm_num)
theorem B4699043 : Blo 2087435 4699043 := bstep (se 1 (by rfl) ⟨3524282, by rfl⟩ : syracuseStep 4699043 = 7048565) B7048565
theorem B3132695 : Blo 2087435 3132695 := bstep (se 1 (by rfl) ⟨2349521, by rfl⟩ : syracuseStep 3132695 = 4699043) B4699043
theorem B2088463 : Blo 2087435 2088463 := bstep (se 1 (by rfl) ⟨1566347, by rfl⟩ : syracuseStep 2088463 = 3132695) B3132695
theorem B3132701 : Blo 2087435 3132701 := bbase (se 3 (by rfl) ⟨587381, by rfl⟩ : syracuseStep 3132701 = 1174763) (by norm_num)
theorem B2088467 : Blo 2087435 2088467 := bstep (se 1 (by rfl) ⟨1566350, by rfl⟩ : syracuseStep 2088467 = 3132701) B3132701
theorem B4699061 : Blo 2087435 4699061 := bbase (se 5 (by rfl) ⟨220268, by rfl⟩ : syracuseStep 4699061 = 440537) (by norm_num)
theorem B3132707 : Blo 2087435 3132707 := bstep (se 1 (by rfl) ⟨2349530, by rfl⟩ : syracuseStep 3132707 = 4699061) B4699061
theorem B2088471 : Blo 2087435 2088471 := bstep (se 1 (by rfl) ⟨1566353, by rfl⟩ : syracuseStep 2088471 = 3132707) B3132707
theorem B8583413 : Blo 2087435 8583413 := bbase (se 5 (by rfl) ⟨402347, by rfl⟩ : syracuseStep 8583413 = 804695) (by norm_num)
theorem B22889101 : Blo 2087435 22889101 := bstep (se 3 (by rfl) ⟨4291706, by rfl⟩ : syracuseStep 22889101 = 8583413) B8583413
theorem B30518801 : Blo 2087435 30518801 := bstep (se 2 (by rfl) ⟨11444550, by rfl⟩ : syracuseStep 30518801 = 22889101) B22889101
theorem B20345867 : Blo 2087435 20345867 := bstep (se 1 (by rfl) ⟨15259400, by rfl⟩ : syracuseStep 20345867 = 30518801) B30518801
theorem B13563911 : Blo 2087435 13563911 := bstep (se 1 (by rfl) ⟨10172933, by rfl⟩ : syracuseStep 13563911 = 20345867) B20345867
theorem B9042607 : Blo 2087435 9042607 := bstep (se 1 (by rfl) ⟨6781955, by rfl⟩ : syracuseStep 9042607 = 13563911) B13563911
theorem B48227237 : Blo 2087435 48227237 := bstep (se 4 (by rfl) ⟨4521303, by rfl⟩ : syracuseStep 48227237 = 9042607) B9042607
theorem B32151491 : Blo 2087435 32151491 := bstep (se 1 (by rfl) ⟨24113618, by rfl⟩ : syracuseStep 32151491 = 48227237) B48227237
theorem B21434327 : Blo 2087435 21434327 := bstep (se 1 (by rfl) ⟨16075745, by rfl⟩ : syracuseStep 21434327 = 32151491) B32151491
theorem B14289551 : Blo 2087435 14289551 := bstep (se 1 (by rfl) ⟨10717163, by rfl⟩ : syracuseStep 14289551 = 21434327) B21434327
theorem B9526367 : Blo 2087435 9526367 := bstep (se 1 (by rfl) ⟨7144775, by rfl⟩ : syracuseStep 9526367 = 14289551) B14289551
theorem B25403645 : Blo 2087435 25403645 := bstep (se 3 (by rfl) ⟨4763183, by rfl⟩ : syracuseStep 25403645 = 9526367) B9526367
theorem B16935763 : Blo 2087435 16935763 := bstep (se 1 (by rfl) ⟨12701822, by rfl⟩ : syracuseStep 16935763 = 25403645) B25403645
theorem B22581017 : Blo 2087435 22581017 := bstep (se 2 (by rfl) ⟨8467881, by rfl⟩ : syracuseStep 22581017 = 16935763) B16935763
theorem B15054011 : Blo 2087435 15054011 := bstep (se 1 (by rfl) ⟨11290508, by rfl⟩ : syracuseStep 15054011 = 22581017) B22581017
theorem B10036007 : Blo 2087435 10036007 := bstep (se 1 (by rfl) ⟨7527005, by rfl⟩ : syracuseStep 10036007 = 15054011) B15054011
theorem B6690671 : Blo 2087435 6690671 := bstep (se 1 (by rfl) ⟨5018003, by rfl⟩ : syracuseStep 6690671 = 10036007) B10036007
theorem B4460447 : Blo 2087435 4460447 := bstep (se 1 (by rfl) ⟨3345335, by rfl⟩ : syracuseStep 4460447 = 6690671) B6690671
theorem B11894525 : Blo 2087435 11894525 := bstep (se 3 (by rfl) ⟨2230223, by rfl⟩ : syracuseStep 11894525 = 4460447) B4460447
theorem B7929683 : Blo 2087435 7929683 := bstep (se 1 (by rfl) ⟨5947262, by rfl⟩ : syracuseStep 7929683 = 11894525) B11894525
theorem B5286455 : Blo 2087435 5286455 := bstep (se 1 (by rfl) ⟨3964841, by rfl⟩ : syracuseStep 5286455 = 7929683) B7929683
theorem B3524303 : Blo 2087435 3524303 := bstep (se 1 (by rfl) ⟨2643227, by rfl⟩ : syracuseStep 3524303 = 5286455) B5286455
theorem B2349535 : Blo 2087435 2349535 := bstep (se 1 (by rfl) ⟨1762151, by rfl⟩ : syracuseStep 2349535 = 3524303) B3524303
theorem B3132713 : Blo 2087435 3132713 := bstep (se 2 (by rfl) ⟨1174767, by rfl⟩ : syracuseStep 3132713 = 2349535) B2349535
theorem B2088475 : Blo 2087435 2088475 := bstep (se 1 (by rfl) ⟨1566356, by rfl⟩ : syracuseStep 2088475 = 3132713) B3132713
theorem B7144789 : Blo 2087435 7144789 := bbase (se 12 (by rfl) ⟨2616, by rfl⟩ : syracuseStep 7144789 = 5233) (by norm_num)
theorem B9526385 : Blo 2087435 9526385 := bstep (se 2 (by rfl) ⟨3572394, by rfl⟩ : syracuseStep 9526385 = 7144789) B7144789
theorem B6350923 : Blo 2087435 6350923 := bstep (se 1 (by rfl) ⟨4763192, by rfl⟩ : syracuseStep 6350923 = 9526385) B9526385
theorem B8467897 : Blo 2087435 8467897 := bstep (se 2 (by rfl) ⟨3175461, by rfl⟩ : syracuseStep 8467897 = 6350923) B6350923
theorem B11290529 : Blo 2087435 11290529 := bstep (se 2 (by rfl) ⟨4233948, by rfl⟩ : syracuseStep 11290529 = 8467897) B8467897
theorem B7527019 : Blo 2087435 7527019 := bstep (se 1 (by rfl) ⟨5645264, by rfl⟩ : syracuseStep 7527019 = 11290529) B11290529
theorem B10036025 : Blo 2087435 10036025 := bstep (se 2 (by rfl) ⟨3763509, by rfl⟩ : syracuseStep 10036025 = 7527019) B7527019
theorem B6690683 : Blo 2087435 6690683 := bstep (se 1 (by rfl) ⟨5018012, by rfl⟩ : syracuseStep 6690683 = 10036025) B10036025
theorem B4460455 : Blo 2087435 4460455 := bstep (se 1 (by rfl) ⟨3345341, by rfl⟩ : syracuseStep 4460455 = 6690683) B6690683
theorem B5947273 : Blo 2087435 5947273 := bstep (se 2 (by rfl) ⟨2230227, by rfl⟩ : syracuseStep 5947273 = 4460455) B4460455
theorem B7929697 : Blo 2087435 7929697 := bstep (se 2 (by rfl) ⟨2973636, by rfl⟩ : syracuseStep 7929697 = 5947273) B5947273
theorem B10572929 : Blo 2087435 10572929 := bstep (se 2 (by rfl) ⟨3964848, by rfl⟩ : syracuseStep 10572929 = 7929697) B7929697
theorem B7048619 : Blo 2087435 7048619 := bstep (se 1 (by rfl) ⟨5286464, by rfl⟩ : syracuseStep 7048619 = 10572929) B10572929
theorem B4699079 : Blo 2087435 4699079 := bstep (se 1 (by rfl) ⟨3524309, by rfl⟩ : syracuseStep 4699079 = 7048619) B7048619
theorem B3132719 : Blo 2087435 3132719 := bstep (se 1 (by rfl) ⟨2349539, by rfl⟩ : syracuseStep 3132719 = 4699079) B4699079
theorem B2088479 : Blo 2087435 2088479 := bstep (se 1 (by rfl) ⟨1566359, by rfl⟩ : syracuseStep 2088479 = 3132719) B3132719
theorem B3132725 : Blo 2087435 3132725 := bbase (se 5 (by rfl) ⟨146846, by rfl⟩ : syracuseStep 3132725 = 293693) (by norm_num)
theorem B2088483 : Blo 2087435 2088483 := bstep (se 1 (by rfl) ⟨1566362, by rfl⟩ : syracuseStep 2088483 = 3132725) B3132725
theorem B5286485 : Blo 2087435 5286485 := bbase (se 8 (by rfl) ⟨30975, by rfl⟩ : syracuseStep 5286485 = 61951) (by norm_num)
theorem B3524323 : Blo 2087435 3524323 := bstep (se 1 (by rfl) ⟨2643242, by rfl⟩ : syracuseStep 3524323 = 5286485) B5286485
theorem B4699097 : Blo 2087435 4699097 := bstep (se 2 (by rfl) ⟨1762161, by rfl⟩ : syracuseStep 4699097 = 3524323) B3524323
theorem B3132731 : Blo 2087435 3132731 := bstep (se 1 (by rfl) ⟨2349548, by rfl⟩ : syracuseStep 3132731 = 4699097) B4699097
theorem B2088487 : Blo 2087435 2088487 := bstep (se 1 (by rfl) ⟨1566365, by rfl⟩ : syracuseStep 2088487 = 3132731) B3132731
theorem B2349553 : Blo 2087435 2349553 := bbase (se 2 (by rfl) ⟨881082, by rfl⟩ : syracuseStep 2349553 = 1762165) (by norm_num)
theorem B3132737 : Blo 2087435 3132737 := bstep (se 2 (by rfl) ⟨1174776, by rfl⟩ : syracuseStep 3132737 = 2349553) B2349553
theorem B2088491 : Blo 2087435 2088491 := bstep (se 1 (by rfl) ⟨1566368, by rfl⟩ : syracuseStep 2088491 = 3132737) B3132737
theorem B7527077 : Blo 2087435 7527077 := bbase (se 4 (by rfl) ⟨705663, by rfl⟩ : syracuseStep 7527077 = 1411327) (by norm_num)
theorem B5018051 : Blo 2087435 5018051 := bstep (se 1 (by rfl) ⟨3763538, by rfl⟩ : syracuseStep 5018051 = 7527077) B7527077
theorem B13381469 : Blo 2087435 13381469 := bstep (se 3 (by rfl) ⟨2509025, by rfl⟩ : syracuseStep 13381469 = 5018051) B5018051
theorem B8920979 : Blo 2087435 8920979 := bstep (se 1 (by rfl) ⟨6690734, by rfl⟩ : syracuseStep 8920979 = 13381469) B13381469
theorem B5947319 : Blo 2087435 5947319 := bstep (se 1 (by rfl) ⟨4460489, by rfl⟩ : syracuseStep 5947319 = 8920979) B8920979
theorem B3964879 : Blo 2087435 3964879 := bstep (se 1 (by rfl) ⟨2973659, by rfl⟩ : syracuseStep 3964879 = 5947319) B5947319
theorem B5286505 : Blo 2087435 5286505 := bstep (se 2 (by rfl) ⟨1982439, by rfl⟩ : syracuseStep 5286505 = 3964879) B3964879
theorem B7048673 : Blo 2087435 7048673 := bstep (se 2 (by rfl) ⟨2643252, by rfl⟩ : syracuseStep 7048673 = 5286505) B5286505
theorem B4699115 : Blo 2087435 4699115 := bstep (se 1 (by rfl) ⟨3524336, by rfl⟩ : syracuseStep 4699115 = 7048673) B7048673
theorem B3132743 : Blo 2087435 3132743 := bstep (se 1 (by rfl) ⟨2349557, by rfl⟩ : syracuseStep 3132743 = 4699115) B4699115
theorem B2088495 : Blo 2087435 2088495 := bstep (se 1 (by rfl) ⟨1566371, by rfl⟩ : syracuseStep 2088495 = 3132743) B3132743
theorem B3132749 : Blo 2087435 3132749 := bbase (se 3 (by rfl) ⟨587390, by rfl⟩ : syracuseStep 3132749 = 1174781) (by norm_num)
theorem B2088499 : Blo 2087435 2088499 := bstep (se 1 (by rfl) ⟨1566374, by rfl⟩ : syracuseStep 2088499 = 3132749) B3132749
theorem B4699133 : Blo 2087435 4699133 := bbase (se 3 (by rfl) ⟨881087, by rfl⟩ : syracuseStep 4699133 = 1762175) (by norm_num)
theorem B3132755 : Blo 2087435 3132755 := bstep (se 1 (by rfl) ⟨2349566, by rfl⟩ : syracuseStep 3132755 = 4699133) B4699133
theorem B2088503 : Blo 2087435 2088503 := bstep (se 1 (by rfl) ⟨1566377, by rfl⟩ : syracuseStep 2088503 = 3132755) B3132755
theorem B3524357 : Blo 2087435 3524357 := bbase (se 4 (by rfl) ⟨330408, by rfl⟩ : syracuseStep 3524357 = 660817) (by norm_num)
theorem B2349571 : Blo 2087435 2349571 := bstep (se 1 (by rfl) ⟨1762178, by rfl⟩ : syracuseStep 2349571 = 3524357) B3524357
theorem B3132761 : Blo 2087435 3132761 := bstep (se 2 (by rfl) ⟨1174785, by rfl⟩ : syracuseStep 3132761 = 2349571) B2349571
theorem B2088507 : Blo 2087435 2088507 := bstep (se 1 (by rfl) ⟨1566380, by rfl⟩ : syracuseStep 2088507 = 3132761) B3132761
theorem B15859637 : Blo 2087435 15859637 := bbase (se 5 (by rfl) ⟨743420, by rfl⟩ : syracuseStep 15859637 = 1486841) (by norm_num)
theorem B10573091 : Blo 2087435 10573091 := bstep (se 1 (by rfl) ⟨7929818, by rfl⟩ : syracuseStep 10573091 = 15859637) B15859637
theorem B7048727 : Blo 2087435 7048727 := bstep (se 1 (by rfl) ⟨5286545, by rfl⟩ : syracuseStep 7048727 = 10573091) B10573091
theorem B4699151 : Blo 2087435 4699151 := bstep (se 1 (by rfl) ⟨3524363, by rfl⟩ : syracuseStep 4699151 = 7048727) B7048727
theorem B3132767 : Blo 2087435 3132767 := bstep (se 1 (by rfl) ⟨2349575, by rfl⟩ : syracuseStep 3132767 = 4699151) B4699151
theorem B2088511 : Blo 2087435 2088511 := bstep (se 1 (by rfl) ⟨1566383, by rfl⟩ : syracuseStep 2088511 = 3132767) B3132767
theorem B3132773 : Blo 2087435 3132773 := bbase (se 4 (by rfl) ⟨293697, by rfl⟩ : syracuseStep 3132773 = 587395) (by norm_num)
theorem B2088515 : Blo 2087435 2088515 := bstep (se 1 (by rfl) ⟨1566386, by rfl⟩ : syracuseStep 2088515 = 3132773) B3132773
theorem B3964925 : Blo 2087435 3964925 := bbase (se 3 (by rfl) ⟨743423, by rfl⟩ : syracuseStep 3964925 = 1486847) (by norm_num)
theorem B2643283 : Blo 2087435 2643283 := bstep (se 1 (by rfl) ⟨1982462, by rfl⟩ : syracuseStep 2643283 = 3964925) B3964925
theorem B3524377 : Blo 2087435 3524377 := bstep (se 2 (by rfl) ⟨1321641, by rfl⟩ : syracuseStep 3524377 = 2643283) B2643283
theorem B4699169 : Blo 2087435 4699169 := bstep (se 2 (by rfl) ⟨1762188, by rfl⟩ : syracuseStep 4699169 = 3524377) B3524377
theorem B3132779 : Blo 2087435 3132779 := bstep (se 1 (by rfl) ⟨2349584, by rfl⟩ : syracuseStep 3132779 = 4699169) B4699169
theorem B2088519 : Blo 2087435 2088519 := bstep (se 1 (by rfl) ⟨1566389, by rfl⟩ : syracuseStep 2088519 = 3132779) B3132779
theorem B2349589 : Blo 2087435 2349589 := bbase (se 6 (by rfl) ⟨55068, by rfl⟩ : syracuseStep 2349589 = 110137) (by norm_num)
theorem B3132785 : Blo 2087435 3132785 := bstep (se 2 (by rfl) ⟨1174794, by rfl⟩ : syracuseStep 3132785 = 2349589) B2349589
theorem B2088523 : Blo 2087435 2088523 := bstep (se 1 (by rfl) ⟨1566392, by rfl⟩ : syracuseStep 2088523 = 3132785) B3132785
theorem B2643293 : Blo 2087435 2643293 := bbase (se 3 (by rfl) ⟨495617, by rfl⟩ : syracuseStep 2643293 = 991235) (by norm_num)
theorem B7048781 : Blo 2087435 7048781 := bstep (se 3 (by rfl) ⟨1321646, by rfl⟩ : syracuseStep 7048781 = 2643293) B2643293
theorem B4699187 : Blo 2087435 4699187 := bstep (se 1 (by rfl) ⟨3524390, by rfl⟩ : syracuseStep 4699187 = 7048781) B7048781
theorem B3132791 : Blo 2087435 3132791 := bstep (se 1 (by rfl) ⟨2349593, by rfl⟩ : syracuseStep 3132791 = 4699187) B4699187
theorem B2088527 : Blo 2087435 2088527 := bstep (se 1 (by rfl) ⟨1566395, by rfl⟩ : syracuseStep 2088527 = 3132791) B3132791
theorem B3132797 : Blo 2087435 3132797 := bbase (se 3 (by rfl) ⟨587399, by rfl⟩ : syracuseStep 3132797 = 1174799) (by norm_num)
theorem B2088531 : Blo 2087435 2088531 := bstep (se 1 (by rfl) ⟨1566398, by rfl⟩ : syracuseStep 2088531 = 3132797) B3132797
theorem B4699205 : Blo 2087435 4699205 := bbase (se 4 (by rfl) ⟨440550, by rfl⟩ : syracuseStep 4699205 = 881101) (by norm_num)
theorem B3132803 : Blo 2087435 3132803 := bstep (se 1 (by rfl) ⟨2349602, by rfl⟩ : syracuseStep 3132803 = 4699205) B4699205
theorem B2088535 : Blo 2087435 2088535 := bstep (se 1 (by rfl) ⟨1566401, by rfl⟩ : syracuseStep 2088535 = 3132803) B3132803
theorem B5947445 : Blo 2087435 5947445 := bbase (se 5 (by rfl) ⟨278786, by rfl⟩ : syracuseStep 5947445 = 557573) (by norm_num)
theorem B3964963 : Blo 2087435 3964963 := bstep (se 1 (by rfl) ⟨2973722, by rfl⟩ : syracuseStep 3964963 = 5947445) B5947445
theorem B5286617 : Blo 2087435 5286617 := bstep (se 2 (by rfl) ⟨1982481, by rfl⟩ : syracuseStep 5286617 = 3964963) B3964963
theorem B3524411 : Blo 2087435 3524411 := bstep (se 1 (by rfl) ⟨2643308, by rfl⟩ : syracuseStep 3524411 = 5286617) B5286617
theorem B2349607 : Blo 2087435 2349607 := bstep (se 1 (by rfl) ⟨1762205, by rfl⟩ : syracuseStep 2349607 = 3524411) B3524411
theorem B3132809 : Blo 2087435 3132809 := bstep (se 2 (by rfl) ⟨1174803, by rfl⟩ : syracuseStep 3132809 = 2349607) B2349607
theorem B2088539 : Blo 2087435 2088539 := bstep (se 1 (by rfl) ⟨1566404, by rfl⟩ : syracuseStep 2088539 = 3132809) B3132809
theorem B10573253 : Blo 2087435 10573253 := bbase (se 4 (by rfl) ⟨991242, by rfl⟩ : syracuseStep 10573253 = 1982485) (by norm_num)
theorem B7048835 : Blo 2087435 7048835 := bstep (se 1 (by rfl) ⟨5286626, by rfl⟩ : syracuseStep 7048835 = 10573253) B10573253
theorem B4699223 : Blo 2087435 4699223 := bstep (se 1 (by rfl) ⟨3524417, by rfl⟩ : syracuseStep 4699223 = 7048835) B7048835
theorem B3132815 : Blo 2087435 3132815 := bstep (se 1 (by rfl) ⟨2349611, by rfl⟩ : syracuseStep 3132815 = 4699223) B4699223
theorem B2088543 : Blo 2087435 2088543 := bstep (se 1 (by rfl) ⟨1566407, by rfl⟩ : syracuseStep 2088543 = 3132815) B3132815
theorem B3132821 : Blo 2087435 3132821 := bbase (se 6 (by rfl) ⟨73425, by rfl⟩ : syracuseStep 3132821 = 146851) (by norm_num)
theorem B2088547 : Blo 2087435 2088547 := bstep (se 1 (by rfl) ⟨1566410, by rfl⟩ : syracuseStep 2088547 = 3132821) B3132821
theorem B2509093 : Blo 2087435 2509093 := bbase (se 4 (by rfl) ⟨235227, by rfl⟩ : syracuseStep 2509093 = 470455) (by norm_num)
theorem B3345457 : Blo 2087435 3345457 := bstep (se 2 (by rfl) ⟨1254546, by rfl⟩ : syracuseStep 3345457 = 2509093) B2509093
theorem B4460609 : Blo 2087435 4460609 := bstep (se 2 (by rfl) ⟨1672728, by rfl⟩ : syracuseStep 4460609 = 3345457) B3345457
theorem B11894957 : Blo 2087435 11894957 := bstep (se 3 (by rfl) ⟨2230304, by rfl⟩ : syracuseStep 11894957 = 4460609) B4460609
theorem B7929971 : Blo 2087435 7929971 := bstep (se 1 (by rfl) ⟨5947478, by rfl⟩ : syracuseStep 7929971 = 11894957) B11894957
theorem B5286647 : Blo 2087435 5286647 := bstep (se 1 (by rfl) ⟨3964985, by rfl⟩ : syracuseStep 5286647 = 7929971) B7929971
theorem B3524431 : Blo 2087435 3524431 := bstep (se 1 (by rfl) ⟨2643323, by rfl⟩ : syracuseStep 3524431 = 5286647) B5286647
theorem B4699241 : Blo 2087435 4699241 := bstep (se 2 (by rfl) ⟨1762215, by rfl⟩ : syracuseStep 4699241 = 3524431) B3524431
theorem B3132827 : Blo 2087435 3132827 := bstep (se 1 (by rfl) ⟨2349620, by rfl⟩ : syracuseStep 3132827 = 4699241) B4699241
theorem B2088551 : Blo 2087435 2088551 := bstep (se 1 (by rfl) ⟨1566413, by rfl⟩ : syracuseStep 2088551 = 3132827) B3132827
theorem B2349625 : Blo 2087435 2349625 := bbase (se 2 (by rfl) ⟨881109, by rfl⟩ : syracuseStep 2349625 = 1762219) (by norm_num)
theorem B3132833 : Blo 2087435 3132833 := bstep (se 2 (by rfl) ⟨1174812, by rfl⟩ : syracuseStep 3132833 = 2349625) B2349625
theorem B2088555 : Blo 2087435 2088555 := bstep (se 1 (by rfl) ⟨1566416, by rfl⟩ : syracuseStep 2088555 = 3132833) B3132833
theorem B2230313 : Blo 2087435 2230313 := bbase (se 2 (by rfl) ⟨836367, by rfl⟩ : syracuseStep 2230313 = 1672735) (by norm_num)
theorem B5947501 : Blo 2087435 5947501 := bstep (se 3 (by rfl) ⟨1115156, by rfl⟩ : syracuseStep 5947501 = 2230313) B2230313
theorem B7930001 : Blo 2087435 7930001 := bstep (se 2 (by rfl) ⟨2973750, by rfl⟩ : syracuseStep 7930001 = 5947501) B5947501
theorem B5286667 : Blo 2087435 5286667 := bstep (se 1 (by rfl) ⟨3965000, by rfl⟩ : syracuseStep 5286667 = 7930001) B7930001
theorem B7048889 : Blo 2087435 7048889 := bstep (se 2 (by rfl) ⟨2643333, by rfl⟩ : syracuseStep 7048889 = 5286667) B5286667
theorem B4699259 : Blo 2087435 4699259 := bstep (se 1 (by rfl) ⟨3524444, by rfl⟩ : syracuseStep 4699259 = 7048889) B7048889
theorem B3132839 : Blo 2087435 3132839 := bstep (se 1 (by rfl) ⟨2349629, by rfl⟩ : syracuseStep 3132839 = 4699259) B4699259
theorem B2088559 : Blo 2087435 2088559 := bstep (se 1 (by rfl) ⟨1566419, by rfl⟩ : syracuseStep 2088559 = 3132839) B3132839
theorem B3132845 : Blo 2087435 3132845 := bbase (se 3 (by rfl) ⟨587408, by rfl⟩ : syracuseStep 3132845 = 1174817) (by norm_num)
theorem B2088563 : Blo 2087435 2088563 := bstep (se 1 (by rfl) ⟨1566422, by rfl⟩ : syracuseStep 2088563 = 3132845) B3132845
theorem B4699277 : Blo 2087435 4699277 := bbase (se 3 (by rfl) ⟨881114, by rfl⟩ : syracuseStep 4699277 = 1762229) (by norm_num)
theorem B3132851 : Blo 2087435 3132851 := bstep (se 1 (by rfl) ⟨2349638, by rfl⟩ : syracuseStep 3132851 = 4699277) B4699277
theorem B2088567 : Blo 2087435 2088567 := bstep (se 1 (by rfl) ⟨1566425, by rfl⟩ : syracuseStep 2088567 = 3132851) B3132851
theorem B2643349 : Blo 2087435 2643349 := bbase (se 6 (by rfl) ⟨61953, by rfl⟩ : syracuseStep 2643349 = 123907) (by norm_num)
theorem B3524465 : Blo 2087435 3524465 := bstep (se 2 (by rfl) ⟨1321674, by rfl⟩ : syracuseStep 3524465 = 2643349) B2643349
theorem B2349643 : Blo 2087435 2349643 := bstep (se 1 (by rfl) ⟨1762232, by rfl⟩ : syracuseStep 2349643 = 3524465) B3524465
theorem B3132857 : Blo 2087435 3132857 := bstep (se 2 (by rfl) ⟨1174821, by rfl⟩ : syracuseStep 3132857 = 2349643) B2349643
theorem B2088571 : Blo 2087435 2088571 := bstep (se 1 (by rfl) ⟨1566428, by rfl⟩ : syracuseStep 2088571 = 3132857) B3132857
theorem B2381705 : Blo 2087435 2381705 := bbase (se 2 (by rfl) ⟨893139, by rfl⟩ : syracuseStep 2381705 = 1786279) (by norm_num)
theorem B25404853 : Blo 2087435 25404853 := bstep (se 5 (by rfl) ⟨1190852, by rfl⟩ : syracuseStep 25404853 = 2381705) B2381705
theorem B33873137 : Blo 2087435 33873137 := bstep (se 2 (by rfl) ⟨12702426, by rfl⟩ : syracuseStep 33873137 = 25404853) B25404853
theorem B22582091 : Blo 2087435 22582091 := bstep (se 1 (by rfl) ⟨16936568, by rfl⟩ : syracuseStep 22582091 = 33873137) B33873137
theorem B60218909 : Blo 2087435 60218909 := bstep (se 3 (by rfl) ⟨11291045, by rfl⟩ : syracuseStep 60218909 = 22582091) B22582091
theorem B40145939 : Blo 2087435 40145939 := bstep (se 1 (by rfl) ⟨30109454, by rfl⟩ : syracuseStep 40145939 = 60218909) B60218909
theorem B26763959 : Blo 2087435 26763959 := bstep (se 1 (by rfl) ⟨20072969, by rfl⟩ : syracuseStep 26763959 = 40145939) B40145939
theorem B17842639 : Blo 2087435 17842639 := bstep (se 1 (by rfl) ⟨13381979, by rfl⟩ : syracuseStep 17842639 = 26763959) B26763959
theorem B23790185 : Blo 2087435 23790185 := bstep (se 2 (by rfl) ⟨8921319, by rfl⟩ : syracuseStep 23790185 = 17842639) B17842639
theorem B15860123 : Blo 2087435 15860123 := bstep (se 1 (by rfl) ⟨11895092, by rfl⟩ : syracuseStep 15860123 = 23790185) B23790185
theorem B10573415 : Blo 2087435 10573415 := bstep (se 1 (by rfl) ⟨7930061, by rfl⟩ : syracuseStep 10573415 = 15860123) B15860123
theorem B7048943 : Blo 2087435 7048943 := bstep (se 1 (by rfl) ⟨5286707, by rfl⟩ : syracuseStep 7048943 = 10573415) B10573415
theorem B4699295 : Blo 2087435 4699295 := bstep (se 1 (by rfl) ⟨3524471, by rfl⟩ : syracuseStep 4699295 = 7048943) B7048943
theorem B3132863 : Blo 2087435 3132863 := bstep (se 1 (by rfl) ⟨2349647, by rfl⟩ : syracuseStep 3132863 = 4699295) B4699295
theorem B2088575 : Blo 2087435 2088575 := bstep (se 1 (by rfl) ⟨1566431, by rfl⟩ : syracuseStep 2088575 = 3132863) B3132863
theorem B3132869 : Blo 2087435 3132869 := bbase (se 4 (by rfl) ⟨293706, by rfl⟩ : syracuseStep 3132869 = 587413) (by norm_num)
theorem B2088579 : Blo 2087435 2088579 := bstep (se 1 (by rfl) ⟨1566434, by rfl⟩ : syracuseStep 2088579 = 3132869) B3132869
theorem B3524485 : Blo 2087435 3524485 := bbase (se 4 (by rfl) ⟨330420, by rfl⟩ : syracuseStep 3524485 = 660841) (by norm_num)
theorem B4699313 : Blo 2087435 4699313 := bstep (se 2 (by rfl) ⟨1762242, by rfl⟩ : syracuseStep 4699313 = 3524485) B3524485
theorem B3132875 : Blo 2087435 3132875 := bstep (se 1 (by rfl) ⟨2349656, by rfl⟩ : syracuseStep 3132875 = 4699313) B4699313
theorem B2088583 : Blo 2087435 2088583 := bstep (se 1 (by rfl) ⟨1566437, by rfl⟩ : syracuseStep 2088583 = 3132875) B3132875
theorem B2349661 : Blo 2087435 2349661 := bbase (se 3 (by rfl) ⟨440561, by rfl⟩ : syracuseStep 2349661 = 881123) (by norm_num)
theorem B3132881 : Blo 2087435 3132881 := bstep (se 2 (by rfl) ⟨1174830, by rfl⟩ : syracuseStep 3132881 = 2349661) B2349661
theorem B2088587 : Blo 2087435 2088587 := bstep (se 1 (by rfl) ⟨1566440, by rfl⟩ : syracuseStep 2088587 = 3132881) B3132881
theorem B7048997 : Blo 2087435 7048997 := bbase (se 4 (by rfl) ⟨660843, by rfl⟩ : syracuseStep 7048997 = 1321687) (by norm_num)
theorem B4699331 : Blo 2087435 4699331 := bstep (se 1 (by rfl) ⟨3524498, by rfl⟩ : syracuseStep 4699331 = 7048997) B7048997
theorem B3132887 : Blo 2087435 3132887 := bstep (se 1 (by rfl) ⟨2349665, by rfl⟩ : syracuseStep 3132887 = 4699331) B4699331
theorem B2088591 : Blo 2087435 2088591 := bstep (se 1 (by rfl) ⟨1566443, by rfl⟩ : syracuseStep 2088591 = 3132887) B3132887
theorem B3132893 : Blo 2087435 3132893 := bbase (se 3 (by rfl) ⟨587417, by rfl⟩ : syracuseStep 3132893 = 1174835) (by norm_num)
theorem B2088595 : Blo 2087435 2088595 := bstep (se 1 (by rfl) ⟨1566446, by rfl⟩ : syracuseStep 2088595 = 3132893) B3132893
theorem B4699349 : Blo 2087435 4699349 := bbase (se 7 (by rfl) ⟨55070, by rfl⟩ : syracuseStep 4699349 = 110141) (by norm_num)
theorem B3132899 : Blo 2087435 3132899 := bstep (se 1 (by rfl) ⟨2349674, by rfl⟩ : syracuseStep 3132899 = 4699349) B4699349
theorem B2088599 : Blo 2087435 2088599 := bstep (se 1 (by rfl) ⟨1566449, by rfl⟩ : syracuseStep 2088599 = 3132899) B3132899
theorem B6351301 : Blo 2087435 6351301 := bbase (se 4 (by rfl) ⟨595434, by rfl⟩ : syracuseStep 6351301 = 1190869) (by norm_num)
theorem B8468401 : Blo 2087435 8468401 := bstep (se 2 (by rfl) ⟨3175650, by rfl⟩ : syracuseStep 8468401 = 6351301) B6351301
theorem B11291201 : Blo 2087435 11291201 := bstep (se 2 (by rfl) ⟨4234200, by rfl⟩ : syracuseStep 11291201 = 8468401) B8468401
theorem B7527467 : Blo 2087435 7527467 := bstep (se 1 (by rfl) ⟨5645600, by rfl⟩ : syracuseStep 7527467 = 11291201) B11291201
theorem B5018311 : Blo 2087435 5018311 := bstep (se 1 (by rfl) ⟨3763733, by rfl⟩ : syracuseStep 5018311 = 7527467) B7527467
theorem B6691081 : Blo 2087435 6691081 := bstep (se 2 (by rfl) ⟨2509155, by rfl⟩ : syracuseStep 6691081 = 5018311) B5018311
theorem B8921441 : Blo 2087435 8921441 := bstep (se 2 (by rfl) ⟨3345540, by rfl⟩ : syracuseStep 8921441 = 6691081) B6691081
theorem B5947627 : Blo 2087435 5947627 := bstep (se 1 (by rfl) ⟨4460720, by rfl⟩ : syracuseStep 5947627 = 8921441) B8921441
theorem B7930169 : Blo 2087435 7930169 := bstep (se 2 (by rfl) ⟨2973813, by rfl⟩ : syracuseStep 7930169 = 5947627) B5947627
theorem B5286779 : Blo 2087435 5286779 := bstep (se 1 (by rfl) ⟨3965084, by rfl⟩ : syracuseStep 5286779 = 7930169) B7930169
theorem B3524519 : Blo 2087435 3524519 := bstep (se 1 (by rfl) ⟨2643389, by rfl⟩ : syracuseStep 3524519 = 5286779) B5286779
theorem B2349679 : Blo 2087435 2349679 := bstep (se 1 (by rfl) ⟨1762259, by rfl⟩ : syracuseStep 2349679 = 3524519) B3524519
theorem B3132905 : Blo 2087435 3132905 := bstep (se 2 (by rfl) ⟨1174839, by rfl⟩ : syracuseStep 3132905 = 2349679) B2349679
theorem B2088603 : Blo 2087435 2088603 := bstep (se 1 (by rfl) ⟨1566452, by rfl⟩ : syracuseStep 2088603 = 3132905) B3132905
theorem B2613269 : Blo 2087435 2613269 := bbase (se 6 (by rfl) ⟨61248, by rfl⟩ : syracuseStep 2613269 = 122497) (by norm_num)
theorem B6968717 : Blo 2087435 6968717 := bstep (se 3 (by rfl) ⟨1306634, by rfl⟩ : syracuseStep 6968717 = 2613269) B2613269
theorem B4645811 : Blo 2087435 4645811 := bstep (se 1 (by rfl) ⟨3484358, by rfl⟩ : syracuseStep 4645811 = 6968717) B6968717
theorem B3097207 : Blo 2087435 3097207 := bstep (se 1 (by rfl) ⟨2322905, by rfl⟩ : syracuseStep 3097207 = 4645811) B4645811
theorem B4129609 : Blo 2087435 4129609 := bstep (se 2 (by rfl) ⟨1548603, by rfl⟩ : syracuseStep 4129609 = 3097207) B3097207
theorem B5506145 : Blo 2087435 5506145 := bstep (se 2 (by rfl) ⟨2064804, by rfl⟩ : syracuseStep 5506145 = 4129609) B4129609
theorem B3670763 : Blo 2087435 3670763 := bstep (se 1 (by rfl) ⟨2753072, by rfl⟩ : syracuseStep 3670763 = 5506145) B5506145
theorem B9788701 : Blo 2087435 9788701 := bstep (se 3 (by rfl) ⟨1835381, by rfl⟩ : syracuseStep 9788701 = 3670763) B3670763
theorem B13051601 : Blo 2087435 13051601 := bstep (se 2 (by rfl) ⟨4894350, by rfl⟩ : syracuseStep 13051601 = 9788701) B9788701
theorem B8701067 : Blo 2087435 8701067 := bstep (se 1 (by rfl) ⟨6525800, by rfl⟩ : syracuseStep 8701067 = 13051601) B13051601
theorem B23202845 : Blo 2087435 23202845 := bstep (se 3 (by rfl) ⟨4350533, by rfl⟩ : syracuseStep 23202845 = 8701067) B8701067
theorem B15468563 : Blo 2087435 15468563 := bstep (se 1 (by rfl) ⟨11601422, by rfl⟩ : syracuseStep 15468563 = 23202845) B23202845
theorem B10312375 : Blo 2087435 10312375 := bstep (se 1 (by rfl) ⟨7734281, by rfl⟩ : syracuseStep 10312375 = 15468563) B15468563
theorem B13749833 : Blo 2087435 13749833 := bstep (se 2 (by rfl) ⟨5156187, by rfl⟩ : syracuseStep 13749833 = 10312375) B10312375
theorem B9166555 : Blo 2087435 9166555 := bstep (se 1 (by rfl) ⟨6874916, by rfl⟩ : syracuseStep 9166555 = 13749833) B13749833
theorem B12222073 : Blo 2087435 12222073 := bstep (se 2 (by rfl) ⟨4583277, by rfl⟩ : syracuseStep 12222073 = 9166555) B9166555
theorem B65184389 : Blo 2087435 65184389 := bstep (se 4 (by rfl) ⟨6111036, by rfl⟩ : syracuseStep 65184389 = 12222073) B12222073
theorem B43456259 : Blo 2087435 43456259 := bstep (se 1 (by rfl) ⟨32592194, by rfl⟩ : syracuseStep 43456259 = 65184389) B65184389
theorem B28970839 : Blo 2087435 28970839 := bstep (se 1 (by rfl) ⟨21728129, by rfl⟩ : syracuseStep 28970839 = 43456259) B43456259
theorem B38627785 : Blo 2087435 38627785 := bstep (se 2 (by rfl) ⟨14485419, by rfl⟩ : syracuseStep 38627785 = 28970839) B28970839
theorem B206014853 : Blo 2087435 206014853 := bstep (se 4 (by rfl) ⟨19313892, by rfl⟩ : syracuseStep 206014853 = 38627785) B38627785
theorem B137343235 : Blo 2087435 137343235 := bstep (se 1 (by rfl) ⟨103007426, by rfl⟩ : syracuseStep 137343235 = 206014853) B206014853
theorem B183124313 : Blo 2087435 183124313 := bstep (se 2 (by rfl) ⟨68671617, by rfl⟩ : syracuseStep 183124313 = 137343235) B137343235
theorem B122082875 : Blo 2087435 122082875 := bstep (se 1 (by rfl) ⟨91562156, by rfl⟩ : syracuseStep 122082875 = 183124313) B183124313
theorem B81388583 : Blo 2087435 81388583 := bstep (se 1 (by rfl) ⟨61041437, by rfl⟩ : syracuseStep 81388583 = 122082875) B122082875
theorem B54259055 : Blo 2087435 54259055 := bstep (se 1 (by rfl) ⟨40694291, by rfl⟩ : syracuseStep 54259055 = 81388583) B81388583
theorem B36172703 : Blo 2087435 36172703 := bstep (se 1 (by rfl) ⟨27129527, by rfl⟩ : syracuseStep 36172703 = 54259055) B54259055
theorem B96460541 : Blo 2087435 96460541 := bstep (se 3 (by rfl) ⟨18086351, by rfl⟩ : syracuseStep 96460541 = 36172703) B36172703
theorem B64307027 : Blo 2087435 64307027 := bstep (se 1 (by rfl) ⟨48230270, by rfl⟩ : syracuseStep 64307027 = 96460541) B96460541
theorem B42871351 : Blo 2087435 42871351 := bstep (se 1 (by rfl) ⟨32153513, by rfl⟩ : syracuseStep 42871351 = 64307027) B64307027
theorem B57161801 : Blo 2087435 57161801 := bstep (se 2 (by rfl) ⟨21435675, by rfl⟩ : syracuseStep 57161801 = 42871351) B42871351
theorem B38107867 : Blo 2087435 38107867 := bstep (se 1 (by rfl) ⟨28580900, by rfl⟩ : syracuseStep 38107867 = 57161801) B57161801
theorem B50810489 : Blo 2087435 50810489 := bstep (se 2 (by rfl) ⟨19053933, by rfl⟩ : syracuseStep 50810489 = 38107867) B38107867
theorem B33873659 : Blo 2087435 33873659 := bstep (se 1 (by rfl) ⟨25405244, by rfl⟩ : syracuseStep 33873659 = 50810489) B50810489
theorem B22582439 : Blo 2087435 22582439 := bstep (se 1 (by rfl) ⟨16936829, by rfl⟩ : syracuseStep 22582439 = 33873659) B33873659
theorem B15054959 : Blo 2087435 15054959 := bstep (se 1 (by rfl) ⟨11291219, by rfl⟩ : syracuseStep 15054959 = 22582439) B22582439
theorem B10036639 : Blo 2087435 10036639 := bstep (se 1 (by rfl) ⟨7527479, by rfl⟩ : syracuseStep 10036639 = 15054959) B15054959
theorem B13382185 : Blo 2087435 13382185 := bstep (se 2 (by rfl) ⟨5018319, by rfl⟩ : syracuseStep 13382185 = 10036639) B10036639
theorem B17842913 : Blo 2087435 17842913 := bstep (se 2 (by rfl) ⟨6691092, by rfl⟩ : syracuseStep 17842913 = 13382185) B13382185
theorem B11895275 : Blo 2087435 11895275 := bstep (se 1 (by rfl) ⟨8921456, by rfl⟩ : syracuseStep 11895275 = 17842913) B17842913
theorem B7930183 : Blo 2087435 7930183 := bstep (se 1 (by rfl) ⟨5947637, by rfl⟩ : syracuseStep 7930183 = 11895275) B11895275
theorem B10573577 : Blo 2087435 10573577 := bstep (se 2 (by rfl) ⟨3965091, by rfl⟩ : syracuseStep 10573577 = 7930183) B7930183
theorem B7049051 : Blo 2087435 7049051 := bstep (se 1 (by rfl) ⟨5286788, by rfl⟩ : syracuseStep 7049051 = 10573577) B10573577
theorem B4699367 : Blo 2087435 4699367 := bstep (se 1 (by rfl) ⟨3524525, by rfl⟩ : syracuseStep 4699367 = 7049051) B7049051
theorem B3132911 : Blo 2087435 3132911 := bstep (se 1 (by rfl) ⟨2349683, by rfl⟩ : syracuseStep 3132911 = 4699367) B4699367
theorem B2088607 : Blo 2087435 2088607 := bstep (se 1 (by rfl) ⟨1566455, by rfl⟩ : syracuseStep 2088607 = 3132911) B3132911
theorem B3132917 : Blo 2087435 3132917 := bbase (se 5 (by rfl) ⟨146855, by rfl⟩ : syracuseStep 3132917 = 293711) (by norm_num)
theorem B2088611 : Blo 2087435 2088611 := bstep (se 1 (by rfl) ⟨1566458, by rfl⟩ : syracuseStep 2088611 = 3132917) B3132917
theorem B2230373 : Blo 2087435 2230373 := bbase (se 4 (by rfl) ⟨209097, by rfl⟩ : syracuseStep 2230373 = 418195) (by norm_num)
theorem B5947661 : Blo 2087435 5947661 := bstep (se 3 (by rfl) ⟨1115186, by rfl⟩ : syracuseStep 5947661 = 2230373) B2230373
theorem B3965107 : Blo 2087435 3965107 := bstep (se 1 (by rfl) ⟨2973830, by rfl⟩ : syracuseStep 3965107 = 5947661) B5947661
theorem B5286809 : Blo 2087435 5286809 := bstep (se 2 (by rfl) ⟨1982553, by rfl⟩ : syracuseStep 5286809 = 3965107) B3965107
theorem B3524539 : Blo 2087435 3524539 := bstep (se 1 (by rfl) ⟨2643404, by rfl⟩ : syracuseStep 3524539 = 5286809) B5286809
theorem B4699385 : Blo 2087435 4699385 := bstep (se 2 (by rfl) ⟨1762269, by rfl⟩ : syracuseStep 4699385 = 3524539) B3524539
theorem B3132923 : Blo 2087435 3132923 := bstep (se 1 (by rfl) ⟨2349692, by rfl⟩ : syracuseStep 3132923 = 4699385) B4699385
theorem B2088615 : Blo 2087435 2088615 := bstep (se 1 (by rfl) ⟨1566461, by rfl⟩ : syracuseStep 2088615 = 3132923) B3132923
theorem B2349697 : Blo 2087435 2349697 := bbase (se 2 (by rfl) ⟨881136, by rfl⟩ : syracuseStep 2349697 = 1762273) (by norm_num)
theorem B3132929 : Blo 2087435 3132929 := bstep (se 2 (by rfl) ⟨1174848, by rfl⟩ : syracuseStep 3132929 = 2349697) B2349697
theorem B2088619 : Blo 2087435 2088619 := bstep (se 1 (by rfl) ⟨1566464, by rfl⟩ : syracuseStep 2088619 = 3132929) B3132929
theorem B5286829 : Blo 2087435 5286829 := bbase (se 3 (by rfl) ⟨991280, by rfl⟩ : syracuseStep 5286829 = 1982561) (by norm_num)
theorem B7049105 : Blo 2087435 7049105 := bstep (se 2 (by rfl) ⟨2643414, by rfl⟩ : syracuseStep 7049105 = 5286829) B5286829
theorem B4699403 : Blo 2087435 4699403 := bstep (se 1 (by rfl) ⟨3524552, by rfl⟩ : syracuseStep 4699403 = 7049105) B7049105
theorem B3132935 : Blo 2087435 3132935 := bstep (se 1 (by rfl) ⟨2349701, by rfl⟩ : syracuseStep 3132935 = 4699403) B4699403
theorem B2088623 : Blo 2087435 2088623 := bstep (se 1 (by rfl) ⟨1566467, by rfl⟩ : syracuseStep 2088623 = 3132935) B3132935
theorem B3132941 : Blo 2087435 3132941 := bbase (se 3 (by rfl) ⟨587426, by rfl⟩ : syracuseStep 3132941 = 1174853) (by norm_num)
theorem B2088627 : Blo 2087435 2088627 := bstep (se 1 (by rfl) ⟨1566470, by rfl⟩ : syracuseStep 2088627 = 3132941) B3132941
theorem B4699421 : Blo 2087435 4699421 := bbase (se 3 (by rfl) ⟨881141, by rfl⟩ : syracuseStep 4699421 = 1762283) (by norm_num)
theorem B3132947 : Blo 2087435 3132947 := bstep (se 1 (by rfl) ⟨2349710, by rfl⟩ : syracuseStep 3132947 = 4699421) B4699421
theorem B2088631 : Blo 2087435 2088631 := bstep (se 1 (by rfl) ⟨1566473, by rfl⟩ : syracuseStep 2088631 = 3132947) B3132947
theorem B3524573 : Blo 2087435 3524573 := bbase (se 3 (by rfl) ⟨660857, by rfl⟩ : syracuseStep 3524573 = 1321715) (by norm_num)
theorem B2349715 : Blo 2087435 2349715 := bstep (se 1 (by rfl) ⟨1762286, by rfl⟩ : syracuseStep 2349715 = 3524573) B3524573
theorem B3132953 : Blo 2087435 3132953 := bstep (se 2 (by rfl) ⟨1174857, by rfl⟩ : syracuseStep 3132953 = 2349715) B2349715
theorem B2088635 : Blo 2087435 2088635 := bstep (se 1 (by rfl) ⟨1566476, by rfl⟩ : syracuseStep 2088635 = 3132953) B3132953
theorem B4763557 : Blo 2087435 4763557 := bbase (se 4 (by rfl) ⟨446583, by rfl⟩ : syracuseStep 4763557 = 893167) (by norm_num)
theorem B6351409 : Blo 2087435 6351409 := bstep (se 2 (by rfl) ⟨2381778, by rfl⟩ : syracuseStep 6351409 = 4763557) B4763557
theorem B8468545 : Blo 2087435 8468545 := bstep (se 2 (by rfl) ⟨3175704, by rfl⟩ : syracuseStep 8468545 = 6351409) B6351409
theorem B11291393 : Blo 2087435 11291393 := bstep (se 2 (by rfl) ⟨4234272, by rfl⟩ : syracuseStep 11291393 = 8468545) B8468545
theorem B7527595 : Blo 2087435 7527595 := bstep (se 1 (by rfl) ⟨5645696, by rfl⟩ : syracuseStep 7527595 = 11291393) B11291393
theorem B10036793 : Blo 2087435 10036793 := bstep (se 2 (by rfl) ⟨3763797, by rfl⟩ : syracuseStep 10036793 = 7527595) B7527595
theorem B6691195 : Blo 2087435 6691195 := bstep (se 1 (by rfl) ⟨5018396, by rfl⟩ : syracuseStep 6691195 = 10036793) B10036793
theorem B8921593 : Blo 2087435 8921593 := bstep (se 2 (by rfl) ⟨3345597, by rfl⟩ : syracuseStep 8921593 = 6691195) B6691195
theorem B11895457 : Blo 2087435 11895457 := bstep (se 2 (by rfl) ⟨4460796, by rfl⟩ : syracuseStep 11895457 = 8921593) B8921593
theorem B15860609 : Blo 2087435 15860609 := bstep (se 2 (by rfl) ⟨5947728, by rfl⟩ : syracuseStep 15860609 = 11895457) B11895457
theorem B10573739 : Blo 2087435 10573739 := bstep (se 1 (by rfl) ⟨7930304, by rfl⟩ : syracuseStep 10573739 = 15860609) B15860609
theorem B7049159 : Blo 2087435 7049159 := bstep (se 1 (by rfl) ⟨5286869, by rfl⟩ : syracuseStep 7049159 = 10573739) B10573739
theorem B4699439 : Blo 2087435 4699439 := bstep (se 1 (by rfl) ⟨3524579, by rfl⟩ : syracuseStep 4699439 = 7049159) B7049159
theorem B3132959 : Blo 2087435 3132959 := bstep (se 1 (by rfl) ⟨2349719, by rfl⟩ : syracuseStep 3132959 = 4699439) B4699439
theorem B2088639 : Blo 2087435 2088639 := bstep (se 1 (by rfl) ⟨1566479, by rfl⟩ : syracuseStep 2088639 = 3132959) B3132959
theorem B3132965 : Blo 2087435 3132965 := bbase (se 4 (by rfl) ⟨293715, by rfl⟩ : syracuseStep 3132965 = 587431) (by norm_num)
theorem B2088643 : Blo 2087435 2088643 := bstep (se 1 (by rfl) ⟨1566482, by rfl⟩ : syracuseStep 2088643 = 3132965) B3132965
theorem B2643445 : Blo 2087435 2643445 := bbase (se 5 (by rfl) ⟨123911, by rfl⟩ : syracuseStep 2643445 = 247823) (by norm_num)
theorem B3524593 : Blo 2087435 3524593 := bstep (se 2 (by rfl) ⟨1321722, by rfl⟩ : syracuseStep 3524593 = 2643445) B2643445
theorem B4699457 : Blo 2087435 4699457 := bstep (se 2 (by rfl) ⟨1762296, by rfl⟩ : syracuseStep 4699457 = 3524593) B3524593
theorem B3132971 : Blo 2087435 3132971 := bstep (se 1 (by rfl) ⟨2349728, by rfl⟩ : syracuseStep 3132971 = 4699457) B4699457
theorem B2088647 : Blo 2087435 2088647 := bstep (se 1 (by rfl) ⟨1566485, by rfl⟩ : syracuseStep 2088647 = 3132971) B3132971
theorem B2349733 : Blo 2087435 2349733 := bbase (se 4 (by rfl) ⟨220287, by rfl⟩ : syracuseStep 2349733 = 440575) (by norm_num)
theorem B3132977 : Blo 2087435 3132977 := bstep (se 2 (by rfl) ⟨1174866, by rfl⟩ : syracuseStep 3132977 = 2349733) B2349733
theorem B2088651 : Blo 2087435 2088651 := bstep (se 1 (by rfl) ⟨1566488, by rfl⟩ : syracuseStep 2088651 = 3132977) B3132977
theorem B2381797 : Blo 2087435 2381797 := bbase (se 4 (by rfl) ⟨223293, by rfl⟩ : syracuseStep 2381797 = 446587) (by norm_num)
theorem B3175729 : Blo 2087435 3175729 := bstep (se 2 (by rfl) ⟨1190898, by rfl⟩ : syracuseStep 3175729 = 2381797) B2381797
theorem B67748885 : Blo 2087435 67748885 := bstep (se 6 (by rfl) ⟨1587864, by rfl⟩ : syracuseStep 67748885 = 3175729) B3175729
theorem B45165923 : Blo 2087435 45165923 := bstep (se 1 (by rfl) ⟨33874442, by rfl⟩ : syracuseStep 45165923 = 67748885) B67748885
theorem B30110615 : Blo 2087435 30110615 := bstep (se 1 (by rfl) ⟨22582961, by rfl⟩ : syracuseStep 30110615 = 45165923) B45165923
theorem B20073743 : Blo 2087435 20073743 := bstep (se 1 (by rfl) ⟨15055307, by rfl⟩ : syracuseStep 20073743 = 30110615) B30110615
theorem B13382495 : Blo 2087435 13382495 := bstep (se 1 (by rfl) ⟨10036871, by rfl⟩ : syracuseStep 13382495 = 20073743) B20073743
theorem B8921663 : Blo 2087435 8921663 := bstep (se 1 (by rfl) ⟨6691247, by rfl⟩ : syracuseStep 8921663 = 13382495) B13382495
theorem B5947775 : Blo 2087435 5947775 := bstep (se 1 (by rfl) ⟨4460831, by rfl⟩ : syracuseStep 5947775 = 8921663) B8921663
theorem B3965183 : Blo 2087435 3965183 := bstep (se 1 (by rfl) ⟨2973887, by rfl⟩ : syracuseStep 3965183 = 5947775) B5947775
theorem B2643455 : Blo 2087435 2643455 := bstep (se 1 (by rfl) ⟨1982591, by rfl⟩ : syracuseStep 2643455 = 3965183) B3965183
theorem B7049213 : Blo 2087435 7049213 := bstep (se 3 (by rfl) ⟨1321727, by rfl⟩ : syracuseStep 7049213 = 2643455) B2643455
theorem B4699475 : Blo 2087435 4699475 := bstep (se 1 (by rfl) ⟨3524606, by rfl⟩ : syracuseStep 4699475 = 7049213) B7049213
theorem B3132983 : Blo 2087435 3132983 := bstep (se 1 (by rfl) ⟨2349737, by rfl⟩ : syracuseStep 3132983 = 4699475) B4699475
theorem B2088655 : Blo 2087435 2088655 := bstep (se 1 (by rfl) ⟨1566491, by rfl⟩ : syracuseStep 2088655 = 3132983) B3132983
theorem B3132989 : Blo 2087435 3132989 := bbase (se 3 (by rfl) ⟨587435, by rfl⟩ : syracuseStep 3132989 = 1174871) (by norm_num)
theorem B2088659 : Blo 2087435 2088659 := bstep (se 1 (by rfl) ⟨1566494, by rfl⟩ : syracuseStep 2088659 = 3132989) B3132989
theorem B4699493 : Blo 2087435 4699493 := bbase (se 4 (by rfl) ⟨440577, by rfl⟩ : syracuseStep 4699493 = 881155) (by norm_num)
theorem B3132995 : Blo 2087435 3132995 := bstep (se 1 (by rfl) ⟨2349746, by rfl⟩ : syracuseStep 3132995 = 4699493) B4699493
theorem B2088663 : Blo 2087435 2088663 := bstep (se 1 (by rfl) ⟨1566497, by rfl⟩ : syracuseStep 2088663 = 3132995) B3132995
theorem B5286941 : Blo 2087435 5286941 := bbase (se 3 (by rfl) ⟨991301, by rfl⟩ : syracuseStep 5286941 = 1982603) (by norm_num)
theorem B3524627 : Blo 2087435 3524627 := bstep (se 1 (by rfl) ⟨2643470, by rfl⟩ : syracuseStep 3524627 = 5286941) B5286941
theorem B2349751 : Blo 2087435 2349751 := bstep (se 1 (by rfl) ⟨1762313, by rfl⟩ : syracuseStep 2349751 = 3524627) B3524627
theorem B3133001 : Blo 2087435 3133001 := bstep (se 2 (by rfl) ⟨1174875, by rfl⟩ : syracuseStep 3133001 = 2349751) B2349751
theorem B2088667 : Blo 2087435 2088667 := bstep (se 1 (by rfl) ⟨1566500, by rfl⟩ : syracuseStep 2088667 = 3133001) B3133001
theorem B3965213 : Blo 2087435 3965213 := bbase (se 3 (by rfl) ⟨743477, by rfl⟩ : syracuseStep 3965213 = 1486955) (by norm_num)
theorem B10573901 : Blo 2087435 10573901 := bstep (se 3 (by rfl) ⟨1982606, by rfl⟩ : syracuseStep 10573901 = 3965213) B3965213
theorem B7049267 : Blo 2087435 7049267 := bstep (se 1 (by rfl) ⟨5286950, by rfl⟩ : syracuseStep 7049267 = 10573901) B10573901
theorem B4699511 : Blo 2087435 4699511 := bstep (se 1 (by rfl) ⟨3524633, by rfl⟩ : syracuseStep 4699511 = 7049267) B7049267
theorem B3133007 : Blo 2087435 3133007 := bstep (se 1 (by rfl) ⟨2349755, by rfl⟩ : syracuseStep 3133007 = 4699511) B4699511
theorem B2088671 : Blo 2087435 2088671 := bstep (se 1 (by rfl) ⟨1566503, by rfl⟩ : syracuseStep 2088671 = 3133007) B3133007
theorem B3133013 : Blo 2087435 3133013 := bbase (se 8 (by rfl) ⟨18357, by rfl⟩ : syracuseStep 3133013 = 36715) (by norm_num)
theorem B2088675 : Blo 2087435 2088675 := bstep (se 1 (by rfl) ⟨1566506, by rfl⟩ : syracuseStep 2088675 = 3133013) B3133013
theorem B8921765 : Blo 2087435 8921765 := bbase (se 4 (by rfl) ⟨836415, by rfl⟩ : syracuseStep 8921765 = 1672831) (by norm_num)
theorem B5947843 : Blo 2087435 5947843 := bstep (se 1 (by rfl) ⟨4460882, by rfl⟩ : syracuseStep 5947843 = 8921765) B8921765
theorem B7930457 : Blo 2087435 7930457 := bstep (se 2 (by rfl) ⟨2973921, by rfl⟩ : syracuseStep 7930457 = 5947843) B5947843
theorem B5286971 : Blo 2087435 5286971 := bstep (se 1 (by rfl) ⟨3965228, by rfl⟩ : syracuseStep 5286971 = 7930457) B7930457
theorem B3524647 : Blo 2087435 3524647 := bstep (se 1 (by rfl) ⟨2643485, by rfl⟩ : syracuseStep 3524647 = 5286971) B5286971
theorem B4699529 : Blo 2087435 4699529 := bstep (se 2 (by rfl) ⟨1762323, by rfl⟩ : syracuseStep 4699529 = 3524647) B3524647
theorem B3133019 : Blo 2087435 3133019 := bstep (se 1 (by rfl) ⟨2349764, by rfl⟩ : syracuseStep 3133019 = 4699529) B4699529
theorem B2088679 : Blo 2087435 2088679 := bstep (se 1 (by rfl) ⟨1566509, by rfl⟩ : syracuseStep 2088679 = 3133019) B3133019
theorem B2349769 : Blo 2087435 2349769 := bbase (se 2 (by rfl) ⟨881163, by rfl⟩ : syracuseStep 2349769 = 1762327) (by norm_num)
theorem B3133025 : Blo 2087435 3133025 := bstep (se 2 (by rfl) ⟨1174884, by rfl⟩ : syracuseStep 3133025 = 2349769) B2349769
theorem B2088683 : Blo 2087435 2088683 := bstep (se 1 (by rfl) ⟨1566512, by rfl⟩ : syracuseStep 2088683 = 3133025) B3133025
theorem B6691349 : Blo 2087435 6691349 := bbase (se 6 (by rfl) ⟨156828, by rfl⟩ : syracuseStep 6691349 = 313657) (by norm_num)
theorem B17843597 : Blo 2087435 17843597 := bstep (se 3 (by rfl) ⟨3345674, by rfl⟩ : syracuseStep 17843597 = 6691349) B6691349
theorem B11895731 : Blo 2087435 11895731 := bstep (se 1 (by rfl) ⟨8921798, by rfl⟩ : syracuseStep 11895731 = 17843597) B17843597
theorem B7930487 : Blo 2087435 7930487 := bstep (se 1 (by rfl) ⟨5947865, by rfl⟩ : syracuseStep 7930487 = 11895731) B11895731
theorem B5286991 : Blo 2087435 5286991 := bstep (se 1 (by rfl) ⟨3965243, by rfl⟩ : syracuseStep 5286991 = 7930487) B7930487
theorem B7049321 : Blo 2087435 7049321 := bstep (se 2 (by rfl) ⟨2643495, by rfl⟩ : syracuseStep 7049321 = 5286991) B5286991
theorem B4699547 : Blo 2087435 4699547 := bstep (se 1 (by rfl) ⟨3524660, by rfl⟩ : syracuseStep 4699547 = 7049321) B7049321
theorem B3133031 : Blo 2087435 3133031 := bstep (se 1 (by rfl) ⟨2349773, by rfl⟩ : syracuseStep 3133031 = 4699547) B4699547
theorem B2088687 : Blo 2087435 2088687 := bstep (se 1 (by rfl) ⟨1566515, by rfl⟩ : syracuseStep 2088687 = 3133031) B3133031
theorem B3133037 : Blo 2087435 3133037 := bbase (se 3 (by rfl) ⟨587444, by rfl⟩ : syracuseStep 3133037 = 1174889) (by norm_num)
theorem B2088691 : Blo 2087435 2088691 := bstep (se 1 (by rfl) ⟨1566518, by rfl⟩ : syracuseStep 2088691 = 3133037) B3133037
theorem B4699565 : Blo 2087435 4699565 := bbase (se 3 (by rfl) ⟨881168, by rfl⟩ : syracuseStep 4699565 = 1762337) (by norm_num)
theorem B3133043 : Blo 2087435 3133043 := bstep (se 1 (by rfl) ⟨2349782, by rfl⟩ : syracuseStep 3133043 = 4699565) B4699565
theorem B2088695 : Blo 2087435 2088695 := bstep (se 1 (by rfl) ⟨1566521, by rfl⟩ : syracuseStep 2088695 = 3133043) B3133043
theorem B12703189 : Blo 2087435 12703189 := bbase (se 7 (by rfl) ⟨148865, by rfl⟩ : syracuseStep 12703189 = 297731) (by norm_num)
theorem B16937585 : Blo 2087435 16937585 := bstep (se 2 (by rfl) ⟨6351594, by rfl⟩ : syracuseStep 16937585 = 12703189) B12703189
theorem B11291723 : Blo 2087435 11291723 := bstep (se 1 (by rfl) ⟨8468792, by rfl⟩ : syracuseStep 11291723 = 16937585) B16937585
theorem B7527815 : Blo 2087435 7527815 := bstep (se 1 (by rfl) ⟨5645861, by rfl⟩ : syracuseStep 7527815 = 11291723) B11291723
theorem B5018543 : Blo 2087435 5018543 := bstep (se 1 (by rfl) ⟨3763907, by rfl⟩ : syracuseStep 5018543 = 7527815) B7527815
theorem B3345695 : Blo 2087435 3345695 := bstep (se 1 (by rfl) ⟨2509271, by rfl⟩ : syracuseStep 3345695 = 5018543) B5018543
theorem B2230463 : Blo 2087435 2230463 := bstep (se 1 (by rfl) ⟨1672847, by rfl⟩ : syracuseStep 2230463 = 3345695) B3345695
theorem B5947901 : Blo 2087435 5947901 := bstep (se 3 (by rfl) ⟨1115231, by rfl⟩ : syracuseStep 5947901 = 2230463) B2230463
theorem B3965267 : Blo 2087435 3965267 := bstep (se 1 (by rfl) ⟨2973950, by rfl⟩ : syracuseStep 3965267 = 5947901) B5947901
theorem B2643511 : Blo 2087435 2643511 := bstep (se 1 (by rfl) ⟨1982633, by rfl⟩ : syracuseStep 2643511 = 3965267) B3965267
theorem B3524681 : Blo 2087435 3524681 := bstep (se 2 (by rfl) ⟨1321755, by rfl⟩ : syracuseStep 3524681 = 2643511) B2643511
theorem B2349787 : Blo 2087435 2349787 := bstep (se 1 (by rfl) ⟨1762340, by rfl⟩ : syracuseStep 2349787 = 3524681) B3524681
theorem B3133049 : Blo 2087435 3133049 := bstep (se 2 (by rfl) ⟨1174893, by rfl⟩ : syracuseStep 3133049 = 2349787) B2349787
theorem B2088699 : Blo 2087435 2088699 := bstep (se 1 (by rfl) ⟨1566524, by rfl⟩ : syracuseStep 2088699 = 3133049) B3133049
theorem B5432285 : Blo 2087435 5432285 := bbase (se 3 (by rfl) ⟨1018553, by rfl⟩ : syracuseStep 5432285 = 2037107) (by norm_num)
theorem B3621523 : Blo 2087435 3621523 := bstep (se 1 (by rfl) ⟨2716142, by rfl⟩ : syracuseStep 3621523 = 5432285) B5432285
theorem B4828697 : Blo 2087435 4828697 := bstep (se 2 (by rfl) ⟨1810761, by rfl⟩ : syracuseStep 4828697 = 3621523) B3621523
theorem B3219131 : Blo 2087435 3219131 := bstep (se 1 (by rfl) ⟨2414348, by rfl⟩ : syracuseStep 3219131 = 4828697) B4828697
theorem B2146087 : Blo 2087435 2146087 := bstep (se 1 (by rfl) ⟨1609565, by rfl⟩ : syracuseStep 2146087 = 3219131) B3219131
theorem B2861449 : Blo 2087435 2861449 := bstep (se 2 (by rfl) ⟨1073043, by rfl⟩ : syracuseStep 2861449 = 2146087) B2146087
theorem B15261061 : Blo 2087435 15261061 := bstep (se 4 (by rfl) ⟨1430724, by rfl⟩ : syracuseStep 15261061 = 2861449) B2861449
theorem B20348081 : Blo 2087435 20348081 := bstep (se 2 (by rfl) ⟨7630530, by rfl⟩ : syracuseStep 20348081 = 15261061) B15261061
theorem B13565387 : Blo 2087435 13565387 := bstep (se 1 (by rfl) ⟨10174040, by rfl⟩ : syracuseStep 13565387 = 20348081) B20348081
theorem B9043591 : Blo 2087435 9043591 := bstep (se 1 (by rfl) ⟨6782693, by rfl⟩ : syracuseStep 9043591 = 13565387) B13565387
theorem B12058121 : Blo 2087435 12058121 := bstep (se 2 (by rfl) ⟨4521795, by rfl⟩ : syracuseStep 12058121 = 9043591) B9043591
theorem B8038747 : Blo 2087435 8038747 := bstep (se 1 (by rfl) ⟨6029060, by rfl⟩ : syracuseStep 8038747 = 12058121) B12058121
theorem B42873317 : Blo 2087435 42873317 := bstep (se 4 (by rfl) ⟨4019373, by rfl⟩ : syracuseStep 42873317 = 8038747) B8038747
theorem B28582211 : Blo 2087435 28582211 := bstep (se 1 (by rfl) ⟨21436658, by rfl⟩ : syracuseStep 28582211 = 42873317) B42873317
theorem B19054807 : Blo 2087435 19054807 := bstep (se 1 (by rfl) ⟨14291105, by rfl⟩ : syracuseStep 19054807 = 28582211) B28582211
theorem B101625637 : Blo 2087435 101625637 := bstep (se 4 (by rfl) ⟨9527403, by rfl⟩ : syracuseStep 101625637 = 19054807) B19054807
theorem B135500849 : Blo 2087435 135500849 := bstep (se 2 (by rfl) ⟨50812818, by rfl⟩ : syracuseStep 135500849 = 101625637) B101625637
theorem B90333899 : Blo 2087435 90333899 := bstep (se 1 (by rfl) ⟨67750424, by rfl⟩ : syracuseStep 90333899 = 135500849) B135500849
theorem B60222599 : Blo 2087435 60222599 := bstep (se 1 (by rfl) ⟨45166949, by rfl⟩ : syracuseStep 60222599 = 90333899) B90333899
theorem B40148399 : Blo 2087435 40148399 := bstep (se 1 (by rfl) ⟨30111299, by rfl⟩ : syracuseStep 40148399 = 60222599) B60222599
theorem B26765599 : Blo 2087435 26765599 := bstep (se 1 (by rfl) ⟨20074199, by rfl⟩ : syracuseStep 26765599 = 40148399) B40148399
theorem B35687465 : Blo 2087435 35687465 := bstep (se 2 (by rfl) ⟨13382799, by rfl⟩ : syracuseStep 35687465 = 26765599) B26765599
theorem B23791643 : Blo 2087435 23791643 := bstep (se 1 (by rfl) ⟨17843732, by rfl⟩ : syracuseStep 23791643 = 35687465) B35687465
theorem B15861095 : Blo 2087435 15861095 := bstep (se 1 (by rfl) ⟨11895821, by rfl⟩ : syracuseStep 15861095 = 23791643) B23791643
theorem B10574063 : Blo 2087435 10574063 := bstep (se 1 (by rfl) ⟨7930547, by rfl⟩ : syracuseStep 10574063 = 15861095) B15861095
theorem B7049375 : Blo 2087435 7049375 := bstep (se 1 (by rfl) ⟨5287031, by rfl⟩ : syracuseStep 7049375 = 10574063) B10574063
theorem B4699583 : Blo 2087435 4699583 := bstep (se 1 (by rfl) ⟨3524687, by rfl⟩ : syracuseStep 4699583 = 7049375) B7049375
theorem B3133055 : Blo 2087435 3133055 := bstep (se 1 (by rfl) ⟨2349791, by rfl⟩ : syracuseStep 3133055 = 4699583) B4699583
theorem B2088703 : Blo 2087435 2088703 := bstep (se 1 (by rfl) ⟨1566527, by rfl⟩ : syracuseStep 2088703 = 3133055) B3133055
theorem B3133061 : Blo 2087435 3133061 := bbase (se 4 (by rfl) ⟨293724, by rfl⟩ : syracuseStep 3133061 = 587449) (by norm_num)
theorem B2088707 : Blo 2087435 2088707 := bstep (se 1 (by rfl) ⟨1566530, by rfl⟩ : syracuseStep 2088707 = 3133061) B3133061
theorem B3524701 : Blo 2087435 3524701 := bbase (se 3 (by rfl) ⟨660881, by rfl⟩ : syracuseStep 3524701 = 1321763) (by norm_num)
theorem B4699601 : Blo 2087435 4699601 := bstep (se 2 (by rfl) ⟨1762350, by rfl⟩ : syracuseStep 4699601 = 3524701) B3524701
theorem B3133067 : Blo 2087435 3133067 := bstep (se 1 (by rfl) ⟨2349800, by rfl⟩ : syracuseStep 3133067 = 4699601) B4699601
theorem B2088711 : Blo 2087435 2088711 := bstep (se 1 (by rfl) ⟨1566533, by rfl⟩ : syracuseStep 2088711 = 3133067) B3133067
theorem B2349805 : Blo 2087435 2349805 := bbase (se 3 (by rfl) ⟨440588, by rfl⟩ : syracuseStep 2349805 = 881177) (by norm_num)
theorem B3133073 : Blo 2087435 3133073 := bstep (se 2 (by rfl) ⟨1174902, by rfl⟩ : syracuseStep 3133073 = 2349805) B2349805
theorem B2088715 : Blo 2087435 2088715 := bstep (se 1 (by rfl) ⟨1566536, by rfl⟩ : syracuseStep 2088715 = 3133073) B3133073
theorem B7049429 : Blo 2087435 7049429 := bbase (se 7 (by rfl) ⟨82610, by rfl⟩ : syracuseStep 7049429 = 165221) (by norm_num)
theorem B4699619 : Blo 2087435 4699619 := bstep (se 1 (by rfl) ⟨3524714, by rfl⟩ : syracuseStep 4699619 = 7049429) B7049429
theorem B3133079 : Blo 2087435 3133079 := bstep (se 1 (by rfl) ⟨2349809, by rfl⟩ : syracuseStep 3133079 = 4699619) B4699619
theorem B2088719 : Blo 2087435 2088719 := bstep (se 1 (by rfl) ⟨1566539, by rfl⟩ : syracuseStep 2088719 = 3133079) B3133079
theorem B3133085 : Blo 2087435 3133085 := bbase (se 3 (by rfl) ⟨587453, by rfl⟩ : syracuseStep 3133085 = 1174907) (by norm_num)
theorem B2088723 : Blo 2087435 2088723 := bstep (se 1 (by rfl) ⟨1566542, by rfl⟩ : syracuseStep 2088723 = 3133085) B3133085
theorem B4699637 : Blo 2087435 4699637 := bbase (se 5 (by rfl) ⟨220295, by rfl⟩ : syracuseStep 4699637 = 440591) (by norm_num)
theorem B3133091 : Blo 2087435 3133091 := bstep (se 1 (by rfl) ⟨2349818, by rfl⟩ : syracuseStep 3133091 = 4699637) B4699637
theorem B2088727 : Blo 2087435 2088727 := bstep (se 1 (by rfl) ⟨1566545, by rfl⟩ : syracuseStep 2088727 = 3133091) B3133091
theorem B4019429 : Blo 2087435 4019429 := bbase (se 4 (by rfl) ⟨376821, by rfl⟩ : syracuseStep 4019429 = 753643) (by norm_num)
theorem B10718477 : Blo 2087435 10718477 := bstep (se 3 (by rfl) ⟨2009714, by rfl⟩ : syracuseStep 10718477 = 4019429) B4019429
theorem B7145651 : Blo 2087435 7145651 := bstep (se 1 (by rfl) ⟨5359238, by rfl⟩ : syracuseStep 7145651 = 10718477) B10718477
theorem B4763767 : Blo 2087435 4763767 := bstep (se 1 (by rfl) ⟨3572825, by rfl⟩ : syracuseStep 4763767 = 7145651) B7145651
theorem B6351689 : Blo 2087435 6351689 := bstep (se 2 (by rfl) ⟨2381883, by rfl⟩ : syracuseStep 6351689 = 4763767) B4763767
theorem B16937837 : Blo 2087435 16937837 := bstep (se 3 (by rfl) ⟨3175844, by rfl⟩ : syracuseStep 16937837 = 6351689) B6351689
theorem B11291891 : Blo 2087435 11291891 := bstep (se 1 (by rfl) ⟨8468918, by rfl⟩ : syracuseStep 11291891 = 16937837) B16937837
theorem B30111709 : Blo 2087435 30111709 := bstep (se 3 (by rfl) ⟨5645945, by rfl⟩ : syracuseStep 30111709 = 11291891) B11291891
theorem B40148945 : Blo 2087435 40148945 := bstep (se 2 (by rfl) ⟨15055854, by rfl⟩ : syracuseStep 40148945 = 30111709) B30111709
theorem B26765963 : Blo 2087435 26765963 := bstep (se 1 (by rfl) ⟨20074472, by rfl⟩ : syracuseStep 26765963 = 40148945) B40148945
theorem B17843975 : Blo 2087435 17843975 := bstep (se 1 (by rfl) ⟨13382981, by rfl⟩ : syracuseStep 17843975 = 26765963) B26765963
theorem B11895983 : Blo 2087435 11895983 := bstep (se 1 (by rfl) ⟨8921987, by rfl⟩ : syracuseStep 11895983 = 17843975) B17843975
theorem B7930655 : Blo 2087435 7930655 := bstep (se 1 (by rfl) ⟨5947991, by rfl⟩ : syracuseStep 7930655 = 11895983) B11895983
theorem B5287103 : Blo 2087435 5287103 := bstep (se 1 (by rfl) ⟨3965327, by rfl⟩ : syracuseStep 5287103 = 7930655) B7930655
theorem B3524735 : Blo 2087435 3524735 := bstep (se 1 (by rfl) ⟨2643551, by rfl⟩ : syracuseStep 3524735 = 5287103) B5287103
theorem B2349823 : Blo 2087435 2349823 := bstep (se 1 (by rfl) ⟨1762367, by rfl⟩ : syracuseStep 2349823 = 3524735) B3524735
theorem B3133097 : Blo 2087435 3133097 := bstep (se 2 (by rfl) ⟨1174911, by rfl⟩ : syracuseStep 3133097 = 2349823) B2349823
theorem B2088731 : Blo 2087435 2088731 := bstep (se 1 (by rfl) ⟨1566548, by rfl⟩ : syracuseStep 2088731 = 3133097) B3133097
theorem B2230501 : Blo 2087435 2230501 := bbase (se 4 (by rfl) ⟨209109, by rfl⟩ : syracuseStep 2230501 = 418219) (by norm_num)
theorem B2974001 : Blo 2087435 2974001 := bstep (se 2 (by rfl) ⟨1115250, by rfl⟩ : syracuseStep 2974001 = 2230501) B2230501
theorem B7930669 : Blo 2087435 7930669 := bstep (se 3 (by rfl) ⟨1487000, by rfl⟩ : syracuseStep 7930669 = 2974001) B2974001
theorem B10574225 : Blo 2087435 10574225 := bstep (se 2 (by rfl) ⟨3965334, by rfl⟩ : syracuseStep 10574225 = 7930669) B7930669
theorem B7049483 : Blo 2087435 7049483 := bstep (se 1 (by rfl) ⟨5287112, by rfl⟩ : syracuseStep 7049483 = 10574225) B10574225
theorem B4699655 : Blo 2087435 4699655 := bstep (se 1 (by rfl) ⟨3524741, by rfl⟩ : syracuseStep 4699655 = 7049483) B7049483
theorem B3133103 : Blo 2087435 3133103 := bstep (se 1 (by rfl) ⟨2349827, by rfl⟩ : syracuseStep 3133103 = 4699655) B4699655
theorem B2088735 : Blo 2087435 2088735 := bstep (se 1 (by rfl) ⟨1566551, by rfl⟩ : syracuseStep 2088735 = 3133103) B3133103
theorem B3133109 : Blo 2087435 3133109 := bbase (se 5 (by rfl) ⟨146864, by rfl⟩ : syracuseStep 3133109 = 293729) (by norm_num)
theorem B2088739 : Blo 2087435 2088739 := bstep (se 1 (by rfl) ⟨1566554, by rfl⟩ : syracuseStep 2088739 = 3133109) B3133109
theorem B5287133 : Blo 2087435 5287133 := bbase (se 3 (by rfl) ⟨991337, by rfl⟩ : syracuseStep 5287133 = 1982675) (by norm_num)
theorem B3524755 : Blo 2087435 3524755 := bstep (se 1 (by rfl) ⟨2643566, by rfl⟩ : syracuseStep 3524755 = 5287133) B5287133
theorem B4699673 : Blo 2087435 4699673 := bstep (se 2 (by rfl) ⟨1762377, by rfl⟩ : syracuseStep 4699673 = 3524755) B3524755
theorem B3133115 : Blo 2087435 3133115 := bstep (se 1 (by rfl) ⟨2349836, by rfl⟩ : syracuseStep 3133115 = 4699673) B4699673
theorem B2088743 : Blo 2087435 2088743 := bstep (se 1 (by rfl) ⟨1566557, by rfl⟩ : syracuseStep 2088743 = 3133115) B3133115
theorem B2349841 : Blo 2087435 2349841 := bbase (se 2 (by rfl) ⟨881190, by rfl⟩ : syracuseStep 2349841 = 1762381) (by norm_num)
theorem B3133121 : Blo 2087435 3133121 := bstep (se 2 (by rfl) ⟨1174920, by rfl⟩ : syracuseStep 3133121 = 2349841) B2349841
theorem B2088747 : Blo 2087435 2088747 := bstep (se 1 (by rfl) ⟨1566560, by rfl⟩ : syracuseStep 2088747 = 3133121) B3133121
theorem B3965365 : Blo 2087435 3965365 := bbase (se 5 (by rfl) ⟨185876, by rfl⟩ : syracuseStep 3965365 = 371753) (by norm_num)
theorem B5287153 : Blo 2087435 5287153 := bstep (se 2 (by rfl) ⟨1982682, by rfl⟩ : syracuseStep 5287153 = 3965365) B3965365
theorem B7049537 : Blo 2087435 7049537 := bstep (se 2 (by rfl) ⟨2643576, by rfl⟩ : syracuseStep 7049537 = 5287153) B5287153
theorem B4699691 : Blo 2087435 4699691 := bstep (se 1 (by rfl) ⟨3524768, by rfl⟩ : syracuseStep 4699691 = 7049537) B7049537
theorem B3133127 : Blo 2087435 3133127 := bstep (se 1 (by rfl) ⟨2349845, by rfl⟩ : syracuseStep 3133127 = 4699691) B4699691
theorem B2088751 : Blo 2087435 2088751 := bstep (se 1 (by rfl) ⟨1566563, by rfl⟩ : syracuseStep 2088751 = 3133127) B3133127
theorem B3133133 : Blo 2087435 3133133 := bbase (se 3 (by rfl) ⟨587462, by rfl⟩ : syracuseStep 3133133 = 1174925) (by norm_num)
theorem B2088755 : Blo 2087435 2088755 := bstep (se 1 (by rfl) ⟨1566566, by rfl⟩ : syracuseStep 2088755 = 3133133) B3133133
theorem B4699709 : Blo 2087435 4699709 := bbase (se 3 (by rfl) ⟨881195, by rfl⟩ : syracuseStep 4699709 = 1762391) (by norm_num)
theorem B3133139 : Blo 2087435 3133139 := bstep (se 1 (by rfl) ⟨2349854, by rfl⟩ : syracuseStep 3133139 = 4699709) B4699709
theorem B2088759 : Blo 2087435 2088759 := bstep (se 1 (by rfl) ⟨1566569, by rfl⟩ : syracuseStep 2088759 = 3133139) B3133139
theorem B3524789 : Blo 2087435 3524789 := bbase (se 5 (by rfl) ⟨165224, by rfl⟩ : syracuseStep 3524789 = 330449) (by norm_num)
theorem B2349859 : Blo 2087435 2349859 := bstep (se 1 (by rfl) ⟨1762394, by rfl⟩ : syracuseStep 2349859 = 3524789) B3524789
theorem B3133145 : Blo 2087435 3133145 := bstep (se 2 (by rfl) ⟨1174929, by rfl⟩ : syracuseStep 3133145 = 2349859) B2349859
theorem B2088763 : Blo 2087435 2088763 := bstep (se 1 (by rfl) ⟨1566572, by rfl⟩ : syracuseStep 2088763 = 3133145) B3133145
theorem B3764029 : Blo 2087435 3764029 := bbase (se 3 (by rfl) ⟨705755, by rfl⟩ : syracuseStep 3764029 = 1411511) (by norm_num)
theorem B5018705 : Blo 2087435 5018705 := bstep (se 2 (by rfl) ⟨1882014, by rfl⟩ : syracuseStep 5018705 = 3764029) B3764029
theorem B3345803 : Blo 2087435 3345803 := bstep (se 1 (by rfl) ⟨2509352, by rfl⟩ : syracuseStep 3345803 = 5018705) B5018705
theorem B2230535 : Blo 2087435 2230535 := bstep (se 1 (by rfl) ⟨1672901, by rfl⟩ : syracuseStep 2230535 = 3345803) B3345803
theorem B5948093 : Blo 2087435 5948093 := bstep (se 3 (by rfl) ⟨1115267, by rfl⟩ : syracuseStep 5948093 = 2230535) B2230535
theorem B15861581 : Blo 2087435 15861581 := bstep (se 3 (by rfl) ⟨2974046, by rfl⟩ : syracuseStep 15861581 = 5948093) B5948093
theorem B10574387 : Blo 2087435 10574387 := bstep (se 1 (by rfl) ⟨7930790, by rfl⟩ : syracuseStep 10574387 = 15861581) B15861581
theorem B7049591 : Blo 2087435 7049591 := bstep (se 1 (by rfl) ⟨5287193, by rfl⟩ : syracuseStep 7049591 = 10574387) B10574387
theorem B4699727 : Blo 2087435 4699727 := bstep (se 1 (by rfl) ⟨3524795, by rfl⟩ : syracuseStep 4699727 = 7049591) B7049591
theorem B3133151 : Blo 2087435 3133151 := bstep (se 1 (by rfl) ⟨2349863, by rfl⟩ : syracuseStep 3133151 = 4699727) B4699727
theorem B2088767 : Blo 2087435 2088767 := bstep (se 1 (by rfl) ⟨1566575, by rfl⟩ : syracuseStep 2088767 = 3133151) B3133151
theorem B3133157 : Blo 2087435 3133157 := bbase (se 4 (by rfl) ⟨293733, by rfl⟩ : syracuseStep 3133157 = 587467) (by norm_num)
theorem B2088771 : Blo 2087435 2088771 := bstep (se 1 (by rfl) ⟨1566578, by rfl⟩ : syracuseStep 2088771 = 3133157) B3133157
theorem B5948117 : Blo 2087435 5948117 := bbase (se 7 (by rfl) ⟨69704, by rfl⟩ : syracuseStep 5948117 = 139409) (by norm_num)
theorem B3965411 : Blo 2087435 3965411 := bstep (se 1 (by rfl) ⟨2974058, by rfl⟩ : syracuseStep 3965411 = 5948117) B5948117
theorem B2643607 : Blo 2087435 2643607 := bstep (se 1 (by rfl) ⟨1982705, by rfl⟩ : syracuseStep 2643607 = 3965411) B3965411
theorem B3524809 : Blo 2087435 3524809 := bstep (se 2 (by rfl) ⟨1321803, by rfl⟩ : syracuseStep 3524809 = 2643607) B2643607
theorem B4699745 : Blo 2087435 4699745 := bstep (se 2 (by rfl) ⟨1762404, by rfl⟩ : syracuseStep 4699745 = 3524809) B3524809
theorem B3133163 : Blo 2087435 3133163 := bstep (se 1 (by rfl) ⟨2349872, by rfl⟩ : syracuseStep 3133163 = 4699745) B4699745
theorem B2088775 : Blo 2087435 2088775 := bstep (se 1 (by rfl) ⟨1566581, by rfl⟩ : syracuseStep 2088775 = 3133163) B3133163
theorem B2349877 : Blo 2087435 2349877 := bbase (se 5 (by rfl) ⟨110150, by rfl⟩ : syracuseStep 2349877 = 220301) (by norm_num)
theorem B3133169 : Blo 2087435 3133169 := bstep (se 2 (by rfl) ⟨1174938, by rfl⟩ : syracuseStep 3133169 = 2349877) B2349877
theorem B2088779 : Blo 2087435 2088779 := bstep (se 1 (by rfl) ⟨1566584, by rfl⟩ : syracuseStep 2088779 = 3133169) B3133169
theorem B2643617 : Blo 2087435 2643617 := bbase (se 2 (by rfl) ⟨991356, by rfl⟩ : syracuseStep 2643617 = 1982713) (by norm_num)
theorem B7049645 : Blo 2087435 7049645 := bstep (se 3 (by rfl) ⟨1321808, by rfl⟩ : syracuseStep 7049645 = 2643617) B2643617
theorem B4699763 : Blo 2087435 4699763 := bstep (se 1 (by rfl) ⟨3524822, by rfl⟩ : syracuseStep 4699763 = 7049645) B7049645
theorem B3133175 : Blo 2087435 3133175 := bstep (se 1 (by rfl) ⟨2349881, by rfl⟩ : syracuseStep 3133175 = 4699763) B4699763
theorem B2088783 : Blo 2087435 2088783 := bstep (se 1 (by rfl) ⟨1566587, by rfl⟩ : syracuseStep 2088783 = 3133175) B3133175
theorem B3133181 : Blo 2087435 3133181 := bbase (se 3 (by rfl) ⟨587471, by rfl⟩ : syracuseStep 3133181 = 1174943) (by norm_num)
theorem B2088787 : Blo 2087435 2088787 := bstep (se 1 (by rfl) ⟨1566590, by rfl⟩ : syracuseStep 2088787 = 3133181) B3133181
theorem B4699781 : Blo 2087435 4699781 := bbase (se 4 (by rfl) ⟨440604, by rfl⟩ : syracuseStep 4699781 = 881209) (by norm_num)
theorem B3133187 : Blo 2087435 3133187 := bstep (se 1 (by rfl) ⟨2349890, by rfl⟩ : syracuseStep 3133187 = 4699781) B4699781
theorem B2088791 : Blo 2087435 2088791 := bstep (se 1 (by rfl) ⟨1566593, by rfl⟩ : syracuseStep 2088791 = 3133187) B3133187
theorem B5018773 : Blo 2087435 5018773 := bbase (se 6 (by rfl) ⟨117627, by rfl⟩ : syracuseStep 5018773 = 235255) (by norm_num)
theorem B6691697 : Blo 2087435 6691697 := bstep (se 2 (by rfl) ⟨2509386, by rfl⟩ : syracuseStep 6691697 = 5018773) B5018773
theorem B4461131 : Blo 2087435 4461131 := bstep (se 1 (by rfl) ⟨3345848, by rfl⟩ : syracuseStep 4461131 = 6691697) B6691697
theorem B2974087 : Blo 2087435 2974087 := bstep (se 1 (by rfl) ⟨2230565, by rfl⟩ : syracuseStep 2974087 = 4461131) B4461131
theorem B3965449 : Blo 2087435 3965449 := bstep (se 2 (by rfl) ⟨1487043, by rfl⟩ : syracuseStep 3965449 = 2974087) B2974087
theorem B5287265 : Blo 2087435 5287265 := bstep (se 2 (by rfl) ⟨1982724, by rfl⟩ : syracuseStep 5287265 = 3965449) B3965449
theorem B3524843 : Blo 2087435 3524843 := bstep (se 1 (by rfl) ⟨2643632, by rfl⟩ : syracuseStep 3524843 = 5287265) B5287265
theorem B2349895 : Blo 2087435 2349895 := bstep (se 1 (by rfl) ⟨1762421, by rfl⟩ : syracuseStep 2349895 = 3524843) B3524843
theorem B3133193 : Blo 2087435 3133193 := bstep (se 2 (by rfl) ⟨1174947, by rfl⟩ : syracuseStep 3133193 = 2349895) B2349895
theorem B2088795 : Blo 2087435 2088795 := bstep (se 1 (by rfl) ⟨1566596, by rfl⟩ : syracuseStep 2088795 = 3133193) B3133193
theorem B10574549 : Blo 2087435 10574549 := bbase (se 7 (by rfl) ⟨123920, by rfl⟩ : syracuseStep 10574549 = 247841) (by norm_num)
theorem B7049699 : Blo 2087435 7049699 := bstep (se 1 (by rfl) ⟨5287274, by rfl⟩ : syracuseStep 7049699 = 10574549) B10574549
theorem B4699799 : Blo 2087435 4699799 := bstep (se 1 (by rfl) ⟨3524849, by rfl⟩ : syracuseStep 4699799 = 7049699) B7049699
theorem B3133199 : Blo 2087435 3133199 := bstep (se 1 (by rfl) ⟨2349899, by rfl⟩ : syracuseStep 3133199 = 4699799) B4699799
theorem B2088799 : Blo 2087435 2088799 := bstep (se 1 (by rfl) ⟨1566599, by rfl⟩ : syracuseStep 2088799 = 3133199) B3133199
theorem B3133205 : Blo 2087435 3133205 := bbase (se 6 (by rfl) ⟨73434, by rfl⟩ : syracuseStep 3133205 = 146869) (by norm_num)
theorem B2088803 : Blo 2087435 2088803 := bstep (se 1 (by rfl) ⟨1566602, by rfl⟩ : syracuseStep 2088803 = 3133205) B3133205
theorem B4234613 : Blo 2087435 4234613 := bbase (se 5 (by rfl) ⟨198497, by rfl⟩ : syracuseStep 4234613 = 396995) (by norm_num)
theorem B11292301 : Blo 2087435 11292301 := bstep (se 3 (by rfl) ⟨2117306, by rfl⟩ : syracuseStep 11292301 = 4234613) B4234613
theorem B60225605 : Blo 2087435 60225605 := bstep (se 4 (by rfl) ⟨5646150, by rfl⟩ : syracuseStep 60225605 = 11292301) B11292301
theorem B40150403 : Blo 2087435 40150403 := bstep (se 1 (by rfl) ⟨30112802, by rfl⟩ : syracuseStep 40150403 = 60225605) B60225605
theorem B26766935 : Blo 2087435 26766935 := bstep (se 1 (by rfl) ⟨20075201, by rfl⟩ : syracuseStep 26766935 = 40150403) B40150403
theorem B17844623 : Blo 2087435 17844623 := bstep (se 1 (by rfl) ⟨13383467, by rfl⟩ : syracuseStep 17844623 = 26766935) B26766935
theorem B11896415 : Blo 2087435 11896415 := bstep (se 1 (by rfl) ⟨8922311, by rfl⟩ : syracuseStep 11896415 = 17844623) B17844623
theorem B7930943 : Blo 2087435 7930943 := bstep (se 1 (by rfl) ⟨5948207, by rfl⟩ : syracuseStep 7930943 = 11896415) B11896415
theorem B5287295 : Blo 2087435 5287295 := bstep (se 1 (by rfl) ⟨3965471, by rfl⟩ : syracuseStep 5287295 = 7930943) B7930943
theorem B3524863 : Blo 2087435 3524863 := bstep (se 1 (by rfl) ⟨2643647, by rfl⟩ : syracuseStep 3524863 = 5287295) B5287295
theorem B4699817 : Blo 2087435 4699817 := bstep (se 2 (by rfl) ⟨1762431, by rfl⟩ : syracuseStep 4699817 = 3524863) B3524863
theorem B3133211 : Blo 2087435 3133211 := bstep (se 1 (by rfl) ⟨2349908, by rfl⟩ : syracuseStep 3133211 = 4699817) B4699817
theorem B2088807 : Blo 2087435 2088807 := bstep (se 1 (by rfl) ⟨1566605, by rfl⟩ : syracuseStep 2088807 = 3133211) B3133211
theorem B2349913 : Blo 2087435 2349913 := bbase (se 2 (by rfl) ⟨881217, by rfl⟩ : syracuseStep 2349913 = 1762435) (by norm_num)
theorem B3133217 : Blo 2087435 3133217 := bstep (se 2 (by rfl) ⟨1174956, by rfl⟩ : syracuseStep 3133217 = 2349913) B2349913
theorem B2088811 : Blo 2087435 2088811 := bstep (se 1 (by rfl) ⟨1566608, by rfl⟩ : syracuseStep 2088811 = 3133217) B3133217
theorem B4461173 : Blo 2087435 4461173 := bbase (se 5 (by rfl) ⟨209117, by rfl⟩ : syracuseStep 4461173 = 418235) (by norm_num)
theorem B2974115 : Blo 2087435 2974115 := bstep (se 1 (by rfl) ⟨2230586, by rfl⟩ : syracuseStep 2974115 = 4461173) B4461173
theorem B7930973 : Blo 2087435 7930973 := bstep (se 3 (by rfl) ⟨1487057, by rfl⟩ : syracuseStep 7930973 = 2974115) B2974115
theorem B5287315 : Blo 2087435 5287315 := bstep (se 1 (by rfl) ⟨3965486, by rfl⟩ : syracuseStep 5287315 = 7930973) B7930973
theorem B7049753 : Blo 2087435 7049753 := bstep (se 2 (by rfl) ⟨2643657, by rfl⟩ : syracuseStep 7049753 = 5287315) B5287315
theorem B4699835 : Blo 2087435 4699835 := bstep (se 1 (by rfl) ⟨3524876, by rfl⟩ : syracuseStep 4699835 = 7049753) B7049753
theorem B3133223 : Blo 2087435 3133223 := bstep (se 1 (by rfl) ⟨2349917, by rfl⟩ : syracuseStep 3133223 = 4699835) B4699835
theorem B2088815 : Blo 2087435 2088815 := bstep (se 1 (by rfl) ⟨1566611, by rfl⟩ : syracuseStep 2088815 = 3133223) B3133223
theorem B3133229 : Blo 2087435 3133229 := bbase (se 3 (by rfl) ⟨587480, by rfl⟩ : syracuseStep 3133229 = 1174961) (by norm_num)
theorem B2088819 : Blo 2087435 2088819 := bstep (se 1 (by rfl) ⟨1566614, by rfl⟩ : syracuseStep 2088819 = 3133229) B3133229
theorem B4699853 : Blo 2087435 4699853 := bbase (se 3 (by rfl) ⟨881222, by rfl⟩ : syracuseStep 4699853 = 1762445) (by norm_num)
theorem B3133235 : Blo 2087435 3133235 := bstep (se 1 (by rfl) ⟨2349926, by rfl⟩ : syracuseStep 3133235 = 4699853) B4699853
theorem B2088823 : Blo 2087435 2088823 := bstep (se 1 (by rfl) ⟨1566617, by rfl⟩ : syracuseStep 2088823 = 3133235) B3133235
theorem B2643673 : Blo 2087435 2643673 := bbase (se 2 (by rfl) ⟨991377, by rfl⟩ : syracuseStep 2643673 = 1982755) (by norm_num)
theorem B3524897 : Blo 2087435 3524897 := bstep (se 2 (by rfl) ⟨1321836, by rfl⟩ : syracuseStep 3524897 = 2643673) B2643673
theorem B2349931 : Blo 2087435 2349931 := bstep (se 1 (by rfl) ⟨1762448, by rfl⟩ : syracuseStep 2349931 = 3524897) B3524897
theorem B3133241 : Blo 2087435 3133241 := bstep (se 2 (by rfl) ⟨1174965, by rfl⟩ : syracuseStep 3133241 = 2349931) B2349931
theorem B2088827 : Blo 2087435 2088827 := bstep (se 1 (by rfl) ⟨1566620, by rfl⟩ : syracuseStep 2088827 = 3133241) B3133241
theorem B2509429 : Blo 2087435 2509429 := bbase (se 5 (by rfl) ⟨117629, by rfl⟩ : syracuseStep 2509429 = 235259) (by norm_num)
theorem B3345905 : Blo 2087435 3345905 := bstep (se 2 (by rfl) ⟨1254714, by rfl⟩ : syracuseStep 3345905 = 2509429) B2509429
theorem B8922413 : Blo 2087435 8922413 := bstep (se 3 (by rfl) ⟨1672952, by rfl⟩ : syracuseStep 8922413 = 3345905) B3345905
theorem B23793101 : Blo 2087435 23793101 := bstep (se 3 (by rfl) ⟨4461206, by rfl⟩ : syracuseStep 23793101 = 8922413) B8922413
theorem B15862067 : Blo 2087435 15862067 := bstep (se 1 (by rfl) ⟨11896550, by rfl⟩ : syracuseStep 15862067 = 23793101) B23793101
theorem B10574711 : Blo 2087435 10574711 := bstep (se 1 (by rfl) ⟨7931033, by rfl⟩ : syracuseStep 10574711 = 15862067) B15862067
theorem B7049807 : Blo 2087435 7049807 := bstep (se 1 (by rfl) ⟨5287355, by rfl⟩ : syracuseStep 7049807 = 10574711) B10574711
theorem B4699871 : Blo 2087435 4699871 := bstep (se 1 (by rfl) ⟨3524903, by rfl⟩ : syracuseStep 4699871 = 7049807) B7049807
theorem B3133247 : Blo 2087435 3133247 := bstep (se 1 (by rfl) ⟨2349935, by rfl⟩ : syracuseStep 3133247 = 4699871) B4699871
theorem B2088831 : Blo 2087435 2088831 := bstep (se 1 (by rfl) ⟨1566623, by rfl⟩ : syracuseStep 2088831 = 3133247) B3133247
theorem B3133253 : Blo 2087435 3133253 := bbase (se 4 (by rfl) ⟨293742, by rfl⟩ : syracuseStep 3133253 = 587485) (by norm_num)
theorem B2088835 : Blo 2087435 2088835 := bstep (se 1 (by rfl) ⟨1566626, by rfl⟩ : syracuseStep 2088835 = 3133253) B3133253
theorem B3524917 : Blo 2087435 3524917 := bbase (se 5 (by rfl) ⟨165230, by rfl⟩ : syracuseStep 3524917 = 330461) (by norm_num)
theorem B4699889 : Blo 2087435 4699889 := bstep (se 2 (by rfl) ⟨1762458, by rfl⟩ : syracuseStep 4699889 = 3524917) B3524917
theorem B3133259 : Blo 2087435 3133259 := bstep (se 1 (by rfl) ⟨2349944, by rfl⟩ : syracuseStep 3133259 = 4699889) B4699889
theorem B2088839 : Blo 2087435 2088839 := bstep (se 1 (by rfl) ⟨1566629, by rfl⟩ : syracuseStep 2088839 = 3133259) B3133259
theorem B2349949 : Blo 2087435 2349949 := bbase (se 3 (by rfl) ⟨440615, by rfl⟩ : syracuseStep 2349949 = 881231) (by norm_num)
theorem B3133265 : Blo 2087435 3133265 := bstep (se 2 (by rfl) ⟨1174974, by rfl⟩ : syracuseStep 3133265 = 2349949) B2349949
theorem B2088843 : Blo 2087435 2088843 := bstep (se 1 (by rfl) ⟨1566632, by rfl⟩ : syracuseStep 2088843 = 3133265) B3133265
theorem B7049861 : Blo 2087435 7049861 := bbase (se 4 (by rfl) ⟨660924, by rfl⟩ : syracuseStep 7049861 = 1321849) (by norm_num)
theorem B4699907 : Blo 2087435 4699907 := bstep (se 1 (by rfl) ⟨3524930, by rfl⟩ : syracuseStep 4699907 = 7049861) B7049861
theorem B3133271 : Blo 2087435 3133271 := bstep (se 1 (by rfl) ⟨2349953, by rfl⟩ : syracuseStep 3133271 = 4699907) B4699907
theorem B2088847 : Blo 2087435 2088847 := bstep (se 1 (by rfl) ⟨1566635, by rfl⟩ : syracuseStep 2088847 = 3133271) B3133271
theorem B3133277 : Blo 2087435 3133277 := bbase (se 3 (by rfl) ⟨587489, by rfl⟩ : syracuseStep 3133277 = 1174979) (by norm_num)
theorem B2088851 : Blo 2087435 2088851 := bstep (se 1 (by rfl) ⟨1566638, by rfl⟩ : syracuseStep 2088851 = 3133277) B3133277
theorem B4699925 : Blo 2087435 4699925 := bbase (se 6 (by rfl) ⟨110154, by rfl⟩ : syracuseStep 4699925 = 220309) (by norm_num)
theorem B3133283 : Blo 2087435 3133283 := bstep (se 1 (by rfl) ⟨2349962, by rfl⟩ : syracuseStep 3133283 = 4699925) B4699925
theorem B2088855 : Blo 2087435 2088855 := bstep (se 1 (by rfl) ⟨1566641, by rfl⟩ : syracuseStep 2088855 = 3133283) B3133283
theorem B7931141 : Blo 2087435 7931141 := bbase (se 4 (by rfl) ⟨743544, by rfl⟩ : syracuseStep 7931141 = 1487089) (by norm_num)
theorem B5287427 : Blo 2087435 5287427 := bstep (se 1 (by rfl) ⟨3965570, by rfl⟩ : syracuseStep 5287427 = 7931141) B7931141
theorem B3524951 : Blo 2087435 3524951 := bstep (se 1 (by rfl) ⟨2643713, by rfl⟩ : syracuseStep 3524951 = 5287427) B5287427
theorem B2349967 : Blo 2087435 2349967 := bstep (se 1 (by rfl) ⟨1762475, by rfl⟩ : syracuseStep 2349967 = 3524951) B3524951
theorem B3133289 : Blo 2087435 3133289 := bstep (se 2 (by rfl) ⟨1174983, by rfl⟩ : syracuseStep 3133289 = 2349967) B2349967
theorem B2088859 : Blo 2087435 2088859 := bstep (se 1 (by rfl) ⟨1566644, by rfl⟩ : syracuseStep 2088859 = 3133289) B3133289
theorem B6029525 : Blo 2087435 6029525 := bbase (se 7 (by rfl) ⟨70658, by rfl⟩ : syracuseStep 6029525 = 141317) (by norm_num)
theorem B16078733 : Blo 2087435 16078733 := bstep (se 3 (by rfl) ⟨3014762, by rfl⟩ : syracuseStep 16078733 = 6029525) B6029525
theorem B10719155 : Blo 2087435 10719155 := bstep (se 1 (by rfl) ⟨8039366, by rfl⟩ : syracuseStep 10719155 = 16078733) B16078733
theorem B7146103 : Blo 2087435 7146103 := bstep (se 1 (by rfl) ⟨5359577, by rfl⟩ : syracuseStep 7146103 = 10719155) B10719155
theorem B9528137 : Blo 2087435 9528137 := bstep (se 2 (by rfl) ⟨3573051, by rfl⟩ : syracuseStep 9528137 = 7146103) B7146103
theorem B6352091 : Blo 2087435 6352091 := bstep (se 1 (by rfl) ⟨4764068, by rfl⟩ : syracuseStep 6352091 = 9528137) B9528137
theorem B4234727 : Blo 2087435 4234727 := bstep (se 1 (by rfl) ⟨3176045, by rfl⟩ : syracuseStep 4234727 = 6352091) B6352091
theorem B11292605 : Blo 2087435 11292605 := bstep (se 3 (by rfl) ⟨2117363, by rfl⟩ : syracuseStep 11292605 = 4234727) B4234727
theorem B7528403 : Blo 2087435 7528403 := bstep (se 1 (by rfl) ⟨5646302, by rfl⟩ : syracuseStep 7528403 = 11292605) B11292605
theorem B5018935 : Blo 2087435 5018935 := bstep (se 1 (by rfl) ⟨3764201, by rfl⟩ : syracuseStep 5018935 = 7528403) B7528403
theorem B6691913 : Blo 2087435 6691913 := bstep (se 2 (by rfl) ⟨2509467, by rfl⟩ : syracuseStep 6691913 = 5018935) B5018935
theorem B4461275 : Blo 2087435 4461275 := bstep (se 1 (by rfl) ⟨3345956, by rfl⟩ : syracuseStep 4461275 = 6691913) B6691913
theorem B11896733 : Blo 2087435 11896733 := bstep (se 3 (by rfl) ⟨2230637, by rfl⟩ : syracuseStep 11896733 = 4461275) B4461275
theorem B7931155 : Blo 2087435 7931155 := bstep (se 1 (by rfl) ⟨5948366, by rfl⟩ : syracuseStep 7931155 = 11896733) B11896733
theorem B10574873 : Blo 2087435 10574873 := bstep (se 2 (by rfl) ⟨3965577, by rfl⟩ : syracuseStep 10574873 = 7931155) B7931155
theorem B7049915 : Blo 2087435 7049915 := bstep (se 1 (by rfl) ⟨5287436, by rfl⟩ : syracuseStep 7049915 = 10574873) B10574873
theorem B4699943 : Blo 2087435 4699943 := bstep (se 1 (by rfl) ⟨3524957, by rfl⟩ : syracuseStep 4699943 = 7049915) B7049915
theorem B3133295 : Blo 2087435 3133295 := bstep (se 1 (by rfl) ⟨2349971, by rfl⟩ : syracuseStep 3133295 = 4699943) B4699943
theorem B2088863 : Blo 2087435 2088863 := bstep (se 1 (by rfl) ⟨1566647, by rfl⟩ : syracuseStep 2088863 = 3133295) B3133295
theorem B3133301 : Blo 2087435 3133301 := bbase (se 5 (by rfl) ⟨146873, by rfl⟩ : syracuseStep 3133301 = 293747) (by norm_num)
theorem B2088867 : Blo 2087435 2088867 := bstep (se 1 (by rfl) ⟨1566650, by rfl⟩ : syracuseStep 2088867 = 3133301) B3133301
theorem B4461293 : Blo 2087435 4461293 := bbase (se 3 (by rfl) ⟨836492, by rfl⟩ : syracuseStep 4461293 = 1672985) (by norm_num)
theorem B2974195 : Blo 2087435 2974195 := bstep (se 1 (by rfl) ⟨2230646, by rfl⟩ : syracuseStep 2974195 = 4461293) B4461293
theorem B3965593 : Blo 2087435 3965593 := bstep (se 2 (by rfl) ⟨1487097, by rfl⟩ : syracuseStep 3965593 = 2974195) B2974195
theorem B5287457 : Blo 2087435 5287457 := bstep (se 2 (by rfl) ⟨1982796, by rfl⟩ : syracuseStep 5287457 = 3965593) B3965593
theorem B3524971 : Blo 2087435 3524971 := bstep (se 1 (by rfl) ⟨2643728, by rfl⟩ : syracuseStep 3524971 = 5287457) B5287457
theorem B4699961 : Blo 2087435 4699961 := bstep (se 2 (by rfl) ⟨1762485, by rfl⟩ : syracuseStep 4699961 = 3524971) B3524971
theorem B3133307 : Blo 2087435 3133307 := bstep (se 1 (by rfl) ⟨2349980, by rfl⟩ : syracuseStep 3133307 = 4699961) B4699961
theorem B2088871 : Blo 2087435 2088871 := bstep (se 1 (by rfl) ⟨1566653, by rfl⟩ : syracuseStep 2088871 = 3133307) B3133307
theorem B2349985 : Blo 2087435 2349985 := bbase (se 2 (by rfl) ⟨881244, by rfl⟩ : syracuseStep 2349985 = 1762489) (by norm_num)
theorem B3133313 : Blo 2087435 3133313 := bstep (se 2 (by rfl) ⟨1174992, by rfl⟩ : syracuseStep 3133313 = 2349985) B2349985
theorem B2088875 : Blo 2087435 2088875 := bstep (se 1 (by rfl) ⟨1566656, by rfl⟩ : syracuseStep 2088875 = 3133313) B3133313
theorem B5287477 : Blo 2087435 5287477 := bbase (se 5 (by rfl) ⟨247850, by rfl⟩ : syracuseStep 5287477 = 495701) (by norm_num)
theorem B7049969 : Blo 2087435 7049969 := bstep (se 2 (by rfl) ⟨2643738, by rfl⟩ : syracuseStep 7049969 = 5287477) B5287477
theorem B4699979 : Blo 2087435 4699979 := bstep (se 1 (by rfl) ⟨3524984, by rfl⟩ : syracuseStep 4699979 = 7049969) B7049969
theorem B3133319 : Blo 2087435 3133319 := bstep (se 1 (by rfl) ⟨2349989, by rfl⟩ : syracuseStep 3133319 = 4699979) B4699979
theorem B2088879 : Blo 2087435 2088879 := bstep (se 1 (by rfl) ⟨1566659, by rfl⟩ : syracuseStep 2088879 = 3133319) B3133319
theorem B3133325 : Blo 2087435 3133325 := bbase (se 3 (by rfl) ⟨587498, by rfl⟩ : syracuseStep 3133325 = 1174997) (by norm_num)
theorem B2088883 : Blo 2087435 2088883 := bstep (se 1 (by rfl) ⟨1566662, by rfl⟩ : syracuseStep 2088883 = 3133325) B3133325
theorem B4699997 : Blo 2087435 4699997 := bbase (se 3 (by rfl) ⟨881249, by rfl⟩ : syracuseStep 4699997 = 1762499) (by norm_num)
theorem B3133331 : Blo 2087435 3133331 := bstep (se 1 (by rfl) ⟨2349998, by rfl⟩ : syracuseStep 3133331 = 4699997) B4699997
theorem B2088887 : Blo 2087435 2088887 := bstep (se 1 (by rfl) ⟨1566665, by rfl⟩ : syracuseStep 2088887 = 3133331) B3133331
theorem B3525005 : Blo 2087435 3525005 := bbase (se 3 (by rfl) ⟨660938, by rfl⟩ : syracuseStep 3525005 = 1321877) (by norm_num)
theorem B2350003 : Blo 2087435 2350003 := bstep (se 1 (by rfl) ⟨1762502, by rfl⟩ : syracuseStep 2350003 = 3525005) B3525005
theorem B3133337 : Blo 2087435 3133337 := bstep (se 2 (by rfl) ⟨1175001, by rfl⟩ : syracuseStep 3133337 = 2350003) B2350003
theorem B2088891 : Blo 2087435 2088891 := bstep (se 1 (by rfl) ⟨1566668, by rfl⟩ : syracuseStep 2088891 = 3133337) B3133337
theorem B10719317 : Blo 2087435 10719317 := bbase (se 8 (by rfl) ⟨62808, by rfl⟩ : syracuseStep 10719317 = 125617) (by norm_num)
theorem B7146211 : Blo 2087435 7146211 := bstep (se 1 (by rfl) ⟨5359658, by rfl⟩ : syracuseStep 7146211 = 10719317) B10719317
theorem B9528281 : Blo 2087435 9528281 := bstep (se 2 (by rfl) ⟨3573105, by rfl⟩ : syracuseStep 9528281 = 7146211) B7146211
theorem B6352187 : Blo 2087435 6352187 := bstep (se 1 (by rfl) ⟨4764140, by rfl⟩ : syracuseStep 6352187 = 9528281) B9528281
theorem B16939165 : Blo 2087435 16939165 := bstep (se 3 (by rfl) ⟨3176093, by rfl⟩ : syracuseStep 16939165 = 6352187) B6352187
theorem B22585553 : Blo 2087435 22585553 := bstep (se 2 (by rfl) ⟨8469582, by rfl⟩ : syracuseStep 22585553 = 16939165) B16939165
theorem B15057035 : Blo 2087435 15057035 := bstep (se 1 (by rfl) ⟨11292776, by rfl⟩ : syracuseStep 15057035 = 22585553) B22585553
theorem B10038023 : Blo 2087435 10038023 := bstep (se 1 (by rfl) ⟨7528517, by rfl⟩ : syracuseStep 10038023 = 15057035) B15057035
theorem B6692015 : Blo 2087435 6692015 := bstep (se 1 (by rfl) ⟨5019011, by rfl⟩ : syracuseStep 6692015 = 10038023) B10038023
theorem B17845373 : Blo 2087435 17845373 := bstep (se 3 (by rfl) ⟨3346007, by rfl⟩ : syracuseStep 17845373 = 6692015) B6692015
theorem B11896915 : Blo 2087435 11896915 := bstep (se 1 (by rfl) ⟨8922686, by rfl⟩ : syracuseStep 11896915 = 17845373) B17845373
theorem B15862553 : Blo 2087435 15862553 := bstep (se 2 (by rfl) ⟨5948457, by rfl⟩ : syracuseStep 15862553 = 11896915) B11896915
theorem B10575035 : Blo 2087435 10575035 := bstep (se 1 (by rfl) ⟨7931276, by rfl⟩ : syracuseStep 10575035 = 15862553) B15862553
theorem B7050023 : Blo 2087435 7050023 := bstep (se 1 (by rfl) ⟨5287517, by rfl⟩ : syracuseStep 7050023 = 10575035) B10575035
theorem B4700015 : Blo 2087435 4700015 := bstep (se 1 (by rfl) ⟨3525011, by rfl⟩ : syracuseStep 4700015 = 7050023) B7050023
theorem B3133343 : Blo 2087435 3133343 := bstep (se 1 (by rfl) ⟨2350007, by rfl⟩ : syracuseStep 3133343 = 4700015) B4700015
theorem B2088895 : Blo 2087435 2088895 := bstep (se 1 (by rfl) ⟨1566671, by rfl⟩ : syracuseStep 2088895 = 3133343) B3133343
theorem B3133349 : Blo 2087435 3133349 := bbase (se 4 (by rfl) ⟨293751, by rfl⟩ : syracuseStep 3133349 = 587503) (by norm_num)
theorem B2088899 : Blo 2087435 2088899 := bstep (se 1 (by rfl) ⟨1566674, by rfl⟩ : syracuseStep 2088899 = 3133349) B3133349
theorem B2643769 : Blo 2087435 2643769 := bbase (se 2 (by rfl) ⟨991413, by rfl⟩ : syracuseStep 2643769 = 1982827) (by norm_num)
theorem B3525025 : Blo 2087435 3525025 := bstep (se 2 (by rfl) ⟨1321884, by rfl⟩ : syracuseStep 3525025 = 2643769) B2643769
theorem B4700033 : Blo 2087435 4700033 := bstep (se 2 (by rfl) ⟨1762512, by rfl⟩ : syracuseStep 4700033 = 3525025) B3525025
theorem B3133355 : Blo 2087435 3133355 := bstep (se 1 (by rfl) ⟨2350016, by rfl⟩ : syracuseStep 3133355 = 4700033) B4700033
theorem B2088903 : Blo 2087435 2088903 := bstep (se 1 (by rfl) ⟨1566677, by rfl⟩ : syracuseStep 2088903 = 3133355) B3133355
theorem B2350021 : Blo 2087435 2350021 := bbase (se 4 (by rfl) ⟨220314, by rfl⟩ : syracuseStep 2350021 = 440629) (by norm_num)
theorem B3133361 : Blo 2087435 3133361 := bstep (se 2 (by rfl) ⟨1175010, by rfl⟩ : syracuseStep 3133361 = 2350021) B2350021
theorem B2088907 : Blo 2087435 2088907 := bstep (se 1 (by rfl) ⟨1566680, by rfl⟩ : syracuseStep 2088907 = 3133361) B3133361
theorem B3965669 : Blo 2087435 3965669 := bbase (se 4 (by rfl) ⟨371781, by rfl⟩ : syracuseStep 3965669 = 743563) (by norm_num)
theorem B2643779 : Blo 2087435 2643779 := bstep (se 1 (by rfl) ⟨1982834, by rfl⟩ : syracuseStep 2643779 = 3965669) B3965669
theorem B7050077 : Blo 2087435 7050077 := bstep (se 3 (by rfl) ⟨1321889, by rfl⟩ : syracuseStep 7050077 = 2643779) B2643779
theorem B4700051 : Blo 2087435 4700051 := bstep (se 1 (by rfl) ⟨3525038, by rfl⟩ : syracuseStep 4700051 = 7050077) B7050077
theorem B3133367 : Blo 2087435 3133367 := bstep (se 1 (by rfl) ⟨2350025, by rfl⟩ : syracuseStep 3133367 = 4700051) B4700051
theorem B2088911 : Blo 2087435 2088911 := bstep (se 1 (by rfl) ⟨1566683, by rfl⟩ : syracuseStep 2088911 = 3133367) B3133367
theorem B3133373 : Blo 2087435 3133373 := bbase (se 3 (by rfl) ⟨587507, by rfl⟩ : syracuseStep 3133373 = 1175015) (by norm_num)
theorem B2088915 : Blo 2087435 2088915 := bstep (se 1 (by rfl) ⟨1566686, by rfl⟩ : syracuseStep 2088915 = 3133373) B3133373
theorem B4700069 : Blo 2087435 4700069 := bbase (se 4 (by rfl) ⟨440631, by rfl⟩ : syracuseStep 4700069 = 881263) (by norm_num)
theorem B3133379 : Blo 2087435 3133379 := bstep (se 1 (by rfl) ⟨2350034, by rfl⟩ : syracuseStep 3133379 = 4700069) B4700069
theorem B2088919 : Blo 2087435 2088919 := bstep (se 1 (by rfl) ⟨1566689, by rfl⟩ : syracuseStep 2088919 = 3133379) B3133379
theorem B5287589 : Blo 2087435 5287589 := bbase (se 4 (by rfl) ⟨495711, by rfl⟩ : syracuseStep 5287589 = 991423) (by norm_num)
theorem B3525059 : Blo 2087435 3525059 := bstep (se 1 (by rfl) ⟨2643794, by rfl⟩ : syracuseStep 3525059 = 5287589) B5287589
theorem B2350039 : Blo 2087435 2350039 := bstep (se 1 (by rfl) ⟨1762529, by rfl⟩ : syracuseStep 2350039 = 3525059) B3525059
theorem B3133385 : Blo 2087435 3133385 := bstep (se 2 (by rfl) ⟨1175019, by rfl⟩ : syracuseStep 3133385 = 2350039) B2350039
theorem B2088923 : Blo 2087435 2088923 := bstep (se 1 (by rfl) ⟨1566692, by rfl⟩ : syracuseStep 2088923 = 3133385) B3133385
theorem B5948549 : Blo 2087435 5948549 := bbase (se 4 (by rfl) ⟨557676, by rfl⟩ : syracuseStep 5948549 = 1115353) (by norm_num)
theorem B3965699 : Blo 2087435 3965699 := bstep (se 1 (by rfl) ⟨2974274, by rfl⟩ : syracuseStep 3965699 = 5948549) B5948549
theorem B10575197 : Blo 2087435 10575197 := bstep (se 3 (by rfl) ⟨1982849, by rfl⟩ : syracuseStep 10575197 = 3965699) B3965699
theorem B7050131 : Blo 2087435 7050131 := bstep (se 1 (by rfl) ⟨5287598, by rfl⟩ : syracuseStep 7050131 = 10575197) B10575197
theorem B4700087 : Blo 2087435 4700087 := bstep (se 1 (by rfl) ⟨3525065, by rfl⟩ : syracuseStep 4700087 = 7050131) B7050131
theorem B3133391 : Blo 2087435 3133391 := bstep (se 1 (by rfl) ⟨2350043, by rfl⟩ : syracuseStep 3133391 = 4700087) B4700087
theorem B2088927 : Blo 2087435 2088927 := bstep (se 1 (by rfl) ⟨1566695, by rfl⟩ : syracuseStep 2088927 = 3133391) B3133391
theorem B3133397 : Blo 2087435 3133397 := bbase (se 7 (by rfl) ⟨36719, by rfl⟩ : syracuseStep 3133397 = 73439) (by norm_num)
theorem B2088931 : Blo 2087435 2088931 := bstep (se 1 (by rfl) ⟨1566698, by rfl⟩ : syracuseStep 2088931 = 3133397) B3133397
theorem B7931429 : Blo 2087435 7931429 := bbase (se 4 (by rfl) ⟨743571, by rfl⟩ : syracuseStep 7931429 = 1487143) (by norm_num)
theorem B5287619 : Blo 2087435 5287619 := bstep (se 1 (by rfl) ⟨3965714, by rfl⟩ : syracuseStep 5287619 = 7931429) B7931429
theorem B3525079 : Blo 2087435 3525079 := bstep (se 1 (by rfl) ⟨2643809, by rfl⟩ : syracuseStep 3525079 = 5287619) B5287619
theorem B4700105 : Blo 2087435 4700105 := bstep (se 2 (by rfl) ⟨1762539, by rfl⟩ : syracuseStep 4700105 = 3525079) B3525079
theorem B3133403 : Blo 2087435 3133403 := bstep (se 1 (by rfl) ⟨2350052, by rfl⟩ : syracuseStep 3133403 = 4700105) B4700105
theorem B2088935 : Blo 2087435 2088935 := bstep (se 1 (by rfl) ⟨1566701, by rfl⟩ : syracuseStep 2088935 = 3133403) B3133403
theorem B2350057 : Blo 2087435 2350057 := bbase (se 2 (by rfl) ⟨881271, by rfl⟩ : syracuseStep 2350057 = 1762543) (by norm_num)
theorem B3133409 : Blo 2087435 3133409 := bstep (se 2 (by rfl) ⟨1175028, by rfl⟩ : syracuseStep 3133409 = 2350057) B2350057
theorem B2088939 : Blo 2087435 2088939 := bstep (se 1 (by rfl) ⟨1566704, by rfl⟩ : syracuseStep 2088939 = 3133409) B3133409
theorem B3346085 : Blo 2087435 3346085 := bbase (se 4 (by rfl) ⟨313695, by rfl⟩ : syracuseStep 3346085 = 627391) (by norm_num)
theorem B2230723 : Blo 2087435 2230723 := bstep (se 1 (by rfl) ⟨1673042, by rfl⟩ : syracuseStep 2230723 = 3346085) B3346085
theorem B11897189 : Blo 2087435 11897189 := bstep (se 4 (by rfl) ⟨1115361, by rfl⟩ : syracuseStep 11897189 = 2230723) B2230723
theorem B7931459 : Blo 2087435 7931459 := bstep (se 1 (by rfl) ⟨5948594, by rfl⟩ : syracuseStep 7931459 = 11897189) B11897189
theorem B5287639 : Blo 2087435 5287639 := bstep (se 1 (by rfl) ⟨3965729, by rfl⟩ : syracuseStep 5287639 = 7931459) B7931459
theorem B7050185 : Blo 2087435 7050185 := bstep (se 2 (by rfl) ⟨2643819, by rfl⟩ : syracuseStep 7050185 = 5287639) B5287639
theorem B4700123 : Blo 2087435 4700123 := bstep (se 1 (by rfl) ⟨3525092, by rfl⟩ : syracuseStep 4700123 = 7050185) B7050185
theorem B3133415 : Blo 2087435 3133415 := bstep (se 1 (by rfl) ⟨2350061, by rfl⟩ : syracuseStep 3133415 = 4700123) B4700123
theorem B2088943 : Blo 2087435 2088943 := bstep (se 1 (by rfl) ⟨1566707, by rfl⟩ : syracuseStep 2088943 = 3133415) B3133415
theorem B3133421 : Blo 2087435 3133421 := bbase (se 3 (by rfl) ⟨587516, by rfl⟩ : syracuseStep 3133421 = 1175033) (by norm_num)
theorem B2088947 : Blo 2087435 2088947 := bstep (se 1 (by rfl) ⟨1566710, by rfl⟩ : syracuseStep 2088947 = 3133421) B3133421
theorem B4700141 : Blo 2087435 4700141 := bbase (se 3 (by rfl) ⟨881276, by rfl⟩ : syracuseStep 4700141 = 1762553) (by norm_num)
theorem B3133427 : Blo 2087435 3133427 := bstep (se 1 (by rfl) ⟨2350070, by rfl⟩ : syracuseStep 3133427 = 4700141) B4700141
theorem B2088951 : Blo 2087435 2088951 := bstep (se 1 (by rfl) ⟨1566713, by rfl⟩ : syracuseStep 2088951 = 3133427) B3133427
theorem B2823277 : Blo 2087435 2823277 := bbase (se 3 (by rfl) ⟨529364, by rfl⟩ : syracuseStep 2823277 = 1058729) (by norm_num)
theorem B3764369 : Blo 2087435 3764369 := bstep (se 2 (by rfl) ⟨1411638, by rfl⟩ : syracuseStep 3764369 = 2823277) B2823277
theorem B2509579 : Blo 2087435 2509579 := bstep (se 1 (by rfl) ⟨1882184, by rfl⟩ : syracuseStep 2509579 = 3764369) B3764369
theorem B3346105 : Blo 2087435 3346105 := bstep (se 2 (by rfl) ⟨1254789, by rfl⟩ : syracuseStep 3346105 = 2509579) B2509579
theorem B4461473 : Blo 2087435 4461473 := bstep (se 2 (by rfl) ⟨1673052, by rfl⟩ : syracuseStep 4461473 = 3346105) B3346105
theorem B2974315 : Blo 2087435 2974315 := bstep (se 1 (by rfl) ⟨2230736, by rfl⟩ : syracuseStep 2974315 = 4461473) B4461473
theorem B3965753 : Blo 2087435 3965753 := bstep (se 2 (by rfl) ⟨1487157, by rfl⟩ : syracuseStep 3965753 = 2974315) B2974315
theorem B2643835 : Blo 2087435 2643835 := bstep (se 1 (by rfl) ⟨1982876, by rfl⟩ : syracuseStep 2643835 = 3965753) B3965753
theorem B3525113 : Blo 2087435 3525113 := bstep (se 2 (by rfl) ⟨1321917, by rfl⟩ : syracuseStep 3525113 = 2643835) B2643835
theorem B2350075 : Blo 2087435 2350075 := bstep (se 1 (by rfl) ⟨1762556, by rfl⟩ : syracuseStep 2350075 = 3525113) B3525113
theorem B3133433 : Blo 2087435 3133433 := bstep (se 2 (by rfl) ⟨1175037, by rfl⟩ : syracuseStep 3133433 = 2350075) B2350075
theorem B2088955 : Blo 2087435 2088955 := bstep (se 1 (by rfl) ⟨1566716, by rfl⟩ : syracuseStep 2088955 = 3133433) B3133433
theorem B21439285 : Blo 2087435 21439285 := bbase (se 5 (by rfl) ⟨1004966, by rfl⟩ : syracuseStep 21439285 = 2009933) (by norm_num)
theorem B114342853 : Blo 2087435 114342853 := bstep (se 4 (by rfl) ⟨10719642, by rfl⟩ : syracuseStep 114342853 = 21439285) B21439285
theorem B152457137 : Blo 2087435 152457137 := bstep (se 2 (by rfl) ⟨57171426, by rfl⟩ : syracuseStep 152457137 = 114342853) B114342853
theorem B101638091 : Blo 2087435 101638091 := bstep (se 1 (by rfl) ⟨76228568, by rfl⟩ : syracuseStep 101638091 = 152457137) B152457137
theorem B271034909 : Blo 2087435 271034909 := bstep (se 3 (by rfl) ⟨50819045, by rfl⟩ : syracuseStep 271034909 = 101638091) B101638091
theorem B180689939 : Blo 2087435 180689939 := bstep (se 1 (by rfl) ⟨135517454, by rfl⟩ : syracuseStep 180689939 = 271034909) B271034909
theorem B120459959 : Blo 2087435 120459959 := bstep (se 1 (by rfl) ⟨90344969, by rfl⟩ : syracuseStep 120459959 = 180689939) B180689939
theorem B80306639 : Blo 2087435 80306639 := bstep (se 1 (by rfl) ⟨60229979, by rfl⟩ : syracuseStep 80306639 = 120459959) B120459959
theorem B53537759 : Blo 2087435 53537759 := bstep (se 1 (by rfl) ⟨40153319, by rfl⟩ : syracuseStep 53537759 = 80306639) B80306639
theorem B35691839 : Blo 2087435 35691839 := bstep (se 1 (by rfl) ⟨26768879, by rfl⟩ : syracuseStep 35691839 = 53537759) B53537759
theorem B23794559 : Blo 2087435 23794559 := bstep (se 1 (by rfl) ⟨17845919, by rfl⟩ : syracuseStep 23794559 = 35691839) B35691839
theorem B15863039 : Blo 2087435 15863039 := bstep (se 1 (by rfl) ⟨11897279, by rfl⟩ : syracuseStep 15863039 = 23794559) B23794559
theorem B10575359 : Blo 2087435 10575359 := bstep (se 1 (by rfl) ⟨7931519, by rfl⟩ : syracuseStep 10575359 = 15863039) B15863039
theorem B7050239 : Blo 2087435 7050239 := bstep (se 1 (by rfl) ⟨5287679, by rfl⟩ : syracuseStep 7050239 = 10575359) B10575359
theorem B4700159 : Blo 2087435 4700159 := bstep (se 1 (by rfl) ⟨3525119, by rfl⟩ : syracuseStep 4700159 = 7050239) B7050239
theorem B3133439 : Blo 2087435 3133439 := bstep (se 1 (by rfl) ⟨2350079, by rfl⟩ : syracuseStep 3133439 = 4700159) B4700159
theorem B2088959 : Blo 2087435 2088959 := bstep (se 1 (by rfl) ⟨1566719, by rfl⟩ : syracuseStep 2088959 = 3133439) B3133439
theorem B3133445 : Blo 2087435 3133445 := bbase (se 4 (by rfl) ⟨293760, by rfl⟩ : syracuseStep 3133445 = 587521) (by norm_num)
theorem B2088963 : Blo 2087435 2088963 := bstep (se 1 (by rfl) ⟨1566722, by rfl⟩ : syracuseStep 2088963 = 3133445) B3133445
theorem B3525133 : Blo 2087435 3525133 := bbase (se 3 (by rfl) ⟨660962, by rfl⟩ : syracuseStep 3525133 = 1321925) (by norm_num)
theorem B4700177 : Blo 2087435 4700177 := bstep (se 2 (by rfl) ⟨1762566, by rfl⟩ : syracuseStep 4700177 = 3525133) B3525133
theorem B3133451 : Blo 2087435 3133451 := bstep (se 1 (by rfl) ⟨2350088, by rfl⟩ : syracuseStep 3133451 = 4700177) B4700177
theorem B2088967 : Blo 2087435 2088967 := bstep (se 1 (by rfl) ⟨1566725, by rfl⟩ : syracuseStep 2088967 = 3133451) B3133451
theorem B2350093 : Blo 2087435 2350093 := bbase (se 3 (by rfl) ⟨440642, by rfl⟩ : syracuseStep 2350093 = 881285) (by norm_num)
theorem B3133457 : Blo 2087435 3133457 := bstep (se 2 (by rfl) ⟨1175046, by rfl⟩ : syracuseStep 3133457 = 2350093) B2350093
theorem B2088971 : Blo 2087435 2088971 := bstep (se 1 (by rfl) ⟨1566728, by rfl⟩ : syracuseStep 2088971 = 3133457) B3133457
theorem B7050293 : Blo 2087435 7050293 := bbase (se 5 (by rfl) ⟨330482, by rfl⟩ : syracuseStep 7050293 = 660965) (by norm_num)
theorem B4700195 : Blo 2087435 4700195 := bstep (se 1 (by rfl) ⟨3525146, by rfl⟩ : syracuseStep 4700195 = 7050293) B7050293
theorem B3133463 : Blo 2087435 3133463 := bstep (se 1 (by rfl) ⟨2350097, by rfl⟩ : syracuseStep 3133463 = 4700195) B4700195
theorem B2088975 : Blo 2087435 2088975 := bstep (se 1 (by rfl) ⟨1566731, by rfl⟩ : syracuseStep 2088975 = 3133463) B3133463
theorem B3133469 : Blo 2087435 3133469 := bbase (se 3 (by rfl) ⟨587525, by rfl⟩ : syracuseStep 3133469 = 1175051) (by norm_num)
theorem B2088979 : Blo 2087435 2088979 := bstep (se 1 (by rfl) ⟨1566734, by rfl⟩ : syracuseStep 2088979 = 3133469) B3133469
theorem B4700213 : Blo 2087435 4700213 := bbase (se 5 (by rfl) ⟨220322, by rfl⟩ : syracuseStep 4700213 = 440645) (by norm_num)
theorem B3133475 : Blo 2087435 3133475 := bstep (se 1 (by rfl) ⟨2350106, by rfl⟩ : syracuseStep 3133475 = 4700213) B4700213
theorem B2088983 : Blo 2087435 2088983 := bstep (se 1 (by rfl) ⟨1566737, by rfl⟩ : syracuseStep 2088983 = 3133475) B3133475
theorem B6352469 : Blo 2087435 6352469 := bbase (se 8 (by rfl) ⟨37221, by rfl⟩ : syracuseStep 6352469 = 74443) (by norm_num)
theorem B4234979 : Blo 2087435 4234979 := bstep (se 1 (by rfl) ⟨3176234, by rfl⟩ : syracuseStep 4234979 = 6352469) B6352469
theorem B2823319 : Blo 2087435 2823319 := bstep (se 1 (by rfl) ⟨2117489, by rfl⟩ : syracuseStep 2823319 = 4234979) B4234979
theorem B15057701 : Blo 2087435 15057701 := bstep (se 4 (by rfl) ⟨1411659, by rfl⟩ : syracuseStep 15057701 = 2823319) B2823319
theorem B10038467 : Blo 2087435 10038467 := bstep (se 1 (by rfl) ⟨7528850, by rfl⟩ : syracuseStep 10038467 = 15057701) B15057701
theorem B6692311 : Blo 2087435 6692311 := bstep (se 1 (by rfl) ⟨5019233, by rfl⟩ : syracuseStep 6692311 = 10038467) B10038467
theorem B8923081 : Blo 2087435 8923081 := bstep (se 2 (by rfl) ⟨3346155, by rfl⟩ : syracuseStep 8923081 = 6692311) B6692311
theorem B11897441 : Blo 2087435 11897441 := bstep (se 2 (by rfl) ⟨4461540, by rfl⟩ : syracuseStep 11897441 = 8923081) B8923081
theorem B7931627 : Blo 2087435 7931627 := bstep (se 1 (by rfl) ⟨5948720, by rfl⟩ : syracuseStep 7931627 = 11897441) B11897441
theorem B5287751 : Blo 2087435 5287751 := bstep (se 1 (by rfl) ⟨3965813, by rfl⟩ : syracuseStep 5287751 = 7931627) B7931627
theorem B3525167 : Blo 2087435 3525167 := bstep (se 1 (by rfl) ⟨2643875, by rfl⟩ : syracuseStep 3525167 = 5287751) B5287751
theorem B2350111 : Blo 2087435 2350111 := bstep (se 1 (by rfl) ⟨1762583, by rfl⟩ : syracuseStep 2350111 = 3525167) B3525167
theorem B3133481 : Blo 2087435 3133481 := bstep (se 2 (by rfl) ⟨1175055, by rfl⟩ : syracuseStep 3133481 = 2350111) B2350111
theorem B2088987 : Blo 2087435 2088987 := bstep (se 1 (by rfl) ⟨1566740, by rfl⟩ : syracuseStep 2088987 = 3133481) B3133481
theorem B10038485 : Blo 2087435 10038485 := bbase (se 7 (by rfl) ⟨117638, by rfl⟩ : syracuseStep 10038485 = 235277) (by norm_num)
theorem B6692323 : Blo 2087435 6692323 := bstep (se 1 (by rfl) ⟨5019242, by rfl⟩ : syracuseStep 6692323 = 10038485) B10038485
theorem B8923097 : Blo 2087435 8923097 := bstep (se 2 (by rfl) ⟨3346161, by rfl⟩ : syracuseStep 8923097 = 6692323) B6692323
theorem B5948731 : Blo 2087435 5948731 := bstep (se 1 (by rfl) ⟨4461548, by rfl⟩ : syracuseStep 5948731 = 8923097) B8923097
theorem B7931641 : Blo 2087435 7931641 := bstep (se 2 (by rfl) ⟨2974365, by rfl⟩ : syracuseStep 7931641 = 5948731) B5948731
theorem B10575521 : Blo 2087435 10575521 := bstep (se 2 (by rfl) ⟨3965820, by rfl⟩ : syracuseStep 10575521 = 7931641) B7931641
theorem B7050347 : Blo 2087435 7050347 := bstep (se 1 (by rfl) ⟨5287760, by rfl⟩ : syracuseStep 7050347 = 10575521) B10575521
theorem B4700231 : Blo 2087435 4700231 := bstep (se 1 (by rfl) ⟨3525173, by rfl⟩ : syracuseStep 4700231 = 7050347) B7050347
theorem B3133487 : Blo 2087435 3133487 := bstep (se 1 (by rfl) ⟨2350115, by rfl⟩ : syracuseStep 3133487 = 4700231) B4700231
theorem B2088991 : Blo 2087435 2088991 := bstep (se 1 (by rfl) ⟨1566743, by rfl⟩ : syracuseStep 2088991 = 3133487) B3133487
theorem B3133493 : Blo 2087435 3133493 := bbase (se 5 (by rfl) ⟨146882, by rfl⟩ : syracuseStep 3133493 = 293765) (by norm_num)
theorem B2088995 : Blo 2087435 2088995 := bstep (se 1 (by rfl) ⟨1566746, by rfl⟩ : syracuseStep 2088995 = 3133493) B3133493
theorem B5287781 : Blo 2087435 5287781 := bbase (se 4 (by rfl) ⟨495729, by rfl⟩ : syracuseStep 5287781 = 991459) (by norm_num)
theorem B3525187 : Blo 2087435 3525187 := bstep (se 1 (by rfl) ⟨2643890, by rfl⟩ : syracuseStep 3525187 = 5287781) B5287781
theorem B4700249 : Blo 2087435 4700249 := bstep (se 2 (by rfl) ⟨1762593, by rfl⟩ : syracuseStep 4700249 = 3525187) B3525187
theorem B3133499 : Blo 2087435 3133499 := bstep (se 1 (by rfl) ⟨2350124, by rfl⟩ : syracuseStep 3133499 = 4700249) B4700249
theorem B2088999 : Blo 2087435 2088999 := bstep (se 1 (by rfl) ⟨1566749, by rfl⟩ : syracuseStep 2088999 = 3133499) B3133499
theorem B2350129 : Blo 2087435 2350129 := bbase (se 2 (by rfl) ⟨881298, by rfl⟩ : syracuseStep 2350129 = 1762597) (by norm_num)
theorem B3133505 : Blo 2087435 3133505 := bstep (se 2 (by rfl) ⟨1175064, by rfl⟩ : syracuseStep 3133505 = 2350129) B2350129
theorem B2089003 : Blo 2087435 2089003 := bstep (se 1 (by rfl) ⟨1566752, by rfl⟩ : syracuseStep 2089003 = 3133505) B3133505
theorem B15057845 : Blo 2087435 15057845 := bbase (se 5 (by rfl) ⟨705836, by rfl⟩ : syracuseStep 15057845 = 1411673) (by norm_num)
theorem B10038563 : Blo 2087435 10038563 := bstep (se 1 (by rfl) ⟨7528922, by rfl⟩ : syracuseStep 10038563 = 15057845) B15057845
theorem B6692375 : Blo 2087435 6692375 := bstep (se 1 (by rfl) ⟨5019281, by rfl⟩ : syracuseStep 6692375 = 10038563) B10038563
theorem B4461583 : Blo 2087435 4461583 := bstep (se 1 (by rfl) ⟨3346187, by rfl⟩ : syracuseStep 4461583 = 6692375) B6692375
theorem B5948777 : Blo 2087435 5948777 := bstep (se 2 (by rfl) ⟨2230791, by rfl⟩ : syracuseStep 5948777 = 4461583) B4461583
theorem B3965851 : Blo 2087435 3965851 := bstep (se 1 (by rfl) ⟨2974388, by rfl⟩ : syracuseStep 3965851 = 5948777) B5948777
theorem B5287801 : Blo 2087435 5287801 := bstep (se 2 (by rfl) ⟨1982925, by rfl⟩ : syracuseStep 5287801 = 3965851) B3965851
theorem B7050401 : Blo 2087435 7050401 := bstep (se 2 (by rfl) ⟨2643900, by rfl⟩ : syracuseStep 7050401 = 5287801) B5287801
theorem B4700267 : Blo 2087435 4700267 := bstep (se 1 (by rfl) ⟨3525200, by rfl⟩ : syracuseStep 4700267 = 7050401) B7050401
theorem B3133511 : Blo 2087435 3133511 := bstep (se 1 (by rfl) ⟨2350133, by rfl⟩ : syracuseStep 3133511 = 4700267) B4700267
theorem B2089007 : Blo 2087435 2089007 := bstep (se 1 (by rfl) ⟨1566755, by rfl⟩ : syracuseStep 2089007 = 3133511) B3133511
theorem B3133517 : Blo 2087435 3133517 := bbase (se 3 (by rfl) ⟨587534, by rfl⟩ : syracuseStep 3133517 = 1175069) (by norm_num)
theorem B2089011 : Blo 2087435 2089011 := bstep (se 1 (by rfl) ⟨1566758, by rfl⟩ : syracuseStep 2089011 = 3133517) B3133517
theorem B4700285 : Blo 2087435 4700285 := bbase (se 3 (by rfl) ⟨881303, by rfl⟩ : syracuseStep 4700285 = 1762607) (by norm_num)
theorem B3133523 : Blo 2087435 3133523 := bstep (se 1 (by rfl) ⟨2350142, by rfl⟩ : syracuseStep 3133523 = 4700285) B4700285
theorem B2089015 : Blo 2087435 2089015 := bstep (se 1 (by rfl) ⟨1566761, by rfl⟩ : syracuseStep 2089015 = 3133523) B3133523
theorem B3525221 : Blo 2087435 3525221 := bbase (se 4 (by rfl) ⟨330489, by rfl⟩ : syracuseStep 3525221 = 660979) (by norm_num)
theorem B2350147 : Blo 2087435 2350147 := bstep (se 1 (by rfl) ⟨1762610, by rfl⟩ : syracuseStep 2350147 = 3525221) B3525221
theorem B3133529 : Blo 2087435 3133529 := bstep (se 2 (by rfl) ⟨1175073, by rfl⟩ : syracuseStep 3133529 = 2350147) B2350147
theorem B2089019 : Blo 2087435 2089019 := bstep (se 1 (by rfl) ⟨1566764, by rfl⟩ : syracuseStep 2089019 = 3133529) B3133529
theorem B3346213 : Blo 2087435 3346213 := bbase (se 4 (by rfl) ⟨313707, by rfl⟩ : syracuseStep 3346213 = 627415) (by norm_num)
theorem B4461617 : Blo 2087435 4461617 := bstep (se 2 (by rfl) ⟨1673106, by rfl⟩ : syracuseStep 4461617 = 3346213) B3346213
theorem B2974411 : Blo 2087435 2974411 := bstep (se 1 (by rfl) ⟨2230808, by rfl⟩ : syracuseStep 2974411 = 4461617) B4461617
theorem B15863525 : Blo 2087435 15863525 := bstep (se 4 (by rfl) ⟨1487205, by rfl⟩ : syracuseStep 15863525 = 2974411) B2974411
theorem B10575683 : Blo 2087435 10575683 := bstep (se 1 (by rfl) ⟨7931762, by rfl⟩ : syracuseStep 10575683 = 15863525) B15863525
theorem B7050455 : Blo 2087435 7050455 := bstep (se 1 (by rfl) ⟨5287841, by rfl⟩ : syracuseStep 7050455 = 10575683) B10575683
theorem B4700303 : Blo 2087435 4700303 := bstep (se 1 (by rfl) ⟨3525227, by rfl⟩ : syracuseStep 4700303 = 7050455) B7050455
theorem B3133535 : Blo 2087435 3133535 := bstep (se 1 (by rfl) ⟨2350151, by rfl⟩ : syracuseStep 3133535 = 4700303) B4700303
theorem B2089023 : Blo 2087435 2089023 := bstep (se 1 (by rfl) ⟨1566767, by rfl⟩ : syracuseStep 2089023 = 3133535) B3133535
theorem B3133541 : Blo 2087435 3133541 := bbase (se 4 (by rfl) ⟨293769, by rfl⟩ : syracuseStep 3133541 = 587539) (by norm_num)
theorem B2089027 : Blo 2087435 2089027 := bstep (se 1 (by rfl) ⟨1566770, by rfl⟩ : syracuseStep 2089027 = 3133541) B3133541
theorem B6692453 : Blo 2087435 6692453 := bbase (se 4 (by rfl) ⟨627417, by rfl⟩ : syracuseStep 6692453 = 1254835) (by norm_num)
theorem B4461635 : Blo 2087435 4461635 := bstep (se 1 (by rfl) ⟨3346226, by rfl⟩ : syracuseStep 4461635 = 6692453) B6692453
theorem B2974423 : Blo 2087435 2974423 := bstep (se 1 (by rfl) ⟨2230817, by rfl⟩ : syracuseStep 2974423 = 4461635) B4461635
theorem B3965897 : Blo 2087435 3965897 := bstep (se 2 (by rfl) ⟨1487211, by rfl⟩ : syracuseStep 3965897 = 2974423) B2974423
theorem B2643931 : Blo 2087435 2643931 := bstep (se 1 (by rfl) ⟨1982948, by rfl⟩ : syracuseStep 2643931 = 3965897) B3965897
theorem B3525241 : Blo 2087435 3525241 := bstep (se 2 (by rfl) ⟨1321965, by rfl⟩ : syracuseStep 3525241 = 2643931) B2643931
theorem B4700321 : Blo 2087435 4700321 := bstep (se 2 (by rfl) ⟨1762620, by rfl⟩ : syracuseStep 4700321 = 3525241) B3525241
theorem B3133547 : Blo 2087435 3133547 := bstep (se 1 (by rfl) ⟨2350160, by rfl⟩ : syracuseStep 3133547 = 4700321) B4700321
theorem B2089031 : Blo 2087435 2089031 := bstep (se 1 (by rfl) ⟨1566773, by rfl⟩ : syracuseStep 2089031 = 3133547) B3133547
theorem B2350165 : Blo 2087435 2350165 := bbase (se 8 (by rfl) ⟨13770, by rfl⟩ : syracuseStep 2350165 = 27541) (by norm_num)
theorem B3133553 : Blo 2087435 3133553 := bstep (se 2 (by rfl) ⟨1175082, by rfl⟩ : syracuseStep 3133553 = 2350165) B2350165
theorem B2089035 : Blo 2087435 2089035 := bstep (se 1 (by rfl) ⟨1566776, by rfl⟩ : syracuseStep 2089035 = 3133553) B3133553
theorem B2643941 : Blo 2087435 2643941 := bbase (se 4 (by rfl) ⟨247869, by rfl⟩ : syracuseStep 2643941 = 495739) (by norm_num)
theorem B7050509 : Blo 2087435 7050509 := bstep (se 3 (by rfl) ⟨1321970, by rfl⟩ : syracuseStep 7050509 = 2643941) B2643941
theorem B4700339 : Blo 2087435 4700339 := bstep (se 1 (by rfl) ⟨3525254, by rfl⟩ : syracuseStep 4700339 = 7050509) B7050509
theorem B3133559 : Blo 2087435 3133559 := bstep (se 1 (by rfl) ⟨2350169, by rfl⟩ : syracuseStep 3133559 = 4700339) B4700339
theorem B2089039 : Blo 2087435 2089039 := bstep (se 1 (by rfl) ⟨1566779, by rfl⟩ : syracuseStep 2089039 = 3133559) B3133559
theorem B3133565 : Blo 2087435 3133565 := bbase (se 3 (by rfl) ⟨587543, by rfl⟩ : syracuseStep 3133565 = 1175087) (by norm_num)
theorem B2089043 : Blo 2087435 2089043 := bstep (se 1 (by rfl) ⟨1566782, by rfl⟩ : syracuseStep 2089043 = 3133565) B3133565
theorem B4700357 : Blo 2087435 4700357 := bbase (se 4 (by rfl) ⟨440658, by rfl⟩ : syracuseStep 4700357 = 881317) (by norm_num)
theorem B3133571 : Blo 2087435 3133571 := bstep (se 1 (by rfl) ⟨2350178, by rfl⟩ : syracuseStep 3133571 = 4700357) B4700357
theorem B2089047 : Blo 2087435 2089047 := bstep (se 1 (by rfl) ⟨1566785, by rfl⟩ : syracuseStep 2089047 = 3133571) B3133571
theorem B14293493 : Blo 2087435 14293493 := bbase (se 5 (by rfl) ⟨670007, by rfl⟩ : syracuseStep 14293493 = 1340015) (by norm_num)
theorem B9528995 : Blo 2087435 9528995 := bstep (se 1 (by rfl) ⟨7146746, by rfl⟩ : syracuseStep 9528995 = 14293493) B14293493
theorem B6352663 : Blo 2087435 6352663 := bstep (se 1 (by rfl) ⟨4764497, by rfl⟩ : syracuseStep 6352663 = 9528995) B9528995
theorem B8470217 : Blo 2087435 8470217 := bstep (se 2 (by rfl) ⟨3176331, by rfl⟩ : syracuseStep 8470217 = 6352663) B6352663
theorem B22587245 : Blo 2087435 22587245 := bstep (se 3 (by rfl) ⟨4235108, by rfl⟩ : syracuseStep 22587245 = 8470217) B8470217
theorem B15058163 : Blo 2087435 15058163 := bstep (se 1 (by rfl) ⟨11293622, by rfl⟩ : syracuseStep 15058163 = 22587245) B22587245
theorem B10038775 : Blo 2087435 10038775 := bstep (se 1 (by rfl) ⟨7529081, by rfl⟩ : syracuseStep 10038775 = 15058163) B15058163
theorem B13385033 : Blo 2087435 13385033 := bstep (se 2 (by rfl) ⟨5019387, by rfl⟩ : syracuseStep 13385033 = 10038775) B10038775
theorem B8923355 : Blo 2087435 8923355 := bstep (se 1 (by rfl) ⟨6692516, by rfl⟩ : syracuseStep 8923355 = 13385033) B13385033
theorem B5948903 : Blo 2087435 5948903 := bstep (se 1 (by rfl) ⟨4461677, by rfl⟩ : syracuseStep 5948903 = 8923355) B8923355
theorem B3965935 : Blo 2087435 3965935 := bstep (se 1 (by rfl) ⟨2974451, by rfl⟩ : syracuseStep 3965935 = 5948903) B5948903
theorem B5287913 : Blo 2087435 5287913 := bstep (se 2 (by rfl) ⟨1982967, by rfl⟩ : syracuseStep 5287913 = 3965935) B3965935
theorem B3525275 : Blo 2087435 3525275 := bstep (se 1 (by rfl) ⟨2643956, by rfl⟩ : syracuseStep 3525275 = 5287913) B5287913
theorem B2350183 : Blo 2087435 2350183 := bstep (se 1 (by rfl) ⟨1762637, by rfl⟩ : syracuseStep 2350183 = 3525275) B3525275
theorem B3133577 : Blo 2087435 3133577 := bstep (se 2 (by rfl) ⟨1175091, by rfl⟩ : syracuseStep 3133577 = 2350183) B2350183
theorem B2089051 : Blo 2087435 2089051 := bstep (se 1 (by rfl) ⟨1566788, by rfl⟩ : syracuseStep 2089051 = 3133577) B3133577
theorem B10575845 : Blo 2087435 10575845 := bbase (se 4 (by rfl) ⟨991485, by rfl⟩ : syracuseStep 10575845 = 1982971) (by norm_num)
theorem B7050563 : Blo 2087435 7050563 := bstep (se 1 (by rfl) ⟨5287922, by rfl⟩ : syracuseStep 7050563 = 10575845) B10575845
theorem B4700375 : Blo 2087435 4700375 := bstep (se 1 (by rfl) ⟨3525281, by rfl⟩ : syracuseStep 4700375 = 7050563) B7050563
theorem B3133583 : Blo 2087435 3133583 := bstep (se 1 (by rfl) ⟨2350187, by rfl⟩ : syracuseStep 3133583 = 4700375) B4700375
theorem B2089055 : Blo 2087435 2089055 := bstep (se 1 (by rfl) ⟨1566791, by rfl⟩ : syracuseStep 2089055 = 3133583) B3133583
theorem B3133589 : Blo 2087435 3133589 := bbase (se 6 (by rfl) ⟨73443, by rfl⟩ : syracuseStep 3133589 = 146887) (by norm_num)
theorem B2089059 : Blo 2087435 2089059 := bstep (se 1 (by rfl) ⟨1566794, by rfl⟩ : syracuseStep 2089059 = 3133589) B3133589
theorem B3346277 : Blo 2087435 3346277 := bbase (se 4 (by rfl) ⟨313713, by rfl⟩ : syracuseStep 3346277 = 627427) (by norm_num)
theorem B8923405 : Blo 2087435 8923405 := bstep (se 3 (by rfl) ⟨1673138, by rfl⟩ : syracuseStep 8923405 = 3346277) B3346277
theorem B11897873 : Blo 2087435 11897873 := bstep (se 2 (by rfl) ⟨4461702, by rfl⟩ : syracuseStep 11897873 = 8923405) B8923405
theorem B7931915 : Blo 2087435 7931915 := bstep (se 1 (by rfl) ⟨5948936, by rfl⟩ : syracuseStep 7931915 = 11897873) B11897873
theorem B5287943 : Blo 2087435 5287943 := bstep (se 1 (by rfl) ⟨3965957, by rfl⟩ : syracuseStep 5287943 = 7931915) B7931915
theorem B3525295 : Blo 2087435 3525295 := bstep (se 1 (by rfl) ⟨2643971, by rfl⟩ : syracuseStep 3525295 = 5287943) B5287943
theorem B4700393 : Blo 2087435 4700393 := bstep (se 2 (by rfl) ⟨1762647, by rfl⟩ : syracuseStep 4700393 = 3525295) B3525295
theorem B3133595 : Blo 2087435 3133595 := bstep (se 1 (by rfl) ⟨2350196, by rfl⟩ : syracuseStep 3133595 = 4700393) B4700393
theorem B2089063 : Blo 2087435 2089063 := bstep (se 1 (by rfl) ⟨1566797, by rfl⟩ : syracuseStep 2089063 = 3133595) B3133595
theorem B2350201 : Blo 2087435 2350201 := bbase (se 2 (by rfl) ⟨881325, by rfl⟩ : syracuseStep 2350201 = 1762651) (by norm_num)
theorem B3133601 : Blo 2087435 3133601 := bstep (se 2 (by rfl) ⟨1175100, by rfl⟩ : syracuseStep 3133601 = 2350201) B2350201
theorem B2089067 : Blo 2087435 2089067 := bstep (se 1 (by rfl) ⟨1566800, by rfl⟩ : syracuseStep 2089067 = 3133601) B3133601
theorem B2716621 : Blo 2087435 2716621 := bbase (se 3 (by rfl) ⟨509366, by rfl⟩ : syracuseStep 2716621 = 1018733) (by norm_num)
theorem B14488645 : Blo 2087435 14488645 := bstep (se 4 (by rfl) ⟨1358310, by rfl⟩ : syracuseStep 14488645 = 2716621) B2716621
theorem B19318193 : Blo 2087435 19318193 := bstep (se 2 (by rfl) ⟨7244322, by rfl⟩ : syracuseStep 19318193 = 14488645) B14488645
theorem B12878795 : Blo 2087435 12878795 := bstep (se 1 (by rfl) ⟨9659096, by rfl⟩ : syracuseStep 12878795 = 19318193) B19318193
theorem B34343453 : Blo 2087435 34343453 := bstep (se 3 (by rfl) ⟨6439397, by rfl⟩ : syracuseStep 34343453 = 12878795) B12878795
theorem B22895635 : Blo 2087435 22895635 := bstep (se 1 (by rfl) ⟨17171726, by rfl⟩ : syracuseStep 22895635 = 34343453) B34343453
theorem B30527513 : Blo 2087435 30527513 := bstep (se 2 (by rfl) ⟨11447817, by rfl⟩ : syracuseStep 30527513 = 22895635) B22895635
theorem B20351675 : Blo 2087435 20351675 := bstep (se 1 (by rfl) ⟨15263756, by rfl⟩ : syracuseStep 20351675 = 30527513) B30527513
theorem B13567783 : Blo 2087435 13567783 := bstep (se 1 (by rfl) ⟨10175837, by rfl⟩ : syracuseStep 13567783 = 20351675) B20351675
theorem B18090377 : Blo 2087435 18090377 := bstep (se 2 (by rfl) ⟨6783891, by rfl⟩ : syracuseStep 18090377 = 13567783) B13567783
theorem B12060251 : Blo 2087435 12060251 := bstep (se 1 (by rfl) ⟨9045188, by rfl⟩ : syracuseStep 12060251 = 18090377) B18090377
theorem B8040167 : Blo 2087435 8040167 := bstep (se 1 (by rfl) ⟨6030125, by rfl⟩ : syracuseStep 8040167 = 12060251) B12060251
theorem B5360111 : Blo 2087435 5360111 := bstep (se 1 (by rfl) ⟨4020083, by rfl⟩ : syracuseStep 5360111 = 8040167) B8040167
theorem B3573407 : Blo 2087435 3573407 := bstep (se 1 (by rfl) ⟨2680055, by rfl⟩ : syracuseStep 3573407 = 5360111) B5360111
theorem B2382271 : Blo 2087435 2382271 := bstep (se 1 (by rfl) ⟨1786703, by rfl⟩ : syracuseStep 2382271 = 3573407) B3573407
theorem B12705445 : Blo 2087435 12705445 := bstep (se 4 (by rfl) ⟨1191135, by rfl⟩ : syracuseStep 12705445 = 2382271) B2382271
theorem B16940593 : Blo 2087435 16940593 := bstep (se 2 (by rfl) ⟨6352722, by rfl⟩ : syracuseStep 16940593 = 12705445) B12705445
theorem B22587457 : Blo 2087435 22587457 := bstep (se 2 (by rfl) ⟨8470296, by rfl⟩ : syracuseStep 22587457 = 16940593) B16940593
theorem B30116609 : Blo 2087435 30116609 := bstep (se 2 (by rfl) ⟨11293728, by rfl⟩ : syracuseStep 30116609 = 22587457) B22587457
theorem B20077739 : Blo 2087435 20077739 := bstep (se 1 (by rfl) ⟨15058304, by rfl⟩ : syracuseStep 20077739 = 30116609) B30116609
theorem B13385159 : Blo 2087435 13385159 := bstep (se 1 (by rfl) ⟨10038869, by rfl⟩ : syracuseStep 13385159 = 20077739) B20077739
theorem B8923439 : Blo 2087435 8923439 := bstep (se 1 (by rfl) ⟨6692579, by rfl⟩ : syracuseStep 8923439 = 13385159) B13385159
theorem B5948959 : Blo 2087435 5948959 := bstep (se 1 (by rfl) ⟨4461719, by rfl⟩ : syracuseStep 5948959 = 8923439) B8923439
theorem B7931945 : Blo 2087435 7931945 := bstep (se 2 (by rfl) ⟨2974479, by rfl⟩ : syracuseStep 7931945 = 5948959) B5948959
theorem B5287963 : Blo 2087435 5287963 := bstep (se 1 (by rfl) ⟨3965972, by rfl⟩ : syracuseStep 5287963 = 7931945) B7931945
theorem B7050617 : Blo 2087435 7050617 := bstep (se 2 (by rfl) ⟨2643981, by rfl⟩ : syracuseStep 7050617 = 5287963) B5287963
theorem B4700411 : Blo 2087435 4700411 := bstep (se 1 (by rfl) ⟨3525308, by rfl⟩ : syracuseStep 4700411 = 7050617) B7050617
theorem B3133607 : Blo 2087435 3133607 := bstep (se 1 (by rfl) ⟨2350205, by rfl⟩ : syracuseStep 3133607 = 4700411) B4700411
theorem B2089071 : Blo 2087435 2089071 := bstep (se 1 (by rfl) ⟨1566803, by rfl⟩ : syracuseStep 2089071 = 3133607) B3133607
theorem B3133613 : Blo 2087435 3133613 := bbase (se 3 (by rfl) ⟨587552, by rfl⟩ : syracuseStep 3133613 = 1175105) (by norm_num)
theorem B2089075 : Blo 2087435 2089075 := bstep (se 1 (by rfl) ⟨1566806, by rfl⟩ : syracuseStep 2089075 = 3133613) B3133613
theorem B4700429 : Blo 2087435 4700429 := bbase (se 3 (by rfl) ⟨881330, by rfl⟩ : syracuseStep 4700429 = 1762661) (by norm_num)
theorem B3133619 : Blo 2087435 3133619 := bstep (se 1 (by rfl) ⟨2350214, by rfl⟩ : syracuseStep 3133619 = 4700429) B4700429
theorem B2089079 : Blo 2087435 2089079 := bstep (se 1 (by rfl) ⟨1566809, by rfl⟩ : syracuseStep 2089079 = 3133619) B3133619
theorem B2643997 : Blo 2087435 2643997 := bbase (se 3 (by rfl) ⟨495749, by rfl⟩ : syracuseStep 2643997 = 991499) (by norm_num)
theorem B3525329 : Blo 2087435 3525329 := bstep (se 2 (by rfl) ⟨1321998, by rfl⟩ : syracuseStep 3525329 = 2643997) B2643997
theorem B2350219 : Blo 2087435 2350219 := bstep (se 1 (by rfl) ⟨1762664, by rfl⟩ : syracuseStep 2350219 = 3525329) B3525329
theorem B3133625 : Blo 2087435 3133625 := bstep (se 2 (by rfl) ⟨1175109, by rfl⟩ : syracuseStep 3133625 = 2350219) B2350219
theorem B2089083 : Blo 2087435 2089083 := bstep (se 1 (by rfl) ⟨1566812, by rfl⟩ : syracuseStep 2089083 = 3133625) B3133625
theorem B3764605 : Blo 2087435 3764605 := bbase (se 3 (by rfl) ⟨705863, by rfl⟩ : syracuseStep 3764605 = 1411727) (by norm_num)
theorem B5019473 : Blo 2087435 5019473 := bstep (se 2 (by rfl) ⟨1882302, by rfl⟩ : syracuseStep 5019473 = 3764605) B3764605
theorem B3346315 : Blo 2087435 3346315 := bstep (se 1 (by rfl) ⟨2509736, by rfl⟩ : syracuseStep 3346315 = 5019473) B5019473
theorem B17847013 : Blo 2087435 17847013 := bstep (se 4 (by rfl) ⟨1673157, by rfl⟩ : syracuseStep 17847013 = 3346315) B3346315
theorem B23796017 : Blo 2087435 23796017 := bstep (se 2 (by rfl) ⟨8923506, by rfl⟩ : syracuseStep 23796017 = 17847013) B17847013
theorem B15864011 : Blo 2087435 15864011 := bstep (se 1 (by rfl) ⟨11898008, by rfl⟩ : syracuseStep 15864011 = 23796017) B23796017
theorem B10576007 : Blo 2087435 10576007 := bstep (se 1 (by rfl) ⟨7932005, by rfl⟩ : syracuseStep 10576007 = 15864011) B15864011
theorem B7050671 : Blo 2087435 7050671 := bstep (se 1 (by rfl) ⟨5288003, by rfl⟩ : syracuseStep 7050671 = 10576007) B10576007
theorem B4700447 : Blo 2087435 4700447 := bstep (se 1 (by rfl) ⟨3525335, by rfl⟩ : syracuseStep 4700447 = 7050671) B7050671
theorem B3133631 : Blo 2087435 3133631 := bstep (se 1 (by rfl) ⟨2350223, by rfl⟩ : syracuseStep 3133631 = 4700447) B4700447
theorem B2089087 : Blo 2087435 2089087 := bstep (se 1 (by rfl) ⟨1566815, by rfl⟩ : syracuseStep 2089087 = 3133631) B3133631
theorem B3133637 : Blo 2087435 3133637 := bbase (se 4 (by rfl) ⟨293778, by rfl⟩ : syracuseStep 3133637 = 587557) (by norm_num)
theorem B2089091 : Blo 2087435 2089091 := bstep (se 1 (by rfl) ⟨1566818, by rfl⟩ : syracuseStep 2089091 = 3133637) B3133637
theorem B3525349 : Blo 2087435 3525349 := bbase (se 4 (by rfl) ⟨330501, by rfl⟩ : syracuseStep 3525349 = 661003) (by norm_num)
theorem B4700465 : Blo 2087435 4700465 := bstep (se 2 (by rfl) ⟨1762674, by rfl⟩ : syracuseStep 4700465 = 3525349) B3525349
theorem B3133643 : Blo 2087435 3133643 := bstep (se 1 (by rfl) ⟨2350232, by rfl⟩ : syracuseStep 3133643 = 4700465) B4700465
theorem B2089095 : Blo 2087435 2089095 := bstep (se 1 (by rfl) ⟨1566821, by rfl⟩ : syracuseStep 2089095 = 3133643) B3133643
theorem B2350237 : Blo 2087435 2350237 := bbase (se 3 (by rfl) ⟨440669, by rfl⟩ : syracuseStep 2350237 = 881339) (by norm_num)
theorem B3133649 : Blo 2087435 3133649 := bstep (se 2 (by rfl) ⟨1175118, by rfl⟩ : syracuseStep 3133649 = 2350237) B2350237
theorem B2089099 : Blo 2087435 2089099 := bstep (se 1 (by rfl) ⟨1566824, by rfl⟩ : syracuseStep 2089099 = 3133649) B3133649
theorem B7050725 : Blo 2087435 7050725 := bbase (se 4 (by rfl) ⟨661005, by rfl⟩ : syracuseStep 7050725 = 1322011) (by norm_num)
theorem B4700483 : Blo 2087435 4700483 := bstep (se 1 (by rfl) ⟨3525362, by rfl⟩ : syracuseStep 4700483 = 7050725) B7050725
theorem B3133655 : Blo 2087435 3133655 := bstep (se 1 (by rfl) ⟨2350241, by rfl⟩ : syracuseStep 3133655 = 4700483) B4700483
theorem B2089103 : Blo 2087435 2089103 := bstep (se 1 (by rfl) ⟨1566827, by rfl⟩ : syracuseStep 2089103 = 3133655) B3133655
theorem B3133661 : Blo 2087435 3133661 := bbase (se 3 (by rfl) ⟨587561, by rfl⟩ : syracuseStep 3133661 = 1175123) (by norm_num)
theorem B2089107 : Blo 2087435 2089107 := bstep (se 1 (by rfl) ⟨1566830, by rfl⟩ : syracuseStep 2089107 = 3133661) B3133661
theorem B4700501 : Blo 2087435 4700501 := bbase (se 10 (by rfl) ⟨6885, by rfl⟩ : syracuseStep 4700501 = 13771) (by norm_num)
theorem B3133667 : Blo 2087435 3133667 := bstep (se 1 (by rfl) ⟨2350250, by rfl⟩ : syracuseStep 3133667 = 4700501) B4700501
theorem B2089111 : Blo 2087435 2089111 := bstep (se 1 (by rfl) ⟨1566833, by rfl⟩ : syracuseStep 2089111 = 3133667) B3133667
theorem B2823493 : Blo 2087435 2823493 := bbase (se 4 (by rfl) ⟨264702, by rfl⟩ : syracuseStep 2823493 = 529405) (by norm_num)
theorem B3764657 : Blo 2087435 3764657 := bstep (se 2 (by rfl) ⟨1411746, by rfl⟩ : syracuseStep 3764657 = 2823493) B2823493
theorem B2509771 : Blo 2087435 2509771 := bstep (se 1 (by rfl) ⟨1882328, by rfl⟩ : syracuseStep 2509771 = 3764657) B3764657
theorem B3346361 : Blo 2087435 3346361 := bstep (se 2 (by rfl) ⟨1254885, by rfl⟩ : syracuseStep 3346361 = 2509771) B2509771
theorem B2230907 : Blo 2087435 2230907 := bstep (se 1 (by rfl) ⟨1673180, by rfl⟩ : syracuseStep 2230907 = 3346361) B3346361
theorem B5949085 : Blo 2087435 5949085 := bstep (se 3 (by rfl) ⟨1115453, by rfl⟩ : syracuseStep 5949085 = 2230907) B2230907
theorem B7932113 : Blo 2087435 7932113 := bstep (se 2 (by rfl) ⟨2974542, by rfl⟩ : syracuseStep 7932113 = 5949085) B5949085
theorem B5288075 : Blo 2087435 5288075 := bstep (se 1 (by rfl) ⟨3966056, by rfl⟩ : syracuseStep 5288075 = 7932113) B7932113
theorem B3525383 : Blo 2087435 3525383 := bstep (se 1 (by rfl) ⟨2644037, by rfl⟩ : syracuseStep 3525383 = 5288075) B5288075
theorem B2350255 : Blo 2087435 2350255 := bstep (se 1 (by rfl) ⟨1762691, by rfl⟩ : syracuseStep 2350255 = 3525383) B3525383
theorem B3133673 : Blo 2087435 3133673 := bstep (se 2 (by rfl) ⟨1175127, by rfl⟩ : syracuseStep 3133673 = 2350255) B2350255
theorem B2089115 : Blo 2087435 2089115 := bstep (se 1 (by rfl) ⟨1566836, by rfl⟩ : syracuseStep 2089115 = 3133673) B3133673
theorem B16940981 : Blo 2087435 16940981 := bbase (se 5 (by rfl) ⟨794108, by rfl⟩ : syracuseStep 16940981 = 1588217) (by norm_num)
theorem B11293987 : Blo 2087435 11293987 := bstep (se 1 (by rfl) ⟨8470490, by rfl⟩ : syracuseStep 11293987 = 16940981) B16940981
theorem B15058649 : Blo 2087435 15058649 := bstep (se 2 (by rfl) ⟨5646993, by rfl⟩ : syracuseStep 15058649 = 11293987) B11293987
theorem B40156397 : Blo 2087435 40156397 := bstep (se 3 (by rfl) ⟨7529324, by rfl⟩ : syracuseStep 40156397 = 15058649) B15058649
theorem B26770931 : Blo 2087435 26770931 := bstep (se 1 (by rfl) ⟨20078198, by rfl⟩ : syracuseStep 26770931 = 40156397) B40156397
theorem B17847287 : Blo 2087435 17847287 := bstep (se 1 (by rfl) ⟨13385465, by rfl⟩ : syracuseStep 17847287 = 26770931) B26770931
theorem B11898191 : Blo 2087435 11898191 := bstep (se 1 (by rfl) ⟨8923643, by rfl⟩ : syracuseStep 11898191 = 17847287) B17847287
theorem B7932127 : Blo 2087435 7932127 := bstep (se 1 (by rfl) ⟨5949095, by rfl⟩ : syracuseStep 7932127 = 11898191) B11898191
theorem B10576169 : Blo 2087435 10576169 := bstep (se 2 (by rfl) ⟨3966063, by rfl⟩ : syracuseStep 10576169 = 7932127) B7932127
theorem B7050779 : Blo 2087435 7050779 := bstep (se 1 (by rfl) ⟨5288084, by rfl⟩ : syracuseStep 7050779 = 10576169) B10576169
theorem B4700519 : Blo 2087435 4700519 := bstep (se 1 (by rfl) ⟨3525389, by rfl⟩ : syracuseStep 4700519 = 7050779) B7050779
theorem B3133679 : Blo 2087435 3133679 := bstep (se 1 (by rfl) ⟨2350259, by rfl⟩ : syracuseStep 3133679 = 4700519) B4700519
theorem B2089119 : Blo 2087435 2089119 := bstep (se 1 (by rfl) ⟨1566839, by rfl⟩ : syracuseStep 2089119 = 3133679) B3133679
theorem B3133685 : Blo 2087435 3133685 := bbase (se 5 (by rfl) ⟨146891, by rfl⟩ : syracuseStep 3133685 = 293783) (by norm_num)
theorem B2089123 : Blo 2087435 2089123 := bstep (se 1 (by rfl) ⟨1566842, by rfl⟩ : syracuseStep 2089123 = 3133685) B3133685
theorem B4584421 : Blo 2087435 4584421 := bbase (se 4 (by rfl) ⟨429789, by rfl⟩ : syracuseStep 4584421 = 859579) (by norm_num)
theorem B24450245 : Blo 2087435 24450245 := bstep (se 4 (by rfl) ⟨2292210, by rfl⟩ : syracuseStep 24450245 = 4584421) B4584421
theorem B16300163 : Blo 2087435 16300163 := bstep (se 1 (by rfl) ⟨12225122, by rfl⟩ : syracuseStep 16300163 = 24450245) B24450245
theorem B43467101 : Blo 2087435 43467101 := bstep (se 3 (by rfl) ⟨8150081, by rfl⟩ : syracuseStep 43467101 = 16300163) B16300163
theorem B28978067 : Blo 2087435 28978067 := bstep (se 1 (by rfl) ⟨21733550, by rfl⟩ : syracuseStep 28978067 = 43467101) B43467101
theorem B19318711 : Blo 2087435 19318711 := bstep (se 1 (by rfl) ⟨14489033, by rfl⟩ : syracuseStep 19318711 = 28978067) B28978067
theorem B25758281 : Blo 2087435 25758281 := bstep (se 2 (by rfl) ⟨9659355, by rfl⟩ : syracuseStep 25758281 = 19318711) B19318711
theorem B68688749 : Blo 2087435 68688749 := bstep (se 3 (by rfl) ⟨12879140, by rfl⟩ : syracuseStep 68688749 = 25758281) B25758281
theorem B45792499 : Blo 2087435 45792499 := bstep (se 1 (by rfl) ⟨34344374, by rfl⟩ : syracuseStep 45792499 = 68688749) B68688749
theorem B61056665 : Blo 2087435 61056665 := bstep (se 2 (by rfl) ⟨22896249, by rfl⟩ : syracuseStep 61056665 = 45792499) B45792499
theorem B40704443 : Blo 2087435 40704443 := bstep (se 1 (by rfl) ⟨30528332, by rfl⟩ : syracuseStep 40704443 = 61056665) B61056665
theorem B27136295 : Blo 2087435 27136295 := bstep (se 1 (by rfl) ⟨20352221, by rfl⟩ : syracuseStep 27136295 = 40704443) B40704443
theorem B18090863 : Blo 2087435 18090863 := bstep (se 1 (by rfl) ⟨13568147, by rfl⟩ : syracuseStep 18090863 = 27136295) B27136295
theorem B12060575 : Blo 2087435 12060575 := bstep (se 1 (by rfl) ⟨9045431, by rfl⟩ : syracuseStep 12060575 = 18090863) B18090863
theorem B8040383 : Blo 2087435 8040383 := bstep (se 1 (by rfl) ⟨6030287, by rfl⟩ : syracuseStep 8040383 = 12060575) B12060575
theorem B5360255 : Blo 2087435 5360255 := bstep (se 1 (by rfl) ⟨4020191, by rfl⟩ : syracuseStep 5360255 = 8040383) B8040383
theorem B3573503 : Blo 2087435 3573503 := bstep (se 1 (by rfl) ⟨2680127, by rfl⟩ : syracuseStep 3573503 = 5360255) B5360255
theorem B2382335 : Blo 2087435 2382335 := bstep (se 1 (by rfl) ⟨1786751, by rfl⟩ : syracuseStep 2382335 = 3573503) B3573503
theorem B25411573 : Blo 2087435 25411573 := bstep (se 5 (by rfl) ⟨1191167, by rfl⟩ : syracuseStep 25411573 = 2382335) B2382335
theorem B33882097 : Blo 2087435 33882097 := bstep (se 2 (by rfl) ⟨12705786, by rfl⟩ : syracuseStep 33882097 = 25411573) B25411573
theorem B45176129 : Blo 2087435 45176129 := bstep (se 2 (by rfl) ⟨16941048, by rfl⟩ : syracuseStep 45176129 = 33882097) B33882097
theorem B30117419 : Blo 2087435 30117419 := bstep (se 1 (by rfl) ⟨22588064, by rfl⟩ : syracuseStep 30117419 = 45176129) B45176129
theorem B20078279 : Blo 2087435 20078279 := bstep (se 1 (by rfl) ⟨15058709, by rfl⟩ : syracuseStep 20078279 = 30117419) B30117419
theorem B13385519 : Blo 2087435 13385519 := bstep (se 1 (by rfl) ⟨10039139, by rfl⟩ : syracuseStep 13385519 = 20078279) B20078279
theorem B8923679 : Blo 2087435 8923679 := bstep (se 1 (by rfl) ⟨6692759, by rfl⟩ : syracuseStep 8923679 = 13385519) B13385519
theorem B5949119 : Blo 2087435 5949119 := bstep (se 1 (by rfl) ⟨4461839, by rfl⟩ : syracuseStep 5949119 = 8923679) B8923679
theorem B3966079 : Blo 2087435 3966079 := bstep (se 1 (by rfl) ⟨2974559, by rfl⟩ : syracuseStep 3966079 = 5949119) B5949119
theorem B5288105 : Blo 2087435 5288105 := bstep (se 2 (by rfl) ⟨1983039, by rfl⟩ : syracuseStep 5288105 = 3966079) B3966079
theorem B3525403 : Blo 2087435 3525403 := bstep (se 1 (by rfl) ⟨2644052, by rfl⟩ : syracuseStep 3525403 = 5288105) B5288105
theorem B4700537 : Blo 2087435 4700537 := bstep (se 2 (by rfl) ⟨1762701, by rfl⟩ : syracuseStep 4700537 = 3525403) B3525403
theorem B3133691 : Blo 2087435 3133691 := bstep (se 1 (by rfl) ⟨2350268, by rfl⟩ : syracuseStep 3133691 = 4700537) B4700537
theorem B2089127 : Blo 2087435 2089127 := bstep (se 1 (by rfl) ⟨1566845, by rfl⟩ : syracuseStep 2089127 = 3133691) B3133691
theorem B2350273 : Blo 2087435 2350273 := bbase (se 2 (by rfl) ⟨881352, by rfl⟩ : syracuseStep 2350273 = 1762705) (by norm_num)
theorem B3133697 : Blo 2087435 3133697 := bstep (se 2 (by rfl) ⟨1175136, by rfl⟩ : syracuseStep 3133697 = 2350273) B2350273
theorem B2089131 : Blo 2087435 2089131 := bstep (se 1 (by rfl) ⟨1566848, by rfl⟩ : syracuseStep 2089131 = 3133697) B3133697
theorem B5288125 : Blo 2087435 5288125 := bbase (se 3 (by rfl) ⟨991523, by rfl⟩ : syracuseStep 5288125 = 1983047) (by norm_num)
theorem B7050833 : Blo 2087435 7050833 := bstep (se 2 (by rfl) ⟨2644062, by rfl⟩ : syracuseStep 7050833 = 5288125) B5288125
theorem B4700555 : Blo 2087435 4700555 := bstep (se 1 (by rfl) ⟨3525416, by rfl⟩ : syracuseStep 4700555 = 7050833) B7050833
theorem B3133703 : Blo 2087435 3133703 := bstep (se 1 (by rfl) ⟨2350277, by rfl⟩ : syracuseStep 3133703 = 4700555) B4700555
theorem B2089135 : Blo 2087435 2089135 := bstep (se 1 (by rfl) ⟨1566851, by rfl⟩ : syracuseStep 2089135 = 3133703) B3133703
theorem B3133709 : Blo 2087435 3133709 := bbase (se 3 (by rfl) ⟨587570, by rfl⟩ : syracuseStep 3133709 = 1175141) (by norm_num)
theorem B2089139 : Blo 2087435 2089139 := bstep (se 1 (by rfl) ⟨1566854, by rfl⟩ : syracuseStep 2089139 = 3133709) B3133709
theorem B4700573 : Blo 2087435 4700573 := bbase (se 3 (by rfl) ⟨881357, by rfl⟩ : syracuseStep 4700573 = 1762715) (by norm_num)
theorem B3133715 : Blo 2087435 3133715 := bstep (se 1 (by rfl) ⟨2350286, by rfl⟩ : syracuseStep 3133715 = 4700573) B4700573
theorem B2089143 : Blo 2087435 2089143 := bstep (se 1 (by rfl) ⟨1566857, by rfl⟩ : syracuseStep 2089143 = 3133715) B3133715
theorem B3525437 : Blo 2087435 3525437 := bbase (se 3 (by rfl) ⟨661019, by rfl⟩ : syracuseStep 3525437 = 1322039) (by norm_num)
theorem B2350291 : Blo 2087435 2350291 := bstep (se 1 (by rfl) ⟨1762718, by rfl⟩ : syracuseStep 2350291 = 3525437) B3525437
theorem B3133721 : Blo 2087435 3133721 := bstep (se 2 (by rfl) ⟨1175145, by rfl⟩ : syracuseStep 3133721 = 2350291) B2350291
theorem B2089147 : Blo 2087435 2089147 := bstep (se 1 (by rfl) ⟨1566860, by rfl⟩ : syracuseStep 2089147 = 3133721) B3133721
theorem B2230945 : Blo 2087435 2230945 := bbase (se 2 (by rfl) ⟨836604, by rfl⟩ : syracuseStep 2230945 = 1673209) (by norm_num)
theorem B11898373 : Blo 2087435 11898373 := bstep (se 4 (by rfl) ⟨1115472, by rfl⟩ : syracuseStep 11898373 = 2230945) B2230945
theorem B15864497 : Blo 2087435 15864497 := bstep (se 2 (by rfl) ⟨5949186, by rfl⟩ : syracuseStep 15864497 = 11898373) B11898373
theorem B10576331 : Blo 2087435 10576331 := bstep (se 1 (by rfl) ⟨7932248, by rfl⟩ : syracuseStep 10576331 = 15864497) B15864497
theorem B7050887 : Blo 2087435 7050887 := bstep (se 1 (by rfl) ⟨5288165, by rfl⟩ : syracuseStep 7050887 = 10576331) B10576331
theorem B4700591 : Blo 2087435 4700591 := bstep (se 1 (by rfl) ⟨3525443, by rfl⟩ : syracuseStep 4700591 = 7050887) B7050887
theorem B3133727 : Blo 2087435 3133727 := bstep (se 1 (by rfl) ⟨2350295, by rfl⟩ : syracuseStep 3133727 = 4700591) B4700591
theorem B2089151 : Blo 2087435 2089151 := bstep (se 1 (by rfl) ⟨1566863, by rfl⟩ : syracuseStep 2089151 = 3133727) B3133727
theorem B3133733 : Blo 2087435 3133733 := bbase (se 4 (by rfl) ⟨293787, by rfl⟩ : syracuseStep 3133733 = 587575) (by norm_num)
theorem B2089155 : Blo 2087435 2089155 := bstep (se 1 (by rfl) ⟨1566866, by rfl⟩ : syracuseStep 2089155 = 3133733) B3133733
theorem B2644093 : Blo 2087435 2644093 := bbase (se 3 (by rfl) ⟨495767, by rfl⟩ : syracuseStep 2644093 = 991535) (by norm_num)
theorem B3525457 : Blo 2087435 3525457 := bstep (se 2 (by rfl) ⟨1322046, by rfl⟩ : syracuseStep 3525457 = 2644093) B2644093
theorem B4700609 : Blo 2087435 4700609 := bstep (se 2 (by rfl) ⟨1762728, by rfl⟩ : syracuseStep 4700609 = 3525457) B3525457
theorem B3133739 : Blo 2087435 3133739 := bstep (se 1 (by rfl) ⟨2350304, by rfl⟩ : syracuseStep 3133739 = 4700609) B4700609
theorem B2089159 : Blo 2087435 2089159 := bstep (se 1 (by rfl) ⟨1566869, by rfl⟩ : syracuseStep 2089159 = 3133739) B3133739
theorem B2350309 : Blo 2087435 2350309 := bbase (se 4 (by rfl) ⟨220341, by rfl⟩ : syracuseStep 2350309 = 440683) (by norm_num)
theorem B3133745 : Blo 2087435 3133745 := bstep (se 2 (by rfl) ⟨1175154, by rfl⟩ : syracuseStep 3133745 = 2350309) B2350309
theorem B2089163 : Blo 2087435 2089163 := bstep (se 1 (by rfl) ⟨1566872, by rfl⟩ : syracuseStep 2089163 = 3133745) B3133745
theorem B4461925 : Blo 2087435 4461925 := bbase (se 4 (by rfl) ⟨418305, by rfl⟩ : syracuseStep 4461925 = 836611) (by norm_num)
theorem B5949233 : Blo 2087435 5949233 := bstep (se 2 (by rfl) ⟨2230962, by rfl⟩ : syracuseStep 5949233 = 4461925) B4461925
theorem B3966155 : Blo 2087435 3966155 := bstep (se 1 (by rfl) ⟨2974616, by rfl⟩ : syracuseStep 3966155 = 5949233) B5949233
theorem B2644103 : Blo 2087435 2644103 := bstep (se 1 (by rfl) ⟨1983077, by rfl⟩ : syracuseStep 2644103 = 3966155) B3966155
theorem B7050941 : Blo 2087435 7050941 := bstep (se 3 (by rfl) ⟨1322051, by rfl⟩ : syracuseStep 7050941 = 2644103) B2644103
theorem B4700627 : Blo 2087435 4700627 := bstep (se 1 (by rfl) ⟨3525470, by rfl⟩ : syracuseStep 4700627 = 7050941) B7050941
theorem B3133751 : Blo 2087435 3133751 := bstep (se 1 (by rfl) ⟨2350313, by rfl⟩ : syracuseStep 3133751 = 4700627) B4700627
theorem B2089167 : Blo 2087435 2089167 := bstep (se 1 (by rfl) ⟨1566875, by rfl⟩ : syracuseStep 2089167 = 3133751) B3133751
theorem B3133757 : Blo 2087435 3133757 := bbase (se 3 (by rfl) ⟨587579, by rfl⟩ : syracuseStep 3133757 = 1175159) (by norm_num)
theorem B2089171 : Blo 2087435 2089171 := bstep (se 1 (by rfl) ⟨1566878, by rfl⟩ : syracuseStep 2089171 = 3133757) B3133757
theorem B4700645 : Blo 2087435 4700645 := bbase (se 4 (by rfl) ⟨440685, by rfl⟩ : syracuseStep 4700645 = 881371) (by norm_num)
theorem B3133763 : Blo 2087435 3133763 := bstep (se 1 (by rfl) ⟨2350322, by rfl⟩ : syracuseStep 3133763 = 4700645) B4700645
theorem B2089175 : Blo 2087435 2089175 := bstep (se 1 (by rfl) ⟨1566881, by rfl⟩ : syracuseStep 2089175 = 3133763) B3133763
theorem B5288237 : Blo 2087435 5288237 := bbase (se 3 (by rfl) ⟨991544, by rfl⟩ : syracuseStep 5288237 = 1983089) (by norm_num)
theorem B3525491 : Blo 2087435 3525491 := bstep (se 1 (by rfl) ⟨2644118, by rfl⟩ : syracuseStep 3525491 = 5288237) B5288237
theorem B2350327 : Blo 2087435 2350327 := bstep (se 1 (by rfl) ⟨1762745, by rfl⟩ : syracuseStep 2350327 = 3525491) B3525491
theorem B3133769 : Blo 2087435 3133769 := bstep (se 2 (by rfl) ⟨1175163, by rfl⟩ : syracuseStep 3133769 = 2350327) B2350327
theorem B2089179 : Blo 2087435 2089179 := bstep (se 1 (by rfl) ⟨1566884, by rfl⟩ : syracuseStep 2089179 = 3133769) B3133769
theorem B7529557 : Blo 2087435 7529557 := bbase (se 8 (by rfl) ⟨44118, by rfl⟩ : syracuseStep 7529557 = 88237) (by norm_num)
theorem B10039409 : Blo 2087435 10039409 := bstep (se 2 (by rfl) ⟨3764778, by rfl⟩ : syracuseStep 10039409 = 7529557) B7529557
theorem B6692939 : Blo 2087435 6692939 := bstep (se 1 (by rfl) ⟨5019704, by rfl⟩ : syracuseStep 6692939 = 10039409) B10039409
theorem B4461959 : Blo 2087435 4461959 := bstep (se 1 (by rfl) ⟨3346469, by rfl⟩ : syracuseStep 4461959 = 6692939) B6692939
theorem B2974639 : Blo 2087435 2974639 := bstep (se 1 (by rfl) ⟨2230979, by rfl⟩ : syracuseStep 2974639 = 4461959) B4461959
theorem B3966185 : Blo 2087435 3966185 := bstep (se 2 (by rfl) ⟨1487319, by rfl⟩ : syracuseStep 3966185 = 2974639) B2974639
theorem B10576493 : Blo 2087435 10576493 := bstep (se 3 (by rfl) ⟨1983092, by rfl⟩ : syracuseStep 10576493 = 3966185) B3966185
theorem B7050995 : Blo 2087435 7050995 := bstep (se 1 (by rfl) ⟨5288246, by rfl⟩ : syracuseStep 7050995 = 10576493) B10576493
theorem B4700663 : Blo 2087435 4700663 := bstep (se 1 (by rfl) ⟨3525497, by rfl⟩ : syracuseStep 4700663 = 7050995) B7050995
theorem B3133775 : Blo 2087435 3133775 := bstep (se 1 (by rfl) ⟨2350331, by rfl⟩ : syracuseStep 3133775 = 4700663) B4700663
theorem B2089183 : Blo 2087435 2089183 := bstep (se 1 (by rfl) ⟨1566887, by rfl⟩ : syracuseStep 2089183 = 3133775) B3133775
theorem B3133781 : Blo 2087435 3133781 := bbase (se 10 (by rfl) ⟨4590, by rfl⟩ : syracuseStep 3133781 = 9181) (by norm_num)
theorem B2089187 : Blo 2087435 2089187 := bstep (se 1 (by rfl) ⟨1566890, by rfl⟩ : syracuseStep 2089187 = 3133781) B3133781
theorem B5949301 : Blo 2087435 5949301 := bbase (se 5 (by rfl) ⟨278873, by rfl⟩ : syracuseStep 5949301 = 557747) (by norm_num)
theorem B7932401 : Blo 2087435 7932401 := bstep (se 2 (by rfl) ⟨2974650, by rfl⟩ : syracuseStep 7932401 = 5949301) B5949301
theorem B5288267 : Blo 2087435 5288267 := bstep (se 1 (by rfl) ⟨3966200, by rfl⟩ : syracuseStep 5288267 = 7932401) B7932401
theorem B3525511 : Blo 2087435 3525511 := bstep (se 1 (by rfl) ⟨2644133, by rfl⟩ : syracuseStep 3525511 = 5288267) B5288267
theorem B4700681 : Blo 2087435 4700681 := bstep (se 2 (by rfl) ⟨1762755, by rfl⟩ : syracuseStep 4700681 = 3525511) B3525511
theorem B3133787 : Blo 2087435 3133787 := bstep (se 1 (by rfl) ⟨2350340, by rfl⟩ : syracuseStep 3133787 = 4700681) B4700681
theorem B2089191 : Blo 2087435 2089191 := bstep (se 1 (by rfl) ⟨1566893, by rfl⟩ : syracuseStep 2089191 = 3133787) B3133787
theorem B2350345 : Blo 2087435 2350345 := bbase (se 2 (by rfl) ⟨881379, by rfl⟩ : syracuseStep 2350345 = 1762759) (by norm_num)
theorem B3133793 : Blo 2087435 3133793 := bstep (se 2 (by rfl) ⟨1175172, by rfl⟩ : syracuseStep 3133793 = 2350345) B2350345
theorem B2089195 : Blo 2087435 2089195 := bstep (se 1 (by rfl) ⟨1566896, by rfl⟩ : syracuseStep 2089195 = 3133793) B3133793
theorem B7147253 : Blo 2087435 7147253 := bbase (se 5 (by rfl) ⟨335027, by rfl⟩ : syracuseStep 7147253 = 670055) (by norm_num)
theorem B4764835 : Blo 2087435 4764835 := bstep (se 1 (by rfl) ⟨3573626, by rfl⟩ : syracuseStep 4764835 = 7147253) B7147253
theorem B6353113 : Blo 2087435 6353113 := bstep (se 2 (by rfl) ⟨2382417, by rfl⟩ : syracuseStep 6353113 = 4764835) B4764835
theorem B8470817 : Blo 2087435 8470817 := bstep (se 2 (by rfl) ⟨3176556, by rfl⟩ : syracuseStep 8470817 = 6353113) B6353113
theorem B5647211 : Blo 2087435 5647211 := bstep (se 1 (by rfl) ⟨4235408, by rfl⟩ : syracuseStep 5647211 = 8470817) B8470817
theorem B3764807 : Blo 2087435 3764807 := bstep (se 1 (by rfl) ⟨2823605, by rfl⟩ : syracuseStep 3764807 = 5647211) B5647211
theorem B2509871 : Blo 2087435 2509871 := bstep (se 1 (by rfl) ⟨1882403, by rfl⟩ : syracuseStep 2509871 = 3764807) B3764807
theorem B26771957 : Blo 2087435 26771957 := bstep (se 5 (by rfl) ⟨1254935, by rfl⟩ : syracuseStep 26771957 = 2509871) B2509871
theorem B17847971 : Blo 2087435 17847971 := bstep (se 1 (by rfl) ⟨13385978, by rfl⟩ : syracuseStep 17847971 = 26771957) B26771957
theorem B11898647 : Blo 2087435 11898647 := bstep (se 1 (by rfl) ⟨8923985, by rfl⟩ : syracuseStep 11898647 = 17847971) B17847971
theorem B7932431 : Blo 2087435 7932431 := bstep (se 1 (by rfl) ⟨5949323, by rfl⟩ : syracuseStep 7932431 = 11898647) B11898647
theorem B5288287 : Blo 2087435 5288287 := bstep (se 1 (by rfl) ⟨3966215, by rfl⟩ : syracuseStep 5288287 = 7932431) B7932431
theorem B7051049 : Blo 2087435 7051049 := bstep (se 2 (by rfl) ⟨2644143, by rfl⟩ : syracuseStep 7051049 = 5288287) B5288287
theorem B4700699 : Blo 2087435 4700699 := bstep (se 1 (by rfl) ⟨3525524, by rfl⟩ : syracuseStep 4700699 = 7051049) B7051049
theorem B3133799 : Blo 2087435 3133799 := bstep (se 1 (by rfl) ⟨2350349, by rfl⟩ : syracuseStep 3133799 = 4700699) B4700699
theorem B2089199 : Blo 2087435 2089199 := bstep (se 1 (by rfl) ⟨1566899, by rfl⟩ : syracuseStep 2089199 = 3133799) B3133799
theorem B3133805 : Blo 2087435 3133805 := bbase (se 3 (by rfl) ⟨587588, by rfl⟩ : syracuseStep 3133805 = 1175177) (by norm_num)
theorem B2089203 : Blo 2087435 2089203 := bstep (se 1 (by rfl) ⟨1566902, by rfl⟩ : syracuseStep 2089203 = 3133805) B3133805
theorem B4700717 : Blo 2087435 4700717 := bbase (se 3 (by rfl) ⟨881384, by rfl⟩ : syracuseStep 4700717 = 1762769) (by norm_num)
theorem B3133811 : Blo 2087435 3133811 := bstep (se 1 (by rfl) ⟨2350358, by rfl⟩ : syracuseStep 3133811 = 4700717) B4700717
theorem B2089207 : Blo 2087435 2089207 := bstep (se 1 (by rfl) ⟨1566905, by rfl⟩ : syracuseStep 2089207 = 3133811) B3133811
theorem B15059317 : Blo 2087435 15059317 := bbase (se 5 (by rfl) ⟨705905, by rfl⟩ : syracuseStep 15059317 = 1411811) (by norm_num)
theorem B20079089 : Blo 2087435 20079089 := bstep (se 2 (by rfl) ⟨7529658, by rfl⟩ : syracuseStep 20079089 = 15059317) B15059317
theorem B13386059 : Blo 2087435 13386059 := bstep (se 1 (by rfl) ⟨10039544, by rfl⟩ : syracuseStep 13386059 = 20079089) B20079089
theorem B8924039 : Blo 2087435 8924039 := bstep (se 1 (by rfl) ⟨6693029, by rfl⟩ : syracuseStep 8924039 = 13386059) B13386059
theorem B5949359 : Blo 2087435 5949359 := bstep (se 1 (by rfl) ⟨4462019, by rfl⟩ : syracuseStep 5949359 = 8924039) B8924039
theorem B3966239 : Blo 2087435 3966239 := bstep (se 1 (by rfl) ⟨2974679, by rfl⟩ : syracuseStep 3966239 = 5949359) B5949359
theorem B2644159 : Blo 2087435 2644159 := bstep (se 1 (by rfl) ⟨1983119, by rfl⟩ : syracuseStep 2644159 = 3966239) B3966239
theorem B3525545 : Blo 2087435 3525545 := bstep (se 2 (by rfl) ⟨1322079, by rfl⟩ : syracuseStep 3525545 = 2644159) B2644159
theorem B2350363 : Blo 2087435 2350363 := bstep (se 1 (by rfl) ⟨1762772, by rfl⟩ : syracuseStep 2350363 = 3525545) B3525545
theorem B3133817 : Blo 2087435 3133817 := bstep (se 2 (by rfl) ⟨1175181, by rfl⟩ : syracuseStep 3133817 = 2350363) B2350363
theorem B2089211 : Blo 2087435 2089211 := bstep (se 1 (by rfl) ⟨1566908, by rfl⟩ : syracuseStep 2089211 = 3133817) B3133817
theorem B35696213 : Blo 2087435 35696213 := bbase (se 8 (by rfl) ⟨209157, by rfl⟩ : syracuseStep 35696213 = 418315) (by norm_num)
theorem B23797475 : Blo 2087435 23797475 := bstep (se 1 (by rfl) ⟨17848106, by rfl⟩ : syracuseStep 23797475 = 35696213) B35696213
theorem B15864983 : Blo 2087435 15864983 := bstep (se 1 (by rfl) ⟨11898737, by rfl⟩ : syracuseStep 15864983 = 23797475) B23797475
theorem B10576655 : Blo 2087435 10576655 := bstep (se 1 (by rfl) ⟨7932491, by rfl⟩ : syracuseStep 10576655 = 15864983) B15864983
theorem B7051103 : Blo 2087435 7051103 := bstep (se 1 (by rfl) ⟨5288327, by rfl⟩ : syracuseStep 7051103 = 10576655) B10576655
theorem B4700735 : Blo 2087435 4700735 := bstep (se 1 (by rfl) ⟨3525551, by rfl⟩ : syracuseStep 4700735 = 7051103) B7051103
theorem B3133823 : Blo 2087435 3133823 := bstep (se 1 (by rfl) ⟨2350367, by rfl⟩ : syracuseStep 3133823 = 4700735) B4700735
theorem B2089215 : Blo 2087435 2089215 := bstep (se 1 (by rfl) ⟨1566911, by rfl⟩ : syracuseStep 2089215 = 3133823) B3133823
theorem B3133829 : Blo 2087435 3133829 := bbase (se 4 (by rfl) ⟨293796, by rfl⟩ : syracuseStep 3133829 = 587593) (by norm_num)
theorem B2089219 : Blo 2087435 2089219 := bstep (se 1 (by rfl) ⟨1566914, by rfl⟩ : syracuseStep 2089219 = 3133829) B3133829
theorem B3525565 : Blo 2087435 3525565 := bbase (se 3 (by rfl) ⟨661043, by rfl⟩ : syracuseStep 3525565 = 1322087) (by norm_num)
theorem B4700753 : Blo 2087435 4700753 := bstep (se 2 (by rfl) ⟨1762782, by rfl⟩ : syracuseStep 4700753 = 3525565) B3525565
theorem B3133835 : Blo 2087435 3133835 := bstep (se 1 (by rfl) ⟨2350376, by rfl⟩ : syracuseStep 3133835 = 4700753) B4700753
theorem B2089223 : Blo 2087435 2089223 := bstep (se 1 (by rfl) ⟨1566917, by rfl⟩ : syracuseStep 2089223 = 3133835) B3133835
theorem B2350381 : Blo 2087435 2350381 := bbase (se 3 (by rfl) ⟨440696, by rfl⟩ : syracuseStep 2350381 = 881393) (by norm_num)
theorem B3133841 : Blo 2087435 3133841 := bstep (se 2 (by rfl) ⟨1175190, by rfl⟩ : syracuseStep 3133841 = 2350381) B2350381
theorem B2089227 : Blo 2087435 2089227 := bstep (se 1 (by rfl) ⟨1566920, by rfl⟩ : syracuseStep 2089227 = 3133841) B3133841
theorem B7051157 : Blo 2087435 7051157 := bbase (se 6 (by rfl) ⟨165261, by rfl⟩ : syracuseStep 7051157 = 330523) (by norm_num)
theorem B4700771 : Blo 2087435 4700771 := bstep (se 1 (by rfl) ⟨3525578, by rfl⟩ : syracuseStep 4700771 = 7051157) B7051157
theorem B3133847 : Blo 2087435 3133847 := bstep (se 1 (by rfl) ⟨2350385, by rfl⟩ : syracuseStep 3133847 = 4700771) B4700771
theorem B2089231 : Blo 2087435 2089231 := bstep (se 1 (by rfl) ⟨1566923, by rfl⟩ : syracuseStep 2089231 = 3133847) B3133847
theorem B3133853 : Blo 2087435 3133853 := bbase (se 3 (by rfl) ⟨587597, by rfl⟩ : syracuseStep 3133853 = 1175195) (by norm_num)
theorem B2089235 : Blo 2087435 2089235 := bstep (se 1 (by rfl) ⟨1566926, by rfl⟩ : syracuseStep 2089235 = 3133853) B3133853
theorem B4700789 : Blo 2087435 4700789 := bbase (se 5 (by rfl) ⟨220349, by rfl⟩ : syracuseStep 4700789 = 440699) (by norm_num)
theorem B3133859 : Blo 2087435 3133859 := bstep (se 1 (by rfl) ⟨2350394, by rfl⟩ : syracuseStep 3133859 = 4700789) B4700789
theorem B2089239 : Blo 2087435 2089239 := bstep (se 1 (by rfl) ⟨1566929, by rfl⟩ : syracuseStep 2089239 = 3133859) B3133859
theorem B2117749 : Blo 2087435 2117749 := bbase (se 5 (by rfl) ⟨99269, by rfl⟩ : syracuseStep 2117749 = 198539) (by norm_num)
theorem B2823665 : Blo 2087435 2823665 := bstep (se 2 (by rfl) ⟨1058874, by rfl⟩ : syracuseStep 2823665 = 2117749) B2117749
theorem B7529773 : Blo 2087435 7529773 := bstep (se 3 (by rfl) ⟨1411832, by rfl⟩ : syracuseStep 7529773 = 2823665) B2823665
theorem B10039697 : Blo 2087435 10039697 := bstep (se 2 (by rfl) ⟨3764886, by rfl⟩ : syracuseStep 10039697 = 7529773) B7529773
theorem B6693131 : Blo 2087435 6693131 := bstep (se 1 (by rfl) ⟨5019848, by rfl⟩ : syracuseStep 6693131 = 10039697) B10039697
theorem B17848349 : Blo 2087435 17848349 := bstep (se 3 (by rfl) ⟨3346565, by rfl⟩ : syracuseStep 17848349 = 6693131) B6693131
theorem B11898899 : Blo 2087435 11898899 := bstep (se 1 (by rfl) ⟨8924174, by rfl⟩ : syracuseStep 11898899 = 17848349) B17848349
theorem B7932599 : Blo 2087435 7932599 := bstep (se 1 (by rfl) ⟨5949449, by rfl⟩ : syracuseStep 7932599 = 11898899) B11898899
theorem B5288399 : Blo 2087435 5288399 := bstep (se 1 (by rfl) ⟨3966299, by rfl⟩ : syracuseStep 5288399 = 7932599) B7932599
theorem B3525599 : Blo 2087435 3525599 := bstep (se 1 (by rfl) ⟨2644199, by rfl⟩ : syracuseStep 3525599 = 5288399) B5288399
theorem B2350399 : Blo 2087435 2350399 := bstep (se 1 (by rfl) ⟨1762799, by rfl⟩ : syracuseStep 2350399 = 3525599) B3525599
theorem B3133865 : Blo 2087435 3133865 := bstep (se 2 (by rfl) ⟨1175199, by rfl⟩ : syracuseStep 3133865 = 2350399) B2350399
theorem B2089243 : Blo 2087435 2089243 := bstep (se 1 (by rfl) ⟨1566932, by rfl⟩ : syracuseStep 2089243 = 3133865) B3133865
theorem B7932613 : Blo 2087435 7932613 := bbase (se 4 (by rfl) ⟨743682, by rfl⟩ : syracuseStep 7932613 = 1487365) (by norm_num)
theorem B10576817 : Blo 2087435 10576817 := bstep (se 2 (by rfl) ⟨3966306, by rfl⟩ : syracuseStep 10576817 = 7932613) B7932613
theorem B7051211 : Blo 2087435 7051211 := bstep (se 1 (by rfl) ⟨5288408, by rfl⟩ : syracuseStep 7051211 = 10576817) B10576817
theorem B4700807 : Blo 2087435 4700807 := bstep (se 1 (by rfl) ⟨3525605, by rfl⟩ : syracuseStep 4700807 = 7051211) B7051211
theorem B3133871 : Blo 2087435 3133871 := bstep (se 1 (by rfl) ⟨2350403, by rfl⟩ : syracuseStep 3133871 = 4700807) B4700807
theorem B2089247 : Blo 2087435 2089247 := bstep (se 1 (by rfl) ⟨1566935, by rfl⟩ : syracuseStep 2089247 = 3133871) B3133871
theorem B3133877 : Blo 2087435 3133877 := bbase (se 5 (by rfl) ⟨146900, by rfl⟩ : syracuseStep 3133877 = 293801) (by norm_num)
theorem B2089251 : Blo 2087435 2089251 := bstep (se 1 (by rfl) ⟨1566938, by rfl⟩ : syracuseStep 2089251 = 3133877) B3133877
theorem B5288429 : Blo 2087435 5288429 := bbase (se 3 (by rfl) ⟨991580, by rfl⟩ : syracuseStep 5288429 = 1983161) (by norm_num)
theorem B3525619 : Blo 2087435 3525619 := bstep (se 1 (by rfl) ⟨2644214, by rfl⟩ : syracuseStep 3525619 = 5288429) B5288429
theorem B4700825 : Blo 2087435 4700825 := bstep (se 2 (by rfl) ⟨1762809, by rfl⟩ : syracuseStep 4700825 = 3525619) B3525619
theorem B3133883 : Blo 2087435 3133883 := bstep (se 1 (by rfl) ⟨2350412, by rfl⟩ : syracuseStep 3133883 = 4700825) B4700825
theorem B2089255 : Blo 2087435 2089255 := bstep (se 1 (by rfl) ⟨1566941, by rfl⟩ : syracuseStep 2089255 = 3133883) B3133883
theorem B2350417 : Blo 2087435 2350417 := bbase (se 2 (by rfl) ⟨881406, by rfl⟩ : syracuseStep 2350417 = 1762813) (by norm_num)
theorem B3133889 : Blo 2087435 3133889 := bstep (se 2 (by rfl) ⟨1175208, by rfl⟩ : syracuseStep 3133889 = 2350417) B2350417
theorem B2089259 : Blo 2087435 2089259 := bstep (se 1 (by rfl) ⟨1566944, by rfl⟩ : syracuseStep 2089259 = 3133889) B3133889
theorem B2231065 : Blo 2087435 2231065 := bbase (se 2 (by rfl) ⟨836649, by rfl⟩ : syracuseStep 2231065 = 1673299) (by norm_num)
theorem B2974753 : Blo 2087435 2974753 := bstep (se 2 (by rfl) ⟨1115532, by rfl⟩ : syracuseStep 2974753 = 2231065) B2231065
theorem B3966337 : Blo 2087435 3966337 := bstep (se 2 (by rfl) ⟨1487376, by rfl⟩ : syracuseStep 3966337 = 2974753) B2974753
theorem B5288449 : Blo 2087435 5288449 := bstep (se 2 (by rfl) ⟨1983168, by rfl⟩ : syracuseStep 5288449 = 3966337) B3966337
theorem B7051265 : Blo 2087435 7051265 := bstep (se 2 (by rfl) ⟨2644224, by rfl⟩ : syracuseStep 7051265 = 5288449) B5288449
theorem B4700843 : Blo 2087435 4700843 := bstep (se 1 (by rfl) ⟨3525632, by rfl⟩ : syracuseStep 4700843 = 7051265) B7051265
theorem B3133895 : Blo 2087435 3133895 := bstep (se 1 (by rfl) ⟨2350421, by rfl⟩ : syracuseStep 3133895 = 4700843) B4700843
theorem B2089263 : Blo 2087435 2089263 := bstep (se 1 (by rfl) ⟨1566947, by rfl⟩ : syracuseStep 2089263 = 3133895) B3133895
theorem B3133901 : Blo 2087435 3133901 := bbase (se 3 (by rfl) ⟨587606, by rfl⟩ : syracuseStep 3133901 = 1175213) (by norm_num)
theorem B2089267 : Blo 2087435 2089267 := bstep (se 1 (by rfl) ⟨1566950, by rfl⟩ : syracuseStep 2089267 = 3133901) B3133901
theorem B4700861 : Blo 2087435 4700861 := bbase (se 3 (by rfl) ⟨881411, by rfl⟩ : syracuseStep 4700861 = 1762823) (by norm_num)
theorem B3133907 : Blo 2087435 3133907 := bstep (se 1 (by rfl) ⟨2350430, by rfl⟩ : syracuseStep 3133907 = 4700861) B4700861
theorem B2089271 : Blo 2087435 2089271 := bstep (se 1 (by rfl) ⟨1566953, by rfl⟩ : syracuseStep 2089271 = 3133907) B3133907
theorem B3525653 : Blo 2087435 3525653 := bbase (se 6 (by rfl) ⟨82632, by rfl⟩ : syracuseStep 3525653 = 165265) (by norm_num)
theorem B2350435 : Blo 2087435 2350435 := bstep (se 1 (by rfl) ⟨1762826, by rfl⟩ : syracuseStep 2350435 = 3525653) B3525653
theorem B3133913 : Blo 2087435 3133913 := bstep (se 2 (by rfl) ⟨1175217, by rfl⟩ : syracuseStep 3133913 = 2350435) B2350435
theorem B2089275 : Blo 2087435 2089275 := bstep (se 1 (by rfl) ⟨1566956, by rfl⟩ : syracuseStep 2089275 = 3133913) B3133913
theorem B8040965 : Blo 2087435 8040965 := bbase (se 4 (by rfl) ⟨753840, by rfl⟩ : syracuseStep 8040965 = 1507681) (by norm_num)
theorem B21442573 : Blo 2087435 21442573 := bstep (se 3 (by rfl) ⟨4020482, by rfl⟩ : syracuseStep 21442573 = 8040965) B8040965
theorem B28590097 : Blo 2087435 28590097 := bstep (se 2 (by rfl) ⟨10721286, by rfl⟩ : syracuseStep 28590097 = 21442573) B21442573
theorem B38120129 : Blo 2087435 38120129 := bstep (se 2 (by rfl) ⟨14295048, by rfl⟩ : syracuseStep 38120129 = 28590097) B28590097
theorem B25413419 : Blo 2087435 25413419 := bstep (se 1 (by rfl) ⟨19060064, by rfl⟩ : syracuseStep 25413419 = 38120129) B38120129
theorem B16942279 : Blo 2087435 16942279 := bstep (se 1 (by rfl) ⟨12706709, by rfl⟩ : syracuseStep 16942279 = 25413419) B25413419
theorem B22589705 : Blo 2087435 22589705 := bstep (se 2 (by rfl) ⟨8471139, by rfl⟩ : syracuseStep 22589705 = 16942279) B16942279
theorem B15059803 : Blo 2087435 15059803 := bstep (se 1 (by rfl) ⟨11294852, by rfl⟩ : syracuseStep 15059803 = 22589705) B22589705
theorem B20079737 : Blo 2087435 20079737 := bstep (se 2 (by rfl) ⟨7529901, by rfl⟩ : syracuseStep 20079737 = 15059803) B15059803
theorem B13386491 : Blo 2087435 13386491 := bstep (se 1 (by rfl) ⟨10039868, by rfl⟩ : syracuseStep 13386491 = 20079737) B20079737
theorem B8924327 : Blo 2087435 8924327 := bstep (se 1 (by rfl) ⟨6693245, by rfl⟩ : syracuseStep 8924327 = 13386491) B13386491
theorem B5949551 : Blo 2087435 5949551 := bstep (se 1 (by rfl) ⟨4462163, by rfl⟩ : syracuseStep 5949551 = 8924327) B8924327
theorem B15865469 : Blo 2087435 15865469 := bstep (se 3 (by rfl) ⟨2974775, by rfl⟩ : syracuseStep 15865469 = 5949551) B5949551
theorem B10576979 : Blo 2087435 10576979 := bstep (se 1 (by rfl) ⟨7932734, by rfl⟩ : syracuseStep 10576979 = 15865469) B15865469
theorem B7051319 : Blo 2087435 7051319 := bstep (se 1 (by rfl) ⟨5288489, by rfl⟩ : syracuseStep 7051319 = 10576979) B10576979
theorem B4700879 : Blo 2087435 4700879 := bstep (se 1 (by rfl) ⟨3525659, by rfl⟩ : syracuseStep 4700879 = 7051319) B7051319
theorem B3133919 : Blo 2087435 3133919 := bstep (se 1 (by rfl) ⟨2350439, by rfl⟩ : syracuseStep 3133919 = 4700879) B4700879
theorem B2089279 : Blo 2087435 2089279 := bstep (se 1 (by rfl) ⟨1566959, by rfl⟩ : syracuseStep 2089279 = 3133919) B3133919
theorem B3133925 : Blo 2087435 3133925 := bbase (se 4 (by rfl) ⟨293805, by rfl⟩ : syracuseStep 3133925 = 587611) (by norm_num)
theorem B2089283 : Blo 2087435 2089283 := bstep (se 1 (by rfl) ⟨1566962, by rfl⟩ : syracuseStep 2089283 = 3133925) B3133925
theorem B10039909 : Blo 2087435 10039909 := bbase (se 4 (by rfl) ⟨941241, by rfl⟩ : syracuseStep 10039909 = 1882483) (by norm_num)
theorem B13386545 : Blo 2087435 13386545 := bstep (se 2 (by rfl) ⟨5019954, by rfl⟩ : syracuseStep 13386545 = 10039909) B10039909
theorem B8924363 : Blo 2087435 8924363 := bstep (se 1 (by rfl) ⟨6693272, by rfl⟩ : syracuseStep 8924363 = 13386545) B13386545
theorem B5949575 : Blo 2087435 5949575 := bstep (se 1 (by rfl) ⟨4462181, by rfl⟩ : syracuseStep 5949575 = 8924363) B8924363
theorem B3966383 : Blo 2087435 3966383 := bstep (se 1 (by rfl) ⟨2974787, by rfl⟩ : syracuseStep 3966383 = 5949575) B5949575
theorem B2644255 : Blo 2087435 2644255 := bstep (se 1 (by rfl) ⟨1983191, by rfl⟩ : syracuseStep 2644255 = 3966383) B3966383
theorem B3525673 : Blo 2087435 3525673 := bstep (se 2 (by rfl) ⟨1322127, by rfl⟩ : syracuseStep 3525673 = 2644255) B2644255
theorem B4700897 : Blo 2087435 4700897 := bstep (se 2 (by rfl) ⟨1762836, by rfl⟩ : syracuseStep 4700897 = 3525673) B3525673
theorem B3133931 : Blo 2087435 3133931 := bstep (se 1 (by rfl) ⟨2350448, by rfl⟩ : syracuseStep 3133931 = 4700897) B4700897
theorem B2089287 : Blo 2087435 2089287 := bstep (se 1 (by rfl) ⟨1566965, by rfl⟩ : syracuseStep 2089287 = 3133931) B3133931
theorem B2350453 : Blo 2087435 2350453 := bbase (se 5 (by rfl) ⟨110177, by rfl⟩ : syracuseStep 2350453 = 220355) (by norm_num)
theorem B3133937 : Blo 2087435 3133937 := bstep (se 2 (by rfl) ⟨1175226, by rfl⟩ : syracuseStep 3133937 = 2350453) B2350453
theorem B2089291 : Blo 2087435 2089291 := bstep (se 1 (by rfl) ⟨1566968, by rfl⟩ : syracuseStep 2089291 = 3133937) B3133937
theorem B2644265 : Blo 2087435 2644265 := bbase (se 2 (by rfl) ⟨991599, by rfl⟩ : syracuseStep 2644265 = 1983199) (by norm_num)
theorem B7051373 : Blo 2087435 7051373 := bstep (se 3 (by rfl) ⟨1322132, by rfl⟩ : syracuseStep 7051373 = 2644265) B2644265
theorem B4700915 : Blo 2087435 4700915 := bstep (se 1 (by rfl) ⟨3525686, by rfl⟩ : syracuseStep 4700915 = 7051373) B7051373
theorem B3133943 : Blo 2087435 3133943 := bstep (se 1 (by rfl) ⟨2350457, by rfl⟩ : syracuseStep 3133943 = 4700915) B4700915
theorem B2089295 : Blo 2087435 2089295 := bstep (se 1 (by rfl) ⟨1566971, by rfl⟩ : syracuseStep 2089295 = 3133943) B3133943
theorem B3133949 : Blo 2087435 3133949 := bbase (se 3 (by rfl) ⟨587615, by rfl⟩ : syracuseStep 3133949 = 1175231) (by norm_num)
theorem B2089299 : Blo 2087435 2089299 := bstep (se 1 (by rfl) ⟨1566974, by rfl⟩ : syracuseStep 2089299 = 3133949) B3133949
theorem B4700933 : Blo 2087435 4700933 := bbase (se 4 (by rfl) ⟨440712, by rfl⟩ : syracuseStep 4700933 = 881425) (by norm_num)
theorem B3133955 : Blo 2087435 3133955 := bstep (se 1 (by rfl) ⟨2350466, by rfl⟩ : syracuseStep 3133955 = 4700933) B4700933
theorem B2089303 : Blo 2087435 2089303 := bstep (se 1 (by rfl) ⟨1566977, by rfl⟩ : syracuseStep 2089303 = 3133955) B3133955
theorem B3966421 : Blo 2087435 3966421 := bbase (se 7 (by rfl) ⟨46481, by rfl⟩ : syracuseStep 3966421 = 92963) (by norm_num)
theorem B5288561 : Blo 2087435 5288561 := bstep (se 2 (by rfl) ⟨1983210, by rfl⟩ : syracuseStep 5288561 = 3966421) B3966421
theorem B3525707 : Blo 2087435 3525707 := bstep (se 1 (by rfl) ⟨2644280, by rfl⟩ : syracuseStep 3525707 = 5288561) B5288561
theorem B2350471 : Blo 2087435 2350471 := bstep (se 1 (by rfl) ⟨1762853, by rfl⟩ : syracuseStep 2350471 = 3525707) B3525707
theorem B3133961 : Blo 2087435 3133961 := bstep (se 2 (by rfl) ⟨1175235, by rfl⟩ : syracuseStep 3133961 = 2350471) B2350471
theorem B2089307 : Blo 2087435 2089307 := bstep (se 1 (by rfl) ⟨1566980, by rfl⟩ : syracuseStep 2089307 = 3133961) B3133961
theorem B10577141 : Blo 2087435 10577141 := bbase (se 5 (by rfl) ⟨495803, by rfl⟩ : syracuseStep 10577141 = 991607) (by norm_num)
theorem B7051427 : Blo 2087435 7051427 := bstep (se 1 (by rfl) ⟨5288570, by rfl⟩ : syracuseStep 7051427 = 10577141) B10577141
theorem B4700951 : Blo 2087435 4700951 := bstep (se 1 (by rfl) ⟨3525713, by rfl⟩ : syracuseStep 4700951 = 7051427) B7051427
theorem B3133967 : Blo 2087435 3133967 := bstep (se 1 (by rfl) ⟨2350475, by rfl⟩ : syracuseStep 3133967 = 4700951) B4700951
theorem B2089311 : Blo 2087435 2089311 := bstep (se 1 (by rfl) ⟨1566983, by rfl⟩ : syracuseStep 2089311 = 3133967) B3133967
theorem B3133973 : Blo 2087435 3133973 := bbase (se 6 (by rfl) ⟨73452, by rfl⟩ : syracuseStep 3133973 = 146905) (by norm_num)
theorem B2089315 : Blo 2087435 2089315 := bstep (se 1 (by rfl) ⟨1566986, by rfl⟩ : syracuseStep 2089315 = 3133973) B3133973
theorem B2146721 : Blo 2087435 2146721 := bbase (se 2 (by rfl) ⟨805020, by rfl⟩ : syracuseStep 2146721 = 1610041) (by norm_num)
theorem B5724589 : Blo 2087435 5724589 := bstep (se 3 (by rfl) ⟨1073360, by rfl⟩ : syracuseStep 5724589 = 2146721) B2146721
theorem B7632785 : Blo 2087435 7632785 := bstep (se 2 (by rfl) ⟨2862294, by rfl⟩ : syracuseStep 7632785 = 5724589) B5724589
theorem B5088523 : Blo 2087435 5088523 := bstep (se 1 (by rfl) ⟨3816392, by rfl⟩ : syracuseStep 5088523 = 7632785) B7632785
theorem B6784697 : Blo 2087435 6784697 := bstep (se 2 (by rfl) ⟨2544261, by rfl⟩ : syracuseStep 6784697 = 5088523) B5088523
theorem B4523131 : Blo 2087435 4523131 := bstep (se 1 (by rfl) ⟨3392348, by rfl⟩ : syracuseStep 4523131 = 6784697) B6784697
theorem B6030841 : Blo 2087435 6030841 := bstep (se 2 (by rfl) ⟨2261565, by rfl⟩ : syracuseStep 6030841 = 4523131) B4523131
theorem B8041121 : Blo 2087435 8041121 := bstep (se 2 (by rfl) ⟨3015420, by rfl⟩ : syracuseStep 8041121 = 6030841) B6030841
theorem B5360747 : Blo 2087435 5360747 := bstep (se 1 (by rfl) ⟨4020560, by rfl⟩ : syracuseStep 5360747 = 8041121) B8041121
theorem B57181301 : Blo 2087435 57181301 := bstep (se 5 (by rfl) ⟨2680373, by rfl⟩ : syracuseStep 57181301 = 5360747) B5360747
theorem B38120867 : Blo 2087435 38120867 := bstep (se 1 (by rfl) ⟨28590650, by rfl⟩ : syracuseStep 38120867 = 57181301) B57181301
theorem B25413911 : Blo 2087435 25413911 := bstep (se 1 (by rfl) ⟨19060433, by rfl⟩ : syracuseStep 25413911 = 38120867) B38120867
theorem B16942607 : Blo 2087435 16942607 := bstep (se 1 (by rfl) ⟨12706955, by rfl⟩ : syracuseStep 16942607 = 25413911) B25413911
theorem B11295071 : Blo 2087435 11295071 := bstep (se 1 (by rfl) ⟨8471303, by rfl⟩ : syracuseStep 11295071 = 16942607) B16942607
theorem B7530047 : Blo 2087435 7530047 := bstep (se 1 (by rfl) ⟨5647535, by rfl⟩ : syracuseStep 7530047 = 11295071) B11295071
theorem B5020031 : Blo 2087435 5020031 := bstep (se 1 (by rfl) ⟨3765023, by rfl⟩ : syracuseStep 5020031 = 7530047) B7530047
theorem B3346687 : Blo 2087435 3346687 := bstep (se 1 (by rfl) ⟨2510015, by rfl⟩ : syracuseStep 3346687 = 5020031) B5020031
theorem B17848997 : Blo 2087435 17848997 := bstep (se 4 (by rfl) ⟨1673343, by rfl⟩ : syracuseStep 17848997 = 3346687) B3346687
theorem B11899331 : Blo 2087435 11899331 := bstep (se 1 (by rfl) ⟨8924498, by rfl⟩ : syracuseStep 11899331 = 17848997) B17848997
theorem B7932887 : Blo 2087435 7932887 := bstep (se 1 (by rfl) ⟨5949665, by rfl⟩ : syracuseStep 7932887 = 11899331) B11899331
theorem B5288591 : Blo 2087435 5288591 := bstep (se 1 (by rfl) ⟨3966443, by rfl⟩ : syracuseStep 5288591 = 7932887) B7932887
theorem B3525727 : Blo 2087435 3525727 := bstep (se 1 (by rfl) ⟨2644295, by rfl⟩ : syracuseStep 3525727 = 5288591) B5288591
theorem B4700969 : Blo 2087435 4700969 := bstep (se 2 (by rfl) ⟨1762863, by rfl⟩ : syracuseStep 4700969 = 3525727) B3525727
theorem B3133979 : Blo 2087435 3133979 := bstep (se 1 (by rfl) ⟨2350484, by rfl⟩ : syracuseStep 3133979 = 4700969) B4700969
theorem B2089319 : Blo 2087435 2089319 := bstep (se 1 (by rfl) ⟨1566989, by rfl⟩ : syracuseStep 2089319 = 3133979) B3133979
theorem B2350489 : Blo 2087435 2350489 := bbase (se 2 (by rfl) ⟨881433, by rfl⟩ : syracuseStep 2350489 = 1762867) (by norm_num)
theorem B3133985 : Blo 2087435 3133985 := bstep (se 2 (by rfl) ⟨1175244, by rfl⟩ : syracuseStep 3133985 = 2350489) B2350489
theorem B2089323 : Blo 2087435 2089323 := bstep (se 1 (by rfl) ⟨1566992, by rfl⟩ : syracuseStep 2089323 = 3133985) B3133985
theorem B7932917 : Blo 2087435 7932917 := bbase (se 5 (by rfl) ⟨371855, by rfl⟩ : syracuseStep 7932917 = 743711) (by norm_num)
theorem B5288611 : Blo 2087435 5288611 := bstep (se 1 (by rfl) ⟨3966458, by rfl⟩ : syracuseStep 5288611 = 7932917) B7932917
theorem B7051481 : Blo 2087435 7051481 := bstep (se 2 (by rfl) ⟨2644305, by rfl⟩ : syracuseStep 7051481 = 5288611) B5288611
theorem B4700987 : Blo 2087435 4700987 := bstep (se 1 (by rfl) ⟨3525740, by rfl⟩ : syracuseStep 4700987 = 7051481) B7051481
theorem B3133991 : Blo 2087435 3133991 := bstep (se 1 (by rfl) ⟨2350493, by rfl⟩ : syracuseStep 3133991 = 4700987) B4700987
theorem B2089327 : Blo 2087435 2089327 := bstep (se 1 (by rfl) ⟨1566995, by rfl⟩ : syracuseStep 2089327 = 3133991) B3133991
theorem B3133997 : Blo 2087435 3133997 := bbase (se 3 (by rfl) ⟨587624, by rfl⟩ : syracuseStep 3133997 = 1175249) (by norm_num)
theorem B2089331 : Blo 2087435 2089331 := bstep (se 1 (by rfl) ⟨1566998, by rfl⟩ : syracuseStep 2089331 = 3133997) B3133997
theorem B4701005 : Blo 2087435 4701005 := bbase (se 3 (by rfl) ⟨881438, by rfl⟩ : syracuseStep 4701005 = 1762877) (by norm_num)
theorem B3134003 : Blo 2087435 3134003 := bstep (se 1 (by rfl) ⟨2350502, by rfl⟩ : syracuseStep 3134003 = 4701005) B4701005
theorem B2089335 : Blo 2087435 2089335 := bstep (se 1 (by rfl) ⟨1567001, by rfl⟩ : syracuseStep 2089335 = 3134003) B3134003
theorem B2644321 : Blo 2087435 2644321 := bbase (se 2 (by rfl) ⟨991620, by rfl⟩ : syracuseStep 2644321 = 1983241) (by norm_num)
theorem B3525761 : Blo 2087435 3525761 := bstep (se 2 (by rfl) ⟨1322160, by rfl⟩ : syracuseStep 3525761 = 2644321) B2644321
theorem B2350507 : Blo 2087435 2350507 := bstep (se 1 (by rfl) ⟨1762880, by rfl⟩ : syracuseStep 2350507 = 3525761) B3525761
theorem B3134009 : Blo 2087435 3134009 := bstep (se 2 (by rfl) ⟨1175253, by rfl⟩ : syracuseStep 3134009 = 2350507) B2350507
theorem B2089339 : Blo 2087435 2089339 := bstep (se 1 (by rfl) ⟨1567004, by rfl⟩ : syracuseStep 2089339 = 3134009) B3134009
theorem B23798933 : Blo 2087435 23798933 := bbase (se 6 (by rfl) ⟨557787, by rfl⟩ : syracuseStep 23798933 = 1115575) (by norm_num)
theorem B15865955 : Blo 2087435 15865955 := bstep (se 1 (by rfl) ⟨11899466, by rfl⟩ : syracuseStep 15865955 = 23798933) B23798933
theorem B10577303 : Blo 2087435 10577303 := bstep (se 1 (by rfl) ⟨7932977, by rfl⟩ : syracuseStep 10577303 = 15865955) B15865955
theorem B7051535 : Blo 2087435 7051535 := bstep (se 1 (by rfl) ⟨5288651, by rfl⟩ : syracuseStep 7051535 = 10577303) B10577303
theorem B4701023 : Blo 2087435 4701023 := bstep (se 1 (by rfl) ⟨3525767, by rfl⟩ : syracuseStep 4701023 = 7051535) B7051535
theorem B3134015 : Blo 2087435 3134015 := bstep (se 1 (by rfl) ⟨2350511, by rfl⟩ : syracuseStep 3134015 = 4701023) B4701023
theorem B2089343 : Blo 2087435 2089343 := bstep (se 1 (by rfl) ⟨1567007, by rfl⟩ : syracuseStep 2089343 = 3134015) B3134015
theorem B3134021 : Blo 2087435 3134021 := bbase (se 4 (by rfl) ⟨293814, by rfl⟩ : syracuseStep 3134021 = 587629) (by norm_num)
theorem B2089347 : Blo 2087435 2089347 := bstep (se 1 (by rfl) ⟨1567010, by rfl⟩ : syracuseStep 2089347 = 3134021) B3134021
theorem B3525781 : Blo 2087435 3525781 := bbase (se 6 (by rfl) ⟨82635, by rfl⟩ : syracuseStep 3525781 = 165271) (by norm_num)
theorem B4701041 : Blo 2087435 4701041 := bstep (se 2 (by rfl) ⟨1762890, by rfl⟩ : syracuseStep 4701041 = 3525781) B3525781
theorem B3134027 : Blo 2087435 3134027 := bstep (se 1 (by rfl) ⟨2350520, by rfl⟩ : syracuseStep 3134027 = 4701041) B4701041
theorem B2089351 : Blo 2087435 2089351 := bstep (se 1 (by rfl) ⟨1567013, by rfl⟩ : syracuseStep 2089351 = 3134027) B3134027
theorem B2350525 : Blo 2087435 2350525 := bbase (se 3 (by rfl) ⟨440723, by rfl⟩ : syracuseStep 2350525 = 881447) (by norm_num)
theorem B3134033 : Blo 2087435 3134033 := bstep (se 2 (by rfl) ⟨1175262, by rfl⟩ : syracuseStep 3134033 = 2350525) B2350525
theorem B2089355 : Blo 2087435 2089355 := bstep (se 1 (by rfl) ⟨1567016, by rfl⟩ : syracuseStep 2089355 = 3134033) B3134033
theorem B7051589 : Blo 2087435 7051589 := bbase (se 4 (by rfl) ⟨661086, by rfl⟩ : syracuseStep 7051589 = 1322173) (by norm_num)
theorem B4701059 : Blo 2087435 4701059 := bstep (se 1 (by rfl) ⟨3525794, by rfl⟩ : syracuseStep 4701059 = 7051589) B7051589
theorem B3134039 : Blo 2087435 3134039 := bstep (se 1 (by rfl) ⟨2350529, by rfl⟩ : syracuseStep 3134039 = 4701059) B4701059
theorem B2089359 : Blo 2087435 2089359 := bstep (se 1 (by rfl) ⟨1567019, by rfl⟩ : syracuseStep 2089359 = 3134039) B3134039
theorem B3134045 : Blo 2087435 3134045 := bbase (se 3 (by rfl) ⟨587633, by rfl⟩ : syracuseStep 3134045 = 1175267) (by norm_num)
theorem B2089363 : Blo 2087435 2089363 := bstep (se 1 (by rfl) ⟨1567022, by rfl⟩ : syracuseStep 2089363 = 3134045) B3134045
theorem B4701077 : Blo 2087435 4701077 := bbase (se 6 (by rfl) ⟨110181, by rfl⟩ : syracuseStep 4701077 = 220363) (by norm_num)
theorem B3134051 : Blo 2087435 3134051 := bstep (se 1 (by rfl) ⟨2350538, by rfl⟩ : syracuseStep 3134051 = 4701077) B4701077
theorem B2089367 : Blo 2087435 2089367 := bstep (se 1 (by rfl) ⟨1567025, by rfl⟩ : syracuseStep 2089367 = 3134051) B3134051
theorem B5020157 : Blo 2087435 5020157 := bbase (se 3 (by rfl) ⟨941279, by rfl⟩ : syracuseStep 5020157 = 1882559) (by norm_num)
theorem B3346771 : Blo 2087435 3346771 := bstep (se 1 (by rfl) ⟨2510078, by rfl⟩ : syracuseStep 3346771 = 5020157) B5020157
theorem B4462361 : Blo 2087435 4462361 := bstep (se 2 (by rfl) ⟨1673385, by rfl⟩ : syracuseStep 4462361 = 3346771) B3346771
theorem B2974907 : Blo 2087435 2974907 := bstep (se 1 (by rfl) ⟨2231180, by rfl⟩ : syracuseStep 2974907 = 4462361) B4462361
theorem B7933085 : Blo 2087435 7933085 := bstep (se 3 (by rfl) ⟨1487453, by rfl⟩ : syracuseStep 7933085 = 2974907) B2974907
theorem B5288723 : Blo 2087435 5288723 := bstep (se 1 (by rfl) ⟨3966542, by rfl⟩ : syracuseStep 5288723 = 7933085) B7933085
theorem B3525815 : Blo 2087435 3525815 := bstep (se 1 (by rfl) ⟨2644361, by rfl⟩ : syracuseStep 3525815 = 5288723) B5288723
theorem B2350543 : Blo 2087435 2350543 := bstep (se 1 (by rfl) ⟨1762907, by rfl⟩ : syracuseStep 2350543 = 3525815) B3525815
theorem B3134057 : Blo 2087435 3134057 := bstep (se 2 (by rfl) ⟨1175271, by rfl⟩ : syracuseStep 3134057 = 2350543) B2350543
theorem B2089371 : Blo 2087435 2089371 := bstep (se 1 (by rfl) ⟨1567028, by rfl⟩ : syracuseStep 2089371 = 3134057) B3134057
theorem B5020165 : Blo 2087435 5020165 := bbase (se 4 (by rfl) ⟨470640, by rfl⟩ : syracuseStep 5020165 = 941281) (by norm_num)
theorem B6693553 : Blo 2087435 6693553 := bstep (se 2 (by rfl) ⟨2510082, by rfl⟩ : syracuseStep 6693553 = 5020165) B5020165
theorem B8924737 : Blo 2087435 8924737 := bstep (se 2 (by rfl) ⟨3346776, by rfl⟩ : syracuseStep 8924737 = 6693553) B6693553
theorem B11899649 : Blo 2087435 11899649 := bstep (se 2 (by rfl) ⟨4462368, by rfl⟩ : syracuseStep 11899649 = 8924737) B8924737
theorem B7933099 : Blo 2087435 7933099 := bstep (se 1 (by rfl) ⟨5949824, by rfl⟩ : syracuseStep 7933099 = 11899649) B11899649
theorem B10577465 : Blo 2087435 10577465 := bstep (se 2 (by rfl) ⟨3966549, by rfl⟩ : syracuseStep 10577465 = 7933099) B7933099
theorem B7051643 : Blo 2087435 7051643 := bstep (se 1 (by rfl) ⟨5288732, by rfl⟩ : syracuseStep 7051643 = 10577465) B10577465
theorem B4701095 : Blo 2087435 4701095 := bstep (se 1 (by rfl) ⟨3525821, by rfl⟩ : syracuseStep 4701095 = 7051643) B7051643
theorem B3134063 : Blo 2087435 3134063 := bstep (se 1 (by rfl) ⟨2350547, by rfl⟩ : syracuseStep 3134063 = 4701095) B4701095
theorem B2089375 : Blo 2087435 2089375 := bstep (se 1 (by rfl) ⟨1567031, by rfl⟩ : syracuseStep 2089375 = 3134063) B3134063
theorem B3134069 : Blo 2087435 3134069 := bbase (se 5 (by rfl) ⟨146909, by rfl⟩ : syracuseStep 3134069 = 293819) (by norm_num)
theorem B2089379 : Blo 2087435 2089379 := bstep (se 1 (by rfl) ⟨1567034, by rfl⟩ : syracuseStep 2089379 = 3134069) B3134069
theorem B3966565 : Blo 2087435 3966565 := bbase (se 4 (by rfl) ⟨371865, by rfl⟩ : syracuseStep 3966565 = 743731) (by norm_num)
theorem B5288753 : Blo 2087435 5288753 := bstep (se 2 (by rfl) ⟨1983282, by rfl⟩ : syracuseStep 5288753 = 3966565) B3966565
theorem B3525835 : Blo 2087435 3525835 := bstep (se 1 (by rfl) ⟨2644376, by rfl⟩ : syracuseStep 3525835 = 5288753) B5288753
theorem B4701113 : Blo 2087435 4701113 := bstep (se 2 (by rfl) ⟨1762917, by rfl⟩ : syracuseStep 4701113 = 3525835) B3525835
theorem B3134075 : Blo 2087435 3134075 := bstep (se 1 (by rfl) ⟨2350556, by rfl⟩ : syracuseStep 3134075 = 4701113) B4701113
theorem B2089383 : Blo 2087435 2089383 := bstep (se 1 (by rfl) ⟨1567037, by rfl⟩ : syracuseStep 2089383 = 3134075) B3134075
theorem B2350561 : Blo 2087435 2350561 := bbase (se 2 (by rfl) ⟨881460, by rfl⟩ : syracuseStep 2350561 = 1762921) (by norm_num)
theorem B3134081 : Blo 2087435 3134081 := bstep (se 2 (by rfl) ⟨1175280, by rfl⟩ : syracuseStep 3134081 = 2350561) B2350561
theorem B2089387 : Blo 2087435 2089387 := bstep (se 1 (by rfl) ⟨1567040, by rfl⟩ : syracuseStep 2089387 = 3134081) B3134081
theorem B5288773 : Blo 2087435 5288773 := bbase (se 4 (by rfl) ⟨495822, by rfl⟩ : syracuseStep 5288773 = 991645) (by norm_num)
theorem B7051697 : Blo 2087435 7051697 := bstep (se 2 (by rfl) ⟨2644386, by rfl⟩ : syracuseStep 7051697 = 5288773) B5288773
theorem B4701131 : Blo 2087435 4701131 := bstep (se 1 (by rfl) ⟨3525848, by rfl⟩ : syracuseStep 4701131 = 7051697) B7051697
theorem B3134087 : Blo 2087435 3134087 := bstep (se 1 (by rfl) ⟨2350565, by rfl⟩ : syracuseStep 3134087 = 4701131) B4701131
theorem B2089391 : Blo 2087435 2089391 := bstep (se 1 (by rfl) ⟨1567043, by rfl⟩ : syracuseStep 2089391 = 3134087) B3134087
theorem B3134093 : Blo 2087435 3134093 := bbase (se 3 (by rfl) ⟨587642, by rfl⟩ : syracuseStep 3134093 = 1175285) (by norm_num)
theorem B2089395 : Blo 2087435 2089395 := bstep (se 1 (by rfl) ⟨1567046, by rfl⟩ : syracuseStep 2089395 = 3134093) B3134093
theorem B4701149 : Blo 2087435 4701149 := bbase (se 3 (by rfl) ⟨881465, by rfl⟩ : syracuseStep 4701149 = 1762931) (by norm_num)
theorem B3134099 : Blo 2087435 3134099 := bstep (se 1 (by rfl) ⟨2350574, by rfl⟩ : syracuseStep 3134099 = 4701149) B4701149
theorem B2089399 : Blo 2087435 2089399 := bstep (se 1 (by rfl) ⟨1567049, by rfl⟩ : syracuseStep 2089399 = 3134099) B3134099
theorem B3525869 : Blo 2087435 3525869 := bbase (se 3 (by rfl) ⟨661100, by rfl⟩ : syracuseStep 3525869 = 1322201) (by norm_num)
theorem B2350579 : Blo 2087435 2350579 := bstep (se 1 (by rfl) ⟨1762934, by rfl⟩ : syracuseStep 2350579 = 3525869) B3525869
theorem B3134105 : Blo 2087435 3134105 := bstep (se 2 (by rfl) ⟨1175289, by rfl⟩ : syracuseStep 3134105 = 2350579) B2350579
theorem B2089403 : Blo 2087435 2089403 := bstep (se 1 (by rfl) ⟨1567052, by rfl⟩ : syracuseStep 2089403 = 3134105) B3134105
theorem B15060725 : Blo 2087435 15060725 := bbase (se 5 (by rfl) ⟨705971, by rfl⟩ : syracuseStep 15060725 = 1411943) (by norm_num)
theorem B10040483 : Blo 2087435 10040483 := bstep (se 1 (by rfl) ⟨7530362, by rfl⟩ : syracuseStep 10040483 = 15060725) B15060725
theorem B26774621 : Blo 2087435 26774621 := bstep (se 3 (by rfl) ⟨5020241, by rfl⟩ : syracuseStep 26774621 = 10040483) B10040483
theorem B17849747 : Blo 2087435 17849747 := bstep (se 1 (by rfl) ⟨13387310, by rfl⟩ : syracuseStep 17849747 = 26774621) B26774621
theorem B11899831 : Blo 2087435 11899831 := bstep (se 1 (by rfl) ⟨8924873, by rfl⟩ : syracuseStep 11899831 = 17849747) B17849747
theorem B15866441 : Blo 2087435 15866441 := bstep (se 2 (by rfl) ⟨5949915, by rfl⟩ : syracuseStep 15866441 = 11899831) B11899831
theorem B10577627 : Blo 2087435 10577627 := bstep (se 1 (by rfl) ⟨7933220, by rfl⟩ : syracuseStep 10577627 = 15866441) B15866441
theorem B7051751 : Blo 2087435 7051751 := bstep (se 1 (by rfl) ⟨5288813, by rfl⟩ : syracuseStep 7051751 = 10577627) B10577627
theorem B4701167 : Blo 2087435 4701167 := bstep (se 1 (by rfl) ⟨3525875, by rfl⟩ : syracuseStep 4701167 = 7051751) B7051751
theorem B3134111 : Blo 2087435 3134111 := bstep (se 1 (by rfl) ⟨2350583, by rfl⟩ : syracuseStep 3134111 = 4701167) B4701167
theorem B2089407 : Blo 2087435 2089407 := bstep (se 1 (by rfl) ⟨1567055, by rfl⟩ : syracuseStep 2089407 = 3134111) B3134111
theorem B3134117 : Blo 2087435 3134117 := bbase (se 4 (by rfl) ⟨293823, by rfl⟩ : syracuseStep 3134117 = 587647) (by norm_num)
theorem B2089411 : Blo 2087435 2089411 := bstep (se 1 (by rfl) ⟨1567058, by rfl⟩ : syracuseStep 2089411 = 3134117) B3134117
theorem B2644417 : Blo 2087435 2644417 := bbase (se 2 (by rfl) ⟨991656, by rfl⟩ : syracuseStep 2644417 = 1983313) (by norm_num)
theorem B3525889 : Blo 2087435 3525889 := bstep (se 2 (by rfl) ⟨1322208, by rfl⟩ : syracuseStep 3525889 = 2644417) B2644417
theorem B4701185 : Blo 2087435 4701185 := bstep (se 2 (by rfl) ⟨1762944, by rfl⟩ : syracuseStep 4701185 = 3525889) B3525889
theorem B3134123 : Blo 2087435 3134123 := bstep (se 1 (by rfl) ⟨2350592, by rfl⟩ : syracuseStep 3134123 = 4701185) B4701185
theorem B2089415 : Blo 2087435 2089415 := bstep (se 1 (by rfl) ⟨1567061, by rfl⟩ : syracuseStep 2089415 = 3134123) B3134123
theorem B2350597 : Blo 2087435 2350597 := bbase (se 4 (by rfl) ⟨220368, by rfl⟩ : syracuseStep 2350597 = 440737) (by norm_num)
theorem B3134129 : Blo 2087435 3134129 := bstep (se 2 (by rfl) ⟨1175298, by rfl⟩ : syracuseStep 3134129 = 2350597) B2350597
theorem B2089419 : Blo 2087435 2089419 := bstep (se 1 (by rfl) ⟨1567064, by rfl⟩ : syracuseStep 2089419 = 3134129) B3134129
theorem B2974981 : Blo 2087435 2974981 := bbase (se 4 (by rfl) ⟨278904, by rfl⟩ : syracuseStep 2974981 = 557809) (by norm_num)
theorem B3966641 : Blo 2087435 3966641 := bstep (se 2 (by rfl) ⟨1487490, by rfl⟩ : syracuseStep 3966641 = 2974981) B2974981
theorem B2644427 : Blo 2087435 2644427 := bstep (se 1 (by rfl) ⟨1983320, by rfl⟩ : syracuseStep 2644427 = 3966641) B3966641
theorem B7051805 : Blo 2087435 7051805 := bstep (se 3 (by rfl) ⟨1322213, by rfl⟩ : syracuseStep 7051805 = 2644427) B2644427
theorem B4701203 : Blo 2087435 4701203 := bstep (se 1 (by rfl) ⟨3525902, by rfl⟩ : syracuseStep 4701203 = 7051805) B7051805
theorem B3134135 : Blo 2087435 3134135 := bstep (se 1 (by rfl) ⟨2350601, by rfl⟩ : syracuseStep 3134135 = 4701203) B4701203
theorem B2089423 : Blo 2087435 2089423 := bstep (se 1 (by rfl) ⟨1567067, by rfl⟩ : syracuseStep 2089423 = 3134135) B3134135
theorem B3134141 : Blo 2087435 3134141 := bbase (se 3 (by rfl) ⟨587651, by rfl⟩ : syracuseStep 3134141 = 1175303) (by norm_num)
theorem B2089427 : Blo 2087435 2089427 := bstep (se 1 (by rfl) ⟨1567070, by rfl⟩ : syracuseStep 2089427 = 3134141) B3134141
theorem B4701221 : Blo 2087435 4701221 := bbase (se 4 (by rfl) ⟨440739, by rfl⟩ : syracuseStep 4701221 = 881479) (by norm_num)
theorem B3134147 : Blo 2087435 3134147 := bstep (se 1 (by rfl) ⟨2350610, by rfl⟩ : syracuseStep 3134147 = 4701221) B4701221
theorem B2089431 : Blo 2087435 2089431 := bstep (se 1 (by rfl) ⟨1567073, by rfl⟩ : syracuseStep 2089431 = 3134147) B3134147
theorem B5288885 : Blo 2087435 5288885 := bbase (se 5 (by rfl) ⟨247916, by rfl⟩ : syracuseStep 5288885 = 495833) (by norm_num)
theorem B3525923 : Blo 2087435 3525923 := bstep (se 1 (by rfl) ⟨2644442, by rfl⟩ : syracuseStep 3525923 = 5288885) B5288885
theorem B2350615 : Blo 2087435 2350615 := bstep (se 1 (by rfl) ⟨1762961, by rfl⟩ : syracuseStep 2350615 = 3525923) B3525923
theorem B3134153 : Blo 2087435 3134153 := bstep (se 2 (by rfl) ⟨1175307, by rfl⟩ : syracuseStep 3134153 = 2350615) B2350615
theorem B2089435 : Blo 2087435 2089435 := bstep (se 1 (by rfl) ⟨1567076, by rfl⟩ : syracuseStep 2089435 = 3134153) B3134153
theorem C0 (j : ℕ) (h1 : 521858 ≤ j) (h2 : j ≤ 522358) : Blo 2087435 (4 * j + 3) := by
  interval_cases j
  · exact B2087435
  · exact B2087439
  · exact B2087443
  · exact B2087447
  · exact B2087451
  · exact B2087455
  · exact B2087459
  · exact B2087463
  · exact B2087467
  · exact B2087471
  · exact B2087475
  · exact B2087479
  · exact B2087483
  · exact B2087487
  · exact B2087491
  · exact B2087495
  · exact B2087499
  · exact B2087503
  · exact B2087507
  · exact B2087511
  · exact B2087515
  · exact B2087519
  · exact B2087523
  · exact B2087527
  · exact B2087531
  · exact B2087535
  · exact B2087539
  · exact B2087543
  · exact B2087547
  · exact B2087551
  · exact B2087555
  · exact B2087559
  · exact B2087563
  · exact B2087567
  · exact B2087571
  · exact B2087575
  · exact B2087579
  · exact B2087583
  · exact B2087587
  · exact B2087591
  · exact B2087595
  · exact B2087599
  · exact B2087603
  · exact B2087607
  · exact B2087611
  · exact B2087615
  · exact B2087619
  · exact B2087623
  · exact B2087627
  · exact B2087631
  · exact B2087635
  · exact B2087639
  · exact B2087643
  · exact B2087647
  · exact B2087651
  · exact B2087655
  · exact B2087659
  · exact B2087663
  · exact B2087667
  · exact B2087671
  · exact B2087675
  · exact B2087679
  · exact B2087683
  · exact B2087687
  · exact B2087691
  · exact B2087695
  · exact B2087699
  · exact B2087703
  · exact B2087707
  · exact B2087711
  · exact B2087715
  · exact B2087719
  · exact B2087723
  · exact B2087727
  · exact B2087731
  · exact B2087735
  · exact B2087739
  · exact B2087743
  · exact B2087747
  · exact B2087751
  · exact B2087755
  · exact B2087759
  · exact B2087763
  · exact B2087767
  · exact B2087771
  · exact B2087775
  · exact B2087779
  · exact B2087783
  · exact B2087787
  · exact B2087791
  · exact B2087795
  · exact B2087799
  · exact B2087803
  · exact B2087807
  · exact B2087811
  · exact B2087815
  · exact B2087819
  · exact B2087823
  · exact B2087827
  · exact B2087831
  · exact B2087835
  · exact B2087839
  · exact B2087843
  · exact B2087847
  · exact B2087851
  · exact B2087855
  · exact B2087859
  · exact B2087863
  · exact B2087867
  · exact B2087871
  · exact B2087875
  · exact B2087879
  · exact B2087883
  · exact B2087887
  · exact B2087891
  · exact B2087895
  · exact B2087899
  · exact B2087903
  · exact B2087907
  · exact B2087911
  · exact B2087915
  · exact B2087919
  · exact B2087923
  · exact B2087927
  · exact B2087931
  · exact B2087935
  · exact B2087939
  · exact B2087943
  · exact B2087947
  · exact B2087951
  · exact B2087955
  · exact B2087959
  · exact B2087963
  · exact B2087967
  · exact B2087971
  · exact B2087975
  · exact B2087979
  · exact B2087983
  · exact B2087987
  · exact B2087991
  · exact B2087995
  · exact B2087999
  · exact B2088003
  · exact B2088007
  · exact B2088011
  · exact B2088015
  · exact B2088019
  · exact B2088023
  · exact B2088027
  · exact B2088031
  · exact B2088035
  · exact B2088039
  · exact B2088043
  · exact B2088047
  · exact B2088051
  · exact B2088055
  · exact B2088059
  · exact B2088063
  · exact B2088067
  · exact B2088071
  · exact B2088075
  · exact B2088079
  · exact B2088083
  · exact B2088087
  · exact B2088091
  · exact B2088095
  · exact B2088099
  · exact B2088103
  · exact B2088107
  · exact B2088111
  · exact B2088115
  · exact B2088119
  · exact B2088123
  · exact B2088127
  · exact B2088131
  · exact B2088135
  · exact B2088139
  · exact B2088143
  · exact B2088147
  · exact B2088151
  · exact B2088155
  · exact B2088159
  · exact B2088163
  · exact B2088167
  · exact B2088171
  · exact B2088175
  · exact B2088179
  · exact B2088183
  · exact B2088187
  · exact B2088191
  · exact B2088195
  · exact B2088199
  · exact B2088203
  · exact B2088207
  · exact B2088211
  · exact B2088215
  · exact B2088219
  · exact B2088223
  · exact B2088227
  · exact B2088231
  · exact B2088235
  · exact B2088239
  · exact B2088243
  · exact B2088247
  · exact B2088251
  · exact B2088255
  · exact B2088259
  · exact B2088263
  · exact B2088267
  · exact B2088271
  · exact B2088275
  · exact B2088279
  · exact B2088283
  · exact B2088287
  · exact B2088291
  · exact B2088295
  · exact B2088299
  · exact B2088303
  · exact B2088307
  · exact B2088311
  · exact B2088315
  · exact B2088319
  · exact B2088323
  · exact B2088327
  · exact B2088331
  · exact B2088335
  · exact B2088339
  · exact B2088343
  · exact B2088347
  · exact B2088351
  · exact B2088355
  · exact B2088359
  · exact B2088363
  · exact B2088367
  · exact B2088371
  · exact B2088375
  · exact B2088379
  · exact B2088383
  · exact B2088387
  · exact B2088391
  · exact B2088395
  · exact B2088399
  · exact B2088403
  · exact B2088407
  · exact B2088411
  · exact B2088415
  · exact B2088419
  · exact B2088423
  · exact B2088427
  · exact B2088431
  · exact B2088435
  · exact B2088439
  · exact B2088443
  · exact B2088447
  · exact B2088451
  · exact B2088455
  · exact B2088459
  · exact B2088463
  · exact B2088467
  · exact B2088471
  · exact B2088475
  · exact B2088479
  · exact B2088483
  · exact B2088487
  · exact B2088491
  · exact B2088495
  · exact B2088499
  · exact B2088503
  · exact B2088507
  · exact B2088511
  · exact B2088515
  · exact B2088519
  · exact B2088523
  · exact B2088527
  · exact B2088531
  · exact B2088535
  · exact B2088539
  · exact B2088543
  · exact B2088547
  · exact B2088551
  · exact B2088555
  · exact B2088559
  · exact B2088563
  · exact B2088567
  · exact B2088571
  · exact B2088575
  · exact B2088579
  · exact B2088583
  · exact B2088587
  · exact B2088591
  · exact B2088595
  · exact B2088599
  · exact B2088603
  · exact B2088607
  · exact B2088611
  · exact B2088615
  · exact B2088619
  · exact B2088623
  · exact B2088627
  · exact B2088631
  · exact B2088635
  · exact B2088639
  · exact B2088643
  · exact B2088647
  · exact B2088651
  · exact B2088655
  · exact B2088659
  · exact B2088663
  · exact B2088667
  · exact B2088671
  · exact B2088675
  · exact B2088679
  · exact B2088683
  · exact B2088687
  · exact B2088691
  · exact B2088695
  · exact B2088699
  · exact B2088703
  · exact B2088707
  · exact B2088711
  · exact B2088715
  · exact B2088719
  · exact B2088723
  · exact B2088727
  · exact B2088731
  · exact B2088735
  · exact B2088739
  · exact B2088743
  · exact B2088747
  · exact B2088751
  · exact B2088755
  · exact B2088759
  · exact B2088763
  · exact B2088767
  · exact B2088771
  · exact B2088775
  · exact B2088779
  · exact B2088783
  · exact B2088787
  · exact B2088791
  · exact B2088795
  · exact B2088799
  · exact B2088803
  · exact B2088807
  · exact B2088811
  · exact B2088815
  · exact B2088819
  · exact B2088823
  · exact B2088827
  · exact B2088831
  · exact B2088835
  · exact B2088839
  · exact B2088843
  · exact B2088847
  · exact B2088851
  · exact B2088855
  · exact B2088859
  · exact B2088863
  · exact B2088867
  · exact B2088871
  · exact B2088875
  · exact B2088879
  · exact B2088883
  · exact B2088887
  · exact B2088891
  · exact B2088895
  · exact B2088899
  · exact B2088903
  · exact B2088907
  · exact B2088911
  · exact B2088915
  · exact B2088919
  · exact B2088923
  · exact B2088927
  · exact B2088931
  · exact B2088935
  · exact B2088939
  · exact B2088943
  · exact B2088947
  · exact B2088951
  · exact B2088955
  · exact B2088959
  · exact B2088963
  · exact B2088967
  · exact B2088971
  · exact B2088975
  · exact B2088979
  · exact B2088983
  · exact B2088987
  · exact B2088991
  · exact B2088995
  · exact B2088999
  · exact B2089003
  · exact B2089007
  · exact B2089011
  · exact B2089015
  · exact B2089019
  · exact B2089023
  · exact B2089027
  · exact B2089031
  · exact B2089035
  · exact B2089039
  · exact B2089043
  · exact B2089047
  · exact B2089051
  · exact B2089055
  · exact B2089059
  · exact B2089063
  · exact B2089067
  · exact B2089071
  · exact B2089075
  · exact B2089079
  · exact B2089083
  · exact B2089087
  · exact B2089091
  · exact B2089095
  · exact B2089099
  · exact B2089103
  · exact B2089107
  · exact B2089111
  · exact B2089115
  · exact B2089119
  · exact B2089123
  · exact B2089127
  · exact B2089131
  · exact B2089135
  · exact B2089139
  · exact B2089143
  · exact B2089147
  · exact B2089151
  · exact B2089155
  · exact B2089159
  · exact B2089163
  · exact B2089167
  · exact B2089171
  · exact B2089175
  · exact B2089179
  · exact B2089183
  · exact B2089187
  · exact B2089191
  · exact B2089195
  · exact B2089199
  · exact B2089203
  · exact B2089207
  · exact B2089211
  · exact B2089215
  · exact B2089219
  · exact B2089223
  · exact B2089227
  · exact B2089231
  · exact B2089235
  · exact B2089239
  · exact B2089243
  · exact B2089247
  · exact B2089251
  · exact B2089255
  · exact B2089259
  · exact B2089263
  · exact B2089267
  · exact B2089271
  · exact B2089275
  · exact B2089279
  · exact B2089283
  · exact B2089287
  · exact B2089291
  · exact B2089295
  · exact B2089299
  · exact B2089303
  · exact B2089307
  · exact B2089311
  · exact B2089315
  · exact B2089319
  · exact B2089323
  · exact B2089327
  · exact B2089331
  · exact B2089335
  · exact B2089339
  · exact B2089343
  · exact B2089347
  · exact B2089351
  · exact B2089355
  · exact B2089359
  · exact B2089363
  · exact B2089367
  · exact B2089371
  · exact B2089375
  · exact B2089379
  · exact B2089383
  · exact B2089387
  · exact B2089391
  · exact B2089395
  · exact B2089399
  · exact B2089403
  · exact B2089407
  · exact B2089411
  · exact B2089415
  · exact B2089419
  · exact B2089423
  · exact B2089427
  · exact B2089431
  · exact B2089435
theorem solution (m : ℕ) (hlo : 2087435 ≤ m) (hhi : m ≤ 2089435) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 521858 ≤ j := by omega
    have hj2 : j ≤ 522358 := by omega
    have hb : Blo 2087435 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
