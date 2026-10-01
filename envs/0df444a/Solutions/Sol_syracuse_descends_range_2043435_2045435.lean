-- Prove2me | solution 1 for syracuse_descends_range_2043435_2045435
-- status  : ACCEPTED   (prove)
-- author  : @chstdu
-- created : 2026-09-23T16:49:18.317239+00:00
-- url     : https://prove2.me/submissions/bb897130-63ec-45e2-8143-1c604924d200

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

theorem B2298865 : Blo 2043435 2298865 := bbase (se 2 (by rfl) ⟨862074, by rfl⟩ : syracuseStep 2298865 = 1724149) (by norm_num)
theorem B3065153 : Blo 2043435 3065153 := bstep (se 2 (by rfl) ⟨1149432, by rfl⟩ : syracuseStep 3065153 = 2298865) B2298865
theorem B2043435 : Blo 2043435 2043435 := bstep (se 1 (by rfl) ⟨1532576, by rfl⟩ : syracuseStep 2043435 = 3065153) B3065153
theorem B9819589 : Blo 2043435 9819589 := bbase (se 4 (by rfl) ⟨920586, by rfl⟩ : syracuseStep 9819589 = 1841173) (by norm_num)
theorem B13092785 : Blo 2043435 13092785 := bstep (se 2 (by rfl) ⟨4909794, by rfl⟩ : syracuseStep 13092785 = 9819589) B9819589
theorem B8728523 : Blo 2043435 8728523 := bstep (se 1 (by rfl) ⟨6546392, by rfl⟩ : syracuseStep 8728523 = 13092785) B13092785
theorem B5819015 : Blo 2043435 5819015 := bstep (se 1 (by rfl) ⟨4364261, by rfl⟩ : syracuseStep 5819015 = 8728523) B8728523
theorem B3879343 : Blo 2043435 3879343 := bstep (se 1 (by rfl) ⟨2909507, by rfl⟩ : syracuseStep 3879343 = 5819015) B5819015
theorem B5172457 : Blo 2043435 5172457 := bstep (se 2 (by rfl) ⟨1939671, by rfl⟩ : syracuseStep 5172457 = 3879343) B3879343
theorem B6896609 : Blo 2043435 6896609 := bstep (se 2 (by rfl) ⟨2586228, by rfl⟩ : syracuseStep 6896609 = 5172457) B5172457
theorem B4597739 : Blo 2043435 4597739 := bstep (se 1 (by rfl) ⟨3448304, by rfl⟩ : syracuseStep 4597739 = 6896609) B6896609
theorem B3065159 : Blo 2043435 3065159 := bstep (se 1 (by rfl) ⟨2298869, by rfl⟩ : syracuseStep 3065159 = 4597739) B4597739
theorem B2043439 : Blo 2043435 2043439 := bstep (se 1 (by rfl) ⟨1532579, by rfl⟩ : syracuseStep 2043439 = 3065159) B3065159
theorem B3065165 : Blo 2043435 3065165 := bbase (se 3 (by rfl) ⟨574718, by rfl⟩ : syracuseStep 3065165 = 1149437) (by norm_num)
theorem B2043443 : Blo 2043435 2043443 := bstep (se 1 (by rfl) ⟨1532582, by rfl⟩ : syracuseStep 2043443 = 3065165) B3065165
theorem B4597757 : Blo 2043435 4597757 := bbase (se 3 (by rfl) ⟨862079, by rfl⟩ : syracuseStep 4597757 = 1724159) (by norm_num)
theorem B3065171 : Blo 2043435 3065171 := bstep (se 1 (by rfl) ⟨2298878, by rfl⟩ : syracuseStep 3065171 = 4597757) B4597757
theorem B2043447 : Blo 2043435 2043447 := bstep (se 1 (by rfl) ⟨1532585, by rfl⟩ : syracuseStep 2043447 = 3065171) B3065171
theorem B3448325 : Blo 2043435 3448325 := bbase (se 4 (by rfl) ⟨323280, by rfl⟩ : syracuseStep 3448325 = 646561) (by norm_num)
theorem B2298883 : Blo 2043435 2298883 := bstep (se 1 (by rfl) ⟨1724162, by rfl⟩ : syracuseStep 2298883 = 3448325) B3448325
theorem B3065177 : Blo 2043435 3065177 := bstep (se 2 (by rfl) ⟨1149441, by rfl⟩ : syracuseStep 3065177 = 2298883) B2298883
theorem B2043451 : Blo 2043435 2043451 := bstep (se 1 (by rfl) ⟨1532588, by rfl⟩ : syracuseStep 2043451 = 3065177) B3065177
theorem B15517493 : Blo 2043435 15517493 := bbase (se 5 (by rfl) ⟨727382, by rfl⟩ : syracuseStep 15517493 = 1454765) (by norm_num)
theorem B10344995 : Blo 2043435 10344995 := bstep (se 1 (by rfl) ⟨7758746, by rfl⟩ : syracuseStep 10344995 = 15517493) B15517493
theorem B6896663 : Blo 2043435 6896663 := bstep (se 1 (by rfl) ⟨5172497, by rfl⟩ : syracuseStep 6896663 = 10344995) B10344995
theorem B4597775 : Blo 2043435 4597775 := bstep (se 1 (by rfl) ⟨3448331, by rfl⟩ : syracuseStep 4597775 = 6896663) B6896663
theorem B3065183 : Blo 2043435 3065183 := bstep (se 1 (by rfl) ⟨2298887, by rfl⟩ : syracuseStep 3065183 = 4597775) B4597775
theorem B2043455 : Blo 2043435 2043455 := bstep (se 1 (by rfl) ⟨1532591, by rfl⟩ : syracuseStep 2043455 = 3065183) B3065183
theorem B3065189 : Blo 2043435 3065189 := bbase (se 4 (by rfl) ⟨287361, by rfl⟩ : syracuseStep 3065189 = 574723) (by norm_num)
theorem B2043459 : Blo 2043435 2043459 := bstep (se 1 (by rfl) ⟨1532594, by rfl⟩ : syracuseStep 2043459 = 3065189) B3065189
theorem B3879389 : Blo 2043435 3879389 := bbase (se 3 (by rfl) ⟨727385, by rfl⟩ : syracuseStep 3879389 = 1454771) (by norm_num)
theorem B2586259 : Blo 2043435 2586259 := bstep (se 1 (by rfl) ⟨1939694, by rfl⟩ : syracuseStep 2586259 = 3879389) B3879389
theorem B3448345 : Blo 2043435 3448345 := bstep (se 2 (by rfl) ⟨1293129, by rfl⟩ : syracuseStep 3448345 = 2586259) B2586259
theorem B4597793 : Blo 2043435 4597793 := bstep (se 2 (by rfl) ⟨1724172, by rfl⟩ : syracuseStep 4597793 = 3448345) B3448345
theorem B3065195 : Blo 2043435 3065195 := bstep (se 1 (by rfl) ⟨2298896, by rfl⟩ : syracuseStep 3065195 = 4597793) B4597793
theorem B2043463 : Blo 2043435 2043463 := bstep (se 1 (by rfl) ⟨1532597, by rfl⟩ : syracuseStep 2043463 = 3065195) B3065195
theorem B2298901 : Blo 2043435 2298901 := bbase (se 6 (by rfl) ⟨53880, by rfl⟩ : syracuseStep 2298901 = 107761) (by norm_num)
theorem B3065201 : Blo 2043435 3065201 := bstep (se 2 (by rfl) ⟨1149450, by rfl⟩ : syracuseStep 3065201 = 2298901) B2298901
theorem B2043467 : Blo 2043435 2043467 := bstep (se 1 (by rfl) ⟨1532600, by rfl⟩ : syracuseStep 2043467 = 3065201) B3065201
theorem B2586269 : Blo 2043435 2586269 := bbase (se 3 (by rfl) ⟨484925, by rfl⟩ : syracuseStep 2586269 = 969851) (by norm_num)
theorem B6896717 : Blo 2043435 6896717 := bstep (se 3 (by rfl) ⟨1293134, by rfl⟩ : syracuseStep 6896717 = 2586269) B2586269
theorem B4597811 : Blo 2043435 4597811 := bstep (se 1 (by rfl) ⟨3448358, by rfl⟩ : syracuseStep 4597811 = 6896717) B6896717
theorem B3065207 : Blo 2043435 3065207 := bstep (se 1 (by rfl) ⟨2298905, by rfl⟩ : syracuseStep 3065207 = 4597811) B4597811
theorem B2043471 : Blo 2043435 2043471 := bstep (se 1 (by rfl) ⟨1532603, by rfl⟩ : syracuseStep 2043471 = 3065207) B3065207
theorem B3065213 : Blo 2043435 3065213 := bbase (se 3 (by rfl) ⟨574727, by rfl⟩ : syracuseStep 3065213 = 1149455) (by norm_num)
theorem B2043475 : Blo 2043435 2043475 := bstep (se 1 (by rfl) ⟨1532606, by rfl⟩ : syracuseStep 2043475 = 3065213) B3065213
theorem B4597829 : Blo 2043435 4597829 := bbase (se 4 (by rfl) ⟨431046, by rfl⟩ : syracuseStep 4597829 = 862093) (by norm_num)
theorem B3065219 : Blo 2043435 3065219 := bstep (se 1 (by rfl) ⟨2298914, by rfl⟩ : syracuseStep 3065219 = 4597829) B4597829
theorem B2043479 : Blo 2043435 2043479 := bstep (se 1 (by rfl) ⟨1532609, by rfl⟩ : syracuseStep 2043479 = 3065219) B3065219
theorem B5819141 : Blo 2043435 5819141 := bbase (se 4 (by rfl) ⟨545544, by rfl⟩ : syracuseStep 5819141 = 1091089) (by norm_num)
theorem B3879427 : Blo 2043435 3879427 := bstep (se 1 (by rfl) ⟨2909570, by rfl⟩ : syracuseStep 3879427 = 5819141) B5819141
theorem B5172569 : Blo 2043435 5172569 := bstep (se 2 (by rfl) ⟨1939713, by rfl⟩ : syracuseStep 5172569 = 3879427) B3879427
theorem B3448379 : Blo 2043435 3448379 := bstep (se 1 (by rfl) ⟨2586284, by rfl⟩ : syracuseStep 3448379 = 5172569) B5172569
theorem B2298919 : Blo 2043435 2298919 := bstep (se 1 (by rfl) ⟨1724189, by rfl⟩ : syracuseStep 2298919 = 3448379) B3448379
theorem B3065225 : Blo 2043435 3065225 := bstep (se 2 (by rfl) ⟨1149459, by rfl⟩ : syracuseStep 3065225 = 2298919) B2298919
theorem B2043483 : Blo 2043435 2043483 := bstep (se 1 (by rfl) ⟨1532612, by rfl⟩ : syracuseStep 2043483 = 3065225) B3065225
theorem B10345157 : Blo 2043435 10345157 := bbase (se 4 (by rfl) ⟨969858, by rfl⟩ : syracuseStep 10345157 = 1939717) (by norm_num)
theorem B6896771 : Blo 2043435 6896771 := bstep (se 1 (by rfl) ⟨5172578, by rfl⟩ : syracuseStep 6896771 = 10345157) B10345157
theorem B4597847 : Blo 2043435 4597847 := bstep (se 1 (by rfl) ⟨3448385, by rfl⟩ : syracuseStep 4597847 = 6896771) B6896771
theorem B3065231 : Blo 2043435 3065231 := bstep (se 1 (by rfl) ⟨2298923, by rfl⟩ : syracuseStep 3065231 = 4597847) B4597847
theorem B2043487 : Blo 2043435 2043487 := bstep (se 1 (by rfl) ⟨1532615, by rfl⟩ : syracuseStep 2043487 = 3065231) B3065231
theorem B3065237 : Blo 2043435 3065237 := bbase (se 6 (by rfl) ⟨71841, by rfl⟩ : syracuseStep 3065237 = 143683) (by norm_num)
theorem B2043491 : Blo 2043435 2043491 := bstep (se 1 (by rfl) ⟨1532618, by rfl⟩ : syracuseStep 2043491 = 3065237) B3065237
theorem B4364381 : Blo 2043435 4364381 := bbase (se 3 (by rfl) ⟨818321, by rfl⟩ : syracuseStep 4364381 = 1636643) (by norm_num)
theorem B11638349 : Blo 2043435 11638349 := bstep (se 3 (by rfl) ⟨2182190, by rfl⟩ : syracuseStep 11638349 = 4364381) B4364381
theorem B7758899 : Blo 2043435 7758899 := bstep (se 1 (by rfl) ⟨5819174, by rfl⟩ : syracuseStep 7758899 = 11638349) B11638349
theorem B5172599 : Blo 2043435 5172599 := bstep (se 1 (by rfl) ⟨3879449, by rfl⟩ : syracuseStep 5172599 = 7758899) B7758899
theorem B3448399 : Blo 2043435 3448399 := bstep (se 1 (by rfl) ⟨2586299, by rfl⟩ : syracuseStep 3448399 = 5172599) B5172599
theorem B4597865 : Blo 2043435 4597865 := bstep (se 2 (by rfl) ⟨1724199, by rfl⟩ : syracuseStep 4597865 = 3448399) B3448399
theorem B3065243 : Blo 2043435 3065243 := bstep (se 1 (by rfl) ⟨2298932, by rfl⟩ : syracuseStep 3065243 = 4597865) B4597865
theorem B2043495 : Blo 2043435 2043495 := bstep (se 1 (by rfl) ⟨1532621, by rfl⟩ : syracuseStep 2043495 = 3065243) B3065243
theorem B2298937 : Blo 2043435 2298937 := bbase (se 2 (by rfl) ⟨862101, by rfl⟩ : syracuseStep 2298937 = 1724203) (by norm_num)
theorem B3065249 : Blo 2043435 3065249 := bstep (se 2 (by rfl) ⟨1149468, by rfl⟩ : syracuseStep 3065249 = 2298937) B2298937
theorem B2043499 : Blo 2043435 2043499 := bstep (se 1 (by rfl) ⟨1532624, by rfl⟩ : syracuseStep 2043499 = 3065249) B3065249
theorem B4909949 : Blo 2043435 4909949 := bbase (se 3 (by rfl) ⟨920615, by rfl⟩ : syracuseStep 4909949 = 1841231) (by norm_num)
theorem B3273299 : Blo 2043435 3273299 := bstep (se 1 (by rfl) ⟨2454974, by rfl⟩ : syracuseStep 3273299 = 4909949) B4909949
theorem B2182199 : Blo 2043435 2182199 := bstep (se 1 (by rfl) ⟨1636649, by rfl⟩ : syracuseStep 2182199 = 3273299) B3273299
theorem B5819197 : Blo 2043435 5819197 := bstep (se 3 (by rfl) ⟨1091099, by rfl⟩ : syracuseStep 5819197 = 2182199) B2182199
theorem B7758929 : Blo 2043435 7758929 := bstep (se 2 (by rfl) ⟨2909598, by rfl⟩ : syracuseStep 7758929 = 5819197) B5819197
theorem B5172619 : Blo 2043435 5172619 := bstep (se 1 (by rfl) ⟨3879464, by rfl⟩ : syracuseStep 5172619 = 7758929) B7758929
theorem B6896825 : Blo 2043435 6896825 := bstep (se 2 (by rfl) ⟨2586309, by rfl⟩ : syracuseStep 6896825 = 5172619) B5172619
theorem B4597883 : Blo 2043435 4597883 := bstep (se 1 (by rfl) ⟨3448412, by rfl⟩ : syracuseStep 4597883 = 6896825) B6896825
theorem B3065255 : Blo 2043435 3065255 := bstep (se 1 (by rfl) ⟨2298941, by rfl⟩ : syracuseStep 3065255 = 4597883) B4597883
theorem B2043503 : Blo 2043435 2043503 := bstep (se 1 (by rfl) ⟨1532627, by rfl⟩ : syracuseStep 2043503 = 3065255) B3065255
theorem B3065261 : Blo 2043435 3065261 := bbase (se 3 (by rfl) ⟨574736, by rfl⟩ : syracuseStep 3065261 = 1149473) (by norm_num)
theorem B2043507 : Blo 2043435 2043507 := bstep (se 1 (by rfl) ⟨1532630, by rfl⟩ : syracuseStep 2043507 = 3065261) B3065261
theorem B4597901 : Blo 2043435 4597901 := bbase (se 3 (by rfl) ⟨862106, by rfl⟩ : syracuseStep 4597901 = 1724213) (by norm_num)
theorem B3065267 : Blo 2043435 3065267 := bstep (se 1 (by rfl) ⟨2298950, by rfl⟩ : syracuseStep 3065267 = 4597901) B4597901
theorem B2043511 : Blo 2043435 2043511 := bstep (se 1 (by rfl) ⟨1532633, by rfl⟩ : syracuseStep 2043511 = 3065267) B3065267
theorem B2586325 : Blo 2043435 2586325 := bbase (se 7 (by rfl) ⟨30308, by rfl⟩ : syracuseStep 2586325 = 60617) (by norm_num)
theorem B3448433 : Blo 2043435 3448433 := bstep (se 2 (by rfl) ⟨1293162, by rfl⟩ : syracuseStep 3448433 = 2586325) B2586325
theorem B2298955 : Blo 2043435 2298955 := bstep (se 1 (by rfl) ⟨1724216, by rfl⟩ : syracuseStep 2298955 = 3448433) B3448433
theorem B3065273 : Blo 2043435 3065273 := bstep (se 2 (by rfl) ⟨1149477, by rfl⟩ : syracuseStep 3065273 = 2298955) B2298955
theorem B2043515 : Blo 2043435 2043515 := bstep (se 1 (by rfl) ⟨1532636, by rfl⟩ : syracuseStep 2043515 = 3065273) B3065273
theorem B3732733 : Blo 2043435 3732733 := bbase (se 3 (by rfl) ⟨699887, by rfl⟩ : syracuseStep 3732733 = 1399775) (by norm_num)
theorem B4976977 : Blo 2043435 4976977 := bstep (se 2 (by rfl) ⟨1866366, by rfl⟩ : syracuseStep 4976977 = 3732733) B3732733
theorem B6635969 : Blo 2043435 6635969 := bstep (se 2 (by rfl) ⟨2488488, by rfl⟩ : syracuseStep 6635969 = 4976977) B4976977
theorem B4423979 : Blo 2043435 4423979 := bstep (se 1 (by rfl) ⟨3317984, by rfl⟩ : syracuseStep 4423979 = 6635969) B6635969
theorem B2949319 : Blo 2043435 2949319 := bstep (se 1 (by rfl) ⟨2211989, by rfl⟩ : syracuseStep 2949319 = 4423979) B4423979
theorem B3932425 : Blo 2043435 3932425 := bstep (se 2 (by rfl) ⟨1474659, by rfl⟩ : syracuseStep 3932425 = 2949319) B2949319
theorem B5243233 : Blo 2043435 5243233 := bstep (se 2 (by rfl) ⟨1966212, by rfl⟩ : syracuseStep 5243233 = 3932425) B3932425
theorem B6990977 : Blo 2043435 6990977 := bstep (se 2 (by rfl) ⟨2621616, by rfl⟩ : syracuseStep 6990977 = 5243233) B5243233
theorem B4660651 : Blo 2043435 4660651 := bstep (se 1 (by rfl) ⟨3495488, by rfl⟩ : syracuseStep 4660651 = 6990977) B6990977
theorem B6214201 : Blo 2043435 6214201 := bstep (se 2 (by rfl) ⟨2330325, by rfl⟩ : syracuseStep 6214201 = 4660651) B4660651
theorem B132569621 : Blo 2043435 132569621 := bstep (se 6 (by rfl) ⟨3107100, by rfl⟩ : syracuseStep 132569621 = 6214201) B6214201
theorem B88379747 : Blo 2043435 88379747 := bstep (se 1 (by rfl) ⟨66284810, by rfl⟩ : syracuseStep 88379747 = 132569621) B132569621
theorem B58919831 : Blo 2043435 58919831 := bstep (se 1 (by rfl) ⟨44189873, by rfl⟩ : syracuseStep 58919831 = 88379747) B88379747
theorem B39279887 : Blo 2043435 39279887 := bstep (se 1 (by rfl) ⟨29459915, by rfl⟩ : syracuseStep 39279887 = 58919831) B58919831
theorem B26186591 : Blo 2043435 26186591 := bstep (se 1 (by rfl) ⟨19639943, by rfl⟩ : syracuseStep 26186591 = 39279887) B39279887
theorem B17457727 : Blo 2043435 17457727 := bstep (se 1 (by rfl) ⟨13093295, by rfl⟩ : syracuseStep 17457727 = 26186591) B26186591
theorem B23276969 : Blo 2043435 23276969 := bstep (se 2 (by rfl) ⟨8728863, by rfl⟩ : syracuseStep 23276969 = 17457727) B17457727
theorem B15517979 : Blo 2043435 15517979 := bstep (se 1 (by rfl) ⟨11638484, by rfl⟩ : syracuseStep 15517979 = 23276969) B23276969
theorem B10345319 : Blo 2043435 10345319 := bstep (se 1 (by rfl) ⟨7758989, by rfl⟩ : syracuseStep 10345319 = 15517979) B15517979
theorem B6896879 : Blo 2043435 6896879 := bstep (se 1 (by rfl) ⟨5172659, by rfl⟩ : syracuseStep 6896879 = 10345319) B10345319
theorem B4597919 : Blo 2043435 4597919 := bstep (se 1 (by rfl) ⟨3448439, by rfl⟩ : syracuseStep 4597919 = 6896879) B6896879
theorem B3065279 : Blo 2043435 3065279 := bstep (se 1 (by rfl) ⟨2298959, by rfl⟩ : syracuseStep 3065279 = 4597919) B4597919
theorem B2043519 : Blo 2043435 2043519 := bstep (se 1 (by rfl) ⟨1532639, by rfl⟩ : syracuseStep 2043519 = 3065279) B3065279
theorem B3065285 : Blo 2043435 3065285 := bbase (se 4 (by rfl) ⟨287370, by rfl⟩ : syracuseStep 3065285 = 574741) (by norm_num)
theorem B2043523 : Blo 2043435 2043523 := bstep (se 1 (by rfl) ⟨1532642, by rfl⟩ : syracuseStep 2043523 = 3065285) B3065285
theorem B3448453 : Blo 2043435 3448453 := bbase (se 4 (by rfl) ⟨323292, by rfl⟩ : syracuseStep 3448453 = 646585) (by norm_num)
theorem B4597937 : Blo 2043435 4597937 := bstep (se 2 (by rfl) ⟨1724226, by rfl⟩ : syracuseStep 4597937 = 3448453) B3448453
theorem B3065291 : Blo 2043435 3065291 := bstep (se 1 (by rfl) ⟨2298968, by rfl⟩ : syracuseStep 3065291 = 4597937) B4597937
theorem B2043527 : Blo 2043435 2043527 := bstep (se 1 (by rfl) ⟨1532645, by rfl⟩ : syracuseStep 2043527 = 3065291) B3065291
theorem B2298973 : Blo 2043435 2298973 := bbase (se 3 (by rfl) ⟨431057, by rfl⟩ : syracuseStep 2298973 = 862115) (by norm_num)
theorem B3065297 : Blo 2043435 3065297 := bstep (se 2 (by rfl) ⟨1149486, by rfl⟩ : syracuseStep 3065297 = 2298973) B2298973
theorem B2043531 : Blo 2043435 2043531 := bstep (se 1 (by rfl) ⟨1532648, by rfl⟩ : syracuseStep 2043531 = 3065297) B3065297
theorem B6896933 : Blo 2043435 6896933 := bbase (se 4 (by rfl) ⟨646587, by rfl⟩ : syracuseStep 6896933 = 1293175) (by norm_num)
theorem B4597955 : Blo 2043435 4597955 := bstep (se 1 (by rfl) ⟨3448466, by rfl⟩ : syracuseStep 4597955 = 6896933) B6896933
theorem B3065303 : Blo 2043435 3065303 := bstep (se 1 (by rfl) ⟨2298977, by rfl⟩ : syracuseStep 3065303 = 4597955) B4597955
theorem B2043535 : Blo 2043435 2043535 := bstep (se 1 (by rfl) ⟨1532651, by rfl⟩ : syracuseStep 2043535 = 3065303) B3065303
theorem B3065309 : Blo 2043435 3065309 := bbase (se 3 (by rfl) ⟨574745, by rfl⟩ : syracuseStep 3065309 = 1149491) (by norm_num)
theorem B2043539 : Blo 2043435 2043539 := bstep (se 1 (by rfl) ⟨1532654, by rfl⟩ : syracuseStep 2043539 = 3065309) B3065309
theorem B4597973 : Blo 2043435 4597973 := bbase (se 7 (by rfl) ⟨53882, by rfl⟩ : syracuseStep 4597973 = 107765) (by norm_num)
theorem B3065315 : Blo 2043435 3065315 := bstep (se 1 (by rfl) ⟨2298986, by rfl⟩ : syracuseStep 3065315 = 4597973) B4597973
theorem B2043543 : Blo 2043435 2043543 := bstep (se 1 (by rfl) ⟨1532657, by rfl⟩ : syracuseStep 2043543 = 3065315) B3065315
theorem B3682541 : Blo 2043435 3682541 := bbase (se 3 (by rfl) ⟨690476, by rfl⟩ : syracuseStep 3682541 = 1380953) (by norm_num)
theorem B9820109 : Blo 2043435 9820109 := bstep (se 3 (by rfl) ⟨1841270, by rfl⟩ : syracuseStep 9820109 = 3682541) B3682541
theorem B6546739 : Blo 2043435 6546739 := bstep (se 1 (by rfl) ⟨4910054, by rfl⟩ : syracuseStep 6546739 = 9820109) B9820109
theorem B8728985 : Blo 2043435 8728985 := bstep (se 2 (by rfl) ⟨3273369, by rfl⟩ : syracuseStep 8728985 = 6546739) B6546739
theorem B5819323 : Blo 2043435 5819323 := bstep (se 1 (by rfl) ⟨4364492, by rfl⟩ : syracuseStep 5819323 = 8728985) B8728985
theorem B7759097 : Blo 2043435 7759097 := bstep (se 2 (by rfl) ⟨2909661, by rfl⟩ : syracuseStep 7759097 = 5819323) B5819323
theorem B5172731 : Blo 2043435 5172731 := bstep (se 1 (by rfl) ⟨3879548, by rfl⟩ : syracuseStep 5172731 = 7759097) B7759097
theorem B3448487 : Blo 2043435 3448487 := bstep (se 1 (by rfl) ⟨2586365, by rfl⟩ : syracuseStep 3448487 = 5172731) B5172731
theorem B2298991 : Blo 2043435 2298991 := bstep (se 1 (by rfl) ⟨1724243, by rfl⟩ : syracuseStep 2298991 = 3448487) B3448487
theorem B3065321 : Blo 2043435 3065321 := bstep (se 2 (by rfl) ⟨1149495, by rfl⟩ : syracuseStep 3065321 = 2298991) B2298991
theorem B2043547 : Blo 2043435 2043547 := bstep (se 1 (by rfl) ⟨1532660, by rfl⟩ : syracuseStep 2043547 = 3065321) B3065321
theorem B3236069 : Blo 2043435 3236069 := bbase (se 4 (by rfl) ⟨303381, by rfl⟩ : syracuseStep 3236069 = 606763) (by norm_num)
theorem B8629517 : Blo 2043435 8629517 := bstep (se 3 (by rfl) ⟨1618034, by rfl⟩ : syracuseStep 8629517 = 3236069) B3236069
theorem B23012045 : Blo 2043435 23012045 := bstep (se 3 (by rfl) ⟨4314758, by rfl⟩ : syracuseStep 23012045 = 8629517) B8629517
theorem B15341363 : Blo 2043435 15341363 := bstep (se 1 (by rfl) ⟨11506022, by rfl⟩ : syracuseStep 15341363 = 23012045) B23012045
theorem B10227575 : Blo 2043435 10227575 := bstep (se 1 (by rfl) ⟨7670681, by rfl⟩ : syracuseStep 10227575 = 15341363) B15341363
theorem B6818383 : Blo 2043435 6818383 := bstep (se 1 (by rfl) ⟨5113787, by rfl⟩ : syracuseStep 6818383 = 10227575) B10227575
theorem B9091177 : Blo 2043435 9091177 := bstep (se 2 (by rfl) ⟨3409191, by rfl⟩ : syracuseStep 9091177 = 6818383) B6818383
theorem B48486277 : Blo 2043435 48486277 := bstep (se 4 (by rfl) ⟨4545588, by rfl⟩ : syracuseStep 48486277 = 9091177) B9091177
theorem B258593477 : Blo 2043435 258593477 := bstep (se 4 (by rfl) ⟨24243138, by rfl⟩ : syracuseStep 258593477 = 48486277) B48486277
theorem B689582605 : Blo 2043435 689582605 := bstep (se 3 (by rfl) ⟨129296738, by rfl⟩ : syracuseStep 689582605 = 258593477) B258593477
theorem B919443473 : Blo 2043435 919443473 := bstep (se 2 (by rfl) ⟨344791302, by rfl⟩ : syracuseStep 919443473 = 689582605) B689582605
theorem B612962315 : Blo 2043435 612962315 := bstep (se 1 (by rfl) ⟨459721736, by rfl⟩ : syracuseStep 612962315 = 919443473) B919443473
theorem B408641543 : Blo 2043435 408641543 := bstep (se 1 (by rfl) ⟨306481157, by rfl⟩ : syracuseStep 408641543 = 612962315) B612962315
theorem B272427695 : Blo 2043435 272427695 := bstep (se 1 (by rfl) ⟨204320771, by rfl⟩ : syracuseStep 272427695 = 408641543) B408641543
theorem B181618463 : Blo 2043435 181618463 := bstep (se 1 (by rfl) ⟨136213847, by rfl⟩ : syracuseStep 181618463 = 272427695) B272427695
theorem B484315901 : Blo 2043435 484315901 := bstep (se 3 (by rfl) ⟨90809231, by rfl⟩ : syracuseStep 484315901 = 181618463) B181618463
theorem B322877267 : Blo 2043435 322877267 := bstep (se 1 (by rfl) ⟨242157950, by rfl⟩ : syracuseStep 322877267 = 484315901) B484315901
theorem B215251511 : Blo 2043435 215251511 := bstep (se 1 (by rfl) ⟨161438633, by rfl⟩ : syracuseStep 215251511 = 322877267) B322877267
theorem B574004029 : Blo 2043435 574004029 := bstep (se 3 (by rfl) ⟨107625755, by rfl⟩ : syracuseStep 574004029 = 215251511) B215251511
theorem B765338705 : Blo 2043435 765338705 := bstep (se 2 (by rfl) ⟨287002014, by rfl⟩ : syracuseStep 765338705 = 574004029) B574004029
theorem B510225803 : Blo 2043435 510225803 := bstep (se 1 (by rfl) ⟨382669352, by rfl⟩ : syracuseStep 510225803 = 765338705) B765338705
theorem B340150535 : Blo 2043435 340150535 := bstep (se 1 (by rfl) ⟨255112901, by rfl⟩ : syracuseStep 340150535 = 510225803) B510225803
theorem B226767023 : Blo 2043435 226767023 := bstep (se 1 (by rfl) ⟨170075267, by rfl⟩ : syracuseStep 226767023 = 340150535) B340150535
theorem B151178015 : Blo 2043435 151178015 := bstep (se 1 (by rfl) ⟨113383511, by rfl⟩ : syracuseStep 151178015 = 226767023) B226767023
theorem B100785343 : Blo 2043435 100785343 := bstep (se 1 (by rfl) ⟨75589007, by rfl⟩ : syracuseStep 100785343 = 151178015) B151178015
theorem B134380457 : Blo 2043435 134380457 := bstep (se 2 (by rfl) ⟨50392671, by rfl⟩ : syracuseStep 134380457 = 100785343) B100785343
theorem B89586971 : Blo 2043435 89586971 := bstep (se 1 (by rfl) ⟨67190228, by rfl⟩ : syracuseStep 89586971 = 134380457) B134380457
theorem B59724647 : Blo 2043435 59724647 := bstep (se 1 (by rfl) ⟨44793485, by rfl⟩ : syracuseStep 59724647 = 89586971) B89586971
theorem B39816431 : Blo 2043435 39816431 := bstep (se 1 (by rfl) ⟨29862323, by rfl⟩ : syracuseStep 39816431 = 59724647) B59724647
theorem B26544287 : Blo 2043435 26544287 := bstep (se 1 (by rfl) ⟨19908215, by rfl⟩ : syracuseStep 26544287 = 39816431) B39816431
theorem B17696191 : Blo 2043435 17696191 := bstep (se 1 (by rfl) ⟨13272143, by rfl⟩ : syracuseStep 17696191 = 26544287) B26544287
theorem B23594921 : Blo 2043435 23594921 := bstep (se 2 (by rfl) ⟨8848095, by rfl⟩ : syracuseStep 23594921 = 17696191) B17696191
theorem B15729947 : Blo 2043435 15729947 := bstep (se 1 (by rfl) ⟨11797460, by rfl⟩ : syracuseStep 15729947 = 23594921) B23594921
theorem B10486631 : Blo 2043435 10486631 := bstep (se 1 (by rfl) ⟨7864973, by rfl⟩ : syracuseStep 10486631 = 15729947) B15729947
theorem B27964349 : Blo 2043435 27964349 := bstep (se 3 (by rfl) ⟨5243315, by rfl⟩ : syracuseStep 27964349 = 10486631) B10486631
theorem B18642899 : Blo 2043435 18642899 := bstep (se 1 (by rfl) ⟨13982174, by rfl⟩ : syracuseStep 18642899 = 27964349) B27964349
theorem B12428599 : Blo 2043435 12428599 := bstep (se 1 (by rfl) ⟨9321449, by rfl⟩ : syracuseStep 12428599 = 18642899) B18642899
theorem B16571465 : Blo 2043435 16571465 := bstep (se 2 (by rfl) ⟨6214299, by rfl⟩ : syracuseStep 16571465 = 12428599) B12428599
theorem B11047643 : Blo 2043435 11047643 := bstep (se 1 (by rfl) ⟨8285732, by rfl⟩ : syracuseStep 11047643 = 16571465) B16571465
theorem B7365095 : Blo 2043435 7365095 := bstep (se 1 (by rfl) ⟨5523821, by rfl⟩ : syracuseStep 7365095 = 11047643) B11047643
theorem B4910063 : Blo 2043435 4910063 := bstep (se 1 (by rfl) ⟨3682547, by rfl⟩ : syracuseStep 4910063 = 7365095) B7365095
theorem B13093501 : Blo 2043435 13093501 := bstep (se 3 (by rfl) ⟨2455031, by rfl⟩ : syracuseStep 13093501 = 4910063) B4910063
theorem B17458001 : Blo 2043435 17458001 := bstep (se 2 (by rfl) ⟨6546750, by rfl⟩ : syracuseStep 17458001 = 13093501) B13093501
theorem B11638667 : Blo 2043435 11638667 := bstep (se 1 (by rfl) ⟨8729000, by rfl⟩ : syracuseStep 11638667 = 17458001) B17458001
theorem B7759111 : Blo 2043435 7759111 := bstep (se 1 (by rfl) ⟨5819333, by rfl⟩ : syracuseStep 7759111 = 11638667) B11638667
theorem B10345481 : Blo 2043435 10345481 := bstep (se 2 (by rfl) ⟨3879555, by rfl⟩ : syracuseStep 10345481 = 7759111) B7759111
theorem B6896987 : Blo 2043435 6896987 := bstep (se 1 (by rfl) ⟨5172740, by rfl⟩ : syracuseStep 6896987 = 10345481) B10345481
theorem B4597991 : Blo 2043435 4597991 := bstep (se 1 (by rfl) ⟨3448493, by rfl⟩ : syracuseStep 4597991 = 6896987) B6896987
theorem B3065327 : Blo 2043435 3065327 := bstep (se 1 (by rfl) ⟨2298995, by rfl⟩ : syracuseStep 3065327 = 4597991) B4597991
theorem B2043551 : Blo 2043435 2043551 := bstep (se 1 (by rfl) ⟨1532663, by rfl⟩ : syracuseStep 2043551 = 3065327) B3065327
theorem B3065333 : Blo 2043435 3065333 := bbase (se 5 (by rfl) ⟨143687, by rfl⟩ : syracuseStep 3065333 = 287375) (by norm_num)
theorem B2043555 : Blo 2043435 2043555 := bstep (se 1 (by rfl) ⟨1532666, by rfl⟩ : syracuseStep 2043555 = 3065333) B3065333
theorem B3273389 : Blo 2043435 3273389 := bbase (se 3 (by rfl) ⟨613760, by rfl⟩ : syracuseStep 3273389 = 1227521) (by norm_num)
theorem B2182259 : Blo 2043435 2182259 := bstep (se 1 (by rfl) ⟨1636694, by rfl⟩ : syracuseStep 2182259 = 3273389) B3273389
theorem B5819357 : Blo 2043435 5819357 := bstep (se 3 (by rfl) ⟨1091129, by rfl⟩ : syracuseStep 5819357 = 2182259) B2182259
theorem B3879571 : Blo 2043435 3879571 := bstep (se 1 (by rfl) ⟨2909678, by rfl⟩ : syracuseStep 3879571 = 5819357) B5819357
theorem B5172761 : Blo 2043435 5172761 := bstep (se 2 (by rfl) ⟨1939785, by rfl⟩ : syracuseStep 5172761 = 3879571) B3879571
theorem B3448507 : Blo 2043435 3448507 := bstep (se 1 (by rfl) ⟨2586380, by rfl⟩ : syracuseStep 3448507 = 5172761) B5172761
theorem B4598009 : Blo 2043435 4598009 := bstep (se 2 (by rfl) ⟨1724253, by rfl⟩ : syracuseStep 4598009 = 3448507) B3448507
theorem B3065339 : Blo 2043435 3065339 := bstep (se 1 (by rfl) ⟨2299004, by rfl⟩ : syracuseStep 3065339 = 4598009) B4598009
theorem B2043559 : Blo 2043435 2043559 := bstep (se 1 (by rfl) ⟨1532669, by rfl⟩ : syracuseStep 2043559 = 3065339) B3065339
theorem B2299009 : Blo 2043435 2299009 := bbase (se 2 (by rfl) ⟨862128, by rfl⟩ : syracuseStep 2299009 = 1724257) (by norm_num)
theorem B3065345 : Blo 2043435 3065345 := bstep (se 2 (by rfl) ⟨1149504, by rfl⟩ : syracuseStep 3065345 = 2299009) B2299009
theorem B2043563 : Blo 2043435 2043563 := bstep (se 1 (by rfl) ⟨1532672, by rfl⟩ : syracuseStep 2043563 = 3065345) B3065345
theorem B5172781 : Blo 2043435 5172781 := bbase (se 3 (by rfl) ⟨969896, by rfl⟩ : syracuseStep 5172781 = 1939793) (by norm_num)
theorem B6897041 : Blo 2043435 6897041 := bstep (se 2 (by rfl) ⟨2586390, by rfl⟩ : syracuseStep 6897041 = 5172781) B5172781
theorem B4598027 : Blo 2043435 4598027 := bstep (se 1 (by rfl) ⟨3448520, by rfl⟩ : syracuseStep 4598027 = 6897041) B6897041
theorem B3065351 : Blo 2043435 3065351 := bstep (se 1 (by rfl) ⟨2299013, by rfl⟩ : syracuseStep 3065351 = 4598027) B4598027
theorem B2043567 : Blo 2043435 2043567 := bstep (se 1 (by rfl) ⟨1532675, by rfl⟩ : syracuseStep 2043567 = 3065351) B3065351
theorem B3065357 : Blo 2043435 3065357 := bbase (se 3 (by rfl) ⟨574754, by rfl⟩ : syracuseStep 3065357 = 1149509) (by norm_num)
theorem B2043571 : Blo 2043435 2043571 := bstep (se 1 (by rfl) ⟨1532678, by rfl⟩ : syracuseStep 2043571 = 3065357) B3065357
theorem B4598045 : Blo 2043435 4598045 := bbase (se 3 (by rfl) ⟨862133, by rfl⟩ : syracuseStep 4598045 = 1724267) (by norm_num)
theorem B3065363 : Blo 2043435 3065363 := bstep (se 1 (by rfl) ⟨2299022, by rfl⟩ : syracuseStep 3065363 = 4598045) B4598045
theorem B2043575 : Blo 2043435 2043575 := bstep (se 1 (by rfl) ⟨1532681, by rfl⟩ : syracuseStep 2043575 = 3065363) B3065363
theorem B3448541 : Blo 2043435 3448541 := bbase (se 3 (by rfl) ⟨646601, by rfl⟩ : syracuseStep 3448541 = 1293203) (by norm_num)
theorem B2299027 : Blo 2043435 2299027 := bstep (se 1 (by rfl) ⟨1724270, by rfl⟩ : syracuseStep 2299027 = 3448541) B3448541
theorem B3065369 : Blo 2043435 3065369 := bstep (se 2 (by rfl) ⟨1149513, by rfl⟩ : syracuseStep 3065369 = 2299027) B2299027
theorem B2043579 : Blo 2043435 2043579 := bstep (se 1 (by rfl) ⟨1532684, by rfl⟩ : syracuseStep 2043579 = 3065369) B3065369
theorem B6546853 : Blo 2043435 6546853 := bbase (se 4 (by rfl) ⟨613767, by rfl⟩ : syracuseStep 6546853 = 1227535) (by norm_num)
theorem B8729137 : Blo 2043435 8729137 := bstep (se 2 (by rfl) ⟨3273426, by rfl⟩ : syracuseStep 8729137 = 6546853) B6546853
theorem B11638849 : Blo 2043435 11638849 := bstep (se 2 (by rfl) ⟨4364568, by rfl⟩ : syracuseStep 11638849 = 8729137) B8729137
theorem B15518465 : Blo 2043435 15518465 := bstep (se 2 (by rfl) ⟨5819424, by rfl⟩ : syracuseStep 15518465 = 11638849) B11638849
theorem B10345643 : Blo 2043435 10345643 := bstep (se 1 (by rfl) ⟨7759232, by rfl⟩ : syracuseStep 10345643 = 15518465) B15518465
theorem B6897095 : Blo 2043435 6897095 := bstep (se 1 (by rfl) ⟨5172821, by rfl⟩ : syracuseStep 6897095 = 10345643) B10345643
theorem B4598063 : Blo 2043435 4598063 := bstep (se 1 (by rfl) ⟨3448547, by rfl⟩ : syracuseStep 4598063 = 6897095) B6897095
theorem B3065375 : Blo 2043435 3065375 := bstep (se 1 (by rfl) ⟨2299031, by rfl⟩ : syracuseStep 3065375 = 4598063) B4598063
theorem B2043583 : Blo 2043435 2043583 := bstep (se 1 (by rfl) ⟨1532687, by rfl⟩ : syracuseStep 2043583 = 3065375) B3065375
theorem B3065381 : Blo 2043435 3065381 := bbase (se 4 (by rfl) ⟨287379, by rfl⟩ : syracuseStep 3065381 = 574759) (by norm_num)
theorem B2043587 : Blo 2043435 2043587 := bstep (se 1 (by rfl) ⟨1532690, by rfl⟩ : syracuseStep 2043587 = 3065381) B3065381
theorem B2586421 : Blo 2043435 2586421 := bbase (se 5 (by rfl) ⟨121238, by rfl⟩ : syracuseStep 2586421 = 242477) (by norm_num)
theorem B3448561 : Blo 2043435 3448561 := bstep (se 2 (by rfl) ⟨1293210, by rfl⟩ : syracuseStep 3448561 = 2586421) B2586421
theorem B4598081 : Blo 2043435 4598081 := bstep (se 2 (by rfl) ⟨1724280, by rfl⟩ : syracuseStep 4598081 = 3448561) B3448561
theorem B3065387 : Blo 2043435 3065387 := bstep (se 1 (by rfl) ⟨2299040, by rfl⟩ : syracuseStep 3065387 = 4598081) B4598081
theorem B2043591 : Blo 2043435 2043591 := bstep (se 1 (by rfl) ⟨1532693, by rfl⟩ : syracuseStep 2043591 = 3065387) B3065387
theorem B2299045 : Blo 2043435 2299045 := bbase (se 4 (by rfl) ⟨215535, by rfl⟩ : syracuseStep 2299045 = 431071) (by norm_num)
theorem B3065393 : Blo 2043435 3065393 := bstep (se 2 (by rfl) ⟨1149522, by rfl⟩ : syracuseStep 3065393 = 2299045) B2299045
theorem B2043595 : Blo 2043435 2043595 := bstep (se 1 (by rfl) ⟨1532696, by rfl⟩ : syracuseStep 2043595 = 3065393) B3065393
theorem B7365269 : Blo 2043435 7365269 := bbase (se 6 (by rfl) ⟨172623, by rfl⟩ : syracuseStep 7365269 = 345247) (by norm_num)
theorem B19640717 : Blo 2043435 19640717 := bstep (se 3 (by rfl) ⟨3682634, by rfl⟩ : syracuseStep 19640717 = 7365269) B7365269
theorem B13093811 : Blo 2043435 13093811 := bstep (se 1 (by rfl) ⟨9820358, by rfl⟩ : syracuseStep 13093811 = 19640717) B19640717
theorem B8729207 : Blo 2043435 8729207 := bstep (se 1 (by rfl) ⟨6546905, by rfl⟩ : syracuseStep 8729207 = 13093811) B13093811
theorem B5819471 : Blo 2043435 5819471 := bstep (se 1 (by rfl) ⟨4364603, by rfl⟩ : syracuseStep 5819471 = 8729207) B8729207
theorem B3879647 : Blo 2043435 3879647 := bstep (se 1 (by rfl) ⟨2909735, by rfl⟩ : syracuseStep 3879647 = 5819471) B5819471
theorem B2586431 : Blo 2043435 2586431 := bstep (se 1 (by rfl) ⟨1939823, by rfl⟩ : syracuseStep 2586431 = 3879647) B3879647
theorem B6897149 : Blo 2043435 6897149 := bstep (se 3 (by rfl) ⟨1293215, by rfl⟩ : syracuseStep 6897149 = 2586431) B2586431
theorem B4598099 : Blo 2043435 4598099 := bstep (se 1 (by rfl) ⟨3448574, by rfl⟩ : syracuseStep 4598099 = 6897149) B6897149
theorem B3065399 : Blo 2043435 3065399 := bstep (se 1 (by rfl) ⟨2299049, by rfl⟩ : syracuseStep 3065399 = 4598099) B4598099
theorem B2043599 : Blo 2043435 2043599 := bstep (se 1 (by rfl) ⟨1532699, by rfl⟩ : syracuseStep 2043599 = 3065399) B3065399
theorem B3065405 : Blo 2043435 3065405 := bbase (se 3 (by rfl) ⟨574763, by rfl⟩ : syracuseStep 3065405 = 1149527) (by norm_num)
theorem B2043603 : Blo 2043435 2043603 := bstep (se 1 (by rfl) ⟨1532702, by rfl⟩ : syracuseStep 2043603 = 3065405) B3065405
theorem B4598117 : Blo 2043435 4598117 := bbase (se 4 (by rfl) ⟨431073, by rfl⟩ : syracuseStep 4598117 = 862147) (by norm_num)
theorem B3065411 : Blo 2043435 3065411 := bstep (se 1 (by rfl) ⟨2299058, by rfl⟩ : syracuseStep 3065411 = 4598117) B4598117
theorem B2043607 : Blo 2043435 2043607 := bstep (se 1 (by rfl) ⟨1532705, by rfl⟩ : syracuseStep 2043607 = 3065411) B3065411
theorem B5172893 : Blo 2043435 5172893 := bbase (se 3 (by rfl) ⟨969917, by rfl⟩ : syracuseStep 5172893 = 1939835) (by norm_num)
theorem B3448595 : Blo 2043435 3448595 := bstep (se 1 (by rfl) ⟨2586446, by rfl⟩ : syracuseStep 3448595 = 5172893) B5172893
theorem B2299063 : Blo 2043435 2299063 := bstep (se 1 (by rfl) ⟨1724297, by rfl⟩ : syracuseStep 2299063 = 3448595) B3448595
theorem B3065417 : Blo 2043435 3065417 := bstep (se 2 (by rfl) ⟨1149531, by rfl⟩ : syracuseStep 3065417 = 2299063) B2299063
theorem B2043611 : Blo 2043435 2043611 := bstep (se 1 (by rfl) ⟨1532708, by rfl⟩ : syracuseStep 2043611 = 3065417) B3065417
theorem B3879677 : Blo 2043435 3879677 := bbase (se 3 (by rfl) ⟨727439, by rfl⟩ : syracuseStep 3879677 = 1454879) (by norm_num)
theorem B10345805 : Blo 2043435 10345805 := bstep (se 3 (by rfl) ⟨1939838, by rfl⟩ : syracuseStep 10345805 = 3879677) B3879677
theorem B6897203 : Blo 2043435 6897203 := bstep (se 1 (by rfl) ⟨5172902, by rfl⟩ : syracuseStep 6897203 = 10345805) B10345805
theorem B4598135 : Blo 2043435 4598135 := bstep (se 1 (by rfl) ⟨3448601, by rfl⟩ : syracuseStep 4598135 = 6897203) B6897203
theorem B3065423 : Blo 2043435 3065423 := bstep (se 1 (by rfl) ⟨2299067, by rfl⟩ : syracuseStep 3065423 = 4598135) B4598135
theorem B2043615 : Blo 2043435 2043615 := bstep (se 1 (by rfl) ⟨1532711, by rfl⟩ : syracuseStep 2043615 = 3065423) B3065423
theorem B3065429 : Blo 2043435 3065429 := bbase (se 8 (by rfl) ⟨17961, by rfl⟩ : syracuseStep 3065429 = 35923) (by norm_num)
theorem B2043619 : Blo 2043435 2043619 := bstep (se 1 (by rfl) ⟨1532714, by rfl⟩ : syracuseStep 2043619 = 3065429) B3065429
theorem B4910237 : Blo 2043435 4910237 := bbase (se 3 (by rfl) ⟨920669, by rfl⟩ : syracuseStep 4910237 = 1841339) (by norm_num)
theorem B3273491 : Blo 2043435 3273491 := bstep (se 1 (by rfl) ⟨2455118, by rfl⟩ : syracuseStep 3273491 = 4910237) B4910237
theorem B8729309 : Blo 2043435 8729309 := bstep (se 3 (by rfl) ⟨1636745, by rfl⟩ : syracuseStep 8729309 = 3273491) B3273491
theorem B5819539 : Blo 2043435 5819539 := bstep (se 1 (by rfl) ⟨4364654, by rfl⟩ : syracuseStep 5819539 = 8729309) B8729309
theorem B7759385 : Blo 2043435 7759385 := bstep (se 2 (by rfl) ⟨2909769, by rfl⟩ : syracuseStep 7759385 = 5819539) B5819539
theorem B5172923 : Blo 2043435 5172923 := bstep (se 1 (by rfl) ⟨3879692, by rfl⟩ : syracuseStep 5172923 = 7759385) B7759385
theorem B3448615 : Blo 2043435 3448615 := bstep (se 1 (by rfl) ⟨2586461, by rfl⟩ : syracuseStep 3448615 = 5172923) B5172923
theorem B4598153 : Blo 2043435 4598153 := bstep (se 2 (by rfl) ⟨1724307, by rfl⟩ : syracuseStep 4598153 = 3448615) B3448615
theorem B3065435 : Blo 2043435 3065435 := bstep (se 1 (by rfl) ⟨2299076, by rfl⟩ : syracuseStep 3065435 = 4598153) B4598153
theorem B2043623 : Blo 2043435 2043623 := bstep (se 1 (by rfl) ⟨1532717, by rfl⟩ : syracuseStep 2043623 = 3065435) B3065435
theorem B2299081 : Blo 2043435 2299081 := bbase (se 2 (by rfl) ⟨862155, by rfl⟩ : syracuseStep 2299081 = 1724311) (by norm_num)
theorem B3065441 : Blo 2043435 3065441 := bstep (se 2 (by rfl) ⟨1149540, by rfl⟩ : syracuseStep 3065441 = 2299081) B2299081
theorem B2043627 : Blo 2043435 2043627 := bstep (se 1 (by rfl) ⟨1532720, by rfl⟩ : syracuseStep 2043627 = 3065441) B3065441
theorem B7465877 : Blo 2043435 7465877 := bbase (se 6 (by rfl) ⟨174981, by rfl⟩ : syracuseStep 7465877 = 349963) (by norm_num)
theorem B4977251 : Blo 2043435 4977251 := bstep (se 1 (by rfl) ⟨3732938, by rfl⟩ : syracuseStep 4977251 = 7465877) B7465877
theorem B3318167 : Blo 2043435 3318167 := bstep (se 1 (by rfl) ⟨2488625, by rfl⟩ : syracuseStep 3318167 = 4977251) B4977251
theorem B2212111 : Blo 2043435 2212111 := bstep (se 1 (by rfl) ⟨1659083, by rfl⟩ : syracuseStep 2212111 = 3318167) B3318167
theorem B2949481 : Blo 2043435 2949481 := bstep (se 2 (by rfl) ⟨1106055, by rfl⟩ : syracuseStep 2949481 = 2212111) B2212111
theorem B3932641 : Blo 2043435 3932641 := bstep (se 2 (by rfl) ⟨1474740, by rfl⟩ : syracuseStep 3932641 = 2949481) B2949481
theorem B5243521 : Blo 2043435 5243521 := bstep (se 2 (by rfl) ⟨1966320, by rfl⟩ : syracuseStep 5243521 = 3932641) B3932641
theorem B6991361 : Blo 2043435 6991361 := bstep (se 2 (by rfl) ⟨2621760, by rfl⟩ : syracuseStep 6991361 = 5243521) B5243521
theorem B4660907 : Blo 2043435 4660907 := bstep (se 1 (by rfl) ⟨3495680, by rfl⟩ : syracuseStep 4660907 = 6991361) B6991361
theorem B49716341 : Blo 2043435 49716341 := bstep (se 5 (by rfl) ⟨2330453, by rfl⟩ : syracuseStep 49716341 = 4660907) B4660907
theorem B33144227 : Blo 2043435 33144227 := bstep (se 1 (by rfl) ⟨24858170, by rfl⟩ : syracuseStep 33144227 = 49716341) B49716341
theorem B22096151 : Blo 2043435 22096151 := bstep (se 1 (by rfl) ⟨16572113, by rfl⟩ : syracuseStep 22096151 = 33144227) B33144227
theorem B14730767 : Blo 2043435 14730767 := bstep (se 1 (by rfl) ⟨11048075, by rfl⟩ : syracuseStep 14730767 = 22096151) B22096151
theorem B9820511 : Blo 2043435 9820511 := bstep (se 1 (by rfl) ⟨7365383, by rfl⟩ : syracuseStep 9820511 = 14730767) B14730767
theorem B6547007 : Blo 2043435 6547007 := bstep (se 1 (by rfl) ⟨4910255, by rfl⟩ : syracuseStep 6547007 = 9820511) B9820511
theorem B17458685 : Blo 2043435 17458685 := bstep (se 3 (by rfl) ⟨3273503, by rfl⟩ : syracuseStep 17458685 = 6547007) B6547007
theorem B11639123 : Blo 2043435 11639123 := bstep (se 1 (by rfl) ⟨8729342, by rfl⟩ : syracuseStep 11639123 = 17458685) B17458685
theorem B7759415 : Blo 2043435 7759415 := bstep (se 1 (by rfl) ⟨5819561, by rfl⟩ : syracuseStep 7759415 = 11639123) B11639123
theorem B5172943 : Blo 2043435 5172943 := bstep (se 1 (by rfl) ⟨3879707, by rfl⟩ : syracuseStep 5172943 = 7759415) B7759415
theorem B6897257 : Blo 2043435 6897257 := bstep (se 2 (by rfl) ⟨2586471, by rfl⟩ : syracuseStep 6897257 = 5172943) B5172943
theorem B4598171 : Blo 2043435 4598171 := bstep (se 1 (by rfl) ⟨3448628, by rfl⟩ : syracuseStep 4598171 = 6897257) B6897257
theorem B3065447 : Blo 2043435 3065447 := bstep (se 1 (by rfl) ⟨2299085, by rfl⟩ : syracuseStep 3065447 = 4598171) B4598171
theorem B2043631 : Blo 2043435 2043631 := bstep (se 1 (by rfl) ⟨1532723, by rfl⟩ : syracuseStep 2043631 = 3065447) B3065447
theorem B3065453 : Blo 2043435 3065453 := bbase (se 3 (by rfl) ⟨574772, by rfl⟩ : syracuseStep 3065453 = 1149545) (by norm_num)
theorem B2043635 : Blo 2043435 2043635 := bstep (se 1 (by rfl) ⟨1532726, by rfl⟩ : syracuseStep 2043635 = 3065453) B3065453
theorem B4598189 : Blo 2043435 4598189 := bbase (se 3 (by rfl) ⟨862160, by rfl⟩ : syracuseStep 4598189 = 1724321) (by norm_num)
theorem B3065459 : Blo 2043435 3065459 := bstep (se 1 (by rfl) ⟨2299094, by rfl⟩ : syracuseStep 3065459 = 4598189) B4598189
theorem B2043639 : Blo 2043435 2043639 := bstep (se 1 (by rfl) ⟨1532729, by rfl⟩ : syracuseStep 2043639 = 3065459) B3065459
theorem B2182349 : Blo 2043435 2182349 := bbase (se 3 (by rfl) ⟨409190, by rfl⟩ : syracuseStep 2182349 = 818381) (by norm_num)
theorem B5819597 : Blo 2043435 5819597 := bstep (se 3 (by rfl) ⟨1091174, by rfl⟩ : syracuseStep 5819597 = 2182349) B2182349
theorem B3879731 : Blo 2043435 3879731 := bstep (se 1 (by rfl) ⟨2909798, by rfl⟩ : syracuseStep 3879731 = 5819597) B5819597
theorem B2586487 : Blo 2043435 2586487 := bstep (se 1 (by rfl) ⟨1939865, by rfl⟩ : syracuseStep 2586487 = 3879731) B3879731
theorem B3448649 : Blo 2043435 3448649 := bstep (se 2 (by rfl) ⟨1293243, by rfl⟩ : syracuseStep 3448649 = 2586487) B2586487
theorem B2299099 : Blo 2043435 2299099 := bstep (se 1 (by rfl) ⟨1724324, by rfl⟩ : syracuseStep 2299099 = 3448649) B3448649
theorem B3065465 : Blo 2043435 3065465 := bstep (se 2 (by rfl) ⟨1149549, by rfl⟩ : syracuseStep 3065465 = 2299099) B2299099
theorem B2043643 : Blo 2043435 2043643 := bstep (se 1 (by rfl) ⟨1532732, by rfl⟩ : syracuseStep 2043643 = 3065465) B3065465
theorem B33596693 : Blo 2043435 33596693 := bbase (se 6 (by rfl) ⟨787422, by rfl⟩ : syracuseStep 33596693 = 1574845) (by norm_num)
theorem B22397795 : Blo 2043435 22397795 := bstep (se 1 (by rfl) ⟨16798346, by rfl⟩ : syracuseStep 22397795 = 33596693) B33596693
theorem B14931863 : Blo 2043435 14931863 := bstep (se 1 (by rfl) ⟨11198897, by rfl⟩ : syracuseStep 14931863 = 22397795) B22397795
theorem B9954575 : Blo 2043435 9954575 := bstep (se 1 (by rfl) ⟨7465931, by rfl⟩ : syracuseStep 9954575 = 14931863) B14931863
theorem B6636383 : Blo 2043435 6636383 := bstep (se 1 (by rfl) ⟨4977287, by rfl⟩ : syracuseStep 6636383 = 9954575) B9954575
theorem B4424255 : Blo 2043435 4424255 := bstep (se 1 (by rfl) ⟨3318191, by rfl⟩ : syracuseStep 4424255 = 6636383) B6636383
theorem B2949503 : Blo 2043435 2949503 := bstep (se 1 (by rfl) ⟨2212127, by rfl⟩ : syracuseStep 2949503 = 4424255) B4424255
theorem B31461365 : Blo 2043435 31461365 := bstep (se 5 (by rfl) ⟨1474751, by rfl⟩ : syracuseStep 31461365 = 2949503) B2949503
theorem B20974243 : Blo 2043435 20974243 := bstep (se 1 (by rfl) ⟨15730682, by rfl⟩ : syracuseStep 20974243 = 31461365) B31461365
theorem B27965657 : Blo 2043435 27965657 := bstep (se 2 (by rfl) ⟨10487121, by rfl⟩ : syracuseStep 27965657 = 20974243) B20974243
theorem B18643771 : Blo 2043435 18643771 := bstep (se 1 (by rfl) ⟨13982828, by rfl⟩ : syracuseStep 18643771 = 27965657) B27965657
theorem B24858361 : Blo 2043435 24858361 := bstep (se 2 (by rfl) ⟨9321885, by rfl⟩ : syracuseStep 24858361 = 18643771) B18643771
theorem B33144481 : Blo 2043435 33144481 := bstep (se 2 (by rfl) ⟨12429180, by rfl⟩ : syracuseStep 33144481 = 24858361) B24858361
theorem B44192641 : Blo 2043435 44192641 := bstep (se 2 (by rfl) ⟨16572240, by rfl⟩ : syracuseStep 44192641 = 33144481) B33144481
theorem B58923521 : Blo 2043435 58923521 := bstep (se 2 (by rfl) ⟨22096320, by rfl⟩ : syracuseStep 58923521 = 44192641) B44192641
theorem B39282347 : Blo 2043435 39282347 := bstep (se 1 (by rfl) ⟨29461760, by rfl⟩ : syracuseStep 39282347 = 58923521) B58923521
theorem B26188231 : Blo 2043435 26188231 := bstep (se 1 (by rfl) ⟨19641173, by rfl⟩ : syracuseStep 26188231 = 39282347) B39282347
theorem B34917641 : Blo 2043435 34917641 := bstep (se 2 (by rfl) ⟨13094115, by rfl⟩ : syracuseStep 34917641 = 26188231) B26188231
theorem B23278427 : Blo 2043435 23278427 := bstep (se 1 (by rfl) ⟨17458820, by rfl⟩ : syracuseStep 23278427 = 34917641) B34917641
theorem B15518951 : Blo 2043435 15518951 := bstep (se 1 (by rfl) ⟨11639213, by rfl⟩ : syracuseStep 15518951 = 23278427) B23278427
theorem B10345967 : Blo 2043435 10345967 := bstep (se 1 (by rfl) ⟨7759475, by rfl⟩ : syracuseStep 10345967 = 15518951) B15518951
theorem B6897311 : Blo 2043435 6897311 := bstep (se 1 (by rfl) ⟨5172983, by rfl⟩ : syracuseStep 6897311 = 10345967) B10345967
theorem B4598207 : Blo 2043435 4598207 := bstep (se 1 (by rfl) ⟨3448655, by rfl⟩ : syracuseStep 4598207 = 6897311) B6897311
theorem B3065471 : Blo 2043435 3065471 := bstep (se 1 (by rfl) ⟨2299103, by rfl⟩ : syracuseStep 3065471 = 4598207) B4598207
theorem B2043647 : Blo 2043435 2043647 := bstep (se 1 (by rfl) ⟨1532735, by rfl⟩ : syracuseStep 2043647 = 3065471) B3065471
theorem B3065477 : Blo 2043435 3065477 := bbase (se 4 (by rfl) ⟨287388, by rfl⟩ : syracuseStep 3065477 = 574777) (by norm_num)
theorem B2043651 : Blo 2043435 2043651 := bstep (se 1 (by rfl) ⟨1532738, by rfl⟩ : syracuseStep 2043651 = 3065477) B3065477
theorem B3448669 : Blo 2043435 3448669 := bbase (se 3 (by rfl) ⟨646625, by rfl⟩ : syracuseStep 3448669 = 1293251) (by norm_num)
theorem B4598225 : Blo 2043435 4598225 := bstep (se 2 (by rfl) ⟨1724334, by rfl⟩ : syracuseStep 4598225 = 3448669) B3448669
theorem B3065483 : Blo 2043435 3065483 := bstep (se 1 (by rfl) ⟨2299112, by rfl⟩ : syracuseStep 3065483 = 4598225) B4598225
theorem B2043655 : Blo 2043435 2043655 := bstep (se 1 (by rfl) ⟨1532741, by rfl⟩ : syracuseStep 2043655 = 3065483) B3065483
theorem B2299117 : Blo 2043435 2299117 := bbase (se 3 (by rfl) ⟨431084, by rfl⟩ : syracuseStep 2299117 = 862169) (by norm_num)
theorem B3065489 : Blo 2043435 3065489 := bstep (se 2 (by rfl) ⟨1149558, by rfl⟩ : syracuseStep 3065489 = 2299117) B2299117
theorem B2043659 : Blo 2043435 2043659 := bstep (se 1 (by rfl) ⟨1532744, by rfl⟩ : syracuseStep 2043659 = 3065489) B3065489
theorem B6897365 : Blo 2043435 6897365 := bbase (se 7 (by rfl) ⟨80828, by rfl⟩ : syracuseStep 6897365 = 161657) (by norm_num)
theorem B4598243 : Blo 2043435 4598243 := bstep (se 1 (by rfl) ⟨3448682, by rfl⟩ : syracuseStep 4598243 = 6897365) B6897365
theorem B3065495 : Blo 2043435 3065495 := bstep (se 1 (by rfl) ⟨2299121, by rfl⟩ : syracuseStep 3065495 = 4598243) B4598243
theorem B2043663 : Blo 2043435 2043663 := bstep (se 1 (by rfl) ⟨1532747, by rfl⟩ : syracuseStep 2043663 = 3065495) B3065495
theorem B3065501 : Blo 2043435 3065501 := bbase (se 3 (by rfl) ⟨574781, by rfl⟩ : syracuseStep 3065501 = 1149563) (by norm_num)
theorem B2043667 : Blo 2043435 2043667 := bstep (se 1 (by rfl) ⟨1532750, by rfl⟩ : syracuseStep 2043667 = 3065501) B3065501
theorem B4598261 : Blo 2043435 4598261 := bbase (se 5 (by rfl) ⟨215543, by rfl⟩ : syracuseStep 4598261 = 431087) (by norm_num)
theorem B3065507 : Blo 2043435 3065507 := bstep (se 1 (by rfl) ⟨2299130, by rfl⟩ : syracuseStep 3065507 = 4598261) B4598261
theorem B2043671 : Blo 2043435 2043671 := bstep (se 1 (by rfl) ⟨1532753, by rfl⟩ : syracuseStep 2043671 = 3065507) B3065507
theorem B3495757 : Blo 2043435 3495757 := bbase (se 3 (by rfl) ⟨655454, by rfl⟩ : syracuseStep 3495757 = 1310909) (by norm_num)
theorem B4661009 : Blo 2043435 4661009 := bstep (se 2 (by rfl) ⟨1747878, by rfl⟩ : syracuseStep 4661009 = 3495757) B3495757
theorem B3107339 : Blo 2043435 3107339 := bstep (se 1 (by rfl) ⟨2330504, by rfl⟩ : syracuseStep 3107339 = 4661009) B4661009
theorem B2071559 : Blo 2043435 2071559 := bstep (se 1 (by rfl) ⟨1553669, by rfl⟩ : syracuseStep 2071559 = 3107339) B3107339
theorem B5524157 : Blo 2043435 5524157 := bstep (se 3 (by rfl) ⟨1035779, by rfl⟩ : syracuseStep 5524157 = 2071559) B2071559
theorem B14731085 : Blo 2043435 14731085 := bstep (se 3 (by rfl) ⟨2762078, by rfl⟩ : syracuseStep 14731085 = 5524157) B5524157
theorem B39282893 : Blo 2043435 39282893 := bstep (se 3 (by rfl) ⟨7365542, by rfl⟩ : syracuseStep 39282893 = 14731085) B14731085
theorem B26188595 : Blo 2043435 26188595 := bstep (se 1 (by rfl) ⟨19641446, by rfl⟩ : syracuseStep 26188595 = 39282893) B39282893
theorem B17459063 : Blo 2043435 17459063 := bstep (se 1 (by rfl) ⟨13094297, by rfl⟩ : syracuseStep 17459063 = 26188595) B26188595
theorem B11639375 : Blo 2043435 11639375 := bstep (se 1 (by rfl) ⟨8729531, by rfl⟩ : syracuseStep 11639375 = 17459063) B17459063
theorem B7759583 : Blo 2043435 7759583 := bstep (se 1 (by rfl) ⟨5819687, by rfl⟩ : syracuseStep 7759583 = 11639375) B11639375
theorem B5173055 : Blo 2043435 5173055 := bstep (se 1 (by rfl) ⟨3879791, by rfl⟩ : syracuseStep 5173055 = 7759583) B7759583
theorem B3448703 : Blo 2043435 3448703 := bstep (se 1 (by rfl) ⟨2586527, by rfl⟩ : syracuseStep 3448703 = 5173055) B5173055
theorem B2299135 : Blo 2043435 2299135 := bstep (se 1 (by rfl) ⟨1724351, by rfl⟩ : syracuseStep 2299135 = 3448703) B3448703
theorem B3065513 : Blo 2043435 3065513 := bstep (se 2 (by rfl) ⟨1149567, by rfl⟩ : syracuseStep 3065513 = 2299135) B2299135
theorem B2043675 : Blo 2043435 2043675 := bstep (se 1 (by rfl) ⟨1532756, by rfl⟩ : syracuseStep 2043675 = 3065513) B3065513
theorem B3273581 : Blo 2043435 3273581 := bbase (se 3 (by rfl) ⟨613796, by rfl⟩ : syracuseStep 3273581 = 1227593) (by norm_num)
theorem B2182387 : Blo 2043435 2182387 := bstep (se 1 (by rfl) ⟨1636790, by rfl⟩ : syracuseStep 2182387 = 3273581) B3273581
theorem B2909849 : Blo 2043435 2909849 := bstep (se 2 (by rfl) ⟨1091193, by rfl⟩ : syracuseStep 2909849 = 2182387) B2182387
theorem B7759597 : Blo 2043435 7759597 := bstep (se 3 (by rfl) ⟨1454924, by rfl⟩ : syracuseStep 7759597 = 2909849) B2909849
theorem B10346129 : Blo 2043435 10346129 := bstep (se 2 (by rfl) ⟨3879798, by rfl⟩ : syracuseStep 10346129 = 7759597) B7759597
theorem B6897419 : Blo 2043435 6897419 := bstep (se 1 (by rfl) ⟨5173064, by rfl⟩ : syracuseStep 6897419 = 10346129) B10346129
theorem B4598279 : Blo 2043435 4598279 := bstep (se 1 (by rfl) ⟨3448709, by rfl⟩ : syracuseStep 4598279 = 6897419) B6897419
theorem B3065519 : Blo 2043435 3065519 := bstep (se 1 (by rfl) ⟨2299139, by rfl⟩ : syracuseStep 3065519 = 4598279) B4598279
theorem B2043679 : Blo 2043435 2043679 := bstep (se 1 (by rfl) ⟨1532759, by rfl⟩ : syracuseStep 2043679 = 3065519) B3065519
theorem B3065525 : Blo 2043435 3065525 := bbase (se 5 (by rfl) ⟨143696, by rfl⟩ : syracuseStep 3065525 = 287393) (by norm_num)
theorem B2043683 : Blo 2043435 2043683 := bstep (se 1 (by rfl) ⟨1532762, by rfl⟩ : syracuseStep 2043683 = 3065525) B3065525
theorem B5173085 : Blo 2043435 5173085 := bbase (se 3 (by rfl) ⟨969953, by rfl⟩ : syracuseStep 5173085 = 1939907) (by norm_num)
theorem B3448723 : Blo 2043435 3448723 := bstep (se 1 (by rfl) ⟨2586542, by rfl⟩ : syracuseStep 3448723 = 5173085) B5173085
theorem B4598297 : Blo 2043435 4598297 := bstep (se 2 (by rfl) ⟨1724361, by rfl⟩ : syracuseStep 4598297 = 3448723) B3448723
theorem B3065531 : Blo 2043435 3065531 := bstep (se 1 (by rfl) ⟨2299148, by rfl⟩ : syracuseStep 3065531 = 4598297) B4598297
theorem B2043687 : Blo 2043435 2043687 := bstep (se 1 (by rfl) ⟨1532765, by rfl⟩ : syracuseStep 2043687 = 3065531) B3065531
theorem B2299153 : Blo 2043435 2299153 := bbase (se 2 (by rfl) ⟨862182, by rfl⟩ : syracuseStep 2299153 = 1724365) (by norm_num)
theorem B3065537 : Blo 2043435 3065537 := bstep (se 2 (by rfl) ⟨1149576, by rfl⟩ : syracuseStep 3065537 = 2299153) B2299153
theorem B2043691 : Blo 2043435 2043691 := bstep (se 1 (by rfl) ⟨1532768, by rfl⟩ : syracuseStep 2043691 = 3065537) B3065537
theorem B3879829 : Blo 2043435 3879829 := bbase (se 6 (by rfl) ⟨90933, by rfl⟩ : syracuseStep 3879829 = 181867) (by norm_num)
theorem B5173105 : Blo 2043435 5173105 := bstep (se 2 (by rfl) ⟨1939914, by rfl⟩ : syracuseStep 5173105 = 3879829) B3879829
theorem B6897473 : Blo 2043435 6897473 := bstep (se 2 (by rfl) ⟨2586552, by rfl⟩ : syracuseStep 6897473 = 5173105) B5173105
theorem B4598315 : Blo 2043435 4598315 := bstep (se 1 (by rfl) ⟨3448736, by rfl⟩ : syracuseStep 4598315 = 6897473) B6897473
theorem B3065543 : Blo 2043435 3065543 := bstep (se 1 (by rfl) ⟨2299157, by rfl⟩ : syracuseStep 3065543 = 4598315) B4598315
theorem B2043695 : Blo 2043435 2043695 := bstep (se 1 (by rfl) ⟨1532771, by rfl⟩ : syracuseStep 2043695 = 3065543) B3065543
theorem B3065549 : Blo 2043435 3065549 := bbase (se 3 (by rfl) ⟨574790, by rfl⟩ : syracuseStep 3065549 = 1149581) (by norm_num)
theorem B2043699 : Blo 2043435 2043699 := bstep (se 1 (by rfl) ⟨1532774, by rfl⟩ : syracuseStep 2043699 = 3065549) B3065549
theorem B4598333 : Blo 2043435 4598333 := bbase (se 3 (by rfl) ⟨862187, by rfl⟩ : syracuseStep 4598333 = 1724375) (by norm_num)
theorem B3065555 : Blo 2043435 3065555 := bstep (se 1 (by rfl) ⟨2299166, by rfl⟩ : syracuseStep 3065555 = 4598333) B4598333
theorem B2043703 : Blo 2043435 2043703 := bstep (se 1 (by rfl) ⟨1532777, by rfl⟩ : syracuseStep 2043703 = 3065555) B3065555
theorem B3448757 : Blo 2043435 3448757 := bbase (se 5 (by rfl) ⟨161660, by rfl⟩ : syracuseStep 3448757 = 323321) (by norm_num)
theorem B2299171 : Blo 2043435 2299171 := bstep (se 1 (by rfl) ⟨1724378, by rfl⟩ : syracuseStep 2299171 = 3448757) B3448757
theorem B3065561 : Blo 2043435 3065561 := bstep (se 2 (by rfl) ⟨1149585, by rfl⟩ : syracuseStep 3065561 = 2299171) B2299171
theorem B2043707 : Blo 2043435 2043707 := bstep (se 1 (by rfl) ⟨1532780, by rfl⟩ : syracuseStep 2043707 = 3065561) B3065561
theorem B2182421 : Blo 2043435 2182421 := bbase (se 6 (by rfl) ⟨51150, by rfl⟩ : syracuseStep 2182421 = 102301) (by norm_num)
theorem B5819789 : Blo 2043435 5819789 := bstep (se 3 (by rfl) ⟨1091210, by rfl⟩ : syracuseStep 5819789 = 2182421) B2182421
theorem B15519437 : Blo 2043435 15519437 := bstep (se 3 (by rfl) ⟨2909894, by rfl⟩ : syracuseStep 15519437 = 5819789) B5819789
theorem B10346291 : Blo 2043435 10346291 := bstep (se 1 (by rfl) ⟨7759718, by rfl⟩ : syracuseStep 10346291 = 15519437) B15519437
theorem B6897527 : Blo 2043435 6897527 := bstep (se 1 (by rfl) ⟨5173145, by rfl⟩ : syracuseStep 6897527 = 10346291) B10346291
theorem B4598351 : Blo 2043435 4598351 := bstep (se 1 (by rfl) ⟨3448763, by rfl⟩ : syracuseStep 4598351 = 6897527) B6897527
theorem B3065567 : Blo 2043435 3065567 := bstep (se 1 (by rfl) ⟨2299175, by rfl⟩ : syracuseStep 3065567 = 4598351) B4598351
theorem B2043711 : Blo 2043435 2043711 := bstep (se 1 (by rfl) ⟨1532783, by rfl⟩ : syracuseStep 2043711 = 3065567) B3065567
theorem B3065573 : Blo 2043435 3065573 := bbase (se 4 (by rfl) ⟨287397, by rfl⟩ : syracuseStep 3065573 = 574795) (by norm_num)
theorem B2043715 : Blo 2043435 2043715 := bstep (se 1 (by rfl) ⟨1532786, by rfl⟩ : syracuseStep 2043715 = 3065573) B3065573
theorem B5819813 : Blo 2043435 5819813 := bbase (se 4 (by rfl) ⟨545607, by rfl⟩ : syracuseStep 5819813 = 1091215) (by norm_num)
theorem B3879875 : Blo 2043435 3879875 := bstep (se 1 (by rfl) ⟨2909906, by rfl⟩ : syracuseStep 3879875 = 5819813) B5819813
theorem B2586583 : Blo 2043435 2586583 := bstep (se 1 (by rfl) ⟨1939937, by rfl⟩ : syracuseStep 2586583 = 3879875) B3879875
theorem B3448777 : Blo 2043435 3448777 := bstep (se 2 (by rfl) ⟨1293291, by rfl⟩ : syracuseStep 3448777 = 2586583) B2586583
theorem B4598369 : Blo 2043435 4598369 := bstep (se 2 (by rfl) ⟨1724388, by rfl⟩ : syracuseStep 4598369 = 3448777) B3448777
theorem B3065579 : Blo 2043435 3065579 := bstep (se 1 (by rfl) ⟨2299184, by rfl⟩ : syracuseStep 3065579 = 4598369) B4598369
theorem B2043719 : Blo 2043435 2043719 := bstep (se 1 (by rfl) ⟨1532789, by rfl⟩ : syracuseStep 2043719 = 3065579) B3065579
theorem B2299189 : Blo 2043435 2299189 := bbase (se 5 (by rfl) ⟨107774, by rfl⟩ : syracuseStep 2299189 = 215549) (by norm_num)
theorem B3065585 : Blo 2043435 3065585 := bstep (se 2 (by rfl) ⟨1149594, by rfl⟩ : syracuseStep 3065585 = 2299189) B2299189
theorem B2043723 : Blo 2043435 2043723 := bstep (se 1 (by rfl) ⟨1532792, by rfl⟩ : syracuseStep 2043723 = 3065585) B3065585
theorem B2586593 : Blo 2043435 2586593 := bbase (se 2 (by rfl) ⟨969972, by rfl⟩ : syracuseStep 2586593 = 1939945) (by norm_num)
theorem B6897581 : Blo 2043435 6897581 := bstep (se 3 (by rfl) ⟨1293296, by rfl⟩ : syracuseStep 6897581 = 2586593) B2586593
theorem B4598387 : Blo 2043435 4598387 := bstep (se 1 (by rfl) ⟨3448790, by rfl⟩ : syracuseStep 4598387 = 6897581) B6897581
theorem B3065591 : Blo 2043435 3065591 := bstep (se 1 (by rfl) ⟨2299193, by rfl⟩ : syracuseStep 3065591 = 4598387) B4598387
theorem B2043727 : Blo 2043435 2043727 := bstep (se 1 (by rfl) ⟨1532795, by rfl⟩ : syracuseStep 2043727 = 3065591) B3065591
theorem B3065597 : Blo 2043435 3065597 := bbase (se 3 (by rfl) ⟨574799, by rfl⟩ : syracuseStep 3065597 = 1149599) (by norm_num)
theorem B2043731 : Blo 2043435 2043731 := bstep (se 1 (by rfl) ⟨1532798, by rfl⟩ : syracuseStep 2043731 = 3065597) B3065597
theorem B4598405 : Blo 2043435 4598405 := bbase (se 4 (by rfl) ⟨431100, by rfl⟩ : syracuseStep 4598405 = 862201) (by norm_num)
theorem B3065603 : Blo 2043435 3065603 := bstep (se 1 (by rfl) ⟨2299202, by rfl⟩ : syracuseStep 3065603 = 4598405) B4598405
theorem B2043735 : Blo 2043435 2043735 := bstep (se 1 (by rfl) ⟨1532801, by rfl⟩ : syracuseStep 2043735 = 3065603) B3065603
theorem B6991733 : Blo 2043435 6991733 := bbase (se 5 (by rfl) ⟨327737, by rfl⟩ : syracuseStep 6991733 = 655475) (by norm_num)
theorem B4661155 : Blo 2043435 4661155 := bstep (se 1 (by rfl) ⟨3495866, by rfl⟩ : syracuseStep 4661155 = 6991733) B6991733
theorem B24859493 : Blo 2043435 24859493 := bstep (se 4 (by rfl) ⟨2330577, by rfl⟩ : syracuseStep 24859493 = 4661155) B4661155
theorem B16572995 : Blo 2043435 16572995 := bstep (se 1 (by rfl) ⟨12429746, by rfl⟩ : syracuseStep 16572995 = 24859493) B24859493
theorem B11048663 : Blo 2043435 11048663 := bstep (se 1 (by rfl) ⟨8286497, by rfl⟩ : syracuseStep 11048663 = 16572995) B16572995
theorem B7365775 : Blo 2043435 7365775 := bstep (se 1 (by rfl) ⟨5524331, by rfl⟩ : syracuseStep 7365775 = 11048663) B11048663
theorem B9821033 : Blo 2043435 9821033 := bstep (se 2 (by rfl) ⟨3682887, by rfl⟩ : syracuseStep 9821033 = 7365775) B7365775
theorem B6547355 : Blo 2043435 6547355 := bstep (se 1 (by rfl) ⟨4910516, by rfl⟩ : syracuseStep 6547355 = 9821033) B9821033
theorem B4364903 : Blo 2043435 4364903 := bstep (se 1 (by rfl) ⟨3273677, by rfl⟩ : syracuseStep 4364903 = 6547355) B6547355
theorem B2909935 : Blo 2043435 2909935 := bstep (se 1 (by rfl) ⟨2182451, by rfl⟩ : syracuseStep 2909935 = 4364903) B4364903
theorem B3879913 : Blo 2043435 3879913 := bstep (se 2 (by rfl) ⟨1454967, by rfl⟩ : syracuseStep 3879913 = 2909935) B2909935
theorem B5173217 : Blo 2043435 5173217 := bstep (se 2 (by rfl) ⟨1939956, by rfl⟩ : syracuseStep 5173217 = 3879913) B3879913
theorem B3448811 : Blo 2043435 3448811 := bstep (se 1 (by rfl) ⟨2586608, by rfl⟩ : syracuseStep 3448811 = 5173217) B5173217
theorem B2299207 : Blo 2043435 2299207 := bstep (se 1 (by rfl) ⟨1724405, by rfl⟩ : syracuseStep 2299207 = 3448811) B3448811
theorem B3065609 : Blo 2043435 3065609 := bstep (se 2 (by rfl) ⟨1149603, by rfl⟩ : syracuseStep 3065609 = 2299207) B2299207
theorem B2043739 : Blo 2043435 2043739 := bstep (se 1 (by rfl) ⟨1532804, by rfl⟩ : syracuseStep 2043739 = 3065609) B3065609
theorem B10346453 : Blo 2043435 10346453 := bbase (se 7 (by rfl) ⟨121247, by rfl⟩ : syracuseStep 10346453 = 242495) (by norm_num)
theorem B6897635 : Blo 2043435 6897635 := bstep (se 1 (by rfl) ⟨5173226, by rfl⟩ : syracuseStep 6897635 = 10346453) B10346453
theorem B4598423 : Blo 2043435 4598423 := bstep (se 1 (by rfl) ⟨3448817, by rfl⟩ : syracuseStep 4598423 = 6897635) B6897635
theorem B3065615 : Blo 2043435 3065615 := bstep (se 1 (by rfl) ⟨2299211, by rfl⟩ : syracuseStep 3065615 = 4598423) B4598423
theorem B2043743 : Blo 2043435 2043743 := bstep (se 1 (by rfl) ⟨1532807, by rfl⟩ : syracuseStep 2043743 = 3065615) B3065615
theorem B3065621 : Blo 2043435 3065621 := bbase (se 6 (by rfl) ⟨71850, by rfl⟩ : syracuseStep 3065621 = 143701) (by norm_num)
theorem B2043747 : Blo 2043435 2043747 := bstep (se 1 (by rfl) ⟨1532810, by rfl⟩ : syracuseStep 2043747 = 3065621) B3065621
theorem B4484845 : Blo 2043435 4484845 := bbase (se 3 (by rfl) ⟨840908, by rfl⟩ : syracuseStep 4484845 = 1681817) (by norm_num)
theorem B5979793 : Blo 2043435 5979793 := bstep (se 2 (by rfl) ⟨2242422, by rfl⟩ : syracuseStep 5979793 = 4484845) B4484845
theorem B7973057 : Blo 2043435 7973057 := bstep (se 2 (by rfl) ⟨2989896, by rfl⟩ : syracuseStep 7973057 = 5979793) B5979793
theorem B5315371 : Blo 2043435 5315371 := bstep (se 1 (by rfl) ⟨3986528, by rfl⟩ : syracuseStep 5315371 = 7973057) B7973057
theorem B28348645 : Blo 2043435 28348645 := bstep (se 4 (by rfl) ⟨2657685, by rfl⟩ : syracuseStep 28348645 = 5315371) B5315371
theorem B604771093 : Blo 2043435 604771093 := bstep (se 6 (by rfl) ⟨14174322, by rfl⟩ : syracuseStep 604771093 = 28348645) B28348645
theorem B3225445829 : Blo 2043435 3225445829 := bstep (se 4 (by rfl) ⟨302385546, by rfl⟩ : syracuseStep 3225445829 = 604771093) B604771093
theorem B2150297219 : Blo 2043435 2150297219 := bstep (se 1 (by rfl) ⟨1612722914, by rfl⟩ : syracuseStep 2150297219 = 3225445829) B3225445829
theorem B5734125917 : Blo 2043435 5734125917 := bstep (se 3 (by rfl) ⟨1075148609, by rfl⟩ : syracuseStep 5734125917 = 2150297219) B2150297219
theorem B3822750611 : Blo 2043435 3822750611 := bstep (se 1 (by rfl) ⟨2867062958, by rfl⟩ : syracuseStep 3822750611 = 5734125917) B5734125917
theorem B2548500407 : Blo 2043435 2548500407 := bstep (se 1 (by rfl) ⟨1911375305, by rfl⟩ : syracuseStep 2548500407 = 3822750611) B3822750611
theorem B1699000271 : Blo 2043435 1699000271 := bstep (se 1 (by rfl) ⟨1274250203, by rfl⟩ : syracuseStep 1699000271 = 2548500407) B2548500407
theorem B1132666847 : Blo 2043435 1132666847 := bstep (se 1 (by rfl) ⟨849500135, by rfl⟩ : syracuseStep 1132666847 = 1699000271) B1699000271
theorem B755111231 : Blo 2043435 755111231 := bstep (se 1 (by rfl) ⟨566333423, by rfl⟩ : syracuseStep 755111231 = 1132666847) B1132666847
theorem B503407487 : Blo 2043435 503407487 := bstep (se 1 (by rfl) ⟨377555615, by rfl⟩ : syracuseStep 503407487 = 755111231) B755111231
theorem B335604991 : Blo 2043435 335604991 := bstep (se 1 (by rfl) ⟨251703743, by rfl⟩ : syracuseStep 335604991 = 503407487) B503407487
theorem B447473321 : Blo 2043435 447473321 := bstep (se 2 (by rfl) ⟨167802495, by rfl⟩ : syracuseStep 447473321 = 335604991) B335604991
theorem B298315547 : Blo 2043435 298315547 := bstep (se 1 (by rfl) ⟨223736660, by rfl⟩ : syracuseStep 298315547 = 447473321) B447473321
theorem B198877031 : Blo 2043435 198877031 := bstep (se 1 (by rfl) ⟨149157773, by rfl⟩ : syracuseStep 198877031 = 298315547) B298315547
theorem B132584687 : Blo 2043435 132584687 := bstep (se 1 (by rfl) ⟨99438515, by rfl⟩ : syracuseStep 132584687 = 198877031) B198877031
theorem B88389791 : Blo 2043435 88389791 := bstep (se 1 (by rfl) ⟨66292343, by rfl⟩ : syracuseStep 88389791 = 132584687) B132584687
theorem B58926527 : Blo 2043435 58926527 := bstep (se 1 (by rfl) ⟨44194895, by rfl⟩ : syracuseStep 58926527 = 88389791) B88389791
theorem B39284351 : Blo 2043435 39284351 := bstep (se 1 (by rfl) ⟨29463263, by rfl⟩ : syracuseStep 39284351 = 58926527) B58926527
theorem B26189567 : Blo 2043435 26189567 := bstep (se 1 (by rfl) ⟨19642175, by rfl⟩ : syracuseStep 26189567 = 39284351) B39284351
theorem B17459711 : Blo 2043435 17459711 := bstep (se 1 (by rfl) ⟨13094783, by rfl⟩ : syracuseStep 17459711 = 26189567) B26189567
theorem B11639807 : Blo 2043435 11639807 := bstep (se 1 (by rfl) ⟨8729855, by rfl⟩ : syracuseStep 11639807 = 17459711) B17459711
theorem B7759871 : Blo 2043435 7759871 := bstep (se 1 (by rfl) ⟨5819903, by rfl⟩ : syracuseStep 7759871 = 11639807) B11639807
theorem B5173247 : Blo 2043435 5173247 := bstep (se 1 (by rfl) ⟨3879935, by rfl⟩ : syracuseStep 5173247 = 7759871) B7759871
theorem B3448831 : Blo 2043435 3448831 := bstep (se 1 (by rfl) ⟨2586623, by rfl⟩ : syracuseStep 3448831 = 5173247) B5173247
theorem B4598441 : Blo 2043435 4598441 := bstep (se 2 (by rfl) ⟨1724415, by rfl⟩ : syracuseStep 4598441 = 3448831) B3448831
theorem B3065627 : Blo 2043435 3065627 := bstep (se 1 (by rfl) ⟨2299220, by rfl⟩ : syracuseStep 3065627 = 4598441) B4598441
theorem B2043751 : Blo 2043435 2043751 := bstep (se 1 (by rfl) ⟨1532813, by rfl⟩ : syracuseStep 2043751 = 3065627) B3065627
theorem B2299225 : Blo 2043435 2299225 := bbase (se 2 (by rfl) ⟨862209, by rfl⟩ : syracuseStep 2299225 = 1724419) (by norm_num)
theorem B3065633 : Blo 2043435 3065633 := bstep (se 2 (by rfl) ⟨1149612, by rfl⟩ : syracuseStep 3065633 = 2299225) B2299225
theorem B2043755 : Blo 2043435 2043755 := bstep (se 1 (by rfl) ⟨1532816, by rfl⟩ : syracuseStep 2043755 = 3065633) B3065633
theorem B3273709 : Blo 2043435 3273709 := bbase (se 3 (by rfl) ⟨613820, by rfl⟩ : syracuseStep 3273709 = 1227641) (by norm_num)
theorem B4364945 : Blo 2043435 4364945 := bstep (se 2 (by rfl) ⟨1636854, by rfl⟩ : syracuseStep 4364945 = 3273709) B3273709
theorem B2909963 : Blo 2043435 2909963 := bstep (se 1 (by rfl) ⟨2182472, by rfl⟩ : syracuseStep 2909963 = 4364945) B4364945
theorem B7759901 : Blo 2043435 7759901 := bstep (se 3 (by rfl) ⟨1454981, by rfl⟩ : syracuseStep 7759901 = 2909963) B2909963
theorem B5173267 : Blo 2043435 5173267 := bstep (se 1 (by rfl) ⟨3879950, by rfl⟩ : syracuseStep 5173267 = 7759901) B7759901
theorem B6897689 : Blo 2043435 6897689 := bstep (se 2 (by rfl) ⟨2586633, by rfl⟩ : syracuseStep 6897689 = 5173267) B5173267
theorem B4598459 : Blo 2043435 4598459 := bstep (se 1 (by rfl) ⟨3448844, by rfl⟩ : syracuseStep 4598459 = 6897689) B6897689
theorem B3065639 : Blo 2043435 3065639 := bstep (se 1 (by rfl) ⟨2299229, by rfl⟩ : syracuseStep 3065639 = 4598459) B4598459
theorem B2043759 : Blo 2043435 2043759 := bstep (se 1 (by rfl) ⟨1532819, by rfl⟩ : syracuseStep 2043759 = 3065639) B3065639
theorem B3065645 : Blo 2043435 3065645 := bbase (se 3 (by rfl) ⟨574808, by rfl⟩ : syracuseStep 3065645 = 1149617) (by norm_num)
theorem B2043763 : Blo 2043435 2043763 := bstep (se 1 (by rfl) ⟨1532822, by rfl⟩ : syracuseStep 2043763 = 3065645) B3065645
theorem B4598477 : Blo 2043435 4598477 := bbase (se 3 (by rfl) ⟨862214, by rfl⟩ : syracuseStep 4598477 = 1724429) (by norm_num)
theorem B3065651 : Blo 2043435 3065651 := bstep (se 1 (by rfl) ⟨2299238, by rfl⟩ : syracuseStep 3065651 = 4598477) B4598477
theorem B2043767 : Blo 2043435 2043767 := bstep (se 1 (by rfl) ⟨1532825, by rfl⟩ : syracuseStep 2043767 = 3065651) B3065651
theorem B2586649 : Blo 2043435 2586649 := bbase (se 2 (by rfl) ⟨969993, by rfl⟩ : syracuseStep 2586649 = 1939987) (by norm_num)
theorem B3448865 : Blo 2043435 3448865 := bstep (se 2 (by rfl) ⟨1293324, by rfl⟩ : syracuseStep 3448865 = 2586649) B2586649
theorem B2299243 : Blo 2043435 2299243 := bstep (se 1 (by rfl) ⟨1724432, by rfl⟩ : syracuseStep 2299243 = 3448865) B3448865
theorem B3065657 : Blo 2043435 3065657 := bstep (se 2 (by rfl) ⟨1149621, by rfl⟩ : syracuseStep 3065657 = 2299243) B2299243
theorem B2043771 : Blo 2043435 2043771 := bstep (se 1 (by rfl) ⟨1532828, by rfl⟩ : syracuseStep 2043771 = 3065657) B3065657
theorem B8729957 : Blo 2043435 8729957 := bbase (se 4 (by rfl) ⟨818433, by rfl⟩ : syracuseStep 8729957 = 1636867) (by norm_num)
theorem B23279885 : Blo 2043435 23279885 := bstep (se 3 (by rfl) ⟨4364978, by rfl⟩ : syracuseStep 23279885 = 8729957) B8729957
theorem B15519923 : Blo 2043435 15519923 := bstep (se 1 (by rfl) ⟨11639942, by rfl⟩ : syracuseStep 15519923 = 23279885) B23279885
theorem B10346615 : Blo 2043435 10346615 := bstep (se 1 (by rfl) ⟨7759961, by rfl⟩ : syracuseStep 10346615 = 15519923) B15519923
theorem B6897743 : Blo 2043435 6897743 := bstep (se 1 (by rfl) ⟨5173307, by rfl⟩ : syracuseStep 6897743 = 10346615) B10346615
theorem B4598495 : Blo 2043435 4598495 := bstep (se 1 (by rfl) ⟨3448871, by rfl⟩ : syracuseStep 4598495 = 6897743) B6897743
theorem B3065663 : Blo 2043435 3065663 := bstep (se 1 (by rfl) ⟨2299247, by rfl⟩ : syracuseStep 3065663 = 4598495) B4598495
theorem B2043775 : Blo 2043435 2043775 := bstep (se 1 (by rfl) ⟨1532831, by rfl⟩ : syracuseStep 2043775 = 3065663) B3065663
theorem B3065669 : Blo 2043435 3065669 := bbase (se 4 (by rfl) ⟨287406, by rfl⟩ : syracuseStep 3065669 = 574813) (by norm_num)
theorem B2043779 : Blo 2043435 2043779 := bstep (se 1 (by rfl) ⟨1532834, by rfl⟩ : syracuseStep 2043779 = 3065669) B3065669
theorem B3448885 : Blo 2043435 3448885 := bbase (se 5 (by rfl) ⟨161666, by rfl⟩ : syracuseStep 3448885 = 323333) (by norm_num)
theorem B4598513 : Blo 2043435 4598513 := bstep (se 2 (by rfl) ⟨1724442, by rfl⟩ : syracuseStep 4598513 = 3448885) B3448885
theorem B3065675 : Blo 2043435 3065675 := bstep (se 1 (by rfl) ⟨2299256, by rfl⟩ : syracuseStep 3065675 = 4598513) B4598513
theorem B2043783 : Blo 2043435 2043783 := bstep (se 1 (by rfl) ⟨1532837, by rfl⟩ : syracuseStep 2043783 = 3065675) B3065675
theorem B2299261 : Blo 2043435 2299261 := bbase (se 3 (by rfl) ⟨431111, by rfl⟩ : syracuseStep 2299261 = 862223) (by norm_num)
theorem B3065681 : Blo 2043435 3065681 := bstep (se 2 (by rfl) ⟨1149630, by rfl⟩ : syracuseStep 3065681 = 2299261) B2299261
theorem B2043787 : Blo 2043435 2043787 := bstep (se 1 (by rfl) ⟨1532840, by rfl⟩ : syracuseStep 2043787 = 3065681) B3065681
theorem B6897797 : Blo 2043435 6897797 := bbase (se 4 (by rfl) ⟨646668, by rfl⟩ : syracuseStep 6897797 = 1293337) (by norm_num)
theorem B4598531 : Blo 2043435 4598531 := bstep (se 1 (by rfl) ⟨3448898, by rfl⟩ : syracuseStep 4598531 = 6897797) B6897797
theorem B3065687 : Blo 2043435 3065687 := bstep (se 1 (by rfl) ⟨2299265, by rfl⟩ : syracuseStep 3065687 = 4598531) B4598531
theorem B2043791 : Blo 2043435 2043791 := bstep (se 1 (by rfl) ⟨1532843, by rfl⟩ : syracuseStep 2043791 = 3065687) B3065687
theorem B3065693 : Blo 2043435 3065693 := bbase (se 3 (by rfl) ⟨574817, by rfl⟩ : syracuseStep 3065693 = 1149635) (by norm_num)
theorem B2043795 : Blo 2043435 2043795 := bstep (se 1 (by rfl) ⟨1532846, by rfl⟩ : syracuseStep 2043795 = 3065693) B3065693
theorem B4598549 : Blo 2043435 4598549 := bbase (se 6 (by rfl) ⟨107778, by rfl⟩ : syracuseStep 4598549 = 215557) (by norm_num)
theorem B3065699 : Blo 2043435 3065699 := bstep (se 1 (by rfl) ⟨2299274, by rfl⟩ : syracuseStep 3065699 = 4598549) B4598549
theorem B2043799 : Blo 2043435 2043799 := bstep (se 1 (by rfl) ⟨1532849, by rfl⟩ : syracuseStep 2043799 = 3065699) B3065699
theorem B7760069 : Blo 2043435 7760069 := bbase (se 4 (by rfl) ⟨727506, by rfl⟩ : syracuseStep 7760069 = 1455013) (by norm_num)
theorem B5173379 : Blo 2043435 5173379 := bstep (se 1 (by rfl) ⟨3880034, by rfl⟩ : syracuseStep 5173379 = 7760069) B7760069
theorem B3448919 : Blo 2043435 3448919 := bstep (se 1 (by rfl) ⟨2586689, by rfl⟩ : syracuseStep 3448919 = 5173379) B5173379
theorem B2299279 : Blo 2043435 2299279 := bstep (se 1 (by rfl) ⟨1724459, by rfl⟩ : syracuseStep 2299279 = 3448919) B3448919
theorem B3065705 : Blo 2043435 3065705 := bstep (se 2 (by rfl) ⟨1149639, by rfl⟩ : syracuseStep 3065705 = 2299279) B2299279
theorem B2043803 : Blo 2043435 2043803 := bstep (se 1 (by rfl) ⟨1532852, by rfl⟩ : syracuseStep 2043803 = 3065705) B3065705
theorem B2071693 : Blo 2043435 2071693 := bbase (se 3 (by rfl) ⟨388442, by rfl⟩ : syracuseStep 2071693 = 776885) (by norm_num)
theorem B2762257 : Blo 2043435 2762257 := bstep (se 2 (by rfl) ⟨1035846, by rfl⟩ : syracuseStep 2762257 = 2071693) B2071693
theorem B3683009 : Blo 2043435 3683009 := bstep (se 2 (by rfl) ⟨1381128, by rfl⟩ : syracuseStep 3683009 = 2762257) B2762257
theorem B9821357 : Blo 2043435 9821357 := bstep (se 3 (by rfl) ⟨1841504, by rfl⟩ : syracuseStep 9821357 = 3683009) B3683009
theorem B6547571 : Blo 2043435 6547571 := bstep (se 1 (by rfl) ⟨4910678, by rfl⟩ : syracuseStep 6547571 = 9821357) B9821357
theorem B4365047 : Blo 2043435 4365047 := bstep (se 1 (by rfl) ⟨3273785, by rfl⟩ : syracuseStep 4365047 = 6547571) B6547571
theorem B11640125 : Blo 2043435 11640125 := bstep (se 3 (by rfl) ⟨2182523, by rfl⟩ : syracuseStep 11640125 = 4365047) B4365047
theorem B7760083 : Blo 2043435 7760083 := bstep (se 1 (by rfl) ⟨5820062, by rfl⟩ : syracuseStep 7760083 = 11640125) B11640125
theorem B10346777 : Blo 2043435 10346777 := bstep (se 2 (by rfl) ⟨3880041, by rfl⟩ : syracuseStep 10346777 = 7760083) B7760083
theorem B6897851 : Blo 2043435 6897851 := bstep (se 1 (by rfl) ⟨5173388, by rfl⟩ : syracuseStep 6897851 = 10346777) B10346777
theorem B4598567 : Blo 2043435 4598567 := bstep (se 1 (by rfl) ⟨3448925, by rfl⟩ : syracuseStep 4598567 = 6897851) B6897851
theorem B3065711 : Blo 2043435 3065711 := bstep (se 1 (by rfl) ⟨2299283, by rfl⟩ : syracuseStep 3065711 = 4598567) B4598567
theorem B2043807 : Blo 2043435 2043807 := bstep (se 1 (by rfl) ⟨1532855, by rfl⟩ : syracuseStep 2043807 = 3065711) B3065711
theorem B3065717 : Blo 2043435 3065717 := bbase (se 5 (by rfl) ⟨143705, by rfl⟩ : syracuseStep 3065717 = 287411) (by norm_num)
theorem B2043811 : Blo 2043435 2043811 := bstep (se 1 (by rfl) ⟨1532858, by rfl⟩ : syracuseStep 2043811 = 3065717) B3065717
theorem B3495997 : Blo 2043435 3495997 := bbase (se 3 (by rfl) ⟨655499, by rfl⟩ : syracuseStep 3495997 = 1310999) (by norm_num)
theorem B4661329 : Blo 2043435 4661329 := bstep (se 2 (by rfl) ⟨1747998, by rfl⟩ : syracuseStep 4661329 = 3495997) B3495997
theorem B6215105 : Blo 2043435 6215105 := bstep (se 2 (by rfl) ⟨2330664, by rfl⟩ : syracuseStep 6215105 = 4661329) B4661329
theorem B4143403 : Blo 2043435 4143403 := bstep (se 1 (by rfl) ⟨3107552, by rfl⟩ : syracuseStep 4143403 = 6215105) B6215105
theorem B5524537 : Blo 2043435 5524537 := bstep (se 2 (by rfl) ⟨2071701, by rfl⟩ : syracuseStep 5524537 = 4143403) B4143403
theorem B7366049 : Blo 2043435 7366049 := bstep (se 2 (by rfl) ⟨2762268, by rfl⟩ : syracuseStep 7366049 = 5524537) B5524537
theorem B4910699 : Blo 2043435 4910699 := bstep (se 1 (by rfl) ⟨3683024, by rfl⟩ : syracuseStep 4910699 = 7366049) B7366049
theorem B3273799 : Blo 2043435 3273799 := bstep (se 1 (by rfl) ⟨2455349, by rfl⟩ : syracuseStep 3273799 = 4910699) B4910699
theorem B4365065 : Blo 2043435 4365065 := bstep (se 2 (by rfl) ⟨1636899, by rfl⟩ : syracuseStep 4365065 = 3273799) B3273799
theorem B2910043 : Blo 2043435 2910043 := bstep (se 1 (by rfl) ⟨2182532, by rfl⟩ : syracuseStep 2910043 = 4365065) B4365065
theorem B3880057 : Blo 2043435 3880057 := bstep (se 2 (by rfl) ⟨1455021, by rfl⟩ : syracuseStep 3880057 = 2910043) B2910043
theorem B5173409 : Blo 2043435 5173409 := bstep (se 2 (by rfl) ⟨1940028, by rfl⟩ : syracuseStep 5173409 = 3880057) B3880057
theorem B3448939 : Blo 2043435 3448939 := bstep (se 1 (by rfl) ⟨2586704, by rfl⟩ : syracuseStep 3448939 = 5173409) B5173409
theorem B4598585 : Blo 2043435 4598585 := bstep (se 2 (by rfl) ⟨1724469, by rfl⟩ : syracuseStep 4598585 = 3448939) B3448939
theorem B3065723 : Blo 2043435 3065723 := bstep (se 1 (by rfl) ⟨2299292, by rfl⟩ : syracuseStep 3065723 = 4598585) B4598585
theorem B2043815 : Blo 2043435 2043815 := bstep (se 1 (by rfl) ⟨1532861, by rfl⟩ : syracuseStep 2043815 = 3065723) B3065723
theorem B2299297 : Blo 2043435 2299297 := bbase (se 2 (by rfl) ⟨862236, by rfl⟩ : syracuseStep 2299297 = 1724473) (by norm_num)
theorem B3065729 : Blo 2043435 3065729 := bstep (se 2 (by rfl) ⟨1149648, by rfl⟩ : syracuseStep 3065729 = 2299297) B2299297
theorem B2043819 : Blo 2043435 2043819 := bstep (se 1 (by rfl) ⟨1532864, by rfl⟩ : syracuseStep 2043819 = 3065729) B3065729
theorem B5173429 : Blo 2043435 5173429 := bbase (se 5 (by rfl) ⟨242504, by rfl⟩ : syracuseStep 5173429 = 485009) (by norm_num)
theorem B6897905 : Blo 2043435 6897905 := bstep (se 2 (by rfl) ⟨2586714, by rfl⟩ : syracuseStep 6897905 = 5173429) B5173429
theorem B4598603 : Blo 2043435 4598603 := bstep (se 1 (by rfl) ⟨3448952, by rfl⟩ : syracuseStep 4598603 = 6897905) B6897905
theorem B3065735 : Blo 2043435 3065735 := bstep (se 1 (by rfl) ⟨2299301, by rfl⟩ : syracuseStep 3065735 = 4598603) B4598603
theorem B2043823 : Blo 2043435 2043823 := bstep (se 1 (by rfl) ⟨1532867, by rfl⟩ : syracuseStep 2043823 = 3065735) B3065735
theorem B3065741 : Blo 2043435 3065741 := bbase (se 3 (by rfl) ⟨574826, by rfl⟩ : syracuseStep 3065741 = 1149653) (by norm_num)
theorem B2043827 : Blo 2043435 2043827 := bstep (se 1 (by rfl) ⟨1532870, by rfl⟩ : syracuseStep 2043827 = 3065741) B3065741
theorem B4598621 : Blo 2043435 4598621 := bbase (se 3 (by rfl) ⟨862241, by rfl⟩ : syracuseStep 4598621 = 1724483) (by norm_num)
theorem B3065747 : Blo 2043435 3065747 := bstep (se 1 (by rfl) ⟨2299310, by rfl⟩ : syracuseStep 3065747 = 4598621) B4598621
theorem B2043831 : Blo 2043435 2043831 := bstep (se 1 (by rfl) ⟨1532873, by rfl⟩ : syracuseStep 2043831 = 3065747) B3065747
theorem B3448973 : Blo 2043435 3448973 := bbase (se 3 (by rfl) ⟨646682, by rfl⟩ : syracuseStep 3448973 = 1293365) (by norm_num)
theorem B2299315 : Blo 2043435 2299315 := bstep (se 1 (by rfl) ⟨1724486, by rfl⟩ : syracuseStep 2299315 = 3448973) B3448973
theorem B3065753 : Blo 2043435 3065753 := bstep (se 2 (by rfl) ⟨1149657, by rfl⟩ : syracuseStep 3065753 = 2299315) B2299315
theorem B2043835 : Blo 2043435 2043835 := bstep (se 1 (by rfl) ⟨1532876, by rfl⟩ : syracuseStep 2043835 = 3065753) B3065753
theorem B7366133 : Blo 2043435 7366133 := bbase (se 5 (by rfl) ⟨345287, by rfl⟩ : syracuseStep 7366133 = 690575) (by norm_num)
theorem B4910755 : Blo 2043435 4910755 := bstep (se 1 (by rfl) ⟨3683066, by rfl⟩ : syracuseStep 4910755 = 7366133) B7366133
theorem B6547673 : Blo 2043435 6547673 := bstep (se 2 (by rfl) ⟨2455377, by rfl⟩ : syracuseStep 6547673 = 4910755) B4910755
theorem B17460461 : Blo 2043435 17460461 := bstep (se 3 (by rfl) ⟨3273836, by rfl⟩ : syracuseStep 17460461 = 6547673) B6547673
theorem B11640307 : Blo 2043435 11640307 := bstep (se 1 (by rfl) ⟨8730230, by rfl⟩ : syracuseStep 11640307 = 17460461) B17460461
theorem B15520409 : Blo 2043435 15520409 := bstep (se 2 (by rfl) ⟨5820153, by rfl⟩ : syracuseStep 15520409 = 11640307) B11640307
theorem B10346939 : Blo 2043435 10346939 := bstep (se 1 (by rfl) ⟨7760204, by rfl⟩ : syracuseStep 10346939 = 15520409) B15520409
theorem B6897959 : Blo 2043435 6897959 := bstep (se 1 (by rfl) ⟨5173469, by rfl⟩ : syracuseStep 6897959 = 10346939) B10346939
theorem B4598639 : Blo 2043435 4598639 := bstep (se 1 (by rfl) ⟨3448979, by rfl⟩ : syracuseStep 4598639 = 6897959) B6897959
theorem B3065759 : Blo 2043435 3065759 := bstep (se 1 (by rfl) ⟨2299319, by rfl⟩ : syracuseStep 3065759 = 4598639) B4598639
theorem B2043839 : Blo 2043435 2043839 := bstep (se 1 (by rfl) ⟨1532879, by rfl⟩ : syracuseStep 2043839 = 3065759) B3065759
theorem B3065765 : Blo 2043435 3065765 := bbase (se 4 (by rfl) ⟨287415, by rfl⟩ : syracuseStep 3065765 = 574831) (by norm_num)
theorem B2043843 : Blo 2043435 2043843 := bstep (se 1 (by rfl) ⟨1532882, by rfl⟩ : syracuseStep 2043843 = 3065765) B3065765
theorem B2586745 : Blo 2043435 2586745 := bbase (se 2 (by rfl) ⟨970029, by rfl⟩ : syracuseStep 2586745 = 1940059) (by norm_num)
theorem B3448993 : Blo 2043435 3448993 := bstep (se 2 (by rfl) ⟨1293372, by rfl⟩ : syracuseStep 3448993 = 2586745) B2586745
theorem B4598657 : Blo 2043435 4598657 := bstep (se 2 (by rfl) ⟨1724496, by rfl⟩ : syracuseStep 4598657 = 3448993) B3448993
theorem B3065771 : Blo 2043435 3065771 := bstep (se 1 (by rfl) ⟨2299328, by rfl⟩ : syracuseStep 3065771 = 4598657) B4598657
theorem B2043847 : Blo 2043435 2043847 := bstep (se 1 (by rfl) ⟨1532885, by rfl⟩ : syracuseStep 2043847 = 3065771) B3065771
theorem B2299333 : Blo 2043435 2299333 := bbase (se 4 (by rfl) ⟨215562, by rfl⟩ : syracuseStep 2299333 = 431125) (by norm_num)
theorem B3065777 : Blo 2043435 3065777 := bstep (se 2 (by rfl) ⟨1149666, by rfl⟩ : syracuseStep 3065777 = 2299333) B2299333
theorem B2043851 : Blo 2043435 2043851 := bstep (se 1 (by rfl) ⟨1532888, by rfl⟩ : syracuseStep 2043851 = 3065777) B3065777
theorem B3880133 : Blo 2043435 3880133 := bbase (se 4 (by rfl) ⟨363762, by rfl⟩ : syracuseStep 3880133 = 727525) (by norm_num)
theorem B2586755 : Blo 2043435 2586755 := bstep (se 1 (by rfl) ⟨1940066, by rfl⟩ : syracuseStep 2586755 = 3880133) B3880133
theorem B6898013 : Blo 2043435 6898013 := bstep (se 3 (by rfl) ⟨1293377, by rfl⟩ : syracuseStep 6898013 = 2586755) B2586755
theorem B4598675 : Blo 2043435 4598675 := bstep (se 1 (by rfl) ⟨3449006, by rfl⟩ : syracuseStep 4598675 = 6898013) B6898013
theorem B3065783 : Blo 2043435 3065783 := bstep (se 1 (by rfl) ⟨2299337, by rfl⟩ : syracuseStep 3065783 = 4598675) B4598675
theorem B2043855 : Blo 2043435 2043855 := bstep (se 1 (by rfl) ⟨1532891, by rfl⟩ : syracuseStep 2043855 = 3065783) B3065783
theorem B3065789 : Blo 2043435 3065789 := bbase (se 3 (by rfl) ⟨574835, by rfl⟩ : syracuseStep 3065789 = 1149671) (by norm_num)
theorem B2043859 : Blo 2043435 2043859 := bstep (se 1 (by rfl) ⟨1532894, by rfl⟩ : syracuseStep 2043859 = 3065789) B3065789
theorem B4598693 : Blo 2043435 4598693 := bbase (se 4 (by rfl) ⟨431127, by rfl⟩ : syracuseStep 4598693 = 862255) (by norm_num)
theorem B3065795 : Blo 2043435 3065795 := bstep (se 1 (by rfl) ⟨2299346, by rfl⟩ : syracuseStep 3065795 = 4598693) B4598693
theorem B2043863 : Blo 2043435 2043863 := bstep (se 1 (by rfl) ⟨1532897, by rfl⟩ : syracuseStep 2043863 = 3065795) B3065795
theorem B5173541 : Blo 2043435 5173541 := bbase (se 4 (by rfl) ⟨485019, by rfl⟩ : syracuseStep 5173541 = 970039) (by norm_num)
theorem B3449027 : Blo 2043435 3449027 := bstep (se 1 (by rfl) ⟨2586770, by rfl⟩ : syracuseStep 3449027 = 5173541) B5173541
theorem B2299351 : Blo 2043435 2299351 := bstep (se 1 (by rfl) ⟨1724513, by rfl⟩ : syracuseStep 2299351 = 3449027) B3449027
theorem B3065801 : Blo 2043435 3065801 := bstep (se 2 (by rfl) ⟨1149675, by rfl⟩ : syracuseStep 3065801 = 2299351) B2299351
theorem B2043867 : Blo 2043435 2043867 := bstep (se 1 (by rfl) ⟨1532900, by rfl⟩ : syracuseStep 2043867 = 3065801) B3065801
theorem B5820245 : Blo 2043435 5820245 := bbase (se 9 (by rfl) ⟨17051, by rfl⟩ : syracuseStep 5820245 = 34103) (by norm_num)
theorem B3880163 : Blo 2043435 3880163 := bstep (se 1 (by rfl) ⟨2910122, by rfl⟩ : syracuseStep 3880163 = 5820245) B5820245
theorem B10347101 : Blo 2043435 10347101 := bstep (se 3 (by rfl) ⟨1940081, by rfl⟩ : syracuseStep 10347101 = 3880163) B3880163
theorem B6898067 : Blo 2043435 6898067 := bstep (se 1 (by rfl) ⟨5173550, by rfl⟩ : syracuseStep 6898067 = 10347101) B10347101
theorem B4598711 : Blo 2043435 4598711 := bstep (se 1 (by rfl) ⟨3449033, by rfl⟩ : syracuseStep 4598711 = 6898067) B6898067
theorem B3065807 : Blo 2043435 3065807 := bstep (se 1 (by rfl) ⟨2299355, by rfl⟩ : syracuseStep 3065807 = 4598711) B4598711
theorem B2043871 : Blo 2043435 2043871 := bstep (se 1 (by rfl) ⟨1532903, by rfl⟩ : syracuseStep 2043871 = 3065807) B3065807
theorem B3065813 : Blo 2043435 3065813 := bbase (se 7 (by rfl) ⟨35927, by rfl⟩ : syracuseStep 3065813 = 71855) (by norm_num)
theorem B2043875 : Blo 2043435 2043875 := bstep (se 1 (by rfl) ⟨1532906, by rfl⟩ : syracuseStep 2043875 = 3065813) B3065813
theorem B7760357 : Blo 2043435 7760357 := bbase (se 4 (by rfl) ⟨727533, by rfl⟩ : syracuseStep 7760357 = 1455067) (by norm_num)
theorem B5173571 : Blo 2043435 5173571 := bstep (se 1 (by rfl) ⟨3880178, by rfl⟩ : syracuseStep 5173571 = 7760357) B7760357
theorem B3449047 : Blo 2043435 3449047 := bstep (se 1 (by rfl) ⟨2586785, by rfl⟩ : syracuseStep 3449047 = 5173571) B5173571
theorem B4598729 : Blo 2043435 4598729 := bstep (se 2 (by rfl) ⟨1724523, by rfl⟩ : syracuseStep 4598729 = 3449047) B3449047
theorem B3065819 : Blo 2043435 3065819 := bstep (se 1 (by rfl) ⟨2299364, by rfl⟩ : syracuseStep 3065819 = 4598729) B4598729
theorem B2043879 : Blo 2043435 2043879 := bstep (se 1 (by rfl) ⟨1532909, by rfl⟩ : syracuseStep 2043879 = 3065819) B3065819
theorem B2299369 : Blo 2043435 2299369 := bbase (se 2 (by rfl) ⟨862263, by rfl⟩ : syracuseStep 2299369 = 1724527) (by norm_num)
theorem B3065825 : Blo 2043435 3065825 := bstep (se 2 (by rfl) ⟨1149684, by rfl⟩ : syracuseStep 3065825 = 2299369) B2299369
theorem B2043883 : Blo 2043435 2043883 := bstep (se 1 (by rfl) ⟨1532912, by rfl⟩ : syracuseStep 2043883 = 3065825) B3065825
theorem B2182609 : Blo 2043435 2182609 := bbase (se 2 (by rfl) ⟨818478, by rfl⟩ : syracuseStep 2182609 = 1636957) (by norm_num)
theorem B11640581 : Blo 2043435 11640581 := bstep (se 4 (by rfl) ⟨1091304, by rfl⟩ : syracuseStep 11640581 = 2182609) B2182609
theorem B7760387 : Blo 2043435 7760387 := bstep (se 1 (by rfl) ⟨5820290, by rfl⟩ : syracuseStep 7760387 = 11640581) B11640581
theorem B5173591 : Blo 2043435 5173591 := bstep (se 1 (by rfl) ⟨3880193, by rfl⟩ : syracuseStep 5173591 = 7760387) B7760387
theorem B6898121 : Blo 2043435 6898121 := bstep (se 2 (by rfl) ⟨2586795, by rfl⟩ : syracuseStep 6898121 = 5173591) B5173591
theorem B4598747 : Blo 2043435 4598747 := bstep (se 1 (by rfl) ⟨3449060, by rfl⟩ : syracuseStep 4598747 = 6898121) B6898121
theorem B3065831 : Blo 2043435 3065831 := bstep (se 1 (by rfl) ⟨2299373, by rfl⟩ : syracuseStep 3065831 = 4598747) B4598747
theorem B2043887 : Blo 2043435 2043887 := bstep (se 1 (by rfl) ⟨1532915, by rfl⟩ : syracuseStep 2043887 = 3065831) B3065831
theorem B3065837 : Blo 2043435 3065837 := bbase (se 3 (by rfl) ⟨574844, by rfl⟩ : syracuseStep 3065837 = 1149689) (by norm_num)
theorem B2043891 : Blo 2043435 2043891 := bstep (se 1 (by rfl) ⟨1532918, by rfl⟩ : syracuseStep 2043891 = 3065837) B3065837
theorem B4598765 : Blo 2043435 4598765 := bbase (se 3 (by rfl) ⟨862268, by rfl⟩ : syracuseStep 4598765 = 1724537) (by norm_num)
theorem B3065843 : Blo 2043435 3065843 := bstep (se 1 (by rfl) ⟨2299382, by rfl⟩ : syracuseStep 3065843 = 4598765) B4598765
theorem B2043895 : Blo 2043435 2043895 := bstep (se 1 (by rfl) ⟨1532921, by rfl⟩ : syracuseStep 2043895 = 3065843) B3065843
theorem B4365245 : Blo 2043435 4365245 := bbase (se 3 (by rfl) ⟨818483, by rfl⟩ : syracuseStep 4365245 = 1636967) (by norm_num)
theorem B2910163 : Blo 2043435 2910163 := bstep (se 1 (by rfl) ⟨2182622, by rfl⟩ : syracuseStep 2910163 = 4365245) B4365245
theorem B3880217 : Blo 2043435 3880217 := bstep (se 2 (by rfl) ⟨1455081, by rfl⟩ : syracuseStep 3880217 = 2910163) B2910163
theorem B2586811 : Blo 2043435 2586811 := bstep (se 1 (by rfl) ⟨1940108, by rfl⟩ : syracuseStep 2586811 = 3880217) B3880217
theorem B3449081 : Blo 2043435 3449081 := bstep (se 2 (by rfl) ⟨1293405, by rfl⟩ : syracuseStep 3449081 = 2586811) B2586811
theorem B2299387 : Blo 2043435 2299387 := bstep (se 1 (by rfl) ⟨1724540, by rfl⟩ : syracuseStep 2299387 = 3449081) B3449081
theorem B3065849 : Blo 2043435 3065849 := bstep (se 2 (by rfl) ⟨1149693, by rfl⟩ : syracuseStep 3065849 = 2299387) B2299387
theorem B2043899 : Blo 2043435 2043899 := bstep (se 1 (by rfl) ⟨1532924, by rfl⟩ : syracuseStep 2043899 = 3065849) B3065849
theorem B7184389 : Blo 2043435 7184389 := bbase (se 4 (by rfl) ⟨673536, by rfl⟩ : syracuseStep 7184389 = 1347073) (by norm_num)
theorem B9579185 : Blo 2043435 9579185 := bstep (se 2 (by rfl) ⟨3592194, by rfl⟩ : syracuseStep 9579185 = 7184389) B7184389
theorem B6386123 : Blo 2043435 6386123 := bstep (se 1 (by rfl) ⟨4789592, by rfl⟩ : syracuseStep 6386123 = 9579185) B9579185
theorem B4257415 : Blo 2043435 4257415 := bstep (se 1 (by rfl) ⟨3193061, by rfl⟩ : syracuseStep 4257415 = 6386123) B6386123
theorem B5676553 : Blo 2043435 5676553 := bstep (se 2 (by rfl) ⟨2128707, by rfl⟩ : syracuseStep 5676553 = 4257415) B4257415
theorem B30274949 : Blo 2043435 30274949 := bstep (se 4 (by rfl) ⟨2838276, by rfl⟩ : syracuseStep 30274949 = 5676553) B5676553
theorem B20183299 : Blo 2043435 20183299 := bstep (se 1 (by rfl) ⟨15137474, by rfl⟩ : syracuseStep 20183299 = 30274949) B30274949
theorem B107644261 : Blo 2043435 107644261 := bstep (se 4 (by rfl) ⟨10091649, by rfl⟩ : syracuseStep 107644261 = 20183299) B20183299
theorem B143525681 : Blo 2043435 143525681 := bstep (se 2 (by rfl) ⟨53822130, by rfl⟩ : syracuseStep 143525681 = 107644261) B107644261
theorem B95683787 : Blo 2043435 95683787 := bstep (se 1 (by rfl) ⟨71762840, by rfl⟩ : syracuseStep 95683787 = 143525681) B143525681
theorem B63789191 : Blo 2043435 63789191 := bstep (se 1 (by rfl) ⟨47841893, by rfl⟩ : syracuseStep 63789191 = 95683787) B95683787
theorem B42526127 : Blo 2043435 42526127 := bstep (se 1 (by rfl) ⟨31894595, by rfl⟩ : syracuseStep 42526127 = 63789191) B63789191
theorem B28350751 : Blo 2043435 28350751 := bstep (se 1 (by rfl) ⟨21263063, by rfl⟩ : syracuseStep 28350751 = 42526127) B42526127
theorem B37801001 : Blo 2043435 37801001 := bstep (se 2 (by rfl) ⟨14175375, by rfl⟩ : syracuseStep 37801001 = 28350751) B28350751
theorem B25200667 : Blo 2043435 25200667 := bstep (se 1 (by rfl) ⟨18900500, by rfl⟩ : syracuseStep 25200667 = 37801001) B37801001
theorem B33600889 : Blo 2043435 33600889 := bstep (se 2 (by rfl) ⟨12600333, by rfl⟩ : syracuseStep 33600889 = 25200667) B25200667
theorem B44801185 : Blo 2043435 44801185 := bstep (se 2 (by rfl) ⟨16800444, by rfl⟩ : syracuseStep 44801185 = 33600889) B33600889
theorem B59734913 : Blo 2043435 59734913 := bstep (se 2 (by rfl) ⟨22400592, by rfl⟩ : syracuseStep 59734913 = 44801185) B44801185
theorem B637172405 : Blo 2043435 637172405 := bstep (se 5 (by rfl) ⟨29867456, by rfl⟩ : syracuseStep 637172405 = 59734913) B59734913
theorem B424781603 : Blo 2043435 424781603 := bstep (se 1 (by rfl) ⟨318586202, by rfl⟩ : syracuseStep 424781603 = 637172405) B637172405
theorem B283187735 : Blo 2043435 283187735 := bstep (se 1 (by rfl) ⟨212390801, by rfl⟩ : syracuseStep 283187735 = 424781603) B424781603
theorem B188791823 : Blo 2043435 188791823 := bstep (se 1 (by rfl) ⟨141593867, by rfl⟩ : syracuseStep 188791823 = 283187735) B283187735
theorem B125861215 : Blo 2043435 125861215 := bstep (se 1 (by rfl) ⟨94395911, by rfl⟩ : syracuseStep 125861215 = 188791823) B188791823
theorem B167814953 : Blo 2043435 167814953 := bstep (se 2 (by rfl) ⟨62930607, by rfl⟩ : syracuseStep 167814953 = 125861215) B125861215
theorem B111876635 : Blo 2043435 111876635 := bstep (se 1 (by rfl) ⟨83907476, by rfl⟩ : syracuseStep 111876635 = 167814953) B167814953
theorem B74584423 : Blo 2043435 74584423 := bstep (se 1 (by rfl) ⟨55938317, by rfl⟩ : syracuseStep 74584423 = 111876635) B111876635
theorem B99445897 : Blo 2043435 99445897 := bstep (se 2 (by rfl) ⟨37292211, by rfl⟩ : syracuseStep 99445897 = 74584423) B74584423
theorem B132594529 : Blo 2043435 132594529 := bstep (se 2 (by rfl) ⟨49722948, by rfl⟩ : syracuseStep 132594529 = 99445897) B99445897
theorem B176792705 : Blo 2043435 176792705 := bstep (se 2 (by rfl) ⟨66297264, by rfl⟩ : syracuseStep 176792705 = 132594529) B132594529
theorem B117861803 : Blo 2043435 117861803 := bstep (se 1 (by rfl) ⟨88396352, by rfl⟩ : syracuseStep 117861803 = 176792705) B176792705
theorem B78574535 : Blo 2043435 78574535 := bstep (se 1 (by rfl) ⟨58930901, by rfl⟩ : syracuseStep 78574535 = 117861803) B117861803
theorem B52383023 : Blo 2043435 52383023 := bstep (se 1 (by rfl) ⟨39287267, by rfl⟩ : syracuseStep 52383023 = 78574535) B78574535
theorem B34922015 : Blo 2043435 34922015 := bstep (se 1 (by rfl) ⟨26191511, by rfl⟩ : syracuseStep 34922015 = 52383023) B52383023
theorem B23281343 : Blo 2043435 23281343 := bstep (se 1 (by rfl) ⟨17461007, by rfl⟩ : syracuseStep 23281343 = 34922015) B34922015
theorem B15520895 : Blo 2043435 15520895 := bstep (se 1 (by rfl) ⟨11640671, by rfl⟩ : syracuseStep 15520895 = 23281343) B23281343
theorem B10347263 : Blo 2043435 10347263 := bstep (se 1 (by rfl) ⟨7760447, by rfl⟩ : syracuseStep 10347263 = 15520895) B15520895
theorem B6898175 : Blo 2043435 6898175 := bstep (se 1 (by rfl) ⟨5173631, by rfl⟩ : syracuseStep 6898175 = 10347263) B10347263
theorem B4598783 : Blo 2043435 4598783 := bstep (se 1 (by rfl) ⟨3449087, by rfl⟩ : syracuseStep 4598783 = 6898175) B6898175
theorem B3065855 : Blo 2043435 3065855 := bstep (se 1 (by rfl) ⟨2299391, by rfl⟩ : syracuseStep 3065855 = 4598783) B4598783
theorem B2043903 : Blo 2043435 2043903 := bstep (se 1 (by rfl) ⟨1532927, by rfl⟩ : syracuseStep 2043903 = 3065855) B3065855
theorem B3065861 : Blo 2043435 3065861 := bbase (se 4 (by rfl) ⟨287424, by rfl⟩ : syracuseStep 3065861 = 574849) (by norm_num)
theorem B2043907 : Blo 2043435 2043907 := bstep (se 1 (by rfl) ⟨1532930, by rfl⟩ : syracuseStep 2043907 = 3065861) B3065861
theorem B3449101 : Blo 2043435 3449101 := bbase (se 3 (by rfl) ⟨646706, by rfl⟩ : syracuseStep 3449101 = 1293413) (by norm_num)
theorem B4598801 : Blo 2043435 4598801 := bstep (se 2 (by rfl) ⟨1724550, by rfl⟩ : syracuseStep 4598801 = 3449101) B3449101
theorem B3065867 : Blo 2043435 3065867 := bstep (se 1 (by rfl) ⟨2299400, by rfl⟩ : syracuseStep 3065867 = 4598801) B4598801
theorem B2043911 : Blo 2043435 2043911 := bstep (se 1 (by rfl) ⟨1532933, by rfl⟩ : syracuseStep 2043911 = 3065867) B3065867
theorem B2299405 : Blo 2043435 2299405 := bbase (se 3 (by rfl) ⟨431138, by rfl⟩ : syracuseStep 2299405 = 862277) (by norm_num)
theorem B3065873 : Blo 2043435 3065873 := bstep (se 2 (by rfl) ⟨1149702, by rfl⟩ : syracuseStep 3065873 = 2299405) B2299405
theorem B2043915 : Blo 2043435 2043915 := bstep (se 1 (by rfl) ⟨1532936, by rfl⟩ : syracuseStep 2043915 = 3065873) B3065873
theorem B6898229 : Blo 2043435 6898229 := bbase (se 5 (by rfl) ⟨323354, by rfl⟩ : syracuseStep 6898229 = 646709) (by norm_num)
theorem B4598819 : Blo 2043435 4598819 := bstep (se 1 (by rfl) ⟨3449114, by rfl⟩ : syracuseStep 4598819 = 6898229) B6898229
theorem B3065879 : Blo 2043435 3065879 := bstep (se 1 (by rfl) ⟨2299409, by rfl⟩ : syracuseStep 3065879 = 4598819) B4598819
theorem B2043919 : Blo 2043435 2043919 := bstep (se 1 (by rfl) ⟨1532939, by rfl⟩ : syracuseStep 2043919 = 3065879) B3065879
theorem B3065885 : Blo 2043435 3065885 := bbase (se 3 (by rfl) ⟨574853, by rfl⟩ : syracuseStep 3065885 = 1149707) (by norm_num)
theorem B2043923 : Blo 2043435 2043923 := bstep (se 1 (by rfl) ⟨1532942, by rfl⟩ : syracuseStep 2043923 = 3065885) B3065885
theorem B4598837 : Blo 2043435 4598837 := bbase (se 5 (by rfl) ⟨215570, by rfl⟩ : syracuseStep 4598837 = 431141) (by norm_num)
theorem B3065891 : Blo 2043435 3065891 := bstep (se 1 (by rfl) ⟨2299418, by rfl⟩ : syracuseStep 3065891 = 4598837) B4598837
theorem B2043927 : Blo 2043435 2043927 := bstep (se 1 (by rfl) ⟨1532945, by rfl⟩ : syracuseStep 2043927 = 3065891) B3065891
theorem B2330797 : Blo 2043435 2330797 := bbase (se 3 (by rfl) ⟨437024, by rfl⟩ : syracuseStep 2330797 = 874049) (by norm_num)
theorem B3107729 : Blo 2043435 3107729 := bstep (se 2 (by rfl) ⟨1165398, by rfl⟩ : syracuseStep 3107729 = 2330797) B2330797
theorem B2071819 : Blo 2043435 2071819 := bstep (se 1 (by rfl) ⟨1553864, by rfl⟩ : syracuseStep 2071819 = 3107729) B3107729
theorem B2762425 : Blo 2043435 2762425 := bstep (se 2 (by rfl) ⟨1035909, by rfl⟩ : syracuseStep 2762425 = 2071819) B2071819
theorem B3683233 : Blo 2043435 3683233 := bstep (se 2 (by rfl) ⟨1381212, by rfl⟩ : syracuseStep 3683233 = 2762425) B2762425
theorem B4910977 : Blo 2043435 4910977 := bstep (se 2 (by rfl) ⟨1841616, by rfl⟩ : syracuseStep 4910977 = 3683233) B3683233
theorem B6547969 : Blo 2043435 6547969 := bstep (se 2 (by rfl) ⟨2455488, by rfl⟩ : syracuseStep 6547969 = 4910977) B4910977
theorem B8730625 : Blo 2043435 8730625 := bstep (se 2 (by rfl) ⟨3273984, by rfl⟩ : syracuseStep 8730625 = 6547969) B6547969
theorem B11640833 : Blo 2043435 11640833 := bstep (se 2 (by rfl) ⟨4365312, by rfl⟩ : syracuseStep 11640833 = 8730625) B8730625
theorem B7760555 : Blo 2043435 7760555 := bstep (se 1 (by rfl) ⟨5820416, by rfl⟩ : syracuseStep 7760555 = 11640833) B11640833
theorem B5173703 : Blo 2043435 5173703 := bstep (se 1 (by rfl) ⟨3880277, by rfl⟩ : syracuseStep 5173703 = 7760555) B7760555
theorem B3449135 : Blo 2043435 3449135 := bstep (se 1 (by rfl) ⟨2586851, by rfl⟩ : syracuseStep 3449135 = 5173703) B5173703
theorem B2299423 : Blo 2043435 2299423 := bstep (se 1 (by rfl) ⟨1724567, by rfl⟩ : syracuseStep 2299423 = 3449135) B3449135
theorem B3065897 : Blo 2043435 3065897 := bstep (se 2 (by rfl) ⟨1149711, by rfl⟩ : syracuseStep 3065897 = 2299423) B2299423
theorem B2043931 : Blo 2043435 2043931 := bstep (se 1 (by rfl) ⟨1532948, by rfl⟩ : syracuseStep 2043931 = 3065897) B3065897
theorem B2455493 : Blo 2043435 2455493 := bbase (se 4 (by rfl) ⟨230202, by rfl⟩ : syracuseStep 2455493 = 460405) (by norm_num)
theorem B6547981 : Blo 2043435 6547981 := bstep (se 3 (by rfl) ⟨1227746, by rfl⟩ : syracuseStep 6547981 = 2455493) B2455493
theorem B8730641 : Blo 2043435 8730641 := bstep (se 2 (by rfl) ⟨3273990, by rfl⟩ : syracuseStep 8730641 = 6547981) B6547981
theorem B5820427 : Blo 2043435 5820427 := bstep (se 1 (by rfl) ⟨4365320, by rfl⟩ : syracuseStep 5820427 = 8730641) B8730641
theorem B7760569 : Blo 2043435 7760569 := bstep (se 2 (by rfl) ⟨2910213, by rfl⟩ : syracuseStep 7760569 = 5820427) B5820427
theorem B10347425 : Blo 2043435 10347425 := bstep (se 2 (by rfl) ⟨3880284, by rfl⟩ : syracuseStep 10347425 = 7760569) B7760569
theorem B6898283 : Blo 2043435 6898283 := bstep (se 1 (by rfl) ⟨5173712, by rfl⟩ : syracuseStep 6898283 = 10347425) B10347425
theorem B4598855 : Blo 2043435 4598855 := bstep (se 1 (by rfl) ⟨3449141, by rfl⟩ : syracuseStep 4598855 = 6898283) B6898283
theorem B3065903 : Blo 2043435 3065903 := bstep (se 1 (by rfl) ⟨2299427, by rfl⟩ : syracuseStep 3065903 = 4598855) B4598855
theorem B2043935 : Blo 2043435 2043935 := bstep (se 1 (by rfl) ⟨1532951, by rfl⟩ : syracuseStep 2043935 = 3065903) B3065903
theorem B3065909 : Blo 2043435 3065909 := bbase (se 5 (by rfl) ⟨143714, by rfl⟩ : syracuseStep 3065909 = 287429) (by norm_num)
theorem B2043939 : Blo 2043435 2043939 := bstep (se 1 (by rfl) ⟨1532954, by rfl⟩ : syracuseStep 2043939 = 3065909) B3065909
theorem B5173733 : Blo 2043435 5173733 := bbase (se 4 (by rfl) ⟨485037, by rfl⟩ : syracuseStep 5173733 = 970075) (by norm_num)
theorem B3449155 : Blo 2043435 3449155 := bstep (se 1 (by rfl) ⟨2586866, by rfl⟩ : syracuseStep 3449155 = 5173733) B5173733
theorem B4598873 : Blo 2043435 4598873 := bstep (se 2 (by rfl) ⟨1724577, by rfl⟩ : syracuseStep 4598873 = 3449155) B3449155
theorem B3065915 : Blo 2043435 3065915 := bstep (se 1 (by rfl) ⟨2299436, by rfl⟩ : syracuseStep 3065915 = 4598873) B4598873
theorem B2043943 : Blo 2043435 2043943 := bstep (se 1 (by rfl) ⟨1532957, by rfl⟩ : syracuseStep 2043943 = 3065915) B3065915
theorem B2299441 : Blo 2043435 2299441 := bbase (se 2 (by rfl) ⟨862290, by rfl⟩ : syracuseStep 2299441 = 1724581) (by norm_num)
theorem B3065921 : Blo 2043435 3065921 := bstep (se 2 (by rfl) ⟨1149720, by rfl⟩ : syracuseStep 3065921 = 2299441) B2299441
theorem B2043947 : Blo 2043435 2043947 := bstep (se 1 (by rfl) ⟨1532960, by rfl⟩ : syracuseStep 2043947 = 3065921) B3065921
theorem B3683269 : Blo 2043435 3683269 := bbase (se 4 (by rfl) ⟨345306, by rfl⟩ : syracuseStep 3683269 = 690613) (by norm_num)
theorem B4911025 : Blo 2043435 4911025 := bstep (se 2 (by rfl) ⟨1841634, by rfl⟩ : syracuseStep 4911025 = 3683269) B3683269
theorem B6548033 : Blo 2043435 6548033 := bstep (se 2 (by rfl) ⟨2455512, by rfl⟩ : syracuseStep 6548033 = 4911025) B4911025
theorem B4365355 : Blo 2043435 4365355 := bstep (se 1 (by rfl) ⟨3274016, by rfl⟩ : syracuseStep 4365355 = 6548033) B6548033
theorem B5820473 : Blo 2043435 5820473 := bstep (se 2 (by rfl) ⟨2182677, by rfl⟩ : syracuseStep 5820473 = 4365355) B4365355
theorem B3880315 : Blo 2043435 3880315 := bstep (se 1 (by rfl) ⟨2910236, by rfl⟩ : syracuseStep 3880315 = 5820473) B5820473
theorem B5173753 : Blo 2043435 5173753 := bstep (se 2 (by rfl) ⟨1940157, by rfl⟩ : syracuseStep 5173753 = 3880315) B3880315
theorem B6898337 : Blo 2043435 6898337 := bstep (se 2 (by rfl) ⟨2586876, by rfl⟩ : syracuseStep 6898337 = 5173753) B5173753
theorem B4598891 : Blo 2043435 4598891 := bstep (se 1 (by rfl) ⟨3449168, by rfl⟩ : syracuseStep 4598891 = 6898337) B6898337
theorem B3065927 : Blo 2043435 3065927 := bstep (se 1 (by rfl) ⟨2299445, by rfl⟩ : syracuseStep 3065927 = 4598891) B4598891
theorem B2043951 : Blo 2043435 2043951 := bstep (se 1 (by rfl) ⟨1532963, by rfl⟩ : syracuseStep 2043951 = 3065927) B3065927
theorem B3065933 : Blo 2043435 3065933 := bbase (se 3 (by rfl) ⟨574862, by rfl⟩ : syracuseStep 3065933 = 1149725) (by norm_num)
theorem B2043955 : Blo 2043435 2043955 := bstep (se 1 (by rfl) ⟨1532966, by rfl⟩ : syracuseStep 2043955 = 3065933) B3065933
theorem B4598909 : Blo 2043435 4598909 := bbase (se 3 (by rfl) ⟨862295, by rfl⟩ : syracuseStep 4598909 = 1724591) (by norm_num)
theorem B3065939 : Blo 2043435 3065939 := bstep (se 1 (by rfl) ⟨2299454, by rfl⟩ : syracuseStep 3065939 = 4598909) B4598909
theorem B2043959 : Blo 2043435 2043959 := bstep (se 1 (by rfl) ⟨1532969, by rfl⟩ : syracuseStep 2043959 = 3065939) B3065939
theorem B3449189 : Blo 2043435 3449189 := bbase (se 4 (by rfl) ⟨323361, by rfl⟩ : syracuseStep 3449189 = 646723) (by norm_num)
theorem B2299459 : Blo 2043435 2299459 := bstep (se 1 (by rfl) ⟨1724594, by rfl⟩ : syracuseStep 2299459 = 3449189) B3449189
theorem B3065945 : Blo 2043435 3065945 := bstep (se 2 (by rfl) ⟨1149729, by rfl⟩ : syracuseStep 3065945 = 2299459) B2299459
theorem B2043963 : Blo 2043435 2043963 := bstep (se 1 (by rfl) ⟨1532972, by rfl⟩ : syracuseStep 2043963 = 3065945) B3065945
theorem B4365389 : Blo 2043435 4365389 := bbase (se 3 (by rfl) ⟨818510, by rfl⟩ : syracuseStep 4365389 = 1637021) (by norm_num)
theorem B2910259 : Blo 2043435 2910259 := bstep (se 1 (by rfl) ⟨2182694, by rfl⟩ : syracuseStep 2910259 = 4365389) B4365389
theorem B15521381 : Blo 2043435 15521381 := bstep (se 4 (by rfl) ⟨1455129, by rfl⟩ : syracuseStep 15521381 = 2910259) B2910259
theorem B10347587 : Blo 2043435 10347587 := bstep (se 1 (by rfl) ⟨7760690, by rfl⟩ : syracuseStep 10347587 = 15521381) B15521381
theorem B6898391 : Blo 2043435 6898391 := bstep (se 1 (by rfl) ⟨5173793, by rfl⟩ : syracuseStep 6898391 = 10347587) B10347587
theorem B4598927 : Blo 2043435 4598927 := bstep (se 1 (by rfl) ⟨3449195, by rfl⟩ : syracuseStep 4598927 = 6898391) B6898391
theorem B3065951 : Blo 2043435 3065951 := bstep (se 1 (by rfl) ⟨2299463, by rfl⟩ : syracuseStep 3065951 = 4598927) B4598927
theorem B2043967 : Blo 2043435 2043967 := bstep (se 1 (by rfl) ⟨1532975, by rfl⟩ : syracuseStep 2043967 = 3065951) B3065951
theorem B3065957 : Blo 2043435 3065957 := bbase (se 4 (by rfl) ⟨287433, by rfl⟩ : syracuseStep 3065957 = 574867) (by norm_num)
theorem B2043971 : Blo 2043435 2043971 := bstep (se 1 (by rfl) ⟨1532978, by rfl⟩ : syracuseStep 2043971 = 3065957) B3065957
theorem B4485341 : Blo 2043435 4485341 := bbase (se 3 (by rfl) ⟨841001, by rfl⟩ : syracuseStep 4485341 = 1682003) (by norm_num)
theorem B11960909 : Blo 2043435 11960909 := bstep (se 3 (by rfl) ⟨2242670, by rfl⟩ : syracuseStep 11960909 = 4485341) B4485341
theorem B7973939 : Blo 2043435 7973939 := bstep (se 1 (by rfl) ⟨5980454, by rfl⟩ : syracuseStep 7973939 = 11960909) B11960909
theorem B5315959 : Blo 2043435 5315959 := bstep (se 1 (by rfl) ⟨3986969, by rfl⟩ : syracuseStep 5315959 = 7973939) B7973939
theorem B7087945 : Blo 2043435 7087945 := bstep (se 2 (by rfl) ⟨2657979, by rfl⟩ : syracuseStep 7087945 = 5315959) B5315959
theorem B9450593 : Blo 2043435 9450593 := bstep (se 2 (by rfl) ⟨3543972, by rfl⟩ : syracuseStep 9450593 = 7087945) B7087945
theorem B6300395 : Blo 2043435 6300395 := bstep (se 1 (by rfl) ⟨4725296, by rfl⟩ : syracuseStep 6300395 = 9450593) B9450593
theorem B4200263 : Blo 2043435 4200263 := bstep (se 1 (by rfl) ⟨3150197, by rfl⟩ : syracuseStep 4200263 = 6300395) B6300395
theorem B2800175 : Blo 2043435 2800175 := bstep (se 1 (by rfl) ⟨2100131, by rfl⟩ : syracuseStep 2800175 = 4200263) B4200263
theorem B29868533 : Blo 2043435 29868533 := bstep (se 5 (by rfl) ⟨1400087, by rfl⟩ : syracuseStep 29868533 = 2800175) B2800175
theorem B19912355 : Blo 2043435 19912355 := bstep (se 1 (by rfl) ⟨14934266, by rfl⟩ : syracuseStep 19912355 = 29868533) B29868533
theorem B13274903 : Blo 2043435 13274903 := bstep (se 1 (by rfl) ⟨9956177, by rfl⟩ : syracuseStep 13274903 = 19912355) B19912355
theorem B8849935 : Blo 2043435 8849935 := bstep (se 1 (by rfl) ⟨6637451, by rfl⟩ : syracuseStep 8849935 = 13274903) B13274903
theorem B11799913 : Blo 2043435 11799913 := bstep (se 2 (by rfl) ⟨4424967, by rfl⟩ : syracuseStep 11799913 = 8849935) B8849935
theorem B15733217 : Blo 2043435 15733217 := bstep (se 2 (by rfl) ⟨5899956, by rfl⟩ : syracuseStep 15733217 = 11799913) B11799913
theorem B10488811 : Blo 2043435 10488811 := bstep (se 1 (by rfl) ⟨7866608, by rfl⟩ : syracuseStep 10488811 = 15733217) B15733217
theorem B13985081 : Blo 2043435 13985081 := bstep (se 2 (by rfl) ⟨5244405, by rfl⟩ : syracuseStep 13985081 = 10488811) B10488811
theorem B9323387 : Blo 2043435 9323387 := bstep (se 1 (by rfl) ⟨6992540, by rfl⟩ : syracuseStep 9323387 = 13985081) B13985081
theorem B6215591 : Blo 2043435 6215591 := bstep (se 1 (by rfl) ⟨4661693, by rfl⟩ : syracuseStep 6215591 = 9323387) B9323387
theorem B4143727 : Blo 2043435 4143727 := bstep (se 1 (by rfl) ⟨3107795, by rfl⟩ : syracuseStep 4143727 = 6215591) B6215591
theorem B22099877 : Blo 2043435 22099877 := bstep (se 4 (by rfl) ⟨2071863, by rfl⟩ : syracuseStep 22099877 = 4143727) B4143727
theorem B14733251 : Blo 2043435 14733251 := bstep (se 1 (by rfl) ⟨11049938, by rfl⟩ : syracuseStep 14733251 = 22099877) B22099877
theorem B9822167 : Blo 2043435 9822167 := bstep (se 1 (by rfl) ⟨7366625, by rfl⟩ : syracuseStep 9822167 = 14733251) B14733251
theorem B6548111 : Blo 2043435 6548111 := bstep (se 1 (by rfl) ⟨4911083, by rfl⟩ : syracuseStep 6548111 = 9822167) B9822167
theorem B4365407 : Blo 2043435 4365407 := bstep (se 1 (by rfl) ⟨3274055, by rfl⟩ : syracuseStep 4365407 = 6548111) B6548111
theorem B2910271 : Blo 2043435 2910271 := bstep (se 1 (by rfl) ⟨2182703, by rfl⟩ : syracuseStep 2910271 = 4365407) B4365407
theorem B3880361 : Blo 2043435 3880361 := bstep (se 2 (by rfl) ⟨1455135, by rfl⟩ : syracuseStep 3880361 = 2910271) B2910271
theorem B2586907 : Blo 2043435 2586907 := bstep (se 1 (by rfl) ⟨1940180, by rfl⟩ : syracuseStep 2586907 = 3880361) B3880361
theorem B3449209 : Blo 2043435 3449209 := bstep (se 2 (by rfl) ⟨1293453, by rfl⟩ : syracuseStep 3449209 = 2586907) B2586907
theorem B4598945 : Blo 2043435 4598945 := bstep (se 2 (by rfl) ⟨1724604, by rfl⟩ : syracuseStep 4598945 = 3449209) B3449209
theorem B3065963 : Blo 2043435 3065963 := bstep (se 1 (by rfl) ⟨2299472, by rfl⟩ : syracuseStep 3065963 = 4598945) B4598945
theorem B2043975 : Blo 2043435 2043975 := bstep (se 1 (by rfl) ⟨1532981, by rfl⟩ : syracuseStep 2043975 = 3065963) B3065963
theorem B2299477 : Blo 2043435 2299477 := bbase (se 8 (by rfl) ⟨13473, by rfl⟩ : syracuseStep 2299477 = 26947) (by norm_num)
theorem B3065969 : Blo 2043435 3065969 := bstep (se 2 (by rfl) ⟨1149738, by rfl⟩ : syracuseStep 3065969 = 2299477) B2299477
theorem B2043979 : Blo 2043435 2043979 := bstep (se 1 (by rfl) ⟨1532984, by rfl⟩ : syracuseStep 2043979 = 3065969) B3065969
theorem B2586917 : Blo 2043435 2586917 := bbase (se 4 (by rfl) ⟨242523, by rfl⟩ : syracuseStep 2586917 = 485047) (by norm_num)
theorem B6898445 : Blo 2043435 6898445 := bstep (se 3 (by rfl) ⟨1293458, by rfl⟩ : syracuseStep 6898445 = 2586917) B2586917
theorem B4598963 : Blo 2043435 4598963 := bstep (se 1 (by rfl) ⟨3449222, by rfl⟩ : syracuseStep 4598963 = 6898445) B6898445
theorem B3065975 : Blo 2043435 3065975 := bstep (se 1 (by rfl) ⟨2299481, by rfl⟩ : syracuseStep 3065975 = 4598963) B4598963
theorem B2043983 : Blo 2043435 2043983 := bstep (se 1 (by rfl) ⟨1532987, by rfl⟩ : syracuseStep 2043983 = 3065975) B3065975
theorem B3065981 : Blo 2043435 3065981 := bbase (se 3 (by rfl) ⟨574871, by rfl⟩ : syracuseStep 3065981 = 1149743) (by norm_num)
theorem B2043987 : Blo 2043435 2043987 := bstep (se 1 (by rfl) ⟨1532990, by rfl⟩ : syracuseStep 2043987 = 3065981) B3065981
theorem B4598981 : Blo 2043435 4598981 := bbase (se 4 (by rfl) ⟨431154, by rfl⟩ : syracuseStep 4598981 = 862309) (by norm_num)
theorem B3065987 : Blo 2043435 3065987 := bstep (se 1 (by rfl) ⟨2299490, by rfl⟩ : syracuseStep 3065987 = 4598981) B4598981
theorem B2043991 : Blo 2043435 2043991 := bstep (se 1 (by rfl) ⟨1532993, by rfl⟩ : syracuseStep 2043991 = 3065987) B3065987
theorem B29868821 : Blo 2043435 29868821 := bbase (se 6 (by rfl) ⟨700050, by rfl⟩ : syracuseStep 29868821 = 1400101) (by norm_num)
theorem B19912547 : Blo 2043435 19912547 := bstep (se 1 (by rfl) ⟨14934410, by rfl⟩ : syracuseStep 19912547 = 29868821) B29868821
theorem B13275031 : Blo 2043435 13275031 := bstep (se 1 (by rfl) ⟨9956273, by rfl⟩ : syracuseStep 13275031 = 19912547) B19912547
theorem B17700041 : Blo 2043435 17700041 := bstep (se 2 (by rfl) ⟨6637515, by rfl⟩ : syracuseStep 17700041 = 13275031) B13275031
theorem B11800027 : Blo 2043435 11800027 := bstep (se 1 (by rfl) ⟨8850020, by rfl⟩ : syracuseStep 11800027 = 17700041) B17700041
theorem B15733369 : Blo 2043435 15733369 := bstep (se 2 (by rfl) ⟨5900013, by rfl⟩ : syracuseStep 15733369 = 11800027) B11800027
theorem B20977825 : Blo 2043435 20977825 := bstep (se 2 (by rfl) ⟨7866684, by rfl⟩ : syracuseStep 20977825 = 15733369) B15733369
theorem B27970433 : Blo 2043435 27970433 := bstep (se 2 (by rfl) ⟨10488912, by rfl⟩ : syracuseStep 27970433 = 20977825) B20977825
theorem B18646955 : Blo 2043435 18646955 := bstep (se 1 (by rfl) ⟨13985216, by rfl⟩ : syracuseStep 18646955 = 27970433) B27970433
theorem B12431303 : Blo 2043435 12431303 := bstep (se 1 (by rfl) ⟨9323477, by rfl⟩ : syracuseStep 12431303 = 18646955) B18646955
theorem B8287535 : Blo 2043435 8287535 := bstep (se 1 (by rfl) ⟨6215651, by rfl⟩ : syracuseStep 8287535 = 12431303) B12431303
theorem B5525023 : Blo 2043435 5525023 := bstep (se 1 (by rfl) ⟨4143767, by rfl⟩ : syracuseStep 5525023 = 8287535) B8287535
theorem B7366697 : Blo 2043435 7366697 := bstep (se 2 (by rfl) ⟨2762511, by rfl⟩ : syracuseStep 7366697 = 5525023) B5525023
theorem B4911131 : Blo 2043435 4911131 := bstep (se 1 (by rfl) ⟨3683348, by rfl⟩ : syracuseStep 4911131 = 7366697) B7366697
theorem B13096349 : Blo 2043435 13096349 := bstep (se 3 (by rfl) ⟨2455565, by rfl⟩ : syracuseStep 13096349 = 4911131) B4911131
theorem B8730899 : Blo 2043435 8730899 := bstep (se 1 (by rfl) ⟨6548174, by rfl⟩ : syracuseStep 8730899 = 13096349) B13096349
theorem B5820599 : Blo 2043435 5820599 := bstep (se 1 (by rfl) ⟨4365449, by rfl⟩ : syracuseStep 5820599 = 8730899) B8730899
theorem B3880399 : Blo 2043435 3880399 := bstep (se 1 (by rfl) ⟨2910299, by rfl⟩ : syracuseStep 3880399 = 5820599) B5820599
theorem B5173865 : Blo 2043435 5173865 := bstep (se 2 (by rfl) ⟨1940199, by rfl⟩ : syracuseStep 5173865 = 3880399) B3880399
theorem B3449243 : Blo 2043435 3449243 := bstep (se 1 (by rfl) ⟨2586932, by rfl⟩ : syracuseStep 3449243 = 5173865) B5173865
theorem B2299495 : Blo 2043435 2299495 := bstep (se 1 (by rfl) ⟨1724621, by rfl⟩ : syracuseStep 2299495 = 3449243) B3449243
theorem B3065993 : Blo 2043435 3065993 := bstep (se 2 (by rfl) ⟨1149747, by rfl⟩ : syracuseStep 3065993 = 2299495) B2299495
theorem B2043995 : Blo 2043435 2043995 := bstep (se 1 (by rfl) ⟨1532996, by rfl⟩ : syracuseStep 2043995 = 3065993) B3065993
theorem B10347749 : Blo 2043435 10347749 := bbase (se 4 (by rfl) ⟨970101, by rfl⟩ : syracuseStep 10347749 = 1940203) (by norm_num)
theorem B6898499 : Blo 2043435 6898499 := bstep (se 1 (by rfl) ⟨5173874, by rfl⟩ : syracuseStep 6898499 = 10347749) B10347749
theorem B4598999 : Blo 2043435 4598999 := bstep (se 1 (by rfl) ⟨3449249, by rfl⟩ : syracuseStep 4598999 = 6898499) B6898499
theorem B3065999 : Blo 2043435 3065999 := bstep (se 1 (by rfl) ⟨2299499, by rfl⟩ : syracuseStep 3065999 = 4598999) B4598999
theorem B2043999 : Blo 2043435 2043999 := bstep (se 1 (by rfl) ⟨1532999, by rfl⟩ : syracuseStep 2043999 = 3065999) B3065999
theorem B3066005 : Blo 2043435 3066005 := bbase (se 6 (by rfl) ⟨71859, by rfl⟩ : syracuseStep 3066005 = 143719) (by norm_num)
theorem B2044003 : Blo 2043435 2044003 := bstep (se 1 (by rfl) ⟨1533002, by rfl⟩ : syracuseStep 2044003 = 3066005) B3066005
theorem B8730949 : Blo 2043435 8730949 := bbase (se 4 (by rfl) ⟨818526, by rfl⟩ : syracuseStep 8730949 = 1637053) (by norm_num)
theorem B11641265 : Blo 2043435 11641265 := bstep (se 2 (by rfl) ⟨4365474, by rfl⟩ : syracuseStep 11641265 = 8730949) B8730949
theorem B7760843 : Blo 2043435 7760843 := bstep (se 1 (by rfl) ⟨5820632, by rfl⟩ : syracuseStep 7760843 = 11641265) B11641265
theorem B5173895 : Blo 2043435 5173895 := bstep (se 1 (by rfl) ⟨3880421, by rfl⟩ : syracuseStep 5173895 = 7760843) B7760843
theorem B3449263 : Blo 2043435 3449263 := bstep (se 1 (by rfl) ⟨2586947, by rfl⟩ : syracuseStep 3449263 = 5173895) B5173895
theorem B4599017 : Blo 2043435 4599017 := bstep (se 2 (by rfl) ⟨1724631, by rfl⟩ : syracuseStep 4599017 = 3449263) B3449263
theorem B3066011 : Blo 2043435 3066011 := bstep (se 1 (by rfl) ⟨2299508, by rfl⟩ : syracuseStep 3066011 = 4599017) B4599017
theorem B2044007 : Blo 2043435 2044007 := bstep (se 1 (by rfl) ⟨1533005, by rfl⟩ : syracuseStep 2044007 = 3066011) B3066011
theorem B2299513 : Blo 2043435 2299513 := bbase (se 2 (by rfl) ⟨862317, by rfl⟩ : syracuseStep 2299513 = 1724635) (by norm_num)
theorem B3066017 : Blo 2043435 3066017 := bstep (se 2 (by rfl) ⟨1149756, by rfl⟩ : syracuseStep 3066017 = 2299513) B2299513
theorem B2044011 : Blo 2043435 2044011 := bstep (se 1 (by rfl) ⟨1533008, by rfl⟩ : syracuseStep 2044011 = 3066017) B3066017
theorem B13456277 : Blo 2043435 13456277 := bbase (se 6 (by rfl) ⟨315381, by rfl⟩ : syracuseStep 13456277 = 630763) (by norm_num)
theorem B8970851 : Blo 2043435 8970851 := bstep (se 1 (by rfl) ⟨6728138, by rfl⟩ : syracuseStep 8970851 = 13456277) B13456277
theorem B5980567 : Blo 2043435 5980567 := bstep (se 1 (by rfl) ⟨4485425, by rfl⟩ : syracuseStep 5980567 = 8970851) B8970851
theorem B7974089 : Blo 2043435 7974089 := bstep (se 2 (by rfl) ⟨2990283, by rfl⟩ : syracuseStep 7974089 = 5980567) B5980567
theorem B5316059 : Blo 2043435 5316059 := bstep (se 1 (by rfl) ⟨3987044, by rfl⟩ : syracuseStep 5316059 = 7974089) B7974089
theorem B3544039 : Blo 2043435 3544039 := bstep (se 1 (by rfl) ⟨2658029, by rfl⟩ : syracuseStep 3544039 = 5316059) B5316059
theorem B18901541 : Blo 2043435 18901541 := bstep (se 4 (by rfl) ⟨1772019, by rfl⟩ : syracuseStep 18901541 = 3544039) B3544039
theorem B12601027 : Blo 2043435 12601027 := bstep (se 1 (by rfl) ⟨9450770, by rfl⟩ : syracuseStep 12601027 = 18901541) B18901541
theorem B67205477 : Blo 2043435 67205477 := bstep (se 4 (by rfl) ⟨6300513, by rfl⟩ : syracuseStep 67205477 = 12601027) B12601027
theorem B179214605 : Blo 2043435 179214605 := bstep (se 3 (by rfl) ⟨33602738, by rfl⟩ : syracuseStep 179214605 = 67205477) B67205477
theorem B119476403 : Blo 2043435 119476403 := bstep (se 1 (by rfl) ⟨89607302, by rfl⟩ : syracuseStep 119476403 = 179214605) B179214605
theorem B79650935 : Blo 2043435 79650935 := bstep (se 1 (by rfl) ⟨59738201, by rfl⟩ : syracuseStep 79650935 = 119476403) B119476403
theorem B53100623 : Blo 2043435 53100623 := bstep (se 1 (by rfl) ⟨39825467, by rfl⟩ : syracuseStep 53100623 = 79650935) B79650935
theorem B35400415 : Blo 2043435 35400415 := bstep (se 1 (by rfl) ⟨26550311, by rfl⟩ : syracuseStep 35400415 = 53100623) B53100623
theorem B47200553 : Blo 2043435 47200553 := bstep (se 2 (by rfl) ⟨17700207, by rfl⟩ : syracuseStep 47200553 = 35400415) B35400415
theorem B31467035 : Blo 2043435 31467035 := bstep (se 1 (by rfl) ⟨23600276, by rfl⟩ : syracuseStep 31467035 = 47200553) B47200553
theorem B20978023 : Blo 2043435 20978023 := bstep (se 1 (by rfl) ⟨15733517, by rfl⟩ : syracuseStep 20978023 = 31467035) B31467035
theorem B27970697 : Blo 2043435 27970697 := bstep (se 2 (by rfl) ⟨10489011, by rfl⟩ : syracuseStep 27970697 = 20978023) B20978023
theorem B74588525 : Blo 2043435 74588525 := bstep (se 3 (by rfl) ⟨13985348, by rfl⟩ : syracuseStep 74588525 = 27970697) B27970697
theorem B49725683 : Blo 2043435 49725683 := bstep (se 1 (by rfl) ⟨37294262, by rfl⟩ : syracuseStep 49725683 = 74588525) B74588525
theorem B33150455 : Blo 2043435 33150455 := bstep (se 1 (by rfl) ⟨24862841, by rfl⟩ : syracuseStep 33150455 = 49725683) B49725683
theorem B22100303 : Blo 2043435 22100303 := bstep (se 1 (by rfl) ⟨16575227, by rfl⟩ : syracuseStep 22100303 = 33150455) B33150455
theorem B14733535 : Blo 2043435 14733535 := bstep (se 1 (by rfl) ⟨11050151, by rfl⟩ : syracuseStep 14733535 = 22100303) B22100303
theorem B19644713 : Blo 2043435 19644713 := bstep (se 2 (by rfl) ⟨7366767, by rfl⟩ : syracuseStep 19644713 = 14733535) B14733535
theorem B13096475 : Blo 2043435 13096475 := bstep (se 1 (by rfl) ⟨9822356, by rfl⟩ : syracuseStep 13096475 = 19644713) B19644713
theorem B8730983 : Blo 2043435 8730983 := bstep (se 1 (by rfl) ⟨6548237, by rfl⟩ : syracuseStep 8730983 = 13096475) B13096475
theorem B5820655 : Blo 2043435 5820655 := bstep (se 1 (by rfl) ⟨4365491, by rfl⟩ : syracuseStep 5820655 = 8730983) B8730983
theorem B7760873 : Blo 2043435 7760873 := bstep (se 2 (by rfl) ⟨2910327, by rfl⟩ : syracuseStep 7760873 = 5820655) B5820655
theorem B5173915 : Blo 2043435 5173915 := bstep (se 1 (by rfl) ⟨3880436, by rfl⟩ : syracuseStep 5173915 = 7760873) B7760873
theorem B6898553 : Blo 2043435 6898553 := bstep (se 2 (by rfl) ⟨2586957, by rfl⟩ : syracuseStep 6898553 = 5173915) B5173915
theorem B4599035 : Blo 2043435 4599035 := bstep (se 1 (by rfl) ⟨3449276, by rfl⟩ : syracuseStep 4599035 = 6898553) B6898553
theorem B3066023 : Blo 2043435 3066023 := bstep (se 1 (by rfl) ⟨2299517, by rfl⟩ : syracuseStep 3066023 = 4599035) B4599035
theorem B2044015 : Blo 2043435 2044015 := bstep (se 1 (by rfl) ⟨1533011, by rfl⟩ : syracuseStep 2044015 = 3066023) B3066023
theorem B3066029 : Blo 2043435 3066029 := bbase (se 3 (by rfl) ⟨574880, by rfl⟩ : syracuseStep 3066029 = 1149761) (by norm_num)
theorem B2044019 : Blo 2043435 2044019 := bstep (se 1 (by rfl) ⟨1533014, by rfl⟩ : syracuseStep 2044019 = 3066029) B3066029
theorem B4599053 : Blo 2043435 4599053 := bbase (se 3 (by rfl) ⟨862322, by rfl⟩ : syracuseStep 4599053 = 1724645) (by norm_num)
theorem B3066035 : Blo 2043435 3066035 := bstep (se 1 (by rfl) ⟨2299526, by rfl⟩ : syracuseStep 3066035 = 4599053) B4599053
theorem B2044023 : Blo 2043435 2044023 := bstep (se 1 (by rfl) ⟨1533017, by rfl⟩ : syracuseStep 2044023 = 3066035) B3066035
theorem B2586973 : Blo 2043435 2586973 := bbase (se 3 (by rfl) ⟨485057, by rfl⟩ : syracuseStep 2586973 = 970115) (by norm_num)
theorem B3449297 : Blo 2043435 3449297 := bstep (se 2 (by rfl) ⟨1293486, by rfl⟩ : syracuseStep 3449297 = 2586973) B2586973
theorem B2299531 : Blo 2043435 2299531 := bstep (se 1 (by rfl) ⟨1724648, by rfl⟩ : syracuseStep 2299531 = 3449297) B3449297
theorem B3066041 : Blo 2043435 3066041 := bstep (se 2 (by rfl) ⟨1149765, by rfl⟩ : syracuseStep 3066041 = 2299531) B2299531
theorem B2044027 : Blo 2043435 2044027 := bstep (se 1 (by rfl) ⟨1533020, by rfl⟩ : syracuseStep 2044027 = 3066041) B3066041
theorem B17462101 : Blo 2043435 17462101 := bbase (se 9 (by rfl) ⟨51158, by rfl⟩ : syracuseStep 17462101 = 102317) (by norm_num)
theorem B23282801 : Blo 2043435 23282801 := bstep (se 2 (by rfl) ⟨8731050, by rfl⟩ : syracuseStep 23282801 = 17462101) B17462101
theorem B15521867 : Blo 2043435 15521867 := bstep (se 1 (by rfl) ⟨11641400, by rfl⟩ : syracuseStep 15521867 = 23282801) B23282801
theorem B10347911 : Blo 2043435 10347911 := bstep (se 1 (by rfl) ⟨7760933, by rfl⟩ : syracuseStep 10347911 = 15521867) B15521867
theorem B6898607 : Blo 2043435 6898607 := bstep (se 1 (by rfl) ⟨5173955, by rfl⟩ : syracuseStep 6898607 = 10347911) B10347911
theorem B4599071 : Blo 2043435 4599071 := bstep (se 1 (by rfl) ⟨3449303, by rfl⟩ : syracuseStep 4599071 = 6898607) B6898607
theorem B3066047 : Blo 2043435 3066047 := bstep (se 1 (by rfl) ⟨2299535, by rfl⟩ : syracuseStep 3066047 = 4599071) B4599071
theorem B2044031 : Blo 2043435 2044031 := bstep (se 1 (by rfl) ⟨1533023, by rfl⟩ : syracuseStep 2044031 = 3066047) B3066047
theorem B3066053 : Blo 2043435 3066053 := bbase (se 4 (by rfl) ⟨287442, by rfl⟩ : syracuseStep 3066053 = 574885) (by norm_num)
theorem B2044035 : Blo 2043435 2044035 := bstep (se 1 (by rfl) ⟨1533026, by rfl⟩ : syracuseStep 2044035 = 3066053) B3066053
theorem B3449317 : Blo 2043435 3449317 := bbase (se 4 (by rfl) ⟨323373, by rfl⟩ : syracuseStep 3449317 = 646747) (by norm_num)
theorem B4599089 : Blo 2043435 4599089 := bstep (se 2 (by rfl) ⟨1724658, by rfl⟩ : syracuseStep 4599089 = 3449317) B3449317
theorem B3066059 : Blo 2043435 3066059 := bstep (se 1 (by rfl) ⟨2299544, by rfl⟩ : syracuseStep 3066059 = 4599089) B4599089
theorem B2044039 : Blo 2043435 2044039 := bstep (se 1 (by rfl) ⟨1533029, by rfl⟩ : syracuseStep 2044039 = 3066059) B3066059
theorem B2299549 : Blo 2043435 2299549 := bbase (se 3 (by rfl) ⟨431165, by rfl⟩ : syracuseStep 2299549 = 862331) (by norm_num)
theorem B3066065 : Blo 2043435 3066065 := bstep (se 2 (by rfl) ⟨1149774, by rfl⟩ : syracuseStep 3066065 = 2299549) B2299549
theorem B2044043 : Blo 2043435 2044043 := bstep (se 1 (by rfl) ⟨1533032, by rfl⟩ : syracuseStep 2044043 = 3066065) B3066065
theorem B6898661 : Blo 2043435 6898661 := bbase (se 4 (by rfl) ⟨646749, by rfl⟩ : syracuseStep 6898661 = 1293499) (by norm_num)
theorem B4599107 : Blo 2043435 4599107 := bstep (se 1 (by rfl) ⟨3449330, by rfl⟩ : syracuseStep 4599107 = 6898661) B6898661
theorem B3066071 : Blo 2043435 3066071 := bstep (se 1 (by rfl) ⟨2299553, by rfl⟩ : syracuseStep 3066071 = 4599107) B4599107
theorem B2044047 : Blo 2043435 2044047 := bstep (se 1 (by rfl) ⟨1533035, by rfl⟩ : syracuseStep 2044047 = 3066071) B3066071
theorem B3066077 : Blo 2043435 3066077 := bbase (se 3 (by rfl) ⟨574889, by rfl⟩ : syracuseStep 3066077 = 1149779) (by norm_num)
theorem B2044051 : Blo 2043435 2044051 := bstep (se 1 (by rfl) ⟨1533038, by rfl⟩ : syracuseStep 2044051 = 3066077) B3066077
theorem B4599125 : Blo 2043435 4599125 := bbase (se 11 (by rfl) ⟨3368, by rfl⟩ : syracuseStep 4599125 = 6737) (by norm_num)
theorem B3066083 : Blo 2043435 3066083 := bstep (se 1 (by rfl) ⟨2299562, by rfl⟩ : syracuseStep 3066083 = 4599125) B4599125
theorem B2044055 : Blo 2043435 2044055 := bstep (se 1 (by rfl) ⟨1533041, by rfl⟩ : syracuseStep 2044055 = 3066083) B3066083
theorem B2182793 : Blo 2043435 2182793 := bbase (se 2 (by rfl) ⟨818547, by rfl⟩ : syracuseStep 2182793 = 1637095) (by norm_num)
theorem B5820781 : Blo 2043435 5820781 := bstep (se 3 (by rfl) ⟨1091396, by rfl⟩ : syracuseStep 5820781 = 2182793) B2182793
theorem B7761041 : Blo 2043435 7761041 := bstep (se 2 (by rfl) ⟨2910390, by rfl⟩ : syracuseStep 7761041 = 5820781) B5820781
theorem B5174027 : Blo 2043435 5174027 := bstep (se 1 (by rfl) ⟨3880520, by rfl⟩ : syracuseStep 5174027 = 7761041) B7761041
theorem B3449351 : Blo 2043435 3449351 := bstep (se 1 (by rfl) ⟨2587013, by rfl⟩ : syracuseStep 3449351 = 5174027) B5174027
theorem B2299567 : Blo 2043435 2299567 := bstep (se 1 (by rfl) ⟨1724675, by rfl⟩ : syracuseStep 2299567 = 3449351) B3449351
theorem B3066089 : Blo 2043435 3066089 := bstep (se 2 (by rfl) ⟨1149783, by rfl⟩ : syracuseStep 3066089 = 2299567) B2299567
theorem B2044059 : Blo 2043435 2044059 := bstep (se 1 (by rfl) ⟨1533044, by rfl⟩ : syracuseStep 2044059 = 3066089) B3066089
theorem B6300661 : Blo 2043435 6300661 := bbase (se 5 (by rfl) ⟨295343, by rfl⟩ : syracuseStep 6300661 = 590687) (by norm_num)
theorem B8400881 : Blo 2043435 8400881 := bstep (se 2 (by rfl) ⟨3150330, by rfl⟩ : syracuseStep 8400881 = 6300661) B6300661
theorem B22402349 : Blo 2043435 22402349 := bstep (se 3 (by rfl) ⟨4200440, by rfl⟩ : syracuseStep 22402349 = 8400881) B8400881
theorem B14934899 : Blo 2043435 14934899 := bstep (se 1 (by rfl) ⟨11201174, by rfl⟩ : syracuseStep 14934899 = 22402349) B22402349
theorem B39826397 : Blo 2043435 39826397 := bstep (se 3 (by rfl) ⟨7467449, by rfl⟩ : syracuseStep 39826397 = 14934899) B14934899
theorem B26550931 : Blo 2043435 26550931 := bstep (se 1 (by rfl) ⟨19913198, by rfl⟩ : syracuseStep 26550931 = 39826397) B39826397
theorem B35401241 : Blo 2043435 35401241 := bstep (se 2 (by rfl) ⟨13275465, by rfl⟩ : syracuseStep 35401241 = 26550931) B26550931
theorem B23600827 : Blo 2043435 23600827 := bstep (se 1 (by rfl) ⟨17700620, by rfl⟩ : syracuseStep 23600827 = 35401241) B35401241
theorem B125871077 : Blo 2043435 125871077 := bstep (se 4 (by rfl) ⟨11800413, by rfl⟩ : syracuseStep 125871077 = 23600827) B23600827
theorem B83914051 : Blo 2043435 83914051 := bstep (se 1 (by rfl) ⟨62935538, by rfl⟩ : syracuseStep 83914051 = 125871077) B125871077
theorem B111885401 : Blo 2043435 111885401 := bstep (se 2 (by rfl) ⟨41957025, by rfl⟩ : syracuseStep 111885401 = 83914051) B83914051
theorem B74590267 : Blo 2043435 74590267 := bstep (se 1 (by rfl) ⟨55942700, by rfl⟩ : syracuseStep 74590267 = 111885401) B111885401
theorem B99453689 : Blo 2043435 99453689 := bstep (se 2 (by rfl) ⟨37295133, by rfl⟩ : syracuseStep 99453689 = 74590267) B74590267
theorem B66302459 : Blo 2043435 66302459 := bstep (se 1 (by rfl) ⟨49726844, by rfl⟩ : syracuseStep 66302459 = 99453689) B99453689
theorem B44201639 : Blo 2043435 44201639 := bstep (se 1 (by rfl) ⟨33151229, by rfl⟩ : syracuseStep 44201639 = 66302459) B66302459
theorem B29467759 : Blo 2043435 29467759 := bstep (se 1 (by rfl) ⟨22100819, by rfl⟩ : syracuseStep 29467759 = 44201639) B44201639
theorem B39290345 : Blo 2043435 39290345 := bstep (se 2 (by rfl) ⟨14733879, by rfl⟩ : syracuseStep 39290345 = 29467759) B29467759
theorem B26193563 : Blo 2043435 26193563 := bstep (se 1 (by rfl) ⟨19645172, by rfl⟩ : syracuseStep 26193563 = 39290345) B39290345
theorem B17462375 : Blo 2043435 17462375 := bstep (se 1 (by rfl) ⟨13096781, by rfl⟩ : syracuseStep 17462375 = 26193563) B26193563
theorem B11641583 : Blo 2043435 11641583 := bstep (se 1 (by rfl) ⟨8731187, by rfl⟩ : syracuseStep 11641583 = 17462375) B17462375
theorem B7761055 : Blo 2043435 7761055 := bstep (se 1 (by rfl) ⟨5820791, by rfl⟩ : syracuseStep 7761055 = 11641583) B11641583
theorem B10348073 : Blo 2043435 10348073 := bstep (se 2 (by rfl) ⟨3880527, by rfl⟩ : syracuseStep 10348073 = 7761055) B7761055
theorem B6898715 : Blo 2043435 6898715 := bstep (se 1 (by rfl) ⟨5174036, by rfl⟩ : syracuseStep 6898715 = 10348073) B10348073
theorem B4599143 : Blo 2043435 4599143 := bstep (se 1 (by rfl) ⟨3449357, by rfl⟩ : syracuseStep 4599143 = 6898715) B6898715
theorem B3066095 : Blo 2043435 3066095 := bstep (se 1 (by rfl) ⟨2299571, by rfl⟩ : syracuseStep 3066095 = 4599143) B4599143
theorem B2044063 : Blo 2043435 2044063 := bstep (se 1 (by rfl) ⟨1533047, by rfl⟩ : syracuseStep 2044063 = 3066095) B3066095
theorem B3066101 : Blo 2043435 3066101 := bbase (se 5 (by rfl) ⟨143723, by rfl⟩ : syracuseStep 3066101 = 287447) (by norm_num)
theorem B2044067 : Blo 2043435 2044067 := bstep (se 1 (by rfl) ⟨1533050, by rfl⟩ : syracuseStep 2044067 = 3066101) B3066101
theorem B3683485 : Blo 2043435 3683485 := bbase (se 3 (by rfl) ⟨690653, by rfl⟩ : syracuseStep 3683485 = 1381307) (by norm_num)
theorem B19645253 : Blo 2043435 19645253 := bstep (se 4 (by rfl) ⟨1841742, by rfl⟩ : syracuseStep 19645253 = 3683485) B3683485
theorem B13096835 : Blo 2043435 13096835 := bstep (se 1 (by rfl) ⟨9822626, by rfl⟩ : syracuseStep 13096835 = 19645253) B19645253
theorem B8731223 : Blo 2043435 8731223 := bstep (se 1 (by rfl) ⟨6548417, by rfl⟩ : syracuseStep 8731223 = 13096835) B13096835
theorem B5820815 : Blo 2043435 5820815 := bstep (se 1 (by rfl) ⟨4365611, by rfl⟩ : syracuseStep 5820815 = 8731223) B8731223
theorem B3880543 : Blo 2043435 3880543 := bstep (se 1 (by rfl) ⟨2910407, by rfl⟩ : syracuseStep 3880543 = 5820815) B5820815
theorem B5174057 : Blo 2043435 5174057 := bstep (se 2 (by rfl) ⟨1940271, by rfl⟩ : syracuseStep 5174057 = 3880543) B3880543
theorem B3449371 : Blo 2043435 3449371 := bstep (se 1 (by rfl) ⟨2587028, by rfl⟩ : syracuseStep 3449371 = 5174057) B5174057
theorem B4599161 : Blo 2043435 4599161 := bstep (se 2 (by rfl) ⟨1724685, by rfl⟩ : syracuseStep 4599161 = 3449371) B3449371
theorem B3066107 : Blo 2043435 3066107 := bstep (se 1 (by rfl) ⟨2299580, by rfl⟩ : syracuseStep 3066107 = 4599161) B4599161
theorem B2044071 : Blo 2043435 2044071 := bstep (se 1 (by rfl) ⟨1533053, by rfl⟩ : syracuseStep 2044071 = 3066107) B3066107
theorem B2299585 : Blo 2043435 2299585 := bbase (se 2 (by rfl) ⟨862344, by rfl⟩ : syracuseStep 2299585 = 1724689) (by norm_num)
theorem B3066113 : Blo 2043435 3066113 := bstep (se 2 (by rfl) ⟨1149792, by rfl⟩ : syracuseStep 3066113 = 2299585) B2299585
theorem B2044075 : Blo 2043435 2044075 := bstep (se 1 (by rfl) ⟨1533056, by rfl⟩ : syracuseStep 2044075 = 3066113) B3066113
theorem B5174077 : Blo 2043435 5174077 := bbase (se 3 (by rfl) ⟨970139, by rfl⟩ : syracuseStep 5174077 = 1940279) (by norm_num)
theorem B6898769 : Blo 2043435 6898769 := bstep (se 2 (by rfl) ⟨2587038, by rfl⟩ : syracuseStep 6898769 = 5174077) B5174077
theorem B4599179 : Blo 2043435 4599179 := bstep (se 1 (by rfl) ⟨3449384, by rfl⟩ : syracuseStep 4599179 = 6898769) B6898769
theorem B3066119 : Blo 2043435 3066119 := bstep (se 1 (by rfl) ⟨2299589, by rfl⟩ : syracuseStep 3066119 = 4599179) B4599179
theorem B2044079 : Blo 2043435 2044079 := bstep (se 1 (by rfl) ⟨1533059, by rfl⟩ : syracuseStep 2044079 = 3066119) B3066119
theorem B3066125 : Blo 2043435 3066125 := bbase (se 3 (by rfl) ⟨574898, by rfl⟩ : syracuseStep 3066125 = 1149797) (by norm_num)
theorem B2044083 : Blo 2043435 2044083 := bstep (se 1 (by rfl) ⟨1533062, by rfl⟩ : syracuseStep 2044083 = 3066125) B3066125
theorem B4599197 : Blo 2043435 4599197 := bbase (se 3 (by rfl) ⟨862349, by rfl⟩ : syracuseStep 4599197 = 1724699) (by norm_num)
theorem B3066131 : Blo 2043435 3066131 := bstep (se 1 (by rfl) ⟨2299598, by rfl⟩ : syracuseStep 3066131 = 4599197) B4599197
theorem B2044087 : Blo 2043435 2044087 := bstep (se 1 (by rfl) ⟨1533065, by rfl⟩ : syracuseStep 2044087 = 3066131) B3066131
theorem B3449405 : Blo 2043435 3449405 := bbase (se 3 (by rfl) ⟨646763, by rfl⟩ : syracuseStep 3449405 = 1293527) (by norm_num)
theorem B2299603 : Blo 2043435 2299603 := bstep (se 1 (by rfl) ⟨1724702, by rfl⟩ : syracuseStep 2299603 = 3449405) B3449405
theorem B3066137 : Blo 2043435 3066137 := bstep (se 2 (by rfl) ⟨1149801, by rfl⟩ : syracuseStep 3066137 = 2299603) B2299603
theorem B2044091 : Blo 2043435 2044091 := bstep (se 1 (by rfl) ⟨1533068, by rfl⟩ : syracuseStep 2044091 = 3066137) B3066137
theorem B2071985 : Blo 2043435 2071985 := bbase (se 2 (by rfl) ⟨776994, by rfl⟩ : syracuseStep 2071985 = 1553989) (by norm_num)
theorem B5525293 : Blo 2043435 5525293 := bstep (se 3 (by rfl) ⟨1035992, by rfl⟩ : syracuseStep 5525293 = 2071985) B2071985
theorem B7367057 : Blo 2043435 7367057 := bstep (se 2 (by rfl) ⟨2762646, by rfl⟩ : syracuseStep 7367057 = 5525293) B5525293
theorem B4911371 : Blo 2043435 4911371 := bstep (se 1 (by rfl) ⟨3683528, by rfl⟩ : syracuseStep 4911371 = 7367057) B7367057
theorem B3274247 : Blo 2043435 3274247 := bstep (se 1 (by rfl) ⟨2455685, by rfl⟩ : syracuseStep 3274247 = 4911371) B4911371
theorem B2182831 : Blo 2043435 2182831 := bstep (se 1 (by rfl) ⟨1637123, by rfl⟩ : syracuseStep 2182831 = 3274247) B3274247
theorem B11641765 : Blo 2043435 11641765 := bstep (se 4 (by rfl) ⟨1091415, by rfl⟩ : syracuseStep 11641765 = 2182831) B2182831
theorem B15522353 : Blo 2043435 15522353 := bstep (se 2 (by rfl) ⟨5820882, by rfl⟩ : syracuseStep 15522353 = 11641765) B11641765
theorem B10348235 : Blo 2043435 10348235 := bstep (se 1 (by rfl) ⟨7761176, by rfl⟩ : syracuseStep 10348235 = 15522353) B15522353
theorem B6898823 : Blo 2043435 6898823 := bstep (se 1 (by rfl) ⟨5174117, by rfl⟩ : syracuseStep 6898823 = 10348235) B10348235
theorem B4599215 : Blo 2043435 4599215 := bstep (se 1 (by rfl) ⟨3449411, by rfl⟩ : syracuseStep 4599215 = 6898823) B6898823
theorem B3066143 : Blo 2043435 3066143 := bstep (se 1 (by rfl) ⟨2299607, by rfl⟩ : syracuseStep 3066143 = 4599215) B4599215
theorem B2044095 : Blo 2043435 2044095 := bstep (se 1 (by rfl) ⟨1533071, by rfl⟩ : syracuseStep 2044095 = 3066143) B3066143
theorem B3066149 : Blo 2043435 3066149 := bbase (se 4 (by rfl) ⟨287451, by rfl⟩ : syracuseStep 3066149 = 574903) (by norm_num)
theorem B2044099 : Blo 2043435 2044099 := bstep (se 1 (by rfl) ⟨1533074, by rfl⟩ : syracuseStep 2044099 = 3066149) B3066149
theorem B2587069 : Blo 2043435 2587069 := bbase (se 3 (by rfl) ⟨485075, by rfl⟩ : syracuseStep 2587069 = 970151) (by norm_num)
theorem B3449425 : Blo 2043435 3449425 := bstep (se 2 (by rfl) ⟨1293534, by rfl⟩ : syracuseStep 3449425 = 2587069) B2587069
theorem B4599233 : Blo 2043435 4599233 := bstep (se 2 (by rfl) ⟨1724712, by rfl⟩ : syracuseStep 4599233 = 3449425) B3449425
theorem B3066155 : Blo 2043435 3066155 := bstep (se 1 (by rfl) ⟨2299616, by rfl⟩ : syracuseStep 3066155 = 4599233) B4599233
theorem B2044103 : Blo 2043435 2044103 := bstep (se 1 (by rfl) ⟨1533077, by rfl⟩ : syracuseStep 2044103 = 3066155) B3066155
theorem B2299621 : Blo 2043435 2299621 := bbase (se 4 (by rfl) ⟨215589, by rfl⟩ : syracuseStep 2299621 = 431179) (by norm_num)
theorem B3066161 : Blo 2043435 3066161 := bstep (se 2 (by rfl) ⟨1149810, by rfl⟩ : syracuseStep 3066161 = 2299621) B2299621
theorem B2044107 : Blo 2043435 2044107 := bstep (se 1 (by rfl) ⟨1533080, by rfl⟩ : syracuseStep 2044107 = 3066161) B3066161
theorem B2455705 : Blo 2043435 2455705 := bbase (se 2 (by rfl) ⟨920889, by rfl⟩ : syracuseStep 2455705 = 1841779) (by norm_num)
theorem B3274273 : Blo 2043435 3274273 := bstep (se 2 (by rfl) ⟨1227852, by rfl⟩ : syracuseStep 3274273 = 2455705) B2455705
theorem B4365697 : Blo 2043435 4365697 := bstep (se 2 (by rfl) ⟨1637136, by rfl⟩ : syracuseStep 4365697 = 3274273) B3274273
theorem B5820929 : Blo 2043435 5820929 := bstep (se 2 (by rfl) ⟨2182848, by rfl⟩ : syracuseStep 5820929 = 4365697) B4365697
theorem B3880619 : Blo 2043435 3880619 := bstep (se 1 (by rfl) ⟨2910464, by rfl⟩ : syracuseStep 3880619 = 5820929) B5820929
theorem B2587079 : Blo 2043435 2587079 := bstep (se 1 (by rfl) ⟨1940309, by rfl⟩ : syracuseStep 2587079 = 3880619) B3880619
theorem B6898877 : Blo 2043435 6898877 := bstep (se 3 (by rfl) ⟨1293539, by rfl⟩ : syracuseStep 6898877 = 2587079) B2587079
theorem B4599251 : Blo 2043435 4599251 := bstep (se 1 (by rfl) ⟨3449438, by rfl⟩ : syracuseStep 4599251 = 6898877) B6898877
theorem B3066167 : Blo 2043435 3066167 := bstep (se 1 (by rfl) ⟨2299625, by rfl⟩ : syracuseStep 3066167 = 4599251) B4599251
theorem B2044111 : Blo 2043435 2044111 := bstep (se 1 (by rfl) ⟨1533083, by rfl⟩ : syracuseStep 2044111 = 3066167) B3066167
theorem B3066173 : Blo 2043435 3066173 := bbase (se 3 (by rfl) ⟨574907, by rfl⟩ : syracuseStep 3066173 = 1149815) (by norm_num)
theorem B2044115 : Blo 2043435 2044115 := bstep (se 1 (by rfl) ⟨1533086, by rfl⟩ : syracuseStep 2044115 = 3066173) B3066173
theorem B4599269 : Blo 2043435 4599269 := bbase (se 4 (by rfl) ⟨431181, by rfl⟩ : syracuseStep 4599269 = 862363) (by norm_num)
theorem B3066179 : Blo 2043435 3066179 := bstep (se 1 (by rfl) ⟨2299634, by rfl⟩ : syracuseStep 3066179 = 4599269) B4599269
theorem B2044119 : Blo 2043435 2044119 := bstep (se 1 (by rfl) ⟨1533089, by rfl⟩ : syracuseStep 2044119 = 3066179) B3066179
theorem B5174189 : Blo 2043435 5174189 := bbase (se 3 (by rfl) ⟨970160, by rfl⟩ : syracuseStep 5174189 = 1940321) (by norm_num)
theorem B3449459 : Blo 2043435 3449459 := bstep (se 1 (by rfl) ⟨2587094, by rfl⟩ : syracuseStep 3449459 = 5174189) B5174189
theorem B2299639 : Blo 2043435 2299639 := bstep (se 1 (by rfl) ⟨1724729, by rfl⟩ : syracuseStep 2299639 = 3449459) B3449459
theorem B3066185 : Blo 2043435 3066185 := bstep (se 2 (by rfl) ⟨1149819, by rfl⟩ : syracuseStep 3066185 = 2299639) B2299639
theorem B2044123 : Blo 2043435 2044123 := bstep (se 1 (by rfl) ⟨1533092, by rfl⟩ : syracuseStep 2044123 = 3066185) B3066185
theorem B6548597 : Blo 2043435 6548597 := bbase (se 5 (by rfl) ⟨306965, by rfl⟩ : syracuseStep 6548597 = 613931) (by norm_num)
theorem B4365731 : Blo 2043435 4365731 := bstep (se 1 (by rfl) ⟨3274298, by rfl⟩ : syracuseStep 4365731 = 6548597) B6548597
theorem B2910487 : Blo 2043435 2910487 := bstep (se 1 (by rfl) ⟨2182865, by rfl⟩ : syracuseStep 2910487 = 4365731) B4365731
theorem B3880649 : Blo 2043435 3880649 := bstep (se 2 (by rfl) ⟨1455243, by rfl⟩ : syracuseStep 3880649 = 2910487) B2910487
theorem B10348397 : Blo 2043435 10348397 := bstep (se 3 (by rfl) ⟨1940324, by rfl⟩ : syracuseStep 10348397 = 3880649) B3880649
theorem B6898931 : Blo 2043435 6898931 := bstep (se 1 (by rfl) ⟨5174198, by rfl⟩ : syracuseStep 6898931 = 10348397) B10348397
theorem B4599287 : Blo 2043435 4599287 := bstep (se 1 (by rfl) ⟨3449465, by rfl⟩ : syracuseStep 4599287 = 6898931) B6898931
theorem B3066191 : Blo 2043435 3066191 := bstep (se 1 (by rfl) ⟨2299643, by rfl⟩ : syracuseStep 3066191 = 4599287) B4599287
theorem B2044127 : Blo 2043435 2044127 := bstep (se 1 (by rfl) ⟨1533095, by rfl⟩ : syracuseStep 2044127 = 3066191) B3066191
theorem B3066197 : Blo 2043435 3066197 := bbase (se 10 (by rfl) ⟨4491, by rfl⟩ : syracuseStep 3066197 = 8983) (by norm_num)
theorem B2044131 : Blo 2043435 2044131 := bstep (se 1 (by rfl) ⟨1533098, by rfl⟩ : syracuseStep 2044131 = 3066197) B3066197
theorem B5820997 : Blo 2043435 5820997 := bbase (se 4 (by rfl) ⟨545718, by rfl⟩ : syracuseStep 5820997 = 1091437) (by norm_num)
theorem B7761329 : Blo 2043435 7761329 := bstep (se 2 (by rfl) ⟨2910498, by rfl⟩ : syracuseStep 7761329 = 5820997) B5820997
theorem B5174219 : Blo 2043435 5174219 := bstep (se 1 (by rfl) ⟨3880664, by rfl⟩ : syracuseStep 5174219 = 7761329) B7761329
theorem B3449479 : Blo 2043435 3449479 := bstep (se 1 (by rfl) ⟨2587109, by rfl⟩ : syracuseStep 3449479 = 5174219) B5174219
theorem B4599305 : Blo 2043435 4599305 := bstep (se 2 (by rfl) ⟨1724739, by rfl⟩ : syracuseStep 4599305 = 3449479) B3449479
theorem B3066203 : Blo 2043435 3066203 := bstep (se 1 (by rfl) ⟨2299652, by rfl⟩ : syracuseStep 3066203 = 4599305) B4599305
theorem B2044135 : Blo 2043435 2044135 := bstep (se 1 (by rfl) ⟨1533101, by rfl⟩ : syracuseStep 2044135 = 3066203) B3066203
theorem B2299657 : Blo 2043435 2299657 := bbase (se 2 (by rfl) ⟨862371, by rfl⟩ : syracuseStep 2299657 = 1724743) (by norm_num)
theorem B3066209 : Blo 2043435 3066209 := bstep (se 2 (by rfl) ⟨1149828, by rfl⟩ : syracuseStep 3066209 = 2299657) B2299657
theorem B2044139 : Blo 2043435 2044139 := bstep (se 1 (by rfl) ⟨1533104, by rfl⟩ : syracuseStep 2044139 = 3066209) B3066209
theorem B3544261 : Blo 2043435 3544261 := bbase (se 4 (by rfl) ⟨332274, by rfl⟩ : syracuseStep 3544261 = 664549) (by norm_num)
theorem B75610901 : Blo 2043435 75610901 := bstep (se 6 (by rfl) ⟨1772130, by rfl⟩ : syracuseStep 75610901 = 3544261) B3544261
theorem B50407267 : Blo 2043435 50407267 := bstep (se 1 (by rfl) ⟨37805450, by rfl⟩ : syracuseStep 50407267 = 75610901) B75610901
theorem B67209689 : Blo 2043435 67209689 := bstep (se 2 (by rfl) ⟨25203633, by rfl⟩ : syracuseStep 67209689 = 50407267) B50407267
theorem B44806459 : Blo 2043435 44806459 := bstep (se 1 (by rfl) ⟨33604844, by rfl⟩ : syracuseStep 44806459 = 67209689) B67209689
theorem B59741945 : Blo 2043435 59741945 := bstep (se 2 (by rfl) ⟨22403229, by rfl⟩ : syracuseStep 59741945 = 44806459) B44806459
theorem B39827963 : Blo 2043435 39827963 := bstep (se 1 (by rfl) ⟨29870972, by rfl⟩ : syracuseStep 39827963 = 59741945) B59741945
theorem B26551975 : Blo 2043435 26551975 := bstep (se 1 (by rfl) ⟨19913981, by rfl⟩ : syracuseStep 26551975 = 39827963) B39827963
theorem B35402633 : Blo 2043435 35402633 := bstep (se 2 (by rfl) ⟨13275987, by rfl⟩ : syracuseStep 35402633 = 26551975) B26551975
theorem B23601755 : Blo 2043435 23601755 := bstep (se 1 (by rfl) ⟨17701316, by rfl⟩ : syracuseStep 23601755 = 35402633) B35402633
theorem B15734503 : Blo 2043435 15734503 := bstep (se 1 (by rfl) ⟨11800877, by rfl⟩ : syracuseStep 15734503 = 23601755) B23601755
theorem B20979337 : Blo 2043435 20979337 := bstep (se 2 (by rfl) ⟨7867251, by rfl⟩ : syracuseStep 20979337 = 15734503) B15734503
theorem B27972449 : Blo 2043435 27972449 := bstep (se 2 (by rfl) ⟨10489668, by rfl⟩ : syracuseStep 27972449 = 20979337) B20979337
theorem B18648299 : Blo 2043435 18648299 := bstep (se 1 (by rfl) ⟨13986224, by rfl⟩ : syracuseStep 18648299 = 27972449) B27972449
theorem B12432199 : Blo 2043435 12432199 := bstep (se 1 (by rfl) ⟨9324149, by rfl⟩ : syracuseStep 12432199 = 18648299) B18648299
theorem B16576265 : Blo 2043435 16576265 := bstep (se 2 (by rfl) ⟨6216099, by rfl⟩ : syracuseStep 16576265 = 12432199) B12432199
theorem B11050843 : Blo 2043435 11050843 := bstep (se 1 (by rfl) ⟨8288132, by rfl⟩ : syracuseStep 11050843 = 16576265) B16576265
theorem B14734457 : Blo 2043435 14734457 := bstep (se 2 (by rfl) ⟨5525421, by rfl⟩ : syracuseStep 14734457 = 11050843) B11050843
theorem B9822971 : Blo 2043435 9822971 := bstep (se 1 (by rfl) ⟨7367228, by rfl⟩ : syracuseStep 9822971 = 14734457) B14734457
theorem B26194589 : Blo 2043435 26194589 := bstep (se 3 (by rfl) ⟨4911485, by rfl⟩ : syracuseStep 26194589 = 9822971) B9822971
theorem B17463059 : Blo 2043435 17463059 := bstep (se 1 (by rfl) ⟨13097294, by rfl⟩ : syracuseStep 17463059 = 26194589) B26194589
theorem B11642039 : Blo 2043435 11642039 := bstep (se 1 (by rfl) ⟨8731529, by rfl⟩ : syracuseStep 11642039 = 17463059) B17463059
theorem B7761359 : Blo 2043435 7761359 := bstep (se 1 (by rfl) ⟨5821019, by rfl⟩ : syracuseStep 7761359 = 11642039) B11642039
theorem B5174239 : Blo 2043435 5174239 := bstep (se 1 (by rfl) ⟨3880679, by rfl⟩ : syracuseStep 5174239 = 7761359) B7761359
theorem B6898985 : Blo 2043435 6898985 := bstep (se 2 (by rfl) ⟨2587119, by rfl⟩ : syracuseStep 6898985 = 5174239) B5174239
theorem B4599323 : Blo 2043435 4599323 := bstep (se 1 (by rfl) ⟨3449492, by rfl⟩ : syracuseStep 4599323 = 6898985) B6898985
theorem B3066215 : Blo 2043435 3066215 := bstep (se 1 (by rfl) ⟨2299661, by rfl⟩ : syracuseStep 3066215 = 4599323) B4599323
theorem B2044143 : Blo 2043435 2044143 := bstep (se 1 (by rfl) ⟨1533107, by rfl⟩ : syracuseStep 2044143 = 3066215) B3066215
theorem B3066221 : Blo 2043435 3066221 := bbase (se 3 (by rfl) ⟨574916, by rfl⟩ : syracuseStep 3066221 = 1149833) (by norm_num)
theorem B2044147 : Blo 2043435 2044147 := bstep (se 1 (by rfl) ⟨1533110, by rfl⟩ : syracuseStep 2044147 = 3066221) B3066221
theorem B4599341 : Blo 2043435 4599341 := bbase (se 3 (by rfl) ⟨862376, by rfl⟩ : syracuseStep 4599341 = 1724753) (by norm_num)
theorem B3066227 : Blo 2043435 3066227 := bstep (se 1 (by rfl) ⟨2299670, by rfl⟩ : syracuseStep 3066227 = 4599341) B4599341
theorem B2044151 : Blo 2043435 2044151 := bstep (se 1 (by rfl) ⟨1533113, by rfl⟩ : syracuseStep 2044151 = 3066227) B3066227
theorem B2622433 : Blo 2043435 2622433 := bbase (se 2 (by rfl) ⟨983412, by rfl⟩ : syracuseStep 2622433 = 1966825) (by norm_num)
theorem B55945237 : Blo 2043435 55945237 := bstep (se 6 (by rfl) ⟨1311216, by rfl⟩ : syracuseStep 55945237 = 2622433) B2622433
theorem B74593649 : Blo 2043435 74593649 := bstep (se 2 (by rfl) ⟨27972618, by rfl⟩ : syracuseStep 74593649 = 55945237) B55945237
theorem B49729099 : Blo 2043435 49729099 := bstep (se 1 (by rfl) ⟨37296824, by rfl⟩ : syracuseStep 49729099 = 74593649) B74593649
theorem B66305465 : Blo 2043435 66305465 := bstep (se 2 (by rfl) ⟨24864549, by rfl⟩ : syracuseStep 66305465 = 49729099) B49729099
theorem B44203643 : Blo 2043435 44203643 := bstep (se 1 (by rfl) ⟨33152732, by rfl⟩ : syracuseStep 44203643 = 66305465) B66305465
theorem B29469095 : Blo 2043435 29469095 := bstep (se 1 (by rfl) ⟨22101821, by rfl⟩ : syracuseStep 29469095 = 44203643) B44203643
theorem B19646063 : Blo 2043435 19646063 := bstep (se 1 (by rfl) ⟨14734547, by rfl⟩ : syracuseStep 19646063 = 29469095) B29469095
theorem B13097375 : Blo 2043435 13097375 := bstep (se 1 (by rfl) ⟨9823031, by rfl⟩ : syracuseStep 13097375 = 19646063) B19646063
theorem B8731583 : Blo 2043435 8731583 := bstep (se 1 (by rfl) ⟨6548687, by rfl⟩ : syracuseStep 8731583 = 13097375) B13097375
theorem B5821055 : Blo 2043435 5821055 := bstep (se 1 (by rfl) ⟨4365791, by rfl⟩ : syracuseStep 5821055 = 8731583) B8731583
theorem B3880703 : Blo 2043435 3880703 := bstep (se 1 (by rfl) ⟨2910527, by rfl⟩ : syracuseStep 3880703 = 5821055) B5821055
theorem B2587135 : Blo 2043435 2587135 := bstep (se 1 (by rfl) ⟨1940351, by rfl⟩ : syracuseStep 2587135 = 3880703) B3880703
theorem B3449513 : Blo 2043435 3449513 := bstep (se 2 (by rfl) ⟨1293567, by rfl⟩ : syracuseStep 3449513 = 2587135) B2587135
theorem B2299675 : Blo 2043435 2299675 := bstep (se 1 (by rfl) ⟨1724756, by rfl⟩ : syracuseStep 2299675 = 3449513) B3449513
theorem B3066233 : Blo 2043435 3066233 := bstep (se 2 (by rfl) ⟨1149837, by rfl⟩ : syracuseStep 3066233 = 2299675) B2299675
theorem B2044155 : Blo 2043435 2044155 := bstep (se 1 (by rfl) ⟨1533116, by rfl⟩ : syracuseStep 2044155 = 3066233) B3066233
theorem B3274349 : Blo 2043435 3274349 := bbase (se 3 (by rfl) ⟨613940, by rfl⟩ : syracuseStep 3274349 = 1227881) (by norm_num)
theorem B34926389 : Blo 2043435 34926389 := bstep (se 5 (by rfl) ⟨1637174, by rfl⟩ : syracuseStep 34926389 = 3274349) B3274349
theorem B23284259 : Blo 2043435 23284259 := bstep (se 1 (by rfl) ⟨17463194, by rfl⟩ : syracuseStep 23284259 = 34926389) B34926389
theorem B15522839 : Blo 2043435 15522839 := bstep (se 1 (by rfl) ⟨11642129, by rfl⟩ : syracuseStep 15522839 = 23284259) B23284259
theorem B10348559 : Blo 2043435 10348559 := bstep (se 1 (by rfl) ⟨7761419, by rfl⟩ : syracuseStep 10348559 = 15522839) B15522839
theorem B6899039 : Blo 2043435 6899039 := bstep (se 1 (by rfl) ⟨5174279, by rfl⟩ : syracuseStep 6899039 = 10348559) B10348559
theorem B4599359 : Blo 2043435 4599359 := bstep (se 1 (by rfl) ⟨3449519, by rfl⟩ : syracuseStep 4599359 = 6899039) B6899039
theorem B3066239 : Blo 2043435 3066239 := bstep (se 1 (by rfl) ⟨2299679, by rfl⟩ : syracuseStep 3066239 = 4599359) B4599359
theorem B2044159 : Blo 2043435 2044159 := bstep (se 1 (by rfl) ⟨1533119, by rfl⟩ : syracuseStep 2044159 = 3066239) B3066239
theorem B3066245 : Blo 2043435 3066245 := bbase (se 4 (by rfl) ⟨287460, by rfl⟩ : syracuseStep 3066245 = 574921) (by norm_num)
theorem B2044163 : Blo 2043435 2044163 := bstep (se 1 (by rfl) ⟨1533122, by rfl⟩ : syracuseStep 2044163 = 3066245) B3066245
theorem B3449533 : Blo 2043435 3449533 := bbase (se 3 (by rfl) ⟨646787, by rfl⟩ : syracuseStep 3449533 = 1293575) (by norm_num)
theorem B4599377 : Blo 2043435 4599377 := bstep (se 2 (by rfl) ⟨1724766, by rfl⟩ : syracuseStep 4599377 = 3449533) B3449533
theorem B3066251 : Blo 2043435 3066251 := bstep (se 1 (by rfl) ⟨2299688, by rfl⟩ : syracuseStep 3066251 = 4599377) B4599377
theorem B2044167 : Blo 2043435 2044167 := bstep (se 1 (by rfl) ⟨1533125, by rfl⟩ : syracuseStep 2044167 = 3066251) B3066251
theorem B2299693 : Blo 2043435 2299693 := bbase (se 3 (by rfl) ⟨431192, by rfl⟩ : syracuseStep 2299693 = 862385) (by norm_num)
theorem B3066257 : Blo 2043435 3066257 := bstep (se 2 (by rfl) ⟨1149846, by rfl⟩ : syracuseStep 3066257 = 2299693) B2299693
theorem B2044171 : Blo 2043435 2044171 := bstep (se 1 (by rfl) ⟨1533128, by rfl⟩ : syracuseStep 2044171 = 3066257) B3066257
theorem B6899093 : Blo 2043435 6899093 := bbase (se 6 (by rfl) ⟨161697, by rfl⟩ : syracuseStep 6899093 = 323395) (by norm_num)
theorem B4599395 : Blo 2043435 4599395 := bstep (se 1 (by rfl) ⟨3449546, by rfl⟩ : syracuseStep 4599395 = 6899093) B6899093
theorem B3066263 : Blo 2043435 3066263 := bstep (se 1 (by rfl) ⟨2299697, by rfl⟩ : syracuseStep 3066263 = 4599395) B4599395
theorem B2044175 : Blo 2043435 2044175 := bstep (se 1 (by rfl) ⟨1533131, by rfl⟩ : syracuseStep 2044175 = 3066263) B3066263
theorem B3066269 : Blo 2043435 3066269 := bbase (se 3 (by rfl) ⟨574925, by rfl⟩ : syracuseStep 3066269 = 1149851) (by norm_num)
theorem B2044179 : Blo 2043435 2044179 := bstep (se 1 (by rfl) ⟨1533134, by rfl⟩ : syracuseStep 2044179 = 3066269) B3066269
theorem B4599413 : Blo 2043435 4599413 := bbase (se 5 (by rfl) ⟨215597, by rfl⟩ : syracuseStep 4599413 = 431195) (by norm_num)
theorem B3066275 : Blo 2043435 3066275 := bstep (se 1 (by rfl) ⟨2299706, by rfl⟩ : syracuseStep 3066275 = 4599413) B4599413
theorem B2044183 : Blo 2043435 2044183 := bstep (se 1 (by rfl) ⟨1533137, by rfl⟩ : syracuseStep 2044183 = 3066275) B3066275
theorem B6548789 : Blo 2043435 6548789 := bbase (se 5 (by rfl) ⟨306974, by rfl⟩ : syracuseStep 6548789 = 613949) (by norm_num)
theorem B17463437 : Blo 2043435 17463437 := bstep (se 3 (by rfl) ⟨3274394, by rfl⟩ : syracuseStep 17463437 = 6548789) B6548789
theorem B11642291 : Blo 2043435 11642291 := bstep (se 1 (by rfl) ⟨8731718, by rfl⟩ : syracuseStep 11642291 = 17463437) B17463437
theorem B7761527 : Blo 2043435 7761527 := bstep (se 1 (by rfl) ⟨5821145, by rfl⟩ : syracuseStep 7761527 = 11642291) B11642291
theorem B5174351 : Blo 2043435 5174351 := bstep (se 1 (by rfl) ⟨3880763, by rfl⟩ : syracuseStep 5174351 = 7761527) B7761527
theorem B3449567 : Blo 2043435 3449567 := bstep (se 1 (by rfl) ⟨2587175, by rfl⟩ : syracuseStep 3449567 = 5174351) B5174351
theorem B2299711 : Blo 2043435 2299711 := bstep (se 1 (by rfl) ⟨1724783, by rfl⟩ : syracuseStep 2299711 = 3449567) B3449567
theorem B3066281 : Blo 2043435 3066281 := bstep (se 2 (by rfl) ⟨1149855, by rfl⟩ : syracuseStep 3066281 = 2299711) B2299711
theorem B2044187 : Blo 2043435 2044187 := bstep (se 1 (by rfl) ⟨1533140, by rfl⟩ : syracuseStep 2044187 = 3066281) B3066281
theorem B7761541 : Blo 2043435 7761541 := bbase (se 4 (by rfl) ⟨727644, by rfl⟩ : syracuseStep 7761541 = 1455289) (by norm_num)
theorem B10348721 : Blo 2043435 10348721 := bstep (se 2 (by rfl) ⟨3880770, by rfl⟩ : syracuseStep 10348721 = 7761541) B7761541
theorem B6899147 : Blo 2043435 6899147 := bstep (se 1 (by rfl) ⟨5174360, by rfl⟩ : syracuseStep 6899147 = 10348721) B10348721
theorem B4599431 : Blo 2043435 4599431 := bstep (se 1 (by rfl) ⟨3449573, by rfl⟩ : syracuseStep 4599431 = 6899147) B6899147
theorem B3066287 : Blo 2043435 3066287 := bstep (se 1 (by rfl) ⟨2299715, by rfl⟩ : syracuseStep 3066287 = 4599431) B4599431
theorem B2044191 : Blo 2043435 2044191 := bstep (se 1 (by rfl) ⟨1533143, by rfl⟩ : syracuseStep 2044191 = 3066287) B3066287
theorem B3066293 : Blo 2043435 3066293 := bbase (se 5 (by rfl) ⟨143732, by rfl⟩ : syracuseStep 3066293 = 287465) (by norm_num)
theorem B2044195 : Blo 2043435 2044195 := bstep (se 1 (by rfl) ⟨1533146, by rfl⟩ : syracuseStep 2044195 = 3066293) B3066293
theorem B5174381 : Blo 2043435 5174381 := bbase (se 3 (by rfl) ⟨970196, by rfl⟩ : syracuseStep 5174381 = 1940393) (by norm_num)
theorem B3449587 : Blo 2043435 3449587 := bstep (se 1 (by rfl) ⟨2587190, by rfl⟩ : syracuseStep 3449587 = 5174381) B5174381
theorem B4599449 : Blo 2043435 4599449 := bstep (se 2 (by rfl) ⟨1724793, by rfl⟩ : syracuseStep 4599449 = 3449587) B3449587
theorem B3066299 : Blo 2043435 3066299 := bstep (se 1 (by rfl) ⟨2299724, by rfl⟩ : syracuseStep 3066299 = 4599449) B4599449
theorem B2044199 : Blo 2043435 2044199 := bstep (se 1 (by rfl) ⟨1533149, by rfl⟩ : syracuseStep 2044199 = 3066299) B3066299
theorem B2299729 : Blo 2043435 2299729 := bbase (se 2 (by rfl) ⟨862398, by rfl⟩ : syracuseStep 2299729 = 1724797) (by norm_num)
theorem B3066305 : Blo 2043435 3066305 := bstep (se 2 (by rfl) ⟨1149864, by rfl⟩ : syracuseStep 3066305 = 2299729) B2299729
theorem B2044203 : Blo 2043435 2044203 := bstep (se 1 (by rfl) ⟨1533152, by rfl⟩ : syracuseStep 2044203 = 3066305) B3066305
theorem B3108149 : Blo 2043435 3108149 := bbase (se 5 (by rfl) ⟨145694, by rfl⟩ : syracuseStep 3108149 = 291389) (by norm_num)
theorem B2072099 : Blo 2043435 2072099 := bstep (se 1 (by rfl) ⟨1554074, by rfl⟩ : syracuseStep 2072099 = 3108149) B3108149
theorem B5525597 : Blo 2043435 5525597 := bstep (se 3 (by rfl) ⟨1036049, by rfl⟩ : syracuseStep 5525597 = 2072099) B2072099
theorem B3683731 : Blo 2043435 3683731 := bstep (se 1 (by rfl) ⟨2762798, by rfl⟩ : syracuseStep 3683731 = 5525597) B5525597
theorem B4911641 : Blo 2043435 4911641 := bstep (se 2 (by rfl) ⟨1841865, by rfl⟩ : syracuseStep 4911641 = 3683731) B3683731
theorem B3274427 : Blo 2043435 3274427 := bstep (se 1 (by rfl) ⟨2455820, by rfl⟩ : syracuseStep 3274427 = 4911641) B4911641
theorem B2182951 : Blo 2043435 2182951 := bstep (se 1 (by rfl) ⟨1637213, by rfl⟩ : syracuseStep 2182951 = 3274427) B3274427
theorem B2910601 : Blo 2043435 2910601 := bstep (se 2 (by rfl) ⟨1091475, by rfl⟩ : syracuseStep 2910601 = 2182951) B2182951
theorem B3880801 : Blo 2043435 3880801 := bstep (se 2 (by rfl) ⟨1455300, by rfl⟩ : syracuseStep 3880801 = 2910601) B2910601
theorem B5174401 : Blo 2043435 5174401 := bstep (se 2 (by rfl) ⟨1940400, by rfl⟩ : syracuseStep 5174401 = 3880801) B3880801
theorem B6899201 : Blo 2043435 6899201 := bstep (se 2 (by rfl) ⟨2587200, by rfl⟩ : syracuseStep 6899201 = 5174401) B5174401
theorem B4599467 : Blo 2043435 4599467 := bstep (se 1 (by rfl) ⟨3449600, by rfl⟩ : syracuseStep 4599467 = 6899201) B6899201
theorem B3066311 : Blo 2043435 3066311 := bstep (se 1 (by rfl) ⟨2299733, by rfl⟩ : syracuseStep 3066311 = 4599467) B4599467
theorem B2044207 : Blo 2043435 2044207 := bstep (se 1 (by rfl) ⟨1533155, by rfl⟩ : syracuseStep 2044207 = 3066311) B3066311
theorem B3066317 : Blo 2043435 3066317 := bbase (se 3 (by rfl) ⟨574934, by rfl⟩ : syracuseStep 3066317 = 1149869) (by norm_num)
theorem B2044211 : Blo 2043435 2044211 := bstep (se 1 (by rfl) ⟨1533158, by rfl⟩ : syracuseStep 2044211 = 3066317) B3066317
theorem B4599485 : Blo 2043435 4599485 := bbase (se 3 (by rfl) ⟨862403, by rfl⟩ : syracuseStep 4599485 = 1724807) (by norm_num)
theorem B3066323 : Blo 2043435 3066323 := bstep (se 1 (by rfl) ⟨2299742, by rfl⟩ : syracuseStep 3066323 = 4599485) B4599485
theorem B2044215 : Blo 2043435 2044215 := bstep (se 1 (by rfl) ⟨1533161, by rfl⟩ : syracuseStep 2044215 = 3066323) B3066323
theorem B3449621 : Blo 2043435 3449621 := bbase (se 6 (by rfl) ⟨80850, by rfl⟩ : syracuseStep 3449621 = 161701) (by norm_num)
theorem B2299747 : Blo 2043435 2299747 := bstep (se 1 (by rfl) ⟨1724810, by rfl⟩ : syracuseStep 2299747 = 3449621) B3449621
theorem B3066329 : Blo 2043435 3066329 := bstep (se 2 (by rfl) ⟨1149873, by rfl⟩ : syracuseStep 3066329 = 2299747) B2299747
theorem B2044219 : Blo 2043435 2044219 := bstep (se 1 (by rfl) ⟨1533164, by rfl⟩ : syracuseStep 2044219 = 3066329) B3066329
theorem B3496693 : Blo 2043435 3496693 := bbase (se 5 (by rfl) ⟨163907, by rfl⟩ : syracuseStep 3496693 = 327815) (by norm_num)
theorem B4662257 : Blo 2043435 4662257 := bstep (se 2 (by rfl) ⟨1748346, by rfl⟩ : syracuseStep 4662257 = 3496693) B3496693
theorem B12432685 : Blo 2043435 12432685 := bstep (se 3 (by rfl) ⟨2331128, by rfl⟩ : syracuseStep 12432685 = 4662257) B4662257
theorem B16576913 : Blo 2043435 16576913 := bstep (se 2 (by rfl) ⟨6216342, by rfl⟩ : syracuseStep 16576913 = 12432685) B12432685
theorem B44205101 : Blo 2043435 44205101 := bstep (se 3 (by rfl) ⟨8288456, by rfl⟩ : syracuseStep 44205101 = 16576913) B16576913
theorem B29470067 : Blo 2043435 29470067 := bstep (se 1 (by rfl) ⟨22102550, by rfl⟩ : syracuseStep 29470067 = 44205101) B44205101
theorem B19646711 : Blo 2043435 19646711 := bstep (se 1 (by rfl) ⟨14735033, by rfl⟩ : syracuseStep 19646711 = 29470067) B29470067
theorem B13097807 : Blo 2043435 13097807 := bstep (se 1 (by rfl) ⟨9823355, by rfl⟩ : syracuseStep 13097807 = 19646711) B19646711
theorem B8731871 : Blo 2043435 8731871 := bstep (se 1 (by rfl) ⟨6548903, by rfl⟩ : syracuseStep 8731871 = 13097807) B13097807
theorem B5821247 : Blo 2043435 5821247 := bstep (se 1 (by rfl) ⟨4365935, by rfl⟩ : syracuseStep 5821247 = 8731871) B8731871
theorem B15523325 : Blo 2043435 15523325 := bstep (se 3 (by rfl) ⟨2910623, by rfl⟩ : syracuseStep 15523325 = 5821247) B5821247
theorem B10348883 : Blo 2043435 10348883 := bstep (se 1 (by rfl) ⟨7761662, by rfl⟩ : syracuseStep 10348883 = 15523325) B15523325
theorem B6899255 : Blo 2043435 6899255 := bstep (se 1 (by rfl) ⟨5174441, by rfl⟩ : syracuseStep 6899255 = 10348883) B10348883
theorem B4599503 : Blo 2043435 4599503 := bstep (se 1 (by rfl) ⟨3449627, by rfl⟩ : syracuseStep 4599503 = 6899255) B6899255
theorem B3066335 : Blo 2043435 3066335 := bstep (se 1 (by rfl) ⟨2299751, by rfl⟩ : syracuseStep 3066335 = 4599503) B4599503
theorem B2044223 : Blo 2043435 2044223 := bstep (se 1 (by rfl) ⟨1533167, by rfl⟩ : syracuseStep 2044223 = 3066335) B3066335
theorem B3066341 : Blo 2043435 3066341 := bbase (se 4 (by rfl) ⟨287469, by rfl⟩ : syracuseStep 3066341 = 574939) (by norm_num)
theorem B2044227 : Blo 2043435 2044227 := bstep (se 1 (by rfl) ⟨1533170, by rfl⟩ : syracuseStep 2044227 = 3066341) B3066341
theorem B2455849 : Blo 2043435 2455849 := bbase (se 2 (by rfl) ⟨920943, by rfl⟩ : syracuseStep 2455849 = 1841887) (by norm_num)
theorem B13097861 : Blo 2043435 13097861 := bstep (se 4 (by rfl) ⟨1227924, by rfl⟩ : syracuseStep 13097861 = 2455849) B2455849
theorem B8731907 : Blo 2043435 8731907 := bstep (se 1 (by rfl) ⟨6548930, by rfl⟩ : syracuseStep 8731907 = 13097861) B13097861
theorem B5821271 : Blo 2043435 5821271 := bstep (se 1 (by rfl) ⟨4365953, by rfl⟩ : syracuseStep 5821271 = 8731907) B8731907
theorem B3880847 : Blo 2043435 3880847 := bstep (se 1 (by rfl) ⟨2910635, by rfl⟩ : syracuseStep 3880847 = 5821271) B5821271
theorem B2587231 : Blo 2043435 2587231 := bstep (se 1 (by rfl) ⟨1940423, by rfl⟩ : syracuseStep 2587231 = 3880847) B3880847
theorem B3449641 : Blo 2043435 3449641 := bstep (se 2 (by rfl) ⟨1293615, by rfl⟩ : syracuseStep 3449641 = 2587231) B2587231
theorem B4599521 : Blo 2043435 4599521 := bstep (se 2 (by rfl) ⟨1724820, by rfl⟩ : syracuseStep 4599521 = 3449641) B3449641
theorem B3066347 : Blo 2043435 3066347 := bstep (se 1 (by rfl) ⟨2299760, by rfl⟩ : syracuseStep 3066347 = 4599521) B4599521
theorem B2044231 : Blo 2043435 2044231 := bstep (se 1 (by rfl) ⟨1533173, by rfl⟩ : syracuseStep 2044231 = 3066347) B3066347
theorem B2299765 : Blo 2043435 2299765 := bbase (se 5 (by rfl) ⟨107801, by rfl⟩ : syracuseStep 2299765 = 215603) (by norm_num)
theorem B3066353 : Blo 2043435 3066353 := bstep (se 2 (by rfl) ⟨1149882, by rfl⟩ : syracuseStep 3066353 = 2299765) B2299765
theorem B2044235 : Blo 2043435 2044235 := bstep (se 1 (by rfl) ⟨1533176, by rfl⟩ : syracuseStep 2044235 = 3066353) B3066353
theorem B2587241 : Blo 2043435 2587241 := bbase (se 2 (by rfl) ⟨970215, by rfl⟩ : syracuseStep 2587241 = 1940431) (by norm_num)
theorem B6899309 : Blo 2043435 6899309 := bstep (se 3 (by rfl) ⟨1293620, by rfl⟩ : syracuseStep 6899309 = 2587241) B2587241
theorem B4599539 : Blo 2043435 4599539 := bstep (se 1 (by rfl) ⟨3449654, by rfl⟩ : syracuseStep 4599539 = 6899309) B6899309
theorem B3066359 : Blo 2043435 3066359 := bstep (se 1 (by rfl) ⟨2299769, by rfl⟩ : syracuseStep 3066359 = 4599539) B4599539
theorem B2044239 : Blo 2043435 2044239 := bstep (se 1 (by rfl) ⟨1533179, by rfl⟩ : syracuseStep 2044239 = 3066359) B3066359
theorem B3066365 : Blo 2043435 3066365 := bbase (se 3 (by rfl) ⟨574943, by rfl⟩ : syracuseStep 3066365 = 1149887) (by norm_num)
theorem B2044243 : Blo 2043435 2044243 := bstep (se 1 (by rfl) ⟨1533182, by rfl⟩ : syracuseStep 2044243 = 3066365) B3066365
theorem B4599557 : Blo 2043435 4599557 := bbase (se 4 (by rfl) ⟨431208, by rfl⟩ : syracuseStep 4599557 = 862417) (by norm_num)
theorem B3066371 : Blo 2043435 3066371 := bstep (se 1 (by rfl) ⟨2299778, by rfl⟩ : syracuseStep 3066371 = 4599557) B4599557
theorem B2044247 : Blo 2043435 2044247 := bstep (se 1 (by rfl) ⟨1533185, by rfl⟩ : syracuseStep 2044247 = 3066371) B3066371
theorem B3880885 : Blo 2043435 3880885 := bbase (se 5 (by rfl) ⟨181916, by rfl⟩ : syracuseStep 3880885 = 363833) (by norm_num)
theorem B5174513 : Blo 2043435 5174513 := bstep (se 2 (by rfl) ⟨1940442, by rfl⟩ : syracuseStep 5174513 = 3880885) B3880885
theorem B3449675 : Blo 2043435 3449675 := bstep (se 1 (by rfl) ⟨2587256, by rfl⟩ : syracuseStep 3449675 = 5174513) B5174513
theorem B2299783 : Blo 2043435 2299783 := bstep (se 1 (by rfl) ⟨1724837, by rfl⟩ : syracuseStep 2299783 = 3449675) B3449675
theorem B3066377 : Blo 2043435 3066377 := bstep (se 2 (by rfl) ⟨1149891, by rfl⟩ : syracuseStep 3066377 = 2299783) B2299783
theorem B2044251 : Blo 2043435 2044251 := bstep (se 1 (by rfl) ⟨1533188, by rfl⟩ : syracuseStep 2044251 = 3066377) B3066377
theorem B10349045 : Blo 2043435 10349045 := bbase (se 5 (by rfl) ⟨485111, by rfl⟩ : syracuseStep 10349045 = 970223) (by norm_num)
theorem B6899363 : Blo 2043435 6899363 := bstep (se 1 (by rfl) ⟨5174522, by rfl⟩ : syracuseStep 6899363 = 10349045) B10349045
theorem B4599575 : Blo 2043435 4599575 := bstep (se 1 (by rfl) ⟨3449681, by rfl⟩ : syracuseStep 4599575 = 6899363) B6899363
theorem B3066383 : Blo 2043435 3066383 := bstep (se 1 (by rfl) ⟨2299787, by rfl⟩ : syracuseStep 3066383 = 4599575) B4599575
theorem B2044255 : Blo 2043435 2044255 := bstep (se 1 (by rfl) ⟨1533191, by rfl⟩ : syracuseStep 2044255 = 3066383) B3066383
theorem B3066389 : Blo 2043435 3066389 := bbase (se 6 (by rfl) ⟨71868, by rfl⟩ : syracuseStep 3066389 = 143737) (by norm_num)
theorem B2044259 : Blo 2043435 2044259 := bstep (se 1 (by rfl) ⟨1533194, by rfl⟩ : syracuseStep 2044259 = 3066389) B3066389
theorem B17464085 : Blo 2043435 17464085 := bbase (se 6 (by rfl) ⟨409314, by rfl⟩ : syracuseStep 17464085 = 818629) (by norm_num)
theorem B11642723 : Blo 2043435 11642723 := bstep (se 1 (by rfl) ⟨8732042, by rfl⟩ : syracuseStep 11642723 = 17464085) B17464085
theorem B7761815 : Blo 2043435 7761815 := bstep (se 1 (by rfl) ⟨5821361, by rfl⟩ : syracuseStep 7761815 = 11642723) B11642723
theorem B5174543 : Blo 2043435 5174543 := bstep (se 1 (by rfl) ⟨3880907, by rfl⟩ : syracuseStep 5174543 = 7761815) B7761815
theorem B3449695 : Blo 2043435 3449695 := bstep (se 1 (by rfl) ⟨2587271, by rfl⟩ : syracuseStep 3449695 = 5174543) B5174543
theorem B4599593 : Blo 2043435 4599593 := bstep (se 2 (by rfl) ⟨1724847, by rfl⟩ : syracuseStep 4599593 = 3449695) B3449695
theorem B3066395 : Blo 2043435 3066395 := bstep (se 1 (by rfl) ⟨2299796, by rfl⟩ : syracuseStep 3066395 = 4599593) B4599593
theorem B2044263 : Blo 2043435 2044263 := bstep (se 1 (by rfl) ⟨1533197, by rfl⟩ : syracuseStep 2044263 = 3066395) B3066395
theorem B2299801 : Blo 2043435 2299801 := bbase (se 2 (by rfl) ⟨862425, by rfl⟩ : syracuseStep 2299801 = 1724851) (by norm_num)
theorem B3066401 : Blo 2043435 3066401 := bstep (se 2 (by rfl) ⟨1149900, by rfl⟩ : syracuseStep 3066401 = 2299801) B2299801
theorem B2044267 : Blo 2043435 2044267 := bstep (se 1 (by rfl) ⟨1533200, by rfl⟩ : syracuseStep 2044267 = 3066401) B3066401
theorem B7761845 : Blo 2043435 7761845 := bbase (se 5 (by rfl) ⟨363836, by rfl⟩ : syracuseStep 7761845 = 727673) (by norm_num)
theorem B5174563 : Blo 2043435 5174563 := bstep (se 1 (by rfl) ⟨3880922, by rfl⟩ : syracuseStep 5174563 = 7761845) B7761845
theorem B6899417 : Blo 2043435 6899417 := bstep (se 2 (by rfl) ⟨2587281, by rfl⟩ : syracuseStep 6899417 = 5174563) B5174563
theorem B4599611 : Blo 2043435 4599611 := bstep (se 1 (by rfl) ⟨3449708, by rfl⟩ : syracuseStep 4599611 = 6899417) B6899417
theorem B3066407 : Blo 2043435 3066407 := bstep (se 1 (by rfl) ⟨2299805, by rfl⟩ : syracuseStep 3066407 = 4599611) B4599611
theorem B2044271 : Blo 2043435 2044271 := bstep (se 1 (by rfl) ⟨1533203, by rfl⟩ : syracuseStep 2044271 = 3066407) B3066407
theorem B3066413 : Blo 2043435 3066413 := bbase (se 3 (by rfl) ⟨574952, by rfl⟩ : syracuseStep 3066413 = 1149905) (by norm_num)
theorem B2044275 : Blo 2043435 2044275 := bstep (se 1 (by rfl) ⟨1533206, by rfl⟩ : syracuseStep 2044275 = 3066413) B3066413
theorem B4599629 : Blo 2043435 4599629 := bbase (se 3 (by rfl) ⟨862430, by rfl⟩ : syracuseStep 4599629 = 1724861) (by norm_num)
theorem B3066419 : Blo 2043435 3066419 := bstep (se 1 (by rfl) ⟨2299814, by rfl⟩ : syracuseStep 3066419 = 4599629) B4599629
theorem B2044279 : Blo 2043435 2044279 := bstep (se 1 (by rfl) ⟨1533209, by rfl⟩ : syracuseStep 2044279 = 3066419) B3066419
theorem B2587297 : Blo 2043435 2587297 := bbase (se 2 (by rfl) ⟨970236, by rfl⟩ : syracuseStep 2587297 = 1940473) (by norm_num)
theorem B3449729 : Blo 2043435 3449729 := bstep (se 2 (by rfl) ⟨1293648, by rfl⟩ : syracuseStep 3449729 = 2587297) B2587297
theorem B2299819 : Blo 2043435 2299819 := bstep (se 1 (by rfl) ⟨1724864, by rfl⟩ : syracuseStep 2299819 = 3449729) B3449729
theorem B3066425 : Blo 2043435 3066425 := bstep (se 2 (by rfl) ⟨1149909, by rfl⟩ : syracuseStep 3066425 = 2299819) B2299819
theorem B2044283 : Blo 2043435 2044283 := bstep (se 1 (by rfl) ⟨1533212, by rfl⟩ : syracuseStep 2044283 = 3066425) B3066425
theorem B23285717 : Blo 2043435 23285717 := bbase (se 7 (by rfl) ⟨272879, by rfl⟩ : syracuseStep 23285717 = 545759) (by norm_num)
theorem B15523811 : Blo 2043435 15523811 := bstep (se 1 (by rfl) ⟨11642858, by rfl⟩ : syracuseStep 15523811 = 23285717) B23285717
theorem B10349207 : Blo 2043435 10349207 := bstep (se 1 (by rfl) ⟨7761905, by rfl⟩ : syracuseStep 10349207 = 15523811) B15523811
theorem B6899471 : Blo 2043435 6899471 := bstep (se 1 (by rfl) ⟨5174603, by rfl⟩ : syracuseStep 6899471 = 10349207) B10349207
theorem B4599647 : Blo 2043435 4599647 := bstep (se 1 (by rfl) ⟨3449735, by rfl⟩ : syracuseStep 4599647 = 6899471) B6899471
theorem B3066431 : Blo 2043435 3066431 := bstep (se 1 (by rfl) ⟨2299823, by rfl⟩ : syracuseStep 3066431 = 4599647) B4599647
theorem B2044287 : Blo 2043435 2044287 := bstep (se 1 (by rfl) ⟨1533215, by rfl⟩ : syracuseStep 2044287 = 3066431) B3066431
theorem B3066437 : Blo 2043435 3066437 := bbase (se 4 (by rfl) ⟨287478, by rfl⟩ : syracuseStep 3066437 = 574957) (by norm_num)
theorem B2044291 : Blo 2043435 2044291 := bstep (se 1 (by rfl) ⟨1533218, by rfl⟩ : syracuseStep 2044291 = 3066437) B3066437
theorem B3449749 : Blo 2043435 3449749 := bbase (se 6 (by rfl) ⟨80853, by rfl⟩ : syracuseStep 3449749 = 161707) (by norm_num)
theorem B4599665 : Blo 2043435 4599665 := bstep (se 2 (by rfl) ⟨1724874, by rfl⟩ : syracuseStep 4599665 = 3449749) B3449749
theorem B3066443 : Blo 2043435 3066443 := bstep (se 1 (by rfl) ⟨2299832, by rfl⟩ : syracuseStep 3066443 = 4599665) B4599665
theorem B2044295 : Blo 2043435 2044295 := bstep (se 1 (by rfl) ⟨1533221, by rfl⟩ : syracuseStep 2044295 = 3066443) B3066443
theorem B2299837 : Blo 2043435 2299837 := bbase (se 3 (by rfl) ⟨431219, by rfl⟩ : syracuseStep 2299837 = 862439) (by norm_num)
theorem B3066449 : Blo 2043435 3066449 := bstep (se 2 (by rfl) ⟨1149918, by rfl⟩ : syracuseStep 3066449 = 2299837) B2299837
theorem B2044299 : Blo 2043435 2044299 := bstep (se 1 (by rfl) ⟨1533224, by rfl⟩ : syracuseStep 2044299 = 3066449) B3066449
theorem B6899525 : Blo 2043435 6899525 := bbase (se 4 (by rfl) ⟨646830, by rfl⟩ : syracuseStep 6899525 = 1293661) (by norm_num)
theorem B4599683 : Blo 2043435 4599683 := bstep (se 1 (by rfl) ⟨3449762, by rfl⟩ : syracuseStep 4599683 = 6899525) B6899525
theorem B3066455 : Blo 2043435 3066455 := bstep (se 1 (by rfl) ⟨2299841, by rfl⟩ : syracuseStep 3066455 = 4599683) B4599683
theorem B2044303 : Blo 2043435 2044303 := bstep (se 1 (by rfl) ⟨1533227, by rfl⟩ : syracuseStep 2044303 = 3066455) B3066455
theorem B3066461 : Blo 2043435 3066461 := bbase (se 3 (by rfl) ⟨574961, by rfl⟩ : syracuseStep 3066461 = 1149923) (by norm_num)
theorem B2044307 : Blo 2043435 2044307 := bstep (se 1 (by rfl) ⟨1533230, by rfl⟩ : syracuseStep 2044307 = 3066461) B3066461
theorem B4599701 : Blo 2043435 4599701 := bbase (se 6 (by rfl) ⟨107805, by rfl⟩ : syracuseStep 4599701 = 215611) (by norm_num)
theorem B3066467 : Blo 2043435 3066467 := bstep (se 1 (by rfl) ⟨2299850, by rfl⟩ : syracuseStep 3066467 = 4599701) B4599701
theorem B2044311 : Blo 2043435 2044311 := bstep (se 1 (by rfl) ⟨1533233, by rfl⟩ : syracuseStep 2044311 = 3066467) B3066467
theorem B4366133 : Blo 2043435 4366133 := bbase (se 5 (by rfl) ⟨204662, by rfl⟩ : syracuseStep 4366133 = 409325) (by norm_num)
theorem B2910755 : Blo 2043435 2910755 := bstep (se 1 (by rfl) ⟨2183066, by rfl⟩ : syracuseStep 2910755 = 4366133) B4366133
theorem B7762013 : Blo 2043435 7762013 := bstep (se 3 (by rfl) ⟨1455377, by rfl⟩ : syracuseStep 7762013 = 2910755) B2910755
theorem B5174675 : Blo 2043435 5174675 := bstep (se 1 (by rfl) ⟨3881006, by rfl⟩ : syracuseStep 5174675 = 7762013) B7762013
theorem B3449783 : Blo 2043435 3449783 := bstep (se 1 (by rfl) ⟨2587337, by rfl⟩ : syracuseStep 3449783 = 5174675) B5174675
theorem B2299855 : Blo 2043435 2299855 := bstep (se 1 (by rfl) ⟨1724891, by rfl⟩ : syracuseStep 2299855 = 3449783) B3449783
theorem B3066473 : Blo 2043435 3066473 := bstep (se 2 (by rfl) ⟨1149927, by rfl⟩ : syracuseStep 3066473 = 2299855) B2299855
theorem B2044315 : Blo 2043435 2044315 := bstep (se 1 (by rfl) ⟨1533236, by rfl⟩ : syracuseStep 2044315 = 3066473) B3066473
theorem B3933965 : Blo 2043435 3933965 := bbase (se 3 (by rfl) ⟨737618, by rfl⟩ : syracuseStep 3933965 = 1475237) (by norm_num)
theorem B10490573 : Blo 2043435 10490573 := bstep (se 3 (by rfl) ⟨1966982, by rfl⟩ : syracuseStep 10490573 = 3933965) B3933965
theorem B6993715 : Blo 2043435 6993715 := bstep (se 1 (by rfl) ⟨5245286, by rfl⟩ : syracuseStep 6993715 = 10490573) B10490573
theorem B9324953 : Blo 2043435 9324953 := bstep (se 2 (by rfl) ⟨3496857, by rfl⟩ : syracuseStep 9324953 = 6993715) B6993715
theorem B6216635 : Blo 2043435 6216635 := bstep (se 1 (by rfl) ⟨4662476, by rfl⟩ : syracuseStep 6216635 = 9324953) B9324953
theorem B16577693 : Blo 2043435 16577693 := bstep (se 3 (by rfl) ⟨3108317, by rfl⟩ : syracuseStep 16577693 = 6216635) B6216635
theorem B11051795 : Blo 2043435 11051795 := bstep (se 1 (by rfl) ⟨8288846, by rfl⟩ : syracuseStep 11051795 = 16577693) B16577693
theorem B7367863 : Blo 2043435 7367863 := bstep (se 1 (by rfl) ⟨5525897, by rfl⟩ : syracuseStep 7367863 = 11051795) B11051795
theorem B9823817 : Blo 2043435 9823817 := bstep (se 2 (by rfl) ⟨3683931, by rfl⟩ : syracuseStep 9823817 = 7367863) B7367863
theorem B6549211 : Blo 2043435 6549211 := bstep (se 1 (by rfl) ⟨4911908, by rfl⟩ : syracuseStep 6549211 = 9823817) B9823817
theorem B8732281 : Blo 2043435 8732281 := bstep (se 2 (by rfl) ⟨3274605, by rfl⟩ : syracuseStep 8732281 = 6549211) B6549211
theorem B11643041 : Blo 2043435 11643041 := bstep (se 2 (by rfl) ⟨4366140, by rfl⟩ : syracuseStep 11643041 = 8732281) B8732281
theorem B7762027 : Blo 2043435 7762027 := bstep (se 1 (by rfl) ⟨5821520, by rfl⟩ : syracuseStep 7762027 = 11643041) B11643041
theorem B10349369 : Blo 2043435 10349369 := bstep (se 2 (by rfl) ⟨3881013, by rfl⟩ : syracuseStep 10349369 = 7762027) B7762027
theorem B6899579 : Blo 2043435 6899579 := bstep (se 1 (by rfl) ⟨5174684, by rfl⟩ : syracuseStep 6899579 = 10349369) B10349369
theorem B4599719 : Blo 2043435 4599719 := bstep (se 1 (by rfl) ⟨3449789, by rfl⟩ : syracuseStep 4599719 = 6899579) B6899579
theorem B3066479 : Blo 2043435 3066479 := bstep (se 1 (by rfl) ⟨2299859, by rfl⟩ : syracuseStep 3066479 = 4599719) B4599719
theorem B2044319 : Blo 2043435 2044319 := bstep (se 1 (by rfl) ⟨1533239, by rfl⟩ : syracuseStep 2044319 = 3066479) B3066479
theorem B3066485 : Blo 2043435 3066485 := bbase (se 5 (by rfl) ⟨143741, by rfl⟩ : syracuseStep 3066485 = 287483) (by norm_num)
theorem B2044323 : Blo 2043435 2044323 := bstep (se 1 (by rfl) ⟨1533242, by rfl⟩ : syracuseStep 2044323 = 3066485) B3066485
theorem B3881029 : Blo 2043435 3881029 := bbase (se 4 (by rfl) ⟨363846, by rfl⟩ : syracuseStep 3881029 = 727693) (by norm_num)
theorem B5174705 : Blo 2043435 5174705 := bstep (se 2 (by rfl) ⟨1940514, by rfl⟩ : syracuseStep 5174705 = 3881029) B3881029
theorem B3449803 : Blo 2043435 3449803 := bstep (se 1 (by rfl) ⟨2587352, by rfl⟩ : syracuseStep 3449803 = 5174705) B5174705
theorem B4599737 : Blo 2043435 4599737 := bstep (se 2 (by rfl) ⟨1724901, by rfl⟩ : syracuseStep 4599737 = 3449803) B3449803
theorem B3066491 : Blo 2043435 3066491 := bstep (se 1 (by rfl) ⟨2299868, by rfl⟩ : syracuseStep 3066491 = 4599737) B4599737
theorem B2044327 : Blo 2043435 2044327 := bstep (se 1 (by rfl) ⟨1533245, by rfl⟩ : syracuseStep 2044327 = 3066491) B3066491
theorem B2299873 : Blo 2043435 2299873 := bbase (se 2 (by rfl) ⟨862452, by rfl⟩ : syracuseStep 2299873 = 1724905) (by norm_num)
theorem B3066497 : Blo 2043435 3066497 := bstep (se 2 (by rfl) ⟨1149936, by rfl⟩ : syracuseStep 3066497 = 2299873) B2299873
theorem B2044331 : Blo 2043435 2044331 := bstep (se 1 (by rfl) ⟨1533248, by rfl⟩ : syracuseStep 2044331 = 3066497) B3066497
theorem B5174725 : Blo 2043435 5174725 := bbase (se 4 (by rfl) ⟨485130, by rfl⟩ : syracuseStep 5174725 = 970261) (by norm_num)
theorem B6899633 : Blo 2043435 6899633 := bstep (se 2 (by rfl) ⟨2587362, by rfl⟩ : syracuseStep 6899633 = 5174725) B5174725
theorem B4599755 : Blo 2043435 4599755 := bstep (se 1 (by rfl) ⟨3449816, by rfl⟩ : syracuseStep 4599755 = 6899633) B6899633
theorem B3066503 : Blo 2043435 3066503 := bstep (se 1 (by rfl) ⟨2299877, by rfl⟩ : syracuseStep 3066503 = 4599755) B4599755
theorem B2044335 : Blo 2043435 2044335 := bstep (se 1 (by rfl) ⟨1533251, by rfl⟩ : syracuseStep 2044335 = 3066503) B3066503
theorem B3066509 : Blo 2043435 3066509 := bbase (se 3 (by rfl) ⟨574970, by rfl⟩ : syracuseStep 3066509 = 1149941) (by norm_num)
theorem B2044339 : Blo 2043435 2044339 := bstep (se 1 (by rfl) ⟨1533254, by rfl⟩ : syracuseStep 2044339 = 3066509) B3066509
theorem B4599773 : Blo 2043435 4599773 := bbase (se 3 (by rfl) ⟨862457, by rfl⟩ : syracuseStep 4599773 = 1724915) (by norm_num)
theorem B3066515 : Blo 2043435 3066515 := bstep (se 1 (by rfl) ⟨2299886, by rfl⟩ : syracuseStep 3066515 = 4599773) B4599773
theorem B2044343 : Blo 2043435 2044343 := bstep (se 1 (by rfl) ⟨1533257, by rfl⟩ : syracuseStep 2044343 = 3066515) B3066515
theorem B3449837 : Blo 2043435 3449837 := bbase (se 3 (by rfl) ⟨646844, by rfl⟩ : syracuseStep 3449837 = 1293689) (by norm_num)
theorem B2299891 : Blo 2043435 2299891 := bstep (se 1 (by rfl) ⟨1724918, by rfl⟩ : syracuseStep 2299891 = 3449837) B3449837
theorem B3066521 : Blo 2043435 3066521 := bstep (se 2 (by rfl) ⟨1149945, by rfl⟩ : syracuseStep 3066521 = 2299891) B2299891
theorem B2044347 : Blo 2043435 2044347 := bstep (se 1 (by rfl) ⟨1533260, by rfl⟩ : syracuseStep 2044347 = 3066521) B3066521
theorem B3683989 : Blo 2043435 3683989 := bbase (se 6 (by rfl) ⟨86343, by rfl⟩ : syracuseStep 3683989 = 172687) (by norm_num)
theorem B4911985 : Blo 2043435 4911985 := bstep (se 2 (by rfl) ⟨1841994, by rfl⟩ : syracuseStep 4911985 = 3683989) B3683989
theorem B26197253 : Blo 2043435 26197253 := bstep (se 4 (by rfl) ⟨2455992, by rfl⟩ : syracuseStep 26197253 = 4911985) B4911985
theorem B17464835 : Blo 2043435 17464835 := bstep (se 1 (by rfl) ⟨13098626, by rfl⟩ : syracuseStep 17464835 = 26197253) B26197253
theorem B11643223 : Blo 2043435 11643223 := bstep (se 1 (by rfl) ⟨8732417, by rfl⟩ : syracuseStep 11643223 = 17464835) B17464835
theorem B15524297 : Blo 2043435 15524297 := bstep (se 2 (by rfl) ⟨5821611, by rfl⟩ : syracuseStep 15524297 = 11643223) B11643223
theorem B10349531 : Blo 2043435 10349531 := bstep (se 1 (by rfl) ⟨7762148, by rfl⟩ : syracuseStep 10349531 = 15524297) B15524297
theorem B6899687 : Blo 2043435 6899687 := bstep (se 1 (by rfl) ⟨5174765, by rfl⟩ : syracuseStep 6899687 = 10349531) B10349531
theorem B4599791 : Blo 2043435 4599791 := bstep (se 1 (by rfl) ⟨3449843, by rfl⟩ : syracuseStep 4599791 = 6899687) B6899687
theorem B3066527 : Blo 2043435 3066527 := bstep (se 1 (by rfl) ⟨2299895, by rfl⟩ : syracuseStep 3066527 = 4599791) B4599791
theorem B2044351 : Blo 2043435 2044351 := bstep (se 1 (by rfl) ⟨1533263, by rfl⟩ : syracuseStep 2044351 = 3066527) B3066527
theorem B3066533 : Blo 2043435 3066533 := bbase (se 4 (by rfl) ⟨287487, by rfl⟩ : syracuseStep 3066533 = 574975) (by norm_num)
theorem B2044355 : Blo 2043435 2044355 := bstep (se 1 (by rfl) ⟨1533266, by rfl⟩ : syracuseStep 2044355 = 3066533) B3066533
theorem B2587393 : Blo 2043435 2587393 := bbase (se 2 (by rfl) ⟨970272, by rfl⟩ : syracuseStep 2587393 = 1940545) (by norm_num)
theorem B3449857 : Blo 2043435 3449857 := bstep (se 2 (by rfl) ⟨1293696, by rfl⟩ : syracuseStep 3449857 = 2587393) B2587393
theorem B4599809 : Blo 2043435 4599809 := bstep (se 2 (by rfl) ⟨1724928, by rfl⟩ : syracuseStep 4599809 = 3449857) B3449857
theorem B3066539 : Blo 2043435 3066539 := bstep (se 1 (by rfl) ⟨2299904, by rfl⟩ : syracuseStep 3066539 = 4599809) B4599809
theorem B2044359 : Blo 2043435 2044359 := bstep (se 1 (by rfl) ⟨1533269, by rfl⟩ : syracuseStep 2044359 = 3066539) B3066539
theorem B2299909 : Blo 2043435 2299909 := bbase (se 4 (by rfl) ⟨215616, by rfl⟩ : syracuseStep 2299909 = 431233) (by norm_num)
theorem B3066545 : Blo 2043435 3066545 := bstep (se 2 (by rfl) ⟨1149954, by rfl⟩ : syracuseStep 3066545 = 2299909) B2299909
theorem B2044363 : Blo 2043435 2044363 := bstep (se 1 (by rfl) ⟨1533272, by rfl⟩ : syracuseStep 2044363 = 3066545) B3066545
theorem B2910829 : Blo 2043435 2910829 := bbase (se 3 (by rfl) ⟨545780, by rfl⟩ : syracuseStep 2910829 = 1091561) (by norm_num)
theorem B3881105 : Blo 2043435 3881105 := bstep (se 2 (by rfl) ⟨1455414, by rfl⟩ : syracuseStep 3881105 = 2910829) B2910829
theorem B2587403 : Blo 2043435 2587403 := bstep (se 1 (by rfl) ⟨1940552, by rfl⟩ : syracuseStep 2587403 = 3881105) B3881105
theorem B6899741 : Blo 2043435 6899741 := bstep (se 3 (by rfl) ⟨1293701, by rfl⟩ : syracuseStep 6899741 = 2587403) B2587403
theorem B4599827 : Blo 2043435 4599827 := bstep (se 1 (by rfl) ⟨3449870, by rfl⟩ : syracuseStep 4599827 = 6899741) B6899741
theorem B3066551 : Blo 2043435 3066551 := bstep (se 1 (by rfl) ⟨2299913, by rfl⟩ : syracuseStep 3066551 = 4599827) B4599827
theorem B2044367 : Blo 2043435 2044367 := bstep (se 1 (by rfl) ⟨1533275, by rfl⟩ : syracuseStep 2044367 = 3066551) B3066551
theorem B3066557 : Blo 2043435 3066557 := bbase (se 3 (by rfl) ⟨574979, by rfl⟩ : syracuseStep 3066557 = 1149959) (by norm_num)
theorem B2044371 : Blo 2043435 2044371 := bstep (se 1 (by rfl) ⟨1533278, by rfl⟩ : syracuseStep 2044371 = 3066557) B3066557
theorem B4599845 : Blo 2043435 4599845 := bbase (se 4 (by rfl) ⟨431235, by rfl⟩ : syracuseStep 4599845 = 862471) (by norm_num)
theorem B3066563 : Blo 2043435 3066563 := bstep (se 1 (by rfl) ⟨2299922, by rfl⟩ : syracuseStep 3066563 = 4599845) B4599845
theorem B2044375 : Blo 2043435 2044375 := bstep (se 1 (by rfl) ⟨1533281, by rfl⟩ : syracuseStep 2044375 = 3066563) B3066563
theorem B5174837 : Blo 2043435 5174837 := bbase (se 5 (by rfl) ⟨242570, by rfl⟩ : syracuseStep 5174837 = 485141) (by norm_num)
theorem B3449891 : Blo 2043435 3449891 := bstep (se 1 (by rfl) ⟨2587418, by rfl⟩ : syracuseStep 3449891 = 5174837) B5174837
theorem B2299927 : Blo 2043435 2299927 := bstep (se 1 (by rfl) ⟨1724945, by rfl⟩ : syracuseStep 2299927 = 3449891) B3449891
theorem B3066569 : Blo 2043435 3066569 := bstep (se 2 (by rfl) ⟨1149963, by rfl⟩ : syracuseStep 3066569 = 2299927) B2299927
theorem B2044379 : Blo 2043435 2044379 := bstep (se 1 (by rfl) ⟨1533284, by rfl⟩ : syracuseStep 2044379 = 3066569) B3066569
theorem B2212925 : Blo 2043435 2212925 := bbase (se 3 (by rfl) ⟨414923, by rfl⟩ : syracuseStep 2212925 = 829847) (by norm_num)
theorem B23604533 : Blo 2043435 23604533 := bstep (se 5 (by rfl) ⟨1106462, by rfl⟩ : syracuseStep 23604533 = 2212925) B2212925
theorem B15736355 : Blo 2043435 15736355 := bstep (se 1 (by rfl) ⟨11802266, by rfl⟩ : syracuseStep 15736355 = 23604533) B23604533
theorem B10490903 : Blo 2043435 10490903 := bstep (se 1 (by rfl) ⟨7868177, by rfl⟩ : syracuseStep 10490903 = 15736355) B15736355
theorem B6993935 : Blo 2043435 6993935 := bstep (se 1 (by rfl) ⟨5245451, by rfl⟩ : syracuseStep 6993935 = 10490903) B10490903
theorem B4662623 : Blo 2043435 4662623 := bstep (se 1 (by rfl) ⟨3496967, by rfl⟩ : syracuseStep 4662623 = 6993935) B6993935
theorem B12433661 : Blo 2043435 12433661 := bstep (se 3 (by rfl) ⟨2331311, by rfl⟩ : syracuseStep 12433661 = 4662623) B4662623
theorem B8289107 : Blo 2043435 8289107 := bstep (se 1 (by rfl) ⟨6216830, by rfl⟩ : syracuseStep 8289107 = 12433661) B12433661
theorem B5526071 : Blo 2043435 5526071 := bstep (se 1 (by rfl) ⟨4144553, by rfl⟩ : syracuseStep 5526071 = 8289107) B8289107
theorem B3684047 : Blo 2043435 3684047 := bstep (se 1 (by rfl) ⟨2763035, by rfl⟩ : syracuseStep 3684047 = 5526071) B5526071
theorem B9824125 : Blo 2043435 9824125 := bstep (se 3 (by rfl) ⟨1842023, by rfl⟩ : syracuseStep 9824125 = 3684047) B3684047
theorem B13098833 : Blo 2043435 13098833 := bstep (se 2 (by rfl) ⟨4912062, by rfl⟩ : syracuseStep 13098833 = 9824125) B9824125
theorem B8732555 : Blo 2043435 8732555 := bstep (se 1 (by rfl) ⟨6549416, by rfl⟩ : syracuseStep 8732555 = 13098833) B13098833
theorem B5821703 : Blo 2043435 5821703 := bstep (se 1 (by rfl) ⟨4366277, by rfl⟩ : syracuseStep 5821703 = 8732555) B8732555
theorem B3881135 : Blo 2043435 3881135 := bstep (se 1 (by rfl) ⟨2910851, by rfl⟩ : syracuseStep 3881135 = 5821703) B5821703
theorem B10349693 : Blo 2043435 10349693 := bstep (se 3 (by rfl) ⟨1940567, by rfl⟩ : syracuseStep 10349693 = 3881135) B3881135
theorem B6899795 : Blo 2043435 6899795 := bstep (se 1 (by rfl) ⟨5174846, by rfl⟩ : syracuseStep 6899795 = 10349693) B10349693
theorem B4599863 : Blo 2043435 4599863 := bstep (se 1 (by rfl) ⟨3449897, by rfl⟩ : syracuseStep 4599863 = 6899795) B6899795
theorem B3066575 : Blo 2043435 3066575 := bstep (se 1 (by rfl) ⟨2299931, by rfl⟩ : syracuseStep 3066575 = 4599863) B4599863
theorem B2044383 : Blo 2043435 2044383 := bstep (se 1 (by rfl) ⟨1533287, by rfl⟩ : syracuseStep 2044383 = 3066575) B3066575
theorem B3066581 : Blo 2043435 3066581 := bbase (se 7 (by rfl) ⟨35936, by rfl⟩ : syracuseStep 3066581 = 71873) (by norm_num)
theorem B2044387 : Blo 2043435 2044387 := bstep (se 1 (by rfl) ⟨1533290, by rfl⟩ : syracuseStep 2044387 = 3066581) B3066581
theorem B9824165 : Blo 2043435 9824165 := bbase (se 4 (by rfl) ⟨921015, by rfl⟩ : syracuseStep 9824165 = 1842031) (by norm_num)
theorem B6549443 : Blo 2043435 6549443 := bstep (se 1 (by rfl) ⟨4912082, by rfl⟩ : syracuseStep 6549443 = 9824165) B9824165
theorem B4366295 : Blo 2043435 4366295 := bstep (se 1 (by rfl) ⟨3274721, by rfl⟩ : syracuseStep 4366295 = 6549443) B6549443
theorem B2910863 : Blo 2043435 2910863 := bstep (se 1 (by rfl) ⟨2183147, by rfl⟩ : syracuseStep 2910863 = 4366295) B4366295
theorem B7762301 : Blo 2043435 7762301 := bstep (se 3 (by rfl) ⟨1455431, by rfl⟩ : syracuseStep 7762301 = 2910863) B2910863
theorem B5174867 : Blo 2043435 5174867 := bstep (se 1 (by rfl) ⟨3881150, by rfl⟩ : syracuseStep 5174867 = 7762301) B7762301
theorem B3449911 : Blo 2043435 3449911 := bstep (se 1 (by rfl) ⟨2587433, by rfl⟩ : syracuseStep 3449911 = 5174867) B5174867
theorem B4599881 : Blo 2043435 4599881 := bstep (se 2 (by rfl) ⟨1724955, by rfl⟩ : syracuseStep 4599881 = 3449911) B3449911
theorem B3066587 : Blo 2043435 3066587 := bstep (se 1 (by rfl) ⟨2299940, by rfl⟩ : syracuseStep 3066587 = 4599881) B4599881
theorem B2044391 : Blo 2043435 2044391 := bstep (se 1 (by rfl) ⟨1533293, by rfl⟩ : syracuseStep 2044391 = 3066587) B3066587
theorem B2299945 : Blo 2043435 2299945 := bbase (se 2 (by rfl) ⟨862479, by rfl⟩ : syracuseStep 2299945 = 1724959) (by norm_num)
theorem B3066593 : Blo 2043435 3066593 := bstep (se 2 (by rfl) ⟨1149972, by rfl⟩ : syracuseStep 3066593 = 2299945) B2299945
theorem B2044395 : Blo 2043435 2044395 := bstep (se 1 (by rfl) ⟨1533296, by rfl⟩ : syracuseStep 2044395 = 3066593) B3066593
theorem B6993989 : Blo 2043435 6993989 := bbase (se 4 (by rfl) ⟨655686, by rfl⟩ : syracuseStep 6993989 = 1311373) (by norm_num)
theorem B4662659 : Blo 2043435 4662659 := bstep (se 1 (by rfl) ⟨3496994, by rfl⟩ : syracuseStep 4662659 = 6993989) B6993989
theorem B3108439 : Blo 2043435 3108439 := bstep (se 1 (by rfl) ⟨2331329, by rfl⟩ : syracuseStep 3108439 = 4662659) B4662659
theorem B16578341 : Blo 2043435 16578341 := bstep (se 4 (by rfl) ⟨1554219, by rfl⟩ : syracuseStep 16578341 = 3108439) B3108439
theorem B11052227 : Blo 2043435 11052227 := bstep (se 1 (by rfl) ⟨8289170, by rfl⟩ : syracuseStep 11052227 = 16578341) B16578341
theorem B29472605 : Blo 2043435 29472605 := bstep (se 3 (by rfl) ⟨5526113, by rfl⟩ : syracuseStep 29472605 = 11052227) B11052227
theorem B19648403 : Blo 2043435 19648403 := bstep (se 1 (by rfl) ⟨14736302, by rfl⟩ : syracuseStep 19648403 = 29472605) B29472605
theorem B13098935 : Blo 2043435 13098935 := bstep (se 1 (by rfl) ⟨9824201, by rfl⟩ : syracuseStep 13098935 = 19648403) B19648403
theorem B8732623 : Blo 2043435 8732623 := bstep (se 1 (by rfl) ⟨6549467, by rfl⟩ : syracuseStep 8732623 = 13098935) B13098935
theorem B11643497 : Blo 2043435 11643497 := bstep (se 2 (by rfl) ⟨4366311, by rfl⟩ : syracuseStep 11643497 = 8732623) B8732623
theorem B7762331 : Blo 2043435 7762331 := bstep (se 1 (by rfl) ⟨5821748, by rfl⟩ : syracuseStep 7762331 = 11643497) B11643497
theorem B5174887 : Blo 2043435 5174887 := bstep (se 1 (by rfl) ⟨3881165, by rfl⟩ : syracuseStep 5174887 = 7762331) B7762331
theorem B6899849 : Blo 2043435 6899849 := bstep (se 2 (by rfl) ⟨2587443, by rfl⟩ : syracuseStep 6899849 = 5174887) B5174887
theorem B4599899 : Blo 2043435 4599899 := bstep (se 1 (by rfl) ⟨3449924, by rfl⟩ : syracuseStep 4599899 = 6899849) B6899849
theorem B3066599 : Blo 2043435 3066599 := bstep (se 1 (by rfl) ⟨2299949, by rfl⟩ : syracuseStep 3066599 = 4599899) B4599899
theorem B2044399 : Blo 2043435 2044399 := bstep (se 1 (by rfl) ⟨1533299, by rfl⟩ : syracuseStep 2044399 = 3066599) B3066599
theorem B3066605 : Blo 2043435 3066605 := bbase (se 3 (by rfl) ⟨574988, by rfl⟩ : syracuseStep 3066605 = 1149977) (by norm_num)
theorem B2044403 : Blo 2043435 2044403 := bstep (se 1 (by rfl) ⟨1533302, by rfl⟩ : syracuseStep 2044403 = 3066605) B3066605
theorem B4599917 : Blo 2043435 4599917 := bbase (se 3 (by rfl) ⟨862484, by rfl⟩ : syracuseStep 4599917 = 1724969) (by norm_num)
theorem B3066611 : Blo 2043435 3066611 := bstep (se 1 (by rfl) ⟨2299958, by rfl⟩ : syracuseStep 3066611 = 4599917) B4599917
theorem B2044407 : Blo 2043435 2044407 := bstep (se 1 (by rfl) ⟨1533305, by rfl⟩ : syracuseStep 2044407 = 3066611) B3066611
theorem B3881189 : Blo 2043435 3881189 := bbase (se 4 (by rfl) ⟨363861, by rfl⟩ : syracuseStep 3881189 = 727723) (by norm_num)
theorem B2587459 : Blo 2043435 2587459 := bstep (se 1 (by rfl) ⟨1940594, by rfl⟩ : syracuseStep 2587459 = 3881189) B3881189
theorem B3449945 : Blo 2043435 3449945 := bstep (se 2 (by rfl) ⟨1293729, by rfl⟩ : syracuseStep 3449945 = 2587459) B2587459
theorem B2299963 : Blo 2043435 2299963 := bstep (se 1 (by rfl) ⟨1724972, by rfl⟩ : syracuseStep 2299963 = 3449945) B3449945
theorem B3066617 : Blo 2043435 3066617 := bstep (se 2 (by rfl) ⟨1149981, by rfl⟩ : syracuseStep 3066617 = 2299963) B2299963
theorem B2044411 : Blo 2043435 2044411 := bstep (se 1 (by rfl) ⟨1533308, by rfl⟩ : syracuseStep 2044411 = 3066617) B3066617
theorem B39297109 : Blo 2043435 39297109 := bbase (se 8 (by rfl) ⟨230256, by rfl⟩ : syracuseStep 39297109 = 460513) (by norm_num)
theorem B52396145 : Blo 2043435 52396145 := bstep (se 2 (by rfl) ⟨19648554, by rfl⟩ : syracuseStep 52396145 = 39297109) B39297109
theorem B34930763 : Blo 2043435 34930763 := bstep (se 1 (by rfl) ⟨26198072, by rfl⟩ : syracuseStep 34930763 = 52396145) B52396145
theorem B23287175 : Blo 2043435 23287175 := bstep (se 1 (by rfl) ⟨17465381, by rfl⟩ : syracuseStep 23287175 = 34930763) B34930763
theorem B15524783 : Blo 2043435 15524783 := bstep (se 1 (by rfl) ⟨11643587, by rfl⟩ : syracuseStep 15524783 = 23287175) B23287175
theorem B10349855 : Blo 2043435 10349855 := bstep (se 1 (by rfl) ⟨7762391, by rfl⟩ : syracuseStep 10349855 = 15524783) B15524783
theorem B6899903 : Blo 2043435 6899903 := bstep (se 1 (by rfl) ⟨5174927, by rfl⟩ : syracuseStep 6899903 = 10349855) B10349855
theorem B4599935 : Blo 2043435 4599935 := bstep (se 1 (by rfl) ⟨3449951, by rfl⟩ : syracuseStep 4599935 = 6899903) B6899903
theorem B3066623 : Blo 2043435 3066623 := bstep (se 1 (by rfl) ⟨2299967, by rfl⟩ : syracuseStep 3066623 = 4599935) B4599935
theorem B2044415 : Blo 2043435 2044415 := bstep (se 1 (by rfl) ⟨1533311, by rfl⟩ : syracuseStep 2044415 = 3066623) B3066623
theorem B3066629 : Blo 2043435 3066629 := bbase (se 4 (by rfl) ⟨287496, by rfl⟩ : syracuseStep 3066629 = 574993) (by norm_num)
theorem B2044419 : Blo 2043435 2044419 := bstep (se 1 (by rfl) ⟨1533314, by rfl⟩ : syracuseStep 2044419 = 3066629) B3066629
theorem B3449965 : Blo 2043435 3449965 := bbase (se 3 (by rfl) ⟨646868, by rfl⟩ : syracuseStep 3449965 = 1293737) (by norm_num)
theorem B4599953 : Blo 2043435 4599953 := bstep (se 2 (by rfl) ⟨1724982, by rfl⟩ : syracuseStep 4599953 = 3449965) B3449965
theorem B3066635 : Blo 2043435 3066635 := bstep (se 1 (by rfl) ⟨2299976, by rfl⟩ : syracuseStep 3066635 = 4599953) B4599953
theorem B2044423 : Blo 2043435 2044423 := bstep (se 1 (by rfl) ⟨1533317, by rfl⟩ : syracuseStep 2044423 = 3066635) B3066635
theorem B2299981 : Blo 2043435 2299981 := bbase (se 3 (by rfl) ⟨431246, by rfl⟩ : syracuseStep 2299981 = 862493) (by norm_num)
theorem B3066641 : Blo 2043435 3066641 := bstep (se 2 (by rfl) ⟨1149990, by rfl⟩ : syracuseStep 3066641 = 2299981) B2299981
theorem B2044427 : Blo 2043435 2044427 := bstep (se 1 (by rfl) ⟨1533320, by rfl⟩ : syracuseStep 2044427 = 3066641) B3066641
theorem B6899957 : Blo 2043435 6899957 := bbase (se 5 (by rfl) ⟨323435, by rfl⟩ : syracuseStep 6899957 = 646871) (by norm_num)
theorem B4599971 : Blo 2043435 4599971 := bstep (se 1 (by rfl) ⟨3449978, by rfl⟩ : syracuseStep 4599971 = 6899957) B6899957
theorem B3066647 : Blo 2043435 3066647 := bstep (se 1 (by rfl) ⟨2299985, by rfl⟩ : syracuseStep 3066647 = 4599971) B4599971
theorem B2044431 : Blo 2043435 2044431 := bstep (se 1 (by rfl) ⟨1533323, by rfl⟩ : syracuseStep 2044431 = 3066647) B3066647
theorem B3066653 : Blo 2043435 3066653 := bbase (se 3 (by rfl) ⟨574997, by rfl⟩ : syracuseStep 3066653 = 1149995) (by norm_num)
theorem B2044435 : Blo 2043435 2044435 := bstep (se 1 (by rfl) ⟨1533326, by rfl⟩ : syracuseStep 2044435 = 3066653) B3066653
theorem B4599989 : Blo 2043435 4599989 := bbase (se 5 (by rfl) ⟨215624, by rfl⟩ : syracuseStep 4599989 = 431249) (by norm_num)
theorem B3066659 : Blo 2043435 3066659 := bstep (se 1 (by rfl) ⟨2299994, by rfl⟩ : syracuseStep 3066659 = 4599989) B4599989
theorem B2044439 : Blo 2043435 2044439 := bstep (se 1 (by rfl) ⟨1533329, by rfl⟩ : syracuseStep 2044439 = 3066659) B3066659
theorem B3274805 : Blo 2043435 3274805 := bbase (se 5 (by rfl) ⟨153506, by rfl⟩ : syracuseStep 3274805 = 307013) (by norm_num)
theorem B2183203 : Blo 2043435 2183203 := bstep (se 1 (by rfl) ⟨1637402, by rfl⟩ : syracuseStep 2183203 = 3274805) B3274805
theorem B11643749 : Blo 2043435 11643749 := bstep (se 4 (by rfl) ⟨1091601, by rfl⟩ : syracuseStep 11643749 = 2183203) B2183203
theorem B7762499 : Blo 2043435 7762499 := bstep (se 1 (by rfl) ⟨5821874, by rfl⟩ : syracuseStep 7762499 = 11643749) B11643749
theorem B5174999 : Blo 2043435 5174999 := bstep (se 1 (by rfl) ⟨3881249, by rfl⟩ : syracuseStep 5174999 = 7762499) B7762499
theorem B3449999 : Blo 2043435 3449999 := bstep (se 1 (by rfl) ⟨2587499, by rfl⟩ : syracuseStep 3449999 = 5174999) B5174999
theorem B2299999 : Blo 2043435 2299999 := bstep (se 1 (by rfl) ⟨1724999, by rfl⟩ : syracuseStep 2299999 = 3449999) B3449999
theorem B3066665 : Blo 2043435 3066665 := bstep (se 2 (by rfl) ⟨1149999, by rfl⟩ : syracuseStep 3066665 = 2299999) B2299999
theorem B2044443 : Blo 2043435 2044443 := bstep (se 1 (by rfl) ⟨1533332, by rfl⟩ : syracuseStep 2044443 = 3066665) B3066665
theorem B5526245 : Blo 2043435 5526245 := bbase (se 4 (by rfl) ⟨518085, by rfl⟩ : syracuseStep 5526245 = 1036171) (by norm_num)
theorem B3684163 : Blo 2043435 3684163 := bstep (se 1 (by rfl) ⟨2763122, by rfl⟩ : syracuseStep 3684163 = 5526245) B5526245
theorem B4912217 : Blo 2043435 4912217 := bstep (se 2 (by rfl) ⟨1842081, by rfl⟩ : syracuseStep 4912217 = 3684163) B3684163
theorem B3274811 : Blo 2043435 3274811 := bstep (se 1 (by rfl) ⟨2456108, by rfl⟩ : syracuseStep 3274811 = 4912217) B4912217
theorem B2183207 : Blo 2043435 2183207 := bstep (se 1 (by rfl) ⟨1637405, by rfl⟩ : syracuseStep 2183207 = 3274811) B3274811
theorem B5821885 : Blo 2043435 5821885 := bstep (se 3 (by rfl) ⟨1091603, by rfl⟩ : syracuseStep 5821885 = 2183207) B2183207
theorem B7762513 : Blo 2043435 7762513 := bstep (se 2 (by rfl) ⟨2910942, by rfl⟩ : syracuseStep 7762513 = 5821885) B5821885
theorem B10350017 : Blo 2043435 10350017 := bstep (se 2 (by rfl) ⟨3881256, by rfl⟩ : syracuseStep 10350017 = 7762513) B7762513
theorem B6900011 : Blo 2043435 6900011 := bstep (se 1 (by rfl) ⟨5175008, by rfl⟩ : syracuseStep 6900011 = 10350017) B10350017
theorem B4600007 : Blo 2043435 4600007 := bstep (se 1 (by rfl) ⟨3450005, by rfl⟩ : syracuseStep 4600007 = 6900011) B6900011
theorem B3066671 : Blo 2043435 3066671 := bstep (se 1 (by rfl) ⟨2300003, by rfl⟩ : syracuseStep 3066671 = 4600007) B4600007
theorem B2044447 : Blo 2043435 2044447 := bstep (se 1 (by rfl) ⟨1533335, by rfl⟩ : syracuseStep 2044447 = 3066671) B3066671
theorem B3066677 : Blo 2043435 3066677 := bbase (se 5 (by rfl) ⟨143750, by rfl⟩ : syracuseStep 3066677 = 287501) (by norm_num)
theorem B2044451 : Blo 2043435 2044451 := bstep (se 1 (by rfl) ⟨1533338, by rfl⟩ : syracuseStep 2044451 = 3066677) B3066677
theorem B5175029 : Blo 2043435 5175029 := bbase (se 5 (by rfl) ⟨242579, by rfl⟩ : syracuseStep 5175029 = 485159) (by norm_num)
theorem B3450019 : Blo 2043435 3450019 := bstep (se 1 (by rfl) ⟨2587514, by rfl⟩ : syracuseStep 3450019 = 5175029) B5175029
theorem B4600025 : Blo 2043435 4600025 := bstep (se 2 (by rfl) ⟨1725009, by rfl⟩ : syracuseStep 4600025 = 3450019) B3450019
theorem B3066683 : Blo 2043435 3066683 := bstep (se 1 (by rfl) ⟨2300012, by rfl⟩ : syracuseStep 3066683 = 4600025) B4600025
theorem B2044455 : Blo 2043435 2044455 := bstep (se 1 (by rfl) ⟨1533341, by rfl⟩ : syracuseStep 2044455 = 3066683) B3066683
theorem B2300017 : Blo 2043435 2300017 := bbase (se 2 (by rfl) ⟨862506, by rfl⟩ : syracuseStep 2300017 = 1725013) (by norm_num)
theorem B3066689 : Blo 2043435 3066689 := bstep (se 2 (by rfl) ⟨1150008, by rfl⟩ : syracuseStep 3066689 = 2300017) B2300017
theorem B2044459 : Blo 2043435 2044459 := bstep (se 1 (by rfl) ⟨1533344, by rfl⟩ : syracuseStep 2044459 = 3066689) B3066689
theorem B3319517 : Blo 2043435 3319517 := bbase (se 3 (by rfl) ⟨622409, by rfl⟩ : syracuseStep 3319517 = 1244819) (by norm_num)
theorem B8852045 : Blo 2043435 8852045 := bstep (se 3 (by rfl) ⟨1659758, by rfl⟩ : syracuseStep 8852045 = 3319517) B3319517
theorem B23605453 : Blo 2043435 23605453 := bstep (se 3 (by rfl) ⟨4426022, by rfl⟩ : syracuseStep 23605453 = 8852045) B8852045
theorem B31473937 : Blo 2043435 31473937 := bstep (se 2 (by rfl) ⟨11802726, by rfl⟩ : syracuseStep 31473937 = 23605453) B23605453
theorem B41965249 : Blo 2043435 41965249 := bstep (se 2 (by rfl) ⟨15736968, by rfl⟩ : syracuseStep 41965249 = 31473937) B31473937
theorem B55953665 : Blo 2043435 55953665 := bstep (se 2 (by rfl) ⟨20982624, by rfl⟩ : syracuseStep 55953665 = 41965249) B41965249
theorem B37302443 : Blo 2043435 37302443 := bstep (se 1 (by rfl) ⟨27976832, by rfl⟩ : syracuseStep 37302443 = 55953665) B55953665
theorem B24868295 : Blo 2043435 24868295 := bstep (se 1 (by rfl) ⟨18651221, by rfl⟩ : syracuseStep 24868295 = 37302443) B37302443
theorem B16578863 : Blo 2043435 16578863 := bstep (se 1 (by rfl) ⟨12434147, by rfl⟩ : syracuseStep 16578863 = 24868295) B24868295
theorem B11052575 : Blo 2043435 11052575 := bstep (se 1 (by rfl) ⟨8289431, by rfl⟩ : syracuseStep 11052575 = 16578863) B16578863
theorem B7368383 : Blo 2043435 7368383 := bstep (se 1 (by rfl) ⟨5526287, by rfl⟩ : syracuseStep 7368383 = 11052575) B11052575
theorem B4912255 : Blo 2043435 4912255 := bstep (se 1 (by rfl) ⟨3684191, by rfl⟩ : syracuseStep 4912255 = 7368383) B7368383
theorem B6549673 : Blo 2043435 6549673 := bstep (se 2 (by rfl) ⟨2456127, by rfl⟩ : syracuseStep 6549673 = 4912255) B4912255
theorem B8732897 : Blo 2043435 8732897 := bstep (se 2 (by rfl) ⟨3274836, by rfl⟩ : syracuseStep 8732897 = 6549673) B6549673
theorem B5821931 : Blo 2043435 5821931 := bstep (se 1 (by rfl) ⟨4366448, by rfl⟩ : syracuseStep 5821931 = 8732897) B8732897
theorem B3881287 : Blo 2043435 3881287 := bstep (se 1 (by rfl) ⟨2910965, by rfl⟩ : syracuseStep 3881287 = 5821931) B5821931
theorem B5175049 : Blo 2043435 5175049 := bstep (se 2 (by rfl) ⟨1940643, by rfl⟩ : syracuseStep 5175049 = 3881287) B3881287
theorem B6900065 : Blo 2043435 6900065 := bstep (se 2 (by rfl) ⟨2587524, by rfl⟩ : syracuseStep 6900065 = 5175049) B5175049
theorem B4600043 : Blo 2043435 4600043 := bstep (se 1 (by rfl) ⟨3450032, by rfl⟩ : syracuseStep 4600043 = 6900065) B6900065
theorem B3066695 : Blo 2043435 3066695 := bstep (se 1 (by rfl) ⟨2300021, by rfl⟩ : syracuseStep 3066695 = 4600043) B4600043
theorem B2044463 : Blo 2043435 2044463 := bstep (se 1 (by rfl) ⟨1533347, by rfl⟩ : syracuseStep 2044463 = 3066695) B3066695
theorem B3066701 : Blo 2043435 3066701 := bbase (se 3 (by rfl) ⟨575006, by rfl⟩ : syracuseStep 3066701 = 1150013) (by norm_num)
theorem B2044467 : Blo 2043435 2044467 := bstep (se 1 (by rfl) ⟨1533350, by rfl⟩ : syracuseStep 2044467 = 3066701) B3066701
theorem B4600061 : Blo 2043435 4600061 := bbase (se 3 (by rfl) ⟨862511, by rfl⟩ : syracuseStep 4600061 = 1725023) (by norm_num)
theorem B3066707 : Blo 2043435 3066707 := bstep (se 1 (by rfl) ⟨2300030, by rfl⟩ : syracuseStep 3066707 = 4600061) B4600061
theorem B2044471 : Blo 2043435 2044471 := bstep (se 1 (by rfl) ⟨1533353, by rfl⟩ : syracuseStep 2044471 = 3066707) B3066707
theorem B3450053 : Blo 2043435 3450053 := bbase (se 4 (by rfl) ⟨323442, by rfl⟩ : syracuseStep 3450053 = 646885) (by norm_num)
theorem B2300035 : Blo 2043435 2300035 := bstep (se 1 (by rfl) ⟨1725026, by rfl⟩ : syracuseStep 2300035 = 3450053) B3450053
theorem B3066713 : Blo 2043435 3066713 := bstep (se 2 (by rfl) ⟨1150017, by rfl⟩ : syracuseStep 3066713 = 2300035) B2300035
theorem B2044475 : Blo 2043435 2044475 := bstep (se 1 (by rfl) ⟨1533356, by rfl⟩ : syracuseStep 2044475 = 3066713) B3066713
theorem B15525269 : Blo 2043435 15525269 := bbase (se 6 (by rfl) ⟨363873, by rfl⟩ : syracuseStep 15525269 = 727747) (by norm_num)
theorem B10350179 : Blo 2043435 10350179 := bstep (se 1 (by rfl) ⟨7762634, by rfl⟩ : syracuseStep 10350179 = 15525269) B15525269
theorem B6900119 : Blo 2043435 6900119 := bstep (se 1 (by rfl) ⟨5175089, by rfl⟩ : syracuseStep 6900119 = 10350179) B10350179
theorem B4600079 : Blo 2043435 4600079 := bstep (se 1 (by rfl) ⟨3450059, by rfl⟩ : syracuseStep 4600079 = 6900119) B6900119
theorem B3066719 : Blo 2043435 3066719 := bstep (se 1 (by rfl) ⟨2300039, by rfl⟩ : syracuseStep 3066719 = 4600079) B4600079
theorem B2044479 : Blo 2043435 2044479 := bstep (se 1 (by rfl) ⟨1533359, by rfl⟩ : syracuseStep 2044479 = 3066719) B3066719
theorem B3066725 : Blo 2043435 3066725 := bbase (se 4 (by rfl) ⟨287505, by rfl⟩ : syracuseStep 3066725 = 575011) (by norm_num)
theorem B2044483 : Blo 2043435 2044483 := bstep (se 1 (by rfl) ⟨1533362, by rfl⟩ : syracuseStep 2044483 = 3066725) B3066725
theorem B3881333 : Blo 2043435 3881333 := bbase (se 5 (by rfl) ⟨181937, by rfl⟩ : syracuseStep 3881333 = 363875) (by norm_num)
theorem B2587555 : Blo 2043435 2587555 := bstep (se 1 (by rfl) ⟨1940666, by rfl⟩ : syracuseStep 2587555 = 3881333) B3881333
theorem B3450073 : Blo 2043435 3450073 := bstep (se 2 (by rfl) ⟨1293777, by rfl⟩ : syracuseStep 3450073 = 2587555) B2587555
theorem B4600097 : Blo 2043435 4600097 := bstep (se 2 (by rfl) ⟨1725036, by rfl⟩ : syracuseStep 4600097 = 3450073) B3450073
theorem B3066731 : Blo 2043435 3066731 := bstep (se 1 (by rfl) ⟨2300048, by rfl⟩ : syracuseStep 3066731 = 4600097) B4600097
theorem B2044487 : Blo 2043435 2044487 := bstep (se 1 (by rfl) ⟨1533365, by rfl⟩ : syracuseStep 2044487 = 3066731) B3066731
theorem B2300053 : Blo 2043435 2300053 := bbase (se 6 (by rfl) ⟨53907, by rfl⟩ : syracuseStep 2300053 = 107815) (by norm_num)
theorem B3066737 : Blo 2043435 3066737 := bstep (se 2 (by rfl) ⟨1150026, by rfl⟩ : syracuseStep 3066737 = 2300053) B2300053
theorem B2044491 : Blo 2043435 2044491 := bstep (se 1 (by rfl) ⟨1533368, by rfl⟩ : syracuseStep 2044491 = 3066737) B3066737
theorem B2587565 : Blo 2043435 2587565 := bbase (se 3 (by rfl) ⟨485168, by rfl⟩ : syracuseStep 2587565 = 970337) (by norm_num)
theorem B6900173 : Blo 2043435 6900173 := bstep (se 3 (by rfl) ⟨1293782, by rfl⟩ : syracuseStep 6900173 = 2587565) B2587565
theorem B4600115 : Blo 2043435 4600115 := bstep (se 1 (by rfl) ⟨3450086, by rfl⟩ : syracuseStep 4600115 = 6900173) B6900173
theorem B3066743 : Blo 2043435 3066743 := bstep (se 1 (by rfl) ⟨2300057, by rfl⟩ : syracuseStep 3066743 = 4600115) B4600115
theorem B2044495 : Blo 2043435 2044495 := bstep (se 1 (by rfl) ⟨1533371, by rfl⟩ : syracuseStep 2044495 = 3066743) B3066743
theorem B3066749 : Blo 2043435 3066749 := bbase (se 3 (by rfl) ⟨575015, by rfl⟩ : syracuseStep 3066749 = 1150031) (by norm_num)
theorem B2044499 : Blo 2043435 2044499 := bstep (se 1 (by rfl) ⟨1533374, by rfl⟩ : syracuseStep 2044499 = 3066749) B3066749
theorem B4600133 : Blo 2043435 4600133 := bbase (se 4 (by rfl) ⟨431262, by rfl⟩ : syracuseStep 4600133 = 862525) (by norm_num)
theorem B3066755 : Blo 2043435 3066755 := bstep (se 1 (by rfl) ⟨2300066, by rfl⟩ : syracuseStep 3066755 = 4600133) B4600133
theorem B2044503 : Blo 2043435 2044503 := bstep (se 1 (by rfl) ⟨1533377, by rfl⟩ : syracuseStep 2044503 = 3066755) B3066755
theorem B9325813 : Blo 2043435 9325813 := bbase (se 5 (by rfl) ⟨437147, by rfl⟩ : syracuseStep 9325813 = 874295) (by norm_num)
theorem B12434417 : Blo 2043435 12434417 := bstep (se 2 (by rfl) ⟨4662906, by rfl⟩ : syracuseStep 12434417 = 9325813) B9325813
theorem B8289611 : Blo 2043435 8289611 := bstep (se 1 (by rfl) ⟨6217208, by rfl⟩ : syracuseStep 8289611 = 12434417) B12434417
theorem B5526407 : Blo 2043435 5526407 := bstep (se 1 (by rfl) ⟨4144805, by rfl⟩ : syracuseStep 5526407 = 8289611) B8289611
theorem B14737085 : Blo 2043435 14737085 := bstep (se 3 (by rfl) ⟨2763203, by rfl⟩ : syracuseStep 14737085 = 5526407) B5526407
theorem B9824723 : Blo 2043435 9824723 := bstep (se 1 (by rfl) ⟨7368542, by rfl⟩ : syracuseStep 9824723 = 14737085) B14737085
theorem B6549815 : Blo 2043435 6549815 := bstep (se 1 (by rfl) ⟨4912361, by rfl⟩ : syracuseStep 6549815 = 9824723) B9824723
theorem B4366543 : Blo 2043435 4366543 := bstep (se 1 (by rfl) ⟨3274907, by rfl⟩ : syracuseStep 4366543 = 6549815) B6549815
theorem B5822057 : Blo 2043435 5822057 := bstep (se 2 (by rfl) ⟨2183271, by rfl⟩ : syracuseStep 5822057 = 4366543) B4366543
theorem B3881371 : Blo 2043435 3881371 := bstep (se 1 (by rfl) ⟨2911028, by rfl⟩ : syracuseStep 3881371 = 5822057) B5822057
theorem B5175161 : Blo 2043435 5175161 := bstep (se 2 (by rfl) ⟨1940685, by rfl⟩ : syracuseStep 5175161 = 3881371) B3881371
theorem B3450107 : Blo 2043435 3450107 := bstep (se 1 (by rfl) ⟨2587580, by rfl⟩ : syracuseStep 3450107 = 5175161) B5175161
theorem B2300071 : Blo 2043435 2300071 := bstep (se 1 (by rfl) ⟨1725053, by rfl⟩ : syracuseStep 2300071 = 3450107) B3450107
theorem B3066761 : Blo 2043435 3066761 := bstep (se 2 (by rfl) ⟨1150035, by rfl⟩ : syracuseStep 3066761 = 2300071) B2300071
theorem B2044507 : Blo 2043435 2044507 := bstep (se 1 (by rfl) ⟨1533380, by rfl⟩ : syracuseStep 2044507 = 3066761) B3066761
theorem B10350341 : Blo 2043435 10350341 := bbase (se 4 (by rfl) ⟨970344, by rfl⟩ : syracuseStep 10350341 = 1940689) (by norm_num)
theorem B6900227 : Blo 2043435 6900227 := bstep (se 1 (by rfl) ⟨5175170, by rfl⟩ : syracuseStep 6900227 = 10350341) B10350341
theorem B4600151 : Blo 2043435 4600151 := bstep (se 1 (by rfl) ⟨3450113, by rfl⟩ : syracuseStep 4600151 = 6900227) B6900227
theorem B3066767 : Blo 2043435 3066767 := bstep (se 1 (by rfl) ⟨2300075, by rfl⟩ : syracuseStep 3066767 = 4600151) B4600151
theorem B2044511 : Blo 2043435 2044511 := bstep (se 1 (by rfl) ⟨1533383, by rfl⟩ : syracuseStep 2044511 = 3066767) B3066767
theorem B3066773 : Blo 2043435 3066773 := bbase (se 6 (by rfl) ⟨71877, by rfl⟩ : syracuseStep 3066773 = 143755) (by norm_num)
theorem B2044515 : Blo 2043435 2044515 := bstep (se 1 (by rfl) ⟨1533386, by rfl⟩ : syracuseStep 2044515 = 3066773) B3066773
theorem B11644181 : Blo 2043435 11644181 := bbase (se 6 (by rfl) ⟨272910, by rfl⟩ : syracuseStep 11644181 = 545821) (by norm_num)
theorem B7762787 : Blo 2043435 7762787 := bstep (se 1 (by rfl) ⟨5822090, by rfl⟩ : syracuseStep 7762787 = 11644181) B11644181
theorem B5175191 : Blo 2043435 5175191 := bstep (se 1 (by rfl) ⟨3881393, by rfl⟩ : syracuseStep 5175191 = 7762787) B7762787
theorem B3450127 : Blo 2043435 3450127 := bstep (se 1 (by rfl) ⟨2587595, by rfl⟩ : syracuseStep 3450127 = 5175191) B5175191
theorem B4600169 : Blo 2043435 4600169 := bstep (se 2 (by rfl) ⟨1725063, by rfl⟩ : syracuseStep 4600169 = 3450127) B3450127
theorem B3066779 : Blo 2043435 3066779 := bstep (se 1 (by rfl) ⟨2300084, by rfl⟩ : syracuseStep 3066779 = 4600169) B4600169
theorem B2044519 : Blo 2043435 2044519 := bstep (se 1 (by rfl) ⟨1533389, by rfl⟩ : syracuseStep 2044519 = 3066779) B3066779
theorem B2300089 : Blo 2043435 2300089 := bbase (se 2 (by rfl) ⟨862533, by rfl⟩ : syracuseStep 2300089 = 1725067) (by norm_num)
theorem B3066785 : Blo 2043435 3066785 := bstep (se 2 (by rfl) ⟨1150044, by rfl⟩ : syracuseStep 3066785 = 2300089) B2300089
theorem B2044523 : Blo 2043435 2044523 := bstep (se 1 (by rfl) ⟨1533392, by rfl⟩ : syracuseStep 2044523 = 3066785) B3066785
theorem B24254741 : Blo 2043435 24254741 := bbase (se 6 (by rfl) ⟨568470, by rfl⟩ : syracuseStep 24254741 = 1136941) (by norm_num)
theorem B16169827 : Blo 2043435 16169827 := bstep (se 1 (by rfl) ⟨12127370, by rfl⟩ : syracuseStep 16169827 = 24254741) B24254741
theorem B21559769 : Blo 2043435 21559769 := bstep (se 2 (by rfl) ⟨8084913, by rfl⟩ : syracuseStep 21559769 = 16169827) B16169827
theorem B14373179 : Blo 2043435 14373179 := bstep (se 1 (by rfl) ⟨10779884, by rfl⟩ : syracuseStep 14373179 = 21559769) B21559769
theorem B9582119 : Blo 2043435 9582119 := bstep (se 1 (by rfl) ⟨7186589, by rfl⟩ : syracuseStep 9582119 = 14373179) B14373179
theorem B6388079 : Blo 2043435 6388079 := bstep (se 1 (by rfl) ⟨4791059, by rfl⟩ : syracuseStep 6388079 = 9582119) B9582119
theorem B17034877 : Blo 2043435 17034877 := bstep (se 3 (by rfl) ⟨3194039, by rfl⟩ : syracuseStep 17034877 = 6388079) B6388079
theorem B22713169 : Blo 2043435 22713169 := bstep (se 2 (by rfl) ⟨8517438, by rfl⟩ : syracuseStep 22713169 = 17034877) B17034877
theorem B30284225 : Blo 2043435 30284225 := bstep (se 2 (by rfl) ⟨11356584, by rfl⟩ : syracuseStep 30284225 = 22713169) B22713169
theorem B20189483 : Blo 2043435 20189483 := bstep (se 1 (by rfl) ⟨15142112, by rfl⟩ : syracuseStep 20189483 = 30284225) B30284225
theorem B13459655 : Blo 2043435 13459655 := bstep (se 1 (by rfl) ⟨10094741, by rfl⟩ : syracuseStep 13459655 = 20189483) B20189483
theorem B35892413 : Blo 2043435 35892413 := bstep (se 3 (by rfl) ⟨6729827, by rfl⟩ : syracuseStep 35892413 = 13459655) B13459655
theorem B23928275 : Blo 2043435 23928275 := bstep (se 1 (by rfl) ⟨17946206, by rfl⟩ : syracuseStep 23928275 = 35892413) B35892413
theorem B15952183 : Blo 2043435 15952183 := bstep (se 1 (by rfl) ⟨11964137, by rfl⟩ : syracuseStep 15952183 = 23928275) B23928275
theorem B85078309 : Blo 2043435 85078309 := bstep (se 4 (by rfl) ⟨7976091, by rfl⟩ : syracuseStep 85078309 = 15952183) B15952183
theorem B113437745 : Blo 2043435 113437745 := bstep (se 2 (by rfl) ⟨42539154, by rfl⟩ : syracuseStep 113437745 = 85078309) B85078309
theorem B75625163 : Blo 2043435 75625163 := bstep (se 1 (by rfl) ⟨56718872, by rfl⟩ : syracuseStep 75625163 = 113437745) B113437745
theorem B50416775 : Blo 2043435 50416775 := bstep (se 1 (by rfl) ⟨37812581, by rfl⟩ : syracuseStep 50416775 = 75625163) B75625163
theorem B33611183 : Blo 2043435 33611183 := bstep (se 1 (by rfl) ⟨25208387, by rfl⟩ : syracuseStep 33611183 = 50416775) B50416775
theorem B22407455 : Blo 2043435 22407455 := bstep (se 1 (by rfl) ⟨16805591, by rfl⟩ : syracuseStep 22407455 = 33611183) B33611183
theorem B59753213 : Blo 2043435 59753213 := bstep (se 3 (by rfl) ⟨11203727, by rfl⟩ : syracuseStep 59753213 = 22407455) B22407455
theorem B39835475 : Blo 2043435 39835475 := bstep (se 1 (by rfl) ⟨29876606, by rfl⟩ : syracuseStep 39835475 = 59753213) B59753213
theorem B26556983 : Blo 2043435 26556983 := bstep (se 1 (by rfl) ⟨19917737, by rfl⟩ : syracuseStep 26556983 = 39835475) B39835475
theorem B17704655 : Blo 2043435 17704655 := bstep (se 1 (by rfl) ⟨13278491, by rfl⟩ : syracuseStep 17704655 = 26556983) B26556983
theorem B11803103 : Blo 2043435 11803103 := bstep (se 1 (by rfl) ⟨8852327, by rfl⟩ : syracuseStep 11803103 = 17704655) B17704655
theorem B7868735 : Blo 2043435 7868735 := bstep (se 1 (by rfl) ⟨5901551, by rfl⟩ : syracuseStep 7868735 = 11803103) B11803103
theorem B5245823 : Blo 2043435 5245823 := bstep (se 1 (by rfl) ⟨3934367, by rfl⟩ : syracuseStep 5245823 = 7868735) B7868735
theorem B3497215 : Blo 2043435 3497215 := bstep (se 1 (by rfl) ⟨2622911, by rfl⟩ : syracuseStep 3497215 = 5245823) B5245823
theorem B4662953 : Blo 2043435 4662953 := bstep (se 2 (by rfl) ⟨1748607, by rfl⟩ : syracuseStep 4662953 = 3497215) B3497215
theorem B3108635 : Blo 2043435 3108635 := bstep (se 1 (by rfl) ⟨2331476, by rfl⟩ : syracuseStep 3108635 = 4662953) B4662953
theorem B2072423 : Blo 2043435 2072423 := bstep (se 1 (by rfl) ⟨1554317, by rfl⟩ : syracuseStep 2072423 = 3108635) B3108635
theorem B5526461 : Blo 2043435 5526461 := bstep (se 3 (by rfl) ⟨1036211, by rfl⟩ : syracuseStep 5526461 = 2072423) B2072423
theorem B3684307 : Blo 2043435 3684307 := bstep (se 1 (by rfl) ⟨2763230, by rfl⟩ : syracuseStep 3684307 = 5526461) B5526461
theorem B4912409 : Blo 2043435 4912409 := bstep (se 2 (by rfl) ⟨1842153, by rfl⟩ : syracuseStep 4912409 = 3684307) B3684307
theorem B3274939 : Blo 2043435 3274939 := bstep (se 1 (by rfl) ⟨2456204, by rfl⟩ : syracuseStep 3274939 = 4912409) B4912409
theorem B4366585 : Blo 2043435 4366585 := bstep (se 2 (by rfl) ⟨1637469, by rfl⟩ : syracuseStep 4366585 = 3274939) B3274939
theorem B5822113 : Blo 2043435 5822113 := bstep (se 2 (by rfl) ⟨2183292, by rfl⟩ : syracuseStep 5822113 = 4366585) B4366585
theorem B7762817 : Blo 2043435 7762817 := bstep (se 2 (by rfl) ⟨2911056, by rfl⟩ : syracuseStep 7762817 = 5822113) B5822113
theorem B5175211 : Blo 2043435 5175211 := bstep (se 1 (by rfl) ⟨3881408, by rfl⟩ : syracuseStep 5175211 = 7762817) B7762817
theorem B6900281 : Blo 2043435 6900281 := bstep (se 2 (by rfl) ⟨2587605, by rfl⟩ : syracuseStep 6900281 = 5175211) B5175211
theorem B4600187 : Blo 2043435 4600187 := bstep (se 1 (by rfl) ⟨3450140, by rfl⟩ : syracuseStep 4600187 = 6900281) B6900281
theorem B3066791 : Blo 2043435 3066791 := bstep (se 1 (by rfl) ⟨2300093, by rfl⟩ : syracuseStep 3066791 = 4600187) B4600187
theorem B2044527 : Blo 2043435 2044527 := bstep (se 1 (by rfl) ⟨1533395, by rfl⟩ : syracuseStep 2044527 = 3066791) B3066791
theorem B3066797 : Blo 2043435 3066797 := bbase (se 3 (by rfl) ⟨575024, by rfl⟩ : syracuseStep 3066797 = 1150049) (by norm_num)
theorem B2044531 : Blo 2043435 2044531 := bstep (se 1 (by rfl) ⟨1533398, by rfl⟩ : syracuseStep 2044531 = 3066797) B3066797
theorem B4600205 : Blo 2043435 4600205 := bbase (se 3 (by rfl) ⟨862538, by rfl⟩ : syracuseStep 4600205 = 1725077) (by norm_num)
theorem B3066803 : Blo 2043435 3066803 := bstep (se 1 (by rfl) ⟨2300102, by rfl⟩ : syracuseStep 3066803 = 4600205) B4600205
theorem B2044535 : Blo 2043435 2044535 := bstep (se 1 (by rfl) ⟨1533401, by rfl⟩ : syracuseStep 2044535 = 3066803) B3066803
theorem B2587621 : Blo 2043435 2587621 := bbase (se 4 (by rfl) ⟨242589, by rfl⟩ : syracuseStep 2587621 = 485179) (by norm_num)
theorem B3450161 : Blo 2043435 3450161 := bstep (se 2 (by rfl) ⟨1293810, by rfl⟩ : syracuseStep 3450161 = 2587621) B2587621
theorem B2300107 : Blo 2043435 2300107 := bstep (se 1 (by rfl) ⟨1725080, by rfl⟩ : syracuseStep 2300107 = 3450161) B3450161
theorem B3066809 : Blo 2043435 3066809 := bstep (se 2 (by rfl) ⟨1150053, by rfl⟩ : syracuseStep 3066809 = 2300107) B2300107
theorem B2044539 : Blo 2043435 2044539 := bstep (se 1 (by rfl) ⟨1533404, by rfl⟩ : syracuseStep 2044539 = 3066809) B3066809
theorem B9325973 : Blo 2043435 9325973 := bbase (se 6 (by rfl) ⟨218577, by rfl⟩ : syracuseStep 9325973 = 437155) (by norm_num)
theorem B24869261 : Blo 2043435 24869261 := bstep (se 3 (by rfl) ⟨4662986, by rfl⟩ : syracuseStep 24869261 = 9325973) B9325973
theorem B16579507 : Blo 2043435 16579507 := bstep (se 1 (by rfl) ⟨12434630, by rfl⟩ : syracuseStep 16579507 = 24869261) B24869261
theorem B22106009 : Blo 2043435 22106009 := bstep (se 2 (by rfl) ⟨8289753, by rfl⟩ : syracuseStep 22106009 = 16579507) B16579507
theorem B14737339 : Blo 2043435 14737339 := bstep (se 1 (by rfl) ⟨11053004, by rfl⟩ : syracuseStep 14737339 = 22106009) B22106009
theorem B19649785 : Blo 2043435 19649785 := bstep (se 2 (by rfl) ⟨7368669, by rfl⟩ : syracuseStep 19649785 = 14737339) B14737339
theorem B26199713 : Blo 2043435 26199713 := bstep (se 2 (by rfl) ⟨9824892, by rfl⟩ : syracuseStep 26199713 = 19649785) B19649785
theorem B17466475 : Blo 2043435 17466475 := bstep (se 1 (by rfl) ⟨13099856, by rfl⟩ : syracuseStep 17466475 = 26199713) B26199713
theorem B23288633 : Blo 2043435 23288633 := bstep (se 2 (by rfl) ⟨8733237, by rfl⟩ : syracuseStep 23288633 = 17466475) B17466475
theorem B15525755 : Blo 2043435 15525755 := bstep (se 1 (by rfl) ⟨11644316, by rfl⟩ : syracuseStep 15525755 = 23288633) B23288633
theorem B10350503 : Blo 2043435 10350503 := bstep (se 1 (by rfl) ⟨7762877, by rfl⟩ : syracuseStep 10350503 = 15525755) B15525755
theorem B6900335 : Blo 2043435 6900335 := bstep (se 1 (by rfl) ⟨5175251, by rfl⟩ : syracuseStep 6900335 = 10350503) B10350503
theorem B4600223 : Blo 2043435 4600223 := bstep (se 1 (by rfl) ⟨3450167, by rfl⟩ : syracuseStep 4600223 = 6900335) B6900335
theorem B3066815 : Blo 2043435 3066815 := bstep (se 1 (by rfl) ⟨2300111, by rfl⟩ : syracuseStep 3066815 = 4600223) B4600223
theorem B2044543 : Blo 2043435 2044543 := bstep (se 1 (by rfl) ⟨1533407, by rfl⟩ : syracuseStep 2044543 = 3066815) B3066815
theorem B3066821 : Blo 2043435 3066821 := bbase (se 4 (by rfl) ⟨287514, by rfl⟩ : syracuseStep 3066821 = 575029) (by norm_num)
theorem B2044547 : Blo 2043435 2044547 := bstep (se 1 (by rfl) ⟨1533410, by rfl⟩ : syracuseStep 2044547 = 3066821) B3066821
theorem B3450181 : Blo 2043435 3450181 := bbase (se 4 (by rfl) ⟨323454, by rfl⟩ : syracuseStep 3450181 = 646909) (by norm_num)
theorem B4600241 : Blo 2043435 4600241 := bstep (se 2 (by rfl) ⟨1725090, by rfl⟩ : syracuseStep 4600241 = 3450181) B3450181
theorem B3066827 : Blo 2043435 3066827 := bstep (se 1 (by rfl) ⟨2300120, by rfl⟩ : syracuseStep 3066827 = 4600241) B4600241
theorem B2044551 : Blo 2043435 2044551 := bstep (se 1 (by rfl) ⟨1533413, by rfl⟩ : syracuseStep 2044551 = 3066827) B3066827
theorem B2300125 : Blo 2043435 2300125 := bbase (se 3 (by rfl) ⟨431273, by rfl⟩ : syracuseStep 2300125 = 862547) (by norm_num)
theorem B3066833 : Blo 2043435 3066833 := bstep (se 2 (by rfl) ⟨1150062, by rfl⟩ : syracuseStep 3066833 = 2300125) B2300125
theorem B2044555 : Blo 2043435 2044555 := bstep (se 1 (by rfl) ⟨1533416, by rfl⟩ : syracuseStep 2044555 = 3066833) B3066833
theorem B6900389 : Blo 2043435 6900389 := bbase (se 4 (by rfl) ⟨646911, by rfl⟩ : syracuseStep 6900389 = 1293823) (by norm_num)
theorem B4600259 : Blo 2043435 4600259 := bstep (se 1 (by rfl) ⟨3450194, by rfl⟩ : syracuseStep 4600259 = 6900389) B6900389
theorem B3066839 : Blo 2043435 3066839 := bstep (se 1 (by rfl) ⟨2300129, by rfl⟩ : syracuseStep 3066839 = 4600259) B4600259
theorem B2044559 : Blo 2043435 2044559 := bstep (se 1 (by rfl) ⟨1533419, by rfl⟩ : syracuseStep 2044559 = 3066839) B3066839
theorem B3066845 : Blo 2043435 3066845 := bbase (se 3 (by rfl) ⟨575033, by rfl⟩ : syracuseStep 3066845 = 1150067) (by norm_num)
theorem B2044563 : Blo 2043435 2044563 := bstep (se 1 (by rfl) ⟨1533422, by rfl⟩ : syracuseStep 2044563 = 3066845) B3066845
theorem B4600277 : Blo 2043435 4600277 := bbase (se 7 (by rfl) ⟨53909, by rfl⟩ : syracuseStep 4600277 = 107819) (by norm_num)
theorem B3066851 : Blo 2043435 3066851 := bstep (se 1 (by rfl) ⟨2300138, by rfl⟩ : syracuseStep 3066851 = 4600277) B4600277
theorem B2044567 : Blo 2043435 2044567 := bstep (se 1 (by rfl) ⟨1533425, by rfl⟩ : syracuseStep 2044567 = 3066851) B3066851
theorem B3108701 : Blo 2043435 3108701 := bbase (se 3 (by rfl) ⟨582881, by rfl⟩ : syracuseStep 3108701 = 1165763) (by norm_num)
theorem B8289869 : Blo 2043435 8289869 := bstep (se 3 (by rfl) ⟨1554350, by rfl⟩ : syracuseStep 8289869 = 3108701) B3108701
theorem B22106317 : Blo 2043435 22106317 := bstep (se 3 (by rfl) ⟨4144934, by rfl⟩ : syracuseStep 22106317 = 8289869) B8289869
theorem B29475089 : Blo 2043435 29475089 := bstep (se 2 (by rfl) ⟨11053158, by rfl⟩ : syracuseStep 29475089 = 22106317) B22106317
theorem B19650059 : Blo 2043435 19650059 := bstep (se 1 (by rfl) ⟨14737544, by rfl⟩ : syracuseStep 19650059 = 29475089) B29475089
theorem B13100039 : Blo 2043435 13100039 := bstep (se 1 (by rfl) ⟨9825029, by rfl⟩ : syracuseStep 13100039 = 19650059) B19650059
theorem B8733359 : Blo 2043435 8733359 := bstep (se 1 (by rfl) ⟨6550019, by rfl⟩ : syracuseStep 8733359 = 13100039) B13100039
theorem B5822239 : Blo 2043435 5822239 := bstep (se 1 (by rfl) ⟨4366679, by rfl⟩ : syracuseStep 5822239 = 8733359) B8733359
theorem B7762985 : Blo 2043435 7762985 := bstep (se 2 (by rfl) ⟨2911119, by rfl⟩ : syracuseStep 7762985 = 5822239) B5822239
theorem B5175323 : Blo 2043435 5175323 := bstep (se 1 (by rfl) ⟨3881492, by rfl⟩ : syracuseStep 5175323 = 7762985) B7762985
theorem B3450215 : Blo 2043435 3450215 := bstep (se 1 (by rfl) ⟨2587661, by rfl⟩ : syracuseStep 3450215 = 5175323) B5175323
theorem B2300143 : Blo 2043435 2300143 := bstep (se 1 (by rfl) ⟨1725107, by rfl⟩ : syracuseStep 2300143 = 3450215) B3450215
theorem B3066857 : Blo 2043435 3066857 := bstep (se 2 (by rfl) ⟨1150071, by rfl⟩ : syracuseStep 3066857 = 2300143) B2300143
theorem B2044571 : Blo 2043435 2044571 := bstep (se 1 (by rfl) ⟨1533428, by rfl⟩ : syracuseStep 2044571 = 3066857) B3066857
theorem B4663061 : Blo 2043435 4663061 := bbase (se 6 (by rfl) ⟨109290, by rfl⟩ : syracuseStep 4663061 = 218581) (by norm_num)
theorem B3108707 : Blo 2043435 3108707 := bstep (se 1 (by rfl) ⟨2331530, by rfl⟩ : syracuseStep 3108707 = 4663061) B4663061
theorem B2072471 : Blo 2043435 2072471 := bstep (se 1 (by rfl) ⟨1554353, by rfl⟩ : syracuseStep 2072471 = 3108707) B3108707
theorem B22106357 : Blo 2043435 22106357 := bstep (se 5 (by rfl) ⟨1036235, by rfl⟩ : syracuseStep 22106357 = 2072471) B2072471
theorem B14737571 : Blo 2043435 14737571 := bstep (se 1 (by rfl) ⟨11053178, by rfl⟩ : syracuseStep 14737571 = 22106357) B22106357
theorem B9825047 : Blo 2043435 9825047 := bstep (se 1 (by rfl) ⟨7368785, by rfl⟩ : syracuseStep 9825047 = 14737571) B14737571
theorem B6550031 : Blo 2043435 6550031 := bstep (se 1 (by rfl) ⟨4912523, by rfl⟩ : syracuseStep 6550031 = 9825047) B9825047
theorem B17466749 : Blo 2043435 17466749 := bstep (se 3 (by rfl) ⟨3275015, by rfl⟩ : syracuseStep 17466749 = 6550031) B6550031
theorem B11644499 : Blo 2043435 11644499 := bstep (se 1 (by rfl) ⟨8733374, by rfl⟩ : syracuseStep 11644499 = 17466749) B17466749
theorem B7762999 : Blo 2043435 7762999 := bstep (se 1 (by rfl) ⟨5822249, by rfl⟩ : syracuseStep 7762999 = 11644499) B11644499
theorem B10350665 : Blo 2043435 10350665 := bstep (se 2 (by rfl) ⟨3881499, by rfl⟩ : syracuseStep 10350665 = 7762999) B7762999
theorem B6900443 : Blo 2043435 6900443 := bstep (se 1 (by rfl) ⟨5175332, by rfl⟩ : syracuseStep 6900443 = 10350665) B10350665
theorem B4600295 : Blo 2043435 4600295 := bstep (se 1 (by rfl) ⟨3450221, by rfl⟩ : syracuseStep 4600295 = 6900443) B6900443
theorem B3066863 : Blo 2043435 3066863 := bstep (se 1 (by rfl) ⟨2300147, by rfl⟩ : syracuseStep 3066863 = 4600295) B4600295
theorem B2044575 : Blo 2043435 2044575 := bstep (se 1 (by rfl) ⟨1533431, by rfl⟩ : syracuseStep 2044575 = 3066863) B3066863
theorem B3066869 : Blo 2043435 3066869 := bbase (se 5 (by rfl) ⟨143759, by rfl⟩ : syracuseStep 3066869 = 287519) (by norm_num)
theorem B2044579 : Blo 2043435 2044579 := bstep (se 1 (by rfl) ⟨1533434, by rfl⟩ : syracuseStep 2044579 = 3066869) B3066869
theorem B3275029 : Blo 2043435 3275029 := bbase (se 6 (by rfl) ⟨76758, by rfl⟩ : syracuseStep 3275029 = 153517) (by norm_num)
theorem B4366705 : Blo 2043435 4366705 := bstep (se 2 (by rfl) ⟨1637514, by rfl⟩ : syracuseStep 4366705 = 3275029) B3275029
theorem B5822273 : Blo 2043435 5822273 := bstep (se 2 (by rfl) ⟨2183352, by rfl⟩ : syracuseStep 5822273 = 4366705) B4366705
theorem B3881515 : Blo 2043435 3881515 := bstep (se 1 (by rfl) ⟨2911136, by rfl⟩ : syracuseStep 3881515 = 5822273) B5822273
theorem B5175353 : Blo 2043435 5175353 := bstep (se 2 (by rfl) ⟨1940757, by rfl⟩ : syracuseStep 5175353 = 3881515) B3881515
theorem B3450235 : Blo 2043435 3450235 := bstep (se 1 (by rfl) ⟨2587676, by rfl⟩ : syracuseStep 3450235 = 5175353) B5175353
theorem B4600313 : Blo 2043435 4600313 := bstep (se 2 (by rfl) ⟨1725117, by rfl⟩ : syracuseStep 4600313 = 3450235) B3450235
theorem B3066875 : Blo 2043435 3066875 := bstep (se 1 (by rfl) ⟨2300156, by rfl⟩ : syracuseStep 3066875 = 4600313) B4600313
theorem B2044583 : Blo 2043435 2044583 := bstep (se 1 (by rfl) ⟨1533437, by rfl⟩ : syracuseStep 2044583 = 3066875) B3066875
theorem B2300161 : Blo 2043435 2300161 := bbase (se 2 (by rfl) ⟨862560, by rfl⟩ : syracuseStep 2300161 = 1725121) (by norm_num)
theorem B3066881 : Blo 2043435 3066881 := bstep (se 2 (by rfl) ⟨1150080, by rfl⟩ : syracuseStep 3066881 = 2300161) B2300161
theorem B2044587 : Blo 2043435 2044587 := bstep (se 1 (by rfl) ⟨1533440, by rfl⟩ : syracuseStep 2044587 = 3066881) B3066881
theorem B5175373 : Blo 2043435 5175373 := bbase (se 3 (by rfl) ⟨970382, by rfl⟩ : syracuseStep 5175373 = 1940765) (by norm_num)
theorem B6900497 : Blo 2043435 6900497 := bstep (se 2 (by rfl) ⟨2587686, by rfl⟩ : syracuseStep 6900497 = 5175373) B5175373
theorem B4600331 : Blo 2043435 4600331 := bstep (se 1 (by rfl) ⟨3450248, by rfl⟩ : syracuseStep 4600331 = 6900497) B6900497
theorem B3066887 : Blo 2043435 3066887 := bstep (se 1 (by rfl) ⟨2300165, by rfl⟩ : syracuseStep 3066887 = 4600331) B4600331
theorem B2044591 : Blo 2043435 2044591 := bstep (se 1 (by rfl) ⟨1533443, by rfl⟩ : syracuseStep 2044591 = 3066887) B3066887
theorem B3066893 : Blo 2043435 3066893 := bbase (se 3 (by rfl) ⟨575042, by rfl⟩ : syracuseStep 3066893 = 1150085) (by norm_num)
theorem B2044595 : Blo 2043435 2044595 := bstep (se 1 (by rfl) ⟨1533446, by rfl⟩ : syracuseStep 2044595 = 3066893) B3066893
theorem B4600349 : Blo 2043435 4600349 := bbase (se 3 (by rfl) ⟨862565, by rfl⟩ : syracuseStep 4600349 = 1725131) (by norm_num)
theorem B3066899 : Blo 2043435 3066899 := bstep (se 1 (by rfl) ⟨2300174, by rfl⟩ : syracuseStep 3066899 = 4600349) B4600349
theorem B2044599 : Blo 2043435 2044599 := bstep (se 1 (by rfl) ⟨1533449, by rfl⟩ : syracuseStep 2044599 = 3066899) B3066899
theorem B3450269 : Blo 2043435 3450269 := bbase (se 3 (by rfl) ⟨646925, by rfl⟩ : syracuseStep 3450269 = 1293851) (by norm_num)
theorem B2300179 : Blo 2043435 2300179 := bstep (se 1 (by rfl) ⟨1725134, by rfl⟩ : syracuseStep 2300179 = 3450269) B3450269
theorem B3066905 : Blo 2043435 3066905 := bstep (se 2 (by rfl) ⟨1150089, by rfl⟩ : syracuseStep 3066905 = 2300179) B2300179
theorem B2044603 : Blo 2043435 2044603 := bstep (se 1 (by rfl) ⟨1533452, by rfl⟩ : syracuseStep 2044603 = 3066905) B3066905
theorem B4726757 : Blo 2043435 4726757 := bbase (se 4 (by rfl) ⟨443133, by rfl⟩ : syracuseStep 4726757 = 886267) (by norm_num)
theorem B3151171 : Blo 2043435 3151171 := bstep (se 1 (by rfl) ⟨2363378, by rfl⟩ : syracuseStep 3151171 = 4726757) B4726757
theorem B4201561 : Blo 2043435 4201561 := bstep (se 2 (by rfl) ⟨1575585, by rfl⟩ : syracuseStep 4201561 = 3151171) B3151171
theorem B5602081 : Blo 2043435 5602081 := bstep (se 2 (by rfl) ⟨2100780, by rfl⟩ : syracuseStep 5602081 = 4201561) B4201561
theorem B7469441 : Blo 2043435 7469441 := bstep (se 2 (by rfl) ⟨2801040, by rfl⟩ : syracuseStep 7469441 = 5602081) B5602081
theorem B4979627 : Blo 2043435 4979627 := bstep (se 1 (by rfl) ⟨3734720, by rfl⟩ : syracuseStep 4979627 = 7469441) B7469441
theorem B3319751 : Blo 2043435 3319751 := bstep (se 1 (by rfl) ⟨2489813, by rfl⟩ : syracuseStep 3319751 = 4979627) B4979627
theorem B2213167 : Blo 2043435 2213167 := bstep (se 1 (by rfl) ⟨1659875, by rfl⟩ : syracuseStep 2213167 = 3319751) B3319751
theorem B2950889 : Blo 2043435 2950889 := bstep (se 2 (by rfl) ⟨1106583, by rfl⟩ : syracuseStep 2950889 = 2213167) B2213167
theorem B7869037 : Blo 2043435 7869037 := bstep (se 3 (by rfl) ⟨1475444, by rfl⟩ : syracuseStep 7869037 = 2950889) B2950889
theorem B10492049 : Blo 2043435 10492049 := bstep (se 2 (by rfl) ⟨3934518, by rfl⟩ : syracuseStep 10492049 = 7869037) B7869037
theorem B27978797 : Blo 2043435 27978797 := bstep (se 3 (by rfl) ⟨5246024, by rfl⟩ : syracuseStep 27978797 = 10492049) B10492049
theorem B18652531 : Blo 2043435 18652531 := bstep (se 1 (by rfl) ⟨13989398, by rfl⟩ : syracuseStep 18652531 = 27978797) B27978797
theorem B24870041 : Blo 2043435 24870041 := bstep (se 2 (by rfl) ⟨9326265, by rfl⟩ : syracuseStep 24870041 = 18652531) B18652531
theorem B16580027 : Blo 2043435 16580027 := bstep (se 1 (by rfl) ⟨12435020, by rfl⟩ : syracuseStep 16580027 = 24870041) B24870041
theorem B11053351 : Blo 2043435 11053351 := bstep (se 1 (by rfl) ⟨8290013, by rfl⟩ : syracuseStep 11053351 = 16580027) B16580027
theorem B14737801 : Blo 2043435 14737801 := bstep (se 2 (by rfl) ⟨5526675, by rfl⟩ : syracuseStep 14737801 = 11053351) B11053351
theorem B19650401 : Blo 2043435 19650401 := bstep (se 2 (by rfl) ⟨7368900, by rfl⟩ : syracuseStep 19650401 = 14737801) B14737801
theorem B13100267 : Blo 2043435 13100267 := bstep (se 1 (by rfl) ⟨9825200, by rfl⟩ : syracuseStep 13100267 = 19650401) B19650401
theorem B8733511 : Blo 2043435 8733511 := bstep (se 1 (by rfl) ⟨6550133, by rfl⟩ : syracuseStep 8733511 = 13100267) B13100267
theorem B11644681 : Blo 2043435 11644681 := bstep (se 2 (by rfl) ⟨4366755, by rfl⟩ : syracuseStep 11644681 = 8733511) B8733511
theorem B15526241 : Blo 2043435 15526241 := bstep (se 2 (by rfl) ⟨5822340, by rfl⟩ : syracuseStep 15526241 = 11644681) B11644681
theorem B10350827 : Blo 2043435 10350827 := bstep (se 1 (by rfl) ⟨7763120, by rfl⟩ : syracuseStep 10350827 = 15526241) B15526241
theorem B6900551 : Blo 2043435 6900551 := bstep (se 1 (by rfl) ⟨5175413, by rfl⟩ : syracuseStep 6900551 = 10350827) B10350827
theorem B4600367 : Blo 2043435 4600367 := bstep (se 1 (by rfl) ⟨3450275, by rfl⟩ : syracuseStep 4600367 = 6900551) B6900551
theorem B3066911 : Blo 2043435 3066911 := bstep (se 1 (by rfl) ⟨2300183, by rfl⟩ : syracuseStep 3066911 = 4600367) B4600367
theorem B2044607 : Blo 2043435 2044607 := bstep (se 1 (by rfl) ⟨1533455, by rfl⟩ : syracuseStep 2044607 = 3066911) B3066911
theorem B3066917 : Blo 2043435 3066917 := bbase (se 4 (by rfl) ⟨287523, by rfl⟩ : syracuseStep 3066917 = 575047) (by norm_num)
theorem B2044611 : Blo 2043435 2044611 := bstep (se 1 (by rfl) ⟨1533458, by rfl⟩ : syracuseStep 2044611 = 3066917) B3066917
theorem B2587717 : Blo 2043435 2587717 := bbase (se 4 (by rfl) ⟨242598, by rfl⟩ : syracuseStep 2587717 = 485197) (by norm_num)
theorem B3450289 : Blo 2043435 3450289 := bstep (se 2 (by rfl) ⟨1293858, by rfl⟩ : syracuseStep 3450289 = 2587717) B2587717
theorem B4600385 : Blo 2043435 4600385 := bstep (se 2 (by rfl) ⟨1725144, by rfl⟩ : syracuseStep 4600385 = 3450289) B3450289
theorem B3066923 : Blo 2043435 3066923 := bstep (se 1 (by rfl) ⟨2300192, by rfl⟩ : syracuseStep 3066923 = 4600385) B4600385
theorem B2044615 : Blo 2043435 2044615 := bstep (se 1 (by rfl) ⟨1533461, by rfl⟩ : syracuseStep 2044615 = 3066923) B3066923
theorem B2300197 : Blo 2043435 2300197 := bbase (se 4 (by rfl) ⟨215643, by rfl⟩ : syracuseStep 2300197 = 431287) (by norm_num)
theorem B3066929 : Blo 2043435 3066929 := bstep (se 2 (by rfl) ⟨1150098, by rfl⟩ : syracuseStep 3066929 = 2300197) B2300197
theorem B2044619 : Blo 2043435 2044619 := bstep (se 1 (by rfl) ⟨1533464, by rfl⟩ : syracuseStep 2044619 = 3066929) B3066929
theorem B3275093 : Blo 2043435 3275093 := bbase (se 10 (by rfl) ⟨4797, by rfl⟩ : syracuseStep 3275093 = 9595) (by norm_num)
theorem B8733581 : Blo 2043435 8733581 := bstep (se 3 (by rfl) ⟨1637546, by rfl⟩ : syracuseStep 8733581 = 3275093) B3275093
theorem B5822387 : Blo 2043435 5822387 := bstep (se 1 (by rfl) ⟨4366790, by rfl⟩ : syracuseStep 5822387 = 8733581) B8733581
theorem B3881591 : Blo 2043435 3881591 := bstep (se 1 (by rfl) ⟨2911193, by rfl⟩ : syracuseStep 3881591 = 5822387) B5822387
theorem B2587727 : Blo 2043435 2587727 := bstep (se 1 (by rfl) ⟨1940795, by rfl⟩ : syracuseStep 2587727 = 3881591) B3881591
theorem B6900605 : Blo 2043435 6900605 := bstep (se 3 (by rfl) ⟨1293863, by rfl⟩ : syracuseStep 6900605 = 2587727) B2587727
theorem B4600403 : Blo 2043435 4600403 := bstep (se 1 (by rfl) ⟨3450302, by rfl⟩ : syracuseStep 4600403 = 6900605) B6900605
theorem B3066935 : Blo 2043435 3066935 := bstep (se 1 (by rfl) ⟨2300201, by rfl⟩ : syracuseStep 3066935 = 4600403) B4600403
theorem B2044623 : Blo 2043435 2044623 := bstep (se 1 (by rfl) ⟨1533467, by rfl⟩ : syracuseStep 2044623 = 3066935) B3066935
theorem B3066941 : Blo 2043435 3066941 := bbase (se 3 (by rfl) ⟨575051, by rfl⟩ : syracuseStep 3066941 = 1150103) (by norm_num)
theorem B2044627 : Blo 2043435 2044627 := bstep (se 1 (by rfl) ⟨1533470, by rfl⟩ : syracuseStep 2044627 = 3066941) B3066941
theorem B4600421 : Blo 2043435 4600421 := bbase (se 4 (by rfl) ⟨431289, by rfl⟩ : syracuseStep 4600421 = 862579) (by norm_num)
theorem B3066947 : Blo 2043435 3066947 := bstep (se 1 (by rfl) ⟨2300210, by rfl⟩ : syracuseStep 3066947 = 4600421) B4600421
theorem B2044631 : Blo 2043435 2044631 := bstep (se 1 (by rfl) ⟨1533473, by rfl⟩ : syracuseStep 2044631 = 3066947) B3066947
theorem B5175485 : Blo 2043435 5175485 := bbase (se 3 (by rfl) ⟨970403, by rfl⟩ : syracuseStep 5175485 = 1940807) (by norm_num)
theorem B3450323 : Blo 2043435 3450323 := bstep (se 1 (by rfl) ⟨2587742, by rfl⟩ : syracuseStep 3450323 = 5175485) B5175485
theorem B2300215 : Blo 2043435 2300215 := bstep (se 1 (by rfl) ⟨1725161, by rfl⟩ : syracuseStep 2300215 = 3450323) B3450323
theorem B3066953 : Blo 2043435 3066953 := bstep (se 2 (by rfl) ⟨1150107, by rfl⟩ : syracuseStep 3066953 = 2300215) B2300215
theorem B2044635 : Blo 2043435 2044635 := bstep (se 1 (by rfl) ⟨1533476, by rfl⟩ : syracuseStep 2044635 = 3066953) B3066953
theorem B3881621 : Blo 2043435 3881621 := bbase (se 6 (by rfl) ⟨90975, by rfl⟩ : syracuseStep 3881621 = 181951) (by norm_num)
theorem B10350989 : Blo 2043435 10350989 := bstep (se 3 (by rfl) ⟨1940810, by rfl⟩ : syracuseStep 10350989 = 3881621) B3881621
theorem B6900659 : Blo 2043435 6900659 := bstep (se 1 (by rfl) ⟨5175494, by rfl⟩ : syracuseStep 6900659 = 10350989) B10350989
theorem B4600439 : Blo 2043435 4600439 := bstep (se 1 (by rfl) ⟨3450329, by rfl⟩ : syracuseStep 4600439 = 6900659) B6900659
theorem B3066959 : Blo 2043435 3066959 := bstep (se 1 (by rfl) ⟨2300219, by rfl⟩ : syracuseStep 3066959 = 4600439) B4600439
theorem B2044639 : Blo 2043435 2044639 := bstep (se 1 (by rfl) ⟨1533479, by rfl⟩ : syracuseStep 2044639 = 3066959) B3066959
theorem B3066965 : Blo 2043435 3066965 := bbase (se 8 (by rfl) ⟨17970, by rfl⟩ : syracuseStep 3066965 = 35941) (by norm_num)
theorem B2044643 : Blo 2043435 2044643 := bstep (se 1 (by rfl) ⟨1533482, by rfl⟩ : syracuseStep 2044643 = 3066965) B3066965
theorem B2331613 : Blo 2043435 2331613 := bbase (se 3 (by rfl) ⟨437177, by rfl⟩ : syracuseStep 2331613 = 874355) (by norm_num)
theorem B3108817 : Blo 2043435 3108817 := bstep (se 2 (by rfl) ⟨1165806, by rfl⟩ : syracuseStep 3108817 = 2331613) B2331613
theorem B4145089 : Blo 2043435 4145089 := bstep (se 2 (by rfl) ⟨1554408, by rfl⟩ : syracuseStep 4145089 = 3108817) B3108817
theorem B5526785 : Blo 2043435 5526785 := bstep (se 2 (by rfl) ⟨2072544, by rfl⟩ : syracuseStep 5526785 = 4145089) B4145089
theorem B3684523 : Blo 2043435 3684523 := bstep (se 1 (by rfl) ⟨2763392, by rfl⟩ : syracuseStep 3684523 = 5526785) B5526785
theorem B4912697 : Blo 2043435 4912697 := bstep (se 2 (by rfl) ⟨1842261, by rfl⟩ : syracuseStep 4912697 = 3684523) B3684523
theorem B13100525 : Blo 2043435 13100525 := bstep (se 3 (by rfl) ⟨2456348, by rfl⟩ : syracuseStep 13100525 = 4912697) B4912697
theorem B8733683 : Blo 2043435 8733683 := bstep (se 1 (by rfl) ⟨6550262, by rfl⟩ : syracuseStep 8733683 = 13100525) B13100525
theorem B5822455 : Blo 2043435 5822455 := bstep (se 1 (by rfl) ⟨4366841, by rfl⟩ : syracuseStep 5822455 = 8733683) B8733683
theorem B7763273 : Blo 2043435 7763273 := bstep (se 2 (by rfl) ⟨2911227, by rfl⟩ : syracuseStep 7763273 = 5822455) B5822455
theorem B5175515 : Blo 2043435 5175515 := bstep (se 1 (by rfl) ⟨3881636, by rfl⟩ : syracuseStep 5175515 = 7763273) B7763273
theorem B3450343 : Blo 2043435 3450343 := bstep (se 1 (by rfl) ⟨2587757, by rfl⟩ : syracuseStep 3450343 = 5175515) B5175515
theorem B4600457 : Blo 2043435 4600457 := bstep (se 2 (by rfl) ⟨1725171, by rfl⟩ : syracuseStep 4600457 = 3450343) B3450343
theorem B3066971 : Blo 2043435 3066971 := bstep (se 1 (by rfl) ⟨2300228, by rfl⟩ : syracuseStep 3066971 = 4600457) B4600457
theorem B2044647 : Blo 2043435 2044647 := bstep (se 1 (by rfl) ⟨1533485, by rfl⟩ : syracuseStep 2044647 = 3066971) B3066971
theorem B2300233 : Blo 2043435 2300233 := bbase (se 2 (by rfl) ⟨862587, by rfl⟩ : syracuseStep 2300233 = 1725175) (by norm_num)
theorem B3066977 : Blo 2043435 3066977 := bstep (se 2 (by rfl) ⟨1150116, by rfl⟩ : syracuseStep 3066977 = 2300233) B2300233
theorem B2044651 : Blo 2043435 2044651 := bstep (se 1 (by rfl) ⟨1533488, by rfl⟩ : syracuseStep 2044651 = 3066977) B3066977
theorem B17705749 : Blo 2043435 17705749 := bbase (se 6 (by rfl) ⟨414978, by rfl⟩ : syracuseStep 17705749 = 829957) (by norm_num)
theorem B23607665 : Blo 2043435 23607665 := bstep (se 2 (by rfl) ⟨8852874, by rfl⟩ : syracuseStep 23607665 = 17705749) B17705749
theorem B15738443 : Blo 2043435 15738443 := bstep (se 1 (by rfl) ⟨11803832, by rfl⟩ : syracuseStep 15738443 = 23607665) B23607665
theorem B10492295 : Blo 2043435 10492295 := bstep (se 1 (by rfl) ⟨7869221, by rfl⟩ : syracuseStep 10492295 = 15738443) B15738443
theorem B27979453 : Blo 2043435 27979453 := bstep (se 3 (by rfl) ⟨5246147, by rfl⟩ : syracuseStep 27979453 = 10492295) B10492295
theorem B37305937 : Blo 2043435 37305937 := bstep (se 2 (by rfl) ⟨13989726, by rfl⟩ : syracuseStep 37305937 = 27979453) B27979453
theorem B49741249 : Blo 2043435 49741249 := bstep (se 2 (by rfl) ⟨18652968, by rfl⟩ : syracuseStep 49741249 = 37305937) B37305937
theorem B66321665 : Blo 2043435 66321665 := bstep (se 2 (by rfl) ⟨24870624, by rfl⟩ : syracuseStep 66321665 = 49741249) B49741249
theorem B44214443 : Blo 2043435 44214443 := bstep (se 1 (by rfl) ⟨33160832, by rfl⟩ : syracuseStep 44214443 = 66321665) B66321665
theorem B29476295 : Blo 2043435 29476295 := bstep (se 1 (by rfl) ⟨22107221, by rfl⟩ : syracuseStep 29476295 = 44214443) B44214443
theorem B19650863 : Blo 2043435 19650863 := bstep (se 1 (by rfl) ⟨14738147, by rfl⟩ : syracuseStep 19650863 = 29476295) B29476295
theorem B13100575 : Blo 2043435 13100575 := bstep (se 1 (by rfl) ⟨9825431, by rfl⟩ : syracuseStep 13100575 = 19650863) B19650863
theorem B17467433 : Blo 2043435 17467433 := bstep (se 2 (by rfl) ⟨6550287, by rfl⟩ : syracuseStep 17467433 = 13100575) B13100575
theorem B11644955 : Blo 2043435 11644955 := bstep (se 1 (by rfl) ⟨8733716, by rfl⟩ : syracuseStep 11644955 = 17467433) B17467433
theorem B7763303 : Blo 2043435 7763303 := bstep (se 1 (by rfl) ⟨5822477, by rfl⟩ : syracuseStep 7763303 = 11644955) B11644955
theorem B5175535 : Blo 2043435 5175535 := bstep (se 1 (by rfl) ⟨3881651, by rfl⟩ : syracuseStep 5175535 = 7763303) B7763303
theorem B6900713 : Blo 2043435 6900713 := bstep (se 2 (by rfl) ⟨2587767, by rfl⟩ : syracuseStep 6900713 = 5175535) B5175535
theorem B4600475 : Blo 2043435 4600475 := bstep (se 1 (by rfl) ⟨3450356, by rfl⟩ : syracuseStep 4600475 = 6900713) B6900713
theorem B3066983 : Blo 2043435 3066983 := bstep (se 1 (by rfl) ⟨2300237, by rfl⟩ : syracuseStep 3066983 = 4600475) B4600475
theorem B2044655 : Blo 2043435 2044655 := bstep (se 1 (by rfl) ⟨1533491, by rfl⟩ : syracuseStep 2044655 = 3066983) B3066983
theorem B3066989 : Blo 2043435 3066989 := bbase (se 3 (by rfl) ⟨575060, by rfl⟩ : syracuseStep 3066989 = 1150121) (by norm_num)
theorem B2044659 : Blo 2043435 2044659 := bstep (se 1 (by rfl) ⟨1533494, by rfl⟩ : syracuseStep 2044659 = 3066989) B3066989
theorem B4600493 : Blo 2043435 4600493 := bbase (se 3 (by rfl) ⟨862592, by rfl⟩ : syracuseStep 4600493 = 1725185) (by norm_num)
theorem B3066995 : Blo 2043435 3066995 := bstep (se 1 (by rfl) ⟨2300246, by rfl⟩ : syracuseStep 3066995 = 4600493) B4600493
theorem B2044663 : Blo 2043435 2044663 := bstep (se 1 (by rfl) ⟨1533497, by rfl⟩ : syracuseStep 2044663 = 3066995) B3066995
theorem B4366885 : Blo 2043435 4366885 := bbase (se 4 (by rfl) ⟨409395, by rfl⟩ : syracuseStep 4366885 = 818791) (by norm_num)
theorem B5822513 : Blo 2043435 5822513 := bstep (se 2 (by rfl) ⟨2183442, by rfl⟩ : syracuseStep 5822513 = 4366885) B4366885
theorem B3881675 : Blo 2043435 3881675 := bstep (se 1 (by rfl) ⟨2911256, by rfl⟩ : syracuseStep 3881675 = 5822513) B5822513
theorem B2587783 : Blo 2043435 2587783 := bstep (se 1 (by rfl) ⟨1940837, by rfl⟩ : syracuseStep 2587783 = 3881675) B3881675
theorem B3450377 : Blo 2043435 3450377 := bstep (se 2 (by rfl) ⟨1293891, by rfl⟩ : syracuseStep 3450377 = 2587783) B2587783
theorem B2300251 : Blo 2043435 2300251 := bstep (se 1 (by rfl) ⟨1725188, by rfl⟩ : syracuseStep 2300251 = 3450377) B3450377
theorem B3067001 : Blo 2043435 3067001 := bstep (se 2 (by rfl) ⟨1150125, by rfl⟩ : syracuseStep 3067001 = 2300251) B2300251
theorem B2044667 : Blo 2043435 2044667 := bstep (se 1 (by rfl) ⟨1533500, by rfl⟩ : syracuseStep 2044667 = 3067001) B3067001
theorem B2950981 : Blo 2043435 2950981 := bbase (se 4 (by rfl) ⟨276654, by rfl⟩ : syracuseStep 2950981 = 553309) (by norm_num)
theorem B15738565 : Blo 2043435 15738565 := bstep (se 4 (by rfl) ⟨1475490, by rfl⟩ : syracuseStep 15738565 = 2950981) B2950981
theorem B20984753 : Blo 2043435 20984753 := bstep (se 2 (by rfl) ⟨7869282, by rfl⟩ : syracuseStep 20984753 = 15738565) B15738565
theorem B13989835 : Blo 2043435 13989835 := bstep (se 1 (by rfl) ⟨10492376, by rfl⟩ : syracuseStep 13989835 = 20984753) B20984753
theorem B18653113 : Blo 2043435 18653113 := bstep (se 2 (by rfl) ⟨6994917, by rfl⟩ : syracuseStep 18653113 = 13989835) B13989835
theorem B24870817 : Blo 2043435 24870817 := bstep (se 2 (by rfl) ⟨9326556, by rfl⟩ : syracuseStep 24870817 = 18653113) B18653113
theorem B33161089 : Blo 2043435 33161089 := bstep (se 2 (by rfl) ⟨12435408, by rfl⟩ : syracuseStep 33161089 = 24870817) B24870817
theorem B44214785 : Blo 2043435 44214785 := bstep (se 2 (by rfl) ⟨16580544, by rfl⟩ : syracuseStep 44214785 = 33161089) B33161089
theorem B29476523 : Blo 2043435 29476523 := bstep (se 1 (by rfl) ⟨22107392, by rfl⟩ : syracuseStep 29476523 = 44214785) B44214785
theorem B19651015 : Blo 2043435 19651015 := bstep (se 1 (by rfl) ⟨14738261, by rfl⟩ : syracuseStep 19651015 = 29476523) B29476523
theorem B26201353 : Blo 2043435 26201353 := bstep (se 2 (by rfl) ⟨9825507, by rfl⟩ : syracuseStep 26201353 = 19651015) B19651015
theorem B34935137 : Blo 2043435 34935137 := bstep (se 2 (by rfl) ⟨13100676, by rfl⟩ : syracuseStep 34935137 = 26201353) B26201353
theorem B23290091 : Blo 2043435 23290091 := bstep (se 1 (by rfl) ⟨17467568, by rfl⟩ : syracuseStep 23290091 = 34935137) B34935137
theorem B15526727 : Blo 2043435 15526727 := bstep (se 1 (by rfl) ⟨11645045, by rfl⟩ : syracuseStep 15526727 = 23290091) B23290091
theorem B10351151 : Blo 2043435 10351151 := bstep (se 1 (by rfl) ⟨7763363, by rfl⟩ : syracuseStep 10351151 = 15526727) B15526727
theorem B6900767 : Blo 2043435 6900767 := bstep (se 1 (by rfl) ⟨5175575, by rfl⟩ : syracuseStep 6900767 = 10351151) B10351151
theorem B4600511 : Blo 2043435 4600511 := bstep (se 1 (by rfl) ⟨3450383, by rfl⟩ : syracuseStep 4600511 = 6900767) B6900767
theorem B3067007 : Blo 2043435 3067007 := bstep (se 1 (by rfl) ⟨2300255, by rfl⟩ : syracuseStep 3067007 = 4600511) B4600511
theorem B2044671 : Blo 2043435 2044671 := bstep (se 1 (by rfl) ⟨1533503, by rfl⟩ : syracuseStep 2044671 = 3067007) B3067007
theorem B3067013 : Blo 2043435 3067013 := bbase (se 4 (by rfl) ⟨287532, by rfl⟩ : syracuseStep 3067013 = 575065) (by norm_num)
theorem B2044675 : Blo 2043435 2044675 := bstep (se 1 (by rfl) ⟨1533506, by rfl⟩ : syracuseStep 2044675 = 3067013) B3067013
theorem B3450397 : Blo 2043435 3450397 := bbase (se 3 (by rfl) ⟨646949, by rfl⟩ : syracuseStep 3450397 = 1293899) (by norm_num)
theorem B4600529 : Blo 2043435 4600529 := bstep (se 2 (by rfl) ⟨1725198, by rfl⟩ : syracuseStep 4600529 = 3450397) B3450397
theorem B3067019 : Blo 2043435 3067019 := bstep (se 1 (by rfl) ⟨2300264, by rfl⟩ : syracuseStep 3067019 = 4600529) B4600529
theorem B2044679 : Blo 2043435 2044679 := bstep (se 1 (by rfl) ⟨1533509, by rfl⟩ : syracuseStep 2044679 = 3067019) B3067019
theorem B2300269 : Blo 2043435 2300269 := bbase (se 3 (by rfl) ⟨431300, by rfl⟩ : syracuseStep 2300269 = 862601) (by norm_num)
theorem B3067025 : Blo 2043435 3067025 := bstep (se 2 (by rfl) ⟨1150134, by rfl⟩ : syracuseStep 3067025 = 2300269) B2300269
theorem B2044683 : Blo 2043435 2044683 := bstep (se 1 (by rfl) ⟨1533512, by rfl⟩ : syracuseStep 2044683 = 3067025) B3067025
theorem B6900821 : Blo 2043435 6900821 := bbase (se 8 (by rfl) ⟨40434, by rfl⟩ : syracuseStep 6900821 = 80869) (by norm_num)
theorem B4600547 : Blo 2043435 4600547 := bstep (se 1 (by rfl) ⟨3450410, by rfl⟩ : syracuseStep 4600547 = 6900821) B6900821
theorem B3067031 : Blo 2043435 3067031 := bstep (se 1 (by rfl) ⟨2300273, by rfl⟩ : syracuseStep 3067031 = 4600547) B4600547
theorem B2044687 : Blo 2043435 2044687 := bstep (se 1 (by rfl) ⟨1533515, by rfl⟩ : syracuseStep 2044687 = 3067031) B3067031
theorem B3067037 : Blo 2043435 3067037 := bbase (se 3 (by rfl) ⟨575069, by rfl⟩ : syracuseStep 3067037 = 1150139) (by norm_num)
theorem B2044691 : Blo 2043435 2044691 := bstep (se 1 (by rfl) ⟨1533518, by rfl⟩ : syracuseStep 2044691 = 3067037) B3067037
theorem B4600565 : Blo 2043435 4600565 := bbase (se 5 (by rfl) ⟨215651, by rfl⟩ : syracuseStep 4600565 = 431303) (by norm_num)
theorem B3067043 : Blo 2043435 3067043 := bstep (se 1 (by rfl) ⟨2300282, by rfl⟩ : syracuseStep 3067043 = 4600565) B4600565
theorem B2044695 : Blo 2043435 2044695 := bstep (se 1 (by rfl) ⟨1533521, by rfl⟩ : syracuseStep 2044695 = 3067043) B3067043
theorem B3497509 : Blo 2043435 3497509 := bbase (se 4 (by rfl) ⟨327891, by rfl⟩ : syracuseStep 3497509 = 655783) (by norm_num)
theorem B4663345 : Blo 2043435 4663345 := bstep (se 2 (by rfl) ⟨1748754, by rfl⟩ : syracuseStep 4663345 = 3497509) B3497509
theorem B6217793 : Blo 2043435 6217793 := bstep (se 2 (by rfl) ⟨2331672, by rfl⟩ : syracuseStep 6217793 = 4663345) B4663345
theorem B4145195 : Blo 2043435 4145195 := bstep (se 1 (by rfl) ⟨3108896, by rfl⟩ : syracuseStep 4145195 = 6217793) B6217793
theorem B2763463 : Blo 2043435 2763463 := bstep (se 1 (by rfl) ⟨2072597, by rfl⟩ : syracuseStep 2763463 = 4145195) B4145195
theorem B3684617 : Blo 2043435 3684617 := bstep (se 2 (by rfl) ⟨1381731, by rfl⟩ : syracuseStep 3684617 = 2763463) B2763463
theorem B2456411 : Blo 2043435 2456411 := bstep (se 1 (by rfl) ⟨1842308, by rfl⟩ : syracuseStep 2456411 = 3684617) B3684617
theorem B26201717 : Blo 2043435 26201717 := bstep (se 5 (by rfl) ⟨1228205, by rfl⟩ : syracuseStep 26201717 = 2456411) B2456411
theorem B17467811 : Blo 2043435 17467811 := bstep (se 1 (by rfl) ⟨13100858, by rfl⟩ : syracuseStep 17467811 = 26201717) B26201717
theorem B11645207 : Blo 2043435 11645207 := bstep (se 1 (by rfl) ⟨8733905, by rfl⟩ : syracuseStep 11645207 = 17467811) B17467811
theorem B7763471 : Blo 2043435 7763471 := bstep (se 1 (by rfl) ⟨5822603, by rfl⟩ : syracuseStep 7763471 = 11645207) B11645207
theorem B5175647 : Blo 2043435 5175647 := bstep (se 1 (by rfl) ⟨3881735, by rfl⟩ : syracuseStep 5175647 = 7763471) B7763471
theorem B3450431 : Blo 2043435 3450431 := bstep (se 1 (by rfl) ⟨2587823, by rfl⟩ : syracuseStep 3450431 = 5175647) B5175647
theorem B2300287 : Blo 2043435 2300287 := bstep (se 1 (by rfl) ⟨1725215, by rfl⟩ : syracuseStep 2300287 = 3450431) B3450431
theorem B3067049 : Blo 2043435 3067049 := bstep (se 2 (by rfl) ⟨1150143, by rfl⟩ : syracuseStep 3067049 = 2300287) B2300287
theorem B2044699 : Blo 2043435 2044699 := bstep (se 1 (by rfl) ⟨1533524, by rfl⟩ : syracuseStep 2044699 = 3067049) B3067049
theorem B3275221 : Blo 2043435 3275221 := bbase (se 7 (by rfl) ⟨38381, by rfl⟩ : syracuseStep 3275221 = 76763) (by norm_num)
theorem B4366961 : Blo 2043435 4366961 := bstep (se 2 (by rfl) ⟨1637610, by rfl⟩ : syracuseStep 4366961 = 3275221) B3275221
theorem B2911307 : Blo 2043435 2911307 := bstep (se 1 (by rfl) ⟨2183480, by rfl⟩ : syracuseStep 2911307 = 4366961) B4366961
theorem B7763485 : Blo 2043435 7763485 := bstep (se 3 (by rfl) ⟨1455653, by rfl⟩ : syracuseStep 7763485 = 2911307) B2911307
theorem B10351313 : Blo 2043435 10351313 := bstep (se 2 (by rfl) ⟨3881742, by rfl⟩ : syracuseStep 10351313 = 7763485) B7763485
theorem B6900875 : Blo 2043435 6900875 := bstep (se 1 (by rfl) ⟨5175656, by rfl⟩ : syracuseStep 6900875 = 10351313) B10351313
theorem B4600583 : Blo 2043435 4600583 := bstep (se 1 (by rfl) ⟨3450437, by rfl⟩ : syracuseStep 4600583 = 6900875) B6900875
theorem B3067055 : Blo 2043435 3067055 := bstep (se 1 (by rfl) ⟨2300291, by rfl⟩ : syracuseStep 3067055 = 4600583) B4600583
theorem B2044703 : Blo 2043435 2044703 := bstep (se 1 (by rfl) ⟨1533527, by rfl⟩ : syracuseStep 2044703 = 3067055) B3067055
theorem B3067061 : Blo 2043435 3067061 := bbase (se 5 (by rfl) ⟨143768, by rfl⟩ : syracuseStep 3067061 = 287537) (by norm_num)
theorem B2044707 : Blo 2043435 2044707 := bstep (se 1 (by rfl) ⟨1533530, by rfl⟩ : syracuseStep 2044707 = 3067061) B3067061
theorem B5175677 : Blo 2043435 5175677 := bbase (se 3 (by rfl) ⟨970439, by rfl⟩ : syracuseStep 5175677 = 1940879) (by norm_num)
theorem B3450451 : Blo 2043435 3450451 := bstep (se 1 (by rfl) ⟨2587838, by rfl⟩ : syracuseStep 3450451 = 5175677) B5175677
theorem B4600601 : Blo 2043435 4600601 := bstep (se 2 (by rfl) ⟨1725225, by rfl⟩ : syracuseStep 4600601 = 3450451) B3450451
theorem B3067067 : Blo 2043435 3067067 := bstep (se 1 (by rfl) ⟨2300300, by rfl⟩ : syracuseStep 3067067 = 4600601) B4600601
theorem B2044711 : Blo 2043435 2044711 := bstep (se 1 (by rfl) ⟨1533533, by rfl⟩ : syracuseStep 2044711 = 3067067) B3067067
theorem B2300305 : Blo 2043435 2300305 := bbase (se 2 (by rfl) ⟨862614, by rfl⟩ : syracuseStep 2300305 = 1725229) (by norm_num)
theorem B3067073 : Blo 2043435 3067073 := bstep (se 2 (by rfl) ⟨1150152, by rfl⟩ : syracuseStep 3067073 = 2300305) B2300305
theorem B2044715 : Blo 2043435 2044715 := bstep (se 1 (by rfl) ⟨1533536, by rfl⟩ : syracuseStep 2044715 = 3067073) B3067073
theorem B3881773 : Blo 2043435 3881773 := bbase (se 3 (by rfl) ⟨727832, by rfl⟩ : syracuseStep 3881773 = 1455665) (by norm_num)
theorem B5175697 : Blo 2043435 5175697 := bstep (se 2 (by rfl) ⟨1940886, by rfl⟩ : syracuseStep 5175697 = 3881773) B3881773
theorem B6900929 : Blo 2043435 6900929 := bstep (se 2 (by rfl) ⟨2587848, by rfl⟩ : syracuseStep 6900929 = 5175697) B5175697
theorem B4600619 : Blo 2043435 4600619 := bstep (se 1 (by rfl) ⟨3450464, by rfl⟩ : syracuseStep 4600619 = 6900929) B6900929
theorem B3067079 : Blo 2043435 3067079 := bstep (se 1 (by rfl) ⟨2300309, by rfl⟩ : syracuseStep 3067079 = 4600619) B4600619
theorem B2044719 : Blo 2043435 2044719 := bstep (se 1 (by rfl) ⟨1533539, by rfl⟩ : syracuseStep 2044719 = 3067079) B3067079
theorem B3067085 : Blo 2043435 3067085 := bbase (se 3 (by rfl) ⟨575078, by rfl⟩ : syracuseStep 3067085 = 1150157) (by norm_num)
theorem B2044723 : Blo 2043435 2044723 := bstep (se 1 (by rfl) ⟨1533542, by rfl⟩ : syracuseStep 2044723 = 3067085) B3067085
theorem B4600637 : Blo 2043435 4600637 := bbase (se 3 (by rfl) ⟨862619, by rfl⟩ : syracuseStep 4600637 = 1725239) (by norm_num)
theorem B3067091 : Blo 2043435 3067091 := bstep (se 1 (by rfl) ⟨2300318, by rfl⟩ : syracuseStep 3067091 = 4600637) B4600637
theorem B2044727 : Blo 2043435 2044727 := bstep (se 1 (by rfl) ⟨1533545, by rfl⟩ : syracuseStep 2044727 = 3067091) B3067091
theorem B3450485 : Blo 2043435 3450485 := bbase (se 5 (by rfl) ⟨161741, by rfl⟩ : syracuseStep 3450485 = 323483) (by norm_num)
theorem B2300323 : Blo 2043435 2300323 := bstep (se 1 (by rfl) ⟨1725242, by rfl⟩ : syracuseStep 2300323 = 3450485) B3450485
theorem B3067097 : Blo 2043435 3067097 := bstep (se 2 (by rfl) ⟨1150161, by rfl⟩ : syracuseStep 3067097 = 2300323) B2300323
theorem B2044731 : Blo 2043435 2044731 := bstep (se 1 (by rfl) ⟨1533548, by rfl⟩ : syracuseStep 2044731 = 3067097) B3067097
theorem B4367029 : Blo 2043435 4367029 := bbase (se 5 (by rfl) ⟨204704, by rfl⟩ : syracuseStep 4367029 = 409409) (by norm_num)
theorem B5822705 : Blo 2043435 5822705 := bstep (se 2 (by rfl) ⟨2183514, by rfl⟩ : syracuseStep 5822705 = 4367029) B4367029
theorem B15527213 : Blo 2043435 15527213 := bstep (se 3 (by rfl) ⟨2911352, by rfl⟩ : syracuseStep 15527213 = 5822705) B5822705
theorem B10351475 : Blo 2043435 10351475 := bstep (se 1 (by rfl) ⟨7763606, by rfl⟩ : syracuseStep 10351475 = 15527213) B15527213
theorem B6900983 : Blo 2043435 6900983 := bstep (se 1 (by rfl) ⟨5175737, by rfl⟩ : syracuseStep 6900983 = 10351475) B10351475
theorem B4600655 : Blo 2043435 4600655 := bstep (se 1 (by rfl) ⟨3450491, by rfl⟩ : syracuseStep 4600655 = 6900983) B6900983
theorem B3067103 : Blo 2043435 3067103 := bstep (se 1 (by rfl) ⟨2300327, by rfl⟩ : syracuseStep 3067103 = 4600655) B4600655
theorem B2044735 : Blo 2043435 2044735 := bstep (se 1 (by rfl) ⟨1533551, by rfl⟩ : syracuseStep 2044735 = 3067103) B3067103
theorem B3067109 : Blo 2043435 3067109 := bbase (se 4 (by rfl) ⟨287541, by rfl⟩ : syracuseStep 3067109 = 575083) (by norm_num)
theorem B2044739 : Blo 2043435 2044739 := bstep (se 1 (by rfl) ⟨1533554, by rfl⟩ : syracuseStep 2044739 = 3067109) B3067109
theorem B5527045 : Blo 2043435 5527045 := bbase (se 4 (by rfl) ⟨518160, by rfl⟩ : syracuseStep 5527045 = 1036321) (by norm_num)
theorem B7369393 : Blo 2043435 7369393 := bstep (se 2 (by rfl) ⟨2763522, by rfl⟩ : syracuseStep 7369393 = 5527045) B5527045
theorem B9825857 : Blo 2043435 9825857 := bstep (se 2 (by rfl) ⟨3684696, by rfl⟩ : syracuseStep 9825857 = 7369393) B7369393
theorem B6550571 : Blo 2043435 6550571 := bstep (se 1 (by rfl) ⟨4912928, by rfl⟩ : syracuseStep 6550571 = 9825857) B9825857
theorem B4367047 : Blo 2043435 4367047 := bstep (se 1 (by rfl) ⟨3275285, by rfl⟩ : syracuseStep 4367047 = 6550571) B6550571
theorem B5822729 : Blo 2043435 5822729 := bstep (se 2 (by rfl) ⟨2183523, by rfl⟩ : syracuseStep 5822729 = 4367047) B4367047
theorem B3881819 : Blo 2043435 3881819 := bstep (se 1 (by rfl) ⟨2911364, by rfl⟩ : syracuseStep 3881819 = 5822729) B5822729
theorem B2587879 : Blo 2043435 2587879 := bstep (se 1 (by rfl) ⟨1940909, by rfl⟩ : syracuseStep 2587879 = 3881819) B3881819
theorem B3450505 : Blo 2043435 3450505 := bstep (se 2 (by rfl) ⟨1293939, by rfl⟩ : syracuseStep 3450505 = 2587879) B2587879
theorem B4600673 : Blo 2043435 4600673 := bstep (se 2 (by rfl) ⟨1725252, by rfl⟩ : syracuseStep 4600673 = 3450505) B3450505
theorem B3067115 : Blo 2043435 3067115 := bstep (se 1 (by rfl) ⟨2300336, by rfl⟩ : syracuseStep 3067115 = 4600673) B4600673
theorem B2044743 : Blo 2043435 2044743 := bstep (se 1 (by rfl) ⟨1533557, by rfl⟩ : syracuseStep 2044743 = 3067115) B3067115
theorem B2300341 : Blo 2043435 2300341 := bbase (se 5 (by rfl) ⟨107828, by rfl⟩ : syracuseStep 2300341 = 215657) (by norm_num)
theorem B3067121 : Blo 2043435 3067121 := bstep (se 2 (by rfl) ⟨1150170, by rfl⟩ : syracuseStep 3067121 = 2300341) B2300341
theorem B2044747 : Blo 2043435 2044747 := bstep (se 1 (by rfl) ⟨1533560, by rfl⟩ : syracuseStep 2044747 = 3067121) B3067121
theorem B2587889 : Blo 2043435 2587889 := bbase (se 2 (by rfl) ⟨970458, by rfl⟩ : syracuseStep 2587889 = 1940917) (by norm_num)
theorem B6901037 : Blo 2043435 6901037 := bstep (se 3 (by rfl) ⟨1293944, by rfl⟩ : syracuseStep 6901037 = 2587889) B2587889
theorem B4600691 : Blo 2043435 4600691 := bstep (se 1 (by rfl) ⟨3450518, by rfl⟩ : syracuseStep 4600691 = 6901037) B6901037
theorem B3067127 : Blo 2043435 3067127 := bstep (se 1 (by rfl) ⟨2300345, by rfl⟩ : syracuseStep 3067127 = 4600691) B4600691
theorem B2044751 : Blo 2043435 2044751 := bstep (se 1 (by rfl) ⟨1533563, by rfl⟩ : syracuseStep 2044751 = 3067127) B3067127
theorem B3067133 : Blo 2043435 3067133 := bbase (se 3 (by rfl) ⟨575087, by rfl⟩ : syracuseStep 3067133 = 1150175) (by norm_num)
theorem B2044755 : Blo 2043435 2044755 := bstep (se 1 (by rfl) ⟨1533566, by rfl⟩ : syracuseStep 2044755 = 3067133) B3067133
theorem B4600709 : Blo 2043435 4600709 := bbase (se 4 (by rfl) ⟨431316, by rfl⟩ : syracuseStep 4600709 = 862633) (by norm_num)
theorem B3067139 : Blo 2043435 3067139 := bstep (se 1 (by rfl) ⟨2300354, by rfl⟩ : syracuseStep 3067139 = 4600709) B4600709
theorem B2044759 : Blo 2043435 2044759 := bstep (se 1 (by rfl) ⟨1533569, by rfl⟩ : syracuseStep 2044759 = 3067139) B3067139
theorem B2183545 : Blo 2043435 2183545 := bbase (se 2 (by rfl) ⟨818829, by rfl⟩ : syracuseStep 2183545 = 1637659) (by norm_num)
theorem B2911393 : Blo 2043435 2911393 := bstep (se 2 (by rfl) ⟨1091772, by rfl⟩ : syracuseStep 2911393 = 2183545) B2183545
theorem B3881857 : Blo 2043435 3881857 := bstep (se 2 (by rfl) ⟨1455696, by rfl⟩ : syracuseStep 3881857 = 2911393) B2911393
theorem B5175809 : Blo 2043435 5175809 := bstep (se 2 (by rfl) ⟨1940928, by rfl⟩ : syracuseStep 5175809 = 3881857) B3881857
theorem B3450539 : Blo 2043435 3450539 := bstep (se 1 (by rfl) ⟨2587904, by rfl⟩ : syracuseStep 3450539 = 5175809) B5175809
theorem B2300359 : Blo 2043435 2300359 := bstep (se 1 (by rfl) ⟨1725269, by rfl⟩ : syracuseStep 2300359 = 3450539) B3450539
theorem B3067145 : Blo 2043435 3067145 := bstep (se 2 (by rfl) ⟨1150179, by rfl⟩ : syracuseStep 3067145 = 2300359) B2300359
theorem B2044763 : Blo 2043435 2044763 := bstep (se 1 (by rfl) ⟨1533572, by rfl⟩ : syracuseStep 2044763 = 3067145) B3067145
theorem B10351637 : Blo 2043435 10351637 := bbase (se 6 (by rfl) ⟨242616, by rfl⟩ : syracuseStep 10351637 = 485233) (by norm_num)
theorem B6901091 : Blo 2043435 6901091 := bstep (se 1 (by rfl) ⟨5175818, by rfl⟩ : syracuseStep 6901091 = 10351637) B10351637
theorem B4600727 : Blo 2043435 4600727 := bstep (se 1 (by rfl) ⟨3450545, by rfl⟩ : syracuseStep 4600727 = 6901091) B6901091
theorem B3067151 : Blo 2043435 3067151 := bstep (se 1 (by rfl) ⟨2300363, by rfl⟩ : syracuseStep 3067151 = 4600727) B4600727
theorem B2044767 : Blo 2043435 2044767 := bstep (se 1 (by rfl) ⟨1533575, by rfl⟩ : syracuseStep 2044767 = 3067151) B3067151
theorem B3067157 : Blo 2043435 3067157 := bbase (se 6 (by rfl) ⟨71886, by rfl⟩ : syracuseStep 3067157 = 143773) (by norm_num)
theorem B2044771 : Blo 2043435 2044771 := bstep (se 1 (by rfl) ⟨1533578, by rfl⟩ : syracuseStep 2044771 = 3067157) B3067157
theorem B2763565 : Blo 2043435 2763565 := bbase (se 3 (by rfl) ⟨518168, by rfl⟩ : syracuseStep 2763565 = 1036337) (by norm_num)
theorem B14739013 : Blo 2043435 14739013 := bstep (se 4 (by rfl) ⟨1381782, by rfl⟩ : syracuseStep 14739013 = 2763565) B2763565
theorem B19652017 : Blo 2043435 19652017 := bstep (se 2 (by rfl) ⟨7369506, by rfl⟩ : syracuseStep 19652017 = 14739013) B14739013
theorem B26202689 : Blo 2043435 26202689 := bstep (se 2 (by rfl) ⟨9826008, by rfl⟩ : syracuseStep 26202689 = 19652017) B19652017
theorem B17468459 : Blo 2043435 17468459 := bstep (se 1 (by rfl) ⟨13101344, by rfl⟩ : syracuseStep 17468459 = 26202689) B26202689
theorem B11645639 : Blo 2043435 11645639 := bstep (se 1 (by rfl) ⟨8734229, by rfl⟩ : syracuseStep 11645639 = 17468459) B17468459
theorem B7763759 : Blo 2043435 7763759 := bstep (se 1 (by rfl) ⟨5822819, by rfl⟩ : syracuseStep 7763759 = 11645639) B11645639
theorem B5175839 : Blo 2043435 5175839 := bstep (se 1 (by rfl) ⟨3881879, by rfl⟩ : syracuseStep 5175839 = 7763759) B7763759
theorem B3450559 : Blo 2043435 3450559 := bstep (se 1 (by rfl) ⟨2587919, by rfl⟩ : syracuseStep 3450559 = 5175839) B5175839
theorem B4600745 : Blo 2043435 4600745 := bstep (se 2 (by rfl) ⟨1725279, by rfl⟩ : syracuseStep 4600745 = 3450559) B3450559
theorem B3067163 : Blo 2043435 3067163 := bstep (se 1 (by rfl) ⟨2300372, by rfl⟩ : syracuseStep 3067163 = 4600745) B4600745
theorem B2044775 : Blo 2043435 2044775 := bstep (se 1 (by rfl) ⟨1533581, by rfl⟩ : syracuseStep 2044775 = 3067163) B3067163
theorem B2300377 : Blo 2043435 2300377 := bbase (se 2 (by rfl) ⟨862641, by rfl⟩ : syracuseStep 2300377 = 1725283) (by norm_num)
theorem B3067169 : Blo 2043435 3067169 := bstep (se 2 (by rfl) ⟨1150188, by rfl⟩ : syracuseStep 3067169 = 2300377) B2300377
theorem B2044779 : Blo 2043435 2044779 := bstep (se 1 (by rfl) ⟨1533584, by rfl⟩ : syracuseStep 2044779 = 3067169) B3067169
theorem B2911421 : Blo 2043435 2911421 := bbase (se 3 (by rfl) ⟨545891, by rfl⟩ : syracuseStep 2911421 = 1091783) (by norm_num)
theorem B7763789 : Blo 2043435 7763789 := bstep (se 3 (by rfl) ⟨1455710, by rfl⟩ : syracuseStep 7763789 = 2911421) B2911421
theorem B5175859 : Blo 2043435 5175859 := bstep (se 1 (by rfl) ⟨3881894, by rfl⟩ : syracuseStep 5175859 = 7763789) B7763789
theorem B6901145 : Blo 2043435 6901145 := bstep (se 2 (by rfl) ⟨2587929, by rfl⟩ : syracuseStep 6901145 = 5175859) B5175859
theorem B4600763 : Blo 2043435 4600763 := bstep (se 1 (by rfl) ⟨3450572, by rfl⟩ : syracuseStep 4600763 = 6901145) B6901145
theorem B3067175 : Blo 2043435 3067175 := bstep (se 1 (by rfl) ⟨2300381, by rfl⟩ : syracuseStep 3067175 = 4600763) B4600763
theorem B2044783 : Blo 2043435 2044783 := bstep (se 1 (by rfl) ⟨1533587, by rfl⟩ : syracuseStep 2044783 = 3067175) B3067175
theorem B3067181 : Blo 2043435 3067181 := bbase (se 3 (by rfl) ⟨575096, by rfl⟩ : syracuseStep 3067181 = 1150193) (by norm_num)
theorem B2044787 : Blo 2043435 2044787 := bstep (se 1 (by rfl) ⟨1533590, by rfl⟩ : syracuseStep 2044787 = 3067181) B3067181
theorem B4600781 : Blo 2043435 4600781 := bbase (se 3 (by rfl) ⟨862646, by rfl⟩ : syracuseStep 4600781 = 1725293) (by norm_num)
theorem B3067187 : Blo 2043435 3067187 := bstep (se 1 (by rfl) ⟨2300390, by rfl⟩ : syracuseStep 3067187 = 4600781) B4600781
theorem B2044791 : Blo 2043435 2044791 := bstep (se 1 (by rfl) ⟨1533593, by rfl⟩ : syracuseStep 2044791 = 3067187) B3067187
theorem B2587945 : Blo 2043435 2587945 := bbase (se 2 (by rfl) ⟨970479, by rfl⟩ : syracuseStep 2587945 = 1940959) (by norm_num)
theorem B3450593 : Blo 2043435 3450593 := bstep (se 2 (by rfl) ⟨1293972, by rfl⟩ : syracuseStep 3450593 = 2587945) B2587945
theorem B2300395 : Blo 2043435 2300395 := bstep (se 1 (by rfl) ⟨1725296, by rfl⟩ : syracuseStep 2300395 = 3450593) B3450593
theorem B3067193 : Blo 2043435 3067193 := bstep (se 2 (by rfl) ⟨1150197, by rfl⟩ : syracuseStep 3067193 = 2300395) B2300395
theorem B2044795 : Blo 2043435 2044795 := bstep (se 1 (by rfl) ⟨1533596, by rfl⟩ : syracuseStep 2044795 = 3067193) B3067193
theorem B11054389 : Blo 2043435 11054389 := bbase (se 5 (by rfl) ⟨518174, by rfl⟩ : syracuseStep 11054389 = 1036349) (by norm_num)
theorem B14739185 : Blo 2043435 14739185 := bstep (se 2 (by rfl) ⟨5527194, by rfl⟩ : syracuseStep 14739185 = 11054389) B11054389
theorem B9826123 : Blo 2043435 9826123 := bstep (se 1 (by rfl) ⟨7369592, by rfl⟩ : syracuseStep 9826123 = 14739185) B14739185
theorem B13101497 : Blo 2043435 13101497 := bstep (se 2 (by rfl) ⟨4913061, by rfl⟩ : syracuseStep 13101497 = 9826123) B9826123
theorem B8734331 : Blo 2043435 8734331 := bstep (se 1 (by rfl) ⟨6550748, by rfl⟩ : syracuseStep 8734331 = 13101497) B13101497
theorem B23291549 : Blo 2043435 23291549 := bstep (se 3 (by rfl) ⟨4367165, by rfl⟩ : syracuseStep 23291549 = 8734331) B8734331
theorem B15527699 : Blo 2043435 15527699 := bstep (se 1 (by rfl) ⟨11645774, by rfl⟩ : syracuseStep 15527699 = 23291549) B23291549
theorem B10351799 : Blo 2043435 10351799 := bstep (se 1 (by rfl) ⟨7763849, by rfl⟩ : syracuseStep 10351799 = 15527699) B15527699
theorem B6901199 : Blo 2043435 6901199 := bstep (se 1 (by rfl) ⟨5175899, by rfl⟩ : syracuseStep 6901199 = 10351799) B10351799
theorem B4600799 : Blo 2043435 4600799 := bstep (se 1 (by rfl) ⟨3450599, by rfl⟩ : syracuseStep 4600799 = 6901199) B6901199
theorem B3067199 : Blo 2043435 3067199 := bstep (se 1 (by rfl) ⟨2300399, by rfl⟩ : syracuseStep 3067199 = 4600799) B4600799
theorem B2044799 : Blo 2043435 2044799 := bstep (se 1 (by rfl) ⟨1533599, by rfl⟩ : syracuseStep 2044799 = 3067199) B3067199
theorem B3067205 : Blo 2043435 3067205 := bbase (se 4 (by rfl) ⟨287550, by rfl⟩ : syracuseStep 3067205 = 575101) (by norm_num)
theorem B2044803 : Blo 2043435 2044803 := bstep (se 1 (by rfl) ⟨1533602, by rfl⟩ : syracuseStep 2044803 = 3067205) B3067205
theorem B3450613 : Blo 2043435 3450613 := bbase (se 5 (by rfl) ⟨161747, by rfl⟩ : syracuseStep 3450613 = 323495) (by norm_num)
theorem B4600817 : Blo 2043435 4600817 := bstep (se 2 (by rfl) ⟨1725306, by rfl⟩ : syracuseStep 4600817 = 3450613) B3450613
theorem B3067211 : Blo 2043435 3067211 := bstep (se 1 (by rfl) ⟨2300408, by rfl⟩ : syracuseStep 3067211 = 4600817) B4600817
theorem B2044807 : Blo 2043435 2044807 := bstep (se 1 (by rfl) ⟨1533605, by rfl⟩ : syracuseStep 2044807 = 3067211) B3067211
theorem B2300413 : Blo 2043435 2300413 := bbase (se 3 (by rfl) ⟨431327, by rfl⟩ : syracuseStep 2300413 = 862655) (by norm_num)
theorem B3067217 : Blo 2043435 3067217 := bstep (se 2 (by rfl) ⟨1150206, by rfl⟩ : syracuseStep 3067217 = 2300413) B2300413
theorem B2044811 : Blo 2043435 2044811 := bstep (se 1 (by rfl) ⟨1533608, by rfl⟩ : syracuseStep 2044811 = 3067217) B3067217
theorem B6901253 : Blo 2043435 6901253 := bbase (se 4 (by rfl) ⟨646992, by rfl⟩ : syracuseStep 6901253 = 1293985) (by norm_num)
theorem B4600835 : Blo 2043435 4600835 := bstep (se 1 (by rfl) ⟨3450626, by rfl⟩ : syracuseStep 4600835 = 6901253) B6901253
theorem B3067223 : Blo 2043435 3067223 := bstep (se 1 (by rfl) ⟨2300417, by rfl⟩ : syracuseStep 3067223 = 4600835) B4600835
theorem B2044815 : Blo 2043435 2044815 := bstep (se 1 (by rfl) ⟨1533611, by rfl⟩ : syracuseStep 2044815 = 3067223) B3067223
theorem B3067229 : Blo 2043435 3067229 := bbase (se 3 (by rfl) ⟨575105, by rfl⟩ : syracuseStep 3067229 = 1150211) (by norm_num)
theorem B2044819 : Blo 2043435 2044819 := bstep (se 1 (by rfl) ⟨1533614, by rfl⟩ : syracuseStep 2044819 = 3067229) B3067229
theorem B4600853 : Blo 2043435 4600853 := bbase (se 6 (by rfl) ⟨107832, by rfl⟩ : syracuseStep 4600853 = 215665) (by norm_num)
theorem B3067235 : Blo 2043435 3067235 := bstep (se 1 (by rfl) ⟨2300426, by rfl⟩ : syracuseStep 3067235 = 4600853) B4600853
theorem B2044823 : Blo 2043435 2044823 := bstep (se 1 (by rfl) ⟨1533617, by rfl⟩ : syracuseStep 2044823 = 3067235) B3067235
theorem B7763957 : Blo 2043435 7763957 := bbase (se 5 (by rfl) ⟨363935, by rfl⟩ : syracuseStep 7763957 = 727871) (by norm_num)
theorem B5175971 : Blo 2043435 5175971 := bstep (se 1 (by rfl) ⟨3881978, by rfl⟩ : syracuseStep 5175971 = 7763957) B7763957
theorem B3450647 : Blo 2043435 3450647 := bstep (se 1 (by rfl) ⟨2587985, by rfl⟩ : syracuseStep 3450647 = 5175971) B5175971
theorem B2300431 : Blo 2043435 2300431 := bstep (se 1 (by rfl) ⟨1725323, by rfl⟩ : syracuseStep 2300431 = 3450647) B3450647
theorem B3067241 : Blo 2043435 3067241 := bstep (se 2 (by rfl) ⟨1150215, by rfl⟩ : syracuseStep 3067241 = 2300431) B2300431
theorem B2044827 : Blo 2043435 2044827 := bstep (se 1 (by rfl) ⟨1533620, by rfl⟩ : syracuseStep 2044827 = 3067241) B3067241
theorem B2183617 : Blo 2043435 2183617 := bbase (se 2 (by rfl) ⟨818856, by rfl⟩ : syracuseStep 2183617 = 1637713) (by norm_num)
theorem B11645957 : Blo 2043435 11645957 := bstep (se 4 (by rfl) ⟨1091808, by rfl⟩ : syracuseStep 11645957 = 2183617) B2183617
theorem B7763971 : Blo 2043435 7763971 := bstep (se 1 (by rfl) ⟨5822978, by rfl⟩ : syracuseStep 7763971 = 11645957) B11645957
theorem B10351961 : Blo 2043435 10351961 := bstep (se 2 (by rfl) ⟨3881985, by rfl⟩ : syracuseStep 10351961 = 7763971) B7763971
theorem B6901307 : Blo 2043435 6901307 := bstep (se 1 (by rfl) ⟨5175980, by rfl⟩ : syracuseStep 6901307 = 10351961) B10351961
theorem B4600871 : Blo 2043435 4600871 := bstep (se 1 (by rfl) ⟨3450653, by rfl⟩ : syracuseStep 4600871 = 6901307) B6901307
theorem B3067247 : Blo 2043435 3067247 := bstep (se 1 (by rfl) ⟨2300435, by rfl⟩ : syracuseStep 3067247 = 4600871) B4600871
theorem B2044831 : Blo 2043435 2044831 := bstep (se 1 (by rfl) ⟨1533623, by rfl⟩ : syracuseStep 2044831 = 3067247) B3067247
theorem B3067253 : Blo 2043435 3067253 := bbase (se 5 (by rfl) ⟨143777, by rfl⟩ : syracuseStep 3067253 = 287555) (by norm_num)
theorem B2044835 : Blo 2043435 2044835 := bstep (se 1 (by rfl) ⟨1533626, by rfl⟩ : syracuseStep 2044835 = 3067253) B3067253
theorem B2911501 : Blo 2043435 2911501 := bbase (se 3 (by rfl) ⟨545906, by rfl⟩ : syracuseStep 2911501 = 1091813) (by norm_num)
theorem B3882001 : Blo 2043435 3882001 := bstep (se 2 (by rfl) ⟨1455750, by rfl⟩ : syracuseStep 3882001 = 2911501) B2911501
theorem B5176001 : Blo 2043435 5176001 := bstep (se 2 (by rfl) ⟨1941000, by rfl⟩ : syracuseStep 5176001 = 3882001) B3882001
theorem B3450667 : Blo 2043435 3450667 := bstep (se 1 (by rfl) ⟨2588000, by rfl⟩ : syracuseStep 3450667 = 5176001) B5176001
theorem B4600889 : Blo 2043435 4600889 := bstep (se 2 (by rfl) ⟨1725333, by rfl⟩ : syracuseStep 4600889 = 3450667) B3450667
theorem B3067259 : Blo 2043435 3067259 := bstep (se 1 (by rfl) ⟨2300444, by rfl⟩ : syracuseStep 3067259 = 4600889) B4600889
theorem B2044839 : Blo 2043435 2044839 := bstep (se 1 (by rfl) ⟨1533629, by rfl⟩ : syracuseStep 2044839 = 3067259) B3067259
theorem B2300449 : Blo 2043435 2300449 := bbase (se 2 (by rfl) ⟨862668, by rfl⟩ : syracuseStep 2300449 = 1725337) (by norm_num)
theorem B3067265 : Blo 2043435 3067265 := bstep (se 2 (by rfl) ⟨1150224, by rfl⟩ : syracuseStep 3067265 = 2300449) B2300449
theorem B2044843 : Blo 2043435 2044843 := bstep (se 1 (by rfl) ⟨1533632, by rfl⟩ : syracuseStep 2044843 = 3067265) B3067265
theorem B5176021 : Blo 2043435 5176021 := bbase (se 7 (by rfl) ⟨60656, by rfl⟩ : syracuseStep 5176021 = 121313) (by norm_num)
theorem B6901361 : Blo 2043435 6901361 := bstep (se 2 (by rfl) ⟨2588010, by rfl⟩ : syracuseStep 6901361 = 5176021) B5176021
theorem B4600907 : Blo 2043435 4600907 := bstep (se 1 (by rfl) ⟨3450680, by rfl⟩ : syracuseStep 4600907 = 6901361) B6901361
theorem B3067271 : Blo 2043435 3067271 := bstep (se 1 (by rfl) ⟨2300453, by rfl⟩ : syracuseStep 3067271 = 4600907) B4600907
theorem B2044847 : Blo 2043435 2044847 := bstep (se 1 (by rfl) ⟨1533635, by rfl⟩ : syracuseStep 2044847 = 3067271) B3067271
theorem B3067277 : Blo 2043435 3067277 := bbase (se 3 (by rfl) ⟨575114, by rfl⟩ : syracuseStep 3067277 = 1150229) (by norm_num)
theorem B2044851 : Blo 2043435 2044851 := bstep (se 1 (by rfl) ⟨1533638, by rfl⟩ : syracuseStep 2044851 = 3067277) B3067277
theorem B4600925 : Blo 2043435 4600925 := bbase (se 3 (by rfl) ⟨862673, by rfl⟩ : syracuseStep 4600925 = 1725347) (by norm_num)
theorem B3067283 : Blo 2043435 3067283 := bstep (se 1 (by rfl) ⟨2300462, by rfl⟩ : syracuseStep 3067283 = 4600925) B4600925
theorem B2044855 : Blo 2043435 2044855 := bstep (se 1 (by rfl) ⟨1533641, by rfl⟩ : syracuseStep 2044855 = 3067283) B3067283
theorem B3450701 : Blo 2043435 3450701 := bbase (se 3 (by rfl) ⟨647006, by rfl⟩ : syracuseStep 3450701 = 1294013) (by norm_num)
theorem B2300467 : Blo 2043435 2300467 := bstep (se 1 (by rfl) ⟨1725350, by rfl⟩ : syracuseStep 2300467 = 3450701) B3450701
theorem B3067289 : Blo 2043435 3067289 := bstep (se 2 (by rfl) ⟨1150233, by rfl⟩ : syracuseStep 3067289 = 2300467) B2300467
theorem B2044859 : Blo 2043435 2044859 := bstep (se 1 (by rfl) ⟨1533644, by rfl⟩ : syracuseStep 2044859 = 3067289) B3067289
theorem B5902517 : Blo 2043435 5902517 := bbase (se 5 (by rfl) ⟨276680, by rfl⟩ : syracuseStep 5902517 = 553361) (by norm_num)
theorem B15740045 : Blo 2043435 15740045 := bstep (se 3 (by rfl) ⟨2951258, by rfl⟩ : syracuseStep 15740045 = 5902517) B5902517
theorem B10493363 : Blo 2043435 10493363 := bstep (se 1 (by rfl) ⟨7870022, by rfl⟩ : syracuseStep 10493363 = 15740045) B15740045
theorem B6995575 : Blo 2043435 6995575 := bstep (se 1 (by rfl) ⟨5246681, by rfl⟩ : syracuseStep 6995575 = 10493363) B10493363
theorem B37309733 : Blo 2043435 37309733 := bstep (se 4 (by rfl) ⟨3497787, by rfl⟩ : syracuseStep 37309733 = 6995575) B6995575
theorem B24873155 : Blo 2043435 24873155 := bstep (se 1 (by rfl) ⟨18654866, by rfl⟩ : syracuseStep 24873155 = 37309733) B37309733
theorem B16582103 : Blo 2043435 16582103 := bstep (se 1 (by rfl) ⟨12436577, by rfl⟩ : syracuseStep 16582103 = 24873155) B24873155
theorem B11054735 : Blo 2043435 11054735 := bstep (se 1 (by rfl) ⟨8291051, by rfl⟩ : syracuseStep 11054735 = 16582103) B16582103
theorem B7369823 : Blo 2043435 7369823 := bstep (se 1 (by rfl) ⟨5527367, by rfl⟩ : syracuseStep 7369823 = 11054735) B11054735
theorem B19652861 : Blo 2043435 19652861 := bstep (se 3 (by rfl) ⟨3684911, by rfl⟩ : syracuseStep 19652861 = 7369823) B7369823
theorem B13101907 : Blo 2043435 13101907 := bstep (se 1 (by rfl) ⟨9826430, by rfl⟩ : syracuseStep 13101907 = 19652861) B19652861
theorem B17469209 : Blo 2043435 17469209 := bstep (se 2 (by rfl) ⟨6550953, by rfl⟩ : syracuseStep 17469209 = 13101907) B13101907
theorem B11646139 : Blo 2043435 11646139 := bstep (se 1 (by rfl) ⟨8734604, by rfl⟩ : syracuseStep 11646139 = 17469209) B17469209
theorem B15528185 : Blo 2043435 15528185 := bstep (se 2 (by rfl) ⟨5823069, by rfl⟩ : syracuseStep 15528185 = 11646139) B11646139
theorem B10352123 : Blo 2043435 10352123 := bstep (se 1 (by rfl) ⟨7764092, by rfl⟩ : syracuseStep 10352123 = 15528185) B15528185
theorem B6901415 : Blo 2043435 6901415 := bstep (se 1 (by rfl) ⟨5176061, by rfl⟩ : syracuseStep 6901415 = 10352123) B10352123
theorem B4600943 : Blo 2043435 4600943 := bstep (se 1 (by rfl) ⟨3450707, by rfl⟩ : syracuseStep 4600943 = 6901415) B6901415
theorem B3067295 : Blo 2043435 3067295 := bstep (se 1 (by rfl) ⟨2300471, by rfl⟩ : syracuseStep 3067295 = 4600943) B4600943
theorem B2044863 : Blo 2043435 2044863 := bstep (se 1 (by rfl) ⟨1533647, by rfl⟩ : syracuseStep 2044863 = 3067295) B3067295
theorem B3067301 : Blo 2043435 3067301 := bbase (se 4 (by rfl) ⟨287559, by rfl⟩ : syracuseStep 3067301 = 575119) (by norm_num)
theorem B2044867 : Blo 2043435 2044867 := bstep (se 1 (by rfl) ⟨1533650, by rfl⟩ : syracuseStep 2044867 = 3067301) B3067301
theorem B2588041 : Blo 2043435 2588041 := bbase (se 2 (by rfl) ⟨970515, by rfl⟩ : syracuseStep 2588041 = 1941031) (by norm_num)
theorem B3450721 : Blo 2043435 3450721 := bstep (se 2 (by rfl) ⟨1294020, by rfl⟩ : syracuseStep 3450721 = 2588041) B2588041
theorem B4600961 : Blo 2043435 4600961 := bstep (se 2 (by rfl) ⟨1725360, by rfl⟩ : syracuseStep 4600961 = 3450721) B3450721
theorem B3067307 : Blo 2043435 3067307 := bstep (se 1 (by rfl) ⟨2300480, by rfl⟩ : syracuseStep 3067307 = 4600961) B4600961
theorem B2044871 : Blo 2043435 2044871 := bstep (se 1 (by rfl) ⟨1533653, by rfl⟩ : syracuseStep 2044871 = 3067307) B3067307
theorem B2300485 : Blo 2043435 2300485 := bbase (se 4 (by rfl) ⟨215670, by rfl⟩ : syracuseStep 2300485 = 431341) (by norm_num)
theorem B3067313 : Blo 2043435 3067313 := bstep (se 2 (by rfl) ⟨1150242, by rfl⟩ : syracuseStep 3067313 = 2300485) B2300485
theorem B2044875 : Blo 2043435 2044875 := bstep (se 1 (by rfl) ⟨1533656, by rfl⟩ : syracuseStep 2044875 = 3067313) B3067313
theorem B3882077 : Blo 2043435 3882077 := bbase (se 3 (by rfl) ⟨727889, by rfl⟩ : syracuseStep 3882077 = 1455779) (by norm_num)
theorem B2588051 : Blo 2043435 2588051 := bstep (se 1 (by rfl) ⟨1941038, by rfl⟩ : syracuseStep 2588051 = 3882077) B3882077
theorem B6901469 : Blo 2043435 6901469 := bstep (se 3 (by rfl) ⟨1294025, by rfl⟩ : syracuseStep 6901469 = 2588051) B2588051
theorem B4600979 : Blo 2043435 4600979 := bstep (se 1 (by rfl) ⟨3450734, by rfl⟩ : syracuseStep 4600979 = 6901469) B6901469
theorem B3067319 : Blo 2043435 3067319 := bstep (se 1 (by rfl) ⟨2300489, by rfl⟩ : syracuseStep 3067319 = 4600979) B4600979
theorem B2044879 : Blo 2043435 2044879 := bstep (se 1 (by rfl) ⟨1533659, by rfl⟩ : syracuseStep 2044879 = 3067319) B3067319
theorem B3067325 : Blo 2043435 3067325 := bbase (se 3 (by rfl) ⟨575123, by rfl⟩ : syracuseStep 3067325 = 1150247) (by norm_num)
theorem B2044883 : Blo 2043435 2044883 := bstep (se 1 (by rfl) ⟨1533662, by rfl⟩ : syracuseStep 2044883 = 3067325) B3067325
theorem B4600997 : Blo 2043435 4600997 := bbase (se 4 (by rfl) ⟨431343, by rfl⟩ : syracuseStep 4600997 = 862687) (by norm_num)
theorem B3067331 : Blo 2043435 3067331 := bstep (se 1 (by rfl) ⟨2300498, by rfl⟩ : syracuseStep 3067331 = 4600997) B4600997
theorem B2044887 : Blo 2043435 2044887 := bstep (se 1 (by rfl) ⟨1533665, by rfl⟩ : syracuseStep 2044887 = 3067331) B3067331
theorem B5176133 : Blo 2043435 5176133 := bbase (se 4 (by rfl) ⟨485262, by rfl⟩ : syracuseStep 5176133 = 970525) (by norm_num)
theorem B3450755 : Blo 2043435 3450755 := bstep (se 1 (by rfl) ⟨2588066, by rfl⟩ : syracuseStep 3450755 = 5176133) B5176133
theorem B2300503 : Blo 2043435 2300503 := bstep (se 1 (by rfl) ⟨1725377, by rfl⟩ : syracuseStep 2300503 = 3450755) B3450755
theorem B3067337 : Blo 2043435 3067337 := bstep (se 2 (by rfl) ⟨1150251, by rfl⟩ : syracuseStep 3067337 = 2300503) B2300503
theorem B2044891 : Blo 2043435 2044891 := bstep (se 1 (by rfl) ⟨1533668, by rfl⟩ : syracuseStep 2044891 = 3067337) B3067337
theorem B4913293 : Blo 2043435 4913293 := bbase (se 3 (by rfl) ⟨921242, by rfl⟩ : syracuseStep 4913293 = 1842485) (by norm_num)
theorem B6551057 : Blo 2043435 6551057 := bstep (se 2 (by rfl) ⟨2456646, by rfl⟩ : syracuseStep 6551057 = 4913293) B4913293
theorem B4367371 : Blo 2043435 4367371 := bstep (se 1 (by rfl) ⟨3275528, by rfl⟩ : syracuseStep 4367371 = 6551057) B6551057
theorem B5823161 : Blo 2043435 5823161 := bstep (se 2 (by rfl) ⟨2183685, by rfl⟩ : syracuseStep 5823161 = 4367371) B4367371
theorem B3882107 : Blo 2043435 3882107 := bstep (se 1 (by rfl) ⟨2911580, by rfl⟩ : syracuseStep 3882107 = 5823161) B5823161
theorem B10352285 : Blo 2043435 10352285 := bstep (se 3 (by rfl) ⟨1941053, by rfl⟩ : syracuseStep 10352285 = 3882107) B3882107
theorem B6901523 : Blo 2043435 6901523 := bstep (se 1 (by rfl) ⟨5176142, by rfl⟩ : syracuseStep 6901523 = 10352285) B10352285
theorem B4601015 : Blo 2043435 4601015 := bstep (se 1 (by rfl) ⟨3450761, by rfl⟩ : syracuseStep 4601015 = 6901523) B6901523
theorem B3067343 : Blo 2043435 3067343 := bstep (se 1 (by rfl) ⟨2300507, by rfl⟩ : syracuseStep 3067343 = 4601015) B4601015
theorem B2044895 : Blo 2043435 2044895 := bstep (se 1 (by rfl) ⟨1533671, by rfl⟩ : syracuseStep 2044895 = 3067343) B3067343
theorem B3067349 : Blo 2043435 3067349 := bbase (se 7 (by rfl) ⟨35945, by rfl⟩ : syracuseStep 3067349 = 71891) (by norm_num)
theorem B2044899 : Blo 2043435 2044899 := bstep (se 1 (by rfl) ⟨1533674, by rfl⟩ : syracuseStep 2044899 = 3067349) B3067349
theorem B7764245 : Blo 2043435 7764245 := bbase (se 6 (by rfl) ⟨181974, by rfl⟩ : syracuseStep 7764245 = 363949) (by norm_num)
theorem B5176163 : Blo 2043435 5176163 := bstep (se 1 (by rfl) ⟨3882122, by rfl⟩ : syracuseStep 5176163 = 7764245) B7764245
theorem B3450775 : Blo 2043435 3450775 := bstep (se 1 (by rfl) ⟨2588081, by rfl⟩ : syracuseStep 3450775 = 5176163) B5176163
theorem B4601033 : Blo 2043435 4601033 := bstep (se 2 (by rfl) ⟨1725387, by rfl⟩ : syracuseStep 4601033 = 3450775) B3450775
theorem B3067355 : Blo 2043435 3067355 := bstep (se 1 (by rfl) ⟨2300516, by rfl⟩ : syracuseStep 3067355 = 4601033) B4601033
theorem B2044903 : Blo 2043435 2044903 := bstep (se 1 (by rfl) ⟨1533677, by rfl⟩ : syracuseStep 2044903 = 3067355) B3067355
theorem B2300521 : Blo 2043435 2300521 := bbase (se 2 (by rfl) ⟨862695, by rfl⟩ : syracuseStep 2300521 = 1725391) (by norm_num)
theorem B3067361 : Blo 2043435 3067361 := bstep (se 2 (by rfl) ⟨1150260, by rfl⟩ : syracuseStep 3067361 = 2300521) B2300521
theorem B2044907 : Blo 2043435 2044907 := bstep (se 1 (by rfl) ⟨1533680, by rfl⟩ : syracuseStep 2044907 = 3067361) B3067361
theorem B4367405 : Blo 2043435 4367405 := bbase (se 3 (by rfl) ⟨818888, by rfl⟩ : syracuseStep 4367405 = 1637777) (by norm_num)
theorem B11646413 : Blo 2043435 11646413 := bstep (se 3 (by rfl) ⟨2183702, by rfl⟩ : syracuseStep 11646413 = 4367405) B4367405
theorem B7764275 : Blo 2043435 7764275 := bstep (se 1 (by rfl) ⟨5823206, by rfl⟩ : syracuseStep 7764275 = 11646413) B11646413
theorem B5176183 : Blo 2043435 5176183 := bstep (se 1 (by rfl) ⟨3882137, by rfl⟩ : syracuseStep 5176183 = 7764275) B7764275
theorem B6901577 : Blo 2043435 6901577 := bstep (se 2 (by rfl) ⟨2588091, by rfl⟩ : syracuseStep 6901577 = 5176183) B5176183
theorem B4601051 : Blo 2043435 4601051 := bstep (se 1 (by rfl) ⟨3450788, by rfl⟩ : syracuseStep 4601051 = 6901577) B6901577
theorem B3067367 : Blo 2043435 3067367 := bstep (se 1 (by rfl) ⟨2300525, by rfl⟩ : syracuseStep 3067367 = 4601051) B4601051
theorem B2044911 : Blo 2043435 2044911 := bstep (se 1 (by rfl) ⟨1533683, by rfl⟩ : syracuseStep 2044911 = 3067367) B3067367
theorem B3067373 : Blo 2043435 3067373 := bbase (se 3 (by rfl) ⟨575132, by rfl⟩ : syracuseStep 3067373 = 1150265) (by norm_num)
theorem B2044915 : Blo 2043435 2044915 := bstep (se 1 (by rfl) ⟨1533686, by rfl⟩ : syracuseStep 2044915 = 3067373) B3067373
theorem B4601069 : Blo 2043435 4601069 := bbase (se 3 (by rfl) ⟨862700, by rfl⟩ : syracuseStep 4601069 = 1725401) (by norm_num)
theorem B3067379 : Blo 2043435 3067379 := bstep (se 1 (by rfl) ⟨2300534, by rfl⟩ : syracuseStep 3067379 = 4601069) B4601069
theorem B2044919 : Blo 2043435 2044919 := bstep (se 1 (by rfl) ⟨1533689, by rfl⟩ : syracuseStep 2044919 = 3067379) B3067379
theorem B2911621 : Blo 2043435 2911621 := bbase (se 4 (by rfl) ⟨272964, by rfl⟩ : syracuseStep 2911621 = 545929) (by norm_num)
theorem B3882161 : Blo 2043435 3882161 := bstep (se 2 (by rfl) ⟨1455810, by rfl⟩ : syracuseStep 3882161 = 2911621) B2911621
theorem B2588107 : Blo 2043435 2588107 := bstep (se 1 (by rfl) ⟨1941080, by rfl⟩ : syracuseStep 2588107 = 3882161) B3882161
theorem B3450809 : Blo 2043435 3450809 := bstep (se 2 (by rfl) ⟨1294053, by rfl⟩ : syracuseStep 3450809 = 2588107) B2588107
theorem B2300539 : Blo 2043435 2300539 := bstep (se 1 (by rfl) ⟨1725404, by rfl⟩ : syracuseStep 2300539 = 3450809) B3450809
theorem B3067385 : Blo 2043435 3067385 := bstep (se 2 (by rfl) ⟨1150269, by rfl⟩ : syracuseStep 3067385 = 2300539) B2300539
theorem B2044923 : Blo 2043435 2044923 := bstep (se 1 (by rfl) ⟨1533692, by rfl⟩ : syracuseStep 2044923 = 3067385) B3067385
theorem B29480213 : Blo 2043435 29480213 := bbase (se 6 (by rfl) ⟨690942, by rfl⟩ : syracuseStep 29480213 = 1381885) (by norm_num)
theorem B78613901 : Blo 2043435 78613901 := bstep (se 3 (by rfl) ⟨14740106, by rfl⟩ : syracuseStep 78613901 = 29480213) B29480213
theorem B52409267 : Blo 2043435 52409267 := bstep (se 1 (by rfl) ⟨39306950, by rfl⟩ : syracuseStep 52409267 = 78613901) B78613901
theorem B34939511 : Blo 2043435 34939511 := bstep (se 1 (by rfl) ⟨26204633, by rfl⟩ : syracuseStep 34939511 = 52409267) B52409267
theorem B23293007 : Blo 2043435 23293007 := bstep (se 1 (by rfl) ⟨17469755, by rfl⟩ : syracuseStep 23293007 = 34939511) B34939511
theorem B15528671 : Blo 2043435 15528671 := bstep (se 1 (by rfl) ⟨11646503, by rfl⟩ : syracuseStep 15528671 = 23293007) B23293007
theorem B10352447 : Blo 2043435 10352447 := bstep (se 1 (by rfl) ⟨7764335, by rfl⟩ : syracuseStep 10352447 = 15528671) B15528671
theorem B6901631 : Blo 2043435 6901631 := bstep (se 1 (by rfl) ⟨5176223, by rfl⟩ : syracuseStep 6901631 = 10352447) B10352447
theorem B4601087 : Blo 2043435 4601087 := bstep (se 1 (by rfl) ⟨3450815, by rfl⟩ : syracuseStep 4601087 = 6901631) B6901631
theorem B3067391 : Blo 2043435 3067391 := bstep (se 1 (by rfl) ⟨2300543, by rfl⟩ : syracuseStep 3067391 = 4601087) B4601087
theorem B2044927 : Blo 2043435 2044927 := bstep (se 1 (by rfl) ⟨1533695, by rfl⟩ : syracuseStep 2044927 = 3067391) B3067391
theorem B3067397 : Blo 2043435 3067397 := bbase (se 4 (by rfl) ⟨287568, by rfl⟩ : syracuseStep 3067397 = 575137) (by norm_num)
theorem B2044931 : Blo 2043435 2044931 := bstep (se 1 (by rfl) ⟨1533698, by rfl⟩ : syracuseStep 2044931 = 3067397) B3067397
theorem B3450829 : Blo 2043435 3450829 := bbase (se 3 (by rfl) ⟨647030, by rfl⟩ : syracuseStep 3450829 = 1294061) (by norm_num)
theorem B4601105 : Blo 2043435 4601105 := bstep (se 2 (by rfl) ⟨1725414, by rfl⟩ : syracuseStep 4601105 = 3450829) B3450829
theorem B3067403 : Blo 2043435 3067403 := bstep (se 1 (by rfl) ⟨2300552, by rfl⟩ : syracuseStep 3067403 = 4601105) B4601105
theorem B2044935 : Blo 2043435 2044935 := bstep (se 1 (by rfl) ⟨1533701, by rfl⟩ : syracuseStep 2044935 = 3067403) B3067403
theorem B2300557 : Blo 2043435 2300557 := bbase (se 3 (by rfl) ⟨431354, by rfl⟩ : syracuseStep 2300557 = 862709) (by norm_num)
theorem B3067409 : Blo 2043435 3067409 := bstep (se 2 (by rfl) ⟨1150278, by rfl⟩ : syracuseStep 3067409 = 2300557) B2300557
theorem B2044939 : Blo 2043435 2044939 := bstep (se 1 (by rfl) ⟨1533704, by rfl⟩ : syracuseStep 2044939 = 3067409) B3067409
theorem B6901685 : Blo 2043435 6901685 := bbase (se 5 (by rfl) ⟨323516, by rfl⟩ : syracuseStep 6901685 = 647033) (by norm_num)
theorem B4601123 : Blo 2043435 4601123 := bstep (se 1 (by rfl) ⟨3450842, by rfl⟩ : syracuseStep 4601123 = 6901685) B6901685
theorem B3067415 : Blo 2043435 3067415 := bstep (se 1 (by rfl) ⟨2300561, by rfl⟩ : syracuseStep 3067415 = 4601123) B4601123
theorem B2044943 : Blo 2043435 2044943 := bstep (se 1 (by rfl) ⟨1533707, by rfl⟩ : syracuseStep 2044943 = 3067415) B3067415
theorem B3067421 : Blo 2043435 3067421 := bbase (se 3 (by rfl) ⟨575141, by rfl⟩ : syracuseStep 3067421 = 1150283) (by norm_num)
theorem B2044947 : Blo 2043435 2044947 := bstep (se 1 (by rfl) ⟨1533710, by rfl⟩ : syracuseStep 2044947 = 3067421) B3067421
theorem B4601141 : Blo 2043435 4601141 := bbase (se 5 (by rfl) ⟨215678, by rfl⟩ : syracuseStep 4601141 = 431357) (by norm_num)
theorem B3067427 : Blo 2043435 3067427 := bstep (se 1 (by rfl) ⟨2300570, by rfl⟩ : syracuseStep 3067427 = 4601141) B4601141
theorem B2044951 : Blo 2043435 2044951 := bstep (se 1 (by rfl) ⟨1533713, by rfl⟩ : syracuseStep 2044951 = 3067427) B3067427
theorem B19653749 : Blo 2043435 19653749 := bbase (se 5 (by rfl) ⟨921269, by rfl⟩ : syracuseStep 19653749 = 1842539) (by norm_num)
theorem B13102499 : Blo 2043435 13102499 := bstep (se 1 (by rfl) ⟨9826874, by rfl⟩ : syracuseStep 13102499 = 19653749) B19653749
theorem B8734999 : Blo 2043435 8734999 := bstep (se 1 (by rfl) ⟨6551249, by rfl⟩ : syracuseStep 8734999 = 13102499) B13102499
theorem B11646665 : Blo 2043435 11646665 := bstep (se 2 (by rfl) ⟨4367499, by rfl⟩ : syracuseStep 11646665 = 8734999) B8734999
theorem B7764443 : Blo 2043435 7764443 := bstep (se 1 (by rfl) ⟨5823332, by rfl⟩ : syracuseStep 7764443 = 11646665) B11646665
theorem B5176295 : Blo 2043435 5176295 := bstep (se 1 (by rfl) ⟨3882221, by rfl⟩ : syracuseStep 5176295 = 7764443) B7764443
theorem B3450863 : Blo 2043435 3450863 := bstep (se 1 (by rfl) ⟨2588147, by rfl⟩ : syracuseStep 3450863 = 5176295) B5176295
theorem B2300575 : Blo 2043435 2300575 := bstep (se 1 (by rfl) ⟨1725431, by rfl⟩ : syracuseStep 2300575 = 3450863) B3450863
theorem B3067433 : Blo 2043435 3067433 := bstep (se 2 (by rfl) ⟨1150287, by rfl⟩ : syracuseStep 3067433 = 2300575) B2300575
theorem B2044955 : Blo 2043435 2044955 := bstep (se 1 (by rfl) ⟨1533716, by rfl⟩ : syracuseStep 2044955 = 3067433) B3067433
theorem B6218581 : Blo 2043435 6218581 := bbase (se 9 (by rfl) ⟨18218, by rfl⟩ : syracuseStep 6218581 = 36437) (by norm_num)
theorem B8291441 : Blo 2043435 8291441 := bstep (se 2 (by rfl) ⟨3109290, by rfl⟩ : syracuseStep 8291441 = 6218581) B6218581
theorem B22110509 : Blo 2043435 22110509 := bstep (se 3 (by rfl) ⟨4145720, by rfl⟩ : syracuseStep 22110509 = 8291441) B8291441
theorem B14740339 : Blo 2043435 14740339 := bstep (se 1 (by rfl) ⟨11055254, by rfl⟩ : syracuseStep 14740339 = 22110509) B22110509
theorem B19653785 : Blo 2043435 19653785 := bstep (se 2 (by rfl) ⟨7370169, by rfl⟩ : syracuseStep 19653785 = 14740339) B14740339
theorem B13102523 : Blo 2043435 13102523 := bstep (se 1 (by rfl) ⟨9826892, by rfl⟩ : syracuseStep 13102523 = 19653785) B19653785
theorem B8735015 : Blo 2043435 8735015 := bstep (se 1 (by rfl) ⟨6551261, by rfl⟩ : syracuseStep 8735015 = 13102523) B13102523
theorem B5823343 : Blo 2043435 5823343 := bstep (se 1 (by rfl) ⟨4367507, by rfl⟩ : syracuseStep 5823343 = 8735015) B8735015
theorem B7764457 : Blo 2043435 7764457 := bstep (se 2 (by rfl) ⟨2911671, by rfl⟩ : syracuseStep 7764457 = 5823343) B5823343
theorem B10352609 : Blo 2043435 10352609 := bstep (se 2 (by rfl) ⟨3882228, by rfl⟩ : syracuseStep 10352609 = 7764457) B7764457
theorem B6901739 : Blo 2043435 6901739 := bstep (se 1 (by rfl) ⟨5176304, by rfl⟩ : syracuseStep 6901739 = 10352609) B10352609
theorem B4601159 : Blo 2043435 4601159 := bstep (se 1 (by rfl) ⟨3450869, by rfl⟩ : syracuseStep 4601159 = 6901739) B6901739
theorem B3067439 : Blo 2043435 3067439 := bstep (se 1 (by rfl) ⟨2300579, by rfl⟩ : syracuseStep 3067439 = 4601159) B4601159
theorem B2044959 : Blo 2043435 2044959 := bstep (se 1 (by rfl) ⟨1533719, by rfl⟩ : syracuseStep 2044959 = 3067439) B3067439
theorem B3067445 : Blo 2043435 3067445 := bbase (se 5 (by rfl) ⟨143786, by rfl⟩ : syracuseStep 3067445 = 287573) (by norm_num)
theorem B2044963 : Blo 2043435 2044963 := bstep (se 1 (by rfl) ⟨1533722, by rfl⟩ : syracuseStep 2044963 = 3067445) B3067445
theorem B5176325 : Blo 2043435 5176325 := bbase (se 4 (by rfl) ⟨485280, by rfl⟩ : syracuseStep 5176325 = 970561) (by norm_num)
theorem B3450883 : Blo 2043435 3450883 := bstep (se 1 (by rfl) ⟨2588162, by rfl⟩ : syracuseStep 3450883 = 5176325) B5176325
theorem B4601177 : Blo 2043435 4601177 := bstep (se 2 (by rfl) ⟨1725441, by rfl⟩ : syracuseStep 4601177 = 3450883) B3450883
theorem B3067451 : Blo 2043435 3067451 := bstep (se 1 (by rfl) ⟨2300588, by rfl⟩ : syracuseStep 3067451 = 4601177) B4601177
theorem B2044967 : Blo 2043435 2044967 := bstep (se 1 (by rfl) ⟨1533725, by rfl⟩ : syracuseStep 2044967 = 3067451) B3067451
theorem B2300593 : Blo 2043435 2300593 := bbase (se 2 (by rfl) ⟨862722, by rfl⟩ : syracuseStep 2300593 = 1725445) (by norm_num)
theorem B3067457 : Blo 2043435 3067457 := bstep (se 2 (by rfl) ⟨1150296, by rfl⟩ : syracuseStep 3067457 = 2300593) B2300593
theorem B2044971 : Blo 2043435 2044971 := bstep (se 1 (by rfl) ⟨1533728, by rfl⟩ : syracuseStep 2044971 = 3067457) B3067457
theorem B28365653 : Blo 2043435 28365653 := bbase (se 9 (by rfl) ⟨83102, by rfl⟩ : syracuseStep 28365653 = 166205) (by norm_num)
theorem B18910435 : Blo 2043435 18910435 := bstep (se 1 (by rfl) ⟨14182826, by rfl⟩ : syracuseStep 18910435 = 28365653) B28365653
theorem B25213913 : Blo 2043435 25213913 := bstep (se 2 (by rfl) ⟨9455217, by rfl⟩ : syracuseStep 25213913 = 18910435) B18910435
theorem B16809275 : Blo 2043435 16809275 := bstep (se 1 (by rfl) ⟨12606956, by rfl⟩ : syracuseStep 16809275 = 25213913) B25213913
theorem B11206183 : Blo 2043435 11206183 := bstep (se 1 (by rfl) ⟨8404637, by rfl⟩ : syracuseStep 11206183 = 16809275) B16809275
theorem B14941577 : Blo 2043435 14941577 := bstep (se 2 (by rfl) ⟨5603091, by rfl⟩ : syracuseStep 14941577 = 11206183) B11206183
theorem B9961051 : Blo 2043435 9961051 := bstep (se 1 (by rfl) ⟨7470788, by rfl⟩ : syracuseStep 9961051 = 14941577) B14941577
theorem B13281401 : Blo 2043435 13281401 := bstep (se 2 (by rfl) ⟨4980525, by rfl⟩ : syracuseStep 13281401 = 9961051) B9961051
theorem B8854267 : Blo 2043435 8854267 := bstep (se 1 (by rfl) ⟨6640700, by rfl⟩ : syracuseStep 8854267 = 13281401) B13281401
theorem B11805689 : Blo 2043435 11805689 := bstep (se 2 (by rfl) ⟨4427133, by rfl⟩ : syracuseStep 11805689 = 8854267) B8854267
theorem B7870459 : Blo 2043435 7870459 := bstep (se 1 (by rfl) ⟨5902844, by rfl⟩ : syracuseStep 7870459 = 11805689) B11805689
theorem B10493945 : Blo 2043435 10493945 := bstep (se 2 (by rfl) ⟨3935229, by rfl⟩ : syracuseStep 10493945 = 7870459) B7870459
theorem B6995963 : Blo 2043435 6995963 := bstep (se 1 (by rfl) ⟨5246972, by rfl⟩ : syracuseStep 6995963 = 10493945) B10493945
theorem B4663975 : Blo 2043435 4663975 := bstep (se 1 (by rfl) ⟨3497981, by rfl⟩ : syracuseStep 4663975 = 6995963) B6995963
theorem B6218633 : Blo 2043435 6218633 := bstep (se 2 (by rfl) ⟨2331987, by rfl⟩ : syracuseStep 6218633 = 4663975) B4663975
theorem B4145755 : Blo 2043435 4145755 := bstep (se 1 (by rfl) ⟨3109316, by rfl⟩ : syracuseStep 4145755 = 6218633) B6218633
theorem B5527673 : Blo 2043435 5527673 := bstep (se 2 (by rfl) ⟨2072877, by rfl⟩ : syracuseStep 5527673 = 4145755) B4145755
theorem B3685115 : Blo 2043435 3685115 := bstep (se 1 (by rfl) ⟨2763836, by rfl⟩ : syracuseStep 3685115 = 5527673) B5527673
theorem B2456743 : Blo 2043435 2456743 := bstep (se 1 (by rfl) ⟨1842557, by rfl⟩ : syracuseStep 2456743 = 3685115) B3685115
theorem B3275657 : Blo 2043435 3275657 := bstep (se 2 (by rfl) ⟨1228371, by rfl⟩ : syracuseStep 3275657 = 2456743) B2456743
theorem B2183771 : Blo 2043435 2183771 := bstep (se 1 (by rfl) ⟨1637828, by rfl⟩ : syracuseStep 2183771 = 3275657) B3275657
theorem B5823389 : Blo 2043435 5823389 := bstep (se 3 (by rfl) ⟨1091885, by rfl⟩ : syracuseStep 5823389 = 2183771) B2183771
theorem B3882259 : Blo 2043435 3882259 := bstep (se 1 (by rfl) ⟨2911694, by rfl⟩ : syracuseStep 3882259 = 5823389) B5823389
theorem B5176345 : Blo 2043435 5176345 := bstep (se 2 (by rfl) ⟨1941129, by rfl⟩ : syracuseStep 5176345 = 3882259) B3882259
theorem B6901793 : Blo 2043435 6901793 := bstep (se 2 (by rfl) ⟨2588172, by rfl⟩ : syracuseStep 6901793 = 5176345) B5176345
theorem B4601195 : Blo 2043435 4601195 := bstep (se 1 (by rfl) ⟨3450896, by rfl⟩ : syracuseStep 4601195 = 6901793) B6901793
theorem B3067463 : Blo 2043435 3067463 := bstep (se 1 (by rfl) ⟨2300597, by rfl⟩ : syracuseStep 3067463 = 4601195) B4601195
theorem B2044975 : Blo 2043435 2044975 := bstep (se 1 (by rfl) ⟨1533731, by rfl⟩ : syracuseStep 2044975 = 3067463) B3067463
theorem B3067469 : Blo 2043435 3067469 := bbase (se 3 (by rfl) ⟨575150, by rfl⟩ : syracuseStep 3067469 = 1150301) (by norm_num)
theorem B2044979 : Blo 2043435 2044979 := bstep (se 1 (by rfl) ⟨1533734, by rfl⟩ : syracuseStep 2044979 = 3067469) B3067469
theorem B4601213 : Blo 2043435 4601213 := bbase (se 3 (by rfl) ⟨862727, by rfl⟩ : syracuseStep 4601213 = 1725455) (by norm_num)
theorem B3067475 : Blo 2043435 3067475 := bstep (se 1 (by rfl) ⟨2300606, by rfl⟩ : syracuseStep 3067475 = 4601213) B4601213
theorem B2044983 : Blo 2043435 2044983 := bstep (se 1 (by rfl) ⟨1533737, by rfl⟩ : syracuseStep 2044983 = 3067475) B3067475
theorem B3450917 : Blo 2043435 3450917 := bbase (se 4 (by rfl) ⟨323523, by rfl⟩ : syracuseStep 3450917 = 647047) (by norm_num)
theorem B2300611 : Blo 2043435 2300611 := bstep (se 1 (by rfl) ⟨1725458, by rfl⟩ : syracuseStep 2300611 = 3450917) B3450917
theorem B3067481 : Blo 2043435 3067481 := bstep (se 2 (by rfl) ⟨1150305, by rfl⟩ : syracuseStep 3067481 = 2300611) B2300611
theorem B2044987 : Blo 2043435 2044987 := bstep (se 1 (by rfl) ⟨1533740, by rfl⟩ : syracuseStep 2044987 = 3067481) B3067481
theorem B2911717 : Blo 2043435 2911717 := bbase (se 4 (by rfl) ⟨272973, by rfl⟩ : syracuseStep 2911717 = 545947) (by norm_num)
theorem B15529157 : Blo 2043435 15529157 := bstep (se 4 (by rfl) ⟨1455858, by rfl⟩ : syracuseStep 15529157 = 2911717) B2911717
theorem B10352771 : Blo 2043435 10352771 := bstep (se 1 (by rfl) ⟨7764578, by rfl⟩ : syracuseStep 10352771 = 15529157) B15529157
theorem B6901847 : Blo 2043435 6901847 := bstep (se 1 (by rfl) ⟨5176385, by rfl⟩ : syracuseStep 6901847 = 10352771) B10352771
theorem B4601231 : Blo 2043435 4601231 := bstep (se 1 (by rfl) ⟨3450923, by rfl⟩ : syracuseStep 4601231 = 6901847) B6901847
theorem B3067487 : Blo 2043435 3067487 := bstep (se 1 (by rfl) ⟨2300615, by rfl⟩ : syracuseStep 3067487 = 4601231) B4601231
theorem B2044991 : Blo 2043435 2044991 := bstep (se 1 (by rfl) ⟨1533743, by rfl⟩ : syracuseStep 2044991 = 3067487) B3067487
theorem B3067493 : Blo 2043435 3067493 := bbase (se 4 (by rfl) ⟨287577, by rfl⟩ : syracuseStep 3067493 = 575155) (by norm_num)
theorem B2044995 : Blo 2043435 2044995 := bstep (se 1 (by rfl) ⟨1533746, by rfl⟩ : syracuseStep 2044995 = 3067493) B3067493
theorem B2183797 : Blo 2043435 2183797 := bbase (se 5 (by rfl) ⟨102365, by rfl⟩ : syracuseStep 2183797 = 204731) (by norm_num)
theorem B2911729 : Blo 2043435 2911729 := bstep (se 2 (by rfl) ⟨1091898, by rfl⟩ : syracuseStep 2911729 = 2183797) B2183797
theorem B3882305 : Blo 2043435 3882305 := bstep (se 2 (by rfl) ⟨1455864, by rfl⟩ : syracuseStep 3882305 = 2911729) B2911729
theorem B2588203 : Blo 2043435 2588203 := bstep (se 1 (by rfl) ⟨1941152, by rfl⟩ : syracuseStep 2588203 = 3882305) B3882305
theorem B3450937 : Blo 2043435 3450937 := bstep (se 2 (by rfl) ⟨1294101, by rfl⟩ : syracuseStep 3450937 = 2588203) B2588203
theorem B4601249 : Blo 2043435 4601249 := bstep (se 2 (by rfl) ⟨1725468, by rfl⟩ : syracuseStep 4601249 = 3450937) B3450937
theorem B3067499 : Blo 2043435 3067499 := bstep (se 1 (by rfl) ⟨2300624, by rfl⟩ : syracuseStep 3067499 = 4601249) B4601249
theorem B2044999 : Blo 2043435 2044999 := bstep (se 1 (by rfl) ⟨1533749, by rfl⟩ : syracuseStep 2044999 = 3067499) B3067499
theorem B2300629 : Blo 2043435 2300629 := bbase (se 7 (by rfl) ⟨26960, by rfl⟩ : syracuseStep 2300629 = 53921) (by norm_num)
theorem B3067505 : Blo 2043435 3067505 := bstep (se 2 (by rfl) ⟨1150314, by rfl⟩ : syracuseStep 3067505 = 2300629) B2300629
theorem B2045003 : Blo 2043435 2045003 := bstep (se 1 (by rfl) ⟨1533752, by rfl⟩ : syracuseStep 2045003 = 3067505) B3067505
theorem B2588213 : Blo 2043435 2588213 := bbase (se 5 (by rfl) ⟨121322, by rfl⟩ : syracuseStep 2588213 = 242645) (by norm_num)
theorem B6901901 : Blo 2043435 6901901 := bstep (se 3 (by rfl) ⟨1294106, by rfl⟩ : syracuseStep 6901901 = 2588213) B2588213
theorem B4601267 : Blo 2043435 4601267 := bstep (se 1 (by rfl) ⟨3450950, by rfl⟩ : syracuseStep 4601267 = 6901901) B6901901
theorem B3067511 : Blo 2043435 3067511 := bstep (se 1 (by rfl) ⟨2300633, by rfl⟩ : syracuseStep 3067511 = 4601267) B4601267
theorem B2045007 : Blo 2043435 2045007 := bstep (se 1 (by rfl) ⟨1533755, by rfl⟩ : syracuseStep 2045007 = 3067511) B3067511
theorem B3067517 : Blo 2043435 3067517 := bbase (se 3 (by rfl) ⟨575159, by rfl⟩ : syracuseStep 3067517 = 1150319) (by norm_num)
theorem B2045011 : Blo 2043435 2045011 := bstep (se 1 (by rfl) ⟨1533758, by rfl⟩ : syracuseStep 2045011 = 3067517) B3067517
theorem B4601285 : Blo 2043435 4601285 := bbase (se 4 (by rfl) ⟨431370, by rfl⟩ : syracuseStep 4601285 = 862741) (by norm_num)
theorem B3067523 : Blo 2043435 3067523 := bstep (se 1 (by rfl) ⟨2300642, by rfl⟩ : syracuseStep 3067523 = 4601285) B4601285
theorem B2045015 : Blo 2043435 2045015 := bstep (se 1 (by rfl) ⟨1533761, by rfl⟩ : syracuseStep 2045015 = 3067523) B3067523
theorem B11206421 : Blo 2043435 11206421 := bbase (se 6 (by rfl) ⟨262650, by rfl⟩ : syracuseStep 11206421 = 525301) (by norm_num)
theorem B7470947 : Blo 2043435 7470947 := bstep (se 1 (by rfl) ⟨5603210, by rfl⟩ : syracuseStep 7470947 = 11206421) B11206421
theorem B4980631 : Blo 2043435 4980631 := bstep (se 1 (by rfl) ⟨3735473, by rfl⟩ : syracuseStep 4980631 = 7470947) B7470947
theorem B6640841 : Blo 2043435 6640841 := bstep (se 2 (by rfl) ⟨2490315, by rfl⟩ : syracuseStep 6640841 = 4980631) B4980631
theorem B4427227 : Blo 2043435 4427227 := bstep (se 1 (by rfl) ⟨3320420, by rfl⟩ : syracuseStep 4427227 = 6640841) B6640841
theorem B5902969 : Blo 2043435 5902969 := bstep (se 2 (by rfl) ⟨2213613, by rfl⟩ : syracuseStep 5902969 = 4427227) B4427227
theorem B7870625 : Blo 2043435 7870625 := bstep (se 2 (by rfl) ⟨2951484, by rfl⟩ : syracuseStep 7870625 = 5902969) B5902969
theorem B5247083 : Blo 2043435 5247083 := bstep (se 1 (by rfl) ⟨3935312, by rfl⟩ : syracuseStep 5247083 = 7870625) B7870625
theorem B13992221 : Blo 2043435 13992221 := bstep (se 3 (by rfl) ⟨2623541, by rfl⟩ : syracuseStep 13992221 = 5247083) B5247083
theorem B37312589 : Blo 2043435 37312589 := bstep (se 3 (by rfl) ⟨6996110, by rfl⟩ : syracuseStep 37312589 = 13992221) B13992221
theorem B24875059 : Blo 2043435 24875059 := bstep (se 1 (by rfl) ⟨18656294, by rfl⟩ : syracuseStep 24875059 = 37312589) B37312589
theorem B33166745 : Blo 2043435 33166745 := bstep (se 2 (by rfl) ⟨12437529, by rfl⟩ : syracuseStep 33166745 = 24875059) B24875059
theorem B22111163 : Blo 2043435 22111163 := bstep (se 1 (by rfl) ⟨16583372, by rfl⟩ : syracuseStep 22111163 = 33166745) B33166745
theorem B14740775 : Blo 2043435 14740775 := bstep (se 1 (by rfl) ⟨11055581, by rfl⟩ : syracuseStep 14740775 = 22111163) B22111163
theorem B9827183 : Blo 2043435 9827183 := bstep (se 1 (by rfl) ⟨7370387, by rfl⟩ : syracuseStep 9827183 = 14740775) B14740775
theorem B6551455 : Blo 2043435 6551455 := bstep (se 1 (by rfl) ⟨4913591, by rfl⟩ : syracuseStep 6551455 = 9827183) B9827183
theorem B8735273 : Blo 2043435 8735273 := bstep (se 2 (by rfl) ⟨3275727, by rfl⟩ : syracuseStep 8735273 = 6551455) B6551455
theorem B5823515 : Blo 2043435 5823515 := bstep (se 1 (by rfl) ⟨4367636, by rfl⟩ : syracuseStep 5823515 = 8735273) B8735273
theorem B3882343 : Blo 2043435 3882343 := bstep (se 1 (by rfl) ⟨2911757, by rfl⟩ : syracuseStep 3882343 = 5823515) B5823515
theorem B5176457 : Blo 2043435 5176457 := bstep (se 2 (by rfl) ⟨1941171, by rfl⟩ : syracuseStep 5176457 = 3882343) B3882343
theorem B3450971 : Blo 2043435 3450971 := bstep (se 1 (by rfl) ⟨2588228, by rfl⟩ : syracuseStep 3450971 = 5176457) B5176457
theorem B2300647 : Blo 2043435 2300647 := bstep (se 1 (by rfl) ⟨1725485, by rfl⟩ : syracuseStep 2300647 = 3450971) B3450971
theorem B3067529 : Blo 2043435 3067529 := bstep (se 2 (by rfl) ⟨1150323, by rfl⟩ : syracuseStep 3067529 = 2300647) B2300647
theorem B2045019 : Blo 2043435 2045019 := bstep (se 1 (by rfl) ⟨1533764, by rfl⟩ : syracuseStep 2045019 = 3067529) B3067529
theorem B10352933 : Blo 2043435 10352933 := bbase (se 4 (by rfl) ⟨970587, by rfl⟩ : syracuseStep 10352933 = 1941175) (by norm_num)
theorem B6901955 : Blo 2043435 6901955 := bstep (se 1 (by rfl) ⟨5176466, by rfl⟩ : syracuseStep 6901955 = 10352933) B10352933
theorem B4601303 : Blo 2043435 4601303 := bstep (se 1 (by rfl) ⟨3450977, by rfl⟩ : syracuseStep 4601303 = 6901955) B6901955
theorem B3067535 : Blo 2043435 3067535 := bstep (se 1 (by rfl) ⟨2300651, by rfl⟩ : syracuseStep 3067535 = 4601303) B4601303
theorem B2045023 : Blo 2043435 2045023 := bstep (se 1 (by rfl) ⟨1533767, by rfl⟩ : syracuseStep 2045023 = 3067535) B3067535
theorem B3067541 : Blo 2043435 3067541 := bbase (se 6 (by rfl) ⟨71895, by rfl⟩ : syracuseStep 3067541 = 143791) (by norm_num)
theorem B2045027 : Blo 2043435 2045027 := bstep (se 1 (by rfl) ⟨1533770, by rfl⟩ : syracuseStep 2045027 = 3067541) B3067541
theorem B10659653 : Blo 2043435 10659653 := bbase (se 4 (by rfl) ⟨999342, by rfl⟩ : syracuseStep 10659653 = 1998685) (by norm_num)
theorem B7106435 : Blo 2043435 7106435 := bstep (se 1 (by rfl) ⟨5329826, by rfl⟩ : syracuseStep 7106435 = 10659653) B10659653
theorem B4737623 : Blo 2043435 4737623 := bstep (se 1 (by rfl) ⟨3553217, by rfl⟩ : syracuseStep 4737623 = 7106435) B7106435
theorem B12633661 : Blo 2043435 12633661 := bstep (se 3 (by rfl) ⟨2368811, by rfl⟩ : syracuseStep 12633661 = 4737623) B4737623
theorem B67379525 : Blo 2043435 67379525 := bstep (se 4 (by rfl) ⟨6316830, by rfl⟩ : syracuseStep 67379525 = 12633661) B12633661
theorem B44919683 : Blo 2043435 44919683 := bstep (se 1 (by rfl) ⟨33689762, by rfl⟩ : syracuseStep 44919683 = 67379525) B67379525
theorem B29946455 : Blo 2043435 29946455 := bstep (se 1 (by rfl) ⟨22459841, by rfl⟩ : syracuseStep 29946455 = 44919683) B44919683
theorem B19964303 : Blo 2043435 19964303 := bstep (se 1 (by rfl) ⟨14973227, by rfl⟩ : syracuseStep 19964303 = 29946455) B29946455
theorem B13309535 : Blo 2043435 13309535 := bstep (se 1 (by rfl) ⟨9982151, by rfl⟩ : syracuseStep 13309535 = 19964303) B19964303
theorem B8873023 : Blo 2043435 8873023 := bstep (se 1 (by rfl) ⟨6654767, by rfl⟩ : syracuseStep 8873023 = 13309535) B13309535
theorem B11830697 : Blo 2043435 11830697 := bstep (se 2 (by rfl) ⟨4436511, by rfl⟩ : syracuseStep 11830697 = 8873023) B8873023
theorem B7887131 : Blo 2043435 7887131 := bstep (se 1 (by rfl) ⟨5915348, by rfl⟩ : syracuseStep 7887131 = 11830697) B11830697
theorem B5258087 : Blo 2043435 5258087 := bstep (se 1 (by rfl) ⟨3943565, by rfl⟩ : syracuseStep 5258087 = 7887131) B7887131
theorem B3505391 : Blo 2043435 3505391 := bstep (se 1 (by rfl) ⟨2629043, by rfl⟩ : syracuseStep 3505391 = 5258087) B5258087
theorem B2336927 : Blo 2043435 2336927 := bstep (se 1 (by rfl) ⟨1752695, by rfl⟩ : syracuseStep 2336927 = 3505391) B3505391
theorem B24927221 : Blo 2043435 24927221 := bstep (se 5 (by rfl) ⟨1168463, by rfl⟩ : syracuseStep 24927221 = 2336927) B2336927
theorem B66472589 : Blo 2043435 66472589 := bstep (se 3 (by rfl) ⟨12463610, by rfl⟩ : syracuseStep 66472589 = 24927221) B24927221
theorem B44315059 : Blo 2043435 44315059 := bstep (se 1 (by rfl) ⟨33236294, by rfl⟩ : syracuseStep 44315059 = 66472589) B66472589
theorem B59086745 : Blo 2043435 59086745 := bstep (se 2 (by rfl) ⟨22157529, by rfl⟩ : syracuseStep 59086745 = 44315059) B44315059
theorem B39391163 : Blo 2043435 39391163 := bstep (se 1 (by rfl) ⟨29543372, by rfl⟩ : syracuseStep 39391163 = 59086745) B59086745
theorem B26260775 : Blo 2043435 26260775 := bstep (se 1 (by rfl) ⟨19695581, by rfl⟩ : syracuseStep 26260775 = 39391163) B39391163
theorem B17507183 : Blo 2043435 17507183 := bstep (se 1 (by rfl) ⟨13130387, by rfl⟩ : syracuseStep 17507183 = 26260775) B26260775
theorem B46685821 : Blo 2043435 46685821 := bstep (se 3 (by rfl) ⟨8753591, by rfl⟩ : syracuseStep 46685821 = 17507183) B17507183
theorem B62247761 : Blo 2043435 62247761 := bstep (se 2 (by rfl) ⟨23342910, by rfl⟩ : syracuseStep 62247761 = 46685821) B46685821
theorem B41498507 : Blo 2043435 41498507 := bstep (se 1 (by rfl) ⟨31123880, by rfl⟩ : syracuseStep 41498507 = 62247761) B62247761
theorem B27665671 : Blo 2043435 27665671 := bstep (se 1 (by rfl) ⟨20749253, by rfl⟩ : syracuseStep 27665671 = 41498507) B41498507
theorem B36887561 : Blo 2043435 36887561 := bstep (se 2 (by rfl) ⟨13832835, by rfl⟩ : syracuseStep 36887561 = 27665671) B27665671
theorem B24591707 : Blo 2043435 24591707 := bstep (se 1 (by rfl) ⟨18443780, by rfl⟩ : syracuseStep 24591707 = 36887561) B36887561
theorem B16394471 : Blo 2043435 16394471 := bstep (se 1 (by rfl) ⟨12295853, by rfl⟩ : syracuseStep 16394471 = 24591707) B24591707
theorem B10929647 : Blo 2043435 10929647 := bstep (se 1 (by rfl) ⟨8197235, by rfl⟩ : syracuseStep 10929647 = 16394471) B16394471
theorem B7286431 : Blo 2043435 7286431 := bstep (se 1 (by rfl) ⟨5464823, by rfl⟩ : syracuseStep 7286431 = 10929647) B10929647
theorem B9715241 : Blo 2043435 9715241 := bstep (se 2 (by rfl) ⟨3643215, by rfl⟩ : syracuseStep 9715241 = 7286431) B7286431
theorem B25907309 : Blo 2043435 25907309 := bstep (se 3 (by rfl) ⟨4857620, by rfl⟩ : syracuseStep 25907309 = 9715241) B9715241
theorem B17271539 : Blo 2043435 17271539 := bstep (se 1 (by rfl) ⟨12953654, by rfl⟩ : syracuseStep 17271539 = 25907309) B25907309
theorem B11514359 : Blo 2043435 11514359 := bstep (se 1 (by rfl) ⟨8635769, by rfl⟩ : syracuseStep 11514359 = 17271539) B17271539
theorem B30704957 : Blo 2043435 30704957 := bstep (se 3 (by rfl) ⟨5757179, by rfl⟩ : syracuseStep 30704957 = 11514359) B11514359
theorem B20469971 : Blo 2043435 20469971 := bstep (se 1 (by rfl) ⟨15352478, by rfl⟩ : syracuseStep 20469971 = 30704957) B30704957
theorem B13646647 : Blo 2043435 13646647 := bstep (se 1 (by rfl) ⟨10234985, by rfl⟩ : syracuseStep 13646647 = 20469971) B20469971
theorem B18195529 : Blo 2043435 18195529 := bstep (se 2 (by rfl) ⟨6823323, by rfl⟩ : syracuseStep 18195529 = 13646647) B13646647
theorem B24260705 : Blo 2043435 24260705 := bstep (se 2 (by rfl) ⟨9097764, by rfl⟩ : syracuseStep 24260705 = 18195529) B18195529
theorem B16173803 : Blo 2043435 16173803 := bstep (se 1 (by rfl) ⟨12130352, by rfl⟩ : syracuseStep 16173803 = 24260705) B24260705
theorem B10782535 : Blo 2043435 10782535 := bstep (se 1 (by rfl) ⟨8086901, by rfl⟩ : syracuseStep 10782535 = 16173803) B16173803
theorem B230027413 : Blo 2043435 230027413 := bstep (se 6 (by rfl) ⟨5391267, by rfl⟩ : syracuseStep 230027413 = 10782535) B10782535
theorem B306703217 : Blo 2043435 306703217 := bstep (se 2 (by rfl) ⟨115013706, by rfl⟩ : syracuseStep 306703217 = 230027413) B230027413
theorem B817875245 : Blo 2043435 817875245 := bstep (se 3 (by rfl) ⟨153351608, by rfl⟩ : syracuseStep 817875245 = 306703217) B306703217
theorem B545250163 : Blo 2043435 545250163 := bstep (se 1 (by rfl) ⟨408937622, by rfl⟩ : syracuseStep 545250163 = 817875245) B817875245
theorem B727000217 : Blo 2043435 727000217 := bstep (se 2 (by rfl) ⟨272625081, by rfl⟩ : syracuseStep 727000217 = 545250163) B545250163
theorem B484666811 : Blo 2043435 484666811 := bstep (se 1 (by rfl) ⟨363500108, by rfl⟩ : syracuseStep 484666811 = 727000217) B727000217
theorem B323111207 : Blo 2043435 323111207 := bstep (se 1 (by rfl) ⟨242333405, by rfl⟩ : syracuseStep 323111207 = 484666811) B484666811
theorem B215407471 : Blo 2043435 215407471 := bstep (se 1 (by rfl) ⟨161555603, by rfl⟩ : syracuseStep 215407471 = 323111207) B323111207
theorem B287209961 : Blo 2043435 287209961 := bstep (se 2 (by rfl) ⟨107703735, by rfl⟩ : syracuseStep 287209961 = 215407471) B215407471
theorem B191473307 : Blo 2043435 191473307 := bstep (se 1 (by rfl) ⟨143604980, by rfl⟩ : syracuseStep 191473307 = 287209961) B287209961
theorem B127648871 : Blo 2043435 127648871 := bstep (se 1 (by rfl) ⟨95736653, by rfl⟩ : syracuseStep 127648871 = 191473307) B191473307
theorem B85099247 : Blo 2043435 85099247 := bstep (se 1 (by rfl) ⟨63824435, by rfl⟩ : syracuseStep 85099247 = 127648871) B127648871
theorem B56732831 : Blo 2043435 56732831 := bstep (se 1 (by rfl) ⟨42549623, by rfl⟩ : syracuseStep 56732831 = 85099247) B85099247
theorem B37821887 : Blo 2043435 37821887 := bstep (se 1 (by rfl) ⟨28366415, by rfl⟩ : syracuseStep 37821887 = 56732831) B56732831
theorem B25214591 : Blo 2043435 25214591 := bstep (se 1 (by rfl) ⟨18910943, by rfl⟩ : syracuseStep 25214591 = 37821887) B37821887
theorem B16809727 : Blo 2043435 16809727 := bstep (se 1 (by rfl) ⟨12607295, by rfl⟩ : syracuseStep 16809727 = 25214591) B25214591
theorem B22412969 : Blo 2043435 22412969 := bstep (se 2 (by rfl) ⟨8404863, by rfl⟩ : syracuseStep 22412969 = 16809727) B16809727
theorem B14941979 : Blo 2043435 14941979 := bstep (se 1 (by rfl) ⟨11206484, by rfl⟩ : syracuseStep 14941979 = 22412969) B22412969
theorem B9961319 : Blo 2043435 9961319 := bstep (se 1 (by rfl) ⟨7470989, by rfl⟩ : syracuseStep 9961319 = 14941979) B14941979
theorem B6640879 : Blo 2043435 6640879 := bstep (se 1 (by rfl) ⟨4980659, by rfl⟩ : syracuseStep 6640879 = 9961319) B9961319
theorem B8854505 : Blo 2043435 8854505 := bstep (se 2 (by rfl) ⟨3320439, by rfl⟩ : syracuseStep 8854505 = 6640879) B6640879
theorem B5903003 : Blo 2043435 5903003 := bstep (se 1 (by rfl) ⟨4427252, by rfl⟩ : syracuseStep 5903003 = 8854505) B8854505
theorem B3935335 : Blo 2043435 3935335 := bstep (se 1 (by rfl) ⟨2951501, by rfl⟩ : syracuseStep 3935335 = 5903003) B5903003
theorem B5247113 : Blo 2043435 5247113 := bstep (se 2 (by rfl) ⟨1967667, by rfl⟩ : syracuseStep 5247113 = 3935335) B3935335
theorem B13992301 : Blo 2043435 13992301 := bstep (se 3 (by rfl) ⟨2623556, by rfl⟩ : syracuseStep 13992301 = 5247113) B5247113
theorem B18656401 : Blo 2043435 18656401 := bstep (se 2 (by rfl) ⟨6996150, by rfl⟩ : syracuseStep 18656401 = 13992301) B13992301
theorem B24875201 : Blo 2043435 24875201 := bstep (se 2 (by rfl) ⟨9328200, by rfl⟩ : syracuseStep 24875201 = 18656401) B18656401
theorem B16583467 : Blo 2043435 16583467 := bstep (se 1 (by rfl) ⟨12437600, by rfl⟩ : syracuseStep 16583467 = 24875201) B24875201
theorem B22111289 : Blo 2043435 22111289 := bstep (se 2 (by rfl) ⟨8291733, by rfl⟩ : syracuseStep 22111289 = 16583467) B16583467
theorem B14740859 : Blo 2043435 14740859 := bstep (se 1 (by rfl) ⟨11055644, by rfl⟩ : syracuseStep 14740859 = 22111289) B22111289
theorem B9827239 : Blo 2043435 9827239 := bstep (se 1 (by rfl) ⟨7370429, by rfl⟩ : syracuseStep 9827239 = 14740859) B14740859
theorem B13102985 : Blo 2043435 13102985 := bstep (se 2 (by rfl) ⟨4913619, by rfl⟩ : syracuseStep 13102985 = 9827239) B9827239
theorem B8735323 : Blo 2043435 8735323 := bstep (se 1 (by rfl) ⟨6551492, by rfl⟩ : syracuseStep 8735323 = 13102985) B13102985
theorem B11647097 : Blo 2043435 11647097 := bstep (se 2 (by rfl) ⟨4367661, by rfl⟩ : syracuseStep 11647097 = 8735323) B8735323
theorem B7764731 : Blo 2043435 7764731 := bstep (se 1 (by rfl) ⟨5823548, by rfl⟩ : syracuseStep 7764731 = 11647097) B11647097
theorem B5176487 : Blo 2043435 5176487 := bstep (se 1 (by rfl) ⟨3882365, by rfl⟩ : syracuseStep 5176487 = 7764731) B7764731
theorem B3450991 : Blo 2043435 3450991 := bstep (se 1 (by rfl) ⟨2588243, by rfl⟩ : syracuseStep 3450991 = 5176487) B5176487
theorem B4601321 : Blo 2043435 4601321 := bstep (se 2 (by rfl) ⟨1725495, by rfl⟩ : syracuseStep 4601321 = 3450991) B3450991
theorem B3067547 : Blo 2043435 3067547 := bstep (se 1 (by rfl) ⟨2300660, by rfl⟩ : syracuseStep 3067547 = 4601321) B4601321
theorem B2045031 : Blo 2043435 2045031 := bstep (se 1 (by rfl) ⟨1533773, by rfl⟩ : syracuseStep 2045031 = 3067547) B3067547
theorem B2300665 : Blo 2043435 2300665 := bbase (se 2 (by rfl) ⟨862749, by rfl⟩ : syracuseStep 2300665 = 1725499) (by norm_num)
theorem B3067553 : Blo 2043435 3067553 := bstep (se 2 (by rfl) ⟨1150332, by rfl⟩ : syracuseStep 3067553 = 2300665) B2300665
theorem B2045035 : Blo 2043435 2045035 := bstep (se 1 (by rfl) ⟨1533776, by rfl⟩ : syracuseStep 2045035 = 3067553) B3067553
theorem B3320453 : Blo 2043435 3320453 := bbase (se 4 (by rfl) ⟨311292, by rfl⟩ : syracuseStep 3320453 = 622585) (by norm_num)
theorem B8854541 : Blo 2043435 8854541 := bstep (se 3 (by rfl) ⟨1660226, by rfl⟩ : syracuseStep 8854541 = 3320453) B3320453
theorem B5903027 : Blo 2043435 5903027 := bstep (se 1 (by rfl) ⟨4427270, by rfl⟩ : syracuseStep 5903027 = 8854541) B8854541
theorem B3935351 : Blo 2043435 3935351 := bstep (se 1 (by rfl) ⟨2951513, by rfl⟩ : syracuseStep 3935351 = 5903027) B5903027
theorem B10494269 : Blo 2043435 10494269 := bstep (se 3 (by rfl) ⟨1967675, by rfl⟩ : syracuseStep 10494269 = 3935351) B3935351
theorem B6996179 : Blo 2043435 6996179 := bstep (se 1 (by rfl) ⟨5247134, by rfl⟩ : syracuseStep 6996179 = 10494269) B10494269
theorem B18656477 : Blo 2043435 18656477 := bstep (se 3 (by rfl) ⟨3498089, by rfl⟩ : syracuseStep 18656477 = 6996179) B6996179
theorem B12437651 : Blo 2043435 12437651 := bstep (se 1 (by rfl) ⟨9328238, by rfl⟩ : syracuseStep 12437651 = 18656477) B18656477
theorem B8291767 : Blo 2043435 8291767 := bstep (se 1 (by rfl) ⟨6218825, by rfl⟩ : syracuseStep 8291767 = 12437651) B12437651
theorem B11055689 : Blo 2043435 11055689 := bstep (se 2 (by rfl) ⟨4145883, by rfl⟩ : syracuseStep 11055689 = 8291767) B8291767
theorem B7370459 : Blo 2043435 7370459 := bstep (se 1 (by rfl) ⟨5527844, by rfl⟩ : syracuseStep 7370459 = 11055689) B11055689
theorem B4913639 : Blo 2043435 4913639 := bstep (se 1 (by rfl) ⟨3685229, by rfl⟩ : syracuseStep 4913639 = 7370459) B7370459
theorem B3275759 : Blo 2043435 3275759 := bstep (se 1 (by rfl) ⟨2456819, by rfl⟩ : syracuseStep 3275759 = 4913639) B4913639
theorem B8735357 : Blo 2043435 8735357 := bstep (se 3 (by rfl) ⟨1637879, by rfl⟩ : syracuseStep 8735357 = 3275759) B3275759
theorem B5823571 : Blo 2043435 5823571 := bstep (se 1 (by rfl) ⟨4367678, by rfl⟩ : syracuseStep 5823571 = 8735357) B8735357
theorem B7764761 : Blo 2043435 7764761 := bstep (se 2 (by rfl) ⟨2911785, by rfl⟩ : syracuseStep 7764761 = 5823571) B5823571
theorem B5176507 : Blo 2043435 5176507 := bstep (se 1 (by rfl) ⟨3882380, by rfl⟩ : syracuseStep 5176507 = 7764761) B7764761
theorem B6902009 : Blo 2043435 6902009 := bstep (se 2 (by rfl) ⟨2588253, by rfl⟩ : syracuseStep 6902009 = 5176507) B5176507
theorem B4601339 : Blo 2043435 4601339 := bstep (se 1 (by rfl) ⟨3451004, by rfl⟩ : syracuseStep 4601339 = 6902009) B6902009
theorem B3067559 : Blo 2043435 3067559 := bstep (se 1 (by rfl) ⟨2300669, by rfl⟩ : syracuseStep 3067559 = 4601339) B4601339
theorem B2045039 : Blo 2043435 2045039 := bstep (se 1 (by rfl) ⟨1533779, by rfl⟩ : syracuseStep 2045039 = 3067559) B3067559
theorem B3067565 : Blo 2043435 3067565 := bbase (se 3 (by rfl) ⟨575168, by rfl⟩ : syracuseStep 3067565 = 1150337) (by norm_num)
theorem B2045043 : Blo 2043435 2045043 := bstep (se 1 (by rfl) ⟨1533782, by rfl⟩ : syracuseStep 2045043 = 3067565) B3067565
theorem B4601357 : Blo 2043435 4601357 := bbase (se 3 (by rfl) ⟨862754, by rfl⟩ : syracuseStep 4601357 = 1725509) (by norm_num)
theorem B3067571 : Blo 2043435 3067571 := bstep (se 1 (by rfl) ⟨2300678, by rfl⟩ : syracuseStep 3067571 = 4601357) B4601357
theorem B2045047 : Blo 2043435 2045047 := bstep (se 1 (by rfl) ⟨1533785, by rfl⟩ : syracuseStep 2045047 = 3067571) B3067571
theorem B2588269 : Blo 2043435 2588269 := bbase (se 3 (by rfl) ⟨485300, by rfl⟩ : syracuseStep 2588269 = 970601) (by norm_num)
theorem B3451025 : Blo 2043435 3451025 := bstep (se 2 (by rfl) ⟨1294134, by rfl⟩ : syracuseStep 3451025 = 2588269) B2588269
theorem B2300683 : Blo 2043435 2300683 := bstep (se 1 (by rfl) ⟨1725512, by rfl⟩ : syracuseStep 2300683 = 3451025) B3451025
theorem B3067577 : Blo 2043435 3067577 := bstep (se 2 (by rfl) ⟨1150341, by rfl⟩ : syracuseStep 3067577 = 2300683) B2300683
theorem B2045051 : Blo 2043435 2045051 := bstep (se 1 (by rfl) ⟨1533788, by rfl⟩ : syracuseStep 2045051 = 3067577) B3067577
theorem B2101241 : Blo 2043435 2101241 := bbase (se 2 (by rfl) ⟨787965, by rfl⟩ : syracuseStep 2101241 = 1575931) (by norm_num)
theorem B5603309 : Blo 2043435 5603309 := bstep (se 3 (by rfl) ⟨1050620, by rfl⟩ : syracuseStep 5603309 = 2101241) B2101241
theorem B3735539 : Blo 2043435 3735539 := bstep (se 1 (by rfl) ⟨2801654, by rfl⟩ : syracuseStep 3735539 = 5603309) B5603309
theorem B2490359 : Blo 2043435 2490359 := bstep (se 1 (by rfl) ⟨1867769, by rfl⟩ : syracuseStep 2490359 = 3735539) B3735539
theorem B6640957 : Blo 2043435 6640957 := bstep (se 3 (by rfl) ⟨1245179, by rfl⟩ : syracuseStep 6640957 = 2490359) B2490359
theorem B8854609 : Blo 2043435 8854609 := bstep (se 2 (by rfl) ⟨3320478, by rfl⟩ : syracuseStep 8854609 = 6640957) B6640957
theorem B11806145 : Blo 2043435 11806145 := bstep (se 2 (by rfl) ⟨4427304, by rfl⟩ : syracuseStep 11806145 = 8854609) B8854609
theorem B7870763 : Blo 2043435 7870763 := bstep (se 1 (by rfl) ⟨5903072, by rfl⟩ : syracuseStep 7870763 = 11806145) B11806145
theorem B5247175 : Blo 2043435 5247175 := bstep (se 1 (by rfl) ⟨3935381, by rfl⟩ : syracuseStep 5247175 = 7870763) B7870763
theorem B6996233 : Blo 2043435 6996233 := bstep (se 2 (by rfl) ⟨2623587, by rfl⟩ : syracuseStep 6996233 = 5247175) B5247175
theorem B4664155 : Blo 2043435 4664155 := bstep (se 1 (by rfl) ⟨3498116, by rfl⟩ : syracuseStep 4664155 = 6996233) B6996233
theorem B6218873 : Blo 2043435 6218873 := bstep (se 2 (by rfl) ⟨2332077, by rfl⟩ : syracuseStep 6218873 = 4664155) B4664155
theorem B4145915 : Blo 2043435 4145915 := bstep (se 1 (by rfl) ⟨3109436, by rfl⟩ : syracuseStep 4145915 = 6218873) B6218873
theorem B11055773 : Blo 2043435 11055773 := bstep (se 3 (by rfl) ⟨2072957, by rfl⟩ : syracuseStep 11055773 = 4145915) B4145915
theorem B7370515 : Blo 2043435 7370515 := bstep (se 1 (by rfl) ⟨5527886, by rfl⟩ : syracuseStep 7370515 = 11055773) B11055773
theorem B9827353 : Blo 2043435 9827353 := bstep (se 2 (by rfl) ⟨3685257, by rfl⟩ : syracuseStep 9827353 = 7370515) B7370515
theorem B13103137 : Blo 2043435 13103137 := bstep (se 2 (by rfl) ⟨4913676, by rfl⟩ : syracuseStep 13103137 = 9827353) B9827353
theorem B17470849 : Blo 2043435 17470849 := bstep (se 2 (by rfl) ⟨6551568, by rfl⟩ : syracuseStep 17470849 = 13103137) B13103137
theorem B23294465 : Blo 2043435 23294465 := bstep (se 2 (by rfl) ⟨8735424, by rfl⟩ : syracuseStep 23294465 = 17470849) B17470849
theorem B15529643 : Blo 2043435 15529643 := bstep (se 1 (by rfl) ⟨11647232, by rfl⟩ : syracuseStep 15529643 = 23294465) B23294465
theorem B10353095 : Blo 2043435 10353095 := bstep (se 1 (by rfl) ⟨7764821, by rfl⟩ : syracuseStep 10353095 = 15529643) B15529643
theorem B6902063 : Blo 2043435 6902063 := bstep (se 1 (by rfl) ⟨5176547, by rfl⟩ : syracuseStep 6902063 = 10353095) B10353095
theorem B4601375 : Blo 2043435 4601375 := bstep (se 1 (by rfl) ⟨3451031, by rfl⟩ : syracuseStep 4601375 = 6902063) B6902063
theorem B3067583 : Blo 2043435 3067583 := bstep (se 1 (by rfl) ⟨2300687, by rfl⟩ : syracuseStep 3067583 = 4601375) B4601375
theorem B2045055 : Blo 2043435 2045055 := bstep (se 1 (by rfl) ⟨1533791, by rfl⟩ : syracuseStep 2045055 = 3067583) B3067583
theorem B3067589 : Blo 2043435 3067589 := bbase (se 4 (by rfl) ⟨287586, by rfl⟩ : syracuseStep 3067589 = 575173) (by norm_num)
theorem B2045059 : Blo 2043435 2045059 := bstep (se 1 (by rfl) ⟨1533794, by rfl⟩ : syracuseStep 2045059 = 3067589) B3067589
theorem B3451045 : Blo 2043435 3451045 := bbase (se 4 (by rfl) ⟨323535, by rfl⟩ : syracuseStep 3451045 = 647071) (by norm_num)
theorem B4601393 : Blo 2043435 4601393 := bstep (se 2 (by rfl) ⟨1725522, by rfl⟩ : syracuseStep 4601393 = 3451045) B3451045
theorem B3067595 : Blo 2043435 3067595 := bstep (se 1 (by rfl) ⟨2300696, by rfl⟩ : syracuseStep 3067595 = 4601393) B4601393
theorem B2045063 : Blo 2043435 2045063 := bstep (se 1 (by rfl) ⟨1533797, by rfl⟩ : syracuseStep 2045063 = 3067595) B3067595
theorem B2300701 : Blo 2043435 2300701 := bbase (se 3 (by rfl) ⟨431381, by rfl⟩ : syracuseStep 2300701 = 862763) (by norm_num)
theorem B3067601 : Blo 2043435 3067601 := bstep (se 2 (by rfl) ⟨1150350, by rfl⟩ : syracuseStep 3067601 = 2300701) B2300701
theorem B2045067 : Blo 2043435 2045067 := bstep (se 1 (by rfl) ⟨1533800, by rfl⟩ : syracuseStep 2045067 = 3067601) B3067601
theorem B6902117 : Blo 2043435 6902117 := bbase (se 4 (by rfl) ⟨647073, by rfl⟩ : syracuseStep 6902117 = 1294147) (by norm_num)
theorem B4601411 : Blo 2043435 4601411 := bstep (se 1 (by rfl) ⟨3451058, by rfl⟩ : syracuseStep 4601411 = 6902117) B6902117
theorem B3067607 : Blo 2043435 3067607 := bstep (se 1 (by rfl) ⟨2300705, by rfl⟩ : syracuseStep 3067607 = 4601411) B4601411
theorem B2045071 : Blo 2043435 2045071 := bstep (se 1 (by rfl) ⟨1533803, by rfl⟩ : syracuseStep 2045071 = 3067607) B3067607
theorem B3067613 : Blo 2043435 3067613 := bbase (se 3 (by rfl) ⟨575177, by rfl⟩ : syracuseStep 3067613 = 1150355) (by norm_num)
theorem B2045075 : Blo 2043435 2045075 := bstep (se 1 (by rfl) ⟨1533806, by rfl⟩ : syracuseStep 2045075 = 3067613) B3067613
theorem B4601429 : Blo 2043435 4601429 := bbase (se 8 (by rfl) ⟨26961, by rfl⟩ : syracuseStep 4601429 = 53923) (by norm_num)
theorem B3067619 : Blo 2043435 3067619 := bstep (se 1 (by rfl) ⟨2300714, by rfl⟩ : syracuseStep 3067619 = 4601429) B4601429
theorem B2045079 : Blo 2043435 2045079 := bstep (se 1 (by rfl) ⟨1533809, by rfl⟩ : syracuseStep 2045079 = 3067619) B3067619
theorem B4367773 : Blo 2043435 4367773 := bbase (se 3 (by rfl) ⟨818957, by rfl⟩ : syracuseStep 4367773 = 1637915) (by norm_num)
theorem B5823697 : Blo 2043435 5823697 := bstep (se 2 (by rfl) ⟨2183886, by rfl⟩ : syracuseStep 5823697 = 4367773) B4367773
theorem B7764929 : Blo 2043435 7764929 := bstep (se 2 (by rfl) ⟨2911848, by rfl⟩ : syracuseStep 7764929 = 5823697) B5823697
theorem B5176619 : Blo 2043435 5176619 := bstep (se 1 (by rfl) ⟨3882464, by rfl⟩ : syracuseStep 5176619 = 7764929) B7764929
theorem B3451079 : Blo 2043435 3451079 := bstep (se 1 (by rfl) ⟨2588309, by rfl⟩ : syracuseStep 3451079 = 5176619) B5176619
theorem B2300719 : Blo 2043435 2300719 := bstep (se 1 (by rfl) ⟨1725539, by rfl⟩ : syracuseStep 2300719 = 3451079) B3451079
theorem B3067625 : Blo 2043435 3067625 := bstep (se 2 (by rfl) ⟨1150359, by rfl⟩ : syracuseStep 3067625 = 2300719) B2300719
theorem B2045083 : Blo 2043435 2045083 := bstep (se 1 (by rfl) ⟨1533812, by rfl⟩ : syracuseStep 2045083 = 3067625) B3067625
theorem B5527973 : Blo 2043435 5527973 := bbase (se 4 (by rfl) ⟨518247, by rfl⟩ : syracuseStep 5527973 = 1036495) (by norm_num)
theorem B14741261 : Blo 2043435 14741261 := bstep (se 3 (by rfl) ⟨2763986, by rfl⟩ : syracuseStep 14741261 = 5527973) B5527973
theorem B9827507 : Blo 2043435 9827507 := bstep (se 1 (by rfl) ⟨7370630, by rfl⟩ : syracuseStep 9827507 = 14741261) B14741261
theorem B26206685 : Blo 2043435 26206685 := bstep (se 3 (by rfl) ⟨4913753, by rfl⟩ : syracuseStep 26206685 = 9827507) B9827507
theorem B17471123 : Blo 2043435 17471123 := bstep (se 1 (by rfl) ⟨13103342, by rfl⟩ : syracuseStep 17471123 = 26206685) B26206685
theorem B11647415 : Blo 2043435 11647415 := bstep (se 1 (by rfl) ⟨8735561, by rfl⟩ : syracuseStep 11647415 = 17471123) B17471123
theorem B7764943 : Blo 2043435 7764943 := bstep (se 1 (by rfl) ⟨5823707, by rfl⟩ : syracuseStep 7764943 = 11647415) B11647415
theorem B10353257 : Blo 2043435 10353257 := bstep (se 2 (by rfl) ⟨3882471, by rfl⟩ : syracuseStep 10353257 = 7764943) B7764943
theorem B6902171 : Blo 2043435 6902171 := bstep (se 1 (by rfl) ⟨5176628, by rfl⟩ : syracuseStep 6902171 = 10353257) B10353257
theorem B4601447 : Blo 2043435 4601447 := bstep (se 1 (by rfl) ⟨3451085, by rfl⟩ : syracuseStep 4601447 = 6902171) B6902171
theorem B3067631 : Blo 2043435 3067631 := bstep (se 1 (by rfl) ⟨2300723, by rfl⟩ : syracuseStep 3067631 = 4601447) B4601447
theorem B2045087 : Blo 2043435 2045087 := bstep (se 1 (by rfl) ⟨1533815, by rfl⟩ : syracuseStep 2045087 = 3067631) B3067631
theorem B3067637 : Blo 2043435 3067637 := bbase (se 5 (by rfl) ⟨143795, by rfl⟩ : syracuseStep 3067637 = 287591) (by norm_num)
theorem B2045091 : Blo 2043435 2045091 := bstep (se 1 (by rfl) ⟨1533818, by rfl⟩ : syracuseStep 2045091 = 3067637) B3067637
theorem B3935461 : Blo 2043435 3935461 := bbase (se 4 (by rfl) ⟨368949, by rfl⟩ : syracuseStep 3935461 = 737899) (by norm_num)
theorem B5247281 : Blo 2043435 5247281 := bstep (se 2 (by rfl) ⟨1967730, by rfl⟩ : syracuseStep 5247281 = 3935461) B3935461
theorem B3498187 : Blo 2043435 3498187 := bstep (se 1 (by rfl) ⟨2623640, by rfl⟩ : syracuseStep 3498187 = 5247281) B5247281
theorem B4664249 : Blo 2043435 4664249 := bstep (se 2 (by rfl) ⟨1749093, by rfl⟩ : syracuseStep 4664249 = 3498187) B3498187
theorem B3109499 : Blo 2043435 3109499 := bstep (se 1 (by rfl) ⟨2332124, by rfl⟩ : syracuseStep 3109499 = 4664249) B4664249
theorem B2072999 : Blo 2043435 2072999 := bstep (se 1 (by rfl) ⟨1554749, by rfl⟩ : syracuseStep 2072999 = 3109499) B3109499
theorem B5527997 : Blo 2043435 5527997 := bstep (se 3 (by rfl) ⟨1036499, by rfl⟩ : syracuseStep 5527997 = 2072999) B2072999
theorem B3685331 : Blo 2043435 3685331 := bstep (se 1 (by rfl) ⟨2763998, by rfl⟩ : syracuseStep 3685331 = 5527997) B5527997
theorem B2456887 : Blo 2043435 2456887 := bstep (se 1 (by rfl) ⟨1842665, by rfl⟩ : syracuseStep 2456887 = 3685331) B3685331
theorem B3275849 : Blo 2043435 3275849 := bstep (se 2 (by rfl) ⟨1228443, by rfl⟩ : syracuseStep 3275849 = 2456887) B2456887
theorem B8735597 : Blo 2043435 8735597 := bstep (se 3 (by rfl) ⟨1637924, by rfl⟩ : syracuseStep 8735597 = 3275849) B3275849
theorem B5823731 : Blo 2043435 5823731 := bstep (se 1 (by rfl) ⟨4367798, by rfl⟩ : syracuseStep 5823731 = 8735597) B8735597
theorem B3882487 : Blo 2043435 3882487 := bstep (se 1 (by rfl) ⟨2911865, by rfl⟩ : syracuseStep 3882487 = 5823731) B5823731
theorem B5176649 : Blo 2043435 5176649 := bstep (se 2 (by rfl) ⟨1941243, by rfl⟩ : syracuseStep 5176649 = 3882487) B3882487
theorem B3451099 : Blo 2043435 3451099 := bstep (se 1 (by rfl) ⟨2588324, by rfl⟩ : syracuseStep 3451099 = 5176649) B5176649
theorem B4601465 : Blo 2043435 4601465 := bstep (se 2 (by rfl) ⟨1725549, by rfl⟩ : syracuseStep 4601465 = 3451099) B3451099
theorem B3067643 : Blo 2043435 3067643 := bstep (se 1 (by rfl) ⟨2300732, by rfl⟩ : syracuseStep 3067643 = 4601465) B4601465
theorem B2045095 : Blo 2043435 2045095 := bstep (se 1 (by rfl) ⟨1533821, by rfl⟩ : syracuseStep 2045095 = 3067643) B3067643
theorem B2300737 : Blo 2043435 2300737 := bbase (se 2 (by rfl) ⟨862776, by rfl⟩ : syracuseStep 2300737 = 1725553) (by norm_num)
theorem B3067649 : Blo 2043435 3067649 := bstep (se 2 (by rfl) ⟨1150368, by rfl⟩ : syracuseStep 3067649 = 2300737) B2300737
theorem B2045099 : Blo 2043435 2045099 := bstep (se 1 (by rfl) ⟨1533824, by rfl⟩ : syracuseStep 2045099 = 3067649) B3067649
theorem B5176669 : Blo 2043435 5176669 := bbase (se 3 (by rfl) ⟨970625, by rfl⟩ : syracuseStep 5176669 = 1941251) (by norm_num)
theorem B6902225 : Blo 2043435 6902225 := bstep (se 2 (by rfl) ⟨2588334, by rfl⟩ : syracuseStep 6902225 = 5176669) B5176669
theorem B4601483 : Blo 2043435 4601483 := bstep (se 1 (by rfl) ⟨3451112, by rfl⟩ : syracuseStep 4601483 = 6902225) B6902225
theorem B3067655 : Blo 2043435 3067655 := bstep (se 1 (by rfl) ⟨2300741, by rfl⟩ : syracuseStep 3067655 = 4601483) B4601483
theorem B2045103 : Blo 2043435 2045103 := bstep (se 1 (by rfl) ⟨1533827, by rfl⟩ : syracuseStep 2045103 = 3067655) B3067655
theorem B3067661 : Blo 2043435 3067661 := bbase (se 3 (by rfl) ⟨575186, by rfl⟩ : syracuseStep 3067661 = 1150373) (by norm_num)
theorem B2045107 : Blo 2043435 2045107 := bstep (se 1 (by rfl) ⟨1533830, by rfl⟩ : syracuseStep 2045107 = 3067661) B3067661
theorem B4601501 : Blo 2043435 4601501 := bbase (se 3 (by rfl) ⟨862781, by rfl⟩ : syracuseStep 4601501 = 1725563) (by norm_num)
theorem B3067667 : Blo 2043435 3067667 := bstep (se 1 (by rfl) ⟨2300750, by rfl⟩ : syracuseStep 3067667 = 4601501) B4601501
theorem B2045111 : Blo 2043435 2045111 := bstep (se 1 (by rfl) ⟨1533833, by rfl⟩ : syracuseStep 2045111 = 3067667) B3067667
theorem B3451133 : Blo 2043435 3451133 := bbase (se 3 (by rfl) ⟨647087, by rfl⟩ : syracuseStep 3451133 = 1294175) (by norm_num)
theorem B2300755 : Blo 2043435 2300755 := bstep (se 1 (by rfl) ⟨1725566, by rfl⟩ : syracuseStep 2300755 = 3451133) B3451133
theorem B3067673 : Blo 2043435 3067673 := bstep (se 2 (by rfl) ⟨1150377, by rfl⟩ : syracuseStep 3067673 = 2300755) B2300755
theorem B2045115 : Blo 2043435 2045115 := bstep (se 1 (by rfl) ⟨1533836, by rfl⟩ : syracuseStep 2045115 = 3067673) B3067673
theorem B2490437 : Blo 2043435 2490437 := bbase (se 4 (by rfl) ⟨233478, by rfl⟩ : syracuseStep 2490437 = 466957) (by norm_num)
theorem B6641165 : Blo 2043435 6641165 := bstep (se 3 (by rfl) ⟨1245218, by rfl⟩ : syracuseStep 6641165 = 2490437) B2490437
theorem B4427443 : Blo 2043435 4427443 := bstep (se 1 (by rfl) ⟨3320582, by rfl⟩ : syracuseStep 4427443 = 6641165) B6641165
theorem B23613029 : Blo 2043435 23613029 := bstep (se 4 (by rfl) ⟨2213721, by rfl⟩ : syracuseStep 23613029 = 4427443) B4427443
theorem B15742019 : Blo 2043435 15742019 := bstep (se 1 (by rfl) ⟨11806514, by rfl⟩ : syracuseStep 15742019 = 23613029) B23613029
theorem B10494679 : Blo 2043435 10494679 := bstep (se 1 (by rfl) ⟨7871009, by rfl⟩ : syracuseStep 10494679 = 15742019) B15742019
theorem B13992905 : Blo 2043435 13992905 := bstep (se 2 (by rfl) ⟨5247339, by rfl⟩ : syracuseStep 13992905 = 10494679) B10494679
theorem B9328603 : Blo 2043435 9328603 := bstep (se 1 (by rfl) ⟨6996452, by rfl⟩ : syracuseStep 9328603 = 13992905) B13992905
theorem B12438137 : Blo 2043435 12438137 := bstep (se 2 (by rfl) ⟨4664301, by rfl⟩ : syracuseStep 12438137 = 9328603) B9328603
theorem B8292091 : Blo 2043435 8292091 := bstep (se 1 (by rfl) ⟨6219068, by rfl⟩ : syracuseStep 8292091 = 12438137) B12438137
theorem B11056121 : Blo 2043435 11056121 := bstep (se 2 (by rfl) ⟨4146045, by rfl⟩ : syracuseStep 11056121 = 8292091) B8292091
theorem B7370747 : Blo 2043435 7370747 := bstep (se 1 (by rfl) ⟨5528060, by rfl⟩ : syracuseStep 7370747 = 11056121) B11056121
theorem B4913831 : Blo 2043435 4913831 := bstep (se 1 (by rfl) ⟨3685373, by rfl⟩ : syracuseStep 4913831 = 7370747) B7370747
theorem B3275887 : Blo 2043435 3275887 := bstep (se 1 (by rfl) ⟨2456915, by rfl⟩ : syracuseStep 3275887 = 4913831) B4913831
theorem B4367849 : Blo 2043435 4367849 := bstep (se 2 (by rfl) ⟨1637943, by rfl⟩ : syracuseStep 4367849 = 3275887) B3275887
theorem B11647597 : Blo 2043435 11647597 := bstep (se 3 (by rfl) ⟨2183924, by rfl⟩ : syracuseStep 11647597 = 4367849) B4367849
theorem B15530129 : Blo 2043435 15530129 := bstep (se 2 (by rfl) ⟨5823798, by rfl⟩ : syracuseStep 15530129 = 11647597) B11647597
theorem B10353419 : Blo 2043435 10353419 := bstep (se 1 (by rfl) ⟨7765064, by rfl⟩ : syracuseStep 10353419 = 15530129) B15530129
theorem B6902279 : Blo 2043435 6902279 := bstep (se 1 (by rfl) ⟨5176709, by rfl⟩ : syracuseStep 6902279 = 10353419) B10353419
theorem B4601519 : Blo 2043435 4601519 := bstep (se 1 (by rfl) ⟨3451139, by rfl⟩ : syracuseStep 4601519 = 6902279) B6902279
theorem B3067679 : Blo 2043435 3067679 := bstep (se 1 (by rfl) ⟨2300759, by rfl⟩ : syracuseStep 3067679 = 4601519) B4601519
theorem B2045119 : Blo 2043435 2045119 := bstep (se 1 (by rfl) ⟨1533839, by rfl⟩ : syracuseStep 2045119 = 3067679) B3067679
theorem B3067685 : Blo 2043435 3067685 := bbase (se 4 (by rfl) ⟨287595, by rfl⟩ : syracuseStep 3067685 = 575191) (by norm_num)
theorem B2045123 : Blo 2043435 2045123 := bstep (se 1 (by rfl) ⟨1533842, by rfl⟩ : syracuseStep 2045123 = 3067685) B3067685
theorem B2588365 : Blo 2043435 2588365 := bbase (se 3 (by rfl) ⟨485318, by rfl⟩ : syracuseStep 2588365 = 970637) (by norm_num)
theorem B3451153 : Blo 2043435 3451153 := bstep (se 2 (by rfl) ⟨1294182, by rfl⟩ : syracuseStep 3451153 = 2588365) B2588365
theorem B4601537 : Blo 2043435 4601537 := bstep (se 2 (by rfl) ⟨1725576, by rfl⟩ : syracuseStep 4601537 = 3451153) B3451153
theorem B3067691 : Blo 2043435 3067691 := bstep (se 1 (by rfl) ⟨2300768, by rfl⟩ : syracuseStep 3067691 = 4601537) B4601537
theorem B2045127 : Blo 2043435 2045127 := bstep (se 1 (by rfl) ⟨1533845, by rfl⟩ : syracuseStep 2045127 = 3067691) B3067691
theorem B2300773 : Blo 2043435 2300773 := bbase (se 4 (by rfl) ⟨215697, by rfl⟩ : syracuseStep 2300773 = 431395) (by norm_num)
theorem B3067697 : Blo 2043435 3067697 := bstep (se 2 (by rfl) ⟨1150386, by rfl⟩ : syracuseStep 3067697 = 2300773) B2300773
theorem B2045131 : Blo 2043435 2045131 := bstep (se 1 (by rfl) ⟨1533848, by rfl⟩ : syracuseStep 2045131 = 3067697) B3067697
theorem B5823845 : Blo 2043435 5823845 := bbase (se 4 (by rfl) ⟨545985, by rfl⟩ : syracuseStep 5823845 = 1091971) (by norm_num)
theorem B3882563 : Blo 2043435 3882563 := bstep (se 1 (by rfl) ⟨2911922, by rfl⟩ : syracuseStep 3882563 = 5823845) B5823845
theorem B2588375 : Blo 2043435 2588375 := bstep (se 1 (by rfl) ⟨1941281, by rfl⟩ : syracuseStep 2588375 = 3882563) B3882563
theorem B6902333 : Blo 2043435 6902333 := bstep (se 3 (by rfl) ⟨1294187, by rfl⟩ : syracuseStep 6902333 = 2588375) B2588375
theorem B4601555 : Blo 2043435 4601555 := bstep (se 1 (by rfl) ⟨3451166, by rfl⟩ : syracuseStep 4601555 = 6902333) B6902333
theorem B3067703 : Blo 2043435 3067703 := bstep (se 1 (by rfl) ⟨2300777, by rfl⟩ : syracuseStep 3067703 = 4601555) B4601555
theorem B2045135 : Blo 2043435 2045135 := bstep (se 1 (by rfl) ⟨1533851, by rfl⟩ : syracuseStep 2045135 = 3067703) B3067703
theorem B3067709 : Blo 2043435 3067709 := bbase (se 3 (by rfl) ⟨575195, by rfl⟩ : syracuseStep 3067709 = 1150391) (by norm_num)
theorem B2045139 : Blo 2043435 2045139 := bstep (se 1 (by rfl) ⟨1533854, by rfl⟩ : syracuseStep 2045139 = 3067709) B3067709
theorem B4601573 : Blo 2043435 4601573 := bbase (se 4 (by rfl) ⟨431397, by rfl⟩ : syracuseStep 4601573 = 862795) (by norm_num)
theorem B3067715 : Blo 2043435 3067715 := bstep (se 1 (by rfl) ⟨2300786, by rfl⟩ : syracuseStep 3067715 = 4601573) B4601573
theorem B2045143 : Blo 2043435 2045143 := bstep (se 1 (by rfl) ⟨1533857, by rfl⟩ : syracuseStep 2045143 = 3067715) B3067715
theorem B5176781 : Blo 2043435 5176781 := bbase (se 3 (by rfl) ⟨970646, by rfl⟩ : syracuseStep 5176781 = 1941293) (by norm_num)
theorem B3451187 : Blo 2043435 3451187 := bstep (se 1 (by rfl) ⟨2588390, by rfl⟩ : syracuseStep 3451187 = 5176781) B5176781
theorem B2300791 : Blo 2043435 2300791 := bstep (se 1 (by rfl) ⟨1725593, by rfl⟩ : syracuseStep 2300791 = 3451187) B3451187
theorem B3067721 : Blo 2043435 3067721 := bstep (se 2 (by rfl) ⟨1150395, by rfl⟩ : syracuseStep 3067721 = 2300791) B2300791
theorem B2045147 : Blo 2043435 2045147 := bstep (se 1 (by rfl) ⟨1533860, by rfl⟩ : syracuseStep 2045147 = 3067721) B3067721
theorem B4913909 : Blo 2043435 4913909 := bbase (se 5 (by rfl) ⟨230339, by rfl⟩ : syracuseStep 4913909 = 460679) (by norm_num)
theorem B3275939 : Blo 2043435 3275939 := bstep (se 1 (by rfl) ⟨2456954, by rfl⟩ : syracuseStep 3275939 = 4913909) B4913909
theorem B2183959 : Blo 2043435 2183959 := bstep (se 1 (by rfl) ⟨1637969, by rfl⟩ : syracuseStep 2183959 = 3275939) B3275939
theorem B2911945 : Blo 2043435 2911945 := bstep (se 2 (by rfl) ⟨1091979, by rfl⟩ : syracuseStep 2911945 = 2183959) B2183959
theorem B3882593 : Blo 2043435 3882593 := bstep (se 2 (by rfl) ⟨1455972, by rfl⟩ : syracuseStep 3882593 = 2911945) B2911945
theorem B10353581 : Blo 2043435 10353581 := bstep (se 3 (by rfl) ⟨1941296, by rfl⟩ : syracuseStep 10353581 = 3882593) B3882593
theorem B6902387 : Blo 2043435 6902387 := bstep (se 1 (by rfl) ⟨5176790, by rfl⟩ : syracuseStep 6902387 = 10353581) B10353581
theorem B4601591 : Blo 2043435 4601591 := bstep (se 1 (by rfl) ⟨3451193, by rfl⟩ : syracuseStep 4601591 = 6902387) B6902387
theorem B3067727 : Blo 2043435 3067727 := bstep (se 1 (by rfl) ⟨2300795, by rfl⟩ : syracuseStep 3067727 = 4601591) B4601591
theorem B2045151 : Blo 2043435 2045151 := bstep (se 1 (by rfl) ⟨1533863, by rfl⟩ : syracuseStep 2045151 = 3067727) B3067727
theorem B3067733 : Blo 2043435 3067733 := bbase (se 9 (by rfl) ⟨8987, by rfl⟩ : syracuseStep 3067733 = 17975) (by norm_num)
theorem B2045155 : Blo 2043435 2045155 := bstep (se 1 (by rfl) ⟨1533866, by rfl⟩ : syracuseStep 2045155 = 3067733) B3067733
theorem B4980973 : Blo 2043435 4980973 := bbase (se 3 (by rfl) ⟨933932, by rfl⟩ : syracuseStep 4980973 = 1867865) (by norm_num)
theorem B6641297 : Blo 2043435 6641297 := bstep (se 2 (by rfl) ⟨2490486, by rfl⟩ : syracuseStep 6641297 = 4980973) B4980973
theorem B4427531 : Blo 2043435 4427531 := bstep (se 1 (by rfl) ⟨3320648, by rfl⟩ : syracuseStep 4427531 = 6641297) B6641297
theorem B2951687 : Blo 2043435 2951687 := bstep (se 1 (by rfl) ⟨2213765, by rfl⟩ : syracuseStep 2951687 = 4427531) B4427531
theorem B7871165 : Blo 2043435 7871165 := bstep (se 3 (by rfl) ⟨1475843, by rfl⟩ : syracuseStep 7871165 = 2951687) B2951687
theorem B5247443 : Blo 2043435 5247443 := bstep (se 1 (by rfl) ⟨3935582, by rfl⟩ : syracuseStep 5247443 = 7871165) B7871165
theorem B3498295 : Blo 2043435 3498295 := bstep (se 1 (by rfl) ⟨2623721, by rfl⟩ : syracuseStep 3498295 = 5247443) B5247443
theorem B4664393 : Blo 2043435 4664393 := bstep (se 2 (by rfl) ⟨1749147, by rfl⟩ : syracuseStep 4664393 = 3498295) B3498295
theorem B3109595 : Blo 2043435 3109595 := bstep (se 1 (by rfl) ⟨2332196, by rfl⟩ : syracuseStep 3109595 = 4664393) B4664393
theorem B33169013 : Blo 2043435 33169013 := bstep (se 5 (by rfl) ⟨1554797, by rfl⟩ : syracuseStep 33169013 = 3109595) B3109595
theorem B22112675 : Blo 2043435 22112675 := bstep (se 1 (by rfl) ⟨16584506, by rfl⟩ : syracuseStep 22112675 = 33169013) B33169013
theorem B14741783 : Blo 2043435 14741783 := bstep (se 1 (by rfl) ⟨11056337, by rfl⟩ : syracuseStep 14741783 = 22112675) B22112675
theorem B9827855 : Blo 2043435 9827855 := bstep (se 1 (by rfl) ⟨7370891, by rfl⟩ : syracuseStep 9827855 = 14741783) B14741783
theorem B6551903 : Blo 2043435 6551903 := bstep (se 1 (by rfl) ⟨4913927, by rfl⟩ : syracuseStep 6551903 = 9827855) B9827855
theorem B4367935 : Blo 2043435 4367935 := bstep (se 1 (by rfl) ⟨3275951, by rfl⟩ : syracuseStep 4367935 = 6551903) B6551903
theorem B5823913 : Blo 2043435 5823913 := bstep (se 2 (by rfl) ⟨2183967, by rfl⟩ : syracuseStep 5823913 = 4367935) B4367935
theorem B7765217 : Blo 2043435 7765217 := bstep (se 2 (by rfl) ⟨2911956, by rfl⟩ : syracuseStep 7765217 = 5823913) B5823913
theorem B5176811 : Blo 2043435 5176811 := bstep (se 1 (by rfl) ⟨3882608, by rfl⟩ : syracuseStep 5176811 = 7765217) B7765217
theorem B3451207 : Blo 2043435 3451207 := bstep (se 1 (by rfl) ⟨2588405, by rfl⟩ : syracuseStep 3451207 = 5176811) B5176811
theorem B4601609 : Blo 2043435 4601609 := bstep (se 2 (by rfl) ⟨1725603, by rfl⟩ : syracuseStep 4601609 = 3451207) B3451207
theorem B3067739 : Blo 2043435 3067739 := bstep (se 1 (by rfl) ⟨2300804, by rfl⟩ : syracuseStep 3067739 = 4601609) B4601609
theorem B2045159 : Blo 2043435 2045159 := bstep (se 1 (by rfl) ⟨1533869, by rfl⟩ : syracuseStep 2045159 = 3067739) B3067739
theorem B2300809 : Blo 2043435 2300809 := bbase (se 2 (by rfl) ⟨862803, by rfl⟩ : syracuseStep 2300809 = 1725607) (by norm_num)
theorem B3067745 : Blo 2043435 3067745 := bstep (se 2 (by rfl) ⟨1150404, by rfl⟩ : syracuseStep 3067745 = 2300809) B2300809
theorem B2045163 : Blo 2043435 2045163 := bstep (se 1 (by rfl) ⟨1533872, by rfl⟩ : syracuseStep 2045163 = 3067745) B3067745
theorem B59771861 : Blo 2043435 59771861 := bbase (se 7 (by rfl) ⟨700451, by rfl⟩ : syracuseStep 59771861 = 1400903) (by norm_num)
theorem B39847907 : Blo 2043435 39847907 := bstep (se 1 (by rfl) ⟨29885930, by rfl⟩ : syracuseStep 39847907 = 59771861) B59771861
theorem B106261085 : Blo 2043435 106261085 := bstep (se 3 (by rfl) ⟨19923953, by rfl⟩ : syracuseStep 106261085 = 39847907) B39847907
theorem B283362893 : Blo 2043435 283362893 := bstep (se 3 (by rfl) ⟨53130542, by rfl⟩ : syracuseStep 283362893 = 106261085) B106261085
theorem B188908595 : Blo 2043435 188908595 := bstep (se 1 (by rfl) ⟨141681446, by rfl⟩ : syracuseStep 188908595 = 283362893) B283362893
theorem B125939063 : Blo 2043435 125939063 := bstep (se 1 (by rfl) ⟨94454297, by rfl⟩ : syracuseStep 125939063 = 188908595) B188908595
theorem B83959375 : Blo 2043435 83959375 := bstep (se 1 (by rfl) ⟨62969531, by rfl⟩ : syracuseStep 83959375 = 125939063) B125939063
theorem B111945833 : Blo 2043435 111945833 := bstep (se 2 (by rfl) ⟨41979687, by rfl⟩ : syracuseStep 111945833 = 83959375) B83959375
theorem B74630555 : Blo 2043435 74630555 := bstep (se 1 (by rfl) ⟨55972916, by rfl⟩ : syracuseStep 74630555 = 111945833) B111945833
theorem B49753703 : Blo 2043435 49753703 := bstep (se 1 (by rfl) ⟨37315277, by rfl⟩ : syracuseStep 49753703 = 74630555) B74630555
theorem B132676541 : Blo 2043435 132676541 := bstep (se 3 (by rfl) ⟨24876851, by rfl⟩ : syracuseStep 132676541 = 49753703) B49753703
theorem B88451027 : Blo 2043435 88451027 := bstep (se 1 (by rfl) ⟨66338270, by rfl⟩ : syracuseStep 88451027 = 132676541) B132676541
theorem B58967351 : Blo 2043435 58967351 := bstep (se 1 (by rfl) ⟨44225513, by rfl⟩ : syracuseStep 58967351 = 88451027) B88451027
theorem B39311567 : Blo 2043435 39311567 := bstep (se 1 (by rfl) ⟨29483675, by rfl⟩ : syracuseStep 39311567 = 58967351) B58967351
theorem B26207711 : Blo 2043435 26207711 := bstep (se 1 (by rfl) ⟨19655783, by rfl⟩ : syracuseStep 26207711 = 39311567) B39311567
theorem B17471807 : Blo 2043435 17471807 := bstep (se 1 (by rfl) ⟨13103855, by rfl⟩ : syracuseStep 17471807 = 26207711) B26207711
theorem B11647871 : Blo 2043435 11647871 := bstep (se 1 (by rfl) ⟨8735903, by rfl⟩ : syracuseStep 11647871 = 17471807) B17471807
theorem B7765247 : Blo 2043435 7765247 := bstep (se 1 (by rfl) ⟨5823935, by rfl⟩ : syracuseStep 7765247 = 11647871) B11647871
theorem B5176831 : Blo 2043435 5176831 := bstep (se 1 (by rfl) ⟨3882623, by rfl⟩ : syracuseStep 5176831 = 7765247) B7765247
theorem B6902441 : Blo 2043435 6902441 := bstep (se 2 (by rfl) ⟨2588415, by rfl⟩ : syracuseStep 6902441 = 5176831) B5176831
theorem B4601627 : Blo 2043435 4601627 := bstep (se 1 (by rfl) ⟨3451220, by rfl⟩ : syracuseStep 4601627 = 6902441) B6902441
theorem B3067751 : Blo 2043435 3067751 := bstep (se 1 (by rfl) ⟨2300813, by rfl⟩ : syracuseStep 3067751 = 4601627) B4601627
theorem B2045167 : Blo 2043435 2045167 := bstep (se 1 (by rfl) ⟨1533875, by rfl⟩ : syracuseStep 2045167 = 3067751) B3067751
theorem B3067757 : Blo 2043435 3067757 := bbase (se 3 (by rfl) ⟨575204, by rfl⟩ : syracuseStep 3067757 = 1150409) (by norm_num)
theorem B2045171 : Blo 2043435 2045171 := bstep (se 1 (by rfl) ⟨1533878, by rfl⟩ : syracuseStep 2045171 = 3067757) B3067757
theorem B4601645 : Blo 2043435 4601645 := bbase (se 3 (by rfl) ⟨862808, by rfl⟩ : syracuseStep 4601645 = 1725617) (by norm_num)
theorem B3067763 : Blo 2043435 3067763 := bstep (se 1 (by rfl) ⟨2300822, by rfl⟩ : syracuseStep 3067763 = 4601645) B4601645
theorem B2045175 : Blo 2043435 2045175 := bstep (se 1 (by rfl) ⟨1533881, by rfl⟩ : syracuseStep 2045175 = 3067763) B3067763
theorem B8735957 : Blo 2043435 8735957 := bbase (se 7 (by rfl) ⟨102374, by rfl⟩ : syracuseStep 8735957 = 204749) (by norm_num)
theorem B5823971 : Blo 2043435 5823971 := bstep (se 1 (by rfl) ⟨4367978, by rfl⟩ : syracuseStep 5823971 = 8735957) B8735957
theorem B3882647 : Blo 2043435 3882647 := bstep (se 1 (by rfl) ⟨2911985, by rfl⟩ : syracuseStep 3882647 = 5823971) B5823971
theorem B2588431 : Blo 2043435 2588431 := bstep (se 1 (by rfl) ⟨1941323, by rfl⟩ : syracuseStep 2588431 = 3882647) B3882647
theorem B3451241 : Blo 2043435 3451241 := bstep (se 2 (by rfl) ⟨1294215, by rfl⟩ : syracuseStep 3451241 = 2588431) B2588431
theorem B2300827 : Blo 2043435 2300827 := bstep (se 1 (by rfl) ⟨1725620, by rfl⟩ : syracuseStep 2300827 = 3451241) B3451241
theorem B3067769 : Blo 2043435 3067769 := bstep (se 2 (by rfl) ⟨1150413, by rfl⟩ : syracuseStep 3067769 = 2300827) B2300827
theorem B2045179 : Blo 2043435 2045179 := bstep (se 1 (by rfl) ⟨1533884, by rfl⟩ : syracuseStep 2045179 = 3067769) B3067769
theorem B13103957 : Blo 2043435 13103957 := bbase (se 9 (by rfl) ⟨38390, by rfl⟩ : syracuseStep 13103957 = 76781) (by norm_num)
theorem B34943885 : Blo 2043435 34943885 := bstep (se 3 (by rfl) ⟨6551978, by rfl⟩ : syracuseStep 34943885 = 13103957) B13103957
theorem B23295923 : Blo 2043435 23295923 := bstep (se 1 (by rfl) ⟨17471942, by rfl⟩ : syracuseStep 23295923 = 34943885) B34943885
theorem B15530615 : Blo 2043435 15530615 := bstep (se 1 (by rfl) ⟨11647961, by rfl⟩ : syracuseStep 15530615 = 23295923) B23295923
theorem B10353743 : Blo 2043435 10353743 := bstep (se 1 (by rfl) ⟨7765307, by rfl⟩ : syracuseStep 10353743 = 15530615) B15530615
theorem B6902495 : Blo 2043435 6902495 := bstep (se 1 (by rfl) ⟨5176871, by rfl⟩ : syracuseStep 6902495 = 10353743) B10353743
theorem B4601663 : Blo 2043435 4601663 := bstep (se 1 (by rfl) ⟨3451247, by rfl⟩ : syracuseStep 4601663 = 6902495) B6902495
theorem B3067775 : Blo 2043435 3067775 := bstep (se 1 (by rfl) ⟨2300831, by rfl⟩ : syracuseStep 3067775 = 4601663) B4601663
theorem B2045183 : Blo 2043435 2045183 := bstep (se 1 (by rfl) ⟨1533887, by rfl⟩ : syracuseStep 2045183 = 3067775) B3067775
theorem B3067781 : Blo 2043435 3067781 := bbase (se 4 (by rfl) ⟨287604, by rfl⟩ : syracuseStep 3067781 = 575209) (by norm_num)
theorem B2045187 : Blo 2043435 2045187 := bstep (se 1 (by rfl) ⟨1533890, by rfl⟩ : syracuseStep 2045187 = 3067781) B3067781
theorem B3451261 : Blo 2043435 3451261 := bbase (se 3 (by rfl) ⟨647111, by rfl⟩ : syracuseStep 3451261 = 1294223) (by norm_num)
theorem B4601681 : Blo 2043435 4601681 := bstep (se 2 (by rfl) ⟨1725630, by rfl⟩ : syracuseStep 4601681 = 3451261) B3451261
theorem B3067787 : Blo 2043435 3067787 := bstep (se 1 (by rfl) ⟨2300840, by rfl⟩ : syracuseStep 3067787 = 4601681) B4601681
theorem B2045191 : Blo 2043435 2045191 := bstep (se 1 (by rfl) ⟨1533893, by rfl⟩ : syracuseStep 2045191 = 3067787) B3067787
theorem B2300845 : Blo 2043435 2300845 := bbase (se 3 (by rfl) ⟨431408, by rfl⟩ : syracuseStep 2300845 = 862817) (by norm_num)
theorem B3067793 : Blo 2043435 3067793 := bstep (se 2 (by rfl) ⟨1150422, by rfl⟩ : syracuseStep 3067793 = 2300845) B2300845
theorem B2045195 : Blo 2043435 2045195 := bstep (se 1 (by rfl) ⟨1533896, by rfl⟩ : syracuseStep 2045195 = 3067793) B3067793
theorem B6902549 : Blo 2043435 6902549 := bbase (se 6 (by rfl) ⟨161778, by rfl⟩ : syracuseStep 6902549 = 323557) (by norm_num)
theorem B4601699 : Blo 2043435 4601699 := bstep (se 1 (by rfl) ⟨3451274, by rfl⟩ : syracuseStep 4601699 = 6902549) B6902549
theorem B3067799 : Blo 2043435 3067799 := bstep (se 1 (by rfl) ⟨2300849, by rfl⟩ : syracuseStep 3067799 = 4601699) B4601699
theorem B2045199 : Blo 2043435 2045199 := bstep (se 1 (by rfl) ⟨1533899, by rfl⟩ : syracuseStep 2045199 = 3067799) B3067799
theorem B3067805 : Blo 2043435 3067805 := bbase (se 3 (by rfl) ⟨575213, by rfl⟩ : syracuseStep 3067805 = 1150427) (by norm_num)
theorem B2045203 : Blo 2043435 2045203 := bstep (se 1 (by rfl) ⟨1533902, by rfl⟩ : syracuseStep 2045203 = 3067805) B3067805
theorem B4601717 : Blo 2043435 4601717 := bbase (se 5 (by rfl) ⟨215705, by rfl⟩ : syracuseStep 4601717 = 431411) (by norm_num)
theorem B3067811 : Blo 2043435 3067811 := bstep (se 1 (by rfl) ⟨2300858, by rfl⟩ : syracuseStep 3067811 = 4601717) B4601717
theorem B2045207 : Blo 2043435 2045207 := bstep (se 1 (by rfl) ⟨1533905, by rfl⟩ : syracuseStep 2045207 = 3067811) B3067811
theorem B5528309 : Blo 2043435 5528309 := bbase (se 5 (by rfl) ⟨259139, by rfl⟩ : syracuseStep 5528309 = 518279) (by norm_num)
theorem B14742157 : Blo 2043435 14742157 := bstep (se 3 (by rfl) ⟨2764154, by rfl⟩ : syracuseStep 14742157 = 5528309) B5528309
theorem B19656209 : Blo 2043435 19656209 := bstep (se 2 (by rfl) ⟨7371078, by rfl⟩ : syracuseStep 19656209 = 14742157) B14742157
theorem B13104139 : Blo 2043435 13104139 := bstep (se 1 (by rfl) ⟨9828104, by rfl⟩ : syracuseStep 13104139 = 19656209) B19656209
theorem B17472185 : Blo 2043435 17472185 := bstep (se 2 (by rfl) ⟨6552069, by rfl⟩ : syracuseStep 17472185 = 13104139) B13104139
theorem B11648123 : Blo 2043435 11648123 := bstep (se 1 (by rfl) ⟨8736092, by rfl⟩ : syracuseStep 11648123 = 17472185) B17472185
theorem B7765415 : Blo 2043435 7765415 := bstep (se 1 (by rfl) ⟨5824061, by rfl⟩ : syracuseStep 7765415 = 11648123) B11648123
theorem B5176943 : Blo 2043435 5176943 := bstep (se 1 (by rfl) ⟨3882707, by rfl⟩ : syracuseStep 5176943 = 7765415) B7765415
theorem B3451295 : Blo 2043435 3451295 := bstep (se 1 (by rfl) ⟨2588471, by rfl⟩ : syracuseStep 3451295 = 5176943) B5176943
theorem B2300863 : Blo 2043435 2300863 := bstep (se 1 (by rfl) ⟨1725647, by rfl⟩ : syracuseStep 2300863 = 3451295) B3451295
theorem B3067817 : Blo 2043435 3067817 := bstep (se 2 (by rfl) ⟨1150431, by rfl⟩ : syracuseStep 3067817 = 2300863) B2300863
theorem B2045211 : Blo 2043435 2045211 := bstep (se 1 (by rfl) ⟨1533908, by rfl⟩ : syracuseStep 2045211 = 3067817) B3067817
theorem B7765429 : Blo 2043435 7765429 := bbase (se 5 (by rfl) ⟨364004, by rfl⟩ : syracuseStep 7765429 = 728009) (by norm_num)
theorem B10353905 : Blo 2043435 10353905 := bstep (se 2 (by rfl) ⟨3882714, by rfl⟩ : syracuseStep 10353905 = 7765429) B7765429
theorem B6902603 : Blo 2043435 6902603 := bstep (se 1 (by rfl) ⟨5176952, by rfl⟩ : syracuseStep 6902603 = 10353905) B10353905
theorem B4601735 : Blo 2043435 4601735 := bstep (se 1 (by rfl) ⟨3451301, by rfl⟩ : syracuseStep 4601735 = 6902603) B6902603
theorem B3067823 : Blo 2043435 3067823 := bstep (se 1 (by rfl) ⟨2300867, by rfl⟩ : syracuseStep 3067823 = 4601735) B4601735
theorem B2045215 : Blo 2043435 2045215 := bstep (se 1 (by rfl) ⟨1533911, by rfl⟩ : syracuseStep 2045215 = 3067823) B3067823
theorem B3067829 : Blo 2043435 3067829 := bbase (se 5 (by rfl) ⟨143804, by rfl⟩ : syracuseStep 3067829 = 287609) (by norm_num)
theorem B2045219 : Blo 2043435 2045219 := bstep (se 1 (by rfl) ⟨1533914, by rfl⟩ : syracuseStep 2045219 = 3067829) B3067829
theorem B5176973 : Blo 2043435 5176973 := bbase (se 3 (by rfl) ⟨970682, by rfl⟩ : syracuseStep 5176973 = 1941365) (by norm_num)
theorem B3451315 : Blo 2043435 3451315 := bstep (se 1 (by rfl) ⟨2588486, by rfl⟩ : syracuseStep 3451315 = 5176973) B5176973
theorem B4601753 : Blo 2043435 4601753 := bstep (se 2 (by rfl) ⟨1725657, by rfl⟩ : syracuseStep 4601753 = 3451315) B3451315
theorem B3067835 : Blo 2043435 3067835 := bstep (se 1 (by rfl) ⟨2300876, by rfl⟩ : syracuseStep 3067835 = 4601753) B4601753
theorem B2045223 : Blo 2043435 2045223 := bstep (se 1 (by rfl) ⟨1533917, by rfl⟩ : syracuseStep 2045223 = 3067835) B3067835
theorem B2300881 : Blo 2043435 2300881 := bbase (se 2 (by rfl) ⟨862830, by rfl⟩ : syracuseStep 2300881 = 1725661) (by norm_num)
theorem B3067841 : Blo 2043435 3067841 := bstep (se 2 (by rfl) ⟨1150440, by rfl⟩ : syracuseStep 3067841 = 2300881) B2300881
theorem B2045227 : Blo 2043435 2045227 := bstep (se 1 (by rfl) ⟨1533920, by rfl⟩ : syracuseStep 2045227 = 3067841) B3067841
theorem B4914101 : Blo 2043435 4914101 := bbase (se 5 (by rfl) ⟨230348, by rfl⟩ : syracuseStep 4914101 = 460697) (by norm_num)
theorem B3276067 : Blo 2043435 3276067 := bstep (se 1 (by rfl) ⟨2457050, by rfl⟩ : syracuseStep 3276067 = 4914101) B4914101
theorem B4368089 : Blo 2043435 4368089 := bstep (se 2 (by rfl) ⟨1638033, by rfl⟩ : syracuseStep 4368089 = 3276067) B3276067
theorem B2912059 : Blo 2043435 2912059 := bstep (se 1 (by rfl) ⟨2184044, by rfl⟩ : syracuseStep 2912059 = 4368089) B4368089
theorem B3882745 : Blo 2043435 3882745 := bstep (se 2 (by rfl) ⟨1456029, by rfl⟩ : syracuseStep 3882745 = 2912059) B2912059
theorem B5176993 : Blo 2043435 5176993 := bstep (se 2 (by rfl) ⟨1941372, by rfl⟩ : syracuseStep 5176993 = 3882745) B3882745
theorem B6902657 : Blo 2043435 6902657 := bstep (se 2 (by rfl) ⟨2588496, by rfl⟩ : syracuseStep 6902657 = 5176993) B5176993
theorem B4601771 : Blo 2043435 4601771 := bstep (se 1 (by rfl) ⟨3451328, by rfl⟩ : syracuseStep 4601771 = 6902657) B6902657
theorem B3067847 : Blo 2043435 3067847 := bstep (se 1 (by rfl) ⟨2300885, by rfl⟩ : syracuseStep 3067847 = 4601771) B4601771
theorem B2045231 : Blo 2043435 2045231 := bstep (se 1 (by rfl) ⟨1533923, by rfl⟩ : syracuseStep 2045231 = 3067847) B3067847
theorem B3067853 : Blo 2043435 3067853 := bbase (se 3 (by rfl) ⟨575222, by rfl⟩ : syracuseStep 3067853 = 1150445) (by norm_num)
theorem B2045235 : Blo 2043435 2045235 := bstep (se 1 (by rfl) ⟨1533926, by rfl⟩ : syracuseStep 2045235 = 3067853) B3067853
theorem B4601789 : Blo 2043435 4601789 := bbase (se 3 (by rfl) ⟨862835, by rfl⟩ : syracuseStep 4601789 = 1725671) (by norm_num)
theorem B3067859 : Blo 2043435 3067859 := bstep (se 1 (by rfl) ⟨2300894, by rfl⟩ : syracuseStep 3067859 = 4601789) B4601789
theorem B2045239 : Blo 2043435 2045239 := bstep (se 1 (by rfl) ⟨1533929, by rfl⟩ : syracuseStep 2045239 = 3067859) B3067859
theorem B3451349 : Blo 2043435 3451349 := bbase (se 7 (by rfl) ⟨40445, by rfl⟩ : syracuseStep 3451349 = 80891) (by norm_num)
theorem B2300899 : Blo 2043435 2300899 := bstep (se 1 (by rfl) ⟨1725674, by rfl⟩ : syracuseStep 2300899 = 3451349) B3451349
theorem B3067865 : Blo 2043435 3067865 := bstep (se 2 (by rfl) ⟨1150449, by rfl⟩ : syracuseStep 3067865 = 2300899) B2300899
theorem B2045243 : Blo 2043435 2045243 := bstep (se 1 (by rfl) ⟨1533932, by rfl⟩ : syracuseStep 2045243 = 3067865) B3067865
theorem B8736245 : Blo 2043435 8736245 := bbase (se 5 (by rfl) ⟨409511, by rfl⟩ : syracuseStep 8736245 = 819023) (by norm_num)
theorem B5824163 : Blo 2043435 5824163 := bstep (se 1 (by rfl) ⟨4368122, by rfl⟩ : syracuseStep 5824163 = 8736245) B8736245
theorem B15531101 : Blo 2043435 15531101 := bstep (se 3 (by rfl) ⟨2912081, by rfl⟩ : syracuseStep 15531101 = 5824163) B5824163
theorem B10354067 : Blo 2043435 10354067 := bstep (se 1 (by rfl) ⟨7765550, by rfl⟩ : syracuseStep 10354067 = 15531101) B15531101
theorem B6902711 : Blo 2043435 6902711 := bstep (se 1 (by rfl) ⟨5177033, by rfl⟩ : syracuseStep 6902711 = 10354067) B10354067
theorem B4601807 : Blo 2043435 4601807 := bstep (se 1 (by rfl) ⟨3451355, by rfl⟩ : syracuseStep 4601807 = 6902711) B6902711
theorem B3067871 : Blo 2043435 3067871 := bstep (se 1 (by rfl) ⟨2300903, by rfl⟩ : syracuseStep 3067871 = 4601807) B4601807
theorem B2045247 : Blo 2043435 2045247 := bstep (se 1 (by rfl) ⟨1533935, by rfl⟩ : syracuseStep 2045247 = 3067871) B3067871
theorem B3067877 : Blo 2043435 3067877 := bbase (se 4 (by rfl) ⟨287613, by rfl⟩ : syracuseStep 3067877 = 575227) (by norm_num)
theorem B2045251 : Blo 2043435 2045251 := bstep (se 1 (by rfl) ⟨1533938, by rfl⟩ : syracuseStep 2045251 = 3067877) B3067877
theorem B2073161 : Blo 2043435 2073161 := bbase (se 2 (by rfl) ⟨777435, by rfl⟩ : syracuseStep 2073161 = 1554871) (by norm_num)
theorem B5528429 : Blo 2043435 5528429 := bstep (se 3 (by rfl) ⟨1036580, by rfl⟩ : syracuseStep 5528429 = 2073161) B2073161
theorem B3685619 : Blo 2043435 3685619 := bstep (se 1 (by rfl) ⟨2764214, by rfl⟩ : syracuseStep 3685619 = 5528429) B5528429
theorem B9828317 : Blo 2043435 9828317 := bstep (se 3 (by rfl) ⟨1842809, by rfl⟩ : syracuseStep 9828317 = 3685619) B3685619
theorem B6552211 : Blo 2043435 6552211 := bstep (se 1 (by rfl) ⟨4914158, by rfl⟩ : syracuseStep 6552211 = 9828317) B9828317
theorem B8736281 : Blo 2043435 8736281 := bstep (se 2 (by rfl) ⟨3276105, by rfl⟩ : syracuseStep 8736281 = 6552211) B6552211
theorem B5824187 : Blo 2043435 5824187 := bstep (se 1 (by rfl) ⟨4368140, by rfl⟩ : syracuseStep 5824187 = 8736281) B8736281
theorem B3882791 : Blo 2043435 3882791 := bstep (se 1 (by rfl) ⟨2912093, by rfl⟩ : syracuseStep 3882791 = 5824187) B5824187
theorem B2588527 : Blo 2043435 2588527 := bstep (se 1 (by rfl) ⟨1941395, by rfl⟩ : syracuseStep 2588527 = 3882791) B3882791
theorem B3451369 : Blo 2043435 3451369 := bstep (se 2 (by rfl) ⟨1294263, by rfl⟩ : syracuseStep 3451369 = 2588527) B2588527
theorem B4601825 : Blo 2043435 4601825 := bstep (se 2 (by rfl) ⟨1725684, by rfl⟩ : syracuseStep 4601825 = 3451369) B3451369
theorem B3067883 : Blo 2043435 3067883 := bstep (se 1 (by rfl) ⟨2300912, by rfl⟩ : syracuseStep 3067883 = 4601825) B4601825
theorem B2045255 : Blo 2043435 2045255 := bstep (se 1 (by rfl) ⟨1533941, by rfl⟩ : syracuseStep 2045255 = 3067883) B3067883
theorem B2300917 : Blo 2043435 2300917 := bbase (se 5 (by rfl) ⟨107855, by rfl⟩ : syracuseStep 2300917 = 215711) (by norm_num)
theorem B3067889 : Blo 2043435 3067889 := bstep (se 2 (by rfl) ⟨1150458, by rfl⟩ : syracuseStep 3067889 = 2300917) B2300917
theorem B2045259 : Blo 2043435 2045259 := bstep (se 1 (by rfl) ⟨1533944, by rfl⟩ : syracuseStep 2045259 = 3067889) B3067889
theorem B2588537 : Blo 2043435 2588537 := bbase (se 2 (by rfl) ⟨970701, by rfl⟩ : syracuseStep 2588537 = 1941403) (by norm_num)
theorem B6902765 : Blo 2043435 6902765 := bstep (se 3 (by rfl) ⟨1294268, by rfl⟩ : syracuseStep 6902765 = 2588537) B2588537
theorem B4601843 : Blo 2043435 4601843 := bstep (se 1 (by rfl) ⟨3451382, by rfl⟩ : syracuseStep 4601843 = 6902765) B6902765
theorem B3067895 : Blo 2043435 3067895 := bstep (se 1 (by rfl) ⟨2300921, by rfl⟩ : syracuseStep 3067895 = 4601843) B4601843
theorem B2045263 : Blo 2043435 2045263 := bstep (se 1 (by rfl) ⟨1533947, by rfl⟩ : syracuseStep 2045263 = 3067895) B3067895
theorem B3067901 : Blo 2043435 3067901 := bbase (se 3 (by rfl) ⟨575231, by rfl⟩ : syracuseStep 3067901 = 1150463) (by norm_num)
theorem B2045267 : Blo 2043435 2045267 := bstep (se 1 (by rfl) ⟨1533950, by rfl⟩ : syracuseStep 2045267 = 3067901) B3067901
theorem B4601861 : Blo 2043435 4601861 := bbase (se 4 (by rfl) ⟨431424, by rfl⟩ : syracuseStep 4601861 = 862849) (by norm_num)
theorem B3067907 : Blo 2043435 3067907 := bstep (se 1 (by rfl) ⟨2300930, by rfl⟩ : syracuseStep 3067907 = 4601861) B4601861
theorem B2045271 : Blo 2043435 2045271 := bstep (se 1 (by rfl) ⟨1533953, by rfl⟩ : syracuseStep 2045271 = 3067907) B3067907
theorem B3882829 : Blo 2043435 3882829 := bbase (se 3 (by rfl) ⟨728030, by rfl⟩ : syracuseStep 3882829 = 1456061) (by norm_num)
theorem B5177105 : Blo 2043435 5177105 := bstep (se 2 (by rfl) ⟨1941414, by rfl⟩ : syracuseStep 5177105 = 3882829) B3882829
theorem B3451403 : Blo 2043435 3451403 := bstep (se 1 (by rfl) ⟨2588552, by rfl⟩ : syracuseStep 3451403 = 5177105) B5177105
theorem B2300935 : Blo 2043435 2300935 := bstep (se 1 (by rfl) ⟨1725701, by rfl⟩ : syracuseStep 2300935 = 3451403) B3451403
theorem B3067913 : Blo 2043435 3067913 := bstep (se 2 (by rfl) ⟨1150467, by rfl⟩ : syracuseStep 3067913 = 2300935) B2300935
theorem B2045275 : Blo 2043435 2045275 := bstep (se 1 (by rfl) ⟨1533956, by rfl⟩ : syracuseStep 2045275 = 3067913) B3067913
theorem B10354229 : Blo 2043435 10354229 := bbase (se 5 (by rfl) ⟨485354, by rfl⟩ : syracuseStep 10354229 = 970709) (by norm_num)
theorem B6902819 : Blo 2043435 6902819 := bstep (se 1 (by rfl) ⟨5177114, by rfl⟩ : syracuseStep 6902819 = 10354229) B10354229
theorem B4601879 : Blo 2043435 4601879 := bstep (se 1 (by rfl) ⟨3451409, by rfl⟩ : syracuseStep 4601879 = 6902819) B6902819
theorem B3067919 : Blo 2043435 3067919 := bstep (se 1 (by rfl) ⟨2300939, by rfl⟩ : syracuseStep 3067919 = 4601879) B4601879
theorem B2045279 : Blo 2043435 2045279 := bstep (se 1 (by rfl) ⟨1533959, by rfl⟩ : syracuseStep 2045279 = 3067919) B3067919
theorem B3067925 : Blo 2043435 3067925 := bbase (se 6 (by rfl) ⟨71904, by rfl⟩ : syracuseStep 3067925 = 143809) (by norm_num)
theorem B2045283 : Blo 2043435 2045283 := bstep (se 1 (by rfl) ⟨1533962, by rfl⟩ : syracuseStep 2045283 = 3067925) B3067925
theorem B9828469 : Blo 2043435 9828469 := bbase (se 5 (by rfl) ⟨460709, by rfl⟩ : syracuseStep 9828469 = 921419) (by norm_num)
theorem B13104625 : Blo 2043435 13104625 := bstep (se 2 (by rfl) ⟨4914234, by rfl⟩ : syracuseStep 13104625 = 9828469) B9828469
theorem B17472833 : Blo 2043435 17472833 := bstep (se 2 (by rfl) ⟨6552312, by rfl⟩ : syracuseStep 17472833 = 13104625) B13104625
theorem B11648555 : Blo 2043435 11648555 := bstep (se 1 (by rfl) ⟨8736416, by rfl⟩ : syracuseStep 11648555 = 17472833) B17472833
theorem B7765703 : Blo 2043435 7765703 := bstep (se 1 (by rfl) ⟨5824277, by rfl⟩ : syracuseStep 7765703 = 11648555) B11648555
theorem B5177135 : Blo 2043435 5177135 := bstep (se 1 (by rfl) ⟨3882851, by rfl⟩ : syracuseStep 5177135 = 7765703) B7765703
theorem B3451423 : Blo 2043435 3451423 := bstep (se 1 (by rfl) ⟨2588567, by rfl⟩ : syracuseStep 3451423 = 5177135) B5177135
theorem B4601897 : Blo 2043435 4601897 := bstep (se 2 (by rfl) ⟨1725711, by rfl⟩ : syracuseStep 4601897 = 3451423) B3451423
theorem B3067931 : Blo 2043435 3067931 := bstep (se 1 (by rfl) ⟨2300948, by rfl⟩ : syracuseStep 3067931 = 4601897) B4601897
theorem B2045287 : Blo 2043435 2045287 := bstep (se 1 (by rfl) ⟨1533965, by rfl⟩ : syracuseStep 2045287 = 3067931) B3067931
theorem B2300953 : Blo 2043435 2300953 := bbase (se 2 (by rfl) ⟨862857, by rfl⟩ : syracuseStep 2300953 = 1725715) (by norm_num)
theorem B3067937 : Blo 2043435 3067937 := bstep (se 2 (by rfl) ⟨1150476, by rfl⟩ : syracuseStep 3067937 = 2300953) B2300953
theorem B2045291 : Blo 2043435 2045291 := bstep (se 1 (by rfl) ⟨1533968, by rfl⟩ : syracuseStep 2045291 = 3067937) B3067937
theorem B7765733 : Blo 2043435 7765733 := bbase (se 4 (by rfl) ⟨728037, by rfl⟩ : syracuseStep 7765733 = 1456075) (by norm_num)
theorem B5177155 : Blo 2043435 5177155 := bstep (se 1 (by rfl) ⟨3882866, by rfl⟩ : syracuseStep 5177155 = 7765733) B7765733
theorem B6902873 : Blo 2043435 6902873 := bstep (se 2 (by rfl) ⟨2588577, by rfl⟩ : syracuseStep 6902873 = 5177155) B5177155
theorem B4601915 : Blo 2043435 4601915 := bstep (se 1 (by rfl) ⟨3451436, by rfl⟩ : syracuseStep 4601915 = 6902873) B6902873
theorem B3067943 : Blo 2043435 3067943 := bstep (se 1 (by rfl) ⟨2300957, by rfl⟩ : syracuseStep 3067943 = 4601915) B4601915
theorem B2045295 : Blo 2043435 2045295 := bstep (se 1 (by rfl) ⟨1533971, by rfl⟩ : syracuseStep 2045295 = 3067943) B3067943
theorem B3067949 : Blo 2043435 3067949 := bbase (se 3 (by rfl) ⟨575240, by rfl⟩ : syracuseStep 3067949 = 1150481) (by norm_num)
theorem B2045299 : Blo 2043435 2045299 := bstep (se 1 (by rfl) ⟨1533974, by rfl⟩ : syracuseStep 2045299 = 3067949) B3067949
theorem B4601933 : Blo 2043435 4601933 := bbase (se 3 (by rfl) ⟨862862, by rfl⟩ : syracuseStep 4601933 = 1725725) (by norm_num)
theorem B3067955 : Blo 2043435 3067955 := bstep (se 1 (by rfl) ⟨2300966, by rfl⟩ : syracuseStep 3067955 = 4601933) B4601933
theorem B2045303 : Blo 2043435 2045303 := bstep (se 1 (by rfl) ⟨1533977, by rfl⟩ : syracuseStep 2045303 = 3067955) B3067955
theorem B2588593 : Blo 2043435 2588593 := bbase (se 2 (by rfl) ⟨970722, by rfl⟩ : syracuseStep 2588593 = 1941445) (by norm_num)
theorem B3451457 : Blo 2043435 3451457 := bstep (se 2 (by rfl) ⟨1294296, by rfl⟩ : syracuseStep 3451457 = 2588593) B2588593
theorem B2300971 : Blo 2043435 2300971 := bstep (se 1 (by rfl) ⟨1725728, by rfl⟩ : syracuseStep 2300971 = 3451457) B3451457
theorem B3067961 : Blo 2043435 3067961 := bstep (se 2 (by rfl) ⟨1150485, by rfl⟩ : syracuseStep 3067961 = 2300971) B2300971
theorem B2045307 : Blo 2043435 2045307 := bstep (se 1 (by rfl) ⟨1533980, by rfl⟩ : syracuseStep 2045307 = 3067961) B3067961
theorem B6552389 : Blo 2043435 6552389 := bbase (se 4 (by rfl) ⟨614286, by rfl⟩ : syracuseStep 6552389 = 1228573) (by norm_num)
theorem B4368259 : Blo 2043435 4368259 := bstep (se 1 (by rfl) ⟨3276194, by rfl⟩ : syracuseStep 4368259 = 6552389) B6552389
theorem B23297381 : Blo 2043435 23297381 := bstep (se 4 (by rfl) ⟨2184129, by rfl⟩ : syracuseStep 23297381 = 4368259) B4368259
theorem B15531587 : Blo 2043435 15531587 := bstep (se 1 (by rfl) ⟨11648690, by rfl⟩ : syracuseStep 15531587 = 23297381) B23297381
theorem B10354391 : Blo 2043435 10354391 := bstep (se 1 (by rfl) ⟨7765793, by rfl⟩ : syracuseStep 10354391 = 15531587) B15531587
theorem B6902927 : Blo 2043435 6902927 := bstep (se 1 (by rfl) ⟨5177195, by rfl⟩ : syracuseStep 6902927 = 10354391) B10354391
theorem B4601951 : Blo 2043435 4601951 := bstep (se 1 (by rfl) ⟨3451463, by rfl⟩ : syracuseStep 4601951 = 6902927) B6902927
theorem B3067967 : Blo 2043435 3067967 := bstep (se 1 (by rfl) ⟨2300975, by rfl⟩ : syracuseStep 3067967 = 4601951) B4601951
theorem B2045311 : Blo 2043435 2045311 := bstep (se 1 (by rfl) ⟨1533983, by rfl⟩ : syracuseStep 2045311 = 3067967) B3067967
theorem B3067973 : Blo 2043435 3067973 := bbase (se 4 (by rfl) ⟨287622, by rfl⟩ : syracuseStep 3067973 = 575245) (by norm_num)
theorem B2045315 : Blo 2043435 2045315 := bstep (se 1 (by rfl) ⟨1533986, by rfl⟩ : syracuseStep 2045315 = 3067973) B3067973
theorem B3451477 : Blo 2043435 3451477 := bbase (se 8 (by rfl) ⟨20223, by rfl⟩ : syracuseStep 3451477 = 40447) (by norm_num)
theorem B4601969 : Blo 2043435 4601969 := bstep (se 2 (by rfl) ⟨1725738, by rfl⟩ : syracuseStep 4601969 = 3451477) B3451477
theorem B3067979 : Blo 2043435 3067979 := bstep (se 1 (by rfl) ⟨2300984, by rfl⟩ : syracuseStep 3067979 = 4601969) B4601969
theorem B2045319 : Blo 2043435 2045319 := bstep (se 1 (by rfl) ⟨1533989, by rfl⟩ : syracuseStep 2045319 = 3067979) B3067979
theorem B2300989 : Blo 2043435 2300989 := bbase (se 3 (by rfl) ⟨431435, by rfl⟩ : syracuseStep 2300989 = 862871) (by norm_num)
theorem B3067985 : Blo 2043435 3067985 := bstep (se 2 (by rfl) ⟨1150494, by rfl⟩ : syracuseStep 3067985 = 2300989) B2300989
theorem B2045323 : Blo 2043435 2045323 := bstep (se 1 (by rfl) ⟨1533992, by rfl⟩ : syracuseStep 2045323 = 3067985) B3067985
theorem B6902981 : Blo 2043435 6902981 := bbase (se 4 (by rfl) ⟨647154, by rfl⟩ : syracuseStep 6902981 = 1294309) (by norm_num)
theorem B4601987 : Blo 2043435 4601987 := bstep (se 1 (by rfl) ⟨3451490, by rfl⟩ : syracuseStep 4601987 = 6902981) B6902981
theorem B3067991 : Blo 2043435 3067991 := bstep (se 1 (by rfl) ⟨2300993, by rfl⟩ : syracuseStep 3067991 = 4601987) B4601987
theorem B2045327 : Blo 2043435 2045327 := bstep (se 1 (by rfl) ⟨1533995, by rfl⟩ : syracuseStep 2045327 = 3067991) B3067991
theorem B3067997 : Blo 2043435 3067997 := bbase (se 3 (by rfl) ⟨575249, by rfl⟩ : syracuseStep 3067997 = 1150499) (by norm_num)
theorem B2045331 : Blo 2043435 2045331 := bstep (se 1 (by rfl) ⟨1533998, by rfl⟩ : syracuseStep 2045331 = 3067997) B3067997
theorem B4602005 : Blo 2043435 4602005 := bbase (se 6 (by rfl) ⟨107859, by rfl⟩ : syracuseStep 4602005 = 215719) (by norm_num)
theorem B3068003 : Blo 2043435 3068003 := bstep (se 1 (by rfl) ⟨2301002, by rfl⟩ : syracuseStep 3068003 = 4602005) B4602005
theorem B2045335 : Blo 2043435 2045335 := bstep (se 1 (by rfl) ⟨1534001, by rfl⟩ : syracuseStep 2045335 = 3068003) B3068003
theorem B2912213 : Blo 2043435 2912213 := bbase (se 7 (by rfl) ⟨34127, by rfl⟩ : syracuseStep 2912213 = 68255) (by norm_num)
theorem B7765901 : Blo 2043435 7765901 := bstep (se 3 (by rfl) ⟨1456106, by rfl⟩ : syracuseStep 7765901 = 2912213) B2912213
theorem B5177267 : Blo 2043435 5177267 := bstep (se 1 (by rfl) ⟨3882950, by rfl⟩ : syracuseStep 5177267 = 7765901) B7765901
theorem B3451511 : Blo 2043435 3451511 := bstep (se 1 (by rfl) ⟨2588633, by rfl⟩ : syracuseStep 3451511 = 5177267) B5177267
theorem B2301007 : Blo 2043435 2301007 := bstep (se 1 (by rfl) ⟨1725755, by rfl⟩ : syracuseStep 2301007 = 3451511) B3451511
theorem B3068009 : Blo 2043435 3068009 := bstep (se 2 (by rfl) ⟨1150503, by rfl⟩ : syracuseStep 3068009 = 2301007) B2301007
theorem B2045339 : Blo 2043435 2045339 := bstep (se 1 (by rfl) ⟨1534004, by rfl⟩ : syracuseStep 2045339 = 3068009) B3068009
theorem B6219749 : Blo 2043435 6219749 := bbase (se 4 (by rfl) ⟨583101, by rfl⟩ : syracuseStep 6219749 = 1166203) (by norm_num)
theorem B4146499 : Blo 2043435 4146499 := bstep (se 1 (by rfl) ⟨3109874, by rfl⟩ : syracuseStep 4146499 = 6219749) B6219749
theorem B5528665 : Blo 2043435 5528665 := bstep (se 2 (by rfl) ⟨2073249, by rfl⟩ : syracuseStep 5528665 = 4146499) B4146499
theorem B29486213 : Blo 2043435 29486213 := bstep (se 4 (by rfl) ⟨2764332, by rfl⟩ : syracuseStep 29486213 = 5528665) B5528665
theorem B19657475 : Blo 2043435 19657475 := bstep (se 1 (by rfl) ⟨14743106, by rfl⟩ : syracuseStep 19657475 = 29486213) B29486213
theorem B13104983 : Blo 2043435 13104983 := bstep (se 1 (by rfl) ⟨9828737, by rfl⟩ : syracuseStep 13104983 = 19657475) B19657475
theorem B8736655 : Blo 2043435 8736655 := bstep (se 1 (by rfl) ⟨6552491, by rfl⟩ : syracuseStep 8736655 = 13104983) B13104983
theorem B11648873 : Blo 2043435 11648873 := bstep (se 2 (by rfl) ⟨4368327, by rfl⟩ : syracuseStep 11648873 = 8736655) B8736655
theorem B7765915 : Blo 2043435 7765915 := bstep (se 1 (by rfl) ⟨5824436, by rfl⟩ : syracuseStep 7765915 = 11648873) B11648873
theorem B10354553 : Blo 2043435 10354553 := bstep (se 2 (by rfl) ⟨3882957, by rfl⟩ : syracuseStep 10354553 = 7765915) B7765915
theorem B6903035 : Blo 2043435 6903035 := bstep (se 1 (by rfl) ⟨5177276, by rfl⟩ : syracuseStep 6903035 = 10354553) B10354553
theorem B4602023 : Blo 2043435 4602023 := bstep (se 1 (by rfl) ⟨3451517, by rfl⟩ : syracuseStep 4602023 = 6903035) B6903035
theorem B3068015 : Blo 2043435 3068015 := bstep (se 1 (by rfl) ⟨2301011, by rfl⟩ : syracuseStep 3068015 = 4602023) B4602023
theorem B2045343 : Blo 2043435 2045343 := bstep (se 1 (by rfl) ⟨1534007, by rfl⟩ : syracuseStep 2045343 = 3068015) B3068015
theorem B3068021 : Blo 2043435 3068021 := bbase (se 5 (by rfl) ⟨143813, by rfl⟩ : syracuseStep 3068021 = 287627) (by norm_num)
theorem B2045347 : Blo 2043435 2045347 := bstep (se 1 (by rfl) ⟨1534010, by rfl⟩ : syracuseStep 2045347 = 3068021) B3068021
theorem B3882973 : Blo 2043435 3882973 := bbase (se 3 (by rfl) ⟨728057, by rfl⟩ : syracuseStep 3882973 = 1456115) (by norm_num)
theorem B5177297 : Blo 2043435 5177297 := bstep (se 2 (by rfl) ⟨1941486, by rfl⟩ : syracuseStep 5177297 = 3882973) B3882973
theorem B3451531 : Blo 2043435 3451531 := bstep (se 1 (by rfl) ⟨2588648, by rfl⟩ : syracuseStep 3451531 = 5177297) B5177297
theorem B4602041 : Blo 2043435 4602041 := bstep (se 2 (by rfl) ⟨1725765, by rfl⟩ : syracuseStep 4602041 = 3451531) B3451531
theorem B3068027 : Blo 2043435 3068027 := bstep (se 1 (by rfl) ⟨2301020, by rfl⟩ : syracuseStep 3068027 = 4602041) B4602041
theorem B2045351 : Blo 2043435 2045351 := bstep (se 1 (by rfl) ⟨1534013, by rfl⟩ : syracuseStep 2045351 = 3068027) B3068027
theorem B2301025 : Blo 2043435 2301025 := bbase (se 2 (by rfl) ⟨862884, by rfl⟩ : syracuseStep 2301025 = 1725769) (by norm_num)
theorem B3068033 : Blo 2043435 3068033 := bstep (se 2 (by rfl) ⟨1150512, by rfl⟩ : syracuseStep 3068033 = 2301025) B2301025
theorem B2045355 : Blo 2043435 2045355 := bstep (se 1 (by rfl) ⟨1534016, by rfl⟩ : syracuseStep 2045355 = 3068033) B3068033
theorem B5177317 : Blo 2043435 5177317 := bbase (se 4 (by rfl) ⟨485373, by rfl⟩ : syracuseStep 5177317 = 970747) (by norm_num)
theorem B6903089 : Blo 2043435 6903089 := bstep (se 2 (by rfl) ⟨2588658, by rfl⟩ : syracuseStep 6903089 = 5177317) B5177317
theorem B4602059 : Blo 2043435 4602059 := bstep (se 1 (by rfl) ⟨3451544, by rfl⟩ : syracuseStep 4602059 = 6903089) B6903089
theorem B3068039 : Blo 2043435 3068039 := bstep (se 1 (by rfl) ⟨2301029, by rfl⟩ : syracuseStep 3068039 = 4602059) B4602059
theorem B2045359 : Blo 2043435 2045359 := bstep (se 1 (by rfl) ⟨1534019, by rfl⟩ : syracuseStep 2045359 = 3068039) B3068039
theorem B3068045 : Blo 2043435 3068045 := bbase (se 3 (by rfl) ⟨575258, by rfl⟩ : syracuseStep 3068045 = 1150517) (by norm_num)
theorem B2045363 : Blo 2043435 2045363 := bstep (se 1 (by rfl) ⟨1534022, by rfl⟩ : syracuseStep 2045363 = 3068045) B3068045
theorem B4602077 : Blo 2043435 4602077 := bbase (se 3 (by rfl) ⟨862889, by rfl⟩ : syracuseStep 4602077 = 1725779) (by norm_num)
theorem B3068051 : Blo 2043435 3068051 := bstep (se 1 (by rfl) ⟨2301038, by rfl⟩ : syracuseStep 3068051 = 4602077) B4602077
theorem B2045367 : Blo 2043435 2045367 := bstep (se 1 (by rfl) ⟨1534025, by rfl⟩ : syracuseStep 2045367 = 3068051) B3068051
theorem B3451565 : Blo 2043435 3451565 := bbase (se 3 (by rfl) ⟨647168, by rfl⟩ : syracuseStep 3451565 = 1294337) (by norm_num)
theorem B2301043 : Blo 2043435 2301043 := bstep (se 1 (by rfl) ⟨1725782, by rfl⟩ : syracuseStep 2301043 = 3451565) B3451565
theorem B3068057 : Blo 2043435 3068057 := bstep (se 2 (by rfl) ⟨1150521, by rfl⟩ : syracuseStep 3068057 = 2301043) B2301043
theorem B2045371 : Blo 2043435 2045371 := bstep (se 1 (by rfl) ⟨1534028, by rfl⟩ : syracuseStep 2045371 = 3068057) B3068057
theorem B5049461 : Blo 2043435 5049461 := bbase (se 5 (by rfl) ⟨236693, by rfl⟩ : syracuseStep 5049461 = 473387) (by norm_num)
theorem B3366307 : Blo 2043435 3366307 := bstep (se 1 (by rfl) ⟨2524730, by rfl⟩ : syracuseStep 3366307 = 5049461) B5049461
theorem B4488409 : Blo 2043435 4488409 := bstep (se 2 (by rfl) ⟨1683153, by rfl⟩ : syracuseStep 4488409 = 3366307) B3366307
theorem B5984545 : Blo 2043435 5984545 := bstep (se 2 (by rfl) ⟨2244204, by rfl⟩ : syracuseStep 5984545 = 4488409) B4488409
theorem B7979393 : Blo 2043435 7979393 := bstep (se 2 (by rfl) ⟨2992272, by rfl⟩ : syracuseStep 7979393 = 5984545) B5984545
theorem B5319595 : Blo 2043435 5319595 := bstep (se 1 (by rfl) ⟨3989696, by rfl⟩ : syracuseStep 5319595 = 7979393) B7979393
theorem B7092793 : Blo 2043435 7092793 := bstep (se 2 (by rfl) ⟨2659797, by rfl⟩ : syracuseStep 7092793 = 5319595) B5319595
theorem B9457057 : Blo 2043435 9457057 := bstep (se 2 (by rfl) ⟨3546396, by rfl⟩ : syracuseStep 9457057 = 7092793) B7092793
theorem B12609409 : Blo 2043435 12609409 := bstep (se 2 (by rfl) ⟨4728528, by rfl⟩ : syracuseStep 12609409 = 9457057) B9457057
theorem B16812545 : Blo 2043435 16812545 := bstep (se 2 (by rfl) ⟨6304704, by rfl⟩ : syracuseStep 16812545 = 12609409) B12609409
theorem B179333813 : Blo 2043435 179333813 := bstep (se 5 (by rfl) ⟨8406272, by rfl⟩ : syracuseStep 179333813 = 16812545) B16812545
theorem B119555875 : Blo 2043435 119555875 := bstep (se 1 (by rfl) ⟨89666906, by rfl⟩ : syracuseStep 119555875 = 179333813) B179333813
theorem B159407833 : Blo 2043435 159407833 := bstep (se 2 (by rfl) ⟨59777937, by rfl⟩ : syracuseStep 159407833 = 119555875) B119555875
theorem B212543777 : Blo 2043435 212543777 := bstep (se 2 (by rfl) ⟨79703916, by rfl⟩ : syracuseStep 212543777 = 159407833) B159407833
theorem B141695851 : Blo 2043435 141695851 := bstep (se 1 (by rfl) ⟨106271888, by rfl⟩ : syracuseStep 141695851 = 212543777) B212543777
theorem B188927801 : Blo 2043435 188927801 := bstep (se 2 (by rfl) ⟨70847925, by rfl⟩ : syracuseStep 188927801 = 141695851) B141695851
theorem B125951867 : Blo 2043435 125951867 := bstep (se 1 (by rfl) ⟨94463900, by rfl⟩ : syracuseStep 125951867 = 188927801) B188927801
theorem B83967911 : Blo 2043435 83967911 := bstep (se 1 (by rfl) ⟨62975933, by rfl⟩ : syracuseStep 83967911 = 125951867) B125951867
theorem B55978607 : Blo 2043435 55978607 := bstep (se 1 (by rfl) ⟨41983955, by rfl⟩ : syracuseStep 55978607 = 83967911) B83967911
theorem B37319071 : Blo 2043435 37319071 := bstep (se 1 (by rfl) ⟨27989303, by rfl⟩ : syracuseStep 37319071 = 55978607) B55978607
theorem B49758761 : Blo 2043435 49758761 := bstep (se 2 (by rfl) ⟨18659535, by rfl⟩ : syracuseStep 49758761 = 37319071) B37319071
theorem B33172507 : Blo 2043435 33172507 := bstep (se 1 (by rfl) ⟨24879380, by rfl⟩ : syracuseStep 33172507 = 49758761) B49758761
theorem B44230009 : Blo 2043435 44230009 := bstep (se 2 (by rfl) ⟨16586253, by rfl⟩ : syracuseStep 44230009 = 33172507) B33172507
theorem B58973345 : Blo 2043435 58973345 := bstep (se 2 (by rfl) ⟨22115004, by rfl⟩ : syracuseStep 58973345 = 44230009) B44230009
theorem B39315563 : Blo 2043435 39315563 := bstep (se 1 (by rfl) ⟨29486672, by rfl⟩ : syracuseStep 39315563 = 58973345) B58973345
theorem B26210375 : Blo 2043435 26210375 := bstep (se 1 (by rfl) ⟨19657781, by rfl⟩ : syracuseStep 26210375 = 39315563) B39315563
theorem B17473583 : Blo 2043435 17473583 := bstep (se 1 (by rfl) ⟨13105187, by rfl⟩ : syracuseStep 17473583 = 26210375) B26210375
theorem B11649055 : Blo 2043435 11649055 := bstep (se 1 (by rfl) ⟨8736791, by rfl⟩ : syracuseStep 11649055 = 17473583) B17473583
theorem B15532073 : Blo 2043435 15532073 := bstep (se 2 (by rfl) ⟨5824527, by rfl⟩ : syracuseStep 15532073 = 11649055) B11649055
theorem B10354715 : Blo 2043435 10354715 := bstep (se 1 (by rfl) ⟨7766036, by rfl⟩ : syracuseStep 10354715 = 15532073) B15532073
theorem B6903143 : Blo 2043435 6903143 := bstep (se 1 (by rfl) ⟨5177357, by rfl⟩ : syracuseStep 6903143 = 10354715) B10354715
theorem B4602095 : Blo 2043435 4602095 := bstep (se 1 (by rfl) ⟨3451571, by rfl⟩ : syracuseStep 4602095 = 6903143) B6903143
theorem B3068063 : Blo 2043435 3068063 := bstep (se 1 (by rfl) ⟨2301047, by rfl⟩ : syracuseStep 3068063 = 4602095) B4602095
theorem B2045375 : Blo 2043435 2045375 := bstep (se 1 (by rfl) ⟨1534031, by rfl⟩ : syracuseStep 2045375 = 3068063) B3068063
theorem B3068069 : Blo 2043435 3068069 := bbase (se 4 (by rfl) ⟨287631, by rfl⟩ : syracuseStep 3068069 = 575263) (by norm_num)
theorem B2045379 : Blo 2043435 2045379 := bstep (se 1 (by rfl) ⟨1534034, by rfl⟩ : syracuseStep 2045379 = 3068069) B3068069
theorem B2588689 : Blo 2043435 2588689 := bbase (se 2 (by rfl) ⟨970758, by rfl⟩ : syracuseStep 2588689 = 1941517) (by norm_num)
theorem B3451585 : Blo 2043435 3451585 := bstep (se 2 (by rfl) ⟨1294344, by rfl⟩ : syracuseStep 3451585 = 2588689) B2588689
theorem B4602113 : Blo 2043435 4602113 := bstep (se 2 (by rfl) ⟨1725792, by rfl⟩ : syracuseStep 4602113 = 3451585) B3451585
theorem B3068075 : Blo 2043435 3068075 := bstep (se 1 (by rfl) ⟨2301056, by rfl⟩ : syracuseStep 3068075 = 4602113) B4602113
theorem B2045383 : Blo 2043435 2045383 := bstep (se 1 (by rfl) ⟨1534037, by rfl⟩ : syracuseStep 2045383 = 3068075) B3068075
theorem B2301061 : Blo 2043435 2301061 := bbase (se 4 (by rfl) ⟨215724, by rfl⟩ : syracuseStep 2301061 = 431449) (by norm_num)
theorem B3068081 : Blo 2043435 3068081 := bstep (se 2 (by rfl) ⟨1150530, by rfl⟩ : syracuseStep 3068081 = 2301061) B2301061
theorem B2045387 : Blo 2043435 2045387 := bstep (se 1 (by rfl) ⟨1534040, by rfl⟩ : syracuseStep 2045387 = 3068081) B3068081
theorem B9329845 : Blo 2043435 9329845 := bbase (se 5 (by rfl) ⟨437336, by rfl⟩ : syracuseStep 9329845 = 874673) (by norm_num)
theorem B12439793 : Blo 2043435 12439793 := bstep (se 2 (by rfl) ⟨4664922, by rfl⟩ : syracuseStep 12439793 = 9329845) B9329845
theorem B8293195 : Blo 2043435 8293195 := bstep (se 1 (by rfl) ⟨6219896, by rfl⟩ : syracuseStep 8293195 = 12439793) B12439793
theorem B11057593 : Blo 2043435 11057593 := bstep (se 2 (by rfl) ⟨4146597, by rfl⟩ : syracuseStep 11057593 = 8293195) B8293195
theorem B14743457 : Blo 2043435 14743457 := bstep (se 2 (by rfl) ⟨5528796, by rfl⟩ : syracuseStep 14743457 = 11057593) B11057593
theorem B9828971 : Blo 2043435 9828971 := bstep (se 1 (by rfl) ⟨7371728, by rfl⟩ : syracuseStep 9828971 = 14743457) B14743457
theorem B6552647 : Blo 2043435 6552647 := bstep (se 1 (by rfl) ⟨4914485, by rfl⟩ : syracuseStep 6552647 = 9828971) B9828971
theorem B4368431 : Blo 2043435 4368431 := bstep (se 1 (by rfl) ⟨3276323, by rfl⟩ : syracuseStep 4368431 = 6552647) B6552647
theorem B2912287 : Blo 2043435 2912287 := bstep (se 1 (by rfl) ⟨2184215, by rfl⟩ : syracuseStep 2912287 = 4368431) B4368431
theorem B3883049 : Blo 2043435 3883049 := bstep (se 2 (by rfl) ⟨1456143, by rfl⟩ : syracuseStep 3883049 = 2912287) B2912287
theorem B2588699 : Blo 2043435 2588699 := bstep (se 1 (by rfl) ⟨1941524, by rfl⟩ : syracuseStep 2588699 = 3883049) B3883049
theorem B6903197 : Blo 2043435 6903197 := bstep (se 3 (by rfl) ⟨1294349, by rfl⟩ : syracuseStep 6903197 = 2588699) B2588699
theorem B4602131 : Blo 2043435 4602131 := bstep (se 1 (by rfl) ⟨3451598, by rfl⟩ : syracuseStep 4602131 = 6903197) B6903197
theorem B3068087 : Blo 2043435 3068087 := bstep (se 1 (by rfl) ⟨2301065, by rfl⟩ : syracuseStep 3068087 = 4602131) B4602131
theorem B2045391 : Blo 2043435 2045391 := bstep (se 1 (by rfl) ⟨1534043, by rfl⟩ : syracuseStep 2045391 = 3068087) B3068087
theorem B3068093 : Blo 2043435 3068093 := bbase (se 3 (by rfl) ⟨575267, by rfl⟩ : syracuseStep 3068093 = 1150535) (by norm_num)
theorem B2045395 : Blo 2043435 2045395 := bstep (se 1 (by rfl) ⟨1534046, by rfl⟩ : syracuseStep 2045395 = 3068093) B3068093
theorem B4602149 : Blo 2043435 4602149 := bbase (se 4 (by rfl) ⟨431451, by rfl⟩ : syracuseStep 4602149 = 862903) (by norm_num)
theorem B3068099 : Blo 2043435 3068099 := bstep (se 1 (by rfl) ⟨2301074, by rfl⟩ : syracuseStep 3068099 = 4602149) B4602149
theorem B2045399 : Blo 2043435 2045399 := bstep (se 1 (by rfl) ⟨1534049, by rfl⟩ : syracuseStep 2045399 = 3068099) B3068099
theorem B5177429 : Blo 2043435 5177429 := bbase (se 8 (by rfl) ⟨30336, by rfl⟩ : syracuseStep 5177429 = 60673) (by norm_num)
theorem B3451619 : Blo 2043435 3451619 := bstep (se 1 (by rfl) ⟨2588714, by rfl⟩ : syracuseStep 3451619 = 5177429) B5177429
theorem B2301079 : Blo 2043435 2301079 := bstep (se 1 (by rfl) ⟨1725809, by rfl⟩ : syracuseStep 2301079 = 3451619) B3451619
theorem B3068105 : Blo 2043435 3068105 := bstep (se 2 (by rfl) ⟨1150539, by rfl⟩ : syracuseStep 3068105 = 2301079) B2301079
theorem B2045403 : Blo 2043435 2045403 := bstep (se 1 (by rfl) ⟨1534052, by rfl⟩ : syracuseStep 2045403 = 3068105) B3068105
theorem B6642101 : Blo 2043435 6642101 := bbase (se 5 (by rfl) ⟨311348, by rfl⟩ : syracuseStep 6642101 = 622697) (by norm_num)
theorem B17712269 : Blo 2043435 17712269 := bstep (se 3 (by rfl) ⟨3321050, by rfl⟩ : syracuseStep 17712269 = 6642101) B6642101
theorem B11808179 : Blo 2043435 11808179 := bstep (se 1 (by rfl) ⟨8856134, by rfl⟩ : syracuseStep 11808179 = 17712269) B17712269
theorem B7872119 : Blo 2043435 7872119 := bstep (se 1 (by rfl) ⟨5904089, by rfl⟩ : syracuseStep 7872119 = 11808179) B11808179
theorem B5248079 : Blo 2043435 5248079 := bstep (se 1 (by rfl) ⟨3936059, by rfl⟩ : syracuseStep 5248079 = 7872119) B7872119
theorem B3498719 : Blo 2043435 3498719 := bstep (se 1 (by rfl) ⟨2624039, by rfl⟩ : syracuseStep 3498719 = 5248079) B5248079
theorem B9329917 : Blo 2043435 9329917 := bstep (se 3 (by rfl) ⟨1749359, by rfl⟩ : syracuseStep 9329917 = 3498719) B3498719
theorem B12439889 : Blo 2043435 12439889 := bstep (se 2 (by rfl) ⟨4664958, by rfl⟩ : syracuseStep 12439889 = 9329917) B9329917
theorem B8293259 : Blo 2043435 8293259 := bstep (se 1 (by rfl) ⟨6219944, by rfl⟩ : syracuseStep 8293259 = 12439889) B12439889
theorem B5528839 : Blo 2043435 5528839 := bstep (se 1 (by rfl) ⟨4146629, by rfl⟩ : syracuseStep 5528839 = 8293259) B8293259
theorem B7371785 : Blo 2043435 7371785 := bstep (se 2 (by rfl) ⟨2764419, by rfl⟩ : syracuseStep 7371785 = 5528839) B5528839
theorem B4914523 : Blo 2043435 4914523 := bstep (se 1 (by rfl) ⟨3685892, by rfl⟩ : syracuseStep 4914523 = 7371785) B7371785
theorem B6552697 : Blo 2043435 6552697 := bstep (se 2 (by rfl) ⟨2457261, by rfl⟩ : syracuseStep 6552697 = 4914523) B4914523
theorem B8736929 : Blo 2043435 8736929 := bstep (se 2 (by rfl) ⟨3276348, by rfl⟩ : syracuseStep 8736929 = 6552697) B6552697
theorem B5824619 : Blo 2043435 5824619 := bstep (se 1 (by rfl) ⟨4368464, by rfl⟩ : syracuseStep 5824619 = 8736929) B8736929
theorem B3883079 : Blo 2043435 3883079 := bstep (se 1 (by rfl) ⟨2912309, by rfl⟩ : syracuseStep 3883079 = 5824619) B5824619
theorem B10354877 : Blo 2043435 10354877 := bstep (se 3 (by rfl) ⟨1941539, by rfl⟩ : syracuseStep 10354877 = 3883079) B3883079
theorem B6903251 : Blo 2043435 6903251 := bstep (se 1 (by rfl) ⟨5177438, by rfl⟩ : syracuseStep 6903251 = 10354877) B10354877
theorem B4602167 : Blo 2043435 4602167 := bstep (se 1 (by rfl) ⟨3451625, by rfl⟩ : syracuseStep 4602167 = 6903251) B6903251
theorem B3068111 : Blo 2043435 3068111 := bstep (se 1 (by rfl) ⟨2301083, by rfl⟩ : syracuseStep 3068111 = 4602167) B4602167
theorem B2045407 : Blo 2043435 2045407 := bstep (se 1 (by rfl) ⟨1534055, by rfl⟩ : syracuseStep 2045407 = 3068111) B3068111
theorem B3068117 : Blo 2043435 3068117 := bbase (se 7 (by rfl) ⟨35954, by rfl⟩ : syracuseStep 3068117 = 71909) (by norm_num)
theorem B2045411 : Blo 2043435 2045411 := bstep (se 1 (by rfl) ⟨1534058, by rfl⟩ : syracuseStep 2045411 = 3068117) B3068117
theorem B2184241 : Blo 2043435 2184241 := bbase (se 2 (by rfl) ⟨819090, by rfl⟩ : syracuseStep 2184241 = 1638181) (by norm_num)
theorem B2912321 : Blo 2043435 2912321 := bstep (se 2 (by rfl) ⟨1092120, by rfl⟩ : syracuseStep 2912321 = 2184241) B2184241
theorem B7766189 : Blo 2043435 7766189 := bstep (se 3 (by rfl) ⟨1456160, by rfl⟩ : syracuseStep 7766189 = 2912321) B2912321
theorem B5177459 : Blo 2043435 5177459 := bstep (se 1 (by rfl) ⟨3883094, by rfl⟩ : syracuseStep 5177459 = 7766189) B7766189
theorem B3451639 : Blo 2043435 3451639 := bstep (se 1 (by rfl) ⟨2588729, by rfl⟩ : syracuseStep 3451639 = 5177459) B5177459
theorem B4602185 : Blo 2043435 4602185 := bstep (se 2 (by rfl) ⟨1725819, by rfl⟩ : syracuseStep 4602185 = 3451639) B3451639
theorem B3068123 : Blo 2043435 3068123 := bstep (se 1 (by rfl) ⟨2301092, by rfl⟩ : syracuseStep 3068123 = 4602185) B4602185
theorem B2045415 : Blo 2043435 2045415 := bstep (se 1 (by rfl) ⟨1534061, by rfl⟩ : syracuseStep 2045415 = 3068123) B3068123
theorem B2301097 : Blo 2043435 2301097 := bbase (se 2 (by rfl) ⟨862911, by rfl⟩ : syracuseStep 2301097 = 1725823) (by norm_num)
theorem B3068129 : Blo 2043435 3068129 := bstep (se 2 (by rfl) ⟨1150548, by rfl⟩ : syracuseStep 3068129 = 2301097) B2301097
theorem B2045419 : Blo 2043435 2045419 := bstep (se 1 (by rfl) ⟨1534064, by rfl⟩ : syracuseStep 2045419 = 3068129) B3068129
theorem B8736997 : Blo 2043435 8736997 := bbase (se 4 (by rfl) ⟨819093, by rfl⟩ : syracuseStep 8736997 = 1638187) (by norm_num)
theorem B11649329 : Blo 2043435 11649329 := bstep (se 2 (by rfl) ⟨4368498, by rfl⟩ : syracuseStep 11649329 = 8736997) B8736997
theorem B7766219 : Blo 2043435 7766219 := bstep (se 1 (by rfl) ⟨5824664, by rfl⟩ : syracuseStep 7766219 = 11649329) B11649329
theorem B5177479 : Blo 2043435 5177479 := bstep (se 1 (by rfl) ⟨3883109, by rfl⟩ : syracuseStep 5177479 = 7766219) B7766219
theorem B6903305 : Blo 2043435 6903305 := bstep (se 2 (by rfl) ⟨2588739, by rfl⟩ : syracuseStep 6903305 = 5177479) B5177479
theorem B4602203 : Blo 2043435 4602203 := bstep (se 1 (by rfl) ⟨3451652, by rfl⟩ : syracuseStep 4602203 = 6903305) B6903305
theorem B3068135 : Blo 2043435 3068135 := bstep (se 1 (by rfl) ⟨2301101, by rfl⟩ : syracuseStep 3068135 = 4602203) B4602203
theorem B2045423 : Blo 2043435 2045423 := bstep (se 1 (by rfl) ⟨1534067, by rfl⟩ : syracuseStep 2045423 = 3068135) B3068135
theorem B3068141 : Blo 2043435 3068141 := bbase (se 3 (by rfl) ⟨575276, by rfl⟩ : syracuseStep 3068141 = 1150553) (by norm_num)
theorem B2045427 : Blo 2043435 2045427 := bstep (se 1 (by rfl) ⟨1534070, by rfl⟩ : syracuseStep 2045427 = 3068141) B3068141
theorem B4602221 : Blo 2043435 4602221 := bbase (se 3 (by rfl) ⟨862916, by rfl⟩ : syracuseStep 4602221 = 1725833) (by norm_num)
theorem B3068147 : Blo 2043435 3068147 := bstep (se 1 (by rfl) ⟨2301110, by rfl⟩ : syracuseStep 3068147 = 4602221) B4602221
theorem B2045431 : Blo 2043435 2045431 := bstep (se 1 (by rfl) ⟨1534073, by rfl⟩ : syracuseStep 2045431 = 3068147) B3068147
theorem B3883133 : Blo 2043435 3883133 := bbase (se 3 (by rfl) ⟨728087, by rfl⟩ : syracuseStep 3883133 = 1456175) (by norm_num)
theorem B2588755 : Blo 2043435 2588755 := bstep (se 1 (by rfl) ⟨1941566, by rfl⟩ : syracuseStep 2588755 = 3883133) B3883133
theorem B3451673 : Blo 2043435 3451673 := bstep (se 2 (by rfl) ⟨1294377, by rfl⟩ : syracuseStep 3451673 = 2588755) B2588755
theorem B2301115 : Blo 2043435 2301115 := bstep (se 1 (by rfl) ⟨1725836, by rfl⟩ : syracuseStep 2301115 = 3451673) B3451673
theorem B3068153 : Blo 2043435 3068153 := bstep (se 2 (by rfl) ⟨1150557, by rfl⟩ : syracuseStep 3068153 = 2301115) B2301115
theorem B2045435 : Blo 2043435 2045435 := bstep (se 1 (by rfl) ⟨1534076, by rfl⟩ : syracuseStep 2045435 = 3068153) B3068153
theorem C0 (j : ℕ) (h1 : 510858 ≤ j) (h2 : j ≤ 511358) : Blo 2043435 (4 * j + 3) := by
  interval_cases j
  · exact B2043435
  · exact B2043439
  · exact B2043443
  · exact B2043447
  · exact B2043451
  · exact B2043455
  · exact B2043459
  · exact B2043463
  · exact B2043467
  · exact B2043471
  · exact B2043475
  · exact B2043479
  · exact B2043483
  · exact B2043487
  · exact B2043491
  · exact B2043495
  · exact B2043499
  · exact B2043503
  · exact B2043507
  · exact B2043511
  · exact B2043515
  · exact B2043519
  · exact B2043523
  · exact B2043527
  · exact B2043531
  · exact B2043535
  · exact B2043539
  · exact B2043543
  · exact B2043547
  · exact B2043551
  · exact B2043555
  · exact B2043559
  · exact B2043563
  · exact B2043567
  · exact B2043571
  · exact B2043575
  · exact B2043579
  · exact B2043583
  · exact B2043587
  · exact B2043591
  · exact B2043595
  · exact B2043599
  · exact B2043603
  · exact B2043607
  · exact B2043611
  · exact B2043615
  · exact B2043619
  · exact B2043623
  · exact B2043627
  · exact B2043631
  · exact B2043635
  · exact B2043639
  · exact B2043643
  · exact B2043647
  · exact B2043651
  · exact B2043655
  · exact B2043659
  · exact B2043663
  · exact B2043667
  · exact B2043671
  · exact B2043675
  · exact B2043679
  · exact B2043683
  · exact B2043687
  · exact B2043691
  · exact B2043695
  · exact B2043699
  · exact B2043703
  · exact B2043707
  · exact B2043711
  · exact B2043715
  · exact B2043719
  · exact B2043723
  · exact B2043727
  · exact B2043731
  · exact B2043735
  · exact B2043739
  · exact B2043743
  · exact B2043747
  · exact B2043751
  · exact B2043755
  · exact B2043759
  · exact B2043763
  · exact B2043767
  · exact B2043771
  · exact B2043775
  · exact B2043779
  · exact B2043783
  · exact B2043787
  · exact B2043791
  · exact B2043795
  · exact B2043799
  · exact B2043803
  · exact B2043807
  · exact B2043811
  · exact B2043815
  · exact B2043819
  · exact B2043823
  · exact B2043827
  · exact B2043831
  · exact B2043835
  · exact B2043839
  · exact B2043843
  · exact B2043847
  · exact B2043851
  · exact B2043855
  · exact B2043859
  · exact B2043863
  · exact B2043867
  · exact B2043871
  · exact B2043875
  · exact B2043879
  · exact B2043883
  · exact B2043887
  · exact B2043891
  · exact B2043895
  · exact B2043899
  · exact B2043903
  · exact B2043907
  · exact B2043911
  · exact B2043915
  · exact B2043919
  · exact B2043923
  · exact B2043927
  · exact B2043931
  · exact B2043935
  · exact B2043939
  · exact B2043943
  · exact B2043947
  · exact B2043951
  · exact B2043955
  · exact B2043959
  · exact B2043963
  · exact B2043967
  · exact B2043971
  · exact B2043975
  · exact B2043979
  · exact B2043983
  · exact B2043987
  · exact B2043991
  · exact B2043995
  · exact B2043999
  · exact B2044003
  · exact B2044007
  · exact B2044011
  · exact B2044015
  · exact B2044019
  · exact B2044023
  · exact B2044027
  · exact B2044031
  · exact B2044035
  · exact B2044039
  · exact B2044043
  · exact B2044047
  · exact B2044051
  · exact B2044055
  · exact B2044059
  · exact B2044063
  · exact B2044067
  · exact B2044071
  · exact B2044075
  · exact B2044079
  · exact B2044083
  · exact B2044087
  · exact B2044091
  · exact B2044095
  · exact B2044099
  · exact B2044103
  · exact B2044107
  · exact B2044111
  · exact B2044115
  · exact B2044119
  · exact B2044123
  · exact B2044127
  · exact B2044131
  · exact B2044135
  · exact B2044139
  · exact B2044143
  · exact B2044147
  · exact B2044151
  · exact B2044155
  · exact B2044159
  · exact B2044163
  · exact B2044167
  · exact B2044171
  · exact B2044175
  · exact B2044179
  · exact B2044183
  · exact B2044187
  · exact B2044191
  · exact B2044195
  · exact B2044199
  · exact B2044203
  · exact B2044207
  · exact B2044211
  · exact B2044215
  · exact B2044219
  · exact B2044223
  · exact B2044227
  · exact B2044231
  · exact B2044235
  · exact B2044239
  · exact B2044243
  · exact B2044247
  · exact B2044251
  · exact B2044255
  · exact B2044259
  · exact B2044263
  · exact B2044267
  · exact B2044271
  · exact B2044275
  · exact B2044279
  · exact B2044283
  · exact B2044287
  · exact B2044291
  · exact B2044295
  · exact B2044299
  · exact B2044303
  · exact B2044307
  · exact B2044311
  · exact B2044315
  · exact B2044319
  · exact B2044323
  · exact B2044327
  · exact B2044331
  · exact B2044335
  · exact B2044339
  · exact B2044343
  · exact B2044347
  · exact B2044351
  · exact B2044355
  · exact B2044359
  · exact B2044363
  · exact B2044367
  · exact B2044371
  · exact B2044375
  · exact B2044379
  · exact B2044383
  · exact B2044387
  · exact B2044391
  · exact B2044395
  · exact B2044399
  · exact B2044403
  · exact B2044407
  · exact B2044411
  · exact B2044415
  · exact B2044419
  · exact B2044423
  · exact B2044427
  · exact B2044431
  · exact B2044435
  · exact B2044439
  · exact B2044443
  · exact B2044447
  · exact B2044451
  · exact B2044455
  · exact B2044459
  · exact B2044463
  · exact B2044467
  · exact B2044471
  · exact B2044475
  · exact B2044479
  · exact B2044483
  · exact B2044487
  · exact B2044491
  · exact B2044495
  · exact B2044499
  · exact B2044503
  · exact B2044507
  · exact B2044511
  · exact B2044515
  · exact B2044519
  · exact B2044523
  · exact B2044527
  · exact B2044531
  · exact B2044535
  · exact B2044539
  · exact B2044543
  · exact B2044547
  · exact B2044551
  · exact B2044555
  · exact B2044559
  · exact B2044563
  · exact B2044567
  · exact B2044571
  · exact B2044575
  · exact B2044579
  · exact B2044583
  · exact B2044587
  · exact B2044591
  · exact B2044595
  · exact B2044599
  · exact B2044603
  · exact B2044607
  · exact B2044611
  · exact B2044615
  · exact B2044619
  · exact B2044623
  · exact B2044627
  · exact B2044631
  · exact B2044635
  · exact B2044639
  · exact B2044643
  · exact B2044647
  · exact B2044651
  · exact B2044655
  · exact B2044659
  · exact B2044663
  · exact B2044667
  · exact B2044671
  · exact B2044675
  · exact B2044679
  · exact B2044683
  · exact B2044687
  · exact B2044691
  · exact B2044695
  · exact B2044699
  · exact B2044703
  · exact B2044707
  · exact B2044711
  · exact B2044715
  · exact B2044719
  · exact B2044723
  · exact B2044727
  · exact B2044731
  · exact B2044735
  · exact B2044739
  · exact B2044743
  · exact B2044747
  · exact B2044751
  · exact B2044755
  · exact B2044759
  · exact B2044763
  · exact B2044767
  · exact B2044771
  · exact B2044775
  · exact B2044779
  · exact B2044783
  · exact B2044787
  · exact B2044791
  · exact B2044795
  · exact B2044799
  · exact B2044803
  · exact B2044807
  · exact B2044811
  · exact B2044815
  · exact B2044819
  · exact B2044823
  · exact B2044827
  · exact B2044831
  · exact B2044835
  · exact B2044839
  · exact B2044843
  · exact B2044847
  · exact B2044851
  · exact B2044855
  · exact B2044859
  · exact B2044863
  · exact B2044867
  · exact B2044871
  · exact B2044875
  · exact B2044879
  · exact B2044883
  · exact B2044887
  · exact B2044891
  · exact B2044895
  · exact B2044899
  · exact B2044903
  · exact B2044907
  · exact B2044911
  · exact B2044915
  · exact B2044919
  · exact B2044923
  · exact B2044927
  · exact B2044931
  · exact B2044935
  · exact B2044939
  · exact B2044943
  · exact B2044947
  · exact B2044951
  · exact B2044955
  · exact B2044959
  · exact B2044963
  · exact B2044967
  · exact B2044971
  · exact B2044975
  · exact B2044979
  · exact B2044983
  · exact B2044987
  · exact B2044991
  · exact B2044995
  · exact B2044999
  · exact B2045003
  · exact B2045007
  · exact B2045011
  · exact B2045015
  · exact B2045019
  · exact B2045023
  · exact B2045027
  · exact B2045031
  · exact B2045035
  · exact B2045039
  · exact B2045043
  · exact B2045047
  · exact B2045051
  · exact B2045055
  · exact B2045059
  · exact B2045063
  · exact B2045067
  · exact B2045071
  · exact B2045075
  · exact B2045079
  · exact B2045083
  · exact B2045087
  · exact B2045091
  · exact B2045095
  · exact B2045099
  · exact B2045103
  · exact B2045107
  · exact B2045111
  · exact B2045115
  · exact B2045119
  · exact B2045123
  · exact B2045127
  · exact B2045131
  · exact B2045135
  · exact B2045139
  · exact B2045143
  · exact B2045147
  · exact B2045151
  · exact B2045155
  · exact B2045159
  · exact B2045163
  · exact B2045167
  · exact B2045171
  · exact B2045175
  · exact B2045179
  · exact B2045183
  · exact B2045187
  · exact B2045191
  · exact B2045195
  · exact B2045199
  · exact B2045203
  · exact B2045207
  · exact B2045211
  · exact B2045215
  · exact B2045219
  · exact B2045223
  · exact B2045227
  · exact B2045231
  · exact B2045235
  · exact B2045239
  · exact B2045243
  · exact B2045247
  · exact B2045251
  · exact B2045255
  · exact B2045259
  · exact B2045263
  · exact B2045267
  · exact B2045271
  · exact B2045275
  · exact B2045279
  · exact B2045283
  · exact B2045287
  · exact B2045291
  · exact B2045295
  · exact B2045299
  · exact B2045303
  · exact B2045307
  · exact B2045311
  · exact B2045315
  · exact B2045319
  · exact B2045323
  · exact B2045327
  · exact B2045331
  · exact B2045335
  · exact B2045339
  · exact B2045343
  · exact B2045347
  · exact B2045351
  · exact B2045355
  · exact B2045359
  · exact B2045363
  · exact B2045367
  · exact B2045371
  · exact B2045375
  · exact B2045379
  · exact B2045383
  · exact B2045387
  · exact B2045391
  · exact B2045395
  · exact B2045399
  · exact B2045403
  · exact B2045407
  · exact B2045411
  · exact B2045415
  · exact B2045419
  · exact B2045423
  · exact B2045427
  · exact B2045431
  · exact B2045435
theorem solution (m : ℕ) (hlo : 2043435 ≤ m) (hhi : m ≤ 2045435) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 510858 ≤ j := by omega
    have hj2 : j ≤ 511358 := by omega
    have hb : Blo 2043435 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
