-- Prove2me | solution 1 for syracuse_descends_range_2179435_2181435
-- status  : ACCEPTED   (prove)
-- author  : @chstdu
-- created : 2026-09-23T17:17:55.744084+00:00
-- url     : https://prove2.me/submissions/222aea2d-6313-437b-bfbe-75ef75927865

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

theorem B2451865 : Blo 2179435 2451865 := bbase (se 2 (by rfl) ⟨919449, by rfl⟩ : syracuseStep 2451865 = 1838899) (by norm_num)
theorem B3269153 : Blo 2179435 3269153 := bstep (se 2 (by rfl) ⟨1225932, by rfl⟩ : syracuseStep 3269153 = 2451865) B2451865
theorem B2179435 : Blo 2179435 2179435 := bstep (se 1 (by rfl) ⟨1634576, by rfl⟩ : syracuseStep 2179435 = 3269153) B3269153
theorem B8275061 : Blo 2179435 8275061 := bbase (se 5 (by rfl) ⟨387893, by rfl⟩ : syracuseStep 8275061 = 775787) (by norm_num)
theorem B5516707 : Blo 2179435 5516707 := bstep (se 1 (by rfl) ⟨4137530, by rfl⟩ : syracuseStep 5516707 = 8275061) B8275061
theorem B7355609 : Blo 2179435 7355609 := bstep (se 2 (by rfl) ⟨2758353, by rfl⟩ : syracuseStep 7355609 = 5516707) B5516707
theorem B4903739 : Blo 2179435 4903739 := bstep (se 1 (by rfl) ⟨3677804, by rfl⟩ : syracuseStep 4903739 = 7355609) B7355609
theorem B3269159 : Blo 2179435 3269159 := bstep (se 1 (by rfl) ⟨2451869, by rfl⟩ : syracuseStep 3269159 = 4903739) B4903739
theorem B2179439 : Blo 2179435 2179439 := bstep (se 1 (by rfl) ⟨1634579, by rfl⟩ : syracuseStep 2179439 = 3269159) B3269159
theorem B3269165 : Blo 2179435 3269165 := bbase (se 3 (by rfl) ⟨612968, by rfl⟩ : syracuseStep 3269165 = 1225937) (by norm_num)
theorem B2179443 : Blo 2179435 2179443 := bstep (se 1 (by rfl) ⟨1634582, by rfl⟩ : syracuseStep 2179443 = 3269165) B3269165
theorem B4903757 : Blo 2179435 4903757 := bbase (se 3 (by rfl) ⟨919454, by rfl⟩ : syracuseStep 4903757 = 1838909) (by norm_num)
theorem B3269171 : Blo 2179435 3269171 := bstep (se 1 (by rfl) ⟨2451878, by rfl⟩ : syracuseStep 3269171 = 4903757) B4903757
theorem B2179447 : Blo 2179435 2179447 := bstep (se 1 (by rfl) ⟨1634585, by rfl⟩ : syracuseStep 2179447 = 3269171) B3269171
theorem B2758369 : Blo 2179435 2758369 := bbase (se 2 (by rfl) ⟨1034388, by rfl⟩ : syracuseStep 2758369 = 2068777) (by norm_num)
theorem B3677825 : Blo 2179435 3677825 := bstep (se 2 (by rfl) ⟨1379184, by rfl⟩ : syracuseStep 3677825 = 2758369) B2758369
theorem B2451883 : Blo 2179435 2451883 := bstep (se 1 (by rfl) ⟨1838912, by rfl⟩ : syracuseStep 2451883 = 3677825) B3677825
theorem B3269177 : Blo 2179435 3269177 := bstep (se 2 (by rfl) ⟨1225941, by rfl⟩ : syracuseStep 3269177 = 2451883) B2451883
theorem B2179451 : Blo 2179435 2179451 := bstep (se 1 (by rfl) ⟨1634588, by rfl⟩ : syracuseStep 2179451 = 3269177) B3269177
theorem B24825365 : Blo 2179435 24825365 := bbase (se 6 (by rfl) ⟨581844, by rfl⟩ : syracuseStep 24825365 = 1163689) (by norm_num)
theorem B16550243 : Blo 2179435 16550243 := bstep (se 1 (by rfl) ⟨12412682, by rfl⟩ : syracuseStep 16550243 = 24825365) B24825365
theorem B11033495 : Blo 2179435 11033495 := bstep (se 1 (by rfl) ⟨8275121, by rfl⟩ : syracuseStep 11033495 = 16550243) B16550243
theorem B7355663 : Blo 2179435 7355663 := bstep (se 1 (by rfl) ⟨5516747, by rfl⟩ : syracuseStep 7355663 = 11033495) B11033495
theorem B4903775 : Blo 2179435 4903775 := bstep (se 1 (by rfl) ⟨3677831, by rfl⟩ : syracuseStep 4903775 = 7355663) B7355663
theorem B3269183 : Blo 2179435 3269183 := bstep (se 1 (by rfl) ⟨2451887, by rfl⟩ : syracuseStep 3269183 = 4903775) B4903775
theorem B2179455 : Blo 2179435 2179455 := bstep (se 1 (by rfl) ⟨1634591, by rfl⟩ : syracuseStep 2179455 = 3269183) B3269183
theorem B3269189 : Blo 2179435 3269189 := bbase (se 4 (by rfl) ⟨306486, by rfl⟩ : syracuseStep 3269189 = 612973) (by norm_num)
theorem B2179459 : Blo 2179435 2179459 := bstep (se 1 (by rfl) ⟨1634594, by rfl⟩ : syracuseStep 2179459 = 3269189) B3269189
theorem B3677845 : Blo 2179435 3677845 := bbase (se 6 (by rfl) ⟨86199, by rfl⟩ : syracuseStep 3677845 = 172399) (by norm_num)
theorem B4903793 : Blo 2179435 4903793 := bstep (se 2 (by rfl) ⟨1838922, by rfl⟩ : syracuseStep 4903793 = 3677845) B3677845
theorem B3269195 : Blo 2179435 3269195 := bstep (se 1 (by rfl) ⟨2451896, by rfl⟩ : syracuseStep 3269195 = 4903793) B4903793
theorem B2179463 : Blo 2179435 2179463 := bstep (se 1 (by rfl) ⟨1634597, by rfl⟩ : syracuseStep 2179463 = 3269195) B3269195
theorem B2451901 : Blo 2179435 2451901 := bbase (se 3 (by rfl) ⟨459731, by rfl⟩ : syracuseStep 2451901 = 919463) (by norm_num)
theorem B3269201 : Blo 2179435 3269201 := bstep (se 2 (by rfl) ⟨1225950, by rfl⟩ : syracuseStep 3269201 = 2451901) B2451901
theorem B2179467 : Blo 2179435 2179467 := bstep (se 1 (by rfl) ⟨1634600, by rfl⟩ : syracuseStep 2179467 = 3269201) B3269201
theorem B7355717 : Blo 2179435 7355717 := bbase (se 4 (by rfl) ⟨689598, by rfl⟩ : syracuseStep 7355717 = 1379197) (by norm_num)
theorem B4903811 : Blo 2179435 4903811 := bstep (se 1 (by rfl) ⟨3677858, by rfl⟩ : syracuseStep 4903811 = 7355717) B7355717
theorem B3269207 : Blo 2179435 3269207 := bstep (se 1 (by rfl) ⟨2451905, by rfl⟩ : syracuseStep 3269207 = 4903811) B4903811
theorem B2179471 : Blo 2179435 2179471 := bstep (se 1 (by rfl) ⟨1634603, by rfl⟩ : syracuseStep 2179471 = 3269207) B3269207
theorem B3269213 : Blo 2179435 3269213 := bbase (se 3 (by rfl) ⟨612977, by rfl⟩ : syracuseStep 3269213 = 1225955) (by norm_num)
theorem B2179475 : Blo 2179435 2179475 := bstep (se 1 (by rfl) ⟨1634606, by rfl⟩ : syracuseStep 2179475 = 3269213) B3269213
theorem B4903829 : Blo 2179435 4903829 := bbase (se 6 (by rfl) ⟨114933, by rfl⟩ : syracuseStep 4903829 = 229867) (by norm_num)
theorem B3269219 : Blo 2179435 3269219 := bstep (se 1 (by rfl) ⟨2451914, by rfl⟩ : syracuseStep 3269219 = 4903829) B4903829
theorem B2179479 : Blo 2179435 2179479 := bstep (se 1 (by rfl) ⟨1634609, by rfl⟩ : syracuseStep 2179479 = 3269219) B3269219
theorem B8502581 : Blo 2179435 8502581 := bbase (se 5 (by rfl) ⟨398558, by rfl⟩ : syracuseStep 8502581 = 797117) (by norm_num)
theorem B5668387 : Blo 2179435 5668387 := bstep (se 1 (by rfl) ⟨4251290, by rfl⟩ : syracuseStep 5668387 = 8502581) B8502581
theorem B30231397 : Blo 2179435 30231397 := bstep (se 4 (by rfl) ⟨2834193, by rfl⟩ : syracuseStep 30231397 = 5668387) B5668387
theorem B40308529 : Blo 2179435 40308529 := bstep (se 2 (by rfl) ⟨15115698, by rfl⟩ : syracuseStep 40308529 = 30231397) B30231397
theorem B53744705 : Blo 2179435 53744705 := bstep (se 2 (by rfl) ⟨20154264, by rfl⟩ : syracuseStep 53744705 = 40308529) B40308529
theorem B35829803 : Blo 2179435 35829803 := bstep (se 1 (by rfl) ⟨26872352, by rfl⟩ : syracuseStep 35829803 = 53744705) B53744705
theorem B23886535 : Blo 2179435 23886535 := bstep (se 1 (by rfl) ⟨17914901, by rfl⟩ : syracuseStep 23886535 = 35829803) B35829803
theorem B31848713 : Blo 2179435 31848713 := bstep (se 2 (by rfl) ⟨11943267, by rfl⟩ : syracuseStep 31848713 = 23886535) B23886535
theorem B21232475 : Blo 2179435 21232475 := bstep (se 1 (by rfl) ⟨15924356, by rfl⟩ : syracuseStep 21232475 = 31848713) B31848713
theorem B14154983 : Blo 2179435 14154983 := bstep (se 1 (by rfl) ⟨10616237, by rfl⟩ : syracuseStep 14154983 = 21232475) B21232475
theorem B9436655 : Blo 2179435 9436655 := bstep (se 1 (by rfl) ⟨7077491, by rfl⟩ : syracuseStep 9436655 = 14154983) B14154983
theorem B6291103 : Blo 2179435 6291103 := bstep (se 1 (by rfl) ⟨4718327, by rfl⟩ : syracuseStep 6291103 = 9436655) B9436655
theorem B8388137 : Blo 2179435 8388137 := bstep (se 2 (by rfl) ⟨3145551, by rfl⟩ : syracuseStep 8388137 = 6291103) B6291103
theorem B5592091 : Blo 2179435 5592091 := bstep (se 1 (by rfl) ⟨4194068, by rfl⟩ : syracuseStep 5592091 = 8388137) B8388137
theorem B7456121 : Blo 2179435 7456121 := bstep (se 2 (by rfl) ⟨2796045, by rfl⟩ : syracuseStep 7456121 = 5592091) B5592091
theorem B4970747 : Blo 2179435 4970747 := bstep (se 1 (by rfl) ⟨3728060, by rfl⟩ : syracuseStep 4970747 = 7456121) B7456121
theorem B13255325 : Blo 2179435 13255325 := bstep (se 3 (by rfl) ⟨2485373, by rfl⟩ : syracuseStep 13255325 = 4970747) B4970747
theorem B8836883 : Blo 2179435 8836883 := bstep (se 1 (by rfl) ⟨6627662, by rfl⟩ : syracuseStep 8836883 = 13255325) B13255325
theorem B5891255 : Blo 2179435 5891255 := bstep (se 1 (by rfl) ⟨4418441, by rfl⟩ : syracuseStep 5891255 = 8836883) B8836883
theorem B3927503 : Blo 2179435 3927503 := bstep (se 1 (by rfl) ⟨2945627, by rfl⟩ : syracuseStep 3927503 = 5891255) B5891255
theorem B2618335 : Blo 2179435 2618335 := bstep (se 1 (by rfl) ⟨1963751, by rfl⟩ : syracuseStep 2618335 = 3927503) B3927503
theorem B3491113 : Blo 2179435 3491113 := bstep (se 2 (by rfl) ⟨1309167, by rfl⟩ : syracuseStep 3491113 = 2618335) B2618335
theorem B4654817 : Blo 2179435 4654817 := bstep (se 2 (by rfl) ⟨1745556, by rfl⟩ : syracuseStep 4654817 = 3491113) B3491113
theorem B3103211 : Blo 2179435 3103211 := bstep (se 1 (by rfl) ⟨2327408, by rfl⟩ : syracuseStep 3103211 = 4654817) B4654817
theorem B8275229 : Blo 2179435 8275229 := bstep (se 3 (by rfl) ⟨1551605, by rfl⟩ : syracuseStep 8275229 = 3103211) B3103211
theorem B5516819 : Blo 2179435 5516819 := bstep (se 1 (by rfl) ⟨4137614, by rfl⟩ : syracuseStep 5516819 = 8275229) B8275229
theorem B3677879 : Blo 2179435 3677879 := bstep (se 1 (by rfl) ⟨2758409, by rfl⟩ : syracuseStep 3677879 = 5516819) B5516819
theorem B2451919 : Blo 2179435 2451919 := bstep (se 1 (by rfl) ⟨1838939, by rfl⟩ : syracuseStep 2451919 = 3677879) B3677879
theorem B3269225 : Blo 2179435 3269225 := bstep (se 2 (by rfl) ⟨1225959, by rfl⟩ : syracuseStep 3269225 = 2451919) B2451919
theorem B2179483 : Blo 2179435 2179483 := bstep (se 1 (by rfl) ⟨1634612, by rfl⟩ : syracuseStep 2179483 = 3269225) B3269225
theorem B3927509 : Blo 2179435 3927509 := bbase (se 7 (by rfl) ⟨46025, by rfl⟩ : syracuseStep 3927509 = 92051) (by norm_num)
theorem B2618339 : Blo 2179435 2618339 := bstep (se 1 (by rfl) ⟨1963754, by rfl⟩ : syracuseStep 2618339 = 3927509) B3927509
theorem B6982237 : Blo 2179435 6982237 := bstep (se 3 (by rfl) ⟨1309169, by rfl⟩ : syracuseStep 6982237 = 2618339) B2618339
theorem B9309649 : Blo 2179435 9309649 := bstep (se 2 (by rfl) ⟨3491118, by rfl⟩ : syracuseStep 9309649 = 6982237) B6982237
theorem B12412865 : Blo 2179435 12412865 := bstep (se 2 (by rfl) ⟨4654824, by rfl⟩ : syracuseStep 12412865 = 9309649) B9309649
theorem B8275243 : Blo 2179435 8275243 := bstep (se 1 (by rfl) ⟨6206432, by rfl⟩ : syracuseStep 8275243 = 12412865) B12412865
theorem B11033657 : Blo 2179435 11033657 := bstep (se 2 (by rfl) ⟨4137621, by rfl⟩ : syracuseStep 11033657 = 8275243) B8275243
theorem B7355771 : Blo 2179435 7355771 := bstep (se 1 (by rfl) ⟨5516828, by rfl⟩ : syracuseStep 7355771 = 11033657) B11033657
theorem B4903847 : Blo 2179435 4903847 := bstep (se 1 (by rfl) ⟨3677885, by rfl⟩ : syracuseStep 4903847 = 7355771) B7355771
theorem B3269231 : Blo 2179435 3269231 := bstep (se 1 (by rfl) ⟨2451923, by rfl⟩ : syracuseStep 3269231 = 4903847) B4903847
theorem B2179487 : Blo 2179435 2179487 := bstep (se 1 (by rfl) ⟨1634615, by rfl⟩ : syracuseStep 2179487 = 3269231) B3269231
theorem B3269237 : Blo 2179435 3269237 := bbase (se 5 (by rfl) ⟨153245, by rfl⟩ : syracuseStep 3269237 = 306491) (by norm_num)
theorem B2179491 : Blo 2179435 2179491 := bstep (se 1 (by rfl) ⟨1634618, by rfl⟩ : syracuseStep 2179491 = 3269237) B3269237
theorem B4137637 : Blo 2179435 4137637 := bbase (se 4 (by rfl) ⟨387903, by rfl⟩ : syracuseStep 4137637 = 775807) (by norm_num)
theorem B5516849 : Blo 2179435 5516849 := bstep (se 2 (by rfl) ⟨2068818, by rfl⟩ : syracuseStep 5516849 = 4137637) B4137637
theorem B3677899 : Blo 2179435 3677899 := bstep (se 1 (by rfl) ⟨2758424, by rfl⟩ : syracuseStep 3677899 = 5516849) B5516849
theorem B4903865 : Blo 2179435 4903865 := bstep (se 2 (by rfl) ⟨1838949, by rfl⟩ : syracuseStep 4903865 = 3677899) B3677899
theorem B3269243 : Blo 2179435 3269243 := bstep (se 1 (by rfl) ⟨2451932, by rfl⟩ : syracuseStep 3269243 = 4903865) B4903865
theorem B2179495 : Blo 2179435 2179495 := bstep (se 1 (by rfl) ⟨1634621, by rfl⟩ : syracuseStep 2179495 = 3269243) B3269243
theorem B2451937 : Blo 2179435 2451937 := bbase (se 2 (by rfl) ⟨919476, by rfl⟩ : syracuseStep 2451937 = 1838953) (by norm_num)
theorem B3269249 : Blo 2179435 3269249 := bstep (se 2 (by rfl) ⟨1225968, by rfl⟩ : syracuseStep 3269249 = 2451937) B2451937
theorem B2179499 : Blo 2179435 2179499 := bstep (se 1 (by rfl) ⟨1634624, by rfl⟩ : syracuseStep 2179499 = 3269249) B3269249
theorem B5516869 : Blo 2179435 5516869 := bbase (se 4 (by rfl) ⟨517206, by rfl⟩ : syracuseStep 5516869 = 1034413) (by norm_num)
theorem B7355825 : Blo 2179435 7355825 := bstep (se 2 (by rfl) ⟨2758434, by rfl⟩ : syracuseStep 7355825 = 5516869) B5516869
theorem B4903883 : Blo 2179435 4903883 := bstep (se 1 (by rfl) ⟨3677912, by rfl⟩ : syracuseStep 4903883 = 7355825) B7355825
theorem B3269255 : Blo 2179435 3269255 := bstep (se 1 (by rfl) ⟨2451941, by rfl⟩ : syracuseStep 3269255 = 4903883) B4903883
theorem B2179503 : Blo 2179435 2179503 := bstep (se 1 (by rfl) ⟨1634627, by rfl⟩ : syracuseStep 2179503 = 3269255) B3269255
theorem B3269261 : Blo 2179435 3269261 := bbase (se 3 (by rfl) ⟨612986, by rfl⟩ : syracuseStep 3269261 = 1225973) (by norm_num)
theorem B2179507 : Blo 2179435 2179507 := bstep (se 1 (by rfl) ⟨1634630, by rfl⟩ : syracuseStep 2179507 = 3269261) B3269261
theorem B4903901 : Blo 2179435 4903901 := bbase (se 3 (by rfl) ⟨919481, by rfl⟩ : syracuseStep 4903901 = 1838963) (by norm_num)
theorem B3269267 : Blo 2179435 3269267 := bstep (se 1 (by rfl) ⟨2451950, by rfl⟩ : syracuseStep 3269267 = 4903901) B4903901
theorem B2179511 : Blo 2179435 2179511 := bstep (se 1 (by rfl) ⟨1634633, by rfl⟩ : syracuseStep 2179511 = 3269267) B3269267
theorem B3677933 : Blo 2179435 3677933 := bbase (se 3 (by rfl) ⟨689612, by rfl⟩ : syracuseStep 3677933 = 1379225) (by norm_num)
theorem B2451955 : Blo 2179435 2451955 := bstep (se 1 (by rfl) ⟨1838966, by rfl⟩ : syracuseStep 2451955 = 3677933) B3677933
theorem B3269273 : Blo 2179435 3269273 := bstep (se 2 (by rfl) ⟨1225977, by rfl⟩ : syracuseStep 3269273 = 2451955) B2451955
theorem B2179515 : Blo 2179435 2179515 := bstep (se 1 (by rfl) ⟨1634636, by rfl⟩ : syracuseStep 2179515 = 3269273) B3269273
theorem B10473509 : Blo 2179435 10473509 := bbase (se 4 (by rfl) ⟨981891, by rfl⟩ : syracuseStep 10473509 = 1963783) (by norm_num)
theorem B27929357 : Blo 2179435 27929357 := bstep (se 3 (by rfl) ⟨5236754, by rfl⟩ : syracuseStep 27929357 = 10473509) B10473509
theorem B18619571 : Blo 2179435 18619571 := bstep (se 1 (by rfl) ⟨13964678, by rfl⟩ : syracuseStep 18619571 = 27929357) B27929357
theorem B12413047 : Blo 2179435 12413047 := bstep (se 1 (by rfl) ⟨9309785, by rfl⟩ : syracuseStep 12413047 = 18619571) B18619571
theorem B16550729 : Blo 2179435 16550729 := bstep (se 2 (by rfl) ⟨6206523, by rfl⟩ : syracuseStep 16550729 = 12413047) B12413047
theorem B11033819 : Blo 2179435 11033819 := bstep (se 1 (by rfl) ⟨8275364, by rfl⟩ : syracuseStep 11033819 = 16550729) B16550729
theorem B7355879 : Blo 2179435 7355879 := bstep (se 1 (by rfl) ⟨5516909, by rfl⟩ : syracuseStep 7355879 = 11033819) B11033819
theorem B4903919 : Blo 2179435 4903919 := bstep (se 1 (by rfl) ⟨3677939, by rfl⟩ : syracuseStep 4903919 = 7355879) B7355879
theorem B3269279 : Blo 2179435 3269279 := bstep (se 1 (by rfl) ⟨2451959, by rfl⟩ : syracuseStep 3269279 = 4903919) B4903919
theorem B2179519 : Blo 2179435 2179519 := bstep (se 1 (by rfl) ⟨1634639, by rfl⟩ : syracuseStep 2179519 = 3269279) B3269279
theorem B3269285 : Blo 2179435 3269285 := bbase (se 4 (by rfl) ⟨306495, by rfl⟩ : syracuseStep 3269285 = 612991) (by norm_num)
theorem B2179523 : Blo 2179435 2179523 := bstep (se 1 (by rfl) ⟨1634642, by rfl⟩ : syracuseStep 2179523 = 3269285) B3269285
theorem B2758465 : Blo 2179435 2758465 := bbase (se 2 (by rfl) ⟨1034424, by rfl⟩ : syracuseStep 2758465 = 2068849) (by norm_num)
theorem B3677953 : Blo 2179435 3677953 := bstep (se 2 (by rfl) ⟨1379232, by rfl⟩ : syracuseStep 3677953 = 2758465) B2758465
theorem B4903937 : Blo 2179435 4903937 := bstep (se 2 (by rfl) ⟨1838976, by rfl⟩ : syracuseStep 4903937 = 3677953) B3677953
theorem B3269291 : Blo 2179435 3269291 := bstep (se 1 (by rfl) ⟨2451968, by rfl⟩ : syracuseStep 3269291 = 4903937) B4903937
theorem B2179527 : Blo 2179435 2179527 := bstep (se 1 (by rfl) ⟨1634645, by rfl⟩ : syracuseStep 2179527 = 3269291) B3269291
theorem B2451973 : Blo 2179435 2451973 := bbase (se 4 (by rfl) ⟨229872, by rfl⟩ : syracuseStep 2451973 = 459745) (by norm_num)
theorem B3269297 : Blo 2179435 3269297 := bstep (se 2 (by rfl) ⟨1225986, by rfl⟩ : syracuseStep 3269297 = 2451973) B2451973
theorem B2179531 : Blo 2179435 2179531 := bstep (se 1 (by rfl) ⟨1634648, by rfl⟩ : syracuseStep 2179531 = 3269297) B3269297
theorem B3103285 : Blo 2179435 3103285 := bbase (se 5 (by rfl) ⟨145466, by rfl⟩ : syracuseStep 3103285 = 290933) (by norm_num)
theorem B4137713 : Blo 2179435 4137713 := bstep (se 2 (by rfl) ⟨1551642, by rfl⟩ : syracuseStep 4137713 = 3103285) B3103285
theorem B2758475 : Blo 2179435 2758475 := bstep (se 1 (by rfl) ⟨2068856, by rfl⟩ : syracuseStep 2758475 = 4137713) B4137713
theorem B7355933 : Blo 2179435 7355933 := bstep (se 3 (by rfl) ⟨1379237, by rfl⟩ : syracuseStep 7355933 = 2758475) B2758475
theorem B4903955 : Blo 2179435 4903955 := bstep (se 1 (by rfl) ⟨3677966, by rfl⟩ : syracuseStep 4903955 = 7355933) B7355933
theorem B3269303 : Blo 2179435 3269303 := bstep (se 1 (by rfl) ⟨2451977, by rfl⟩ : syracuseStep 3269303 = 4903955) B4903955
theorem B2179535 : Blo 2179435 2179535 := bstep (se 1 (by rfl) ⟨1634651, by rfl⟩ : syracuseStep 2179535 = 3269303) B3269303
theorem B3269309 : Blo 2179435 3269309 := bbase (se 3 (by rfl) ⟨612995, by rfl⟩ : syracuseStep 3269309 = 1225991) (by norm_num)
theorem B2179539 : Blo 2179435 2179539 := bstep (se 1 (by rfl) ⟨1634654, by rfl⟩ : syracuseStep 2179539 = 3269309) B3269309
theorem B4903973 : Blo 2179435 4903973 := bbase (se 4 (by rfl) ⟨459747, by rfl⟩ : syracuseStep 4903973 = 919495) (by norm_num)
theorem B3269315 : Blo 2179435 3269315 := bstep (se 1 (by rfl) ⟨2451986, by rfl⟩ : syracuseStep 3269315 = 4903973) B4903973
theorem B2179543 : Blo 2179435 2179543 := bstep (se 1 (by rfl) ⟨1634657, by rfl⟩ : syracuseStep 2179543 = 3269315) B3269315
theorem B5516981 : Blo 2179435 5516981 := bbase (se 5 (by rfl) ⟨258608, by rfl⟩ : syracuseStep 5516981 = 517217) (by norm_num)
theorem B3677987 : Blo 2179435 3677987 := bstep (se 1 (by rfl) ⟨2758490, by rfl⟩ : syracuseStep 3677987 = 5516981) B5516981
theorem B2451991 : Blo 2179435 2451991 := bstep (se 1 (by rfl) ⟨1838993, by rfl⟩ : syracuseStep 2451991 = 3677987) B3677987
theorem B3269321 : Blo 2179435 3269321 := bstep (se 2 (by rfl) ⟨1225995, by rfl⟩ : syracuseStep 3269321 = 2451991) B2451991
theorem B2179547 : Blo 2179435 2179547 := bstep (se 1 (by rfl) ⟨1634660, by rfl⟩ : syracuseStep 2179547 = 3269321) B3269321
theorem B13964885 : Blo 2179435 13964885 := bbase (se 8 (by rfl) ⟨81825, by rfl⟩ : syracuseStep 13964885 = 163651) (by norm_num)
theorem B9309923 : Blo 2179435 9309923 := bstep (se 1 (by rfl) ⟨6982442, by rfl⟩ : syracuseStep 9309923 = 13964885) B13964885
theorem B6206615 : Blo 2179435 6206615 := bstep (se 1 (by rfl) ⟨4654961, by rfl⟩ : syracuseStep 6206615 = 9309923) B9309923
theorem B4137743 : Blo 2179435 4137743 := bstep (se 1 (by rfl) ⟨3103307, by rfl⟩ : syracuseStep 4137743 = 6206615) B6206615
theorem B11033981 : Blo 2179435 11033981 := bstep (se 3 (by rfl) ⟨2068871, by rfl⟩ : syracuseStep 11033981 = 4137743) B4137743
theorem B7355987 : Blo 2179435 7355987 := bstep (se 1 (by rfl) ⟨5516990, by rfl⟩ : syracuseStep 7355987 = 11033981) B11033981
theorem B4903991 : Blo 2179435 4903991 := bstep (se 1 (by rfl) ⟨3677993, by rfl⟩ : syracuseStep 4903991 = 7355987) B7355987
theorem B3269327 : Blo 2179435 3269327 := bstep (se 1 (by rfl) ⟨2451995, by rfl⟩ : syracuseStep 3269327 = 4903991) B4903991
theorem B2179551 : Blo 2179435 2179551 := bstep (se 1 (by rfl) ⟨1634663, by rfl⟩ : syracuseStep 2179551 = 3269327) B3269327
theorem B3269333 : Blo 2179435 3269333 := bbase (se 7 (by rfl) ⟨38312, by rfl⟩ : syracuseStep 3269333 = 76625) (by norm_num)
theorem B2179555 : Blo 2179435 2179555 := bstep (se 1 (by rfl) ⟨1634666, by rfl⟩ : syracuseStep 2179555 = 3269333) B3269333
theorem B6982469 : Blo 2179435 6982469 := bbase (se 4 (by rfl) ⟨654606, by rfl⟩ : syracuseStep 6982469 = 1309213) (by norm_num)
theorem B4654979 : Blo 2179435 4654979 := bstep (se 1 (by rfl) ⟨3491234, by rfl⟩ : syracuseStep 4654979 = 6982469) B6982469
theorem B3103319 : Blo 2179435 3103319 := bstep (se 1 (by rfl) ⟨2327489, by rfl⟩ : syracuseStep 3103319 = 4654979) B4654979
theorem B8275517 : Blo 2179435 8275517 := bstep (se 3 (by rfl) ⟨1551659, by rfl⟩ : syracuseStep 8275517 = 3103319) B3103319
theorem B5517011 : Blo 2179435 5517011 := bstep (se 1 (by rfl) ⟨4137758, by rfl⟩ : syracuseStep 5517011 = 8275517) B8275517
theorem B3678007 : Blo 2179435 3678007 := bstep (se 1 (by rfl) ⟨2758505, by rfl⟩ : syracuseStep 3678007 = 5517011) B5517011
theorem B4904009 : Blo 2179435 4904009 := bstep (se 2 (by rfl) ⟨1839003, by rfl⟩ : syracuseStep 4904009 = 3678007) B3678007
theorem B3269339 : Blo 2179435 3269339 := bstep (se 1 (by rfl) ⟨2452004, by rfl⟩ : syracuseStep 3269339 = 4904009) B4904009
theorem B2179559 : Blo 2179435 2179559 := bstep (se 1 (by rfl) ⟨1634669, by rfl⟩ : syracuseStep 2179559 = 3269339) B3269339
theorem B2452009 : Blo 2179435 2452009 := bbase (se 2 (by rfl) ⟨919503, by rfl⟩ : syracuseStep 2452009 = 1839007) (by norm_num)
theorem B3269345 : Blo 2179435 3269345 := bstep (se 2 (by rfl) ⟨1226004, by rfl⟩ : syracuseStep 3269345 = 2452009) B2452009
theorem B2179563 : Blo 2179435 2179563 := bstep (se 1 (by rfl) ⟨1634672, by rfl⟩ : syracuseStep 2179563 = 3269345) B3269345
theorem B13255829 : Blo 2179435 13255829 := bbase (se 6 (by rfl) ⟨310683, by rfl⟩ : syracuseStep 13255829 = 621367) (by norm_num)
theorem B8837219 : Blo 2179435 8837219 := bstep (se 1 (by rfl) ⟨6627914, by rfl⟩ : syracuseStep 8837219 = 13255829) B13255829
theorem B23565917 : Blo 2179435 23565917 := bstep (se 3 (by rfl) ⟨4418609, by rfl⟩ : syracuseStep 23565917 = 8837219) B8837219
theorem B15710611 : Blo 2179435 15710611 := bstep (se 1 (by rfl) ⟨11782958, by rfl⟩ : syracuseStep 15710611 = 23565917) B23565917
theorem B20947481 : Blo 2179435 20947481 := bstep (se 2 (by rfl) ⟨7855305, by rfl⟩ : syracuseStep 20947481 = 15710611) B15710611
theorem B13964987 : Blo 2179435 13964987 := bstep (se 1 (by rfl) ⟨10473740, by rfl⟩ : syracuseStep 13964987 = 20947481) B20947481
theorem B9309991 : Blo 2179435 9309991 := bstep (se 1 (by rfl) ⟨6982493, by rfl⟩ : syracuseStep 9309991 = 13964987) B13964987
theorem B12413321 : Blo 2179435 12413321 := bstep (se 2 (by rfl) ⟨4654995, by rfl⟩ : syracuseStep 12413321 = 9309991) B9309991
theorem B8275547 : Blo 2179435 8275547 := bstep (se 1 (by rfl) ⟨6206660, by rfl⟩ : syracuseStep 8275547 = 12413321) B12413321
theorem B5517031 : Blo 2179435 5517031 := bstep (se 1 (by rfl) ⟨4137773, by rfl⟩ : syracuseStep 5517031 = 8275547) B8275547
theorem B7356041 : Blo 2179435 7356041 := bstep (se 2 (by rfl) ⟨2758515, by rfl⟩ : syracuseStep 7356041 = 5517031) B5517031
theorem B4904027 : Blo 2179435 4904027 := bstep (se 1 (by rfl) ⟨3678020, by rfl⟩ : syracuseStep 4904027 = 7356041) B7356041
theorem B3269351 : Blo 2179435 3269351 := bstep (se 1 (by rfl) ⟨2452013, by rfl⟩ : syracuseStep 3269351 = 4904027) B4904027
theorem B2179567 : Blo 2179435 2179567 := bstep (se 1 (by rfl) ⟨1634675, by rfl⟩ : syracuseStep 2179567 = 3269351) B3269351
theorem B3269357 : Blo 2179435 3269357 := bbase (se 3 (by rfl) ⟨613004, by rfl⟩ : syracuseStep 3269357 = 1226009) (by norm_num)
theorem B2179571 : Blo 2179435 2179571 := bstep (se 1 (by rfl) ⟨1634678, by rfl⟩ : syracuseStep 2179571 = 3269357) B3269357
theorem B4904045 : Blo 2179435 4904045 := bbase (se 3 (by rfl) ⟨919508, by rfl⟩ : syracuseStep 4904045 = 1839017) (by norm_num)
theorem B3269363 : Blo 2179435 3269363 := bstep (se 1 (by rfl) ⟨2452022, by rfl⟩ : syracuseStep 3269363 = 4904045) B4904045
theorem B2179575 : Blo 2179435 2179575 := bstep (se 1 (by rfl) ⟨1634681, by rfl⟩ : syracuseStep 2179575 = 3269363) B3269363
theorem B4137797 : Blo 2179435 4137797 := bbase (se 4 (by rfl) ⟨387918, by rfl⟩ : syracuseStep 4137797 = 775837) (by norm_num)
theorem B2758531 : Blo 2179435 2758531 := bstep (se 1 (by rfl) ⟨2068898, by rfl⟩ : syracuseStep 2758531 = 4137797) B4137797
theorem B3678041 : Blo 2179435 3678041 := bstep (se 2 (by rfl) ⟨1379265, by rfl⟩ : syracuseStep 3678041 = 2758531) B2758531
theorem B2452027 : Blo 2179435 2452027 := bstep (se 1 (by rfl) ⟨1839020, by rfl⟩ : syracuseStep 2452027 = 3678041) B3678041
theorem B3269369 : Blo 2179435 3269369 := bstep (se 2 (by rfl) ⟨1226013, by rfl⟩ : syracuseStep 3269369 = 2452027) B2452027
theorem B2179579 : Blo 2179435 2179579 := bstep (se 1 (by rfl) ⟨1634684, by rfl⟩ : syracuseStep 2179579 = 3269369) B3269369
theorem B12582773 : Blo 2179435 12582773 := bbase (se 5 (by rfl) ⟨589817, by rfl⟩ : syracuseStep 12582773 = 1179635) (by norm_num)
theorem B8388515 : Blo 2179435 8388515 := bstep (se 1 (by rfl) ⟨6291386, by rfl⟩ : syracuseStep 8388515 = 12582773) B12582773
theorem B22369373 : Blo 2179435 22369373 := bstep (se 3 (by rfl) ⟨4194257, by rfl⟩ : syracuseStep 22369373 = 8388515) B8388515
theorem B14912915 : Blo 2179435 14912915 := bstep (se 1 (by rfl) ⟨11184686, by rfl⟩ : syracuseStep 14912915 = 22369373) B22369373
theorem B39767773 : Blo 2179435 39767773 := bstep (se 3 (by rfl) ⟨7456457, by rfl⟩ : syracuseStep 39767773 = 14912915) B14912915
theorem B53023697 : Blo 2179435 53023697 := bstep (se 2 (by rfl) ⟨19883886, by rfl⟩ : syracuseStep 53023697 = 39767773) B39767773
theorem B35349131 : Blo 2179435 35349131 := bstep (se 1 (by rfl) ⟨26511848, by rfl⟩ : syracuseStep 35349131 = 53023697) B53023697
theorem B23566087 : Blo 2179435 23566087 := bstep (se 1 (by rfl) ⟨17674565, by rfl⟩ : syracuseStep 23566087 = 35349131) B35349131
theorem B31421449 : Blo 2179435 31421449 := bstep (se 2 (by rfl) ⟨11783043, by rfl⟩ : syracuseStep 31421449 = 23566087) B23566087
theorem B41895265 : Blo 2179435 41895265 := bstep (se 2 (by rfl) ⟨15710724, by rfl⟩ : syracuseStep 41895265 = 31421449) B31421449
theorem B55860353 : Blo 2179435 55860353 := bstep (se 2 (by rfl) ⟨20947632, by rfl⟩ : syracuseStep 55860353 = 41895265) B41895265
theorem B37240235 : Blo 2179435 37240235 := bstep (se 1 (by rfl) ⟨27930176, by rfl⟩ : syracuseStep 37240235 = 55860353) B55860353
theorem B24826823 : Blo 2179435 24826823 := bstep (se 1 (by rfl) ⟨18620117, by rfl⟩ : syracuseStep 24826823 = 37240235) B37240235
theorem B16551215 : Blo 2179435 16551215 := bstep (se 1 (by rfl) ⟨12413411, by rfl⟩ : syracuseStep 16551215 = 24826823) B24826823
theorem B11034143 : Blo 2179435 11034143 := bstep (se 1 (by rfl) ⟨8275607, by rfl⟩ : syracuseStep 11034143 = 16551215) B16551215
theorem B7356095 : Blo 2179435 7356095 := bstep (se 1 (by rfl) ⟨5517071, by rfl⟩ : syracuseStep 7356095 = 11034143) B11034143
theorem B4904063 : Blo 2179435 4904063 := bstep (se 1 (by rfl) ⟨3678047, by rfl⟩ : syracuseStep 4904063 = 7356095) B7356095
theorem B3269375 : Blo 2179435 3269375 := bstep (se 1 (by rfl) ⟨2452031, by rfl⟩ : syracuseStep 3269375 = 4904063) B4904063
theorem B2179583 : Blo 2179435 2179583 := bstep (se 1 (by rfl) ⟨1634687, by rfl⟩ : syracuseStep 2179583 = 3269375) B3269375
theorem B3269381 : Blo 2179435 3269381 := bbase (se 4 (by rfl) ⟨306504, by rfl⟩ : syracuseStep 3269381 = 613009) (by norm_num)
theorem B2179587 : Blo 2179435 2179587 := bstep (se 1 (by rfl) ⟨1634690, by rfl⟩ : syracuseStep 2179587 = 3269381) B3269381
theorem B3678061 : Blo 2179435 3678061 := bbase (se 3 (by rfl) ⟨689636, by rfl⟩ : syracuseStep 3678061 = 1379273) (by norm_num)
theorem B4904081 : Blo 2179435 4904081 := bstep (se 2 (by rfl) ⟨1839030, by rfl⟩ : syracuseStep 4904081 = 3678061) B3678061
theorem B3269387 : Blo 2179435 3269387 := bstep (se 1 (by rfl) ⟨2452040, by rfl⟩ : syracuseStep 3269387 = 4904081) B4904081
theorem B2179591 : Blo 2179435 2179591 := bstep (se 1 (by rfl) ⟨1634693, by rfl⟩ : syracuseStep 2179591 = 3269387) B3269387
theorem B2452045 : Blo 2179435 2452045 := bbase (se 3 (by rfl) ⟨459758, by rfl⟩ : syracuseStep 2452045 = 919517) (by norm_num)
theorem B3269393 : Blo 2179435 3269393 := bstep (se 2 (by rfl) ⟨1226022, by rfl⟩ : syracuseStep 3269393 = 2452045) B2452045
theorem B2179595 : Blo 2179435 2179595 := bstep (se 1 (by rfl) ⟨1634696, by rfl⟩ : syracuseStep 2179595 = 3269393) B3269393
theorem B7356149 : Blo 2179435 7356149 := bbase (se 5 (by rfl) ⟨344819, by rfl⟩ : syracuseStep 7356149 = 689639) (by norm_num)
theorem B4904099 : Blo 2179435 4904099 := bstep (se 1 (by rfl) ⟨3678074, by rfl⟩ : syracuseStep 4904099 = 7356149) B7356149
theorem B3269399 : Blo 2179435 3269399 := bstep (se 1 (by rfl) ⟨2452049, by rfl⟩ : syracuseStep 3269399 = 4904099) B4904099
theorem B2179599 : Blo 2179435 2179599 := bstep (se 1 (by rfl) ⟨1634699, by rfl⟩ : syracuseStep 2179599 = 3269399) B3269399
theorem B3269405 : Blo 2179435 3269405 := bbase (se 3 (by rfl) ⟨613013, by rfl⟩ : syracuseStep 3269405 = 1226027) (by norm_num)
theorem B2179603 : Blo 2179435 2179603 := bstep (se 1 (by rfl) ⟨1634702, by rfl⟩ : syracuseStep 2179603 = 3269405) B3269405
theorem B4904117 : Blo 2179435 4904117 := bbase (se 5 (by rfl) ⟨229880, by rfl⟩ : syracuseStep 4904117 = 459761) (by norm_num)
theorem B3269411 : Blo 2179435 3269411 := bstep (se 1 (by rfl) ⟨2452058, by rfl⟩ : syracuseStep 3269411 = 4904117) B4904117
theorem B2179607 : Blo 2179435 2179607 := bstep (se 1 (by rfl) ⟨1634705, by rfl⟩ : syracuseStep 2179607 = 3269411) B3269411
theorem B2327545 : Blo 2179435 2327545 := bbase (se 2 (by rfl) ⟨872829, by rfl⟩ : syracuseStep 2327545 = 1745659) (by norm_num)
theorem B12413573 : Blo 2179435 12413573 := bstep (se 4 (by rfl) ⟨1163772, by rfl⟩ : syracuseStep 12413573 = 2327545) B2327545
theorem B8275715 : Blo 2179435 8275715 := bstep (se 1 (by rfl) ⟨6206786, by rfl⟩ : syracuseStep 8275715 = 12413573) B12413573
theorem B5517143 : Blo 2179435 5517143 := bstep (se 1 (by rfl) ⟨4137857, by rfl⟩ : syracuseStep 5517143 = 8275715) B8275715
theorem B3678095 : Blo 2179435 3678095 := bstep (se 1 (by rfl) ⟨2758571, by rfl⟩ : syracuseStep 3678095 = 5517143) B5517143
theorem B2452063 : Blo 2179435 2452063 := bstep (se 1 (by rfl) ⟨1839047, by rfl⟩ : syracuseStep 2452063 = 3678095) B3678095
theorem B3269417 : Blo 2179435 3269417 := bstep (se 2 (by rfl) ⟨1226031, by rfl⟩ : syracuseStep 3269417 = 2452063) B2452063
theorem B2179611 : Blo 2179435 2179611 := bstep (se 1 (by rfl) ⟨1634708, by rfl⟩ : syracuseStep 2179611 = 3269417) B3269417
theorem B2327549 : Blo 2179435 2327549 := bbase (se 3 (by rfl) ⟨436415, by rfl⟩ : syracuseStep 2327549 = 872831) (by norm_num)
theorem B6206797 : Blo 2179435 6206797 := bstep (se 3 (by rfl) ⟨1163774, by rfl⟩ : syracuseStep 6206797 = 2327549) B2327549
theorem B8275729 : Blo 2179435 8275729 := bstep (se 2 (by rfl) ⟨3103398, by rfl⟩ : syracuseStep 8275729 = 6206797) B6206797
theorem B11034305 : Blo 2179435 11034305 := bstep (se 2 (by rfl) ⟨4137864, by rfl⟩ : syracuseStep 11034305 = 8275729) B8275729
theorem B7356203 : Blo 2179435 7356203 := bstep (se 1 (by rfl) ⟨5517152, by rfl⟩ : syracuseStep 7356203 = 11034305) B11034305
theorem B4904135 : Blo 2179435 4904135 := bstep (se 1 (by rfl) ⟨3678101, by rfl⟩ : syracuseStep 4904135 = 7356203) B7356203
theorem B3269423 : Blo 2179435 3269423 := bstep (se 1 (by rfl) ⟨2452067, by rfl⟩ : syracuseStep 3269423 = 4904135) B4904135
theorem B2179615 : Blo 2179435 2179615 := bstep (se 1 (by rfl) ⟨1634711, by rfl⟩ : syracuseStep 2179615 = 3269423) B3269423
theorem B3269429 : Blo 2179435 3269429 := bbase (se 5 (by rfl) ⟨153254, by rfl⟩ : syracuseStep 3269429 = 306509) (by norm_num)
theorem B2179619 : Blo 2179435 2179619 := bstep (se 1 (by rfl) ⟨1634714, by rfl⟩ : syracuseStep 2179619 = 3269429) B3269429
theorem B5517173 : Blo 2179435 5517173 := bbase (se 5 (by rfl) ⟨258617, by rfl⟩ : syracuseStep 5517173 = 517235) (by norm_num)
theorem B3678115 : Blo 2179435 3678115 := bstep (se 1 (by rfl) ⟨2758586, by rfl⟩ : syracuseStep 3678115 = 5517173) B5517173
theorem B4904153 : Blo 2179435 4904153 := bstep (se 2 (by rfl) ⟨1839057, by rfl⟩ : syracuseStep 4904153 = 3678115) B3678115
theorem B3269435 : Blo 2179435 3269435 := bstep (se 1 (by rfl) ⟨2452076, by rfl⟩ : syracuseStep 3269435 = 4904153) B4904153
theorem B2179623 : Blo 2179435 2179623 := bstep (se 1 (by rfl) ⟨1634717, by rfl⟩ : syracuseStep 2179623 = 3269435) B3269435
theorem B2452081 : Blo 2179435 2452081 := bbase (se 2 (by rfl) ⟨919530, by rfl⟩ : syracuseStep 2452081 = 1839061) (by norm_num)
theorem B3269441 : Blo 2179435 3269441 := bstep (se 2 (by rfl) ⟨1226040, by rfl⟩ : syracuseStep 3269441 = 2452081) B2452081
theorem B2179627 : Blo 2179435 2179627 := bstep (se 1 (by rfl) ⟨1634720, by rfl⟩ : syracuseStep 2179627 = 3269441) B3269441
theorem B5891653 : Blo 2179435 5891653 := bbase (se 4 (by rfl) ⟨552342, by rfl⟩ : syracuseStep 5891653 = 1104685) (by norm_num)
theorem B7855537 : Blo 2179435 7855537 := bstep (se 2 (by rfl) ⟨2945826, by rfl⟩ : syracuseStep 7855537 = 5891653) B5891653
theorem B10474049 : Blo 2179435 10474049 := bstep (se 2 (by rfl) ⟨3927768, by rfl⟩ : syracuseStep 10474049 = 7855537) B7855537
theorem B6982699 : Blo 2179435 6982699 := bstep (se 1 (by rfl) ⟨5237024, by rfl⟩ : syracuseStep 6982699 = 10474049) B10474049
theorem B9310265 : Blo 2179435 9310265 := bstep (se 2 (by rfl) ⟨3491349, by rfl⟩ : syracuseStep 9310265 = 6982699) B6982699
theorem B6206843 : Blo 2179435 6206843 := bstep (se 1 (by rfl) ⟨4655132, by rfl⟩ : syracuseStep 6206843 = 9310265) B9310265
theorem B4137895 : Blo 2179435 4137895 := bstep (se 1 (by rfl) ⟨3103421, by rfl⟩ : syracuseStep 4137895 = 6206843) B6206843
theorem B5517193 : Blo 2179435 5517193 := bstep (se 2 (by rfl) ⟨2068947, by rfl⟩ : syracuseStep 5517193 = 4137895) B4137895
theorem B7356257 : Blo 2179435 7356257 := bstep (se 2 (by rfl) ⟨2758596, by rfl⟩ : syracuseStep 7356257 = 5517193) B5517193
theorem B4904171 : Blo 2179435 4904171 := bstep (se 1 (by rfl) ⟨3678128, by rfl⟩ : syracuseStep 4904171 = 7356257) B7356257
theorem B3269447 : Blo 2179435 3269447 := bstep (se 1 (by rfl) ⟨2452085, by rfl⟩ : syracuseStep 3269447 = 4904171) B4904171
theorem B2179631 : Blo 2179435 2179631 := bstep (se 1 (by rfl) ⟨1634723, by rfl⟩ : syracuseStep 2179631 = 3269447) B3269447
theorem B3269453 : Blo 2179435 3269453 := bbase (se 3 (by rfl) ⟨613022, by rfl⟩ : syracuseStep 3269453 = 1226045) (by norm_num)
theorem B2179635 : Blo 2179435 2179635 := bstep (se 1 (by rfl) ⟨1634726, by rfl⟩ : syracuseStep 2179635 = 3269453) B3269453
theorem B4904189 : Blo 2179435 4904189 := bbase (se 3 (by rfl) ⟨919535, by rfl⟩ : syracuseStep 4904189 = 1839071) (by norm_num)
theorem B3269459 : Blo 2179435 3269459 := bstep (se 1 (by rfl) ⟨2452094, by rfl⟩ : syracuseStep 3269459 = 4904189) B4904189
theorem B2179639 : Blo 2179435 2179639 := bstep (se 1 (by rfl) ⟨1634729, by rfl⟩ : syracuseStep 2179639 = 3269459) B3269459
theorem B3678149 : Blo 2179435 3678149 := bbase (se 4 (by rfl) ⟨344826, by rfl⟩ : syracuseStep 3678149 = 689653) (by norm_num)
theorem B2452099 : Blo 2179435 2452099 := bstep (se 1 (by rfl) ⟨1839074, by rfl⟩ : syracuseStep 2452099 = 3678149) B3678149
theorem B3269465 : Blo 2179435 3269465 := bstep (se 2 (by rfl) ⟨1226049, by rfl⟩ : syracuseStep 3269465 = 2452099) B2452099
theorem B2179643 : Blo 2179435 2179643 := bstep (se 1 (by rfl) ⟨1634732, by rfl⟩ : syracuseStep 2179643 = 3269465) B3269465
theorem B16551701 : Blo 2179435 16551701 := bbase (se 6 (by rfl) ⟨387930, by rfl⟩ : syracuseStep 16551701 = 775861) (by norm_num)
theorem B11034467 : Blo 2179435 11034467 := bstep (se 1 (by rfl) ⟨8275850, by rfl⟩ : syracuseStep 11034467 = 16551701) B16551701
theorem B7356311 : Blo 2179435 7356311 := bstep (se 1 (by rfl) ⟨5517233, by rfl⟩ : syracuseStep 7356311 = 11034467) B11034467
theorem B4904207 : Blo 2179435 4904207 := bstep (se 1 (by rfl) ⟨3678155, by rfl⟩ : syracuseStep 4904207 = 7356311) B7356311
theorem B3269471 : Blo 2179435 3269471 := bstep (se 1 (by rfl) ⟨2452103, by rfl⟩ : syracuseStep 3269471 = 4904207) B4904207
theorem B2179647 : Blo 2179435 2179647 := bstep (se 1 (by rfl) ⟨1634735, by rfl⟩ : syracuseStep 2179647 = 3269471) B3269471
theorem B3269477 : Blo 2179435 3269477 := bbase (se 4 (by rfl) ⟨306513, by rfl⟩ : syracuseStep 3269477 = 613027) (by norm_num)
theorem B2179651 : Blo 2179435 2179651 := bstep (se 1 (by rfl) ⟨1634738, by rfl⟩ : syracuseStep 2179651 = 3269477) B3269477
theorem B4137941 : Blo 2179435 4137941 := bbase (se 7 (by rfl) ⟨48491, by rfl⟩ : syracuseStep 4137941 = 96983) (by norm_num)
theorem B2758627 : Blo 2179435 2758627 := bstep (se 1 (by rfl) ⟨2068970, by rfl⟩ : syracuseStep 2758627 = 4137941) B4137941
theorem B3678169 : Blo 2179435 3678169 := bstep (se 2 (by rfl) ⟨1379313, by rfl⟩ : syracuseStep 3678169 = 2758627) B2758627
theorem B4904225 : Blo 2179435 4904225 := bstep (se 2 (by rfl) ⟨1839084, by rfl⟩ : syracuseStep 4904225 = 3678169) B3678169
theorem B3269483 : Blo 2179435 3269483 := bstep (se 1 (by rfl) ⟨2452112, by rfl⟩ : syracuseStep 3269483 = 4904225) B4904225
theorem B2179655 : Blo 2179435 2179655 := bstep (se 1 (by rfl) ⟨1634741, by rfl⟩ : syracuseStep 2179655 = 3269483) B3269483
theorem B2452117 : Blo 2179435 2452117 := bbase (se 6 (by rfl) ⟨57471, by rfl⟩ : syracuseStep 2452117 = 114943) (by norm_num)
theorem B3269489 : Blo 2179435 3269489 := bstep (se 2 (by rfl) ⟨1226058, by rfl⟩ : syracuseStep 3269489 = 2452117) B2452117
theorem B2179659 : Blo 2179435 2179659 := bstep (se 1 (by rfl) ⟨1634744, by rfl⟩ : syracuseStep 2179659 = 3269489) B3269489
theorem B2758637 : Blo 2179435 2758637 := bbase (se 3 (by rfl) ⟨517244, by rfl⟩ : syracuseStep 2758637 = 1034489) (by norm_num)
theorem B7356365 : Blo 2179435 7356365 := bstep (se 3 (by rfl) ⟨1379318, by rfl⟩ : syracuseStep 7356365 = 2758637) B2758637
theorem B4904243 : Blo 2179435 4904243 := bstep (se 1 (by rfl) ⟨3678182, by rfl⟩ : syracuseStep 4904243 = 7356365) B7356365
theorem B3269495 : Blo 2179435 3269495 := bstep (se 1 (by rfl) ⟨2452121, by rfl⟩ : syracuseStep 3269495 = 4904243) B4904243
theorem B2179663 : Blo 2179435 2179663 := bstep (se 1 (by rfl) ⟨1634747, by rfl⟩ : syracuseStep 2179663 = 3269495) B3269495
theorem B3269501 : Blo 2179435 3269501 := bbase (se 3 (by rfl) ⟨613031, by rfl⟩ : syracuseStep 3269501 = 1226063) (by norm_num)
theorem B2179667 : Blo 2179435 2179667 := bstep (se 1 (by rfl) ⟨1634750, by rfl⟩ : syracuseStep 2179667 = 3269501) B3269501
theorem B4904261 : Blo 2179435 4904261 := bbase (se 4 (by rfl) ⟨459774, by rfl⟩ : syracuseStep 4904261 = 919549) (by norm_num)
theorem B3269507 : Blo 2179435 3269507 := bstep (se 1 (by rfl) ⟨2452130, by rfl⟩ : syracuseStep 3269507 = 4904261) B4904261
theorem B2179671 : Blo 2179435 2179671 := bstep (se 1 (by rfl) ⟨1634753, by rfl⟩ : syracuseStep 2179671 = 3269507) B3269507
theorem B3728389 : Blo 2179435 3728389 := bbase (se 4 (by rfl) ⟨349536, by rfl⟩ : syracuseStep 3728389 = 699073) (by norm_num)
theorem B4971185 : Blo 2179435 4971185 := bstep (se 2 (by rfl) ⟨1864194, by rfl⟩ : syracuseStep 4971185 = 3728389) B3728389
theorem B3314123 : Blo 2179435 3314123 := bstep (se 1 (by rfl) ⟨2485592, by rfl⟩ : syracuseStep 3314123 = 4971185) B4971185
theorem B2209415 : Blo 2179435 2209415 := bstep (se 1 (by rfl) ⟨1657061, by rfl⟩ : syracuseStep 2209415 = 3314123) B3314123
theorem B5891773 : Blo 2179435 5891773 := bstep (se 3 (by rfl) ⟨1104707, by rfl⟩ : syracuseStep 5891773 = 2209415) B2209415
theorem B7855697 : Blo 2179435 7855697 := bstep (se 2 (by rfl) ⟨2945886, by rfl⟩ : syracuseStep 7855697 = 5891773) B5891773
theorem B5237131 : Blo 2179435 5237131 := bstep (se 1 (by rfl) ⟨3927848, by rfl⟩ : syracuseStep 5237131 = 7855697) B7855697
theorem B6982841 : Blo 2179435 6982841 := bstep (se 2 (by rfl) ⟨2618565, by rfl⟩ : syracuseStep 6982841 = 5237131) B5237131
theorem B4655227 : Blo 2179435 4655227 := bstep (se 1 (by rfl) ⟨3491420, by rfl⟩ : syracuseStep 4655227 = 6982841) B6982841
theorem B6206969 : Blo 2179435 6206969 := bstep (se 2 (by rfl) ⟨2327613, by rfl⟩ : syracuseStep 6206969 = 4655227) B4655227
theorem B4137979 : Blo 2179435 4137979 := bstep (se 1 (by rfl) ⟨3103484, by rfl⟩ : syracuseStep 4137979 = 6206969) B6206969
theorem B5517305 : Blo 2179435 5517305 := bstep (se 2 (by rfl) ⟨2068989, by rfl⟩ : syracuseStep 5517305 = 4137979) B4137979
theorem B3678203 : Blo 2179435 3678203 := bstep (se 1 (by rfl) ⟨2758652, by rfl⟩ : syracuseStep 3678203 = 5517305) B5517305
theorem B2452135 : Blo 2179435 2452135 := bstep (se 1 (by rfl) ⟨1839101, by rfl⟩ : syracuseStep 2452135 = 3678203) B3678203
theorem B3269513 : Blo 2179435 3269513 := bstep (se 2 (by rfl) ⟨1226067, by rfl⟩ : syracuseStep 3269513 = 2452135) B2452135
theorem B2179675 : Blo 2179435 2179675 := bstep (se 1 (by rfl) ⟨1634756, by rfl⟩ : syracuseStep 2179675 = 3269513) B3269513
theorem B11034629 : Blo 2179435 11034629 := bbase (se 4 (by rfl) ⟨1034496, by rfl⟩ : syracuseStep 11034629 = 2068993) (by norm_num)
theorem B7356419 : Blo 2179435 7356419 := bstep (se 1 (by rfl) ⟨5517314, by rfl⟩ : syracuseStep 7356419 = 11034629) B11034629
theorem B4904279 : Blo 2179435 4904279 := bstep (se 1 (by rfl) ⟨3678209, by rfl⟩ : syracuseStep 4904279 = 7356419) B7356419
theorem B3269519 : Blo 2179435 3269519 := bstep (se 1 (by rfl) ⟨2452139, by rfl⟩ : syracuseStep 3269519 = 4904279) B4904279
theorem B2179679 : Blo 2179435 2179679 := bstep (se 1 (by rfl) ⟨1634759, by rfl⟩ : syracuseStep 2179679 = 3269519) B3269519
theorem B3269525 : Blo 2179435 3269525 := bbase (se 6 (by rfl) ⟨76629, by rfl⟩ : syracuseStep 3269525 = 153259) (by norm_num)
theorem B2179683 : Blo 2179435 2179683 := bstep (se 1 (by rfl) ⟨1634762, by rfl⟩ : syracuseStep 2179683 = 3269525) B3269525
theorem B12414005 : Blo 2179435 12414005 := bbase (se 5 (by rfl) ⟨581906, by rfl⟩ : syracuseStep 12414005 = 1163813) (by norm_num)
theorem B8276003 : Blo 2179435 8276003 := bstep (se 1 (by rfl) ⟨6207002, by rfl⟩ : syracuseStep 8276003 = 12414005) B12414005
theorem B5517335 : Blo 2179435 5517335 := bstep (se 1 (by rfl) ⟨4138001, by rfl⟩ : syracuseStep 5517335 = 8276003) B8276003
theorem B3678223 : Blo 2179435 3678223 := bstep (se 1 (by rfl) ⟨2758667, by rfl⟩ : syracuseStep 3678223 = 5517335) B5517335
theorem B4904297 : Blo 2179435 4904297 := bstep (se 2 (by rfl) ⟨1839111, by rfl⟩ : syracuseStep 4904297 = 3678223) B3678223
theorem B3269531 : Blo 2179435 3269531 := bstep (se 1 (by rfl) ⟨2452148, by rfl⟩ : syracuseStep 3269531 = 4904297) B4904297
theorem B2179687 : Blo 2179435 2179687 := bstep (se 1 (by rfl) ⟨1634765, by rfl⟩ : syracuseStep 2179687 = 3269531) B3269531
theorem B2452153 : Blo 2179435 2452153 := bbase (se 2 (by rfl) ⟨919557, by rfl⟩ : syracuseStep 2452153 = 1839115) (by norm_num)
theorem B3269537 : Blo 2179435 3269537 := bstep (se 2 (by rfl) ⟨1226076, by rfl⟩ : syracuseStep 3269537 = 2452153) B2452153
theorem B2179691 : Blo 2179435 2179691 := bstep (se 1 (by rfl) ⟨1634768, by rfl⟩ : syracuseStep 2179691 = 3269537) B3269537
theorem B4655269 : Blo 2179435 4655269 := bbase (se 4 (by rfl) ⟨436431, by rfl⟩ : syracuseStep 4655269 = 872863) (by norm_num)
theorem B6207025 : Blo 2179435 6207025 := bstep (se 2 (by rfl) ⟨2327634, by rfl⟩ : syracuseStep 6207025 = 4655269) B4655269
theorem B8276033 : Blo 2179435 8276033 := bstep (se 2 (by rfl) ⟨3103512, by rfl⟩ : syracuseStep 8276033 = 6207025) B6207025
theorem B5517355 : Blo 2179435 5517355 := bstep (se 1 (by rfl) ⟨4138016, by rfl⟩ : syracuseStep 5517355 = 8276033) B8276033
theorem B7356473 : Blo 2179435 7356473 := bstep (se 2 (by rfl) ⟨2758677, by rfl⟩ : syracuseStep 7356473 = 5517355) B5517355
theorem B4904315 : Blo 2179435 4904315 := bstep (se 1 (by rfl) ⟨3678236, by rfl⟩ : syracuseStep 4904315 = 7356473) B7356473
theorem B3269543 : Blo 2179435 3269543 := bstep (se 1 (by rfl) ⟨2452157, by rfl⟩ : syracuseStep 3269543 = 4904315) B4904315
theorem B2179695 : Blo 2179435 2179695 := bstep (se 1 (by rfl) ⟨1634771, by rfl⟩ : syracuseStep 2179695 = 3269543) B3269543
theorem B3269549 : Blo 2179435 3269549 := bbase (se 3 (by rfl) ⟨613040, by rfl⟩ : syracuseStep 3269549 = 1226081) (by norm_num)
theorem B2179699 : Blo 2179435 2179699 := bstep (se 1 (by rfl) ⟨1634774, by rfl⟩ : syracuseStep 2179699 = 3269549) B3269549
theorem B4904333 : Blo 2179435 4904333 := bbase (se 3 (by rfl) ⟨919562, by rfl⟩ : syracuseStep 4904333 = 1839125) (by norm_num)
theorem B3269555 : Blo 2179435 3269555 := bstep (se 1 (by rfl) ⟨2452166, by rfl⟩ : syracuseStep 3269555 = 4904333) B4904333
theorem B2179703 : Blo 2179435 2179703 := bstep (se 1 (by rfl) ⟨1634777, by rfl⟩ : syracuseStep 2179703 = 3269555) B3269555
theorem B2758693 : Blo 2179435 2758693 := bbase (se 4 (by rfl) ⟨258627, by rfl⟩ : syracuseStep 2758693 = 517255) (by norm_num)
theorem B3678257 : Blo 2179435 3678257 := bstep (se 2 (by rfl) ⟨1379346, by rfl⟩ : syracuseStep 3678257 = 2758693) B2758693
theorem B2452171 : Blo 2179435 2452171 := bstep (se 1 (by rfl) ⟨1839128, by rfl⟩ : syracuseStep 2452171 = 3678257) B3678257
theorem B3269561 : Blo 2179435 3269561 := bstep (se 2 (by rfl) ⟨1226085, by rfl⟩ : syracuseStep 3269561 = 2452171) B2452171
theorem B2179707 : Blo 2179435 2179707 := bstep (se 1 (by rfl) ⟨1634780, by rfl⟩ : syracuseStep 2179707 = 3269561) B3269561
theorem B4665037 : Blo 2179435 4665037 := bbase (se 3 (by rfl) ⟨874694, by rfl⟩ : syracuseStep 4665037 = 1749389) (by norm_num)
theorem B6220049 : Blo 2179435 6220049 := bstep (se 2 (by rfl) ⟨2332518, by rfl⟩ : syracuseStep 6220049 = 4665037) B4665037
theorem B16586797 : Blo 2179435 16586797 := bstep (se 3 (by rfl) ⟨3110024, by rfl⟩ : syracuseStep 16586797 = 6220049) B6220049
theorem B22115729 : Blo 2179435 22115729 := bstep (se 2 (by rfl) ⟨8293398, by rfl⟩ : syracuseStep 22115729 = 16586797) B16586797
theorem B14743819 : Blo 2179435 14743819 := bstep (se 1 (by rfl) ⟨11057864, by rfl⟩ : syracuseStep 14743819 = 22115729) B22115729
theorem B19658425 : Blo 2179435 19658425 := bstep (se 2 (by rfl) ⟨7371909, by rfl⟩ : syracuseStep 19658425 = 14743819) B14743819
theorem B26211233 : Blo 2179435 26211233 := bstep (se 2 (by rfl) ⟨9829212, by rfl⟩ : syracuseStep 26211233 = 19658425) B19658425
theorem B69896621 : Blo 2179435 69896621 := bstep (se 3 (by rfl) ⟨13105616, by rfl⟩ : syracuseStep 69896621 = 26211233) B26211233
theorem B186390989 : Blo 2179435 186390989 := bstep (se 3 (by rfl) ⟨34948310, by rfl⟩ : syracuseStep 186390989 = 69896621) B69896621
theorem B124260659 : Blo 2179435 124260659 := bstep (se 1 (by rfl) ⟨93195494, by rfl⟩ : syracuseStep 124260659 = 186390989) B186390989
theorem B82840439 : Blo 2179435 82840439 := bstep (se 1 (by rfl) ⟨62130329, by rfl⟩ : syracuseStep 82840439 = 124260659) B124260659
theorem B220907837 : Blo 2179435 220907837 := bstep (se 3 (by rfl) ⟨41420219, by rfl⟩ : syracuseStep 220907837 = 82840439) B82840439
theorem B589087565 : Blo 2179435 589087565 := bstep (se 3 (by rfl) ⟨110453918, by rfl⟩ : syracuseStep 589087565 = 220907837) B220907837
theorem B392725043 : Blo 2179435 392725043 := bstep (se 1 (by rfl) ⟨294543782, by rfl⟩ : syracuseStep 392725043 = 589087565) B589087565
theorem B261816695 : Blo 2179435 261816695 := bstep (se 1 (by rfl) ⟨196362521, by rfl⟩ : syracuseStep 261816695 = 392725043) B392725043
theorem B174544463 : Blo 2179435 174544463 := bstep (se 1 (by rfl) ⟨130908347, by rfl⟩ : syracuseStep 174544463 = 261816695) B261816695
theorem B116362975 : Blo 2179435 116362975 := bstep (se 1 (by rfl) ⟨87272231, by rfl⟩ : syracuseStep 116362975 = 174544463) B174544463
theorem B155150633 : Blo 2179435 155150633 := bstep (se 2 (by rfl) ⟨58181487, by rfl⟩ : syracuseStep 155150633 = 116362975) B116362975
theorem B103433755 : Blo 2179435 103433755 := bstep (se 1 (by rfl) ⟨77575316, by rfl⟩ : syracuseStep 103433755 = 155150633) B155150633
theorem B137911673 : Blo 2179435 137911673 := bstep (se 2 (by rfl) ⟨51716877, by rfl⟩ : syracuseStep 137911673 = 103433755) B103433755
theorem B91941115 : Blo 2179435 91941115 := bstep (se 1 (by rfl) ⟨68955836, by rfl⟩ : syracuseStep 91941115 = 137911673) B137911673
theorem B122588153 : Blo 2179435 122588153 := bstep (se 2 (by rfl) ⟨45970557, by rfl⟩ : syracuseStep 122588153 = 91941115) B91941115
theorem B81725435 : Blo 2179435 81725435 := bstep (se 1 (by rfl) ⟨61294076, by rfl⟩ : syracuseStep 81725435 = 122588153) B122588153
theorem B54483623 : Blo 2179435 54483623 := bstep (se 1 (by rfl) ⟨40862717, by rfl⟩ : syracuseStep 54483623 = 81725435) B81725435
theorem B36322415 : Blo 2179435 36322415 := bstep (se 1 (by rfl) ⟨27241811, by rfl⟩ : syracuseStep 36322415 = 54483623) B54483623
theorem B24214943 : Blo 2179435 24214943 := bstep (se 1 (by rfl) ⟨18161207, by rfl⟩ : syracuseStep 24214943 = 36322415) B36322415
theorem B16143295 : Blo 2179435 16143295 := bstep (se 1 (by rfl) ⟨12107471, by rfl⟩ : syracuseStep 16143295 = 24214943) B24214943
theorem B21524393 : Blo 2179435 21524393 := bstep (se 2 (by rfl) ⟨8071647, by rfl⟩ : syracuseStep 21524393 = 16143295) B16143295
theorem B14349595 : Blo 2179435 14349595 := bstep (se 1 (by rfl) ⟨10762196, by rfl⟩ : syracuseStep 14349595 = 21524393) B21524393
theorem B19132793 : Blo 2179435 19132793 := bstep (se 2 (by rfl) ⟨7174797, by rfl⟩ : syracuseStep 19132793 = 14349595) B14349595
theorem B12755195 : Blo 2179435 12755195 := bstep (se 1 (by rfl) ⟨9566396, by rfl⟩ : syracuseStep 12755195 = 19132793) B19132793
theorem B8503463 : Blo 2179435 8503463 := bstep (se 1 (by rfl) ⟨6377597, by rfl⟩ : syracuseStep 8503463 = 12755195) B12755195
theorem B5668975 : Blo 2179435 5668975 := bstep (se 1 (by rfl) ⟨4251731, by rfl⟩ : syracuseStep 5668975 = 8503463) B8503463
theorem B7558633 : Blo 2179435 7558633 := bstep (se 2 (by rfl) ⟨2834487, by rfl⟩ : syracuseStep 7558633 = 5668975) B5668975
theorem B10078177 : Blo 2179435 10078177 := bstep (se 2 (by rfl) ⟨3779316, by rfl⟩ : syracuseStep 10078177 = 7558633) B7558633
theorem B13437569 : Blo 2179435 13437569 := bstep (se 2 (by rfl) ⟨5039088, by rfl⟩ : syracuseStep 13437569 = 10078177) B10078177
theorem B8958379 : Blo 2179435 8958379 := bstep (se 1 (by rfl) ⟨6718784, by rfl⟩ : syracuseStep 8958379 = 13437569) B13437569
theorem B11944505 : Blo 2179435 11944505 := bstep (se 2 (by rfl) ⟨4479189, by rfl⟩ : syracuseStep 11944505 = 8958379) B8958379
theorem B31852013 : Blo 2179435 31852013 := bstep (se 3 (by rfl) ⟨5972252, by rfl⟩ : syracuseStep 31852013 = 11944505) B11944505
theorem B84938701 : Blo 2179435 84938701 := bstep (se 3 (by rfl) ⟨15926006, by rfl⟩ : syracuseStep 84938701 = 31852013) B31852013
theorem B113251601 : Blo 2179435 113251601 := bstep (se 2 (by rfl) ⟨42469350, by rfl⟩ : syracuseStep 113251601 = 84938701) B84938701
theorem B75501067 : Blo 2179435 75501067 := bstep (se 1 (by rfl) ⟨56625800, by rfl⟩ : syracuseStep 75501067 = 113251601) B113251601
theorem B100668089 : Blo 2179435 100668089 := bstep (se 2 (by rfl) ⟨37750533, by rfl⟩ : syracuseStep 100668089 = 75501067) B75501067
theorem B67112059 : Blo 2179435 67112059 := bstep (se 1 (by rfl) ⟨50334044, by rfl⟩ : syracuseStep 67112059 = 100668089) B100668089
theorem B89482745 : Blo 2179435 89482745 := bstep (se 2 (by rfl) ⟨33556029, by rfl⟩ : syracuseStep 89482745 = 67112059) B67112059
theorem B238620653 : Blo 2179435 238620653 := bstep (se 3 (by rfl) ⟨44741372, by rfl⟩ : syracuseStep 238620653 = 89482745) B89482745
theorem B159080435 : Blo 2179435 159080435 := bstep (se 1 (by rfl) ⟨119310326, by rfl⟩ : syracuseStep 159080435 = 238620653) B238620653
theorem B106053623 : Blo 2179435 106053623 := bstep (se 1 (by rfl) ⟨79540217, by rfl⟩ : syracuseStep 106053623 = 159080435) B159080435
theorem B70702415 : Blo 2179435 70702415 := bstep (se 1 (by rfl) ⟨53026811, by rfl⟩ : syracuseStep 70702415 = 106053623) B106053623
theorem B47134943 : Blo 2179435 47134943 := bstep (se 1 (by rfl) ⟨35351207, by rfl⟩ : syracuseStep 47134943 = 70702415) B70702415
theorem B31423295 : Blo 2179435 31423295 := bstep (se 1 (by rfl) ⟨23567471, by rfl⟩ : syracuseStep 31423295 = 47134943) B47134943
theorem B20948863 : Blo 2179435 20948863 := bstep (se 1 (by rfl) ⟨15711647, by rfl⟩ : syracuseStep 20948863 = 31423295) B31423295
theorem B27931817 : Blo 2179435 27931817 := bstep (se 2 (by rfl) ⟨10474431, by rfl⟩ : syracuseStep 27931817 = 20948863) B20948863
theorem B18621211 : Blo 2179435 18621211 := bstep (se 1 (by rfl) ⟨13965908, by rfl⟩ : syracuseStep 18621211 = 27931817) B27931817
theorem B24828281 : Blo 2179435 24828281 := bstep (se 2 (by rfl) ⟨9310605, by rfl⟩ : syracuseStep 24828281 = 18621211) B18621211
theorem B16552187 : Blo 2179435 16552187 := bstep (se 1 (by rfl) ⟨12414140, by rfl⟩ : syracuseStep 16552187 = 24828281) B24828281
theorem B11034791 : Blo 2179435 11034791 := bstep (se 1 (by rfl) ⟨8276093, by rfl⟩ : syracuseStep 11034791 = 16552187) B16552187
theorem B7356527 : Blo 2179435 7356527 := bstep (se 1 (by rfl) ⟨5517395, by rfl⟩ : syracuseStep 7356527 = 11034791) B11034791
theorem B4904351 : Blo 2179435 4904351 := bstep (se 1 (by rfl) ⟨3678263, by rfl⟩ : syracuseStep 4904351 = 7356527) B7356527
theorem B3269567 : Blo 2179435 3269567 := bstep (se 1 (by rfl) ⟨2452175, by rfl⟩ : syracuseStep 3269567 = 4904351) B4904351
theorem B2179711 : Blo 2179435 2179711 := bstep (se 1 (by rfl) ⟨1634783, by rfl⟩ : syracuseStep 2179711 = 3269567) B3269567
theorem B3269573 : Blo 2179435 3269573 := bbase (se 4 (by rfl) ⟨306522, by rfl⟩ : syracuseStep 3269573 = 613045) (by norm_num)
theorem B2179715 : Blo 2179435 2179715 := bstep (se 1 (by rfl) ⟨1634786, by rfl⟩ : syracuseStep 2179715 = 3269573) B3269573
theorem B3678277 : Blo 2179435 3678277 := bbase (se 4 (by rfl) ⟨344838, by rfl⟩ : syracuseStep 3678277 = 689677) (by norm_num)
theorem B4904369 : Blo 2179435 4904369 := bstep (se 2 (by rfl) ⟨1839138, by rfl⟩ : syracuseStep 4904369 = 3678277) B3678277
theorem B3269579 : Blo 2179435 3269579 := bstep (se 1 (by rfl) ⟨2452184, by rfl⟩ : syracuseStep 3269579 = 4904369) B4904369
theorem B2179719 : Blo 2179435 2179719 := bstep (se 1 (by rfl) ⟨1634789, by rfl⟩ : syracuseStep 2179719 = 3269579) B3269579
theorem B2452189 : Blo 2179435 2452189 := bbase (se 3 (by rfl) ⟨459785, by rfl⟩ : syracuseStep 2452189 = 919571) (by norm_num)
theorem B3269585 : Blo 2179435 3269585 := bstep (se 2 (by rfl) ⟨1226094, by rfl⟩ : syracuseStep 3269585 = 2452189) B2452189
theorem B2179723 : Blo 2179435 2179723 := bstep (se 1 (by rfl) ⟨1634792, by rfl⟩ : syracuseStep 2179723 = 3269585) B3269585
theorem B7356581 : Blo 2179435 7356581 := bbase (se 4 (by rfl) ⟨689679, by rfl⟩ : syracuseStep 7356581 = 1379359) (by norm_num)
theorem B4904387 : Blo 2179435 4904387 := bstep (se 1 (by rfl) ⟨3678290, by rfl⟩ : syracuseStep 4904387 = 7356581) B7356581
theorem B3269591 : Blo 2179435 3269591 := bstep (se 1 (by rfl) ⟨2452193, by rfl⟩ : syracuseStep 3269591 = 4904387) B4904387
theorem B2179727 : Blo 2179435 2179727 := bstep (se 1 (by rfl) ⟨1634795, by rfl⟩ : syracuseStep 2179727 = 3269591) B3269591
theorem B3269597 : Blo 2179435 3269597 := bbase (se 3 (by rfl) ⟨613049, by rfl⟩ : syracuseStep 3269597 = 1226099) (by norm_num)
theorem B2179731 : Blo 2179435 2179731 := bstep (se 1 (by rfl) ⟨1634798, by rfl⟩ : syracuseStep 2179731 = 3269597) B3269597
theorem B4904405 : Blo 2179435 4904405 := bbase (se 7 (by rfl) ⟨57473, by rfl⟩ : syracuseStep 4904405 = 114947) (by norm_num)
theorem B3269603 : Blo 2179435 3269603 := bstep (se 1 (by rfl) ⟨2452202, by rfl⟩ : syracuseStep 3269603 = 4904405) B4904405
theorem B2179735 : Blo 2179435 2179735 := bstep (se 1 (by rfl) ⟨1634801, by rfl⟩ : syracuseStep 2179735 = 3269603) B3269603
theorem B2796373 : Blo 2179435 2796373 := bbase (se 9 (by rfl) ⟨8192, by rfl⟩ : syracuseStep 2796373 = 16385) (by norm_num)
theorem B14913989 : Blo 2179435 14913989 := bstep (se 4 (by rfl) ⟨1398186, by rfl⟩ : syracuseStep 14913989 = 2796373) B2796373
theorem B9942659 : Blo 2179435 9942659 := bstep (se 1 (by rfl) ⟨7456994, by rfl⟩ : syracuseStep 9942659 = 14913989) B14913989
theorem B6628439 : Blo 2179435 6628439 := bstep (se 1 (by rfl) ⟨4971329, by rfl⟩ : syracuseStep 6628439 = 9942659) B9942659
theorem B4418959 : Blo 2179435 4418959 := bstep (se 1 (by rfl) ⟨3314219, by rfl⟩ : syracuseStep 4418959 = 6628439) B6628439
theorem B5891945 : Blo 2179435 5891945 := bstep (se 2 (by rfl) ⟨2209479, by rfl⟩ : syracuseStep 5891945 = 4418959) B4418959
theorem B15711853 : Blo 2179435 15711853 := bstep (se 3 (by rfl) ⟨2945972, by rfl⟩ : syracuseStep 15711853 = 5891945) B5891945
theorem B20949137 : Blo 2179435 20949137 := bstep (se 2 (by rfl) ⟨7855926, by rfl⟩ : syracuseStep 20949137 = 15711853) B15711853
theorem B13966091 : Blo 2179435 13966091 := bstep (se 1 (by rfl) ⟨10474568, by rfl⟩ : syracuseStep 13966091 = 20949137) B20949137
theorem B9310727 : Blo 2179435 9310727 := bstep (se 1 (by rfl) ⟨6983045, by rfl⟩ : syracuseStep 9310727 = 13966091) B13966091
theorem B6207151 : Blo 2179435 6207151 := bstep (se 1 (by rfl) ⟨4655363, by rfl⟩ : syracuseStep 6207151 = 9310727) B9310727
theorem B8276201 : Blo 2179435 8276201 := bstep (se 2 (by rfl) ⟨3103575, by rfl⟩ : syracuseStep 8276201 = 6207151) B6207151
theorem B5517467 : Blo 2179435 5517467 := bstep (se 1 (by rfl) ⟨4138100, by rfl⟩ : syracuseStep 5517467 = 8276201) B8276201
theorem B3678311 : Blo 2179435 3678311 := bstep (se 1 (by rfl) ⟨2758733, by rfl⟩ : syracuseStep 3678311 = 5517467) B5517467
theorem B2452207 : Blo 2179435 2452207 := bstep (se 1 (by rfl) ⟨1839155, by rfl⟩ : syracuseStep 2452207 = 3678311) B3678311
theorem B3269609 : Blo 2179435 3269609 := bstep (se 2 (by rfl) ⟨1226103, by rfl⟩ : syracuseStep 3269609 = 2452207) B2452207
theorem B2179739 : Blo 2179435 2179739 := bstep (se 1 (by rfl) ⟨1634804, by rfl⟩ : syracuseStep 2179739 = 3269609) B3269609
theorem B5237293 : Blo 2179435 5237293 := bbase (se 3 (by rfl) ⟨981992, by rfl⟩ : syracuseStep 5237293 = 1963985) (by norm_num)
theorem B6983057 : Blo 2179435 6983057 := bstep (se 2 (by rfl) ⟨2618646, by rfl⟩ : syracuseStep 6983057 = 5237293) B5237293
theorem B18621485 : Blo 2179435 18621485 := bstep (se 3 (by rfl) ⟨3491528, by rfl⟩ : syracuseStep 18621485 = 6983057) B6983057
theorem B12414323 : Blo 2179435 12414323 := bstep (se 1 (by rfl) ⟨9310742, by rfl⟩ : syracuseStep 12414323 = 18621485) B18621485
theorem B8276215 : Blo 2179435 8276215 := bstep (se 1 (by rfl) ⟨6207161, by rfl⟩ : syracuseStep 8276215 = 12414323) B12414323
theorem B11034953 : Blo 2179435 11034953 := bstep (se 2 (by rfl) ⟨4138107, by rfl⟩ : syracuseStep 11034953 = 8276215) B8276215
theorem B7356635 : Blo 2179435 7356635 := bstep (se 1 (by rfl) ⟨5517476, by rfl⟩ : syracuseStep 7356635 = 11034953) B11034953
theorem B4904423 : Blo 2179435 4904423 := bstep (se 1 (by rfl) ⟨3678317, by rfl⟩ : syracuseStep 4904423 = 7356635) B7356635
theorem B3269615 : Blo 2179435 3269615 := bstep (se 1 (by rfl) ⟨2452211, by rfl⟩ : syracuseStep 3269615 = 4904423) B4904423
theorem B2179743 : Blo 2179435 2179743 := bstep (se 1 (by rfl) ⟨1634807, by rfl⟩ : syracuseStep 2179743 = 3269615) B3269615
theorem B3269621 : Blo 2179435 3269621 := bbase (se 5 (by rfl) ⟨153263, by rfl⟩ : syracuseStep 3269621 = 306527) (by norm_num)
theorem B2179747 : Blo 2179435 2179747 := bstep (se 1 (by rfl) ⟨1634810, by rfl⟩ : syracuseStep 2179747 = 3269621) B3269621
theorem B4655389 : Blo 2179435 4655389 := bbase (se 3 (by rfl) ⟨872885, by rfl⟩ : syracuseStep 4655389 = 1745771) (by norm_num)
theorem B6207185 : Blo 2179435 6207185 := bstep (se 2 (by rfl) ⟨2327694, by rfl⟩ : syracuseStep 6207185 = 4655389) B4655389
theorem B4138123 : Blo 2179435 4138123 := bstep (se 1 (by rfl) ⟨3103592, by rfl⟩ : syracuseStep 4138123 = 6207185) B6207185
theorem B5517497 : Blo 2179435 5517497 := bstep (se 2 (by rfl) ⟨2069061, by rfl⟩ : syracuseStep 5517497 = 4138123) B4138123
theorem B3678331 : Blo 2179435 3678331 := bstep (se 1 (by rfl) ⟨2758748, by rfl⟩ : syracuseStep 3678331 = 5517497) B5517497
theorem B4904441 : Blo 2179435 4904441 := bstep (se 2 (by rfl) ⟨1839165, by rfl⟩ : syracuseStep 4904441 = 3678331) B3678331
theorem B3269627 : Blo 2179435 3269627 := bstep (se 1 (by rfl) ⟨2452220, by rfl⟩ : syracuseStep 3269627 = 4904441) B4904441
theorem B2179751 : Blo 2179435 2179751 := bstep (se 1 (by rfl) ⟨1634813, by rfl⟩ : syracuseStep 2179751 = 3269627) B3269627
theorem B2452225 : Blo 2179435 2452225 := bbase (se 2 (by rfl) ⟨919584, by rfl⟩ : syracuseStep 2452225 = 1839169) (by norm_num)
theorem B3269633 : Blo 2179435 3269633 := bstep (se 2 (by rfl) ⟨1226112, by rfl⟩ : syracuseStep 3269633 = 2452225) B2452225
theorem B2179755 : Blo 2179435 2179755 := bstep (se 1 (by rfl) ⟨1634816, by rfl⟩ : syracuseStep 2179755 = 3269633) B3269633
theorem B5517517 : Blo 2179435 5517517 := bbase (se 3 (by rfl) ⟨1034534, by rfl⟩ : syracuseStep 5517517 = 2069069) (by norm_num)
theorem B7356689 : Blo 2179435 7356689 := bstep (se 2 (by rfl) ⟨2758758, by rfl⟩ : syracuseStep 7356689 = 5517517) B5517517
theorem B4904459 : Blo 2179435 4904459 := bstep (se 1 (by rfl) ⟨3678344, by rfl⟩ : syracuseStep 4904459 = 7356689) B7356689
theorem B3269639 : Blo 2179435 3269639 := bstep (se 1 (by rfl) ⟨2452229, by rfl⟩ : syracuseStep 3269639 = 4904459) B4904459
theorem B2179759 : Blo 2179435 2179759 := bstep (se 1 (by rfl) ⟨1634819, by rfl⟩ : syracuseStep 2179759 = 3269639) B3269639
theorem B3269645 : Blo 2179435 3269645 := bbase (se 3 (by rfl) ⟨613058, by rfl⟩ : syracuseStep 3269645 = 1226117) (by norm_num)
theorem B2179763 : Blo 2179435 2179763 := bstep (se 1 (by rfl) ⟨1634822, by rfl⟩ : syracuseStep 2179763 = 3269645) B3269645
theorem B4904477 : Blo 2179435 4904477 := bbase (se 3 (by rfl) ⟨919589, by rfl⟩ : syracuseStep 4904477 = 1839179) (by norm_num)
theorem B3269651 : Blo 2179435 3269651 := bstep (se 1 (by rfl) ⟨2452238, by rfl⟩ : syracuseStep 3269651 = 4904477) B4904477
theorem B2179767 : Blo 2179435 2179767 := bstep (se 1 (by rfl) ⟨1634825, by rfl⟩ : syracuseStep 2179767 = 3269651) B3269651
theorem B3678365 : Blo 2179435 3678365 := bbase (se 3 (by rfl) ⟨689693, by rfl⟩ : syracuseStep 3678365 = 1379387) (by norm_num)
theorem B2452243 : Blo 2179435 2452243 := bstep (se 1 (by rfl) ⟨1839182, by rfl⟩ : syracuseStep 2452243 = 3678365) B3678365
theorem B3269657 : Blo 2179435 3269657 := bstep (se 2 (by rfl) ⟨1226121, by rfl⟩ : syracuseStep 3269657 = 2452243) B2452243
theorem B2179771 : Blo 2179435 2179771 := bstep (se 1 (by rfl) ⟨1634828, by rfl⟩ : syracuseStep 2179771 = 3269657) B3269657
theorem B2239661 : Blo 2179435 2239661 := bbase (se 3 (by rfl) ⟨419936, by rfl⟩ : syracuseStep 2239661 = 839873) (by norm_num)
theorem B5972429 : Blo 2179435 5972429 := bstep (se 3 (by rfl) ⟨1119830, by rfl⟩ : syracuseStep 5972429 = 2239661) B2239661
theorem B3981619 : Blo 2179435 3981619 := bstep (se 1 (by rfl) ⟨2986214, by rfl⟩ : syracuseStep 3981619 = 5972429) B5972429
theorem B21235301 : Blo 2179435 21235301 := bstep (se 4 (by rfl) ⟨1990809, by rfl⟩ : syracuseStep 21235301 = 3981619) B3981619
theorem B14156867 : Blo 2179435 14156867 := bstep (se 1 (by rfl) ⟨10617650, by rfl⟩ : syracuseStep 14156867 = 21235301) B21235301
theorem B37751645 : Blo 2179435 37751645 := bstep (se 3 (by rfl) ⟨7078433, by rfl⟩ : syracuseStep 37751645 = 14156867) B14156867
theorem B25167763 : Blo 2179435 25167763 := bstep (se 1 (by rfl) ⟨18875822, by rfl⟩ : syracuseStep 25167763 = 37751645) B37751645
theorem B33557017 : Blo 2179435 33557017 := bstep (se 2 (by rfl) ⟨12583881, by rfl⟩ : syracuseStep 33557017 = 25167763) B25167763
theorem B44742689 : Blo 2179435 44742689 := bstep (se 2 (by rfl) ⟨16778508, by rfl⟩ : syracuseStep 44742689 = 33557017) B33557017
theorem B29828459 : Blo 2179435 29828459 := bstep (se 1 (by rfl) ⟨22371344, by rfl⟩ : syracuseStep 29828459 = 44742689) B44742689
theorem B79542557 : Blo 2179435 79542557 := bstep (se 3 (by rfl) ⟨14914229, by rfl⟩ : syracuseStep 79542557 = 29828459) B29828459
theorem B53028371 : Blo 2179435 53028371 := bstep (se 1 (by rfl) ⟨39771278, by rfl⟩ : syracuseStep 53028371 = 79542557) B79542557
theorem B35352247 : Blo 2179435 35352247 := bstep (se 1 (by rfl) ⟨26514185, by rfl⟩ : syracuseStep 35352247 = 53028371) B53028371
theorem B47136329 : Blo 2179435 47136329 := bstep (se 2 (by rfl) ⟨17676123, by rfl⟩ : syracuseStep 47136329 = 35352247) B35352247
theorem B31424219 : Blo 2179435 31424219 := bstep (se 1 (by rfl) ⟨23568164, by rfl⟩ : syracuseStep 31424219 = 47136329) B47136329
theorem B20949479 : Blo 2179435 20949479 := bstep (se 1 (by rfl) ⟨15712109, by rfl⟩ : syracuseStep 20949479 = 31424219) B31424219
theorem B13966319 : Blo 2179435 13966319 := bstep (se 1 (by rfl) ⟨10474739, by rfl⟩ : syracuseStep 13966319 = 20949479) B20949479
theorem B9310879 : Blo 2179435 9310879 := bstep (se 1 (by rfl) ⟨6983159, by rfl⟩ : syracuseStep 9310879 = 13966319) B13966319
theorem B12414505 : Blo 2179435 12414505 := bstep (se 2 (by rfl) ⟨4655439, by rfl⟩ : syracuseStep 12414505 = 9310879) B9310879
theorem B16552673 : Blo 2179435 16552673 := bstep (se 2 (by rfl) ⟨6207252, by rfl⟩ : syracuseStep 16552673 = 12414505) B12414505
theorem B11035115 : Blo 2179435 11035115 := bstep (se 1 (by rfl) ⟨8276336, by rfl⟩ : syracuseStep 11035115 = 16552673) B16552673
theorem B7356743 : Blo 2179435 7356743 := bstep (se 1 (by rfl) ⟨5517557, by rfl⟩ : syracuseStep 7356743 = 11035115) B11035115
theorem B4904495 : Blo 2179435 4904495 := bstep (se 1 (by rfl) ⟨3678371, by rfl⟩ : syracuseStep 4904495 = 7356743) B7356743
theorem B3269663 : Blo 2179435 3269663 := bstep (se 1 (by rfl) ⟨2452247, by rfl⟩ : syracuseStep 3269663 = 4904495) B4904495
theorem B2179775 : Blo 2179435 2179775 := bstep (se 1 (by rfl) ⟨1634831, by rfl⟩ : syracuseStep 2179775 = 3269663) B3269663
theorem B3269669 : Blo 2179435 3269669 := bbase (se 4 (by rfl) ⟨306531, by rfl⟩ : syracuseStep 3269669 = 613063) (by norm_num)
theorem B2179779 : Blo 2179435 2179779 := bstep (se 1 (by rfl) ⟨1634834, by rfl⟩ : syracuseStep 2179779 = 3269669) B3269669
theorem B2758789 : Blo 2179435 2758789 := bbase (se 4 (by rfl) ⟨258636, by rfl⟩ : syracuseStep 2758789 = 517273) (by norm_num)
theorem B3678385 : Blo 2179435 3678385 := bstep (se 2 (by rfl) ⟨1379394, by rfl⟩ : syracuseStep 3678385 = 2758789) B2758789
theorem B4904513 : Blo 2179435 4904513 := bstep (se 2 (by rfl) ⟨1839192, by rfl⟩ : syracuseStep 4904513 = 3678385) B3678385
theorem B3269675 : Blo 2179435 3269675 := bstep (se 1 (by rfl) ⟨2452256, by rfl⟩ : syracuseStep 3269675 = 4904513) B4904513
theorem B2179783 : Blo 2179435 2179783 := bstep (se 1 (by rfl) ⟨1634837, by rfl⟩ : syracuseStep 2179783 = 3269675) B3269675
theorem B2452261 : Blo 2179435 2452261 := bbase (se 4 (by rfl) ⟨229899, by rfl⟩ : syracuseStep 2452261 = 459799) (by norm_num)
theorem B3269681 : Blo 2179435 3269681 := bstep (se 2 (by rfl) ⟨1226130, by rfl⟩ : syracuseStep 3269681 = 2452261) B2452261
theorem B2179787 : Blo 2179435 2179787 := bstep (se 1 (by rfl) ⟨1634840, by rfl⟩ : syracuseStep 2179787 = 3269681) B3269681
theorem B9310949 : Blo 2179435 9310949 := bbase (se 4 (by rfl) ⟨872901, by rfl⟩ : syracuseStep 9310949 = 1745803) (by norm_num)
theorem B6207299 : Blo 2179435 6207299 := bstep (se 1 (by rfl) ⟨4655474, by rfl⟩ : syracuseStep 6207299 = 9310949) B9310949
theorem B4138199 : Blo 2179435 4138199 := bstep (se 1 (by rfl) ⟨3103649, by rfl⟩ : syracuseStep 4138199 = 6207299) B6207299
theorem B2758799 : Blo 2179435 2758799 := bstep (se 1 (by rfl) ⟨2069099, by rfl⟩ : syracuseStep 2758799 = 4138199) B4138199
theorem B7356797 : Blo 2179435 7356797 := bstep (se 3 (by rfl) ⟨1379399, by rfl⟩ : syracuseStep 7356797 = 2758799) B2758799
theorem B4904531 : Blo 2179435 4904531 := bstep (se 1 (by rfl) ⟨3678398, by rfl⟩ : syracuseStep 4904531 = 7356797) B7356797
theorem B3269687 : Blo 2179435 3269687 := bstep (se 1 (by rfl) ⟨2452265, by rfl⟩ : syracuseStep 3269687 = 4904531) B4904531
theorem B2179791 : Blo 2179435 2179791 := bstep (se 1 (by rfl) ⟨1634843, by rfl⟩ : syracuseStep 2179791 = 3269687) B3269687
theorem B3269693 : Blo 2179435 3269693 := bbase (se 3 (by rfl) ⟨613067, by rfl⟩ : syracuseStep 3269693 = 1226135) (by norm_num)
theorem B2179795 : Blo 2179435 2179795 := bstep (se 1 (by rfl) ⟨1634846, by rfl⟩ : syracuseStep 2179795 = 3269693) B3269693
theorem B4904549 : Blo 2179435 4904549 := bbase (se 4 (by rfl) ⟨459801, by rfl⟩ : syracuseStep 4904549 = 919603) (by norm_num)
theorem B3269699 : Blo 2179435 3269699 := bstep (se 1 (by rfl) ⟨2452274, by rfl⟩ : syracuseStep 3269699 = 4904549) B4904549
theorem B2179799 : Blo 2179435 2179799 := bstep (se 1 (by rfl) ⟨1634849, by rfl⟩ : syracuseStep 2179799 = 3269699) B3269699
theorem B5517629 : Blo 2179435 5517629 := bbase (se 3 (by rfl) ⟨1034555, by rfl⟩ : syracuseStep 5517629 = 2069111) (by norm_num)
theorem B3678419 : Blo 2179435 3678419 := bstep (se 1 (by rfl) ⟨2758814, by rfl⟩ : syracuseStep 3678419 = 5517629) B5517629
theorem B2452279 : Blo 2179435 2452279 := bstep (se 1 (by rfl) ⟨1839209, by rfl⟩ : syracuseStep 2452279 = 3678419) B3678419
theorem B3269705 : Blo 2179435 3269705 := bstep (se 2 (by rfl) ⟨1226139, by rfl⟩ : syracuseStep 3269705 = 2452279) B2452279
theorem B2179803 : Blo 2179435 2179803 := bstep (se 1 (by rfl) ⟨1634852, by rfl⟩ : syracuseStep 2179803 = 3269705) B3269705
theorem B4138229 : Blo 2179435 4138229 := bbase (se 5 (by rfl) ⟨193979, by rfl⟩ : syracuseStep 4138229 = 387959) (by norm_num)
theorem B11035277 : Blo 2179435 11035277 := bstep (se 3 (by rfl) ⟨2069114, by rfl⟩ : syracuseStep 11035277 = 4138229) B4138229
theorem B7356851 : Blo 2179435 7356851 := bstep (se 1 (by rfl) ⟨5517638, by rfl⟩ : syracuseStep 7356851 = 11035277) B11035277
theorem B4904567 : Blo 2179435 4904567 := bstep (se 1 (by rfl) ⟨3678425, by rfl⟩ : syracuseStep 4904567 = 7356851) B7356851
theorem B3269711 : Blo 2179435 3269711 := bstep (se 1 (by rfl) ⟨2452283, by rfl⟩ : syracuseStep 3269711 = 4904567) B4904567
theorem B2179807 : Blo 2179435 2179807 := bstep (se 1 (by rfl) ⟨1634855, by rfl⟩ : syracuseStep 2179807 = 3269711) B3269711
theorem B3269717 : Blo 2179435 3269717 := bbase (se 8 (by rfl) ⟨19158, by rfl⟩ : syracuseStep 3269717 = 38317) (by norm_num)
theorem B2179811 : Blo 2179435 2179811 := bstep (se 1 (by rfl) ⟨1634858, by rfl⟩ : syracuseStep 2179811 = 3269717) B3269717
theorem B10474933 : Blo 2179435 10474933 := bbase (se 5 (by rfl) ⟨491012, by rfl⟩ : syracuseStep 10474933 = 982025) (by norm_num)
theorem B13966577 : Blo 2179435 13966577 := bstep (se 2 (by rfl) ⟨5237466, by rfl⟩ : syracuseStep 13966577 = 10474933) B10474933
theorem B9311051 : Blo 2179435 9311051 := bstep (se 1 (by rfl) ⟨6983288, by rfl⟩ : syracuseStep 9311051 = 13966577) B13966577
theorem B6207367 : Blo 2179435 6207367 := bstep (se 1 (by rfl) ⟨4655525, by rfl⟩ : syracuseStep 6207367 = 9311051) B9311051
theorem B8276489 : Blo 2179435 8276489 := bstep (se 2 (by rfl) ⟨3103683, by rfl⟩ : syracuseStep 8276489 = 6207367) B6207367
theorem B5517659 : Blo 2179435 5517659 := bstep (se 1 (by rfl) ⟨4138244, by rfl⟩ : syracuseStep 5517659 = 8276489) B8276489
theorem B3678439 : Blo 2179435 3678439 := bstep (se 1 (by rfl) ⟨2758829, by rfl⟩ : syracuseStep 3678439 = 5517659) B5517659
theorem B4904585 : Blo 2179435 4904585 := bstep (se 2 (by rfl) ⟨1839219, by rfl⟩ : syracuseStep 4904585 = 3678439) B3678439
theorem B3269723 : Blo 2179435 3269723 := bstep (se 1 (by rfl) ⟨2452292, by rfl⟩ : syracuseStep 3269723 = 4904585) B4904585
theorem B2179815 : Blo 2179435 2179815 := bstep (se 1 (by rfl) ⟨1634861, by rfl⟩ : syracuseStep 2179815 = 3269723) B3269723
theorem B2452297 : Blo 2179435 2452297 := bbase (se 2 (by rfl) ⟨919611, by rfl⟩ : syracuseStep 2452297 = 1839223) (by norm_num)
theorem B3269729 : Blo 2179435 3269729 := bstep (se 2 (by rfl) ⟨1226148, by rfl⟩ : syracuseStep 3269729 = 2452297) B2452297
theorem B2179819 : Blo 2179435 2179819 := bstep (se 1 (by rfl) ⟨1634864, by rfl⟩ : syracuseStep 2179819 = 3269729) B3269729
theorem B20949941 : Blo 2179435 20949941 := bbase (se 5 (by rfl) ⟨982028, by rfl⟩ : syracuseStep 20949941 = 1964057) (by norm_num)
theorem B13966627 : Blo 2179435 13966627 := bstep (se 1 (by rfl) ⟨10474970, by rfl⟩ : syracuseStep 13966627 = 20949941) B20949941
theorem B18622169 : Blo 2179435 18622169 := bstep (se 2 (by rfl) ⟨6983313, by rfl⟩ : syracuseStep 18622169 = 13966627) B13966627
theorem B12414779 : Blo 2179435 12414779 := bstep (se 1 (by rfl) ⟨9311084, by rfl⟩ : syracuseStep 12414779 = 18622169) B18622169
theorem B8276519 : Blo 2179435 8276519 := bstep (se 1 (by rfl) ⟨6207389, by rfl⟩ : syracuseStep 8276519 = 12414779) B12414779
theorem B5517679 : Blo 2179435 5517679 := bstep (se 1 (by rfl) ⟨4138259, by rfl⟩ : syracuseStep 5517679 = 8276519) B8276519
theorem B7356905 : Blo 2179435 7356905 := bstep (se 2 (by rfl) ⟨2758839, by rfl⟩ : syracuseStep 7356905 = 5517679) B5517679
theorem B4904603 : Blo 2179435 4904603 := bstep (se 1 (by rfl) ⟨3678452, by rfl⟩ : syracuseStep 4904603 = 7356905) B7356905
theorem B3269735 : Blo 2179435 3269735 := bstep (se 1 (by rfl) ⟨2452301, by rfl⟩ : syracuseStep 3269735 = 4904603) B4904603
theorem B2179823 : Blo 2179435 2179823 := bstep (se 1 (by rfl) ⟨1634867, by rfl⟩ : syracuseStep 2179823 = 3269735) B3269735
theorem B3269741 : Blo 2179435 3269741 := bbase (se 3 (by rfl) ⟨613076, by rfl⟩ : syracuseStep 3269741 = 1226153) (by norm_num)
theorem B2179827 : Blo 2179435 2179827 := bstep (se 1 (by rfl) ⟨1634870, by rfl⟩ : syracuseStep 2179827 = 3269741) B3269741
theorem B4904621 : Blo 2179435 4904621 := bbase (se 3 (by rfl) ⟨919616, by rfl⟩ : syracuseStep 4904621 = 1839233) (by norm_num)
theorem B3269747 : Blo 2179435 3269747 := bstep (se 1 (by rfl) ⟨2452310, by rfl⟩ : syracuseStep 3269747 = 4904621) B4904621
theorem B2179831 : Blo 2179435 2179831 := bstep (se 1 (by rfl) ⟨1634873, by rfl⟩ : syracuseStep 2179831 = 3269747) B3269747
theorem B3491677 : Blo 2179435 3491677 := bbase (se 3 (by rfl) ⟨654689, by rfl⟩ : syracuseStep 3491677 = 1309379) (by norm_num)
theorem B4655569 : Blo 2179435 4655569 := bstep (se 2 (by rfl) ⟨1745838, by rfl⟩ : syracuseStep 4655569 = 3491677) B3491677
theorem B6207425 : Blo 2179435 6207425 := bstep (se 2 (by rfl) ⟨2327784, by rfl⟩ : syracuseStep 6207425 = 4655569) B4655569
theorem B4138283 : Blo 2179435 4138283 := bstep (se 1 (by rfl) ⟨3103712, by rfl⟩ : syracuseStep 4138283 = 6207425) B6207425
theorem B2758855 : Blo 2179435 2758855 := bstep (se 1 (by rfl) ⟨2069141, by rfl⟩ : syracuseStep 2758855 = 4138283) B4138283
theorem B3678473 : Blo 2179435 3678473 := bstep (se 2 (by rfl) ⟨1379427, by rfl⟩ : syracuseStep 3678473 = 2758855) B2758855
theorem B2452315 : Blo 2179435 2452315 := bstep (se 1 (by rfl) ⟨1839236, by rfl⟩ : syracuseStep 2452315 = 3678473) B3678473
theorem B3269753 : Blo 2179435 3269753 := bstep (se 2 (by rfl) ⟨1226157, by rfl⟩ : syracuseStep 3269753 = 2452315) B2452315
theorem B2179835 : Blo 2179435 2179835 := bstep (se 1 (by rfl) ⟨1634876, by rfl⟩ : syracuseStep 2179835 = 3269753) B3269753
theorem B4971557 : Blo 2179435 4971557 := bbase (se 4 (by rfl) ⟨466083, by rfl⟩ : syracuseStep 4971557 = 932167) (by norm_num)
theorem B3314371 : Blo 2179435 3314371 := bstep (se 1 (by rfl) ⟨2485778, by rfl⟩ : syracuseStep 3314371 = 4971557) B4971557
theorem B4419161 : Blo 2179435 4419161 := bstep (se 2 (by rfl) ⟨1657185, by rfl⟩ : syracuseStep 4419161 = 3314371) B3314371
theorem B2946107 : Blo 2179435 2946107 := bstep (se 1 (by rfl) ⟨2209580, by rfl⟩ : syracuseStep 2946107 = 4419161) B4419161
theorem B7856285 : Blo 2179435 7856285 := bstep (se 3 (by rfl) ⟨1473053, by rfl⟩ : syracuseStep 7856285 = 2946107) B2946107
theorem B20950093 : Blo 2179435 20950093 := bstep (se 3 (by rfl) ⟨3928142, by rfl⟩ : syracuseStep 20950093 = 7856285) B7856285
theorem B27933457 : Blo 2179435 27933457 := bstep (se 2 (by rfl) ⟨10475046, by rfl⟩ : syracuseStep 27933457 = 20950093) B20950093
theorem B37244609 : Blo 2179435 37244609 := bstep (se 2 (by rfl) ⟨13966728, by rfl⟩ : syracuseStep 37244609 = 27933457) B27933457
theorem B24829739 : Blo 2179435 24829739 := bstep (se 1 (by rfl) ⟨18622304, by rfl⟩ : syracuseStep 24829739 = 37244609) B37244609
theorem B16553159 : Blo 2179435 16553159 := bstep (se 1 (by rfl) ⟨12414869, by rfl⟩ : syracuseStep 16553159 = 24829739) B24829739
theorem B11035439 : Blo 2179435 11035439 := bstep (se 1 (by rfl) ⟨8276579, by rfl⟩ : syracuseStep 11035439 = 16553159) B16553159
theorem B7356959 : Blo 2179435 7356959 := bstep (se 1 (by rfl) ⟨5517719, by rfl⟩ : syracuseStep 7356959 = 11035439) B11035439
theorem B4904639 : Blo 2179435 4904639 := bstep (se 1 (by rfl) ⟨3678479, by rfl⟩ : syracuseStep 4904639 = 7356959) B7356959
theorem B3269759 : Blo 2179435 3269759 := bstep (se 1 (by rfl) ⟨2452319, by rfl⟩ : syracuseStep 3269759 = 4904639) B4904639
theorem B2179839 : Blo 2179435 2179839 := bstep (se 1 (by rfl) ⟨1634879, by rfl⟩ : syracuseStep 2179839 = 3269759) B3269759
theorem B3269765 : Blo 2179435 3269765 := bbase (se 4 (by rfl) ⟨306540, by rfl⟩ : syracuseStep 3269765 = 613081) (by norm_num)
theorem B2179843 : Blo 2179435 2179843 := bstep (se 1 (by rfl) ⟨1634882, by rfl⟩ : syracuseStep 2179843 = 3269765) B3269765
theorem B3678493 : Blo 2179435 3678493 := bbase (se 3 (by rfl) ⟨689717, by rfl⟩ : syracuseStep 3678493 = 1379435) (by norm_num)
theorem B4904657 : Blo 2179435 4904657 := bstep (se 2 (by rfl) ⟨1839246, by rfl⟩ : syracuseStep 4904657 = 3678493) B3678493
theorem B3269771 : Blo 2179435 3269771 := bstep (se 1 (by rfl) ⟨2452328, by rfl⟩ : syracuseStep 3269771 = 4904657) B4904657
theorem B2179847 : Blo 2179435 2179847 := bstep (se 1 (by rfl) ⟨1634885, by rfl⟩ : syracuseStep 2179847 = 3269771) B3269771
theorem B2452333 : Blo 2179435 2452333 := bbase (se 3 (by rfl) ⟨459812, by rfl⟩ : syracuseStep 2452333 = 919625) (by norm_num)
theorem B3269777 : Blo 2179435 3269777 := bstep (se 2 (by rfl) ⟨1226166, by rfl⟩ : syracuseStep 3269777 = 2452333) B2452333
theorem B2179851 : Blo 2179435 2179851 := bstep (se 1 (by rfl) ⟨1634888, by rfl⟩ : syracuseStep 2179851 = 3269777) B3269777
theorem B7357013 : Blo 2179435 7357013 := bbase (se 8 (by rfl) ⟨43107, by rfl⟩ : syracuseStep 7357013 = 86215) (by norm_num)
theorem B4904675 : Blo 2179435 4904675 := bstep (se 1 (by rfl) ⟨3678506, by rfl⟩ : syracuseStep 4904675 = 7357013) B7357013
theorem B3269783 : Blo 2179435 3269783 := bstep (se 1 (by rfl) ⟨2452337, by rfl⟩ : syracuseStep 3269783 = 4904675) B4904675
theorem B2179855 : Blo 2179435 2179855 := bstep (se 1 (by rfl) ⟨1634891, by rfl⟩ : syracuseStep 2179855 = 3269783) B3269783
theorem B3269789 : Blo 2179435 3269789 := bbase (se 3 (by rfl) ⟨613085, by rfl⟩ : syracuseStep 3269789 = 1226171) (by norm_num)
theorem B2179859 : Blo 2179435 2179859 := bstep (se 1 (by rfl) ⟨1634894, by rfl⟩ : syracuseStep 2179859 = 3269789) B3269789
theorem B4904693 : Blo 2179435 4904693 := bbase (se 5 (by rfl) ⟨229907, by rfl⟩ : syracuseStep 4904693 = 459815) (by norm_num)
theorem B3269795 : Blo 2179435 3269795 := bstep (se 1 (by rfl) ⟨2452346, by rfl⟩ : syracuseStep 3269795 = 4904693) B4904693
theorem B2179863 : Blo 2179435 2179863 := bstep (se 1 (by rfl) ⟨1634897, by rfl⟩ : syracuseStep 2179863 = 3269795) B3269795
theorem B16779221 : Blo 2179435 16779221 := bbase (se 7 (by rfl) ⟨196631, by rfl⟩ : syracuseStep 16779221 = 393263) (by norm_num)
theorem B11186147 : Blo 2179435 11186147 := bstep (se 1 (by rfl) ⟨8389610, by rfl⟩ : syracuseStep 11186147 = 16779221) B16779221
theorem B7457431 : Blo 2179435 7457431 := bstep (se 1 (by rfl) ⟨5593073, by rfl⟩ : syracuseStep 7457431 = 11186147) B11186147
theorem B9943241 : Blo 2179435 9943241 := bstep (se 2 (by rfl) ⟨3728715, by rfl⟩ : syracuseStep 9943241 = 7457431) B7457431
theorem B26515309 : Blo 2179435 26515309 := bstep (se 3 (by rfl) ⟨4971620, by rfl⟩ : syracuseStep 26515309 = 9943241) B9943241
theorem B35353745 : Blo 2179435 35353745 := bstep (se 2 (by rfl) ⟨13257654, by rfl⟩ : syracuseStep 35353745 = 26515309) B26515309
theorem B23569163 : Blo 2179435 23569163 := bstep (se 1 (by rfl) ⟨17676872, by rfl⟩ : syracuseStep 23569163 = 35353745) B35353745
theorem B15712775 : Blo 2179435 15712775 := bstep (se 1 (by rfl) ⟨11784581, by rfl⟩ : syracuseStep 15712775 = 23569163) B23569163
theorem B10475183 : Blo 2179435 10475183 := bstep (se 1 (by rfl) ⟨7856387, by rfl⟩ : syracuseStep 10475183 = 15712775) B15712775
theorem B27933821 : Blo 2179435 27933821 := bstep (se 3 (by rfl) ⟨5237591, by rfl⟩ : syracuseStep 27933821 = 10475183) B10475183
theorem B18622547 : Blo 2179435 18622547 := bstep (se 1 (by rfl) ⟨13966910, by rfl⟩ : syracuseStep 18622547 = 27933821) B27933821
theorem B12415031 : Blo 2179435 12415031 := bstep (se 1 (by rfl) ⟨9311273, by rfl⟩ : syracuseStep 12415031 = 18622547) B18622547
theorem B8276687 : Blo 2179435 8276687 := bstep (se 1 (by rfl) ⟨6207515, by rfl⟩ : syracuseStep 8276687 = 12415031) B12415031
theorem B5517791 : Blo 2179435 5517791 := bstep (se 1 (by rfl) ⟨4138343, by rfl⟩ : syracuseStep 5517791 = 8276687) B8276687
theorem B3678527 : Blo 2179435 3678527 := bstep (se 1 (by rfl) ⟨2758895, by rfl⟩ : syracuseStep 3678527 = 5517791) B5517791
theorem B2452351 : Blo 2179435 2452351 := bstep (se 1 (by rfl) ⟨1839263, by rfl⟩ : syracuseStep 2452351 = 3678527) B3678527
theorem B3269801 : Blo 2179435 3269801 := bstep (se 2 (by rfl) ⟨1226175, by rfl⟩ : syracuseStep 3269801 = 2452351) B2452351
theorem B2179867 : Blo 2179435 2179867 := bstep (se 1 (by rfl) ⟨1634900, by rfl⟩ : syracuseStep 2179867 = 3269801) B3269801
theorem B4655645 : Blo 2179435 4655645 := bbase (se 3 (by rfl) ⟨872933, by rfl⟩ : syracuseStep 4655645 = 1745867) (by norm_num)
theorem B3103763 : Blo 2179435 3103763 := bstep (se 1 (by rfl) ⟨2327822, by rfl⟩ : syracuseStep 3103763 = 4655645) B4655645
theorem B8276701 : Blo 2179435 8276701 := bstep (se 3 (by rfl) ⟨1551881, by rfl⟩ : syracuseStep 8276701 = 3103763) B3103763
theorem B11035601 : Blo 2179435 11035601 := bstep (se 2 (by rfl) ⟨4138350, by rfl⟩ : syracuseStep 11035601 = 8276701) B8276701
theorem B7357067 : Blo 2179435 7357067 := bstep (se 1 (by rfl) ⟨5517800, by rfl⟩ : syracuseStep 7357067 = 11035601) B11035601
theorem B4904711 : Blo 2179435 4904711 := bstep (se 1 (by rfl) ⟨3678533, by rfl⟩ : syracuseStep 4904711 = 7357067) B7357067
theorem B3269807 : Blo 2179435 3269807 := bstep (se 1 (by rfl) ⟨2452355, by rfl⟩ : syracuseStep 3269807 = 4904711) B4904711
theorem B2179871 : Blo 2179435 2179871 := bstep (se 1 (by rfl) ⟨1634903, by rfl⟩ : syracuseStep 2179871 = 3269807) B3269807
theorem B3269813 : Blo 2179435 3269813 := bbase (se 5 (by rfl) ⟨153272, by rfl⟩ : syracuseStep 3269813 = 306545) (by norm_num)
theorem B2179875 : Blo 2179435 2179875 := bstep (se 1 (by rfl) ⟨1634906, by rfl⟩ : syracuseStep 2179875 = 3269813) B3269813
theorem B5517821 : Blo 2179435 5517821 := bbase (se 3 (by rfl) ⟨1034591, by rfl⟩ : syracuseStep 5517821 = 2069183) (by norm_num)
theorem B3678547 : Blo 2179435 3678547 := bstep (se 1 (by rfl) ⟨2758910, by rfl⟩ : syracuseStep 3678547 = 5517821) B5517821
theorem B4904729 : Blo 2179435 4904729 := bstep (se 2 (by rfl) ⟨1839273, by rfl⟩ : syracuseStep 4904729 = 3678547) B3678547
theorem B3269819 : Blo 2179435 3269819 := bstep (se 1 (by rfl) ⟨2452364, by rfl⟩ : syracuseStep 3269819 = 4904729) B4904729
theorem B2179879 : Blo 2179435 2179879 := bstep (se 1 (by rfl) ⟨1634909, by rfl⟩ : syracuseStep 2179879 = 3269819) B3269819
theorem B2452369 : Blo 2179435 2452369 := bbase (se 2 (by rfl) ⟨919638, by rfl⟩ : syracuseStep 2452369 = 1839277) (by norm_num)
theorem B3269825 : Blo 2179435 3269825 := bstep (se 2 (by rfl) ⟨1226184, by rfl⟩ : syracuseStep 3269825 = 2452369) B2452369
theorem B2179883 : Blo 2179435 2179883 := bstep (se 1 (by rfl) ⟨1634912, by rfl⟩ : syracuseStep 2179883 = 3269825) B3269825
theorem B4138381 : Blo 2179435 4138381 := bbase (se 3 (by rfl) ⟨775946, by rfl⟩ : syracuseStep 4138381 = 1551893) (by norm_num)
theorem B5517841 : Blo 2179435 5517841 := bstep (se 2 (by rfl) ⟨2069190, by rfl⟩ : syracuseStep 5517841 = 4138381) B4138381
theorem B7357121 : Blo 2179435 7357121 := bstep (se 2 (by rfl) ⟨2758920, by rfl⟩ : syracuseStep 7357121 = 5517841) B5517841
theorem B4904747 : Blo 2179435 4904747 := bstep (se 1 (by rfl) ⟨3678560, by rfl⟩ : syracuseStep 4904747 = 7357121) B7357121
theorem B3269831 : Blo 2179435 3269831 := bstep (se 1 (by rfl) ⟨2452373, by rfl⟩ : syracuseStep 3269831 = 4904747) B4904747
theorem B2179887 : Blo 2179435 2179887 := bstep (se 1 (by rfl) ⟨1634915, by rfl⟩ : syracuseStep 2179887 = 3269831) B3269831
theorem B3269837 : Blo 2179435 3269837 := bbase (se 3 (by rfl) ⟨613094, by rfl⟩ : syracuseStep 3269837 = 1226189) (by norm_num)
theorem B2179891 : Blo 2179435 2179891 := bstep (se 1 (by rfl) ⟨1634918, by rfl⟩ : syracuseStep 2179891 = 3269837) B3269837
theorem B4904765 : Blo 2179435 4904765 := bbase (se 3 (by rfl) ⟨919643, by rfl⟩ : syracuseStep 4904765 = 1839287) (by norm_num)
theorem B3269843 : Blo 2179435 3269843 := bstep (se 1 (by rfl) ⟨2452382, by rfl⟩ : syracuseStep 3269843 = 4904765) B4904765
theorem B2179895 : Blo 2179435 2179895 := bstep (se 1 (by rfl) ⟨1634921, by rfl⟩ : syracuseStep 2179895 = 3269843) B3269843
theorem B3678581 : Blo 2179435 3678581 := bbase (se 5 (by rfl) ⟨172433, by rfl⟩ : syracuseStep 3678581 = 344867) (by norm_num)
theorem B2452387 : Blo 2179435 2452387 := bstep (se 1 (by rfl) ⟨1839290, by rfl⟩ : syracuseStep 2452387 = 3678581) B3678581
theorem B3269849 : Blo 2179435 3269849 := bstep (se 2 (by rfl) ⟨1226193, by rfl⟩ : syracuseStep 3269849 = 2452387) B2452387
theorem B2179899 : Blo 2179435 2179899 := bstep (se 1 (by rfl) ⟨1634924, by rfl⟩ : syracuseStep 2179899 = 3269849) B3269849
theorem B5892389 : Blo 2179435 5892389 := bbase (se 4 (by rfl) ⟨552411, by rfl⟩ : syracuseStep 5892389 = 1104823) (by norm_num)
theorem B3928259 : Blo 2179435 3928259 := bstep (se 1 (by rfl) ⟨2946194, by rfl⟩ : syracuseStep 3928259 = 5892389) B5892389
theorem B2618839 : Blo 2179435 2618839 := bstep (se 1 (by rfl) ⟨1964129, by rfl⟩ : syracuseStep 2618839 = 3928259) B3928259
theorem B3491785 : Blo 2179435 3491785 := bstep (se 2 (by rfl) ⟨1309419, by rfl⟩ : syracuseStep 3491785 = 2618839) B2618839
theorem B4655713 : Blo 2179435 4655713 := bstep (se 2 (by rfl) ⟨1745892, by rfl⟩ : syracuseStep 4655713 = 3491785) B3491785
theorem B6207617 : Blo 2179435 6207617 := bstep (se 2 (by rfl) ⟨2327856, by rfl⟩ : syracuseStep 6207617 = 4655713) B4655713
theorem B16553645 : Blo 2179435 16553645 := bstep (se 3 (by rfl) ⟨3103808, by rfl⟩ : syracuseStep 16553645 = 6207617) B6207617
theorem B11035763 : Blo 2179435 11035763 := bstep (se 1 (by rfl) ⟨8276822, by rfl⟩ : syracuseStep 11035763 = 16553645) B16553645
theorem B7357175 : Blo 2179435 7357175 := bstep (se 1 (by rfl) ⟨5517881, by rfl⟩ : syracuseStep 7357175 = 11035763) B11035763
theorem B4904783 : Blo 2179435 4904783 := bstep (se 1 (by rfl) ⟨3678587, by rfl⟩ : syracuseStep 4904783 = 7357175) B7357175
theorem B3269855 : Blo 2179435 3269855 := bstep (se 1 (by rfl) ⟨2452391, by rfl⟩ : syracuseStep 3269855 = 4904783) B4904783
theorem B2179903 : Blo 2179435 2179903 := bstep (se 1 (by rfl) ⟨1634927, by rfl⟩ : syracuseStep 2179903 = 3269855) B3269855
theorem B3269861 : Blo 2179435 3269861 := bbase (se 4 (by rfl) ⟨306549, by rfl⟩ : syracuseStep 3269861 = 613099) (by norm_num)
theorem B2179907 : Blo 2179435 2179907 := bstep (se 1 (by rfl) ⟨1634930, by rfl⟩ : syracuseStep 2179907 = 3269861) B3269861
theorem B2618849 : Blo 2179435 2618849 := bbase (se 2 (by rfl) ⟨982068, by rfl⟩ : syracuseStep 2618849 = 1964137) (by norm_num)
theorem B6983597 : Blo 2179435 6983597 := bstep (se 3 (by rfl) ⟨1309424, by rfl⟩ : syracuseStep 6983597 = 2618849) B2618849
theorem B4655731 : Blo 2179435 4655731 := bstep (se 1 (by rfl) ⟨3491798, by rfl⟩ : syracuseStep 4655731 = 6983597) B6983597
theorem B6207641 : Blo 2179435 6207641 := bstep (se 2 (by rfl) ⟨2327865, by rfl⟩ : syracuseStep 6207641 = 4655731) B4655731
theorem B4138427 : Blo 2179435 4138427 := bstep (se 1 (by rfl) ⟨3103820, by rfl⟩ : syracuseStep 4138427 = 6207641) B6207641
theorem B2758951 : Blo 2179435 2758951 := bstep (se 1 (by rfl) ⟨2069213, by rfl⟩ : syracuseStep 2758951 = 4138427) B4138427
theorem B3678601 : Blo 2179435 3678601 := bstep (se 2 (by rfl) ⟨1379475, by rfl⟩ : syracuseStep 3678601 = 2758951) B2758951
theorem B4904801 : Blo 2179435 4904801 := bstep (se 2 (by rfl) ⟨1839300, by rfl⟩ : syracuseStep 4904801 = 3678601) B3678601
theorem B3269867 : Blo 2179435 3269867 := bstep (se 1 (by rfl) ⟨2452400, by rfl⟩ : syracuseStep 3269867 = 4904801) B4904801
theorem B2179911 : Blo 2179435 2179911 := bstep (se 1 (by rfl) ⟨1634933, by rfl⟩ : syracuseStep 2179911 = 3269867) B3269867
theorem B2452405 : Blo 2179435 2452405 := bbase (se 5 (by rfl) ⟨114956, by rfl⟩ : syracuseStep 2452405 = 229913) (by norm_num)
theorem B3269873 : Blo 2179435 3269873 := bstep (se 2 (by rfl) ⟨1226202, by rfl⟩ : syracuseStep 3269873 = 2452405) B2452405
theorem B2179915 : Blo 2179435 2179915 := bstep (se 1 (by rfl) ⟨1634936, by rfl⟩ : syracuseStep 2179915 = 3269873) B3269873
theorem B2758961 : Blo 2179435 2758961 := bbase (se 2 (by rfl) ⟨1034610, by rfl⟩ : syracuseStep 2758961 = 2069221) (by norm_num)
theorem B7357229 : Blo 2179435 7357229 := bstep (se 3 (by rfl) ⟨1379480, by rfl⟩ : syracuseStep 7357229 = 2758961) B2758961
theorem B4904819 : Blo 2179435 4904819 := bstep (se 1 (by rfl) ⟨3678614, by rfl⟩ : syracuseStep 4904819 = 7357229) B7357229
theorem B3269879 : Blo 2179435 3269879 := bstep (se 1 (by rfl) ⟨2452409, by rfl⟩ : syracuseStep 3269879 = 4904819) B4904819
theorem B2179919 : Blo 2179435 2179919 := bstep (se 1 (by rfl) ⟨1634939, by rfl⟩ : syracuseStep 2179919 = 3269879) B3269879
theorem B3269885 : Blo 2179435 3269885 := bbase (se 3 (by rfl) ⟨613103, by rfl⟩ : syracuseStep 3269885 = 1226207) (by norm_num)
theorem B2179923 : Blo 2179435 2179923 := bstep (se 1 (by rfl) ⟨1634942, by rfl⟩ : syracuseStep 2179923 = 3269885) B3269885
theorem B4904837 : Blo 2179435 4904837 := bbase (se 4 (by rfl) ⟨459828, by rfl⟩ : syracuseStep 4904837 = 919657) (by norm_num)
theorem B3269891 : Blo 2179435 3269891 := bstep (se 1 (by rfl) ⟨2452418, by rfl⟩ : syracuseStep 3269891 = 4904837) B4904837
theorem B2179927 : Blo 2179435 2179927 := bstep (se 1 (by rfl) ⟨1634945, by rfl⟩ : syracuseStep 2179927 = 3269891) B3269891
theorem B2485885 : Blo 2179435 2485885 := bbase (se 3 (by rfl) ⟨466103, by rfl⟩ : syracuseStep 2485885 = 932207) (by norm_num)
theorem B3314513 : Blo 2179435 3314513 := bstep (se 2 (by rfl) ⟨1242942, by rfl⟩ : syracuseStep 3314513 = 2485885) B2485885
theorem B2209675 : Blo 2179435 2209675 := bstep (se 1 (by rfl) ⟨1657256, by rfl⟩ : syracuseStep 2209675 = 3314513) B3314513
theorem B2946233 : Blo 2179435 2946233 := bstep (se 2 (by rfl) ⟨1104837, by rfl⟩ : syracuseStep 2946233 = 2209675) B2209675
theorem B7856621 : Blo 2179435 7856621 := bstep (se 3 (by rfl) ⟨1473116, by rfl⟩ : syracuseStep 7856621 = 2946233) B2946233
theorem B5237747 : Blo 2179435 5237747 := bstep (se 1 (by rfl) ⟨3928310, by rfl⟩ : syracuseStep 5237747 = 7856621) B7856621
theorem B3491831 : Blo 2179435 3491831 := bstep (se 1 (by rfl) ⟨2618873, by rfl⟩ : syracuseStep 3491831 = 5237747) B5237747
theorem B2327887 : Blo 2179435 2327887 := bstep (se 1 (by rfl) ⟨1745915, by rfl⟩ : syracuseStep 2327887 = 3491831) B3491831
theorem B3103849 : Blo 2179435 3103849 := bstep (se 2 (by rfl) ⟨1163943, by rfl⟩ : syracuseStep 3103849 = 2327887) B2327887
theorem B4138465 : Blo 2179435 4138465 := bstep (se 2 (by rfl) ⟨1551924, by rfl⟩ : syracuseStep 4138465 = 3103849) B3103849
theorem B5517953 : Blo 2179435 5517953 := bstep (se 2 (by rfl) ⟨2069232, by rfl⟩ : syracuseStep 5517953 = 4138465) B4138465
theorem B3678635 : Blo 2179435 3678635 := bstep (se 1 (by rfl) ⟨2758976, by rfl⟩ : syracuseStep 3678635 = 5517953) B5517953
theorem B2452423 : Blo 2179435 2452423 := bstep (se 1 (by rfl) ⟨1839317, by rfl⟩ : syracuseStep 2452423 = 3678635) B3678635
theorem B3269897 : Blo 2179435 3269897 := bstep (se 2 (by rfl) ⟨1226211, by rfl⟩ : syracuseStep 3269897 = 2452423) B2452423
theorem B2179931 : Blo 2179435 2179931 := bstep (se 1 (by rfl) ⟨1634948, by rfl⟩ : syracuseStep 2179931 = 3269897) B3269897
theorem B11035925 : Blo 2179435 11035925 := bbase (se 6 (by rfl) ⟨258654, by rfl⟩ : syracuseStep 11035925 = 517309) (by norm_num)
theorem B7357283 : Blo 2179435 7357283 := bstep (se 1 (by rfl) ⟨5517962, by rfl⟩ : syracuseStep 7357283 = 11035925) B11035925
theorem B4904855 : Blo 2179435 4904855 := bstep (se 1 (by rfl) ⟨3678641, by rfl⟩ : syracuseStep 4904855 = 7357283) B7357283
theorem B3269903 : Blo 2179435 3269903 := bstep (se 1 (by rfl) ⟨2452427, by rfl⟩ : syracuseStep 3269903 = 4904855) B4904855
theorem B2179935 : Blo 2179435 2179935 := bstep (se 1 (by rfl) ⟨1634951, by rfl⟩ : syracuseStep 2179935 = 3269903) B3269903
theorem B3269909 : Blo 2179435 3269909 := bbase (se 6 (by rfl) ⟨76638, by rfl⟩ : syracuseStep 3269909 = 153277) (by norm_num)
theorem B2179939 : Blo 2179435 2179939 := bstep (se 1 (by rfl) ⟨1634954, by rfl⟩ : syracuseStep 2179939 = 3269909) B3269909
theorem B2519813 : Blo 2179435 2519813 := bbase (se 4 (by rfl) ⟨236232, by rfl⟩ : syracuseStep 2519813 = 472465) (by norm_num)
theorem B6719501 : Blo 2179435 6719501 := bstep (se 3 (by rfl) ⟨1259906, by rfl⟩ : syracuseStep 6719501 = 2519813) B2519813
theorem B4479667 : Blo 2179435 4479667 := bstep (se 1 (by rfl) ⟨3359750, by rfl⟩ : syracuseStep 4479667 = 6719501) B6719501
theorem B95566229 : Blo 2179435 95566229 := bstep (se 6 (by rfl) ⟨2239833, by rfl⟩ : syracuseStep 95566229 = 4479667) B4479667
theorem B63710819 : Blo 2179435 63710819 := bstep (se 1 (by rfl) ⟨47783114, by rfl⟩ : syracuseStep 63710819 = 95566229) B95566229
theorem B42473879 : Blo 2179435 42473879 := bstep (se 1 (by rfl) ⟨31855409, by rfl⟩ : syracuseStep 42473879 = 63710819) B63710819
theorem B28315919 : Blo 2179435 28315919 := bstep (se 1 (by rfl) ⟨21236939, by rfl⟩ : syracuseStep 28315919 = 42473879) B42473879
theorem B18877279 : Blo 2179435 18877279 := bstep (se 1 (by rfl) ⟨14157959, by rfl⟩ : syracuseStep 18877279 = 28315919) B28315919
theorem B25169705 : Blo 2179435 25169705 := bstep (se 2 (by rfl) ⟨9438639, by rfl⟩ : syracuseStep 25169705 = 18877279) B18877279
theorem B16779803 : Blo 2179435 16779803 := bstep (se 1 (by rfl) ⟨12584852, by rfl⟩ : syracuseStep 16779803 = 25169705) B25169705
theorem B44746141 : Blo 2179435 44746141 := bstep (se 3 (by rfl) ⟨8389901, by rfl⟩ : syracuseStep 44746141 = 16779803) B16779803
theorem B59661521 : Blo 2179435 59661521 := bstep (se 2 (by rfl) ⟨22373070, by rfl⟩ : syracuseStep 59661521 = 44746141) B44746141
theorem B39774347 : Blo 2179435 39774347 := bstep (se 1 (by rfl) ⟨29830760, by rfl⟩ : syracuseStep 39774347 = 59661521) B59661521
theorem B26516231 : Blo 2179435 26516231 := bstep (se 1 (by rfl) ⟨19887173, by rfl⟩ : syracuseStep 26516231 = 39774347) B39774347
theorem B17677487 : Blo 2179435 17677487 := bstep (se 1 (by rfl) ⟨13258115, by rfl⟩ : syracuseStep 17677487 = 26516231) B26516231
theorem B47139965 : Blo 2179435 47139965 := bstep (se 3 (by rfl) ⟨8838743, by rfl⟩ : syracuseStep 47139965 = 17677487) B17677487
theorem B31426643 : Blo 2179435 31426643 := bstep (se 1 (by rfl) ⟨23569982, by rfl⟩ : syracuseStep 31426643 = 47139965) B47139965
theorem B20951095 : Blo 2179435 20951095 := bstep (se 1 (by rfl) ⟨15713321, by rfl⟩ : syracuseStep 20951095 = 31426643) B31426643
theorem B27934793 : Blo 2179435 27934793 := bstep (se 2 (by rfl) ⟨10475547, by rfl⟩ : syracuseStep 27934793 = 20951095) B20951095
theorem B18623195 : Blo 2179435 18623195 := bstep (se 1 (by rfl) ⟨13967396, by rfl⟩ : syracuseStep 18623195 = 27934793) B27934793
theorem B12415463 : Blo 2179435 12415463 := bstep (se 1 (by rfl) ⟨9311597, by rfl⟩ : syracuseStep 12415463 = 18623195) B18623195
theorem B8276975 : Blo 2179435 8276975 := bstep (se 1 (by rfl) ⟨6207731, by rfl⟩ : syracuseStep 8276975 = 12415463) B12415463
theorem B5517983 : Blo 2179435 5517983 := bstep (se 1 (by rfl) ⟨4138487, by rfl⟩ : syracuseStep 5517983 = 8276975) B8276975
theorem B3678655 : Blo 2179435 3678655 := bstep (se 1 (by rfl) ⟨2758991, by rfl⟩ : syracuseStep 3678655 = 5517983) B5517983
theorem B4904873 : Blo 2179435 4904873 := bstep (se 2 (by rfl) ⟨1839327, by rfl⟩ : syracuseStep 4904873 = 3678655) B3678655
theorem B3269915 : Blo 2179435 3269915 := bstep (se 1 (by rfl) ⟨2452436, by rfl⟩ : syracuseStep 3269915 = 4904873) B4904873
theorem B2179943 : Blo 2179435 2179943 := bstep (se 1 (by rfl) ⟨1634957, by rfl⟩ : syracuseStep 2179943 = 3269915) B3269915
theorem B2452441 : Blo 2179435 2452441 := bbase (se 2 (by rfl) ⟨919665, by rfl⟩ : syracuseStep 2452441 = 1839331) (by norm_num)
theorem B3269921 : Blo 2179435 3269921 := bstep (se 2 (by rfl) ⟨1226220, by rfl⟩ : syracuseStep 3269921 = 2452441) B2452441
theorem B2179947 : Blo 2179435 2179947 := bstep (se 1 (by rfl) ⟨1634960, by rfl⟩ : syracuseStep 2179947 = 3269921) B3269921
theorem B3103877 : Blo 2179435 3103877 := bbase (se 4 (by rfl) ⟨290988, by rfl⟩ : syracuseStep 3103877 = 581977) (by norm_num)
theorem B8277005 : Blo 2179435 8277005 := bstep (se 3 (by rfl) ⟨1551938, by rfl⟩ : syracuseStep 8277005 = 3103877) B3103877
theorem B5518003 : Blo 2179435 5518003 := bstep (se 1 (by rfl) ⟨4138502, by rfl⟩ : syracuseStep 5518003 = 8277005) B8277005
theorem B7357337 : Blo 2179435 7357337 := bstep (se 2 (by rfl) ⟨2759001, by rfl⟩ : syracuseStep 7357337 = 5518003) B5518003
theorem B4904891 : Blo 2179435 4904891 := bstep (se 1 (by rfl) ⟨3678668, by rfl⟩ : syracuseStep 4904891 = 7357337) B7357337
theorem B3269927 : Blo 2179435 3269927 := bstep (se 1 (by rfl) ⟨2452445, by rfl⟩ : syracuseStep 3269927 = 4904891) B4904891
theorem B2179951 : Blo 2179435 2179951 := bstep (se 1 (by rfl) ⟨1634963, by rfl⟩ : syracuseStep 2179951 = 3269927) B3269927
theorem B3269933 : Blo 2179435 3269933 := bbase (se 3 (by rfl) ⟨613112, by rfl⟩ : syracuseStep 3269933 = 1226225) (by norm_num)
theorem B2179955 : Blo 2179435 2179955 := bstep (se 1 (by rfl) ⟨1634966, by rfl⟩ : syracuseStep 2179955 = 3269933) B3269933
theorem B4904909 : Blo 2179435 4904909 := bbase (se 3 (by rfl) ⟨919670, by rfl⟩ : syracuseStep 4904909 = 1839341) (by norm_num)
theorem B3269939 : Blo 2179435 3269939 := bstep (se 1 (by rfl) ⟨2452454, by rfl⟩ : syracuseStep 3269939 = 4904909) B4904909
theorem B2179959 : Blo 2179435 2179959 := bstep (se 1 (by rfl) ⟨1634969, by rfl⟩ : syracuseStep 2179959 = 3269939) B3269939
theorem B2759017 : Blo 2179435 2759017 := bbase (se 2 (by rfl) ⟨1034631, by rfl⟩ : syracuseStep 2759017 = 2069263) (by norm_num)
theorem B3678689 : Blo 2179435 3678689 := bstep (se 2 (by rfl) ⟨1379508, by rfl⟩ : syracuseStep 3678689 = 2759017) B2759017
theorem B2452459 : Blo 2179435 2452459 := bstep (se 1 (by rfl) ⟨1839344, by rfl⟩ : syracuseStep 2452459 = 3678689) B3678689
theorem B3269945 : Blo 2179435 3269945 := bstep (se 2 (by rfl) ⟨1226229, by rfl⟩ : syracuseStep 3269945 = 2452459) B2452459
theorem B2179963 : Blo 2179435 2179963 := bstep (se 1 (by rfl) ⟨1634972, by rfl⟩ : syracuseStep 2179963 = 3269945) B3269945
theorem B2796665 : Blo 2179435 2796665 := bbase (se 2 (by rfl) ⟨1048749, by rfl⟩ : syracuseStep 2796665 = 2097499) (by norm_num)
theorem B7457773 : Blo 2179435 7457773 := bstep (se 3 (by rfl) ⟨1398332, by rfl⟩ : syracuseStep 7457773 = 2796665) B2796665
theorem B9943697 : Blo 2179435 9943697 := bstep (se 2 (by rfl) ⟨3728886, by rfl⟩ : syracuseStep 9943697 = 7457773) B7457773
theorem B6629131 : Blo 2179435 6629131 := bstep (se 1 (by rfl) ⟨4971848, by rfl⟩ : syracuseStep 6629131 = 9943697) B9943697
theorem B8838841 : Blo 2179435 8838841 := bstep (se 2 (by rfl) ⟨3314565, by rfl⟩ : syracuseStep 8838841 = 6629131) B6629131
theorem B11785121 : Blo 2179435 11785121 := bstep (se 2 (by rfl) ⟨4419420, by rfl⟩ : syracuseStep 11785121 = 8838841) B8838841
theorem B7856747 : Blo 2179435 7856747 := bstep (se 1 (by rfl) ⟨5892560, by rfl⟩ : syracuseStep 7856747 = 11785121) B11785121
theorem B5237831 : Blo 2179435 5237831 := bstep (se 1 (by rfl) ⟨3928373, by rfl⟩ : syracuseStep 5237831 = 7856747) B7856747
theorem B13967549 : Blo 2179435 13967549 := bstep (se 3 (by rfl) ⟨2618915, by rfl⟩ : syracuseStep 13967549 = 5237831) B5237831
theorem B9311699 : Blo 2179435 9311699 := bstep (se 1 (by rfl) ⟨6983774, by rfl⟩ : syracuseStep 9311699 = 13967549) B13967549
theorem B24831197 : Blo 2179435 24831197 := bstep (se 3 (by rfl) ⟨4655849, by rfl⟩ : syracuseStep 24831197 = 9311699) B9311699
theorem B16554131 : Blo 2179435 16554131 := bstep (se 1 (by rfl) ⟨12415598, by rfl⟩ : syracuseStep 16554131 = 24831197) B24831197
theorem B11036087 : Blo 2179435 11036087 := bstep (se 1 (by rfl) ⟨8277065, by rfl⟩ : syracuseStep 11036087 = 16554131) B16554131
theorem B7357391 : Blo 2179435 7357391 := bstep (se 1 (by rfl) ⟨5518043, by rfl⟩ : syracuseStep 7357391 = 11036087) B11036087
theorem B4904927 : Blo 2179435 4904927 := bstep (se 1 (by rfl) ⟨3678695, by rfl⟩ : syracuseStep 4904927 = 7357391) B7357391
theorem B3269951 : Blo 2179435 3269951 := bstep (se 1 (by rfl) ⟨2452463, by rfl⟩ : syracuseStep 3269951 = 4904927) B4904927
theorem B2179967 : Blo 2179435 2179967 := bstep (se 1 (by rfl) ⟨1634975, by rfl⟩ : syracuseStep 2179967 = 3269951) B3269951
theorem B3269957 : Blo 2179435 3269957 := bbase (se 4 (by rfl) ⟨306558, by rfl⟩ : syracuseStep 3269957 = 613117) (by norm_num)
theorem B2179971 : Blo 2179435 2179971 := bstep (se 1 (by rfl) ⟨1634978, by rfl⟩ : syracuseStep 2179971 = 3269957) B3269957
theorem B3678709 : Blo 2179435 3678709 := bbase (se 5 (by rfl) ⟨172439, by rfl⟩ : syracuseStep 3678709 = 344879) (by norm_num)
theorem B4904945 : Blo 2179435 4904945 := bstep (se 2 (by rfl) ⟨1839354, by rfl⟩ : syracuseStep 4904945 = 3678709) B3678709
theorem B3269963 : Blo 2179435 3269963 := bstep (se 1 (by rfl) ⟨2452472, by rfl⟩ : syracuseStep 3269963 = 4904945) B4904945
theorem B2179975 : Blo 2179435 2179975 := bstep (se 1 (by rfl) ⟨1634981, by rfl⟩ : syracuseStep 2179975 = 3269963) B3269963
theorem B2452477 : Blo 2179435 2452477 := bbase (se 3 (by rfl) ⟨459839, by rfl⟩ : syracuseStep 2452477 = 919679) (by norm_num)
theorem B3269969 : Blo 2179435 3269969 := bstep (se 2 (by rfl) ⟨1226238, by rfl⟩ : syracuseStep 3269969 = 2452477) B2452477
theorem B2179979 : Blo 2179435 2179979 := bstep (se 1 (by rfl) ⟨1634984, by rfl⟩ : syracuseStep 2179979 = 3269969) B3269969
theorem B7357445 : Blo 2179435 7357445 := bbase (se 4 (by rfl) ⟨689760, by rfl⟩ : syracuseStep 7357445 = 1379521) (by norm_num)
theorem B4904963 : Blo 2179435 4904963 := bstep (se 1 (by rfl) ⟨3678722, by rfl⟩ : syracuseStep 4904963 = 7357445) B7357445
theorem B3269975 : Blo 2179435 3269975 := bstep (se 1 (by rfl) ⟨2452481, by rfl⟩ : syracuseStep 3269975 = 4904963) B4904963
theorem B2179983 : Blo 2179435 2179983 := bstep (se 1 (by rfl) ⟨1634987, by rfl⟩ : syracuseStep 2179983 = 3269975) B3269975
theorem B3269981 : Blo 2179435 3269981 := bbase (se 3 (by rfl) ⟨613121, by rfl⟩ : syracuseStep 3269981 = 1226243) (by norm_num)
theorem B2179987 : Blo 2179435 2179987 := bstep (se 1 (by rfl) ⟨1634990, by rfl⟩ : syracuseStep 2179987 = 3269981) B3269981
theorem B4904981 : Blo 2179435 4904981 := bbase (se 6 (by rfl) ⟨114960, by rfl⟩ : syracuseStep 4904981 = 229921) (by norm_num)
theorem B3269987 : Blo 2179435 3269987 := bstep (se 1 (by rfl) ⟨2452490, by rfl⟩ : syracuseStep 3269987 = 4904981) B4904981
theorem B2179991 : Blo 2179435 2179991 := bstep (se 1 (by rfl) ⟨1634993, by rfl⟩ : syracuseStep 2179991 = 3269987) B3269987
theorem B8277173 : Blo 2179435 8277173 := bbase (se 5 (by rfl) ⟨387992, by rfl⟩ : syracuseStep 8277173 = 775985) (by norm_num)
theorem B5518115 : Blo 2179435 5518115 := bstep (se 1 (by rfl) ⟨4138586, by rfl⟩ : syracuseStep 5518115 = 8277173) B8277173
theorem B3678743 : Blo 2179435 3678743 := bstep (se 1 (by rfl) ⟨2759057, by rfl⟩ : syracuseStep 3678743 = 5518115) B5518115
theorem B2452495 : Blo 2179435 2452495 := bstep (se 1 (by rfl) ⟨1839371, by rfl⟩ : syracuseStep 2452495 = 3678743) B3678743
theorem B3269993 : Blo 2179435 3269993 := bstep (se 2 (by rfl) ⟨1226247, by rfl⟩ : syracuseStep 3269993 = 2452495) B2452495
theorem B2179995 : Blo 2179435 2179995 := bstep (se 1 (by rfl) ⟨1634996, by rfl⟩ : syracuseStep 2179995 = 3269993) B3269993
theorem B5237909 : Blo 2179435 5237909 := bbase (se 6 (by rfl) ⟨122763, by rfl⟩ : syracuseStep 5237909 = 245527) (by norm_num)
theorem B3491939 : Blo 2179435 3491939 := bstep (se 1 (by rfl) ⟨2618954, by rfl⟩ : syracuseStep 3491939 = 5237909) B5237909
theorem B2327959 : Blo 2179435 2327959 := bstep (se 1 (by rfl) ⟨1745969, by rfl⟩ : syracuseStep 2327959 = 3491939) B3491939
theorem B12415781 : Blo 2179435 12415781 := bstep (se 4 (by rfl) ⟨1163979, by rfl⟩ : syracuseStep 12415781 = 2327959) B2327959
theorem B8277187 : Blo 2179435 8277187 := bstep (se 1 (by rfl) ⟨6207890, by rfl⟩ : syracuseStep 8277187 = 12415781) B12415781
theorem B11036249 : Blo 2179435 11036249 := bstep (se 2 (by rfl) ⟨4138593, by rfl⟩ : syracuseStep 11036249 = 8277187) B8277187
theorem B7357499 : Blo 2179435 7357499 := bstep (se 1 (by rfl) ⟨5518124, by rfl⟩ : syracuseStep 7357499 = 11036249) B11036249
theorem B4904999 : Blo 2179435 4904999 := bstep (se 1 (by rfl) ⟨3678749, by rfl⟩ : syracuseStep 4904999 = 7357499) B7357499
theorem B3269999 : Blo 2179435 3269999 := bstep (se 1 (by rfl) ⟨2452499, by rfl⟩ : syracuseStep 3269999 = 4904999) B4904999
theorem B2179999 : Blo 2179435 2179999 := bstep (se 1 (by rfl) ⟨1634999, by rfl⟩ : syracuseStep 2179999 = 3269999) B3269999
theorem B3270005 : Blo 2179435 3270005 := bbase (se 5 (by rfl) ⟨153281, by rfl⟩ : syracuseStep 3270005 = 306563) (by norm_num)
theorem B2180003 : Blo 2179435 2180003 := bstep (se 1 (by rfl) ⟨1635002, by rfl⟩ : syracuseStep 2180003 = 3270005) B3270005
theorem B3103957 : Blo 2179435 3103957 := bbase (se 7 (by rfl) ⟨36374, by rfl⟩ : syracuseStep 3103957 = 72749) (by norm_num)
theorem B4138609 : Blo 2179435 4138609 := bstep (se 2 (by rfl) ⟨1551978, by rfl⟩ : syracuseStep 4138609 = 3103957) B3103957
theorem B5518145 : Blo 2179435 5518145 := bstep (se 2 (by rfl) ⟨2069304, by rfl⟩ : syracuseStep 5518145 = 4138609) B4138609
theorem B3678763 : Blo 2179435 3678763 := bstep (se 1 (by rfl) ⟨2759072, by rfl⟩ : syracuseStep 3678763 = 5518145) B5518145
theorem B4905017 : Blo 2179435 4905017 := bstep (se 2 (by rfl) ⟨1839381, by rfl⟩ : syracuseStep 4905017 = 3678763) B3678763
theorem B3270011 : Blo 2179435 3270011 := bstep (se 1 (by rfl) ⟨2452508, by rfl⟩ : syracuseStep 3270011 = 4905017) B4905017
theorem B2180007 : Blo 2179435 2180007 := bstep (se 1 (by rfl) ⟨1635005, by rfl⟩ : syracuseStep 2180007 = 3270011) B3270011
theorem B2452513 : Blo 2179435 2452513 := bbase (se 2 (by rfl) ⟨919692, by rfl⟩ : syracuseStep 2452513 = 1839385) (by norm_num)
theorem B3270017 : Blo 2179435 3270017 := bstep (se 2 (by rfl) ⟨1226256, by rfl⟩ : syracuseStep 3270017 = 2452513) B2452513
theorem B2180011 : Blo 2179435 2180011 := bstep (se 1 (by rfl) ⟨1635008, by rfl⟩ : syracuseStep 2180011 = 3270017) B3270017
theorem B5518165 : Blo 2179435 5518165 := bbase (se 9 (by rfl) ⟨16166, by rfl⟩ : syracuseStep 5518165 = 32333) (by norm_num)
theorem B7357553 : Blo 2179435 7357553 := bstep (se 2 (by rfl) ⟨2759082, by rfl⟩ : syracuseStep 7357553 = 5518165) B5518165
theorem B4905035 : Blo 2179435 4905035 := bstep (se 1 (by rfl) ⟨3678776, by rfl⟩ : syracuseStep 4905035 = 7357553) B7357553
theorem B3270023 : Blo 2179435 3270023 := bstep (se 1 (by rfl) ⟨2452517, by rfl⟩ : syracuseStep 3270023 = 4905035) B4905035
theorem B2180015 : Blo 2179435 2180015 := bstep (se 1 (by rfl) ⟨1635011, by rfl⟩ : syracuseStep 2180015 = 3270023) B3270023
theorem B3270029 : Blo 2179435 3270029 := bbase (se 3 (by rfl) ⟨613130, by rfl⟩ : syracuseStep 3270029 = 1226261) (by norm_num)
theorem B2180019 : Blo 2179435 2180019 := bstep (se 1 (by rfl) ⟨1635014, by rfl⟩ : syracuseStep 2180019 = 3270029) B3270029
theorem B4905053 : Blo 2179435 4905053 := bbase (se 3 (by rfl) ⟨919697, by rfl⟩ : syracuseStep 4905053 = 1839395) (by norm_num)
theorem B3270035 : Blo 2179435 3270035 := bstep (se 1 (by rfl) ⟨2452526, by rfl⟩ : syracuseStep 3270035 = 4905053) B4905053
theorem B2180023 : Blo 2179435 2180023 := bstep (se 1 (by rfl) ⟨1635017, by rfl⟩ : syracuseStep 2180023 = 3270035) B3270035
theorem B3678797 : Blo 2179435 3678797 := bbase (se 3 (by rfl) ⟨689774, by rfl⟩ : syracuseStep 3678797 = 1379549) (by norm_num)
theorem B2452531 : Blo 2179435 2452531 := bstep (se 1 (by rfl) ⟨1839398, by rfl⟩ : syracuseStep 2452531 = 3678797) B3678797
theorem B3270041 : Blo 2179435 3270041 := bstep (se 2 (by rfl) ⟨1226265, by rfl⟩ : syracuseStep 3270041 = 2452531) B2452531
theorem B2180027 : Blo 2179435 2180027 := bstep (se 1 (by rfl) ⟨1635020, by rfl⟩ : syracuseStep 2180027 = 3270041) B3270041
theorem B12585365 : Blo 2179435 12585365 := bbase (se 6 (by rfl) ⟨294969, by rfl⟩ : syracuseStep 12585365 = 589939) (by norm_num)
theorem B8390243 : Blo 2179435 8390243 := bstep (se 1 (by rfl) ⟨6292682, by rfl⟩ : syracuseStep 8390243 = 12585365) B12585365
theorem B5593495 : Blo 2179435 5593495 := bstep (se 1 (by rfl) ⟨4195121, by rfl⟩ : syracuseStep 5593495 = 8390243) B8390243
theorem B7457993 : Blo 2179435 7457993 := bstep (se 2 (by rfl) ⟨2796747, by rfl⟩ : syracuseStep 7457993 = 5593495) B5593495
theorem B4971995 : Blo 2179435 4971995 := bstep (se 1 (by rfl) ⟨3728996, by rfl⟩ : syracuseStep 4971995 = 7457993) B7457993
theorem B3314663 : Blo 2179435 3314663 := bstep (se 1 (by rfl) ⟨2485997, by rfl⟩ : syracuseStep 3314663 = 4971995) B4971995
theorem B2209775 : Blo 2179435 2209775 := bstep (se 1 (by rfl) ⟨1657331, by rfl⟩ : syracuseStep 2209775 = 3314663) B3314663
theorem B5892733 : Blo 2179435 5892733 := bstep (se 3 (by rfl) ⟨1104887, by rfl⟩ : syracuseStep 5892733 = 2209775) B2209775
theorem B31427909 : Blo 2179435 31427909 := bstep (se 4 (by rfl) ⟨2946366, by rfl⟩ : syracuseStep 31427909 = 5892733) B5892733
theorem B20951939 : Blo 2179435 20951939 := bstep (se 1 (by rfl) ⟨15713954, by rfl⟩ : syracuseStep 20951939 = 31427909) B31427909
theorem B13967959 : Blo 2179435 13967959 := bstep (se 1 (by rfl) ⟨10475969, by rfl⟩ : syracuseStep 13967959 = 20951939) B20951939
theorem B18623945 : Blo 2179435 18623945 := bstep (se 2 (by rfl) ⟨6983979, by rfl⟩ : syracuseStep 18623945 = 13967959) B13967959
theorem B12415963 : Blo 2179435 12415963 := bstep (se 1 (by rfl) ⟨9311972, by rfl⟩ : syracuseStep 12415963 = 18623945) B18623945
theorem B16554617 : Blo 2179435 16554617 := bstep (se 2 (by rfl) ⟨6207981, by rfl⟩ : syracuseStep 16554617 = 12415963) B12415963
theorem B11036411 : Blo 2179435 11036411 := bstep (se 1 (by rfl) ⟨8277308, by rfl⟩ : syracuseStep 11036411 = 16554617) B16554617
theorem B7357607 : Blo 2179435 7357607 := bstep (se 1 (by rfl) ⟨5518205, by rfl⟩ : syracuseStep 7357607 = 11036411) B11036411
theorem B4905071 : Blo 2179435 4905071 := bstep (se 1 (by rfl) ⟨3678803, by rfl⟩ : syracuseStep 4905071 = 7357607) B7357607
theorem B3270047 : Blo 2179435 3270047 := bstep (se 1 (by rfl) ⟨2452535, by rfl⟩ : syracuseStep 3270047 = 4905071) B4905071
theorem B2180031 : Blo 2179435 2180031 := bstep (se 1 (by rfl) ⟨1635023, by rfl⟩ : syracuseStep 2180031 = 3270047) B3270047
theorem B3270053 : Blo 2179435 3270053 := bbase (se 4 (by rfl) ⟨306567, by rfl⟩ : syracuseStep 3270053 = 613135) (by norm_num)
theorem B2180035 : Blo 2179435 2180035 := bstep (se 1 (by rfl) ⟨1635026, by rfl⟩ : syracuseStep 2180035 = 3270053) B3270053
theorem B2759113 : Blo 2179435 2759113 := bbase (se 2 (by rfl) ⟨1034667, by rfl⟩ : syracuseStep 2759113 = 2069335) (by norm_num)
theorem B3678817 : Blo 2179435 3678817 := bstep (se 2 (by rfl) ⟨1379556, by rfl⟩ : syracuseStep 3678817 = 2759113) B2759113
theorem B4905089 : Blo 2179435 4905089 := bstep (se 2 (by rfl) ⟨1839408, by rfl⟩ : syracuseStep 4905089 = 3678817) B3678817
theorem B3270059 : Blo 2179435 3270059 := bstep (se 1 (by rfl) ⟨2452544, by rfl⟩ : syracuseStep 3270059 = 4905089) B4905089
theorem B2180039 : Blo 2179435 2180039 := bstep (se 1 (by rfl) ⟨1635029, by rfl⟩ : syracuseStep 2180039 = 3270059) B3270059
theorem B2452549 : Blo 2179435 2452549 := bbase (se 4 (by rfl) ⟨229926, by rfl⟩ : syracuseStep 2452549 = 459853) (by norm_num)
theorem B3270065 : Blo 2179435 3270065 := bstep (se 2 (by rfl) ⟨1226274, by rfl⟩ : syracuseStep 3270065 = 2452549) B2452549
theorem B2180043 : Blo 2179435 2180043 := bstep (se 1 (by rfl) ⟨1635032, by rfl⟩ : syracuseStep 2180043 = 3270065) B3270065
theorem B4138685 : Blo 2179435 4138685 := bbase (se 3 (by rfl) ⟨776003, by rfl⟩ : syracuseStep 4138685 = 1552007) (by norm_num)
theorem B2759123 : Blo 2179435 2759123 := bstep (se 1 (by rfl) ⟨2069342, by rfl⟩ : syracuseStep 2759123 = 4138685) B4138685
theorem B7357661 : Blo 2179435 7357661 := bstep (se 3 (by rfl) ⟨1379561, by rfl⟩ : syracuseStep 7357661 = 2759123) B2759123
theorem B4905107 : Blo 2179435 4905107 := bstep (se 1 (by rfl) ⟨3678830, by rfl⟩ : syracuseStep 4905107 = 7357661) B7357661
theorem B3270071 : Blo 2179435 3270071 := bstep (se 1 (by rfl) ⟨2452553, by rfl⟩ : syracuseStep 3270071 = 4905107) B4905107
theorem B2180047 : Blo 2179435 2180047 := bstep (se 1 (by rfl) ⟨1635035, by rfl⟩ : syracuseStep 2180047 = 3270071) B3270071
theorem B3270077 : Blo 2179435 3270077 := bbase (se 3 (by rfl) ⟨613139, by rfl⟩ : syracuseStep 3270077 = 1226279) (by norm_num)
theorem B2180051 : Blo 2179435 2180051 := bstep (se 1 (by rfl) ⟨1635038, by rfl⟩ : syracuseStep 2180051 = 3270077) B3270077
theorem B4905125 : Blo 2179435 4905125 := bbase (se 4 (by rfl) ⟨459855, by rfl⟩ : syracuseStep 4905125 = 919711) (by norm_num)
theorem B3270083 : Blo 2179435 3270083 := bstep (se 1 (by rfl) ⟨2452562, by rfl⟩ : syracuseStep 3270083 = 4905125) B4905125
theorem B2180055 : Blo 2179435 2180055 := bstep (se 1 (by rfl) ⟨1635041, by rfl⟩ : syracuseStep 2180055 = 3270083) B3270083
theorem B5518277 : Blo 2179435 5518277 := bbase (se 4 (by rfl) ⟨517338, by rfl⟩ : syracuseStep 5518277 = 1034677) (by norm_num)
theorem B3678851 : Blo 2179435 3678851 := bstep (se 1 (by rfl) ⟨2759138, by rfl⟩ : syracuseStep 3678851 = 5518277) B5518277
theorem B2452567 : Blo 2179435 2452567 := bstep (se 1 (by rfl) ⟨1839425, by rfl⟩ : syracuseStep 2452567 = 3678851) B3678851
theorem B3270089 : Blo 2179435 3270089 := bstep (se 2 (by rfl) ⟨1226283, by rfl⟩ : syracuseStep 3270089 = 2452567) B2452567
theorem B2180059 : Blo 2179435 2180059 := bstep (se 1 (by rfl) ⟨1635044, by rfl⟩ : syracuseStep 2180059 = 3270089) B3270089
theorem B5892821 : Blo 2179435 5892821 := bbase (se 7 (by rfl) ⟨69056, by rfl⟩ : syracuseStep 5892821 = 138113) (by norm_num)
theorem B3928547 : Blo 2179435 3928547 := bstep (se 1 (by rfl) ⟨2946410, by rfl⟩ : syracuseStep 3928547 = 5892821) B5892821
theorem B10476125 : Blo 2179435 10476125 := bstep (se 3 (by rfl) ⟨1964273, by rfl⟩ : syracuseStep 10476125 = 3928547) B3928547
theorem B6984083 : Blo 2179435 6984083 := bstep (se 1 (by rfl) ⟨5238062, by rfl⟩ : syracuseStep 6984083 = 10476125) B10476125
theorem B4656055 : Blo 2179435 4656055 := bstep (se 1 (by rfl) ⟨3492041, by rfl⟩ : syracuseStep 4656055 = 6984083) B6984083
theorem B6208073 : Blo 2179435 6208073 := bstep (se 2 (by rfl) ⟨2328027, by rfl⟩ : syracuseStep 6208073 = 4656055) B4656055
theorem B4138715 : Blo 2179435 4138715 := bstep (se 1 (by rfl) ⟨3104036, by rfl⟩ : syracuseStep 4138715 = 6208073) B6208073
theorem B11036573 : Blo 2179435 11036573 := bstep (se 3 (by rfl) ⟨2069357, by rfl⟩ : syracuseStep 11036573 = 4138715) B4138715
theorem B7357715 : Blo 2179435 7357715 := bstep (se 1 (by rfl) ⟨5518286, by rfl⟩ : syracuseStep 7357715 = 11036573) B11036573
theorem B4905143 : Blo 2179435 4905143 := bstep (se 1 (by rfl) ⟨3678857, by rfl⟩ : syracuseStep 4905143 = 7357715) B7357715
theorem B3270095 : Blo 2179435 3270095 := bstep (se 1 (by rfl) ⟨2452571, by rfl⟩ : syracuseStep 3270095 = 4905143) B4905143
theorem B2180063 : Blo 2179435 2180063 := bstep (se 1 (by rfl) ⟨1635047, by rfl⟩ : syracuseStep 2180063 = 3270095) B3270095
theorem B3270101 : Blo 2179435 3270101 := bbase (se 7 (by rfl) ⟨38321, by rfl⟩ : syracuseStep 3270101 = 76643) (by norm_num)
theorem B2180067 : Blo 2179435 2180067 := bstep (se 1 (by rfl) ⟨1635050, by rfl⟩ : syracuseStep 2180067 = 3270101) B3270101
theorem B8277461 : Blo 2179435 8277461 := bbase (se 7 (by rfl) ⟨97001, by rfl⟩ : syracuseStep 8277461 = 194003) (by norm_num)
theorem B5518307 : Blo 2179435 5518307 := bstep (se 1 (by rfl) ⟨4138730, by rfl⟩ : syracuseStep 5518307 = 8277461) B8277461
theorem B3678871 : Blo 2179435 3678871 := bstep (se 1 (by rfl) ⟨2759153, by rfl⟩ : syracuseStep 3678871 = 5518307) B5518307
theorem B4905161 : Blo 2179435 4905161 := bstep (se 2 (by rfl) ⟨1839435, by rfl⟩ : syracuseStep 4905161 = 3678871) B3678871
theorem B3270107 : Blo 2179435 3270107 := bstep (se 1 (by rfl) ⟨2452580, by rfl⟩ : syracuseStep 3270107 = 4905161) B4905161
theorem B2180071 : Blo 2179435 2180071 := bstep (se 1 (by rfl) ⟨1635053, by rfl⟩ : syracuseStep 2180071 = 3270107) B3270107
theorem B2452585 : Blo 2179435 2452585 := bbase (se 2 (by rfl) ⟨919719, by rfl⟩ : syracuseStep 2452585 = 1839439) (by norm_num)
theorem B3270113 : Blo 2179435 3270113 := bstep (se 2 (by rfl) ⟨1226292, by rfl⟩ : syracuseStep 3270113 = 2452585) B2452585
theorem B2180075 : Blo 2179435 2180075 := bstep (se 1 (by rfl) ⟨1635056, by rfl⟩ : syracuseStep 2180075 = 3270113) B3270113
theorem B5238101 : Blo 2179435 5238101 := bbase (se 11 (by rfl) ⟨3836, by rfl⟩ : syracuseStep 5238101 = 7673) (by norm_num)
theorem B3492067 : Blo 2179435 3492067 := bstep (se 1 (by rfl) ⟨2619050, by rfl⟩ : syracuseStep 3492067 = 5238101) B5238101
theorem B4656089 : Blo 2179435 4656089 := bstep (se 2 (by rfl) ⟨1746033, by rfl⟩ : syracuseStep 4656089 = 3492067) B3492067
theorem B12416237 : Blo 2179435 12416237 := bstep (se 3 (by rfl) ⟨2328044, by rfl⟩ : syracuseStep 12416237 = 4656089) B4656089
theorem B8277491 : Blo 2179435 8277491 := bstep (se 1 (by rfl) ⟨6208118, by rfl⟩ : syracuseStep 8277491 = 12416237) B12416237
theorem B5518327 : Blo 2179435 5518327 := bstep (se 1 (by rfl) ⟨4138745, by rfl⟩ : syracuseStep 5518327 = 8277491) B8277491
theorem B7357769 : Blo 2179435 7357769 := bstep (se 2 (by rfl) ⟨2759163, by rfl⟩ : syracuseStep 7357769 = 5518327) B5518327
theorem B4905179 : Blo 2179435 4905179 := bstep (se 1 (by rfl) ⟨3678884, by rfl⟩ : syracuseStep 4905179 = 7357769) B7357769
theorem B3270119 : Blo 2179435 3270119 := bstep (se 1 (by rfl) ⟨2452589, by rfl⟩ : syracuseStep 3270119 = 4905179) B4905179
theorem B2180079 : Blo 2179435 2180079 := bstep (se 1 (by rfl) ⟨1635059, by rfl⟩ : syracuseStep 2180079 = 3270119) B3270119
theorem B3270125 : Blo 2179435 3270125 := bbase (se 3 (by rfl) ⟨613148, by rfl⟩ : syracuseStep 3270125 = 1226297) (by norm_num)
theorem B2180083 : Blo 2179435 2180083 := bstep (se 1 (by rfl) ⟨1635062, by rfl⟩ : syracuseStep 2180083 = 3270125) B3270125
theorem B4905197 : Blo 2179435 4905197 := bbase (se 3 (by rfl) ⟨919724, by rfl⟩ : syracuseStep 4905197 = 1839449) (by norm_num)
theorem B3270131 : Blo 2179435 3270131 := bstep (se 1 (by rfl) ⟨2452598, by rfl⟩ : syracuseStep 3270131 = 4905197) B4905197
theorem B2180087 : Blo 2179435 2180087 := bstep (se 1 (by rfl) ⟨1635065, by rfl⟩ : syracuseStep 2180087 = 3270131) B3270131
theorem B3104077 : Blo 2179435 3104077 := bbase (se 3 (by rfl) ⟨582014, by rfl⟩ : syracuseStep 3104077 = 1164029) (by norm_num)
theorem B4138769 : Blo 2179435 4138769 := bstep (se 2 (by rfl) ⟨1552038, by rfl⟩ : syracuseStep 4138769 = 3104077) B3104077
theorem B2759179 : Blo 2179435 2759179 := bstep (se 1 (by rfl) ⟨2069384, by rfl⟩ : syracuseStep 2759179 = 4138769) B4138769
theorem B3678905 : Blo 2179435 3678905 := bstep (se 2 (by rfl) ⟨1379589, by rfl⟩ : syracuseStep 3678905 = 2759179) B2759179
theorem B2452603 : Blo 2179435 2452603 := bstep (se 1 (by rfl) ⟨1839452, by rfl⟩ : syracuseStep 2452603 = 3678905) B3678905
theorem B3270137 : Blo 2179435 3270137 := bstep (se 2 (by rfl) ⟨1226301, by rfl⟩ : syracuseStep 3270137 = 2452603) B2452603
theorem B2180091 : Blo 2179435 2180091 := bstep (se 1 (by rfl) ⟨1635068, by rfl⟩ : syracuseStep 2180091 = 3270137) B3270137
theorem B35839829 : Blo 2179435 35839829 := bbase (se 9 (by rfl) ⟨104999, by rfl⟩ : syracuseStep 35839829 = 209999) (by norm_num)
theorem B23893219 : Blo 2179435 23893219 := bstep (se 1 (by rfl) ⟨17919914, by rfl⟩ : syracuseStep 23893219 = 35839829) B35839829
theorem B31857625 : Blo 2179435 31857625 := bstep (se 2 (by rfl) ⟨11946609, by rfl⟩ : syracuseStep 31857625 = 23893219) B23893219
theorem B42476833 : Blo 2179435 42476833 := bstep (se 2 (by rfl) ⟨15928812, by rfl⟩ : syracuseStep 42476833 = 31857625) B31857625
theorem B56635777 : Blo 2179435 56635777 := bstep (se 2 (by rfl) ⟨21238416, by rfl⟩ : syracuseStep 56635777 = 42476833) B42476833
theorem B75514369 : Blo 2179435 75514369 := bstep (se 2 (by rfl) ⟨28317888, by rfl⟩ : syracuseStep 75514369 = 56635777) B56635777
theorem B100685825 : Blo 2179435 100685825 := bstep (se 2 (by rfl) ⟨37757184, by rfl⟩ : syracuseStep 100685825 = 75514369) B75514369
theorem B67123883 : Blo 2179435 67123883 := bstep (se 1 (by rfl) ⟨50342912, by rfl⟩ : syracuseStep 67123883 = 100685825) B100685825
theorem B44749255 : Blo 2179435 44749255 := bstep (se 1 (by rfl) ⟨33561941, by rfl⟩ : syracuseStep 44749255 = 67123883) B67123883
theorem B59665673 : Blo 2179435 59665673 := bstep (se 2 (by rfl) ⟨22374627, by rfl⟩ : syracuseStep 59665673 = 44749255) B44749255
theorem B39777115 : Blo 2179435 39777115 := bstep (se 1 (by rfl) ⟨29832836, by rfl⟩ : syracuseStep 39777115 = 59665673) B59665673
theorem B53036153 : Blo 2179435 53036153 := bstep (se 2 (by rfl) ⟨19888557, by rfl⟩ : syracuseStep 53036153 = 39777115) B39777115
theorem B35357435 : Blo 2179435 35357435 := bstep (se 1 (by rfl) ⟨26518076, by rfl⟩ : syracuseStep 35357435 = 53036153) B53036153
theorem B23571623 : Blo 2179435 23571623 := bstep (se 1 (by rfl) ⟨17678717, by rfl⟩ : syracuseStep 23571623 = 35357435) B35357435
theorem B15714415 : Blo 2179435 15714415 := bstep (se 1 (by rfl) ⟨11785811, by rfl⟩ : syracuseStep 15714415 = 23571623) B23571623
theorem B83810213 : Blo 2179435 83810213 := bstep (se 4 (by rfl) ⟨7857207, by rfl⟩ : syracuseStep 83810213 = 15714415) B15714415
theorem B55873475 : Blo 2179435 55873475 := bstep (se 1 (by rfl) ⟨41905106, by rfl⟩ : syracuseStep 55873475 = 83810213) B83810213
theorem B37248983 : Blo 2179435 37248983 := bstep (se 1 (by rfl) ⟨27936737, by rfl⟩ : syracuseStep 37248983 = 55873475) B55873475
theorem B24832655 : Blo 2179435 24832655 := bstep (se 1 (by rfl) ⟨18624491, by rfl⟩ : syracuseStep 24832655 = 37248983) B37248983
theorem B16555103 : Blo 2179435 16555103 := bstep (se 1 (by rfl) ⟨12416327, by rfl⟩ : syracuseStep 16555103 = 24832655) B24832655
theorem B11036735 : Blo 2179435 11036735 := bstep (se 1 (by rfl) ⟨8277551, by rfl⟩ : syracuseStep 11036735 = 16555103) B16555103
theorem B7357823 : Blo 2179435 7357823 := bstep (se 1 (by rfl) ⟨5518367, by rfl⟩ : syracuseStep 7357823 = 11036735) B11036735
theorem B4905215 : Blo 2179435 4905215 := bstep (se 1 (by rfl) ⟨3678911, by rfl⟩ : syracuseStep 4905215 = 7357823) B7357823
theorem B3270143 : Blo 2179435 3270143 := bstep (se 1 (by rfl) ⟨2452607, by rfl⟩ : syracuseStep 3270143 = 4905215) B4905215
theorem B2180095 : Blo 2179435 2180095 := bstep (se 1 (by rfl) ⟨1635071, by rfl⟩ : syracuseStep 2180095 = 3270143) B3270143
theorem B3270149 : Blo 2179435 3270149 := bbase (se 4 (by rfl) ⟨306576, by rfl⟩ : syracuseStep 3270149 = 613153) (by norm_num)
theorem B2180099 : Blo 2179435 2180099 := bstep (se 1 (by rfl) ⟨1635074, by rfl⟩ : syracuseStep 2180099 = 3270149) B3270149
theorem B3678925 : Blo 2179435 3678925 := bbase (se 3 (by rfl) ⟨689798, by rfl⟩ : syracuseStep 3678925 = 1379597) (by norm_num)
theorem B4905233 : Blo 2179435 4905233 := bstep (se 2 (by rfl) ⟨1839462, by rfl⟩ : syracuseStep 4905233 = 3678925) B3678925
theorem B3270155 : Blo 2179435 3270155 := bstep (se 1 (by rfl) ⟨2452616, by rfl⟩ : syracuseStep 3270155 = 4905233) B4905233
theorem B2180103 : Blo 2179435 2180103 := bstep (se 1 (by rfl) ⟨1635077, by rfl⟩ : syracuseStep 2180103 = 3270155) B3270155
theorem B2452621 : Blo 2179435 2452621 := bbase (se 3 (by rfl) ⟨459866, by rfl⟩ : syracuseStep 2452621 = 919733) (by norm_num)
theorem B3270161 : Blo 2179435 3270161 := bstep (se 2 (by rfl) ⟨1226310, by rfl⟩ : syracuseStep 3270161 = 2452621) B2452621
theorem B2180107 : Blo 2179435 2180107 := bstep (se 1 (by rfl) ⟨1635080, by rfl⟩ : syracuseStep 2180107 = 3270161) B3270161
theorem B7357877 : Blo 2179435 7357877 := bbase (se 5 (by rfl) ⟨344900, by rfl⟩ : syracuseStep 7357877 = 689801) (by norm_num)
theorem B4905251 : Blo 2179435 4905251 := bstep (se 1 (by rfl) ⟨3678938, by rfl⟩ : syracuseStep 4905251 = 7357877) B7357877
theorem B3270167 : Blo 2179435 3270167 := bstep (se 1 (by rfl) ⟨2452625, by rfl⟩ : syracuseStep 3270167 = 4905251) B4905251
theorem B2180111 : Blo 2179435 2180111 := bstep (se 1 (by rfl) ⟨1635083, by rfl⟩ : syracuseStep 2180111 = 3270167) B3270167
theorem B3270173 : Blo 2179435 3270173 := bbase (se 3 (by rfl) ⟨613157, by rfl⟩ : syracuseStep 3270173 = 1226315) (by norm_num)
theorem B2180115 : Blo 2179435 2180115 := bstep (se 1 (by rfl) ⟨1635086, by rfl⟩ : syracuseStep 2180115 = 3270173) B3270173
theorem B4905269 : Blo 2179435 4905269 := bbase (se 5 (by rfl) ⟨229934, by rfl⟩ : syracuseStep 4905269 = 459869) (by norm_num)
theorem B3270179 : Blo 2179435 3270179 := bstep (se 1 (by rfl) ⟨2452634, by rfl⟩ : syracuseStep 3270179 = 4905269) B4905269
theorem B2180119 : Blo 2179435 2180119 := bstep (se 1 (by rfl) ⟨1635089, by rfl⟩ : syracuseStep 2180119 = 3270179) B3270179
theorem B2796865 : Blo 2179435 2796865 := bbase (se 2 (by rfl) ⟨1048824, by rfl⟩ : syracuseStep 2796865 = 2097649) (by norm_num)
theorem B59666453 : Blo 2179435 59666453 := bstep (se 6 (by rfl) ⟨1398432, by rfl⟩ : syracuseStep 59666453 = 2796865) B2796865
theorem B39777635 : Blo 2179435 39777635 := bstep (se 1 (by rfl) ⟨29833226, by rfl⟩ : syracuseStep 39777635 = 59666453) B59666453
theorem B26518423 : Blo 2179435 26518423 := bstep (se 1 (by rfl) ⟨19888817, by rfl⟩ : syracuseStep 26518423 = 39777635) B39777635
theorem B35357897 : Blo 2179435 35357897 := bstep (se 2 (by rfl) ⟨13259211, by rfl⟩ : syracuseStep 35357897 = 26518423) B26518423
theorem B23571931 : Blo 2179435 23571931 := bstep (se 1 (by rfl) ⟨17678948, by rfl⟩ : syracuseStep 23571931 = 35357897) B35357897
theorem B31429241 : Blo 2179435 31429241 := bstep (se 2 (by rfl) ⟨11785965, by rfl⟩ : syracuseStep 31429241 = 23571931) B23571931
theorem B20952827 : Blo 2179435 20952827 := bstep (se 1 (by rfl) ⟨15714620, by rfl⟩ : syracuseStep 20952827 = 31429241) B31429241
theorem B13968551 : Blo 2179435 13968551 := bstep (se 1 (by rfl) ⟨10476413, by rfl⟩ : syracuseStep 13968551 = 20952827) B20952827
theorem B9312367 : Blo 2179435 9312367 := bstep (se 1 (by rfl) ⟨6984275, by rfl⟩ : syracuseStep 9312367 = 13968551) B13968551
theorem B12416489 : Blo 2179435 12416489 := bstep (se 2 (by rfl) ⟨4656183, by rfl⟩ : syracuseStep 12416489 = 9312367) B9312367
theorem B8277659 : Blo 2179435 8277659 := bstep (se 1 (by rfl) ⟨6208244, by rfl⟩ : syracuseStep 8277659 = 12416489) B12416489
theorem B5518439 : Blo 2179435 5518439 := bstep (se 1 (by rfl) ⟨4138829, by rfl⟩ : syracuseStep 5518439 = 8277659) B8277659
theorem B3678959 : Blo 2179435 3678959 := bstep (se 1 (by rfl) ⟨2759219, by rfl⟩ : syracuseStep 3678959 = 5518439) B5518439
theorem B2452639 : Blo 2179435 2452639 := bstep (se 1 (by rfl) ⟨1839479, by rfl⟩ : syracuseStep 2452639 = 3678959) B3678959
theorem B3270185 : Blo 2179435 3270185 := bstep (se 2 (by rfl) ⟨1226319, by rfl⟩ : syracuseStep 3270185 = 2452639) B2452639
theorem B2180123 : Blo 2179435 2180123 := bstep (se 1 (by rfl) ⟨1635092, by rfl⟩ : syracuseStep 2180123 = 3270185) B3270185
theorem B3539789 : Blo 2179435 3539789 := bbase (se 3 (by rfl) ⟨663710, by rfl⟩ : syracuseStep 3539789 = 1327421) (by norm_num)
theorem B2359859 : Blo 2179435 2359859 := bstep (se 1 (by rfl) ⟨1769894, by rfl⟩ : syracuseStep 2359859 = 3539789) B3539789
theorem B25171829 : Blo 2179435 25171829 := bstep (se 5 (by rfl) ⟨1179929, by rfl⟩ : syracuseStep 25171829 = 2359859) B2359859
theorem B16781219 : Blo 2179435 16781219 := bstep (se 1 (by rfl) ⟨12585914, by rfl⟩ : syracuseStep 16781219 = 25171829) B25171829
theorem B11187479 : Blo 2179435 11187479 := bstep (se 1 (by rfl) ⟨8390609, by rfl⟩ : syracuseStep 11187479 = 16781219) B16781219
theorem B29833277 : Blo 2179435 29833277 := bstep (se 3 (by rfl) ⟨5593739, by rfl⟩ : syracuseStep 29833277 = 11187479) B11187479
theorem B79555405 : Blo 2179435 79555405 := bstep (se 3 (by rfl) ⟨14916638, by rfl⟩ : syracuseStep 79555405 = 29833277) B29833277
theorem B106073873 : Blo 2179435 106073873 := bstep (se 2 (by rfl) ⟨39777702, by rfl⟩ : syracuseStep 106073873 = 79555405) B79555405
theorem B70715915 : Blo 2179435 70715915 := bstep (se 1 (by rfl) ⟨53036936, by rfl⟩ : syracuseStep 70715915 = 106073873) B106073873
theorem B47143943 : Blo 2179435 47143943 := bstep (se 1 (by rfl) ⟨35357957, by rfl⟩ : syracuseStep 47143943 = 70715915) B70715915
theorem B31429295 : Blo 2179435 31429295 := bstep (se 1 (by rfl) ⟨23571971, by rfl⟩ : syracuseStep 31429295 = 47143943) B47143943
theorem B20952863 : Blo 2179435 20952863 := bstep (se 1 (by rfl) ⟨15714647, by rfl⟩ : syracuseStep 20952863 = 31429295) B31429295
theorem B13968575 : Blo 2179435 13968575 := bstep (se 1 (by rfl) ⟨10476431, by rfl⟩ : syracuseStep 13968575 = 20952863) B20952863
theorem B9312383 : Blo 2179435 9312383 := bstep (se 1 (by rfl) ⟨6984287, by rfl⟩ : syracuseStep 9312383 = 13968575) B13968575
theorem B6208255 : Blo 2179435 6208255 := bstep (se 1 (by rfl) ⟨4656191, by rfl⟩ : syracuseStep 6208255 = 9312383) B9312383
theorem B8277673 : Blo 2179435 8277673 := bstep (se 2 (by rfl) ⟨3104127, by rfl⟩ : syracuseStep 8277673 = 6208255) B6208255
theorem B11036897 : Blo 2179435 11036897 := bstep (se 2 (by rfl) ⟨4138836, by rfl⟩ : syracuseStep 11036897 = 8277673) B8277673
theorem B7357931 : Blo 2179435 7357931 := bstep (se 1 (by rfl) ⟨5518448, by rfl⟩ : syracuseStep 7357931 = 11036897) B11036897
theorem B4905287 : Blo 2179435 4905287 := bstep (se 1 (by rfl) ⟨3678965, by rfl⟩ : syracuseStep 4905287 = 7357931) B7357931
theorem B3270191 : Blo 2179435 3270191 := bstep (se 1 (by rfl) ⟨2452643, by rfl⟩ : syracuseStep 3270191 = 4905287) B4905287
theorem B2180127 : Blo 2179435 2180127 := bstep (se 1 (by rfl) ⟨1635095, by rfl⟩ : syracuseStep 2180127 = 3270191) B3270191
theorem B3270197 : Blo 2179435 3270197 := bbase (se 5 (by rfl) ⟨153290, by rfl⟩ : syracuseStep 3270197 = 306581) (by norm_num)
theorem B2180131 : Blo 2179435 2180131 := bstep (se 1 (by rfl) ⟨1635098, by rfl⟩ : syracuseStep 2180131 = 3270197) B3270197
theorem B5518469 : Blo 2179435 5518469 := bbase (se 4 (by rfl) ⟨517356, by rfl⟩ : syracuseStep 5518469 = 1034713) (by norm_num)
theorem B3678979 : Blo 2179435 3678979 := bstep (se 1 (by rfl) ⟨2759234, by rfl⟩ : syracuseStep 3678979 = 5518469) B5518469
theorem B4905305 : Blo 2179435 4905305 := bstep (se 2 (by rfl) ⟨1839489, by rfl⟩ : syracuseStep 4905305 = 3678979) B3678979
theorem B3270203 : Blo 2179435 3270203 := bstep (se 1 (by rfl) ⟨2452652, by rfl⟩ : syracuseStep 3270203 = 4905305) B4905305
theorem B2180135 : Blo 2179435 2180135 := bstep (se 1 (by rfl) ⟨1635101, by rfl⟩ : syracuseStep 2180135 = 3270203) B3270203
theorem B2452657 : Blo 2179435 2452657 := bbase (se 2 (by rfl) ⟨919746, by rfl⟩ : syracuseStep 2452657 = 1839493) (by norm_num)
theorem B3270209 : Blo 2179435 3270209 := bstep (se 2 (by rfl) ⟨1226328, by rfl⟩ : syracuseStep 3270209 = 2452657) B2452657
theorem B2180139 : Blo 2179435 2180139 := bstep (se 1 (by rfl) ⟨1635104, by rfl⟩ : syracuseStep 2180139 = 3270209) B3270209
theorem B2328113 : Blo 2179435 2328113 := bbase (se 2 (by rfl) ⟨873042, by rfl⟩ : syracuseStep 2328113 = 1746085) (by norm_num)
theorem B6208301 : Blo 2179435 6208301 := bstep (se 3 (by rfl) ⟨1164056, by rfl⟩ : syracuseStep 6208301 = 2328113) B2328113
theorem B4138867 : Blo 2179435 4138867 := bstep (se 1 (by rfl) ⟨3104150, by rfl⟩ : syracuseStep 4138867 = 6208301) B6208301
theorem B5518489 : Blo 2179435 5518489 := bstep (se 2 (by rfl) ⟨2069433, by rfl⟩ : syracuseStep 5518489 = 4138867) B4138867
theorem B7357985 : Blo 2179435 7357985 := bstep (se 2 (by rfl) ⟨2759244, by rfl⟩ : syracuseStep 7357985 = 5518489) B5518489
theorem B4905323 : Blo 2179435 4905323 := bstep (se 1 (by rfl) ⟨3678992, by rfl⟩ : syracuseStep 4905323 = 7357985) B7357985
theorem B3270215 : Blo 2179435 3270215 := bstep (se 1 (by rfl) ⟨2452661, by rfl⟩ : syracuseStep 3270215 = 4905323) B4905323
theorem B2180143 : Blo 2179435 2180143 := bstep (se 1 (by rfl) ⟨1635107, by rfl⟩ : syracuseStep 2180143 = 3270215) B3270215
theorem B3270221 : Blo 2179435 3270221 := bbase (se 3 (by rfl) ⟨613166, by rfl⟩ : syracuseStep 3270221 = 1226333) (by norm_num)
theorem B2180147 : Blo 2179435 2180147 := bstep (se 1 (by rfl) ⟨1635110, by rfl⟩ : syracuseStep 2180147 = 3270221) B3270221
theorem B4905341 : Blo 2179435 4905341 := bbase (se 3 (by rfl) ⟨919751, by rfl⟩ : syracuseStep 4905341 = 1839503) (by norm_num)
theorem B3270227 : Blo 2179435 3270227 := bstep (se 1 (by rfl) ⟨2452670, by rfl⟩ : syracuseStep 3270227 = 4905341) B4905341
theorem B2180151 : Blo 2179435 2180151 := bstep (se 1 (by rfl) ⟨1635113, by rfl⟩ : syracuseStep 2180151 = 3270227) B3270227
theorem B3679013 : Blo 2179435 3679013 := bbase (se 4 (by rfl) ⟨344907, by rfl⟩ : syracuseStep 3679013 = 689815) (by norm_num)
theorem B2452675 : Blo 2179435 2452675 := bstep (se 1 (by rfl) ⟨1839506, by rfl⟩ : syracuseStep 2452675 = 3679013) B3679013
theorem B3270233 : Blo 2179435 3270233 := bstep (se 2 (by rfl) ⟨1226337, by rfl⟩ : syracuseStep 3270233 = 2452675) B2452675
theorem B2180155 : Blo 2179435 2180155 := bstep (se 1 (by rfl) ⟨1635116, by rfl⟩ : syracuseStep 2180155 = 3270233) B3270233
theorem B3104173 : Blo 2179435 3104173 := bbase (se 3 (by rfl) ⟨582032, by rfl⟩ : syracuseStep 3104173 = 1164065) (by norm_num)
theorem B16555589 : Blo 2179435 16555589 := bstep (se 4 (by rfl) ⟨1552086, by rfl⟩ : syracuseStep 16555589 = 3104173) B3104173
theorem B11037059 : Blo 2179435 11037059 := bstep (se 1 (by rfl) ⟨8277794, by rfl⟩ : syracuseStep 11037059 = 16555589) B16555589
theorem B7358039 : Blo 2179435 7358039 := bstep (se 1 (by rfl) ⟨5518529, by rfl⟩ : syracuseStep 7358039 = 11037059) B11037059
theorem B4905359 : Blo 2179435 4905359 := bstep (se 1 (by rfl) ⟨3679019, by rfl⟩ : syracuseStep 4905359 = 7358039) B7358039
theorem B3270239 : Blo 2179435 3270239 := bstep (se 1 (by rfl) ⟨2452679, by rfl⟩ : syracuseStep 3270239 = 4905359) B4905359
theorem B2180159 : Blo 2179435 2180159 := bstep (se 1 (by rfl) ⟨1635119, by rfl⟩ : syracuseStep 2180159 = 3270239) B3270239
theorem B3270245 : Blo 2179435 3270245 := bbase (se 4 (by rfl) ⟨306585, by rfl⟩ : syracuseStep 3270245 = 613171) (by norm_num)
theorem B2180163 : Blo 2179435 2180163 := bstep (se 1 (by rfl) ⟨1635122, by rfl⟩ : syracuseStep 2180163 = 3270245) B3270245
theorem B2619157 : Blo 2179435 2619157 := bbase (se 6 (by rfl) ⟨61386, by rfl⟩ : syracuseStep 2619157 = 122773) (by norm_num)
theorem B3492209 : Blo 2179435 3492209 := bstep (se 2 (by rfl) ⟨1309578, by rfl⟩ : syracuseStep 3492209 = 2619157) B2619157
theorem B2328139 : Blo 2179435 2328139 := bstep (se 1 (by rfl) ⟨1746104, by rfl⟩ : syracuseStep 2328139 = 3492209) B3492209
theorem B3104185 : Blo 2179435 3104185 := bstep (se 2 (by rfl) ⟨1164069, by rfl⟩ : syracuseStep 3104185 = 2328139) B2328139
theorem B4138913 : Blo 2179435 4138913 := bstep (se 2 (by rfl) ⟨1552092, by rfl⟩ : syracuseStep 4138913 = 3104185) B3104185
theorem B2759275 : Blo 2179435 2759275 := bstep (se 1 (by rfl) ⟨2069456, by rfl⟩ : syracuseStep 2759275 = 4138913) B4138913
theorem B3679033 : Blo 2179435 3679033 := bstep (se 2 (by rfl) ⟨1379637, by rfl⟩ : syracuseStep 3679033 = 2759275) B2759275
theorem B4905377 : Blo 2179435 4905377 := bstep (se 2 (by rfl) ⟨1839516, by rfl⟩ : syracuseStep 4905377 = 3679033) B3679033
theorem B3270251 : Blo 2179435 3270251 := bstep (se 1 (by rfl) ⟨2452688, by rfl⟩ : syracuseStep 3270251 = 4905377) B4905377
theorem B2180167 : Blo 2179435 2180167 := bstep (se 1 (by rfl) ⟨1635125, by rfl⟩ : syracuseStep 2180167 = 3270251) B3270251
theorem B2452693 : Blo 2179435 2452693 := bbase (se 7 (by rfl) ⟨28742, by rfl⟩ : syracuseStep 2452693 = 57485) (by norm_num)
theorem B3270257 : Blo 2179435 3270257 := bstep (se 2 (by rfl) ⟨1226346, by rfl⟩ : syracuseStep 3270257 = 2452693) B2452693
theorem B2180171 : Blo 2179435 2180171 := bstep (se 1 (by rfl) ⟨1635128, by rfl⟩ : syracuseStep 2180171 = 3270257) B3270257
theorem B2759285 : Blo 2179435 2759285 := bbase (se 5 (by rfl) ⟨129341, by rfl⟩ : syracuseStep 2759285 = 258683) (by norm_num)
theorem B7358093 : Blo 2179435 7358093 := bstep (se 3 (by rfl) ⟨1379642, by rfl⟩ : syracuseStep 7358093 = 2759285) B2759285
theorem B4905395 : Blo 2179435 4905395 := bstep (se 1 (by rfl) ⟨3679046, by rfl⟩ : syracuseStep 4905395 = 7358093) B7358093
theorem B3270263 : Blo 2179435 3270263 := bstep (se 1 (by rfl) ⟨2452697, by rfl⟩ : syracuseStep 3270263 = 4905395) B4905395
theorem B2180175 : Blo 2179435 2180175 := bstep (se 1 (by rfl) ⟨1635131, by rfl⟩ : syracuseStep 2180175 = 3270263) B3270263
theorem B3270269 : Blo 2179435 3270269 := bbase (se 3 (by rfl) ⟨613175, by rfl⟩ : syracuseStep 3270269 = 1226351) (by norm_num)
theorem B2180179 : Blo 2179435 2180179 := bstep (se 1 (by rfl) ⟨1635134, by rfl⟩ : syracuseStep 2180179 = 3270269) B3270269
theorem B4905413 : Blo 2179435 4905413 := bbase (se 4 (by rfl) ⟨459882, by rfl⟩ : syracuseStep 4905413 = 919765) (by norm_num)
theorem B3270275 : Blo 2179435 3270275 := bstep (se 1 (by rfl) ⟨2452706, by rfl⟩ : syracuseStep 3270275 = 4905413) B4905413
theorem B2180183 : Blo 2179435 2180183 := bstep (se 1 (by rfl) ⟨1635137, by rfl⟩ : syracuseStep 2180183 = 3270275) B3270275
theorem B5893157 : Blo 2179435 5893157 := bbase (se 4 (by rfl) ⟨552483, by rfl⟩ : syracuseStep 5893157 = 1104967) (by norm_num)
theorem B3928771 : Blo 2179435 3928771 := bstep (se 1 (by rfl) ⟨2946578, by rfl⟩ : syracuseStep 3928771 = 5893157) B5893157
theorem B5238361 : Blo 2179435 5238361 := bstep (se 2 (by rfl) ⟨1964385, by rfl⟩ : syracuseStep 5238361 = 3928771) B3928771
theorem B6984481 : Blo 2179435 6984481 := bstep (se 2 (by rfl) ⟨2619180, by rfl⟩ : syracuseStep 6984481 = 5238361) B5238361
theorem B9312641 : Blo 2179435 9312641 := bstep (se 2 (by rfl) ⟨3492240, by rfl⟩ : syracuseStep 9312641 = 6984481) B6984481
theorem B6208427 : Blo 2179435 6208427 := bstep (se 1 (by rfl) ⟨4656320, by rfl⟩ : syracuseStep 6208427 = 9312641) B9312641
theorem B4138951 : Blo 2179435 4138951 := bstep (se 1 (by rfl) ⟨3104213, by rfl⟩ : syracuseStep 4138951 = 6208427) B6208427
theorem B5518601 : Blo 2179435 5518601 := bstep (se 2 (by rfl) ⟨2069475, by rfl⟩ : syracuseStep 5518601 = 4138951) B4138951
theorem B3679067 : Blo 2179435 3679067 := bstep (se 1 (by rfl) ⟨2759300, by rfl⟩ : syracuseStep 3679067 = 5518601) B5518601
theorem B2452711 : Blo 2179435 2452711 := bstep (se 1 (by rfl) ⟨1839533, by rfl⟩ : syracuseStep 2452711 = 3679067) B3679067
theorem B3270281 : Blo 2179435 3270281 := bstep (se 2 (by rfl) ⟨1226355, by rfl⟩ : syracuseStep 3270281 = 2452711) B2452711
theorem B2180187 : Blo 2179435 2180187 := bstep (se 1 (by rfl) ⟨1635140, by rfl⟩ : syracuseStep 2180187 = 3270281) B3270281
theorem B11037221 : Blo 2179435 11037221 := bbase (se 4 (by rfl) ⟨1034739, by rfl⟩ : syracuseStep 11037221 = 2069479) (by norm_num)
theorem B7358147 : Blo 2179435 7358147 := bstep (se 1 (by rfl) ⟨5518610, by rfl⟩ : syracuseStep 7358147 = 11037221) B11037221
theorem B4905431 : Blo 2179435 4905431 := bstep (se 1 (by rfl) ⟨3679073, by rfl⟩ : syracuseStep 4905431 = 7358147) B7358147
theorem B3270287 : Blo 2179435 3270287 := bstep (se 1 (by rfl) ⟨2452715, by rfl⟩ : syracuseStep 3270287 = 4905431) B4905431
theorem B2180191 : Blo 2179435 2180191 := bstep (se 1 (by rfl) ⟨1635143, by rfl⟩ : syracuseStep 2180191 = 3270287) B3270287
theorem B3270293 : Blo 2179435 3270293 := bbase (se 6 (by rfl) ⟨76647, by rfl⟩ : syracuseStep 3270293 = 153295) (by norm_num)
theorem B2180195 : Blo 2179435 2180195 := bstep (se 1 (by rfl) ⟨1635146, by rfl⟩ : syracuseStep 2180195 = 3270293) B3270293
theorem B5238389 : Blo 2179435 5238389 := bbase (se 5 (by rfl) ⟨245549, by rfl⟩ : syracuseStep 5238389 = 491099) (by norm_num)
theorem B13969037 : Blo 2179435 13969037 := bstep (se 3 (by rfl) ⟨2619194, by rfl⟩ : syracuseStep 13969037 = 5238389) B5238389
theorem B9312691 : Blo 2179435 9312691 := bstep (se 1 (by rfl) ⟨6984518, by rfl⟩ : syracuseStep 9312691 = 13969037) B13969037
theorem B12416921 : Blo 2179435 12416921 := bstep (se 2 (by rfl) ⟨4656345, by rfl⟩ : syracuseStep 12416921 = 9312691) B9312691
theorem B8277947 : Blo 2179435 8277947 := bstep (se 1 (by rfl) ⟨6208460, by rfl⟩ : syracuseStep 8277947 = 12416921) B12416921
theorem B5518631 : Blo 2179435 5518631 := bstep (se 1 (by rfl) ⟨4138973, by rfl⟩ : syracuseStep 5518631 = 8277947) B8277947
theorem B3679087 : Blo 2179435 3679087 := bstep (se 1 (by rfl) ⟨2759315, by rfl⟩ : syracuseStep 3679087 = 5518631) B5518631
theorem B4905449 : Blo 2179435 4905449 := bstep (se 2 (by rfl) ⟨1839543, by rfl⟩ : syracuseStep 4905449 = 3679087) B3679087
theorem B3270299 : Blo 2179435 3270299 := bstep (se 1 (by rfl) ⟨2452724, by rfl⟩ : syracuseStep 3270299 = 4905449) B4905449
theorem B2180199 : Blo 2179435 2180199 := bstep (se 1 (by rfl) ⟨1635149, by rfl⟩ : syracuseStep 2180199 = 3270299) B3270299
theorem B2452729 : Blo 2179435 2452729 := bbase (se 2 (by rfl) ⟨919773, by rfl⟩ : syracuseStep 2452729 = 1839547) (by norm_num)
theorem B3270305 : Blo 2179435 3270305 := bstep (se 2 (by rfl) ⟨1226364, by rfl⟩ : syracuseStep 3270305 = 2452729) B2452729
theorem B2180203 : Blo 2179435 2180203 := bstep (se 1 (by rfl) ⟨1635152, by rfl⟩ : syracuseStep 2180203 = 3270305) B3270305
theorem B9312725 : Blo 2179435 9312725 := bbase (se 7 (by rfl) ⟨109133, by rfl⟩ : syracuseStep 9312725 = 218267) (by norm_num)
theorem B6208483 : Blo 2179435 6208483 := bstep (se 1 (by rfl) ⟨4656362, by rfl⟩ : syracuseStep 6208483 = 9312725) B9312725
theorem B8277977 : Blo 2179435 8277977 := bstep (se 2 (by rfl) ⟨3104241, by rfl⟩ : syracuseStep 8277977 = 6208483) B6208483
theorem B5518651 : Blo 2179435 5518651 := bstep (se 1 (by rfl) ⟨4138988, by rfl⟩ : syracuseStep 5518651 = 8277977) B8277977
theorem B7358201 : Blo 2179435 7358201 := bstep (se 2 (by rfl) ⟨2759325, by rfl⟩ : syracuseStep 7358201 = 5518651) B5518651
theorem B4905467 : Blo 2179435 4905467 := bstep (se 1 (by rfl) ⟨3679100, by rfl⟩ : syracuseStep 4905467 = 7358201) B7358201
theorem B3270311 : Blo 2179435 3270311 := bstep (se 1 (by rfl) ⟨2452733, by rfl⟩ : syracuseStep 3270311 = 4905467) B4905467
theorem B2180207 : Blo 2179435 2180207 := bstep (se 1 (by rfl) ⟨1635155, by rfl⟩ : syracuseStep 2180207 = 3270311) B3270311
theorem B3270317 : Blo 2179435 3270317 := bbase (se 3 (by rfl) ⟨613184, by rfl⟩ : syracuseStep 3270317 = 1226369) (by norm_num)
theorem B2180211 : Blo 2179435 2180211 := bstep (se 1 (by rfl) ⟨1635158, by rfl⟩ : syracuseStep 2180211 = 3270317) B3270317
theorem B4905485 : Blo 2179435 4905485 := bbase (se 3 (by rfl) ⟨919778, by rfl⟩ : syracuseStep 4905485 = 1839557) (by norm_num)
theorem B3270323 : Blo 2179435 3270323 := bstep (se 1 (by rfl) ⟨2452742, by rfl⟩ : syracuseStep 3270323 = 4905485) B4905485
theorem B2180215 : Blo 2179435 2180215 := bstep (se 1 (by rfl) ⟨1635161, by rfl⟩ : syracuseStep 2180215 = 3270323) B3270323
theorem B2759341 : Blo 2179435 2759341 := bbase (se 3 (by rfl) ⟨517376, by rfl⟩ : syracuseStep 2759341 = 1034753) (by norm_num)
theorem B3679121 : Blo 2179435 3679121 := bstep (se 2 (by rfl) ⟨1379670, by rfl⟩ : syracuseStep 3679121 = 2759341) B2759341
theorem B2452747 : Blo 2179435 2452747 := bstep (se 1 (by rfl) ⟨1839560, by rfl⟩ : syracuseStep 2452747 = 3679121) B3679121
theorem B3270329 : Blo 2179435 3270329 := bstep (se 2 (by rfl) ⟨1226373, by rfl⟩ : syracuseStep 3270329 = 2452747) B2452747
theorem B2180219 : Blo 2179435 2180219 := bstep (se 1 (by rfl) ⟨1635164, by rfl⟩ : syracuseStep 2180219 = 3270329) B3270329
theorem B5893253 : Blo 2179435 5893253 := bbase (se 4 (by rfl) ⟨552492, by rfl⟩ : syracuseStep 5893253 = 1104985) (by norm_num)
theorem B3928835 : Blo 2179435 3928835 := bstep (se 1 (by rfl) ⟨2946626, by rfl⟩ : syracuseStep 3928835 = 5893253) B5893253
theorem B2619223 : Blo 2179435 2619223 := bstep (se 1 (by rfl) ⟨1964417, by rfl⟩ : syracuseStep 2619223 = 3928835) B3928835
theorem B13969189 : Blo 2179435 13969189 := bstep (se 4 (by rfl) ⟨1309611, by rfl⟩ : syracuseStep 13969189 = 2619223) B2619223
theorem B18625585 : Blo 2179435 18625585 := bstep (se 2 (by rfl) ⟨6984594, by rfl⟩ : syracuseStep 18625585 = 13969189) B13969189
theorem B24834113 : Blo 2179435 24834113 := bstep (se 2 (by rfl) ⟨9312792, by rfl⟩ : syracuseStep 24834113 = 18625585) B18625585
theorem B16556075 : Blo 2179435 16556075 := bstep (se 1 (by rfl) ⟨12417056, by rfl⟩ : syracuseStep 16556075 = 24834113) B24834113
theorem B11037383 : Blo 2179435 11037383 := bstep (se 1 (by rfl) ⟨8278037, by rfl⟩ : syracuseStep 11037383 = 16556075) B16556075
theorem B7358255 : Blo 2179435 7358255 := bstep (se 1 (by rfl) ⟨5518691, by rfl⟩ : syracuseStep 7358255 = 11037383) B11037383
theorem B4905503 : Blo 2179435 4905503 := bstep (se 1 (by rfl) ⟨3679127, by rfl⟩ : syracuseStep 4905503 = 7358255) B7358255
theorem B3270335 : Blo 2179435 3270335 := bstep (se 1 (by rfl) ⟨2452751, by rfl⟩ : syracuseStep 3270335 = 4905503) B4905503
theorem B2180223 : Blo 2179435 2180223 := bstep (se 1 (by rfl) ⟨1635167, by rfl⟩ : syracuseStep 2180223 = 3270335) B3270335
theorem B3270341 : Blo 2179435 3270341 := bbase (se 4 (by rfl) ⟨306594, by rfl⟩ : syracuseStep 3270341 = 613189) (by norm_num)
theorem B2180227 : Blo 2179435 2180227 := bstep (se 1 (by rfl) ⟨1635170, by rfl⟩ : syracuseStep 2180227 = 3270341) B3270341
theorem B3679141 : Blo 2179435 3679141 := bbase (se 4 (by rfl) ⟨344919, by rfl⟩ : syracuseStep 3679141 = 689839) (by norm_num)
theorem B4905521 : Blo 2179435 4905521 := bstep (se 2 (by rfl) ⟨1839570, by rfl⟩ : syracuseStep 4905521 = 3679141) B3679141
theorem B3270347 : Blo 2179435 3270347 := bstep (se 1 (by rfl) ⟨2452760, by rfl⟩ : syracuseStep 3270347 = 4905521) B4905521
theorem B2180231 : Blo 2179435 2180231 := bstep (se 1 (by rfl) ⟨1635173, by rfl⟩ : syracuseStep 2180231 = 3270347) B3270347
theorem B2452765 : Blo 2179435 2452765 := bbase (se 3 (by rfl) ⟨459893, by rfl⟩ : syracuseStep 2452765 = 919787) (by norm_num)
theorem B3270353 : Blo 2179435 3270353 := bstep (se 2 (by rfl) ⟨1226382, by rfl⟩ : syracuseStep 3270353 = 2452765) B2452765
theorem B2180235 : Blo 2179435 2180235 := bstep (se 1 (by rfl) ⟨1635176, by rfl⟩ : syracuseStep 2180235 = 3270353) B3270353
theorem B7358309 : Blo 2179435 7358309 := bbase (se 4 (by rfl) ⟨689841, by rfl⟩ : syracuseStep 7358309 = 1379683) (by norm_num)
theorem B4905539 : Blo 2179435 4905539 := bstep (se 1 (by rfl) ⟨3679154, by rfl⟩ : syracuseStep 4905539 = 7358309) B7358309
theorem B3270359 : Blo 2179435 3270359 := bstep (se 1 (by rfl) ⟨2452769, by rfl⟩ : syracuseStep 3270359 = 4905539) B4905539
theorem B2180239 : Blo 2179435 2180239 := bstep (se 1 (by rfl) ⟨1635179, by rfl⟩ : syracuseStep 2180239 = 3270359) B3270359
theorem B3270365 : Blo 2179435 3270365 := bbase (se 3 (by rfl) ⟨613193, by rfl⟩ : syracuseStep 3270365 = 1226387) (by norm_num)
theorem B2180243 : Blo 2179435 2180243 := bstep (se 1 (by rfl) ⟨1635182, by rfl⟩ : syracuseStep 2180243 = 3270365) B3270365
theorem B4905557 : Blo 2179435 4905557 := bbase (se 8 (by rfl) ⟨28743, by rfl⟩ : syracuseStep 4905557 = 57487) (by norm_num)
theorem B3270371 : Blo 2179435 3270371 := bstep (se 1 (by rfl) ⟨2452778, by rfl⟩ : syracuseStep 3270371 = 4905557) B4905557
theorem B2180247 : Blo 2179435 2180247 := bstep (se 1 (by rfl) ⟨1635185, by rfl⟩ : syracuseStep 2180247 = 3270371) B3270371
theorem B3982493 : Blo 2179435 3982493 := bbase (se 3 (by rfl) ⟨746717, by rfl⟩ : syracuseStep 3982493 = 1493435) (by norm_num)
theorem B10619981 : Blo 2179435 10619981 := bstep (se 3 (by rfl) ⟨1991246, by rfl⟩ : syracuseStep 10619981 = 3982493) B3982493
theorem B7079987 : Blo 2179435 7079987 := bstep (se 1 (by rfl) ⟨5309990, by rfl⟩ : syracuseStep 7079987 = 10619981) B10619981
theorem B4719991 : Blo 2179435 4719991 := bstep (se 1 (by rfl) ⟨3539993, by rfl⟩ : syracuseStep 4719991 = 7079987) B7079987
theorem B6293321 : Blo 2179435 6293321 := bstep (se 2 (by rfl) ⟨2359995, by rfl⟩ : syracuseStep 6293321 = 4719991) B4719991
theorem B4195547 : Blo 2179435 4195547 := bstep (se 1 (by rfl) ⟨3146660, by rfl⟩ : syracuseStep 4195547 = 6293321) B6293321
theorem B2797031 : Blo 2179435 2797031 := bstep (se 1 (by rfl) ⟨2097773, by rfl⟩ : syracuseStep 2797031 = 4195547) B4195547
theorem B7458749 : Blo 2179435 7458749 := bstep (se 3 (by rfl) ⟨1398515, by rfl⟩ : syracuseStep 7458749 = 2797031) B2797031
theorem B4972499 : Blo 2179435 4972499 := bstep (se 1 (by rfl) ⟨3729374, by rfl⟩ : syracuseStep 4972499 = 7458749) B7458749
theorem B3314999 : Blo 2179435 3314999 := bstep (se 1 (by rfl) ⟨2486249, by rfl⟩ : syracuseStep 3314999 = 4972499) B4972499
theorem B2209999 : Blo 2179435 2209999 := bstep (se 1 (by rfl) ⟨1657499, by rfl⟩ : syracuseStep 2209999 = 3314999) B3314999
theorem B2946665 : Blo 2179435 2946665 := bstep (se 2 (by rfl) ⟨1104999, by rfl⟩ : syracuseStep 2946665 = 2209999) B2209999
theorem B7857773 : Blo 2179435 7857773 := bstep (se 3 (by rfl) ⟨1473332, by rfl⟩ : syracuseStep 7857773 = 2946665) B2946665
theorem B5238515 : Blo 2179435 5238515 := bstep (se 1 (by rfl) ⟨3928886, by rfl⟩ : syracuseStep 5238515 = 7857773) B7857773
theorem B3492343 : Blo 2179435 3492343 := bstep (se 1 (by rfl) ⟨2619257, by rfl⟩ : syracuseStep 3492343 = 5238515) B5238515
theorem B4656457 : Blo 2179435 4656457 := bstep (se 2 (by rfl) ⟨1746171, by rfl⟩ : syracuseStep 4656457 = 3492343) B3492343
theorem B6208609 : Blo 2179435 6208609 := bstep (se 2 (by rfl) ⟨2328228, by rfl⟩ : syracuseStep 6208609 = 4656457) B4656457
theorem B8278145 : Blo 2179435 8278145 := bstep (se 2 (by rfl) ⟨3104304, by rfl⟩ : syracuseStep 8278145 = 6208609) B6208609
theorem B5518763 : Blo 2179435 5518763 := bstep (se 1 (by rfl) ⟨4139072, by rfl⟩ : syracuseStep 5518763 = 8278145) B8278145
theorem B3679175 : Blo 2179435 3679175 := bstep (se 1 (by rfl) ⟨2759381, by rfl⟩ : syracuseStep 3679175 = 5518763) B5518763
theorem B2452783 : Blo 2179435 2452783 := bstep (se 1 (by rfl) ⟨1839587, by rfl⟩ : syracuseStep 2452783 = 3679175) B3679175
theorem B3270377 : Blo 2179435 3270377 := bstep (se 2 (by rfl) ⟨1226391, by rfl⟩ : syracuseStep 3270377 = 2452783) B2452783
theorem B2180251 : Blo 2179435 2180251 := bstep (se 1 (by rfl) ⟨1635188, by rfl⟩ : syracuseStep 2180251 = 3270377) B3270377
theorem B5594069 : Blo 2179435 5594069 := bbase (se 7 (by rfl) ⟨65555, by rfl⟩ : syracuseStep 5594069 = 131111) (by norm_num)
theorem B14917517 : Blo 2179435 14917517 := bstep (se 3 (by rfl) ⟨2797034, by rfl⟩ : syracuseStep 14917517 = 5594069) B5594069
theorem B9945011 : Blo 2179435 9945011 := bstep (se 1 (by rfl) ⟨7458758, by rfl⟩ : syracuseStep 9945011 = 14917517) B14917517
theorem B6630007 : Blo 2179435 6630007 := bstep (se 1 (by rfl) ⟨4972505, by rfl⟩ : syracuseStep 6630007 = 9945011) B9945011
theorem B8840009 : Blo 2179435 8840009 := bstep (se 2 (by rfl) ⟨3315003, by rfl⟩ : syracuseStep 8840009 = 6630007) B6630007
theorem B5893339 : Blo 2179435 5893339 := bstep (se 1 (by rfl) ⟨4420004, by rfl⟩ : syracuseStep 5893339 = 8840009) B8840009
theorem B7857785 : Blo 2179435 7857785 := bstep (se 2 (by rfl) ⟨2946669, by rfl⟩ : syracuseStep 7857785 = 5893339) B5893339
theorem B5238523 : Blo 2179435 5238523 := bstep (se 1 (by rfl) ⟨3928892, by rfl⟩ : syracuseStep 5238523 = 7857785) B7857785
theorem B27938789 : Blo 2179435 27938789 := bstep (se 4 (by rfl) ⟨2619261, by rfl⟩ : syracuseStep 27938789 = 5238523) B5238523
theorem B18625859 : Blo 2179435 18625859 := bstep (se 1 (by rfl) ⟨13969394, by rfl⟩ : syracuseStep 18625859 = 27938789) B27938789
theorem B12417239 : Blo 2179435 12417239 := bstep (se 1 (by rfl) ⟨9312929, by rfl⟩ : syracuseStep 12417239 = 18625859) B18625859
theorem B8278159 : Blo 2179435 8278159 := bstep (se 1 (by rfl) ⟨6208619, by rfl⟩ : syracuseStep 8278159 = 12417239) B12417239
theorem B11037545 : Blo 2179435 11037545 := bstep (se 2 (by rfl) ⟨4139079, by rfl⟩ : syracuseStep 11037545 = 8278159) B8278159
theorem B7358363 : Blo 2179435 7358363 := bstep (se 1 (by rfl) ⟨5518772, by rfl⟩ : syracuseStep 7358363 = 11037545) B11037545
theorem B4905575 : Blo 2179435 4905575 := bstep (se 1 (by rfl) ⟨3679181, by rfl⟩ : syracuseStep 4905575 = 7358363) B7358363
theorem B3270383 : Blo 2179435 3270383 := bstep (se 1 (by rfl) ⟨2452787, by rfl⟩ : syracuseStep 3270383 = 4905575) B4905575
theorem B2180255 : Blo 2179435 2180255 := bstep (se 1 (by rfl) ⟨1635191, by rfl⟩ : syracuseStep 2180255 = 3270383) B3270383
theorem B3270389 : Blo 2179435 3270389 := bbase (se 5 (by rfl) ⟨153299, by rfl⟩ : syracuseStep 3270389 = 306599) (by norm_num)
theorem B2180259 : Blo 2179435 2180259 := bstep (se 1 (by rfl) ⟨1635194, by rfl⟩ : syracuseStep 2180259 = 3270389) B3270389
theorem B9312965 : Blo 2179435 9312965 := bbase (se 4 (by rfl) ⟨873090, by rfl⟩ : syracuseStep 9312965 = 1746181) (by norm_num)
theorem B6208643 : Blo 2179435 6208643 := bstep (se 1 (by rfl) ⟨4656482, by rfl⟩ : syracuseStep 6208643 = 9312965) B9312965
theorem B4139095 : Blo 2179435 4139095 := bstep (se 1 (by rfl) ⟨3104321, by rfl⟩ : syracuseStep 4139095 = 6208643) B6208643
theorem B5518793 : Blo 2179435 5518793 := bstep (se 2 (by rfl) ⟨2069547, by rfl⟩ : syracuseStep 5518793 = 4139095) B4139095
theorem B3679195 : Blo 2179435 3679195 := bstep (se 1 (by rfl) ⟨2759396, by rfl⟩ : syracuseStep 3679195 = 5518793) B5518793
theorem B4905593 : Blo 2179435 4905593 := bstep (se 2 (by rfl) ⟨1839597, by rfl⟩ : syracuseStep 4905593 = 3679195) B3679195
theorem B3270395 : Blo 2179435 3270395 := bstep (se 1 (by rfl) ⟨2452796, by rfl⟩ : syracuseStep 3270395 = 4905593) B4905593
theorem B2180263 : Blo 2179435 2180263 := bstep (se 1 (by rfl) ⟨1635197, by rfl⟩ : syracuseStep 2180263 = 3270395) B3270395
theorem B2452801 : Blo 2179435 2452801 := bbase (se 2 (by rfl) ⟨919800, by rfl⟩ : syracuseStep 2452801 = 1839601) (by norm_num)
theorem B3270401 : Blo 2179435 3270401 := bstep (se 2 (by rfl) ⟨1226400, by rfl⟩ : syracuseStep 3270401 = 2452801) B2452801
theorem B2180267 : Blo 2179435 2180267 := bstep (se 1 (by rfl) ⟨1635200, by rfl⟩ : syracuseStep 2180267 = 3270401) B3270401
theorem B5518813 : Blo 2179435 5518813 := bbase (se 3 (by rfl) ⟨1034777, by rfl⟩ : syracuseStep 5518813 = 2069555) (by norm_num)
theorem B7358417 : Blo 2179435 7358417 := bstep (se 2 (by rfl) ⟨2759406, by rfl⟩ : syracuseStep 7358417 = 5518813) B5518813
theorem B4905611 : Blo 2179435 4905611 := bstep (se 1 (by rfl) ⟨3679208, by rfl⟩ : syracuseStep 4905611 = 7358417) B7358417
theorem B3270407 : Blo 2179435 3270407 := bstep (se 1 (by rfl) ⟨2452805, by rfl⟩ : syracuseStep 3270407 = 4905611) B4905611
theorem B2180271 : Blo 2179435 2180271 := bstep (se 1 (by rfl) ⟨1635203, by rfl⟩ : syracuseStep 2180271 = 3270407) B3270407
theorem B3270413 : Blo 2179435 3270413 := bbase (se 3 (by rfl) ⟨613202, by rfl⟩ : syracuseStep 3270413 = 1226405) (by norm_num)
theorem B2180275 : Blo 2179435 2180275 := bstep (se 1 (by rfl) ⟨1635206, by rfl⟩ : syracuseStep 2180275 = 3270413) B3270413
theorem B4905629 : Blo 2179435 4905629 := bbase (se 3 (by rfl) ⟨919805, by rfl⟩ : syracuseStep 4905629 = 1839611) (by norm_num)
theorem B3270419 : Blo 2179435 3270419 := bstep (se 1 (by rfl) ⟨2452814, by rfl⟩ : syracuseStep 3270419 = 4905629) B4905629
theorem B2180279 : Blo 2179435 2180279 := bstep (se 1 (by rfl) ⟨1635209, by rfl⟩ : syracuseStep 2180279 = 3270419) B3270419
theorem B3679229 : Blo 2179435 3679229 := bbase (se 3 (by rfl) ⟨689855, by rfl⟩ : syracuseStep 3679229 = 1379711) (by norm_num)
theorem B2452819 : Blo 2179435 2452819 := bstep (se 1 (by rfl) ⟨1839614, by rfl⟩ : syracuseStep 2452819 = 3679229) B3679229
theorem B3270425 : Blo 2179435 3270425 := bstep (se 2 (by rfl) ⟨1226409, by rfl⟩ : syracuseStep 3270425 = 2452819) B2452819
theorem B2180283 : Blo 2179435 2180283 := bstep (se 1 (by rfl) ⟨1635212, by rfl⟩ : syracuseStep 2180283 = 3270425) B3270425
theorem B4656533 : Blo 2179435 4656533 := bbase (se 6 (by rfl) ⟨109137, by rfl⟩ : syracuseStep 4656533 = 218275) (by norm_num)
theorem B12417421 : Blo 2179435 12417421 := bstep (se 3 (by rfl) ⟨2328266, by rfl⟩ : syracuseStep 12417421 = 4656533) B4656533
theorem B16556561 : Blo 2179435 16556561 := bstep (se 2 (by rfl) ⟨6208710, by rfl⟩ : syracuseStep 16556561 = 12417421) B12417421
theorem B11037707 : Blo 2179435 11037707 := bstep (se 1 (by rfl) ⟨8278280, by rfl⟩ : syracuseStep 11037707 = 16556561) B16556561
theorem B7358471 : Blo 2179435 7358471 := bstep (se 1 (by rfl) ⟨5518853, by rfl⟩ : syracuseStep 7358471 = 11037707) B11037707
theorem B4905647 : Blo 2179435 4905647 := bstep (se 1 (by rfl) ⟨3679235, by rfl⟩ : syracuseStep 4905647 = 7358471) B7358471
theorem B3270431 : Blo 2179435 3270431 := bstep (se 1 (by rfl) ⟨2452823, by rfl⟩ : syracuseStep 3270431 = 4905647) B4905647
theorem B2180287 : Blo 2179435 2180287 := bstep (se 1 (by rfl) ⟨1635215, by rfl⟩ : syracuseStep 2180287 = 3270431) B3270431
theorem B3270437 : Blo 2179435 3270437 := bbase (se 4 (by rfl) ⟨306603, by rfl⟩ : syracuseStep 3270437 = 613207) (by norm_num)
theorem B2180291 : Blo 2179435 2180291 := bstep (se 1 (by rfl) ⟨1635218, by rfl⟩ : syracuseStep 2180291 = 3270437) B3270437
theorem B2759437 : Blo 2179435 2759437 := bbase (se 3 (by rfl) ⟨517394, by rfl⟩ : syracuseStep 2759437 = 1034789) (by norm_num)
theorem B3679249 : Blo 2179435 3679249 := bstep (se 2 (by rfl) ⟨1379718, by rfl⟩ : syracuseStep 3679249 = 2759437) B2759437
theorem B4905665 : Blo 2179435 4905665 := bstep (se 2 (by rfl) ⟨1839624, by rfl⟩ : syracuseStep 4905665 = 3679249) B3679249
theorem B3270443 : Blo 2179435 3270443 := bstep (se 1 (by rfl) ⟨2452832, by rfl⟩ : syracuseStep 3270443 = 4905665) B4905665
theorem B2180295 : Blo 2179435 2180295 := bstep (se 1 (by rfl) ⟨1635221, by rfl⟩ : syracuseStep 2180295 = 3270443) B3270443
theorem B2452837 : Blo 2179435 2452837 := bbase (se 4 (by rfl) ⟨229953, by rfl⟩ : syracuseStep 2452837 = 459907) (by norm_num)
theorem B3270449 : Blo 2179435 3270449 := bstep (se 2 (by rfl) ⟨1226418, by rfl⟩ : syracuseStep 3270449 = 2452837) B2452837
theorem B2180299 : Blo 2179435 2180299 := bstep (se 1 (by rfl) ⟨1635224, by rfl⟩ : syracuseStep 2180299 = 3270449) B3270449
theorem B6208757 : Blo 2179435 6208757 := bbase (se 5 (by rfl) ⟨291035, by rfl⟩ : syracuseStep 6208757 = 582071) (by norm_num)
theorem B4139171 : Blo 2179435 4139171 := bstep (se 1 (by rfl) ⟨3104378, by rfl⟩ : syracuseStep 4139171 = 6208757) B6208757
theorem B2759447 : Blo 2179435 2759447 := bstep (se 1 (by rfl) ⟨2069585, by rfl⟩ : syracuseStep 2759447 = 4139171) B4139171
theorem B7358525 : Blo 2179435 7358525 := bstep (se 3 (by rfl) ⟨1379723, by rfl⟩ : syracuseStep 7358525 = 2759447) B2759447
theorem B4905683 : Blo 2179435 4905683 := bstep (se 1 (by rfl) ⟨3679262, by rfl⟩ : syracuseStep 4905683 = 7358525) B7358525
theorem B3270455 : Blo 2179435 3270455 := bstep (se 1 (by rfl) ⟨2452841, by rfl⟩ : syracuseStep 3270455 = 4905683) B4905683
theorem B2180303 : Blo 2179435 2180303 := bstep (se 1 (by rfl) ⟨1635227, by rfl⟩ : syracuseStep 2180303 = 3270455) B3270455
theorem B3270461 : Blo 2179435 3270461 := bbase (se 3 (by rfl) ⟨613211, by rfl⟩ : syracuseStep 3270461 = 1226423) (by norm_num)
theorem B2180307 : Blo 2179435 2180307 := bstep (se 1 (by rfl) ⟨1635230, by rfl⟩ : syracuseStep 2180307 = 3270461) B3270461
theorem B4905701 : Blo 2179435 4905701 := bbase (se 4 (by rfl) ⟨459909, by rfl⟩ : syracuseStep 4905701 = 919819) (by norm_num)
theorem B3270467 : Blo 2179435 3270467 := bstep (se 1 (by rfl) ⟨2452850, by rfl⟩ : syracuseStep 3270467 = 4905701) B4905701
theorem B2180311 : Blo 2179435 2180311 := bstep (se 1 (by rfl) ⟨1635233, by rfl⟩ : syracuseStep 2180311 = 3270467) B3270467
theorem B5518925 : Blo 2179435 5518925 := bbase (se 3 (by rfl) ⟨1034798, by rfl⟩ : syracuseStep 5518925 = 2069597) (by norm_num)
theorem B3679283 : Blo 2179435 3679283 := bstep (se 1 (by rfl) ⟨2759462, by rfl⟩ : syracuseStep 3679283 = 5518925) B5518925
theorem B2452855 : Blo 2179435 2452855 := bstep (se 1 (by rfl) ⟨1839641, by rfl⟩ : syracuseStep 2452855 = 3679283) B3679283
theorem B3270473 : Blo 2179435 3270473 := bstep (se 2 (by rfl) ⟨1226427, by rfl⟩ : syracuseStep 3270473 = 2452855) B2452855
theorem B2180315 : Blo 2179435 2180315 := bstep (se 1 (by rfl) ⟨1635236, by rfl⟩ : syracuseStep 2180315 = 3270473) B3270473
theorem B2328301 : Blo 2179435 2328301 := bbase (se 3 (by rfl) ⟨436556, by rfl⟩ : syracuseStep 2328301 = 873113) (by norm_num)
theorem B3104401 : Blo 2179435 3104401 := bstep (se 2 (by rfl) ⟨1164150, by rfl⟩ : syracuseStep 3104401 = 2328301) B2328301
theorem B4139201 : Blo 2179435 4139201 := bstep (se 2 (by rfl) ⟨1552200, by rfl⟩ : syracuseStep 4139201 = 3104401) B3104401
theorem B11037869 : Blo 2179435 11037869 := bstep (se 3 (by rfl) ⟨2069600, by rfl⟩ : syracuseStep 11037869 = 4139201) B4139201
theorem B7358579 : Blo 2179435 7358579 := bstep (se 1 (by rfl) ⟨5518934, by rfl⟩ : syracuseStep 7358579 = 11037869) B11037869
theorem B4905719 : Blo 2179435 4905719 := bstep (se 1 (by rfl) ⟨3679289, by rfl⟩ : syracuseStep 4905719 = 7358579) B7358579
theorem B3270479 : Blo 2179435 3270479 := bstep (se 1 (by rfl) ⟨2452859, by rfl⟩ : syracuseStep 3270479 = 4905719) B4905719
theorem B2180319 : Blo 2179435 2180319 := bstep (se 1 (by rfl) ⟨1635239, by rfl⟩ : syracuseStep 2180319 = 3270479) B3270479
theorem B3270485 : Blo 2179435 3270485 := bbase (se 9 (by rfl) ⟨9581, by rfl⟩ : syracuseStep 3270485 = 19163) (by norm_num)
theorem B2180323 : Blo 2179435 2180323 := bstep (se 1 (by rfl) ⟨1635242, by rfl⟩ : syracuseStep 2180323 = 3270485) B3270485
theorem B7080229 : Blo 2179435 7080229 := bbase (se 4 (by rfl) ⟨663771, by rfl⟩ : syracuseStep 7080229 = 1327543) (by norm_num)
theorem B37761221 : Blo 2179435 37761221 := bstep (se 4 (by rfl) ⟨3540114, by rfl⟩ : syracuseStep 37761221 = 7080229) B7080229
theorem B25174147 : Blo 2179435 25174147 := bstep (se 1 (by rfl) ⟨18880610, by rfl⟩ : syracuseStep 25174147 = 37761221) B37761221
theorem B33565529 : Blo 2179435 33565529 := bstep (se 2 (by rfl) ⟨12587073, by rfl⟩ : syracuseStep 33565529 = 25174147) B25174147
theorem B22377019 : Blo 2179435 22377019 := bstep (se 1 (by rfl) ⟨16782764, by rfl⟩ : syracuseStep 22377019 = 33565529) B33565529
theorem B29836025 : Blo 2179435 29836025 := bstep (se 2 (by rfl) ⟨11188509, by rfl⟩ : syracuseStep 29836025 = 22377019) B22377019
theorem B19890683 : Blo 2179435 19890683 := bstep (se 1 (by rfl) ⟨14918012, by rfl⟩ : syracuseStep 19890683 = 29836025) B29836025
theorem B13260455 : Blo 2179435 13260455 := bstep (se 1 (by rfl) ⟨9945341, by rfl⟩ : syracuseStep 13260455 = 19890683) B19890683
theorem B8840303 : Blo 2179435 8840303 := bstep (se 1 (by rfl) ⟨6630227, by rfl⟩ : syracuseStep 8840303 = 13260455) B13260455
theorem B5893535 : Blo 2179435 5893535 := bstep (se 1 (by rfl) ⟨4420151, by rfl⟩ : syracuseStep 5893535 = 8840303) B8840303
theorem B3929023 : Blo 2179435 3929023 := bstep (se 1 (by rfl) ⟨2946767, by rfl⟩ : syracuseStep 3929023 = 5893535) B5893535
theorem B5238697 : Blo 2179435 5238697 := bstep (se 2 (by rfl) ⟨1964511, by rfl⟩ : syracuseStep 5238697 = 3929023) B3929023
theorem B6984929 : Blo 2179435 6984929 := bstep (se 2 (by rfl) ⟨2619348, by rfl⟩ : syracuseStep 6984929 = 5238697) B5238697
theorem B4656619 : Blo 2179435 4656619 := bstep (se 1 (by rfl) ⟨3492464, by rfl⟩ : syracuseStep 4656619 = 6984929) B6984929
theorem B6208825 : Blo 2179435 6208825 := bstep (se 2 (by rfl) ⟨2328309, by rfl⟩ : syracuseStep 6208825 = 4656619) B4656619
theorem B8278433 : Blo 2179435 8278433 := bstep (se 2 (by rfl) ⟨3104412, by rfl⟩ : syracuseStep 8278433 = 6208825) B6208825
theorem B5518955 : Blo 2179435 5518955 := bstep (se 1 (by rfl) ⟨4139216, by rfl⟩ : syracuseStep 5518955 = 8278433) B8278433
theorem B3679303 : Blo 2179435 3679303 := bstep (se 1 (by rfl) ⟨2759477, by rfl⟩ : syracuseStep 3679303 = 5518955) B5518955
theorem B4905737 : Blo 2179435 4905737 := bstep (se 2 (by rfl) ⟨1839651, by rfl⟩ : syracuseStep 4905737 = 3679303) B3679303
theorem B3270491 : Blo 2179435 3270491 := bstep (se 1 (by rfl) ⟨2452868, by rfl⟩ : syracuseStep 3270491 = 4905737) B4905737
theorem B2180327 : Blo 2179435 2180327 := bstep (se 1 (by rfl) ⟨1635245, by rfl⟩ : syracuseStep 2180327 = 3270491) B3270491
theorem B2452873 : Blo 2179435 2452873 := bbase (se 2 (by rfl) ⟨919827, by rfl⟩ : syracuseStep 2452873 = 1839655) (by norm_num)
theorem B3270497 : Blo 2179435 3270497 := bstep (se 2 (by rfl) ⟨1226436, by rfl⟩ : syracuseStep 3270497 = 2452873) B2452873
theorem B2180331 : Blo 2179435 2180331 := bstep (se 1 (by rfl) ⟨1635248, by rfl⟩ : syracuseStep 2180331 = 3270497) B3270497
theorem B2392285 : Blo 2179435 2392285 := bbase (se 3 (by rfl) ⟨448553, by rfl⟩ : syracuseStep 2392285 = 897107) (by norm_num)
theorem B3189713 : Blo 2179435 3189713 := bstep (se 2 (by rfl) ⟨1196142, by rfl⟩ : syracuseStep 3189713 = 2392285) B2392285
theorem B8505901 : Blo 2179435 8505901 := bstep (se 3 (by rfl) ⟨1594856, by rfl⟩ : syracuseStep 8505901 = 3189713) B3189713
theorem B45364805 : Blo 2179435 45364805 := bstep (se 4 (by rfl) ⟨4252950, by rfl⟩ : syracuseStep 45364805 = 8505901) B8505901
theorem B30243203 : Blo 2179435 30243203 := bstep (se 1 (by rfl) ⟨22682402, by rfl⟩ : syracuseStep 30243203 = 45364805) B45364805
theorem B20162135 : Blo 2179435 20162135 := bstep (se 1 (by rfl) ⟨15121601, by rfl⟩ : syracuseStep 20162135 = 30243203) B30243203
theorem B13441423 : Blo 2179435 13441423 := bstep (se 1 (by rfl) ⟨10081067, by rfl⟩ : syracuseStep 13441423 = 20162135) B20162135
theorem B17921897 : Blo 2179435 17921897 := bstep (se 2 (by rfl) ⟨6720711, by rfl⟩ : syracuseStep 17921897 = 13441423) B13441423
theorem B11947931 : Blo 2179435 11947931 := bstep (se 1 (by rfl) ⟨8960948, by rfl⟩ : syracuseStep 11947931 = 17921897) B17921897
theorem B7965287 : Blo 2179435 7965287 := bstep (se 1 (by rfl) ⟨5973965, by rfl⟩ : syracuseStep 7965287 = 11947931) B11947931
theorem B5310191 : Blo 2179435 5310191 := bstep (se 1 (by rfl) ⟨3982643, by rfl⟩ : syracuseStep 5310191 = 7965287) B7965287
theorem B3540127 : Blo 2179435 3540127 := bstep (se 1 (by rfl) ⟨2655095, by rfl⟩ : syracuseStep 3540127 = 5310191) B5310191
theorem B4720169 : Blo 2179435 4720169 := bstep (se 2 (by rfl) ⟨1770063, by rfl⟩ : syracuseStep 4720169 = 3540127) B3540127
theorem B3146779 : Blo 2179435 3146779 := bstep (se 1 (by rfl) ⟨2360084, by rfl⟩ : syracuseStep 3146779 = 4720169) B4720169
theorem B16782821 : Blo 2179435 16782821 := bstep (se 4 (by rfl) ⟨1573389, by rfl⟩ : syracuseStep 16782821 = 3146779) B3146779
theorem B11188547 : Blo 2179435 11188547 := bstep (se 1 (by rfl) ⟨8391410, by rfl⟩ : syracuseStep 11188547 = 16782821) B16782821
theorem B7459031 : Blo 2179435 7459031 := bstep (se 1 (by rfl) ⟨5594273, by rfl⟩ : syracuseStep 7459031 = 11188547) B11188547
theorem B4972687 : Blo 2179435 4972687 := bstep (se 1 (by rfl) ⟨3729515, by rfl⟩ : syracuseStep 4972687 = 7459031) B7459031
theorem B106083989 : Blo 2179435 106083989 := bstep (se 6 (by rfl) ⟨2486343, by rfl⟩ : syracuseStep 106083989 = 4972687) B4972687
theorem B70722659 : Blo 2179435 70722659 := bstep (se 1 (by rfl) ⟨53041994, by rfl⟩ : syracuseStep 70722659 = 106083989) B106083989
theorem B47148439 : Blo 2179435 47148439 := bstep (se 1 (by rfl) ⟨35361329, by rfl⟩ : syracuseStep 47148439 = 70722659) B70722659
theorem B62864585 : Blo 2179435 62864585 := bstep (se 2 (by rfl) ⟨23574219, by rfl⟩ : syracuseStep 62864585 = 47148439) B47148439
theorem B41909723 : Blo 2179435 41909723 := bstep (se 1 (by rfl) ⟨31432292, by rfl⟩ : syracuseStep 41909723 = 62864585) B62864585
theorem B27939815 : Blo 2179435 27939815 := bstep (se 1 (by rfl) ⟨20954861, by rfl⟩ : syracuseStep 27939815 = 41909723) B41909723
theorem B18626543 : Blo 2179435 18626543 := bstep (se 1 (by rfl) ⟨13969907, by rfl⟩ : syracuseStep 18626543 = 27939815) B27939815
theorem B12417695 : Blo 2179435 12417695 := bstep (se 1 (by rfl) ⟨9313271, by rfl⟩ : syracuseStep 12417695 = 18626543) B18626543
theorem B8278463 : Blo 2179435 8278463 := bstep (se 1 (by rfl) ⟨6208847, by rfl⟩ : syracuseStep 8278463 = 12417695) B12417695
theorem B5518975 : Blo 2179435 5518975 := bstep (se 1 (by rfl) ⟨4139231, by rfl⟩ : syracuseStep 5518975 = 8278463) B8278463
theorem B7358633 : Blo 2179435 7358633 := bstep (se 2 (by rfl) ⟨2759487, by rfl⟩ : syracuseStep 7358633 = 5518975) B5518975
theorem B4905755 : Blo 2179435 4905755 := bstep (se 1 (by rfl) ⟨3679316, by rfl⟩ : syracuseStep 4905755 = 7358633) B7358633
theorem B3270503 : Blo 2179435 3270503 := bstep (se 1 (by rfl) ⟨2452877, by rfl⟩ : syracuseStep 3270503 = 4905755) B4905755
theorem B2180335 : Blo 2179435 2180335 := bstep (se 1 (by rfl) ⟨1635251, by rfl⟩ : syracuseStep 2180335 = 3270503) B3270503
theorem B3270509 : Blo 2179435 3270509 := bbase (se 3 (by rfl) ⟨613220, by rfl⟩ : syracuseStep 3270509 = 1226441) (by norm_num)
theorem B2180339 : Blo 2179435 2180339 := bstep (se 1 (by rfl) ⟨1635254, by rfl⟩ : syracuseStep 2180339 = 3270509) B3270509
theorem B4905773 : Blo 2179435 4905773 := bbase (se 3 (by rfl) ⟨919832, by rfl⟩ : syracuseStep 4905773 = 1839665) (by norm_num)
theorem B3270515 : Blo 2179435 3270515 := bstep (se 1 (by rfl) ⟨2452886, by rfl⟩ : syracuseStep 3270515 = 4905773) B4905773
theorem B2180343 : Blo 2179435 2180343 := bstep (se 1 (by rfl) ⟨1635257, by rfl⟩ : syracuseStep 2180343 = 3270515) B3270515
theorem B2619373 : Blo 2179435 2619373 := bbase (se 3 (by rfl) ⟨491132, by rfl⟩ : syracuseStep 2619373 = 982265) (by norm_num)
theorem B3492497 : Blo 2179435 3492497 := bstep (se 2 (by rfl) ⟨1309686, by rfl⟩ : syracuseStep 3492497 = 2619373) B2619373
theorem B9313325 : Blo 2179435 9313325 := bstep (se 3 (by rfl) ⟨1746248, by rfl⟩ : syracuseStep 9313325 = 3492497) B3492497
theorem B6208883 : Blo 2179435 6208883 := bstep (se 1 (by rfl) ⟨4656662, by rfl⟩ : syracuseStep 6208883 = 9313325) B9313325
theorem B4139255 : Blo 2179435 4139255 := bstep (se 1 (by rfl) ⟨3104441, by rfl⟩ : syracuseStep 4139255 = 6208883) B6208883
theorem B2759503 : Blo 2179435 2759503 := bstep (se 1 (by rfl) ⟨2069627, by rfl⟩ : syracuseStep 2759503 = 4139255) B4139255
theorem B3679337 : Blo 2179435 3679337 := bstep (se 2 (by rfl) ⟨1379751, by rfl⟩ : syracuseStep 3679337 = 2759503) B2759503
theorem B2452891 : Blo 2179435 2452891 := bstep (se 1 (by rfl) ⟨1839668, by rfl⟩ : syracuseStep 2452891 = 3679337) B3679337
theorem B3270521 : Blo 2179435 3270521 := bstep (se 2 (by rfl) ⟨1226445, by rfl⟩ : syracuseStep 3270521 = 2452891) B2452891
theorem B2180347 : Blo 2179435 2180347 := bstep (se 1 (by rfl) ⟨1635260, by rfl⟩ : syracuseStep 2180347 = 3270521) B3270521
theorem B25174421 : Blo 2179435 25174421 := bbase (se 6 (by rfl) ⟨590025, by rfl⟩ : syracuseStep 25174421 = 1180051) (by norm_num)
theorem B16782947 : Blo 2179435 16782947 := bstep (se 1 (by rfl) ⟨12587210, by rfl⟩ : syracuseStep 16782947 = 25174421) B25174421
theorem B11188631 : Blo 2179435 11188631 := bstep (se 1 (by rfl) ⟨8391473, by rfl⟩ : syracuseStep 11188631 = 16782947) B16782947
theorem B7459087 : Blo 2179435 7459087 := bstep (se 1 (by rfl) ⟨5594315, by rfl⟩ : syracuseStep 7459087 = 11188631) B11188631
theorem B9945449 : Blo 2179435 9945449 := bstep (se 2 (by rfl) ⟨3729543, by rfl⟩ : syracuseStep 9945449 = 7459087) B7459087
theorem B6630299 : Blo 2179435 6630299 := bstep (se 1 (by rfl) ⟨4972724, by rfl⟩ : syracuseStep 6630299 = 9945449) B9945449
theorem B4420199 : Blo 2179435 4420199 := bstep (se 1 (by rfl) ⟨3315149, by rfl⟩ : syracuseStep 4420199 = 6630299) B6630299
theorem B2946799 : Blo 2179435 2946799 := bstep (se 1 (by rfl) ⟨2210099, by rfl⟩ : syracuseStep 2946799 = 4420199) B4420199
theorem B15716261 : Blo 2179435 15716261 := bstep (se 4 (by rfl) ⟨1473399, by rfl⟩ : syracuseStep 15716261 = 2946799) B2946799
theorem B10477507 : Blo 2179435 10477507 := bstep (se 1 (by rfl) ⟨7858130, by rfl⟩ : syracuseStep 10477507 = 15716261) B15716261
theorem B13970009 : Blo 2179435 13970009 := bstep (se 2 (by rfl) ⟨5238753, by rfl⟩ : syracuseStep 13970009 = 10477507) B10477507
theorem B37253357 : Blo 2179435 37253357 := bstep (se 3 (by rfl) ⟨6985004, by rfl⟩ : syracuseStep 37253357 = 13970009) B13970009
theorem B24835571 : Blo 2179435 24835571 := bstep (se 1 (by rfl) ⟨18626678, by rfl⟩ : syracuseStep 24835571 = 37253357) B37253357
theorem B16557047 : Blo 2179435 16557047 := bstep (se 1 (by rfl) ⟨12417785, by rfl⟩ : syracuseStep 16557047 = 24835571) B24835571
theorem B11038031 : Blo 2179435 11038031 := bstep (se 1 (by rfl) ⟨8278523, by rfl⟩ : syracuseStep 11038031 = 16557047) B16557047
theorem B7358687 : Blo 2179435 7358687 := bstep (se 1 (by rfl) ⟨5519015, by rfl⟩ : syracuseStep 7358687 = 11038031) B11038031
theorem B4905791 : Blo 2179435 4905791 := bstep (se 1 (by rfl) ⟨3679343, by rfl⟩ : syracuseStep 4905791 = 7358687) B7358687
theorem B3270527 : Blo 2179435 3270527 := bstep (se 1 (by rfl) ⟨2452895, by rfl⟩ : syracuseStep 3270527 = 4905791) B4905791
theorem B2180351 : Blo 2179435 2180351 := bstep (se 1 (by rfl) ⟨1635263, by rfl⟩ : syracuseStep 2180351 = 3270527) B3270527
theorem B3270533 : Blo 2179435 3270533 := bbase (se 4 (by rfl) ⟨306612, by rfl⟩ : syracuseStep 3270533 = 613225) (by norm_num)
theorem B2180355 : Blo 2179435 2180355 := bstep (se 1 (by rfl) ⟨1635266, by rfl⟩ : syracuseStep 2180355 = 3270533) B3270533
theorem B3679357 : Blo 2179435 3679357 := bbase (se 3 (by rfl) ⟨689879, by rfl⟩ : syracuseStep 3679357 = 1379759) (by norm_num)
theorem B4905809 : Blo 2179435 4905809 := bstep (se 2 (by rfl) ⟨1839678, by rfl⟩ : syracuseStep 4905809 = 3679357) B3679357
theorem B3270539 : Blo 2179435 3270539 := bstep (se 1 (by rfl) ⟨2452904, by rfl⟩ : syracuseStep 3270539 = 4905809) B4905809
theorem B2180359 : Blo 2179435 2180359 := bstep (se 1 (by rfl) ⟨1635269, by rfl⟩ : syracuseStep 2180359 = 3270539) B3270539
theorem B2452909 : Blo 2179435 2452909 := bbase (se 3 (by rfl) ⟨459920, by rfl⟩ : syracuseStep 2452909 = 919841) (by norm_num)
theorem B3270545 : Blo 2179435 3270545 := bstep (se 2 (by rfl) ⟨1226454, by rfl⟩ : syracuseStep 3270545 = 2452909) B2452909
theorem B2180363 : Blo 2179435 2180363 := bstep (se 1 (by rfl) ⟨1635272, by rfl⟩ : syracuseStep 2180363 = 3270545) B3270545
theorem B7358741 : Blo 2179435 7358741 := bbase (se 6 (by rfl) ⟨172470, by rfl⟩ : syracuseStep 7358741 = 344941) (by norm_num)
theorem B4905827 : Blo 2179435 4905827 := bstep (se 1 (by rfl) ⟨3679370, by rfl⟩ : syracuseStep 4905827 = 7358741) B7358741
theorem B3270551 : Blo 2179435 3270551 := bstep (se 1 (by rfl) ⟨2452913, by rfl⟩ : syracuseStep 3270551 = 4905827) B4905827
theorem B2180367 : Blo 2179435 2180367 := bstep (se 1 (by rfl) ⟨1635275, by rfl⟩ : syracuseStep 2180367 = 3270551) B3270551
theorem B3270557 : Blo 2179435 3270557 := bbase (se 3 (by rfl) ⟨613229, by rfl⟩ : syracuseStep 3270557 = 1226459) (by norm_num)
theorem B2180371 : Blo 2179435 2180371 := bstep (se 1 (by rfl) ⟨1635278, by rfl⟩ : syracuseStep 2180371 = 3270557) B3270557
theorem B4905845 : Blo 2179435 4905845 := bbase (se 5 (by rfl) ⟨229961, by rfl⟩ : syracuseStep 4905845 = 459923) (by norm_num)
theorem B3270563 : Blo 2179435 3270563 := bstep (se 1 (by rfl) ⟨2452922, by rfl⟩ : syracuseStep 3270563 = 4905845) B4905845
theorem B2180375 : Blo 2179435 2180375 := bstep (se 1 (by rfl) ⟨1635281, by rfl⟩ : syracuseStep 2180375 = 3270563) B3270563
theorem B47149397 : Blo 2179435 47149397 := bbase (se 10 (by rfl) ⟨69066, by rfl⟩ : syracuseStep 47149397 = 138133) (by norm_num)
theorem B31432931 : Blo 2179435 31432931 := bstep (se 1 (by rfl) ⟨23574698, by rfl⟩ : syracuseStep 31432931 = 47149397) B47149397
theorem B20955287 : Blo 2179435 20955287 := bstep (se 1 (by rfl) ⟨15716465, by rfl⟩ : syracuseStep 20955287 = 31432931) B31432931
theorem B13970191 : Blo 2179435 13970191 := bstep (se 1 (by rfl) ⟨10477643, by rfl⟩ : syracuseStep 13970191 = 20955287) B20955287
theorem B18626921 : Blo 2179435 18626921 := bstep (se 2 (by rfl) ⟨6985095, by rfl⟩ : syracuseStep 18626921 = 13970191) B13970191
theorem B12417947 : Blo 2179435 12417947 := bstep (se 1 (by rfl) ⟨9313460, by rfl⟩ : syracuseStep 12417947 = 18626921) B18626921
theorem B8278631 : Blo 2179435 8278631 := bstep (se 1 (by rfl) ⟨6208973, by rfl⟩ : syracuseStep 8278631 = 12417947) B12417947
theorem B5519087 : Blo 2179435 5519087 := bstep (se 1 (by rfl) ⟨4139315, by rfl⟩ : syracuseStep 5519087 = 8278631) B8278631
theorem B3679391 : Blo 2179435 3679391 := bstep (se 1 (by rfl) ⟨2759543, by rfl⟩ : syracuseStep 3679391 = 5519087) B5519087
theorem B2452927 : Blo 2179435 2452927 := bstep (se 1 (by rfl) ⟨1839695, by rfl⟩ : syracuseStep 2452927 = 3679391) B3679391
theorem B3270569 : Blo 2179435 3270569 := bstep (se 2 (by rfl) ⟨1226463, by rfl⟩ : syracuseStep 3270569 = 2452927) B2452927
theorem B2180379 : Blo 2179435 2180379 := bstep (se 1 (by rfl) ⟨1635284, by rfl⟩ : syracuseStep 2180379 = 3270569) B3270569
theorem B8278645 : Blo 2179435 8278645 := bbase (se 5 (by rfl) ⟨388061, by rfl⟩ : syracuseStep 8278645 = 776123) (by norm_num)
theorem B11038193 : Blo 2179435 11038193 := bstep (se 2 (by rfl) ⟨4139322, by rfl⟩ : syracuseStep 11038193 = 8278645) B8278645
theorem B7358795 : Blo 2179435 7358795 := bstep (se 1 (by rfl) ⟨5519096, by rfl⟩ : syracuseStep 7358795 = 11038193) B11038193
theorem B4905863 : Blo 2179435 4905863 := bstep (se 1 (by rfl) ⟨3679397, by rfl⟩ : syracuseStep 4905863 = 7358795) B7358795
theorem B3270575 : Blo 2179435 3270575 := bstep (se 1 (by rfl) ⟨2452931, by rfl⟩ : syracuseStep 3270575 = 4905863) B4905863
theorem B2180383 : Blo 2179435 2180383 := bstep (se 1 (by rfl) ⟨1635287, by rfl⟩ : syracuseStep 2180383 = 3270575) B3270575
theorem B3270581 : Blo 2179435 3270581 := bbase (se 5 (by rfl) ⟨153308, by rfl⟩ : syracuseStep 3270581 = 306617) (by norm_num)
theorem B2180387 : Blo 2179435 2180387 := bstep (se 1 (by rfl) ⟨1635290, by rfl⟩ : syracuseStep 2180387 = 3270581) B3270581
theorem B5519117 : Blo 2179435 5519117 := bbase (se 3 (by rfl) ⟨1034834, by rfl⟩ : syracuseStep 5519117 = 2069669) (by norm_num)
theorem B3679411 : Blo 2179435 3679411 := bstep (se 1 (by rfl) ⟨2759558, by rfl⟩ : syracuseStep 3679411 = 5519117) B5519117
theorem B4905881 : Blo 2179435 4905881 := bstep (se 2 (by rfl) ⟨1839705, by rfl⟩ : syracuseStep 4905881 = 3679411) B3679411
theorem B3270587 : Blo 2179435 3270587 := bstep (se 1 (by rfl) ⟨2452940, by rfl⟩ : syracuseStep 3270587 = 4905881) B4905881
theorem B2180391 : Blo 2179435 2180391 := bstep (se 1 (by rfl) ⟨1635293, by rfl⟩ : syracuseStep 2180391 = 3270587) B3270587
theorem B2452945 : Blo 2179435 2452945 := bbase (se 2 (by rfl) ⟨919854, by rfl⟩ : syracuseStep 2452945 = 1839709) (by norm_num)
theorem B3270593 : Blo 2179435 3270593 := bstep (se 2 (by rfl) ⟨1226472, by rfl⟩ : syracuseStep 3270593 = 2452945) B2452945
theorem B2180395 : Blo 2179435 2180395 := bstep (se 1 (by rfl) ⟨1635296, by rfl⟩ : syracuseStep 2180395 = 3270593) B3270593
theorem B4656773 : Blo 2179435 4656773 := bbase (se 4 (by rfl) ⟨436572, by rfl⟩ : syracuseStep 4656773 = 873145) (by norm_num)
theorem B3104515 : Blo 2179435 3104515 := bstep (se 1 (by rfl) ⟨2328386, by rfl⟩ : syracuseStep 3104515 = 4656773) B4656773
theorem B4139353 : Blo 2179435 4139353 := bstep (se 2 (by rfl) ⟨1552257, by rfl⟩ : syracuseStep 4139353 = 3104515) B3104515
theorem B5519137 : Blo 2179435 5519137 := bstep (se 2 (by rfl) ⟨2069676, by rfl⟩ : syracuseStep 5519137 = 4139353) B4139353
theorem B7358849 : Blo 2179435 7358849 := bstep (se 2 (by rfl) ⟨2759568, by rfl⟩ : syracuseStep 7358849 = 5519137) B5519137
theorem B4905899 : Blo 2179435 4905899 := bstep (se 1 (by rfl) ⟨3679424, by rfl⟩ : syracuseStep 4905899 = 7358849) B7358849
theorem B3270599 : Blo 2179435 3270599 := bstep (se 1 (by rfl) ⟨2452949, by rfl⟩ : syracuseStep 3270599 = 4905899) B4905899
theorem B2180399 : Blo 2179435 2180399 := bstep (se 1 (by rfl) ⟨1635299, by rfl⟩ : syracuseStep 2180399 = 3270599) B3270599
theorem B3270605 : Blo 2179435 3270605 := bbase (se 3 (by rfl) ⟨613238, by rfl⟩ : syracuseStep 3270605 = 1226477) (by norm_num)
theorem B2180403 : Blo 2179435 2180403 := bstep (se 1 (by rfl) ⟨1635302, by rfl⟩ : syracuseStep 2180403 = 3270605) B3270605
theorem B4905917 : Blo 2179435 4905917 := bbase (se 3 (by rfl) ⟨919859, by rfl⟩ : syracuseStep 4905917 = 1839719) (by norm_num)
theorem B3270611 : Blo 2179435 3270611 := bstep (se 1 (by rfl) ⟨2452958, by rfl⟩ : syracuseStep 3270611 = 4905917) B4905917
theorem B2180407 : Blo 2179435 2180407 := bstep (se 1 (by rfl) ⟨1635305, by rfl⟩ : syracuseStep 2180407 = 3270611) B3270611
theorem B3679445 : Blo 2179435 3679445 := bbase (se 7 (by rfl) ⟨43118, by rfl⟩ : syracuseStep 3679445 = 86237) (by norm_num)
theorem B2452963 : Blo 2179435 2452963 := bstep (se 1 (by rfl) ⟨1839722, by rfl⟩ : syracuseStep 2452963 = 3679445) B3679445
theorem B3270617 : Blo 2179435 3270617 := bstep (se 2 (by rfl) ⟨1226481, by rfl⟩ : syracuseStep 3270617 = 2452963) B2452963
theorem B2180411 : Blo 2179435 2180411 := bstep (se 1 (by rfl) ⟨1635308, by rfl⟩ : syracuseStep 2180411 = 3270617) B3270617
theorem B3492605 : Blo 2179435 3492605 := bbase (se 3 (by rfl) ⟨654863, by rfl⟩ : syracuseStep 3492605 = 1309727) (by norm_num)
theorem B9313613 : Blo 2179435 9313613 := bstep (se 3 (by rfl) ⟨1746302, by rfl⟩ : syracuseStep 9313613 = 3492605) B3492605
theorem B6209075 : Blo 2179435 6209075 := bstep (se 1 (by rfl) ⟨4656806, by rfl⟩ : syracuseStep 6209075 = 9313613) B9313613
theorem B16557533 : Blo 2179435 16557533 := bstep (se 3 (by rfl) ⟨3104537, by rfl⟩ : syracuseStep 16557533 = 6209075) B6209075
theorem B11038355 : Blo 2179435 11038355 := bstep (se 1 (by rfl) ⟨8278766, by rfl⟩ : syracuseStep 11038355 = 16557533) B16557533
theorem B7358903 : Blo 2179435 7358903 := bstep (se 1 (by rfl) ⟨5519177, by rfl⟩ : syracuseStep 7358903 = 11038355) B11038355
theorem B4905935 : Blo 2179435 4905935 := bstep (se 1 (by rfl) ⟨3679451, by rfl⟩ : syracuseStep 4905935 = 7358903) B7358903
theorem B3270623 : Blo 2179435 3270623 := bstep (se 1 (by rfl) ⟨2452967, by rfl⟩ : syracuseStep 3270623 = 4905935) B4905935
theorem B2180415 : Blo 2179435 2180415 := bstep (se 1 (by rfl) ⟨1635311, by rfl⟩ : syracuseStep 2180415 = 3270623) B3270623
theorem B3270629 : Blo 2179435 3270629 := bbase (se 4 (by rfl) ⟨306621, by rfl⟩ : syracuseStep 3270629 = 613243) (by norm_num)
theorem B2180419 : Blo 2179435 2180419 := bstep (se 1 (by rfl) ⟨1635314, by rfl⟩ : syracuseStep 2180419 = 3270629) B3270629
theorem B6985237 : Blo 2179435 6985237 := bbase (se 6 (by rfl) ⟨163716, by rfl⟩ : syracuseStep 6985237 = 327433) (by norm_num)
theorem B9313649 : Blo 2179435 9313649 := bstep (se 2 (by rfl) ⟨3492618, by rfl⟩ : syracuseStep 9313649 = 6985237) B6985237
theorem B6209099 : Blo 2179435 6209099 := bstep (se 1 (by rfl) ⟨4656824, by rfl⟩ : syracuseStep 6209099 = 9313649) B9313649
theorem B4139399 : Blo 2179435 4139399 := bstep (se 1 (by rfl) ⟨3104549, by rfl⟩ : syracuseStep 4139399 = 6209099) B6209099
theorem B2759599 : Blo 2179435 2759599 := bstep (se 1 (by rfl) ⟨2069699, by rfl⟩ : syracuseStep 2759599 = 4139399) B4139399
theorem B3679465 : Blo 2179435 3679465 := bstep (se 2 (by rfl) ⟨1379799, by rfl⟩ : syracuseStep 3679465 = 2759599) B2759599
theorem B4905953 : Blo 2179435 4905953 := bstep (se 2 (by rfl) ⟨1839732, by rfl⟩ : syracuseStep 4905953 = 3679465) B3679465
theorem B3270635 : Blo 2179435 3270635 := bstep (se 1 (by rfl) ⟨2452976, by rfl⟩ : syracuseStep 3270635 = 4905953) B4905953
theorem B2180423 : Blo 2179435 2180423 := bstep (se 1 (by rfl) ⟨1635317, by rfl⟩ : syracuseStep 2180423 = 3270635) B3270635
theorem B2452981 : Blo 2179435 2452981 := bbase (se 5 (by rfl) ⟨114983, by rfl⟩ : syracuseStep 2452981 = 229967) (by norm_num)
theorem B3270641 : Blo 2179435 3270641 := bstep (se 2 (by rfl) ⟨1226490, by rfl⟩ : syracuseStep 3270641 = 2452981) B2452981
theorem B2180427 : Blo 2179435 2180427 := bstep (se 1 (by rfl) ⟨1635320, by rfl⟩ : syracuseStep 2180427 = 3270641) B3270641
theorem B2759609 : Blo 2179435 2759609 := bbase (se 2 (by rfl) ⟨1034853, by rfl⟩ : syracuseStep 2759609 = 2069707) (by norm_num)
theorem B7358957 : Blo 2179435 7358957 := bstep (se 3 (by rfl) ⟨1379804, by rfl⟩ : syracuseStep 7358957 = 2759609) B2759609
theorem B4905971 : Blo 2179435 4905971 := bstep (se 1 (by rfl) ⟨3679478, by rfl⟩ : syracuseStep 4905971 = 7358957) B7358957
theorem B3270647 : Blo 2179435 3270647 := bstep (se 1 (by rfl) ⟨2452985, by rfl⟩ : syracuseStep 3270647 = 4905971) B4905971
theorem B2180431 : Blo 2179435 2180431 := bstep (se 1 (by rfl) ⟨1635323, by rfl⟩ : syracuseStep 2180431 = 3270647) B3270647
theorem B3270653 : Blo 2179435 3270653 := bbase (se 3 (by rfl) ⟨613247, by rfl⟩ : syracuseStep 3270653 = 1226495) (by norm_num)
theorem B2180435 : Blo 2179435 2180435 := bstep (se 1 (by rfl) ⟨1635326, by rfl⟩ : syracuseStep 2180435 = 3270653) B3270653
theorem B4905989 : Blo 2179435 4905989 := bbase (se 4 (by rfl) ⟨459936, by rfl⟩ : syracuseStep 4905989 = 919873) (by norm_num)
theorem B3270659 : Blo 2179435 3270659 := bstep (se 1 (by rfl) ⟨2452994, by rfl⟩ : syracuseStep 3270659 = 4905989) B4905989
theorem B2180439 : Blo 2179435 2180439 := bstep (se 1 (by rfl) ⟨1635329, by rfl⟩ : syracuseStep 2180439 = 3270659) B3270659
theorem B4139437 : Blo 2179435 4139437 := bbase (se 3 (by rfl) ⟨776144, by rfl⟩ : syracuseStep 4139437 = 1552289) (by norm_num)
theorem B5519249 : Blo 2179435 5519249 := bstep (se 2 (by rfl) ⟨2069718, by rfl⟩ : syracuseStep 5519249 = 4139437) B4139437
theorem B3679499 : Blo 2179435 3679499 := bstep (se 1 (by rfl) ⟨2759624, by rfl⟩ : syracuseStep 3679499 = 5519249) B5519249
theorem B2452999 : Blo 2179435 2452999 := bstep (se 1 (by rfl) ⟨1839749, by rfl⟩ : syracuseStep 2452999 = 3679499) B3679499
theorem B3270665 : Blo 2179435 3270665 := bstep (se 2 (by rfl) ⟨1226499, by rfl⟩ : syracuseStep 3270665 = 2452999) B2452999
theorem B2180443 : Blo 2179435 2180443 := bstep (se 1 (by rfl) ⟨1635332, by rfl⟩ : syracuseStep 2180443 = 3270665) B3270665
theorem B11038517 : Blo 2179435 11038517 := bbase (se 5 (by rfl) ⟨517430, by rfl⟩ : syracuseStep 11038517 = 1034861) (by norm_num)
theorem B7359011 : Blo 2179435 7359011 := bstep (se 1 (by rfl) ⟨5519258, by rfl⟩ : syracuseStep 7359011 = 11038517) B11038517
theorem B4906007 : Blo 2179435 4906007 := bstep (se 1 (by rfl) ⟨3679505, by rfl⟩ : syracuseStep 4906007 = 7359011) B7359011
theorem B3270671 : Blo 2179435 3270671 := bstep (se 1 (by rfl) ⟨2453003, by rfl⟩ : syracuseStep 3270671 = 4906007) B4906007
theorem B2180447 : Blo 2179435 2180447 := bstep (se 1 (by rfl) ⟨1635335, by rfl⟩ : syracuseStep 2180447 = 3270671) B3270671
theorem B3270677 : Blo 2179435 3270677 := bbase (se 6 (by rfl) ⟨76656, by rfl⟩ : syracuseStep 3270677 = 153313) (by norm_num)
theorem B2180451 : Blo 2179435 2180451 := bstep (se 1 (by rfl) ⟨1635338, by rfl⟩ : syracuseStep 2180451 = 3270677) B3270677
theorem B13970677 : Blo 2179435 13970677 := bbase (se 5 (by rfl) ⟨654875, by rfl⟩ : syracuseStep 13970677 = 1309751) (by norm_num)
theorem B18627569 : Blo 2179435 18627569 := bstep (se 2 (by rfl) ⟨6985338, by rfl⟩ : syracuseStep 18627569 = 13970677) B13970677
theorem B12418379 : Blo 2179435 12418379 := bstep (se 1 (by rfl) ⟨9313784, by rfl⟩ : syracuseStep 12418379 = 18627569) B18627569
theorem B8278919 : Blo 2179435 8278919 := bstep (se 1 (by rfl) ⟨6209189, by rfl⟩ : syracuseStep 8278919 = 12418379) B12418379
theorem B5519279 : Blo 2179435 5519279 := bstep (se 1 (by rfl) ⟨4139459, by rfl⟩ : syracuseStep 5519279 = 8278919) B8278919
theorem B3679519 : Blo 2179435 3679519 := bstep (se 1 (by rfl) ⟨2759639, by rfl⟩ : syracuseStep 3679519 = 5519279) B5519279
theorem B4906025 : Blo 2179435 4906025 := bstep (se 2 (by rfl) ⟨1839759, by rfl⟩ : syracuseStep 4906025 = 3679519) B3679519
theorem B3270683 : Blo 2179435 3270683 := bstep (se 1 (by rfl) ⟨2453012, by rfl⟩ : syracuseStep 3270683 = 4906025) B4906025
theorem B2180455 : Blo 2179435 2180455 := bstep (se 1 (by rfl) ⟨1635341, by rfl⟩ : syracuseStep 2180455 = 3270683) B3270683
theorem B2453017 : Blo 2179435 2453017 := bbase (se 2 (by rfl) ⟨919881, by rfl⟩ : syracuseStep 2453017 = 1839763) (by norm_num)
theorem B3270689 : Blo 2179435 3270689 := bstep (se 2 (by rfl) ⟨1226508, by rfl⟩ : syracuseStep 3270689 = 2453017) B2453017
theorem B2180459 : Blo 2179435 2180459 := bstep (se 1 (by rfl) ⟨1635344, by rfl⟩ : syracuseStep 2180459 = 3270689) B3270689
theorem B8278949 : Blo 2179435 8278949 := bbase (se 4 (by rfl) ⟨776151, by rfl⟩ : syracuseStep 8278949 = 1552303) (by norm_num)
theorem B5519299 : Blo 2179435 5519299 := bstep (se 1 (by rfl) ⟨4139474, by rfl⟩ : syracuseStep 5519299 = 8278949) B8278949
theorem B7359065 : Blo 2179435 7359065 := bstep (se 2 (by rfl) ⟨2759649, by rfl⟩ : syracuseStep 7359065 = 5519299) B5519299
theorem B4906043 : Blo 2179435 4906043 := bstep (se 1 (by rfl) ⟨3679532, by rfl⟩ : syracuseStep 4906043 = 7359065) B7359065
theorem B3270695 : Blo 2179435 3270695 := bstep (se 1 (by rfl) ⟨2453021, by rfl⟩ : syracuseStep 3270695 = 4906043) B4906043
theorem B2180463 : Blo 2179435 2180463 := bstep (se 1 (by rfl) ⟨1635347, by rfl⟩ : syracuseStep 2180463 = 3270695) B3270695
theorem B3270701 : Blo 2179435 3270701 := bbase (se 3 (by rfl) ⟨613256, by rfl⟩ : syracuseStep 3270701 = 1226513) (by norm_num)
theorem B2180467 : Blo 2179435 2180467 := bstep (se 1 (by rfl) ⟨1635350, by rfl⟩ : syracuseStep 2180467 = 3270701) B3270701
theorem B4906061 : Blo 2179435 4906061 := bbase (se 3 (by rfl) ⟨919886, by rfl⟩ : syracuseStep 4906061 = 1839773) (by norm_num)
theorem B3270707 : Blo 2179435 3270707 := bstep (se 1 (by rfl) ⟨2453030, by rfl⟩ : syracuseStep 3270707 = 4906061) B4906061
theorem B2180471 : Blo 2179435 2180471 := bstep (se 1 (by rfl) ⟨1635353, by rfl⟩ : syracuseStep 2180471 = 3270707) B3270707
theorem B2759665 : Blo 2179435 2759665 := bbase (se 2 (by rfl) ⟨1034874, by rfl⟩ : syracuseStep 2759665 = 2069749) (by norm_num)
theorem B3679553 : Blo 2179435 3679553 := bstep (se 2 (by rfl) ⟨1379832, by rfl⟩ : syracuseStep 3679553 = 2759665) B2759665
theorem B2453035 : Blo 2179435 2453035 := bstep (se 1 (by rfl) ⟨1839776, by rfl⟩ : syracuseStep 2453035 = 3679553) B3679553
theorem B3270713 : Blo 2179435 3270713 := bstep (se 2 (by rfl) ⟨1226517, by rfl⟩ : syracuseStep 3270713 = 2453035) B2453035
theorem B2180475 : Blo 2179435 2180475 := bstep (se 1 (by rfl) ⟨1635356, by rfl⟩ : syracuseStep 2180475 = 3270713) B3270713
theorem B8840917 : Blo 2179435 8840917 := bbase (se 7 (by rfl) ⟨103604, by rfl⟩ : syracuseStep 8840917 = 207209) (by norm_num)
theorem B11787889 : Blo 2179435 11787889 := bstep (se 2 (by rfl) ⟨4420458, by rfl⟩ : syracuseStep 11787889 = 8840917) B8840917
theorem B15717185 : Blo 2179435 15717185 := bstep (se 2 (by rfl) ⟨5893944, by rfl⟩ : syracuseStep 15717185 = 11787889) B11787889
theorem B10478123 : Blo 2179435 10478123 := bstep (se 1 (by rfl) ⟨7858592, by rfl⟩ : syracuseStep 10478123 = 15717185) B15717185
theorem B6985415 : Blo 2179435 6985415 := bstep (se 1 (by rfl) ⟨5239061, by rfl⟩ : syracuseStep 6985415 = 10478123) B10478123
theorem B4656943 : Blo 2179435 4656943 := bstep (se 1 (by rfl) ⟨3492707, by rfl⟩ : syracuseStep 4656943 = 6985415) B6985415
theorem B24837029 : Blo 2179435 24837029 := bstep (se 4 (by rfl) ⟨2328471, by rfl⟩ : syracuseStep 24837029 = 4656943) B4656943
theorem B16558019 : Blo 2179435 16558019 := bstep (se 1 (by rfl) ⟨12418514, by rfl⟩ : syracuseStep 16558019 = 24837029) B24837029
theorem B11038679 : Blo 2179435 11038679 := bstep (se 1 (by rfl) ⟨8279009, by rfl⟩ : syracuseStep 11038679 = 16558019) B16558019
theorem B7359119 : Blo 2179435 7359119 := bstep (se 1 (by rfl) ⟨5519339, by rfl⟩ : syracuseStep 7359119 = 11038679) B11038679
theorem B4906079 : Blo 2179435 4906079 := bstep (se 1 (by rfl) ⟨3679559, by rfl⟩ : syracuseStep 4906079 = 7359119) B7359119
theorem B3270719 : Blo 2179435 3270719 := bstep (se 1 (by rfl) ⟨2453039, by rfl⟩ : syracuseStep 3270719 = 4906079) B4906079
theorem B2180479 : Blo 2179435 2180479 := bstep (se 1 (by rfl) ⟨1635359, by rfl⟩ : syracuseStep 2180479 = 3270719) B3270719
theorem B3270725 : Blo 2179435 3270725 := bbase (se 4 (by rfl) ⟨306630, by rfl⟩ : syracuseStep 3270725 = 613261) (by norm_num)
theorem B2180483 : Blo 2179435 2180483 := bstep (se 1 (by rfl) ⟨1635362, by rfl⟩ : syracuseStep 2180483 = 3270725) B3270725
theorem B3679573 : Blo 2179435 3679573 := bbase (se 12 (by rfl) ⟨1347, by rfl⟩ : syracuseStep 3679573 = 2695) (by norm_num)
theorem B4906097 : Blo 2179435 4906097 := bstep (se 2 (by rfl) ⟨1839786, by rfl⟩ : syracuseStep 4906097 = 3679573) B3679573
theorem B3270731 : Blo 2179435 3270731 := bstep (se 1 (by rfl) ⟨2453048, by rfl⟩ : syracuseStep 3270731 = 4906097) B4906097
theorem B2180487 : Blo 2179435 2180487 := bstep (se 1 (by rfl) ⟨1635365, by rfl⟩ : syracuseStep 2180487 = 3270731) B3270731
theorem B2453053 : Blo 2179435 2453053 := bbase (se 3 (by rfl) ⟨459947, by rfl⟩ : syracuseStep 2453053 = 919895) (by norm_num)
theorem B3270737 : Blo 2179435 3270737 := bstep (se 2 (by rfl) ⟨1226526, by rfl⟩ : syracuseStep 3270737 = 2453053) B2453053
theorem B2180491 : Blo 2179435 2180491 := bstep (se 1 (by rfl) ⟨1635368, by rfl⟩ : syracuseStep 2180491 = 3270737) B3270737
theorem B7359173 : Blo 2179435 7359173 := bbase (se 4 (by rfl) ⟨689922, by rfl⟩ : syracuseStep 7359173 = 1379845) (by norm_num)
theorem B4906115 : Blo 2179435 4906115 := bstep (se 1 (by rfl) ⟨3679586, by rfl⟩ : syracuseStep 4906115 = 7359173) B7359173
theorem B3270743 : Blo 2179435 3270743 := bstep (se 1 (by rfl) ⟨2453057, by rfl⟩ : syracuseStep 3270743 = 4906115) B4906115
theorem B2180495 : Blo 2179435 2180495 := bstep (se 1 (by rfl) ⟨1635371, by rfl⟩ : syracuseStep 2180495 = 3270743) B3270743
theorem B3270749 : Blo 2179435 3270749 := bbase (se 3 (by rfl) ⟨613265, by rfl⟩ : syracuseStep 3270749 = 1226531) (by norm_num)
theorem B2180499 : Blo 2179435 2180499 := bstep (se 1 (by rfl) ⟨1635374, by rfl⟩ : syracuseStep 2180499 = 3270749) B3270749
theorem B4906133 : Blo 2179435 4906133 := bbase (se 6 (by rfl) ⟨114987, by rfl⟩ : syracuseStep 4906133 = 229975) (by norm_num)
theorem B3270755 : Blo 2179435 3270755 := bstep (se 1 (by rfl) ⟨2453066, by rfl⟩ : syracuseStep 3270755 = 4906133) B4906133
theorem B2180503 : Blo 2179435 2180503 := bstep (se 1 (by rfl) ⟨1635377, by rfl⟩ : syracuseStep 2180503 = 3270755) B3270755
theorem B3104669 : Blo 2179435 3104669 := bbase (se 3 (by rfl) ⟨582125, by rfl⟩ : syracuseStep 3104669 = 1164251) (by norm_num)
theorem B8279117 : Blo 2179435 8279117 := bstep (se 3 (by rfl) ⟨1552334, by rfl⟩ : syracuseStep 8279117 = 3104669) B3104669
theorem B5519411 : Blo 2179435 5519411 := bstep (se 1 (by rfl) ⟨4139558, by rfl⟩ : syracuseStep 5519411 = 8279117) B8279117
theorem B3679607 : Blo 2179435 3679607 := bstep (se 1 (by rfl) ⟨2759705, by rfl⟩ : syracuseStep 3679607 = 5519411) B5519411
theorem B2453071 : Blo 2179435 2453071 := bstep (se 1 (by rfl) ⟨1839803, by rfl⟩ : syracuseStep 2453071 = 3679607) B3679607
theorem B3270761 : Blo 2179435 3270761 := bstep (se 2 (by rfl) ⟨1226535, by rfl⟩ : syracuseStep 3270761 = 2453071) B2453071
theorem B2180507 : Blo 2179435 2180507 := bstep (se 1 (by rfl) ⟨1635380, by rfl⟩ : syracuseStep 2180507 = 3270761) B3270761
theorem B5594725 : Blo 2179435 5594725 := bbase (se 4 (by rfl) ⟨524505, by rfl⟩ : syracuseStep 5594725 = 1049011) (by norm_num)
theorem B7459633 : Blo 2179435 7459633 := bstep (se 2 (by rfl) ⟨2797362, by rfl⟩ : syracuseStep 7459633 = 5594725) B5594725
theorem B39784709 : Blo 2179435 39784709 := bstep (se 4 (by rfl) ⟨3729816, by rfl⟩ : syracuseStep 39784709 = 7459633) B7459633
theorem B26523139 : Blo 2179435 26523139 := bstep (se 1 (by rfl) ⟨19892354, by rfl⟩ : syracuseStep 26523139 = 39784709) B39784709
theorem B35364185 : Blo 2179435 35364185 := bstep (se 2 (by rfl) ⟨13261569, by rfl⟩ : syracuseStep 35364185 = 26523139) B26523139
theorem B23576123 : Blo 2179435 23576123 := bstep (se 1 (by rfl) ⟨17682092, by rfl⟩ : syracuseStep 23576123 = 35364185) B35364185
theorem B15717415 : Blo 2179435 15717415 := bstep (se 1 (by rfl) ⟨11788061, by rfl⟩ : syracuseStep 15717415 = 23576123) B23576123
theorem B20956553 : Blo 2179435 20956553 := bstep (se 2 (by rfl) ⟨7858707, by rfl⟩ : syracuseStep 20956553 = 15717415) B15717415
theorem B13971035 : Blo 2179435 13971035 := bstep (se 1 (by rfl) ⟨10478276, by rfl⟩ : syracuseStep 13971035 = 20956553) B20956553
theorem B9314023 : Blo 2179435 9314023 := bstep (se 1 (by rfl) ⟨6985517, by rfl⟩ : syracuseStep 9314023 = 13971035) B13971035
theorem B12418697 : Blo 2179435 12418697 := bstep (se 2 (by rfl) ⟨4657011, by rfl⟩ : syracuseStep 12418697 = 9314023) B9314023
theorem B8279131 : Blo 2179435 8279131 := bstep (se 1 (by rfl) ⟨6209348, by rfl⟩ : syracuseStep 8279131 = 12418697) B12418697
theorem B11038841 : Blo 2179435 11038841 := bstep (se 2 (by rfl) ⟨4139565, by rfl⟩ : syracuseStep 11038841 = 8279131) B8279131
theorem B7359227 : Blo 2179435 7359227 := bstep (se 1 (by rfl) ⟨5519420, by rfl⟩ : syracuseStep 7359227 = 11038841) B11038841
theorem B4906151 : Blo 2179435 4906151 := bstep (se 1 (by rfl) ⟨3679613, by rfl⟩ : syracuseStep 4906151 = 7359227) B7359227
theorem B3270767 : Blo 2179435 3270767 := bstep (se 1 (by rfl) ⟨2453075, by rfl⟩ : syracuseStep 3270767 = 4906151) B4906151
theorem B2180511 : Blo 2179435 2180511 := bstep (se 1 (by rfl) ⟨1635383, by rfl⟩ : syracuseStep 2180511 = 3270767) B3270767
theorem B3270773 : Blo 2179435 3270773 := bbase (se 5 (by rfl) ⟨153317, by rfl⟩ : syracuseStep 3270773 = 306635) (by norm_num)
theorem B2180515 : Blo 2179435 2180515 := bstep (se 1 (by rfl) ⟨1635386, by rfl⟩ : syracuseStep 2180515 = 3270773) B3270773
theorem B4139581 : Blo 2179435 4139581 := bbase (se 3 (by rfl) ⟨776171, by rfl⟩ : syracuseStep 4139581 = 1552343) (by norm_num)
theorem B5519441 : Blo 2179435 5519441 := bstep (se 2 (by rfl) ⟨2069790, by rfl⟩ : syracuseStep 5519441 = 4139581) B4139581
theorem B3679627 : Blo 2179435 3679627 := bstep (se 1 (by rfl) ⟨2759720, by rfl⟩ : syracuseStep 3679627 = 5519441) B5519441
theorem B4906169 : Blo 2179435 4906169 := bstep (se 2 (by rfl) ⟨1839813, by rfl⟩ : syracuseStep 4906169 = 3679627) B3679627
theorem B3270779 : Blo 2179435 3270779 := bstep (se 1 (by rfl) ⟨2453084, by rfl⟩ : syracuseStep 3270779 = 4906169) B4906169
theorem B2180519 : Blo 2179435 2180519 := bstep (se 1 (by rfl) ⟨1635389, by rfl⟩ : syracuseStep 2180519 = 3270779) B3270779
theorem B2453089 : Blo 2179435 2453089 := bbase (se 2 (by rfl) ⟨919908, by rfl⟩ : syracuseStep 2453089 = 1839817) (by norm_num)
theorem B3270785 : Blo 2179435 3270785 := bstep (se 2 (by rfl) ⟨1226544, by rfl⟩ : syracuseStep 3270785 = 2453089) B2453089
theorem B2180523 : Blo 2179435 2180523 := bstep (se 1 (by rfl) ⟨1635392, by rfl⟩ : syracuseStep 2180523 = 3270785) B3270785
theorem B5519461 : Blo 2179435 5519461 := bbase (se 4 (by rfl) ⟨517449, by rfl⟩ : syracuseStep 5519461 = 1034899) (by norm_num)
theorem B7359281 : Blo 2179435 7359281 := bstep (se 2 (by rfl) ⟨2759730, by rfl⟩ : syracuseStep 7359281 = 5519461) B5519461
theorem B4906187 : Blo 2179435 4906187 := bstep (se 1 (by rfl) ⟨3679640, by rfl⟩ : syracuseStep 4906187 = 7359281) B7359281
theorem B3270791 : Blo 2179435 3270791 := bstep (se 1 (by rfl) ⟨2453093, by rfl⟩ : syracuseStep 3270791 = 4906187) B4906187
theorem B2180527 : Blo 2179435 2180527 := bstep (se 1 (by rfl) ⟨1635395, by rfl⟩ : syracuseStep 2180527 = 3270791) B3270791
theorem B3270797 : Blo 2179435 3270797 := bbase (se 3 (by rfl) ⟨613274, by rfl⟩ : syracuseStep 3270797 = 1226549) (by norm_num)
theorem B2180531 : Blo 2179435 2180531 := bstep (se 1 (by rfl) ⟨1635398, by rfl⟩ : syracuseStep 2180531 = 3270797) B3270797
theorem B4906205 : Blo 2179435 4906205 := bbase (se 3 (by rfl) ⟨919913, by rfl⟩ : syracuseStep 4906205 = 1839827) (by norm_num)
theorem B3270803 : Blo 2179435 3270803 := bstep (se 1 (by rfl) ⟨2453102, by rfl⟩ : syracuseStep 3270803 = 4906205) B4906205
theorem B2180535 : Blo 2179435 2180535 := bstep (se 1 (by rfl) ⟨1635401, by rfl⟩ : syracuseStep 2180535 = 3270803) B3270803
theorem B3679661 : Blo 2179435 3679661 := bbase (se 3 (by rfl) ⟨689936, by rfl⟩ : syracuseStep 3679661 = 1379873) (by norm_num)
theorem B2453107 : Blo 2179435 2453107 := bstep (se 1 (by rfl) ⟨1839830, by rfl⟩ : syracuseStep 2453107 = 3679661) B3679661
theorem B3270809 : Blo 2179435 3270809 := bstep (se 2 (by rfl) ⟨1226553, by rfl⟩ : syracuseStep 3270809 = 2453107) B2453107
theorem B2180539 : Blo 2179435 2180539 := bstep (se 1 (by rfl) ⟨1635404, by rfl⟩ : syracuseStep 2180539 = 3270809) B3270809
theorem B4253357 : Blo 2179435 4253357 := bbase (se 3 (by rfl) ⟨797504, by rfl⟩ : syracuseStep 4253357 = 1595009) (by norm_num)
theorem B2835571 : Blo 2179435 2835571 := bstep (se 1 (by rfl) ⟨2126678, by rfl⟩ : syracuseStep 2835571 = 4253357) B4253357
theorem B3780761 : Blo 2179435 3780761 := bstep (se 2 (by rfl) ⟨1417785, by rfl⟩ : syracuseStep 3780761 = 2835571) B2835571
theorem B10082029 : Blo 2179435 10082029 := bstep (se 3 (by rfl) ⟨1890380, by rfl⟩ : syracuseStep 10082029 = 3780761) B3780761
theorem B13442705 : Blo 2179435 13442705 := bstep (se 2 (by rfl) ⟨5041014, by rfl⟩ : syracuseStep 13442705 = 10082029) B10082029
theorem B8961803 : Blo 2179435 8961803 := bstep (se 1 (by rfl) ⟨6721352, by rfl⟩ : syracuseStep 8961803 = 13442705) B13442705
theorem B5974535 : Blo 2179435 5974535 := bstep (se 1 (by rfl) ⟨4480901, by rfl⟩ : syracuseStep 5974535 = 8961803) B8961803
theorem B3983023 : Blo 2179435 3983023 := bstep (se 1 (by rfl) ⟨2987267, by rfl⟩ : syracuseStep 3983023 = 5974535) B5974535
theorem B5310697 : Blo 2179435 5310697 := bstep (se 2 (by rfl) ⟨1991511, by rfl⟩ : syracuseStep 5310697 = 3983023) B3983023
theorem B7080929 : Blo 2179435 7080929 := bstep (se 2 (by rfl) ⟨2655348, by rfl⟩ : syracuseStep 7080929 = 5310697) B5310697
theorem B4720619 : Blo 2179435 4720619 := bstep (se 1 (by rfl) ⟨3540464, by rfl⟩ : syracuseStep 4720619 = 7080929) B7080929
theorem B12588317 : Blo 2179435 12588317 := bstep (se 3 (by rfl) ⟨2360309, by rfl⟩ : syracuseStep 12588317 = 4720619) B4720619
theorem B8392211 : Blo 2179435 8392211 := bstep (se 1 (by rfl) ⟨6294158, by rfl⟩ : syracuseStep 8392211 = 12588317) B12588317
theorem B5594807 : Blo 2179435 5594807 := bstep (se 1 (by rfl) ⟨4196105, by rfl⟩ : syracuseStep 5594807 = 8392211) B8392211
theorem B3729871 : Blo 2179435 3729871 := bstep (se 1 (by rfl) ⟨2797403, by rfl⟩ : syracuseStep 3729871 = 5594807) B5594807
theorem B19892645 : Blo 2179435 19892645 := bstep (se 4 (by rfl) ⟨1864935, by rfl⟩ : syracuseStep 19892645 = 3729871) B3729871
theorem B13261763 : Blo 2179435 13261763 := bstep (se 1 (by rfl) ⟨9946322, by rfl⟩ : syracuseStep 13261763 = 19892645) B19892645
theorem B35364701 : Blo 2179435 35364701 := bstep (se 3 (by rfl) ⟨6630881, by rfl⟩ : syracuseStep 35364701 = 13261763) B13261763
theorem B94305869 : Blo 2179435 94305869 := bstep (se 3 (by rfl) ⟨17682350, by rfl⟩ : syracuseStep 94305869 = 35364701) B35364701
theorem B62870579 : Blo 2179435 62870579 := bstep (se 1 (by rfl) ⟨47152934, by rfl⟩ : syracuseStep 62870579 = 94305869) B94305869
theorem B41913719 : Blo 2179435 41913719 := bstep (se 1 (by rfl) ⟨31435289, by rfl⟩ : syracuseStep 41913719 = 62870579) B62870579
theorem B27942479 : Blo 2179435 27942479 := bstep (se 1 (by rfl) ⟨20956859, by rfl⟩ : syracuseStep 27942479 = 41913719) B41913719
theorem B18628319 : Blo 2179435 18628319 := bstep (se 1 (by rfl) ⟨13971239, by rfl⟩ : syracuseStep 18628319 = 27942479) B27942479
theorem B12418879 : Blo 2179435 12418879 := bstep (se 1 (by rfl) ⟨9314159, by rfl⟩ : syracuseStep 12418879 = 18628319) B18628319
theorem B16558505 : Blo 2179435 16558505 := bstep (se 2 (by rfl) ⟨6209439, by rfl⟩ : syracuseStep 16558505 = 12418879) B12418879
theorem B11039003 : Blo 2179435 11039003 := bstep (se 1 (by rfl) ⟨8279252, by rfl⟩ : syracuseStep 11039003 = 16558505) B16558505
theorem B7359335 : Blo 2179435 7359335 := bstep (se 1 (by rfl) ⟨5519501, by rfl⟩ : syracuseStep 7359335 = 11039003) B11039003
theorem B4906223 : Blo 2179435 4906223 := bstep (se 1 (by rfl) ⟨3679667, by rfl⟩ : syracuseStep 4906223 = 7359335) B7359335
theorem B3270815 : Blo 2179435 3270815 := bstep (se 1 (by rfl) ⟨2453111, by rfl⟩ : syracuseStep 3270815 = 4906223) B4906223
theorem B2180543 : Blo 2179435 2180543 := bstep (se 1 (by rfl) ⟨1635407, by rfl⟩ : syracuseStep 2180543 = 3270815) B3270815
theorem B3270821 : Blo 2179435 3270821 := bbase (se 4 (by rfl) ⟨306639, by rfl⟩ : syracuseStep 3270821 = 613279) (by norm_num)
theorem B2180547 : Blo 2179435 2180547 := bstep (se 1 (by rfl) ⟨1635410, by rfl⟩ : syracuseStep 2180547 = 3270821) B3270821
theorem B2759761 : Blo 2179435 2759761 := bbase (se 2 (by rfl) ⟨1034910, by rfl⟩ : syracuseStep 2759761 = 2069821) (by norm_num)
theorem B3679681 : Blo 2179435 3679681 := bstep (se 2 (by rfl) ⟨1379880, by rfl⟩ : syracuseStep 3679681 = 2759761) B2759761
theorem B4906241 : Blo 2179435 4906241 := bstep (se 2 (by rfl) ⟨1839840, by rfl⟩ : syracuseStep 4906241 = 3679681) B3679681
theorem B3270827 : Blo 2179435 3270827 := bstep (se 1 (by rfl) ⟨2453120, by rfl⟩ : syracuseStep 3270827 = 4906241) B4906241
theorem B2180551 : Blo 2179435 2180551 := bstep (se 1 (by rfl) ⟨1635413, by rfl⟩ : syracuseStep 2180551 = 3270827) B3270827
theorem B2453125 : Blo 2179435 2453125 := bbase (se 4 (by rfl) ⟨229980, by rfl⟩ : syracuseStep 2453125 = 459961) (by norm_num)
theorem B3270833 : Blo 2179435 3270833 := bstep (se 2 (by rfl) ⟨1226562, by rfl⟩ : syracuseStep 3270833 = 2453125) B2453125
theorem B2180555 : Blo 2179435 2180555 := bstep (se 1 (by rfl) ⟨1635416, by rfl⟩ : syracuseStep 2180555 = 3270833) B3270833
theorem B3729901 : Blo 2179435 3729901 := bbase (se 3 (by rfl) ⟨699356, by rfl⟩ : syracuseStep 3729901 = 1398713) (by norm_num)
theorem B4973201 : Blo 2179435 4973201 := bstep (se 2 (by rfl) ⟨1864950, by rfl⟩ : syracuseStep 4973201 = 3729901) B3729901
theorem B3315467 : Blo 2179435 3315467 := bstep (se 1 (by rfl) ⟨2486600, by rfl⟩ : syracuseStep 3315467 = 4973201) B4973201
theorem B2210311 : Blo 2179435 2210311 := bstep (se 1 (by rfl) ⟨1657733, by rfl⟩ : syracuseStep 2210311 = 3315467) B3315467
theorem B11788325 : Blo 2179435 11788325 := bstep (se 4 (by rfl) ⟨1105155, by rfl⟩ : syracuseStep 11788325 = 2210311) B2210311
theorem B7858883 : Blo 2179435 7858883 := bstep (se 1 (by rfl) ⟨5894162, by rfl⟩ : syracuseStep 7858883 = 11788325) B11788325
theorem B5239255 : Blo 2179435 5239255 := bstep (se 1 (by rfl) ⟨3929441, by rfl⟩ : syracuseStep 5239255 = 7858883) B7858883
theorem B6985673 : Blo 2179435 6985673 := bstep (se 2 (by rfl) ⟨2619627, by rfl⟩ : syracuseStep 6985673 = 5239255) B5239255
theorem B4657115 : Blo 2179435 4657115 := bstep (se 1 (by rfl) ⟨3492836, by rfl⟩ : syracuseStep 4657115 = 6985673) B6985673
theorem B3104743 : Blo 2179435 3104743 := bstep (se 1 (by rfl) ⟨2328557, by rfl⟩ : syracuseStep 3104743 = 4657115) B4657115
theorem B4139657 : Blo 2179435 4139657 := bstep (se 2 (by rfl) ⟨1552371, by rfl⟩ : syracuseStep 4139657 = 3104743) B3104743
theorem B2759771 : Blo 2179435 2759771 := bstep (se 1 (by rfl) ⟨2069828, by rfl⟩ : syracuseStep 2759771 = 4139657) B4139657
theorem B7359389 : Blo 2179435 7359389 := bstep (se 3 (by rfl) ⟨1379885, by rfl⟩ : syracuseStep 7359389 = 2759771) B2759771
theorem B4906259 : Blo 2179435 4906259 := bstep (se 1 (by rfl) ⟨3679694, by rfl⟩ : syracuseStep 4906259 = 7359389) B7359389
theorem B3270839 : Blo 2179435 3270839 := bstep (se 1 (by rfl) ⟨2453129, by rfl⟩ : syracuseStep 3270839 = 4906259) B4906259
theorem B2180559 : Blo 2179435 2180559 := bstep (se 1 (by rfl) ⟨1635419, by rfl⟩ : syracuseStep 2180559 = 3270839) B3270839
theorem B3270845 : Blo 2179435 3270845 := bbase (se 3 (by rfl) ⟨613283, by rfl⟩ : syracuseStep 3270845 = 1226567) (by norm_num)
theorem B2180563 : Blo 2179435 2180563 := bstep (se 1 (by rfl) ⟨1635422, by rfl⟩ : syracuseStep 2180563 = 3270845) B3270845
theorem B4906277 : Blo 2179435 4906277 := bbase (se 4 (by rfl) ⟨459963, by rfl⟩ : syracuseStep 4906277 = 919927) (by norm_num)
theorem B3270851 : Blo 2179435 3270851 := bstep (se 1 (by rfl) ⟨2453138, by rfl⟩ : syracuseStep 3270851 = 4906277) B4906277
theorem B2180567 : Blo 2179435 2180567 := bstep (se 1 (by rfl) ⟨1635425, by rfl⟩ : syracuseStep 2180567 = 3270851) B3270851
theorem B5519573 : Blo 2179435 5519573 := bbase (se 7 (by rfl) ⟨64682, by rfl⟩ : syracuseStep 5519573 = 129365) (by norm_num)
theorem B3679715 : Blo 2179435 3679715 := bstep (se 1 (by rfl) ⟨2759786, by rfl⟩ : syracuseStep 3679715 = 5519573) B5519573
theorem B2453143 : Blo 2179435 2453143 := bstep (se 1 (by rfl) ⟨1839857, by rfl⟩ : syracuseStep 2453143 = 3679715) B3679715
theorem B3270857 : Blo 2179435 3270857 := bstep (se 2 (by rfl) ⟨1226571, by rfl⟩ : syracuseStep 3270857 = 2453143) B2453143
theorem B2180571 : Blo 2179435 2180571 := bstep (se 1 (by rfl) ⟨1635428, by rfl⟩ : syracuseStep 2180571 = 3270857) B3270857
theorem B8074853 : Blo 2179435 8074853 := bbase (se 4 (by rfl) ⟨757017, by rfl⟩ : syracuseStep 8074853 = 1514035) (by norm_num)
theorem B5383235 : Blo 2179435 5383235 := bstep (se 1 (by rfl) ⟨4037426, by rfl⟩ : syracuseStep 5383235 = 8074853) B8074853
theorem B3588823 : Blo 2179435 3588823 := bstep (se 1 (by rfl) ⟨2691617, by rfl⟩ : syracuseStep 3588823 = 5383235) B5383235
theorem B4785097 : Blo 2179435 4785097 := bstep (se 2 (by rfl) ⟨1794411, by rfl⟩ : syracuseStep 4785097 = 3588823) B3588823
theorem B6380129 : Blo 2179435 6380129 := bstep (se 2 (by rfl) ⟨2392548, by rfl⟩ : syracuseStep 6380129 = 4785097) B4785097
theorem B4253419 : Blo 2179435 4253419 := bstep (se 1 (by rfl) ⟨3190064, by rfl⟩ : syracuseStep 4253419 = 6380129) B6380129
theorem B5671225 : Blo 2179435 5671225 := bstep (se 2 (by rfl) ⟨2126709, by rfl⟩ : syracuseStep 5671225 = 4253419) B4253419
theorem B7561633 : Blo 2179435 7561633 := bstep (se 2 (by rfl) ⟨2835612, by rfl⟩ : syracuseStep 7561633 = 5671225) B5671225
theorem B10082177 : Blo 2179435 10082177 := bstep (se 2 (by rfl) ⟨3780816, by rfl⟩ : syracuseStep 10082177 = 7561633) B7561633
theorem B6721451 : Blo 2179435 6721451 := bstep (se 1 (by rfl) ⟨5041088, by rfl⟩ : syracuseStep 6721451 = 10082177) B10082177
theorem B4480967 : Blo 2179435 4480967 := bstep (se 1 (by rfl) ⟨3360725, by rfl⟩ : syracuseStep 4480967 = 6721451) B6721451
theorem B2987311 : Blo 2179435 2987311 := bstep (se 1 (by rfl) ⟨2240483, by rfl⟩ : syracuseStep 2987311 = 4480967) B4480967
theorem B63729301 : Blo 2179435 63729301 := bstep (se 6 (by rfl) ⟨1493655, by rfl⟩ : syracuseStep 63729301 = 2987311) B2987311
theorem B84972401 : Blo 2179435 84972401 := bstep (se 2 (by rfl) ⟨31864650, by rfl⟩ : syracuseStep 84972401 = 63729301) B63729301
theorem B56648267 : Blo 2179435 56648267 := bstep (se 1 (by rfl) ⟨42486200, by rfl⟩ : syracuseStep 56648267 = 84972401) B84972401
theorem B37765511 : Blo 2179435 37765511 := bstep (se 1 (by rfl) ⟨28324133, by rfl⟩ : syracuseStep 37765511 = 56648267) B56648267
theorem B25177007 : Blo 2179435 25177007 := bstep (se 1 (by rfl) ⟨18882755, by rfl⟩ : syracuseStep 25177007 = 37765511) B37765511
theorem B16784671 : Blo 2179435 16784671 := bstep (se 1 (by rfl) ⟨12588503, by rfl⟩ : syracuseStep 16784671 = 25177007) B25177007
theorem B22379561 : Blo 2179435 22379561 := bstep (se 2 (by rfl) ⟨8392335, by rfl⟩ : syracuseStep 22379561 = 16784671) B16784671
theorem B14919707 : Blo 2179435 14919707 := bstep (se 1 (by rfl) ⟨11189780, by rfl⟩ : syracuseStep 14919707 = 22379561) B22379561
theorem B9946471 : Blo 2179435 9946471 := bstep (se 1 (by rfl) ⟨7459853, by rfl⟩ : syracuseStep 9946471 = 14919707) B14919707
theorem B13261961 : Blo 2179435 13261961 := bstep (se 2 (by rfl) ⟨4973235, by rfl⟩ : syracuseStep 13261961 = 9946471) B9946471
theorem B8841307 : Blo 2179435 8841307 := bstep (se 1 (by rfl) ⟨6630980, by rfl⟩ : syracuseStep 8841307 = 13261961) B13261961
theorem B11788409 : Blo 2179435 11788409 := bstep (se 2 (by rfl) ⟨4420653, by rfl⟩ : syracuseStep 11788409 = 8841307) B8841307
theorem B7858939 : Blo 2179435 7858939 := bstep (se 1 (by rfl) ⟨5894204, by rfl⟩ : syracuseStep 7858939 = 11788409) B11788409
theorem B10478585 : Blo 2179435 10478585 := bstep (se 2 (by rfl) ⟨3929469, by rfl⟩ : syracuseStep 10478585 = 7858939) B7858939
theorem B6985723 : Blo 2179435 6985723 := bstep (se 1 (by rfl) ⟨5239292, by rfl⟩ : syracuseStep 6985723 = 10478585) B10478585
theorem B9314297 : Blo 2179435 9314297 := bstep (se 2 (by rfl) ⟨3492861, by rfl⟩ : syracuseStep 9314297 = 6985723) B6985723
theorem B6209531 : Blo 2179435 6209531 := bstep (se 1 (by rfl) ⟨4657148, by rfl⟩ : syracuseStep 6209531 = 9314297) B9314297
theorem B4139687 : Blo 2179435 4139687 := bstep (se 1 (by rfl) ⟨3104765, by rfl⟩ : syracuseStep 4139687 = 6209531) B6209531
theorem B11039165 : Blo 2179435 11039165 := bstep (se 3 (by rfl) ⟨2069843, by rfl⟩ : syracuseStep 11039165 = 4139687) B4139687
theorem B7359443 : Blo 2179435 7359443 := bstep (se 1 (by rfl) ⟨5519582, by rfl⟩ : syracuseStep 7359443 = 11039165) B11039165
theorem B4906295 : Blo 2179435 4906295 := bstep (se 1 (by rfl) ⟨3679721, by rfl⟩ : syracuseStep 4906295 = 7359443) B7359443
theorem B3270863 : Blo 2179435 3270863 := bstep (se 1 (by rfl) ⟨2453147, by rfl⟩ : syracuseStep 3270863 = 4906295) B4906295
theorem B2180575 : Blo 2179435 2180575 := bstep (se 1 (by rfl) ⟨1635431, by rfl⟩ : syracuseStep 2180575 = 3270863) B3270863
theorem B3270869 : Blo 2179435 3270869 := bbase (se 7 (by rfl) ⟨38330, by rfl⟩ : syracuseStep 3270869 = 76661) (by norm_num)
theorem B2180579 : Blo 2179435 2180579 := bstep (se 1 (by rfl) ⟨1635434, by rfl⟩ : syracuseStep 2180579 = 3270869) B3270869
theorem B3929485 : Blo 2179435 3929485 := bbase (se 3 (by rfl) ⟨736778, by rfl⟩ : syracuseStep 3929485 = 1473557) (by norm_num)
theorem B5239313 : Blo 2179435 5239313 := bstep (se 2 (by rfl) ⟨1964742, by rfl⟩ : syracuseStep 5239313 = 3929485) B3929485
theorem B3492875 : Blo 2179435 3492875 := bstep (se 1 (by rfl) ⟨2619656, by rfl⟩ : syracuseStep 3492875 = 5239313) B5239313
theorem B2328583 : Blo 2179435 2328583 := bstep (se 1 (by rfl) ⟨1746437, by rfl⟩ : syracuseStep 2328583 = 3492875) B3492875
theorem B3104777 : Blo 2179435 3104777 := bstep (se 2 (by rfl) ⟨1164291, by rfl⟩ : syracuseStep 3104777 = 2328583) B2328583
theorem B8279405 : Blo 2179435 8279405 := bstep (se 3 (by rfl) ⟨1552388, by rfl⟩ : syracuseStep 8279405 = 3104777) B3104777
theorem B5519603 : Blo 2179435 5519603 := bstep (se 1 (by rfl) ⟨4139702, by rfl⟩ : syracuseStep 5519603 = 8279405) B8279405
theorem B3679735 : Blo 2179435 3679735 := bstep (se 1 (by rfl) ⟨2759801, by rfl⟩ : syracuseStep 3679735 = 5519603) B5519603
theorem B4906313 : Blo 2179435 4906313 := bstep (se 2 (by rfl) ⟨1839867, by rfl⟩ : syracuseStep 4906313 = 3679735) B3679735
theorem B3270875 : Blo 2179435 3270875 := bstep (se 1 (by rfl) ⟨2453156, by rfl⟩ : syracuseStep 3270875 = 4906313) B4906313
theorem B2180583 : Blo 2179435 2180583 := bstep (se 1 (by rfl) ⟨1635437, by rfl⟩ : syracuseStep 2180583 = 3270875) B3270875
theorem B2453161 : Blo 2179435 2453161 := bbase (se 2 (by rfl) ⟨919935, by rfl⟩ : syracuseStep 2453161 = 1839871) (by norm_num)
theorem B3270881 : Blo 2179435 3270881 := bstep (se 2 (by rfl) ⟨1226580, by rfl⟩ : syracuseStep 3270881 = 2453161) B2453161
theorem B2180587 : Blo 2179435 2180587 := bstep (se 1 (by rfl) ⟨1635440, by rfl⟩ : syracuseStep 2180587 = 3270881) B3270881
theorem B7858997 : Blo 2179435 7858997 := bbase (se 5 (by rfl) ⟨368390, by rfl⟩ : syracuseStep 7858997 = 736781) (by norm_num)
theorem B5239331 : Blo 2179435 5239331 := bstep (se 1 (by rfl) ⟨3929498, by rfl⟩ : syracuseStep 5239331 = 7858997) B7858997
theorem B3492887 : Blo 2179435 3492887 := bstep (se 1 (by rfl) ⟨2619665, by rfl⟩ : syracuseStep 3492887 = 5239331) B5239331
theorem B9314365 : Blo 2179435 9314365 := bstep (se 3 (by rfl) ⟨1746443, by rfl⟩ : syracuseStep 9314365 = 3492887) B3492887
theorem B12419153 : Blo 2179435 12419153 := bstep (se 2 (by rfl) ⟨4657182, by rfl⟩ : syracuseStep 12419153 = 9314365) B9314365
theorem B8279435 : Blo 2179435 8279435 := bstep (se 1 (by rfl) ⟨6209576, by rfl⟩ : syracuseStep 8279435 = 12419153) B12419153
theorem B5519623 : Blo 2179435 5519623 := bstep (se 1 (by rfl) ⟨4139717, by rfl⟩ : syracuseStep 5519623 = 8279435) B8279435
theorem B7359497 : Blo 2179435 7359497 := bstep (se 2 (by rfl) ⟨2759811, by rfl⟩ : syracuseStep 7359497 = 5519623) B5519623
theorem B4906331 : Blo 2179435 4906331 := bstep (se 1 (by rfl) ⟨3679748, by rfl⟩ : syracuseStep 4906331 = 7359497) B7359497
theorem B3270887 : Blo 2179435 3270887 := bstep (se 1 (by rfl) ⟨2453165, by rfl⟩ : syracuseStep 3270887 = 4906331) B4906331
theorem B2180591 : Blo 2179435 2180591 := bstep (se 1 (by rfl) ⟨1635443, by rfl⟩ : syracuseStep 2180591 = 3270887) B3270887
theorem B3270893 : Blo 2179435 3270893 := bbase (se 3 (by rfl) ⟨613292, by rfl⟩ : syracuseStep 3270893 = 1226585) (by norm_num)
theorem B2180595 : Blo 2179435 2180595 := bstep (se 1 (by rfl) ⟨1635446, by rfl⟩ : syracuseStep 2180595 = 3270893) B3270893
theorem B4906349 : Blo 2179435 4906349 := bbase (se 3 (by rfl) ⟨919940, by rfl⟩ : syracuseStep 4906349 = 1839881) (by norm_num)
theorem B3270899 : Blo 2179435 3270899 := bstep (se 1 (by rfl) ⟨2453174, by rfl⟩ : syracuseStep 3270899 = 4906349) B4906349
theorem B2180599 : Blo 2179435 2180599 := bstep (se 1 (by rfl) ⟨1635449, by rfl⟩ : syracuseStep 2180599 = 3270899) B3270899
theorem B4139741 : Blo 2179435 4139741 := bbase (se 3 (by rfl) ⟨776201, by rfl⟩ : syracuseStep 4139741 = 1552403) (by norm_num)
theorem B2759827 : Blo 2179435 2759827 := bstep (se 1 (by rfl) ⟨2069870, by rfl⟩ : syracuseStep 2759827 = 4139741) B4139741
theorem B3679769 : Blo 2179435 3679769 := bstep (se 2 (by rfl) ⟨1379913, by rfl⟩ : syracuseStep 3679769 = 2759827) B2759827
theorem B2453179 : Blo 2179435 2453179 := bstep (se 1 (by rfl) ⟨1839884, by rfl⟩ : syracuseStep 2453179 = 3679769) B3679769
theorem B3270905 : Blo 2179435 3270905 := bstep (se 2 (by rfl) ⟨1226589, by rfl⟩ : syracuseStep 3270905 = 2453179) B2453179
theorem B2180603 : Blo 2179435 2180603 := bstep (se 1 (by rfl) ⟨1635452, by rfl⟩ : syracuseStep 2180603 = 3270905) B3270905
theorem B4973309 : Blo 2179435 4973309 := bbase (se 3 (by rfl) ⟨932495, by rfl⟩ : syracuseStep 4973309 = 1864991) (by norm_num)
theorem B3315539 : Blo 2179435 3315539 := bstep (se 1 (by rfl) ⟨2486654, by rfl⟩ : syracuseStep 3315539 = 4973309) B4973309
theorem B2210359 : Blo 2179435 2210359 := bstep (se 1 (by rfl) ⟨1657769, by rfl⟩ : syracuseStep 2210359 = 3315539) B3315539
theorem B2947145 : Blo 2179435 2947145 := bstep (se 2 (by rfl) ⟨1105179, by rfl⟩ : syracuseStep 2947145 = 2210359) B2210359
theorem B7859053 : Blo 2179435 7859053 := bstep (se 3 (by rfl) ⟨1473572, by rfl⟩ : syracuseStep 7859053 = 2947145) B2947145
theorem B10478737 : Blo 2179435 10478737 := bstep (se 2 (by rfl) ⟨3929526, by rfl⟩ : syracuseStep 10478737 = 7859053) B7859053
theorem B55886597 : Blo 2179435 55886597 := bstep (se 4 (by rfl) ⟨5239368, by rfl⟩ : syracuseStep 55886597 = 10478737) B10478737
theorem B37257731 : Blo 2179435 37257731 := bstep (se 1 (by rfl) ⟨27943298, by rfl⟩ : syracuseStep 37257731 = 55886597) B55886597
theorem B24838487 : Blo 2179435 24838487 := bstep (se 1 (by rfl) ⟨18628865, by rfl⟩ : syracuseStep 24838487 = 37257731) B37257731
theorem B16558991 : Blo 2179435 16558991 := bstep (se 1 (by rfl) ⟨12419243, by rfl⟩ : syracuseStep 16558991 = 24838487) B24838487
theorem B11039327 : Blo 2179435 11039327 := bstep (se 1 (by rfl) ⟨8279495, by rfl⟩ : syracuseStep 11039327 = 16558991) B16558991
theorem B7359551 : Blo 2179435 7359551 := bstep (se 1 (by rfl) ⟨5519663, by rfl⟩ : syracuseStep 7359551 = 11039327) B11039327
theorem B4906367 : Blo 2179435 4906367 := bstep (se 1 (by rfl) ⟨3679775, by rfl⟩ : syracuseStep 4906367 = 7359551) B7359551
theorem B3270911 : Blo 2179435 3270911 := bstep (se 1 (by rfl) ⟨2453183, by rfl⟩ : syracuseStep 3270911 = 4906367) B4906367
theorem B2180607 : Blo 2179435 2180607 := bstep (se 1 (by rfl) ⟨1635455, by rfl⟩ : syracuseStep 2180607 = 3270911) B3270911
theorem B3270917 : Blo 2179435 3270917 := bbase (se 4 (by rfl) ⟨306648, by rfl⟩ : syracuseStep 3270917 = 613297) (by norm_num)
theorem B2180611 : Blo 2179435 2180611 := bstep (se 1 (by rfl) ⟨1635458, by rfl⟩ : syracuseStep 2180611 = 3270917) B3270917
theorem B3679789 : Blo 2179435 3679789 := bbase (se 3 (by rfl) ⟨689960, by rfl⟩ : syracuseStep 3679789 = 1379921) (by norm_num)
theorem B4906385 : Blo 2179435 4906385 := bstep (se 2 (by rfl) ⟨1839894, by rfl⟩ : syracuseStep 4906385 = 3679789) B3679789
theorem B3270923 : Blo 2179435 3270923 := bstep (se 1 (by rfl) ⟨2453192, by rfl⟩ : syracuseStep 3270923 = 4906385) B4906385
theorem B2180615 : Blo 2179435 2180615 := bstep (se 1 (by rfl) ⟨1635461, by rfl⟩ : syracuseStep 2180615 = 3270923) B3270923
theorem B2453197 : Blo 2179435 2453197 := bbase (se 3 (by rfl) ⟨459974, by rfl⟩ : syracuseStep 2453197 = 919949) (by norm_num)
theorem B3270929 : Blo 2179435 3270929 := bstep (se 2 (by rfl) ⟨1226598, by rfl⟩ : syracuseStep 3270929 = 2453197) B2453197
theorem B2180619 : Blo 2179435 2180619 := bstep (se 1 (by rfl) ⟨1635464, by rfl⟩ : syracuseStep 2180619 = 3270929) B3270929
theorem B7359605 : Blo 2179435 7359605 := bbase (se 5 (by rfl) ⟨344981, by rfl⟩ : syracuseStep 7359605 = 689963) (by norm_num)
theorem B4906403 : Blo 2179435 4906403 := bstep (se 1 (by rfl) ⟨3679802, by rfl⟩ : syracuseStep 4906403 = 7359605) B7359605
theorem B3270935 : Blo 2179435 3270935 := bstep (se 1 (by rfl) ⟨2453201, by rfl⟩ : syracuseStep 3270935 = 4906403) B4906403
theorem B2180623 : Blo 2179435 2180623 := bstep (se 1 (by rfl) ⟨1635467, by rfl⟩ : syracuseStep 2180623 = 3270935) B3270935
theorem B3270941 : Blo 2179435 3270941 := bbase (se 3 (by rfl) ⟨613301, by rfl⟩ : syracuseStep 3270941 = 1226603) (by norm_num)
theorem B2180627 : Blo 2179435 2180627 := bstep (se 1 (by rfl) ⟨1635470, by rfl⟩ : syracuseStep 2180627 = 3270941) B3270941
theorem B4906421 : Blo 2179435 4906421 := bbase (se 5 (by rfl) ⟨229988, by rfl⟩ : syracuseStep 4906421 = 459977) (by norm_num)
theorem B3270947 : Blo 2179435 3270947 := bstep (se 1 (by rfl) ⟨2453210, by rfl⟩ : syracuseStep 3270947 = 4906421) B4906421
theorem B2180631 : Blo 2179435 2180631 := bstep (se 1 (by rfl) ⟨1635473, by rfl⟩ : syracuseStep 2180631 = 3270947) B3270947
theorem B4657277 : Blo 2179435 4657277 := bbase (se 3 (by rfl) ⟨873239, by rfl⟩ : syracuseStep 4657277 = 1746479) (by norm_num)
theorem B12419405 : Blo 2179435 12419405 := bstep (se 3 (by rfl) ⟨2328638, by rfl⟩ : syracuseStep 12419405 = 4657277) B4657277
theorem B8279603 : Blo 2179435 8279603 := bstep (se 1 (by rfl) ⟨6209702, by rfl⟩ : syracuseStep 8279603 = 12419405) B12419405
theorem B5519735 : Blo 2179435 5519735 := bstep (se 1 (by rfl) ⟨4139801, by rfl⟩ : syracuseStep 5519735 = 8279603) B8279603
theorem B3679823 : Blo 2179435 3679823 := bstep (se 1 (by rfl) ⟨2759867, by rfl⟩ : syracuseStep 3679823 = 5519735) B5519735
theorem B2453215 : Blo 2179435 2453215 := bstep (se 1 (by rfl) ⟨1839911, by rfl⟩ : syracuseStep 2453215 = 3679823) B3679823
theorem B3270953 : Blo 2179435 3270953 := bstep (se 2 (by rfl) ⟨1226607, by rfl⟩ : syracuseStep 3270953 = 2453215) B2453215
theorem B2180635 : Blo 2179435 2180635 := bstep (se 1 (by rfl) ⟨1635476, by rfl⟩ : syracuseStep 2180635 = 3270953) B3270953
theorem B4657285 : Blo 2179435 4657285 := bbase (se 4 (by rfl) ⟨436620, by rfl⟩ : syracuseStep 4657285 = 873241) (by norm_num)
theorem B6209713 : Blo 2179435 6209713 := bstep (se 2 (by rfl) ⟨2328642, by rfl⟩ : syracuseStep 6209713 = 4657285) B4657285
theorem B8279617 : Blo 2179435 8279617 := bstep (se 2 (by rfl) ⟨3104856, by rfl⟩ : syracuseStep 8279617 = 6209713) B6209713
theorem B11039489 : Blo 2179435 11039489 := bstep (se 2 (by rfl) ⟨4139808, by rfl⟩ : syracuseStep 11039489 = 8279617) B8279617
theorem B7359659 : Blo 2179435 7359659 := bstep (se 1 (by rfl) ⟨5519744, by rfl⟩ : syracuseStep 7359659 = 11039489) B11039489
theorem B4906439 : Blo 2179435 4906439 := bstep (se 1 (by rfl) ⟨3679829, by rfl⟩ : syracuseStep 4906439 = 7359659) B7359659
theorem B3270959 : Blo 2179435 3270959 := bstep (se 1 (by rfl) ⟨2453219, by rfl⟩ : syracuseStep 3270959 = 4906439) B4906439
theorem B2180639 : Blo 2179435 2180639 := bstep (se 1 (by rfl) ⟨1635479, by rfl⟩ : syracuseStep 2180639 = 3270959) B3270959
theorem B3270965 : Blo 2179435 3270965 := bbase (se 5 (by rfl) ⟨153326, by rfl⟩ : syracuseStep 3270965 = 306653) (by norm_num)
theorem B2180643 : Blo 2179435 2180643 := bstep (se 1 (by rfl) ⟨1635482, by rfl⟩ : syracuseStep 2180643 = 3270965) B3270965
theorem B5519765 : Blo 2179435 5519765 := bbase (se 6 (by rfl) ⟨129369, by rfl⟩ : syracuseStep 5519765 = 258739) (by norm_num)
theorem B3679843 : Blo 2179435 3679843 := bstep (se 1 (by rfl) ⟨2759882, by rfl⟩ : syracuseStep 3679843 = 5519765) B5519765
theorem B4906457 : Blo 2179435 4906457 := bstep (se 2 (by rfl) ⟨1839921, by rfl⟩ : syracuseStep 4906457 = 3679843) B3679843
theorem B3270971 : Blo 2179435 3270971 := bstep (se 1 (by rfl) ⟨2453228, by rfl⟩ : syracuseStep 3270971 = 4906457) B4906457
theorem B2180647 : Blo 2179435 2180647 := bstep (se 1 (by rfl) ⟨1635485, by rfl⟩ : syracuseStep 2180647 = 3270971) B3270971
theorem B2453233 : Blo 2179435 2453233 := bbase (se 2 (by rfl) ⟨919962, by rfl⟩ : syracuseStep 2453233 = 1839925) (by norm_num)
theorem B3270977 : Blo 2179435 3270977 := bstep (se 2 (by rfl) ⟨1226616, by rfl⟩ : syracuseStep 3270977 = 2453233) B2453233
theorem B2180651 : Blo 2179435 2180651 := bstep (se 1 (by rfl) ⟨1635488, by rfl⟩ : syracuseStep 2180651 = 3270977) B3270977
theorem B7177909 : Blo 2179435 7177909 := bbase (se 5 (by rfl) ⟨336464, by rfl⟩ : syracuseStep 7177909 = 672929) (by norm_num)
theorem B9570545 : Blo 2179435 9570545 := bstep (se 2 (by rfl) ⟨3588954, by rfl⟩ : syracuseStep 9570545 = 7177909) B7177909
theorem B6380363 : Blo 2179435 6380363 := bstep (se 1 (by rfl) ⟨4785272, by rfl⟩ : syracuseStep 6380363 = 9570545) B9570545
theorem B4253575 : Blo 2179435 4253575 := bstep (se 1 (by rfl) ⟨3190181, by rfl⟩ : syracuseStep 4253575 = 6380363) B6380363
theorem B5671433 : Blo 2179435 5671433 := bstep (se 2 (by rfl) ⟨2126787, by rfl⟩ : syracuseStep 5671433 = 4253575) B4253575
theorem B3780955 : Blo 2179435 3780955 := bstep (se 1 (by rfl) ⟨2835716, by rfl⟩ : syracuseStep 3780955 = 5671433) B5671433
theorem B5041273 : Blo 2179435 5041273 := bstep (se 2 (by rfl) ⟨1890477, by rfl⟩ : syracuseStep 5041273 = 3780955) B3780955
theorem B6721697 : Blo 2179435 6721697 := bstep (se 2 (by rfl) ⟨2520636, by rfl⟩ : syracuseStep 6721697 = 5041273) B5041273
theorem B4481131 : Blo 2179435 4481131 := bstep (se 1 (by rfl) ⟨3360848, by rfl⟩ : syracuseStep 4481131 = 6721697) B6721697
theorem B5974841 : Blo 2179435 5974841 := bstep (se 2 (by rfl) ⟨2240565, by rfl⟩ : syracuseStep 5974841 = 4481131) B4481131
theorem B15932909 : Blo 2179435 15932909 := bstep (se 3 (by rfl) ⟨2987420, by rfl⟩ : syracuseStep 15932909 = 5974841) B5974841
theorem B10621939 : Blo 2179435 10621939 := bstep (se 1 (by rfl) ⟨7966454, by rfl⟩ : syracuseStep 10621939 = 15932909) B15932909
theorem B14162585 : Blo 2179435 14162585 := bstep (se 2 (by rfl) ⟨5310969, by rfl⟩ : syracuseStep 14162585 = 10621939) B10621939
theorem B37766893 : Blo 2179435 37766893 := bstep (se 3 (by rfl) ⟨7081292, by rfl⟩ : syracuseStep 37766893 = 14162585) B14162585
theorem B50355857 : Blo 2179435 50355857 := bstep (se 2 (by rfl) ⟨18883446, by rfl⟩ : syracuseStep 50355857 = 37766893) B37766893
theorem B33570571 : Blo 2179435 33570571 := bstep (se 1 (by rfl) ⟨25177928, by rfl⟩ : syracuseStep 33570571 = 50355857) B50355857
theorem B44760761 : Blo 2179435 44760761 := bstep (se 2 (by rfl) ⟨16785285, by rfl⟩ : syracuseStep 44760761 = 33570571) B33570571
theorem B29840507 : Blo 2179435 29840507 := bstep (se 1 (by rfl) ⟨22380380, by rfl⟩ : syracuseStep 29840507 = 44760761) B44760761
theorem B19893671 : Blo 2179435 19893671 := bstep (se 1 (by rfl) ⟨14920253, by rfl⟩ : syracuseStep 19893671 = 29840507) B29840507
theorem B13262447 : Blo 2179435 13262447 := bstep (se 1 (by rfl) ⟨9946835, by rfl⟩ : syracuseStep 13262447 = 19893671) B19893671
theorem B8841631 : Blo 2179435 8841631 := bstep (se 1 (by rfl) ⟨6631223, by rfl⟩ : syracuseStep 8841631 = 13262447) B13262447
theorem B11788841 : Blo 2179435 11788841 := bstep (se 2 (by rfl) ⟨4420815, by rfl⟩ : syracuseStep 11788841 = 8841631) B8841631
theorem B31436909 : Blo 2179435 31436909 := bstep (se 3 (by rfl) ⟨5894420, by rfl⟩ : syracuseStep 31436909 = 11788841) B11788841
theorem B20957939 : Blo 2179435 20957939 := bstep (se 1 (by rfl) ⟨15718454, by rfl⟩ : syracuseStep 20957939 = 31436909) B31436909
theorem B13971959 : Blo 2179435 13971959 := bstep (se 1 (by rfl) ⟨10478969, by rfl⟩ : syracuseStep 13971959 = 20957939) B20957939
theorem B9314639 : Blo 2179435 9314639 := bstep (se 1 (by rfl) ⟨6985979, by rfl⟩ : syracuseStep 9314639 = 13971959) B13971959
theorem B6209759 : Blo 2179435 6209759 := bstep (se 1 (by rfl) ⟨4657319, by rfl⟩ : syracuseStep 6209759 = 9314639) B9314639
theorem B4139839 : Blo 2179435 4139839 := bstep (se 1 (by rfl) ⟨3104879, by rfl⟩ : syracuseStep 4139839 = 6209759) B6209759
theorem B5519785 : Blo 2179435 5519785 := bstep (se 2 (by rfl) ⟨2069919, by rfl⟩ : syracuseStep 5519785 = 4139839) B4139839
theorem B7359713 : Blo 2179435 7359713 := bstep (se 2 (by rfl) ⟨2759892, by rfl⟩ : syracuseStep 7359713 = 5519785) B5519785
theorem B4906475 : Blo 2179435 4906475 := bstep (se 1 (by rfl) ⟨3679856, by rfl⟩ : syracuseStep 4906475 = 7359713) B7359713
theorem B3270983 : Blo 2179435 3270983 := bstep (se 1 (by rfl) ⟨2453237, by rfl⟩ : syracuseStep 3270983 = 4906475) B4906475
theorem B2180655 : Blo 2179435 2180655 := bstep (se 1 (by rfl) ⟨1635491, by rfl⟩ : syracuseStep 2180655 = 3270983) B3270983
theorem B3270989 : Blo 2179435 3270989 := bbase (se 3 (by rfl) ⟨613310, by rfl⟩ : syracuseStep 3270989 = 1226621) (by norm_num)
theorem B2180659 : Blo 2179435 2180659 := bstep (se 1 (by rfl) ⟨1635494, by rfl⟩ : syracuseStep 2180659 = 3270989) B3270989
theorem B4906493 : Blo 2179435 4906493 := bbase (se 3 (by rfl) ⟨919967, by rfl⟩ : syracuseStep 4906493 = 1839935) (by norm_num)
theorem B3270995 : Blo 2179435 3270995 := bstep (se 1 (by rfl) ⟨2453246, by rfl⟩ : syracuseStep 3270995 = 4906493) B4906493
theorem B2180663 : Blo 2179435 2180663 := bstep (se 1 (by rfl) ⟨1635497, by rfl⟩ : syracuseStep 2180663 = 3270995) B3270995
theorem B3679877 : Blo 2179435 3679877 := bbase (se 4 (by rfl) ⟨344988, by rfl⟩ : syracuseStep 3679877 = 689977) (by norm_num)
theorem B2453251 : Blo 2179435 2453251 := bstep (se 1 (by rfl) ⟨1839938, by rfl⟩ : syracuseStep 2453251 = 3679877) B3679877
theorem B3271001 : Blo 2179435 3271001 := bstep (se 2 (by rfl) ⟨1226625, by rfl⟩ : syracuseStep 3271001 = 2453251) B2453251
theorem B2180667 : Blo 2179435 2180667 := bstep (se 1 (by rfl) ⟨1635500, by rfl⟩ : syracuseStep 2180667 = 3271001) B3271001
theorem B16559477 : Blo 2179435 16559477 := bbase (se 5 (by rfl) ⟨776225, by rfl⟩ : syracuseStep 16559477 = 1552451) (by norm_num)
theorem B11039651 : Blo 2179435 11039651 := bstep (se 1 (by rfl) ⟨8279738, by rfl⟩ : syracuseStep 11039651 = 16559477) B16559477
theorem B7359767 : Blo 2179435 7359767 := bstep (se 1 (by rfl) ⟨5519825, by rfl⟩ : syracuseStep 7359767 = 11039651) B11039651
theorem B4906511 : Blo 2179435 4906511 := bstep (se 1 (by rfl) ⟨3679883, by rfl⟩ : syracuseStep 4906511 = 7359767) B7359767
theorem B3271007 : Blo 2179435 3271007 := bstep (se 1 (by rfl) ⟨2453255, by rfl⟩ : syracuseStep 3271007 = 4906511) B4906511
theorem B2180671 : Blo 2179435 2180671 := bstep (se 1 (by rfl) ⟨1635503, by rfl⟩ : syracuseStep 2180671 = 3271007) B3271007
theorem B3271013 : Blo 2179435 3271013 := bbase (se 4 (by rfl) ⟨306657, by rfl⟩ : syracuseStep 3271013 = 613315) (by norm_num)
theorem B2180675 : Blo 2179435 2180675 := bstep (se 1 (by rfl) ⟨1635506, by rfl⟩ : syracuseStep 2180675 = 3271013) B3271013
theorem B4139885 : Blo 2179435 4139885 := bbase (se 3 (by rfl) ⟨776228, by rfl⟩ : syracuseStep 4139885 = 1552457) (by norm_num)
theorem B2759923 : Blo 2179435 2759923 := bstep (se 1 (by rfl) ⟨2069942, by rfl⟩ : syracuseStep 2759923 = 4139885) B4139885
theorem B3679897 : Blo 2179435 3679897 := bstep (se 2 (by rfl) ⟨1379961, by rfl⟩ : syracuseStep 3679897 = 2759923) B2759923
theorem B4906529 : Blo 2179435 4906529 := bstep (se 2 (by rfl) ⟨1839948, by rfl⟩ : syracuseStep 4906529 = 3679897) B3679897
theorem B3271019 : Blo 2179435 3271019 := bstep (se 1 (by rfl) ⟨2453264, by rfl⟩ : syracuseStep 3271019 = 4906529) B4906529
theorem B2180679 : Blo 2179435 2180679 := bstep (se 1 (by rfl) ⟨1635509, by rfl⟩ : syracuseStep 2180679 = 3271019) B3271019
theorem B2453269 : Blo 2179435 2453269 := bbase (se 6 (by rfl) ⟨57498, by rfl⟩ : syracuseStep 2453269 = 114997) (by norm_num)
theorem B3271025 : Blo 2179435 3271025 := bstep (se 2 (by rfl) ⟨1226634, by rfl⟩ : syracuseStep 3271025 = 2453269) B2453269
theorem B2180683 : Blo 2179435 2180683 := bstep (se 1 (by rfl) ⟨1635512, by rfl⟩ : syracuseStep 2180683 = 3271025) B3271025
theorem B2759933 : Blo 2179435 2759933 := bbase (se 3 (by rfl) ⟨517487, by rfl⟩ : syracuseStep 2759933 = 1034975) (by norm_num)
theorem B7359821 : Blo 2179435 7359821 := bstep (se 3 (by rfl) ⟨1379966, by rfl⟩ : syracuseStep 7359821 = 2759933) B2759933
theorem B4906547 : Blo 2179435 4906547 := bstep (se 1 (by rfl) ⟨3679910, by rfl⟩ : syracuseStep 4906547 = 7359821) B7359821
theorem B3271031 : Blo 2179435 3271031 := bstep (se 1 (by rfl) ⟨2453273, by rfl⟩ : syracuseStep 3271031 = 4906547) B4906547
theorem B2180687 : Blo 2179435 2180687 := bstep (se 1 (by rfl) ⟨1635515, by rfl⟩ : syracuseStep 2180687 = 3271031) B3271031
theorem B3271037 : Blo 2179435 3271037 := bbase (se 3 (by rfl) ⟨613319, by rfl⟩ : syracuseStep 3271037 = 1226639) (by norm_num)
theorem B2180691 : Blo 2179435 2180691 := bstep (se 1 (by rfl) ⟨1635518, by rfl⟩ : syracuseStep 2180691 = 3271037) B3271037
theorem B4906565 : Blo 2179435 4906565 := bbase (se 4 (by rfl) ⟨459990, by rfl⟩ : syracuseStep 4906565 = 919981) (by norm_num)
theorem B3271043 : Blo 2179435 3271043 := bstep (se 1 (by rfl) ⟨2453282, by rfl⟩ : syracuseStep 3271043 = 4906565) B4906565
theorem B2180695 : Blo 2179435 2180695 := bstep (se 1 (by rfl) ⟨1635521, by rfl⟩ : syracuseStep 2180695 = 3271043) B3271043
theorem B3493061 : Blo 2179435 3493061 := bbase (se 4 (by rfl) ⟨327474, by rfl⟩ : syracuseStep 3493061 = 654949) (by norm_num)
theorem B2328707 : Blo 2179435 2328707 := bstep (se 1 (by rfl) ⟨1746530, by rfl⟩ : syracuseStep 2328707 = 3493061) B3493061
theorem B6209885 : Blo 2179435 6209885 := bstep (se 3 (by rfl) ⟨1164353, by rfl⟩ : syracuseStep 6209885 = 2328707) B2328707
theorem B4139923 : Blo 2179435 4139923 := bstep (se 1 (by rfl) ⟨3104942, by rfl⟩ : syracuseStep 4139923 = 6209885) B6209885
theorem B5519897 : Blo 2179435 5519897 := bstep (se 2 (by rfl) ⟨2069961, by rfl⟩ : syracuseStep 5519897 = 4139923) B4139923
theorem B3679931 : Blo 2179435 3679931 := bstep (se 1 (by rfl) ⟨2759948, by rfl⟩ : syracuseStep 3679931 = 5519897) B5519897
theorem B2453287 : Blo 2179435 2453287 := bstep (se 1 (by rfl) ⟨1839965, by rfl⟩ : syracuseStep 2453287 = 3679931) B3679931
theorem B3271049 : Blo 2179435 3271049 := bstep (se 2 (by rfl) ⟨1226643, by rfl⟩ : syracuseStep 3271049 = 2453287) B2453287
theorem B2180699 : Blo 2179435 2180699 := bstep (se 1 (by rfl) ⟨1635524, by rfl⟩ : syracuseStep 2180699 = 3271049) B3271049
theorem B11039813 : Blo 2179435 11039813 := bbase (se 4 (by rfl) ⟨1034982, by rfl⟩ : syracuseStep 11039813 = 2069965) (by norm_num)
theorem B7359875 : Blo 2179435 7359875 := bstep (se 1 (by rfl) ⟨5519906, by rfl⟩ : syracuseStep 7359875 = 11039813) B11039813
theorem B4906583 : Blo 2179435 4906583 := bstep (se 1 (by rfl) ⟨3679937, by rfl⟩ : syracuseStep 4906583 = 7359875) B7359875
theorem B3271055 : Blo 2179435 3271055 := bstep (se 1 (by rfl) ⟨2453291, by rfl⟩ : syracuseStep 3271055 = 4906583) B4906583
theorem B2180703 : Blo 2179435 2180703 := bstep (se 1 (by rfl) ⟨1635527, by rfl⟩ : syracuseStep 2180703 = 3271055) B3271055
theorem B3271061 : Blo 2179435 3271061 := bbase (se 6 (by rfl) ⟨76665, by rfl⟩ : syracuseStep 3271061 = 153331) (by norm_num)
theorem B2180707 : Blo 2179435 2180707 := bstep (se 1 (by rfl) ⟨1635530, by rfl⟩ : syracuseStep 2180707 = 3271061) B3271061
theorem B2486773 : Blo 2179435 2486773 := bbase (se 5 (by rfl) ⟨116567, by rfl⟩ : syracuseStep 2486773 = 233135) (by norm_num)
theorem B3315697 : Blo 2179435 3315697 := bstep (se 2 (by rfl) ⟨1243386, by rfl⟩ : syracuseStep 3315697 = 2486773) B2486773
theorem B17683717 : Blo 2179435 17683717 := bstep (se 4 (by rfl) ⟨1657848, by rfl⟩ : syracuseStep 17683717 = 3315697) B3315697
theorem B23578289 : Blo 2179435 23578289 := bstep (se 2 (by rfl) ⟨8841858, by rfl⟩ : syracuseStep 23578289 = 17683717) B17683717
theorem B15718859 : Blo 2179435 15718859 := bstep (se 1 (by rfl) ⟨11789144, by rfl⟩ : syracuseStep 15718859 = 23578289) B23578289
theorem B10479239 : Blo 2179435 10479239 := bstep (se 1 (by rfl) ⟨7859429, by rfl⟩ : syracuseStep 10479239 = 15718859) B15718859
theorem B6986159 : Blo 2179435 6986159 := bstep (se 1 (by rfl) ⟨5239619, by rfl⟩ : syracuseStep 6986159 = 10479239) B10479239
theorem B4657439 : Blo 2179435 4657439 := bstep (se 1 (by rfl) ⟨3493079, by rfl⟩ : syracuseStep 4657439 = 6986159) B6986159
theorem B12419837 : Blo 2179435 12419837 := bstep (se 3 (by rfl) ⟨2328719, by rfl⟩ : syracuseStep 12419837 = 4657439) B4657439
theorem B8279891 : Blo 2179435 8279891 := bstep (se 1 (by rfl) ⟨6209918, by rfl⟩ : syracuseStep 8279891 = 12419837) B12419837
theorem B5519927 : Blo 2179435 5519927 := bstep (se 1 (by rfl) ⟨4139945, by rfl⟩ : syracuseStep 5519927 = 8279891) B8279891
theorem B3679951 : Blo 2179435 3679951 := bstep (se 1 (by rfl) ⟨2759963, by rfl⟩ : syracuseStep 3679951 = 5519927) B5519927
theorem B4906601 : Blo 2179435 4906601 := bstep (se 2 (by rfl) ⟨1839975, by rfl⟩ : syracuseStep 4906601 = 3679951) B3679951
theorem B3271067 : Blo 2179435 3271067 := bstep (se 1 (by rfl) ⟨2453300, by rfl⟩ : syracuseStep 3271067 = 4906601) B4906601
theorem B2180711 : Blo 2179435 2180711 := bstep (se 1 (by rfl) ⟨1635533, by rfl⟩ : syracuseStep 2180711 = 3271067) B3271067
theorem B2453305 : Blo 2179435 2453305 := bbase (se 2 (by rfl) ⟨919989, by rfl⟩ : syracuseStep 2453305 = 1839979) (by norm_num)
theorem B3271073 : Blo 2179435 3271073 := bstep (se 2 (by rfl) ⟨1226652, by rfl⟩ : syracuseStep 3271073 = 2453305) B2453305
theorem B2180715 : Blo 2179435 2180715 := bstep (se 1 (by rfl) ⟨1635536, by rfl⟩ : syracuseStep 2180715 = 3271073) B3271073
theorem B6209941 : Blo 2179435 6209941 := bbase (se 6 (by rfl) ⟨145545, by rfl⟩ : syracuseStep 6209941 = 291091) (by norm_num)
theorem B8279921 : Blo 2179435 8279921 := bstep (se 2 (by rfl) ⟨3104970, by rfl⟩ : syracuseStep 8279921 = 6209941) B6209941
theorem B5519947 : Blo 2179435 5519947 := bstep (se 1 (by rfl) ⟨4139960, by rfl⟩ : syracuseStep 5519947 = 8279921) B8279921
theorem B7359929 : Blo 2179435 7359929 := bstep (se 2 (by rfl) ⟨2759973, by rfl⟩ : syracuseStep 7359929 = 5519947) B5519947
theorem B4906619 : Blo 2179435 4906619 := bstep (se 1 (by rfl) ⟨3679964, by rfl⟩ : syracuseStep 4906619 = 7359929) B7359929
theorem B3271079 : Blo 2179435 3271079 := bstep (se 1 (by rfl) ⟨2453309, by rfl⟩ : syracuseStep 3271079 = 4906619) B4906619
theorem B2180719 : Blo 2179435 2180719 := bstep (se 1 (by rfl) ⟨1635539, by rfl⟩ : syracuseStep 2180719 = 3271079) B3271079
theorem B3271085 : Blo 2179435 3271085 := bbase (se 3 (by rfl) ⟨613328, by rfl⟩ : syracuseStep 3271085 = 1226657) (by norm_num)
theorem B2180723 : Blo 2179435 2180723 := bstep (se 1 (by rfl) ⟨1635542, by rfl⟩ : syracuseStep 2180723 = 3271085) B3271085
theorem B4906637 : Blo 2179435 4906637 := bbase (se 3 (by rfl) ⟨919994, by rfl⟩ : syracuseStep 4906637 = 1839989) (by norm_num)
theorem B3271091 : Blo 2179435 3271091 := bstep (se 1 (by rfl) ⟨2453318, by rfl⟩ : syracuseStep 3271091 = 4906637) B4906637
theorem B2180727 : Blo 2179435 2180727 := bstep (se 1 (by rfl) ⟨1635545, by rfl⟩ : syracuseStep 2180727 = 3271091) B3271091
theorem B2759989 : Blo 2179435 2759989 := bbase (se 5 (by rfl) ⟨129374, by rfl⟩ : syracuseStep 2759989 = 258749) (by norm_num)
theorem B3679985 : Blo 2179435 3679985 := bstep (se 2 (by rfl) ⟨1379994, by rfl⟩ : syracuseStep 3679985 = 2759989) B2759989
theorem B2453323 : Blo 2179435 2453323 := bstep (se 1 (by rfl) ⟨1839992, by rfl⟩ : syracuseStep 2453323 = 3679985) B3679985
theorem B3271097 : Blo 2179435 3271097 := bstep (se 2 (by rfl) ⟨1226661, by rfl⟩ : syracuseStep 3271097 = 2453323) B2453323
theorem B2180731 : Blo 2179435 2180731 := bstep (se 1 (by rfl) ⟨1635548, by rfl⟩ : syracuseStep 2180731 = 3271097) B3271097
theorem B8392949 : Blo 2179435 8392949 := bbase (se 5 (by rfl) ⟨393419, by rfl⟩ : syracuseStep 8392949 = 786839) (by norm_num)
theorem B5595299 : Blo 2179435 5595299 := bstep (se 1 (by rfl) ⟨4196474, by rfl⟩ : syracuseStep 5595299 = 8392949) B8392949
theorem B59683189 : Blo 2179435 59683189 := bstep (se 5 (by rfl) ⟨2797649, by rfl⟩ : syracuseStep 59683189 = 5595299) B5595299
theorem B79577585 : Blo 2179435 79577585 := bstep (se 2 (by rfl) ⟨29841594, by rfl⟩ : syracuseStep 79577585 = 59683189) B59683189
theorem B53051723 : Blo 2179435 53051723 := bstep (se 1 (by rfl) ⟨39788792, by rfl⟩ : syracuseStep 53051723 = 79577585) B79577585
theorem B35367815 : Blo 2179435 35367815 := bstep (se 1 (by rfl) ⟨26525861, by rfl⟩ : syracuseStep 35367815 = 53051723) B53051723
theorem B23578543 : Blo 2179435 23578543 := bstep (se 1 (by rfl) ⟨17683907, by rfl⟩ : syracuseStep 23578543 = 35367815) B35367815
theorem B31438057 : Blo 2179435 31438057 := bstep (se 2 (by rfl) ⟨11789271, by rfl⟩ : syracuseStep 31438057 = 23578543) B23578543
theorem B41917409 : Blo 2179435 41917409 := bstep (se 2 (by rfl) ⟨15719028, by rfl⟩ : syracuseStep 41917409 = 31438057) B31438057
theorem B27944939 : Blo 2179435 27944939 := bstep (se 1 (by rfl) ⟨20958704, by rfl⟩ : syracuseStep 27944939 = 41917409) B41917409
theorem B18629959 : Blo 2179435 18629959 := bstep (se 1 (by rfl) ⟨13972469, by rfl⟩ : syracuseStep 18629959 = 27944939) B27944939
theorem B24839945 : Blo 2179435 24839945 := bstep (se 2 (by rfl) ⟨9314979, by rfl⟩ : syracuseStep 24839945 = 18629959) B18629959
theorem B16559963 : Blo 2179435 16559963 := bstep (se 1 (by rfl) ⟨12419972, by rfl⟩ : syracuseStep 16559963 = 24839945) B24839945
theorem B11039975 : Blo 2179435 11039975 := bstep (se 1 (by rfl) ⟨8279981, by rfl⟩ : syracuseStep 11039975 = 16559963) B16559963
theorem B7359983 : Blo 2179435 7359983 := bstep (se 1 (by rfl) ⟨5519987, by rfl⟩ : syracuseStep 7359983 = 11039975) B11039975
theorem B4906655 : Blo 2179435 4906655 := bstep (se 1 (by rfl) ⟨3679991, by rfl⟩ : syracuseStep 4906655 = 7359983) B7359983
theorem B3271103 : Blo 2179435 3271103 := bstep (se 1 (by rfl) ⟨2453327, by rfl⟩ : syracuseStep 3271103 = 4906655) B4906655
theorem B2180735 : Blo 2179435 2180735 := bstep (se 1 (by rfl) ⟨1635551, by rfl⟩ : syracuseStep 2180735 = 3271103) B3271103
theorem B3271109 : Blo 2179435 3271109 := bbase (se 4 (by rfl) ⟨306666, by rfl⟩ : syracuseStep 3271109 = 613333) (by norm_num)
theorem B2180739 : Blo 2179435 2180739 := bstep (se 1 (by rfl) ⟨1635554, by rfl⟩ : syracuseStep 2180739 = 3271109) B3271109
theorem B3680005 : Blo 2179435 3680005 := bbase (se 4 (by rfl) ⟨345000, by rfl⟩ : syracuseStep 3680005 = 690001) (by norm_num)
theorem B4906673 : Blo 2179435 4906673 := bstep (se 2 (by rfl) ⟨1840002, by rfl⟩ : syracuseStep 4906673 = 3680005) B3680005
theorem B3271115 : Blo 2179435 3271115 := bstep (se 1 (by rfl) ⟨2453336, by rfl⟩ : syracuseStep 3271115 = 4906673) B4906673
theorem B2180743 : Blo 2179435 2180743 := bstep (se 1 (by rfl) ⟨1635557, by rfl⟩ : syracuseStep 2180743 = 3271115) B3271115
theorem B2453341 : Blo 2179435 2453341 := bbase (se 3 (by rfl) ⟨460001, by rfl⟩ : syracuseStep 2453341 = 920003) (by norm_num)
theorem B3271121 : Blo 2179435 3271121 := bstep (se 2 (by rfl) ⟨1226670, by rfl⟩ : syracuseStep 3271121 = 2453341) B2453341
theorem B2180747 : Blo 2179435 2180747 := bstep (se 1 (by rfl) ⟨1635560, by rfl⟩ : syracuseStep 2180747 = 3271121) B3271121
theorem B7360037 : Blo 2179435 7360037 := bbase (se 4 (by rfl) ⟨690003, by rfl⟩ : syracuseStep 7360037 = 1380007) (by norm_num)
theorem B4906691 : Blo 2179435 4906691 := bstep (se 1 (by rfl) ⟨3680018, by rfl⟩ : syracuseStep 4906691 = 7360037) B7360037
theorem B3271127 : Blo 2179435 3271127 := bstep (se 1 (by rfl) ⟨2453345, by rfl⟩ : syracuseStep 3271127 = 4906691) B4906691
theorem B2180751 : Blo 2179435 2180751 := bstep (se 1 (by rfl) ⟨1635563, by rfl⟩ : syracuseStep 2180751 = 3271127) B3271127
theorem B3271133 : Blo 2179435 3271133 := bbase (se 3 (by rfl) ⟨613337, by rfl⟩ : syracuseStep 3271133 = 1226675) (by norm_num)
theorem B2180755 : Blo 2179435 2180755 := bstep (se 1 (by rfl) ⟨1635566, by rfl⟩ : syracuseStep 2180755 = 3271133) B3271133
theorem B4906709 : Blo 2179435 4906709 := bbase (se 7 (by rfl) ⟨57500, by rfl⟩ : syracuseStep 4906709 = 115001) (by norm_num)
theorem B3271139 : Blo 2179435 3271139 := bstep (se 1 (by rfl) ⟨2453354, by rfl⟩ : syracuseStep 3271139 = 4906709) B4906709
theorem B2180759 : Blo 2179435 2180759 := bstep (se 1 (by rfl) ⟨1635569, by rfl⟩ : syracuseStep 2180759 = 3271139) B3271139
theorem B2947357 : Blo 2179435 2947357 := bbase (se 3 (by rfl) ⟨552629, by rfl⟩ : syracuseStep 2947357 = 1105259) (by norm_num)
theorem B3929809 : Blo 2179435 3929809 := bstep (se 2 (by rfl) ⟨1473678, by rfl⟩ : syracuseStep 3929809 = 2947357) B2947357
theorem B5239745 : Blo 2179435 5239745 := bstep (se 2 (by rfl) ⟨1964904, by rfl⟩ : syracuseStep 5239745 = 3929809) B3929809
theorem B3493163 : Blo 2179435 3493163 := bstep (se 1 (by rfl) ⟨2619872, by rfl⟩ : syracuseStep 3493163 = 5239745) B5239745
theorem B9315101 : Blo 2179435 9315101 := bstep (se 3 (by rfl) ⟨1746581, by rfl⟩ : syracuseStep 9315101 = 3493163) B3493163
theorem B6210067 : Blo 2179435 6210067 := bstep (se 1 (by rfl) ⟨4657550, by rfl⟩ : syracuseStep 6210067 = 9315101) B9315101
theorem B8280089 : Blo 2179435 8280089 := bstep (se 2 (by rfl) ⟨3105033, by rfl⟩ : syracuseStep 8280089 = 6210067) B6210067
theorem B5520059 : Blo 2179435 5520059 := bstep (se 1 (by rfl) ⟨4140044, by rfl⟩ : syracuseStep 5520059 = 8280089) B8280089
theorem B3680039 : Blo 2179435 3680039 := bstep (se 1 (by rfl) ⟨2760029, by rfl⟩ : syracuseStep 3680039 = 5520059) B5520059
theorem B2453359 : Blo 2179435 2453359 := bstep (se 1 (by rfl) ⟨1840019, by rfl⟩ : syracuseStep 2453359 = 3680039) B3680039
theorem B3271145 : Blo 2179435 3271145 := bstep (se 2 (by rfl) ⟨1226679, by rfl⟩ : syracuseStep 3271145 = 2453359) B2453359
theorem B2180763 : Blo 2179435 2180763 := bstep (se 1 (by rfl) ⟨1635572, by rfl⟩ : syracuseStep 2180763 = 3271145) B3271145
theorem B8842085 : Blo 2179435 8842085 := bbase (se 4 (by rfl) ⟨828945, by rfl⟩ : syracuseStep 8842085 = 1657891) (by norm_num)
theorem B5894723 : Blo 2179435 5894723 := bstep (se 1 (by rfl) ⟨4421042, by rfl⟩ : syracuseStep 5894723 = 8842085) B8842085
theorem B3929815 : Blo 2179435 3929815 := bstep (se 1 (by rfl) ⟨2947361, by rfl⟩ : syracuseStep 3929815 = 5894723) B5894723
theorem B20959013 : Blo 2179435 20959013 := bstep (se 4 (by rfl) ⟨1964907, by rfl⟩ : syracuseStep 20959013 = 3929815) B3929815
theorem B13972675 : Blo 2179435 13972675 := bstep (se 1 (by rfl) ⟨10479506, by rfl⟩ : syracuseStep 13972675 = 20959013) B20959013
theorem B18630233 : Blo 2179435 18630233 := bstep (se 2 (by rfl) ⟨6986337, by rfl⟩ : syracuseStep 18630233 = 13972675) B13972675
theorem B12420155 : Blo 2179435 12420155 := bstep (se 1 (by rfl) ⟨9315116, by rfl⟩ : syracuseStep 12420155 = 18630233) B18630233
theorem B8280103 : Blo 2179435 8280103 := bstep (se 1 (by rfl) ⟨6210077, by rfl⟩ : syracuseStep 8280103 = 12420155) B12420155
theorem B11040137 : Blo 2179435 11040137 := bstep (se 2 (by rfl) ⟨4140051, by rfl⟩ : syracuseStep 11040137 = 8280103) B8280103
theorem B7360091 : Blo 2179435 7360091 := bstep (se 1 (by rfl) ⟨5520068, by rfl⟩ : syracuseStep 7360091 = 11040137) B11040137
theorem B4906727 : Blo 2179435 4906727 := bstep (se 1 (by rfl) ⟨3680045, by rfl⟩ : syracuseStep 4906727 = 7360091) B7360091
theorem B3271151 : Blo 2179435 3271151 := bstep (se 1 (by rfl) ⟨2453363, by rfl⟩ : syracuseStep 3271151 = 4906727) B4906727
theorem B2180767 : Blo 2179435 2180767 := bstep (se 1 (by rfl) ⟨1635575, by rfl⟩ : syracuseStep 2180767 = 3271151) B3271151
theorem B3271157 : Blo 2179435 3271157 := bbase (se 5 (by rfl) ⟨153335, by rfl⟩ : syracuseStep 3271157 = 306671) (by norm_num)
theorem B2180771 : Blo 2179435 2180771 := bstep (se 1 (by rfl) ⟨1635578, by rfl⟩ : syracuseStep 2180771 = 3271157) B3271157
theorem B6210101 : Blo 2179435 6210101 := bbase (se 5 (by rfl) ⟨291098, by rfl⟩ : syracuseStep 6210101 = 582197) (by norm_num)
theorem B4140067 : Blo 2179435 4140067 := bstep (se 1 (by rfl) ⟨3105050, by rfl⟩ : syracuseStep 4140067 = 6210101) B6210101
theorem B5520089 : Blo 2179435 5520089 := bstep (se 2 (by rfl) ⟨2070033, by rfl⟩ : syracuseStep 5520089 = 4140067) B4140067
theorem B3680059 : Blo 2179435 3680059 := bstep (se 1 (by rfl) ⟨2760044, by rfl⟩ : syracuseStep 3680059 = 5520089) B5520089
theorem B4906745 : Blo 2179435 4906745 := bstep (se 2 (by rfl) ⟨1840029, by rfl⟩ : syracuseStep 4906745 = 3680059) B3680059
theorem B3271163 : Blo 2179435 3271163 := bstep (se 1 (by rfl) ⟨2453372, by rfl⟩ : syracuseStep 3271163 = 4906745) B4906745
theorem B2180775 : Blo 2179435 2180775 := bstep (se 1 (by rfl) ⟨1635581, by rfl⟩ : syracuseStep 2180775 = 3271163) B3271163
theorem B2453377 : Blo 2179435 2453377 := bbase (se 2 (by rfl) ⟨920016, by rfl⟩ : syracuseStep 2453377 = 1840033) (by norm_num)
theorem B3271169 : Blo 2179435 3271169 := bstep (se 2 (by rfl) ⟨1226688, by rfl⟩ : syracuseStep 3271169 = 2453377) B2453377
theorem B2180779 : Blo 2179435 2180779 := bstep (se 1 (by rfl) ⟨1635584, by rfl⟩ : syracuseStep 2180779 = 3271169) B3271169
theorem B5520109 : Blo 2179435 5520109 := bbase (se 3 (by rfl) ⟨1035020, by rfl⟩ : syracuseStep 5520109 = 2070041) (by norm_num)
theorem B7360145 : Blo 2179435 7360145 := bstep (se 2 (by rfl) ⟨2760054, by rfl⟩ : syracuseStep 7360145 = 5520109) B5520109
theorem B4906763 : Blo 2179435 4906763 := bstep (se 1 (by rfl) ⟨3680072, by rfl⟩ : syracuseStep 4906763 = 7360145) B7360145
theorem B3271175 : Blo 2179435 3271175 := bstep (se 1 (by rfl) ⟨2453381, by rfl⟩ : syracuseStep 3271175 = 4906763) B4906763
theorem B2180783 : Blo 2179435 2180783 := bstep (se 1 (by rfl) ⟨1635587, by rfl⟩ : syracuseStep 2180783 = 3271175) B3271175
theorem B3271181 : Blo 2179435 3271181 := bbase (se 3 (by rfl) ⟨613346, by rfl⟩ : syracuseStep 3271181 = 1226693) (by norm_num)
theorem B2180787 : Blo 2179435 2180787 := bstep (se 1 (by rfl) ⟨1635590, by rfl⟩ : syracuseStep 2180787 = 3271181) B3271181
theorem B4906781 : Blo 2179435 4906781 := bbase (se 3 (by rfl) ⟨920021, by rfl⟩ : syracuseStep 4906781 = 1840043) (by norm_num)
theorem B3271187 : Blo 2179435 3271187 := bstep (se 1 (by rfl) ⟨2453390, by rfl⟩ : syracuseStep 3271187 = 4906781) B4906781
theorem B2180791 : Blo 2179435 2180791 := bstep (se 1 (by rfl) ⟨1635593, by rfl⟩ : syracuseStep 2180791 = 3271187) B3271187
theorem B3680093 : Blo 2179435 3680093 := bbase (se 3 (by rfl) ⟨690017, by rfl⟩ : syracuseStep 3680093 = 1380035) (by norm_num)
theorem B2453395 : Blo 2179435 2453395 := bstep (se 1 (by rfl) ⟨1840046, by rfl⟩ : syracuseStep 2453395 = 3680093) B3680093
theorem B3271193 : Blo 2179435 3271193 := bstep (se 2 (by rfl) ⟨1226697, by rfl⟩ : syracuseStep 3271193 = 2453395) B2453395
theorem B2180795 : Blo 2179435 2180795 := bstep (se 1 (by rfl) ⟨1635596, by rfl⟩ : syracuseStep 2180795 = 3271193) B3271193
theorem B9315253 : Blo 2179435 9315253 := bbase (se 5 (by rfl) ⟨436652, by rfl⟩ : syracuseStep 9315253 = 873305) (by norm_num)
theorem B12420337 : Blo 2179435 12420337 := bstep (se 2 (by rfl) ⟨4657626, by rfl⟩ : syracuseStep 12420337 = 9315253) B9315253
theorem B16560449 : Blo 2179435 16560449 := bstep (se 2 (by rfl) ⟨6210168, by rfl⟩ : syracuseStep 16560449 = 12420337) B12420337
theorem B11040299 : Blo 2179435 11040299 := bstep (se 1 (by rfl) ⟨8280224, by rfl⟩ : syracuseStep 11040299 = 16560449) B16560449
theorem B7360199 : Blo 2179435 7360199 := bstep (se 1 (by rfl) ⟨5520149, by rfl⟩ : syracuseStep 7360199 = 11040299) B11040299
theorem B4906799 : Blo 2179435 4906799 := bstep (se 1 (by rfl) ⟨3680099, by rfl⟩ : syracuseStep 4906799 = 7360199) B7360199
theorem B3271199 : Blo 2179435 3271199 := bstep (se 1 (by rfl) ⟨2453399, by rfl⟩ : syracuseStep 3271199 = 4906799) B4906799
theorem B2180799 : Blo 2179435 2180799 := bstep (se 1 (by rfl) ⟨1635599, by rfl⟩ : syracuseStep 2180799 = 3271199) B3271199
theorem B3271205 : Blo 2179435 3271205 := bbase (se 4 (by rfl) ⟨306675, by rfl⟩ : syracuseStep 3271205 = 613351) (by norm_num)
theorem B2180803 : Blo 2179435 2180803 := bstep (se 1 (by rfl) ⟨1635602, by rfl⟩ : syracuseStep 2180803 = 3271205) B3271205
theorem B2760085 : Blo 2179435 2760085 := bbase (se 6 (by rfl) ⟨64689, by rfl⟩ : syracuseStep 2760085 = 129379) (by norm_num)
theorem B3680113 : Blo 2179435 3680113 := bstep (se 2 (by rfl) ⟨1380042, by rfl⟩ : syracuseStep 3680113 = 2760085) B2760085
theorem B4906817 : Blo 2179435 4906817 := bstep (se 2 (by rfl) ⟨1840056, by rfl⟩ : syracuseStep 4906817 = 3680113) B3680113
theorem B3271211 : Blo 2179435 3271211 := bstep (se 1 (by rfl) ⟨2453408, by rfl⟩ : syracuseStep 3271211 = 4906817) B4906817
theorem B2180807 : Blo 2179435 2180807 := bstep (se 1 (by rfl) ⟨1635605, by rfl⟩ : syracuseStep 2180807 = 3271211) B3271211
theorem B2453413 : Blo 2179435 2453413 := bbase (se 4 (by rfl) ⟨230007, by rfl⟩ : syracuseStep 2453413 = 460015) (by norm_num)
theorem B3271217 : Blo 2179435 3271217 := bstep (se 2 (by rfl) ⟨1226706, by rfl⟩ : syracuseStep 3271217 = 2453413) B2453413
theorem B2180811 : Blo 2179435 2180811 := bstep (se 1 (by rfl) ⟨1635608, by rfl⟩ : syracuseStep 2180811 = 3271217) B3271217
theorem B11191013 : Blo 2179435 11191013 := bbase (se 4 (by rfl) ⟨1049157, by rfl⟩ : syracuseStep 11191013 = 2098315) (by norm_num)
theorem B7460675 : Blo 2179435 7460675 := bstep (se 1 (by rfl) ⟨5595506, by rfl⟩ : syracuseStep 7460675 = 11191013) B11191013
theorem B4973783 : Blo 2179435 4973783 := bstep (se 1 (by rfl) ⟨3730337, by rfl⟩ : syracuseStep 4973783 = 7460675) B7460675
theorem B13263421 : Blo 2179435 13263421 := bstep (se 3 (by rfl) ⟨2486891, by rfl⟩ : syracuseStep 13263421 = 4973783) B4973783
theorem B17684561 : Blo 2179435 17684561 := bstep (se 2 (by rfl) ⟨6631710, by rfl⟩ : syracuseStep 17684561 = 13263421) B13263421
theorem B11789707 : Blo 2179435 11789707 := bstep (se 1 (by rfl) ⟨8842280, by rfl⟩ : syracuseStep 11789707 = 17684561) B17684561
theorem B15719609 : Blo 2179435 15719609 := bstep (se 2 (by rfl) ⟨5894853, by rfl⟩ : syracuseStep 15719609 = 11789707) B11789707
theorem B10479739 : Blo 2179435 10479739 := bstep (se 1 (by rfl) ⟨7859804, by rfl⟩ : syracuseStep 10479739 = 15719609) B15719609
theorem B13972985 : Blo 2179435 13972985 := bstep (se 2 (by rfl) ⟨5239869, by rfl⟩ : syracuseStep 13972985 = 10479739) B10479739
theorem B9315323 : Blo 2179435 9315323 := bstep (se 1 (by rfl) ⟨6986492, by rfl⟩ : syracuseStep 9315323 = 13972985) B13972985
theorem B6210215 : Blo 2179435 6210215 := bstep (se 1 (by rfl) ⟨4657661, by rfl⟩ : syracuseStep 6210215 = 9315323) B9315323
theorem B4140143 : Blo 2179435 4140143 := bstep (se 1 (by rfl) ⟨3105107, by rfl⟩ : syracuseStep 4140143 = 6210215) B6210215
theorem B2760095 : Blo 2179435 2760095 := bstep (se 1 (by rfl) ⟨2070071, by rfl⟩ : syracuseStep 2760095 = 4140143) B4140143
theorem B7360253 : Blo 2179435 7360253 := bstep (se 3 (by rfl) ⟨1380047, by rfl⟩ : syracuseStep 7360253 = 2760095) B2760095
theorem B4906835 : Blo 2179435 4906835 := bstep (se 1 (by rfl) ⟨3680126, by rfl⟩ : syracuseStep 4906835 = 7360253) B7360253
theorem B3271223 : Blo 2179435 3271223 := bstep (se 1 (by rfl) ⟨2453417, by rfl⟩ : syracuseStep 3271223 = 4906835) B4906835
theorem B2180815 : Blo 2179435 2180815 := bstep (se 1 (by rfl) ⟨1635611, by rfl⟩ : syracuseStep 2180815 = 3271223) B3271223
theorem B3271229 : Blo 2179435 3271229 := bbase (se 3 (by rfl) ⟨613355, by rfl⟩ : syracuseStep 3271229 = 1226711) (by norm_num)
theorem B2180819 : Blo 2179435 2180819 := bstep (se 1 (by rfl) ⟨1635614, by rfl⟩ : syracuseStep 2180819 = 3271229) B3271229
theorem B4906853 : Blo 2179435 4906853 := bbase (se 4 (by rfl) ⟨460017, by rfl⟩ : syracuseStep 4906853 = 920035) (by norm_num)
theorem B3271235 : Blo 2179435 3271235 := bstep (se 1 (by rfl) ⟨2453426, by rfl⟩ : syracuseStep 3271235 = 4906853) B4906853
theorem B2180823 : Blo 2179435 2180823 := bstep (se 1 (by rfl) ⟨1635617, by rfl⟩ : syracuseStep 2180823 = 3271235) B3271235
theorem B5520221 : Blo 2179435 5520221 := bbase (se 3 (by rfl) ⟨1035041, by rfl⟩ : syracuseStep 5520221 = 2070083) (by norm_num)
theorem B3680147 : Blo 2179435 3680147 := bstep (se 1 (by rfl) ⟨2760110, by rfl⟩ : syracuseStep 3680147 = 5520221) B5520221
theorem B2453431 : Blo 2179435 2453431 := bstep (se 1 (by rfl) ⟨1840073, by rfl⟩ : syracuseStep 2453431 = 3680147) B3680147
theorem B3271241 : Blo 2179435 3271241 := bstep (se 2 (by rfl) ⟨1226715, by rfl⟩ : syracuseStep 3271241 = 2453431) B2453431
theorem B2180827 : Blo 2179435 2180827 := bstep (se 1 (by rfl) ⟨1635620, by rfl⟩ : syracuseStep 2180827 = 3271241) B3271241
theorem B4140173 : Blo 2179435 4140173 := bbase (se 3 (by rfl) ⟨776282, by rfl⟩ : syracuseStep 4140173 = 1552565) (by norm_num)
theorem B11040461 : Blo 2179435 11040461 := bstep (se 3 (by rfl) ⟨2070086, by rfl⟩ : syracuseStep 11040461 = 4140173) B4140173
theorem B7360307 : Blo 2179435 7360307 := bstep (se 1 (by rfl) ⟨5520230, by rfl⟩ : syracuseStep 7360307 = 11040461) B11040461
theorem B4906871 : Blo 2179435 4906871 := bstep (se 1 (by rfl) ⟨3680153, by rfl⟩ : syracuseStep 4906871 = 7360307) B7360307
theorem B3271247 : Blo 2179435 3271247 := bstep (se 1 (by rfl) ⟨2453435, by rfl⟩ : syracuseStep 3271247 = 4906871) B4906871
theorem B2180831 : Blo 2179435 2180831 := bstep (se 1 (by rfl) ⟨1635623, by rfl⟩ : syracuseStep 2180831 = 3271247) B3271247
theorem B3271253 : Blo 2179435 3271253 := bbase (se 8 (by rfl) ⟨19167, by rfl⟩ : syracuseStep 3271253 = 38335) (by norm_num)
theorem B2180835 : Blo 2179435 2180835 := bstep (se 1 (by rfl) ⟨1635626, by rfl⟩ : syracuseStep 2180835 = 3271253) B3271253
theorem B4421189 : Blo 2179435 4421189 := bbase (se 4 (by rfl) ⟨414486, by rfl⟩ : syracuseStep 4421189 = 828973) (by norm_num)
theorem B11789837 : Blo 2179435 11789837 := bstep (se 3 (by rfl) ⟨2210594, by rfl⟩ : syracuseStep 11789837 = 4421189) B4421189
theorem B7859891 : Blo 2179435 7859891 := bstep (se 1 (by rfl) ⟨5894918, by rfl⟩ : syracuseStep 7859891 = 11789837) B11789837
theorem B5239927 : Blo 2179435 5239927 := bstep (se 1 (by rfl) ⟨3929945, by rfl⟩ : syracuseStep 5239927 = 7859891) B7859891
theorem B6986569 : Blo 2179435 6986569 := bstep (se 2 (by rfl) ⟨2619963, by rfl⟩ : syracuseStep 6986569 = 5239927) B5239927
theorem B9315425 : Blo 2179435 9315425 := bstep (se 2 (by rfl) ⟨3493284, by rfl⟩ : syracuseStep 9315425 = 6986569) B6986569
theorem B6210283 : Blo 2179435 6210283 := bstep (se 1 (by rfl) ⟨4657712, by rfl⟩ : syracuseStep 6210283 = 9315425) B9315425
theorem B8280377 : Blo 2179435 8280377 := bstep (se 2 (by rfl) ⟨3105141, by rfl⟩ : syracuseStep 8280377 = 6210283) B6210283
theorem B5520251 : Blo 2179435 5520251 := bstep (se 1 (by rfl) ⟨4140188, by rfl⟩ : syracuseStep 5520251 = 8280377) B8280377
theorem B3680167 : Blo 2179435 3680167 := bstep (se 1 (by rfl) ⟨2760125, by rfl⟩ : syracuseStep 3680167 = 5520251) B5520251
theorem B4906889 : Blo 2179435 4906889 := bstep (se 2 (by rfl) ⟨1840083, by rfl⟩ : syracuseStep 4906889 = 3680167) B3680167
theorem B3271259 : Blo 2179435 3271259 := bstep (se 1 (by rfl) ⟨2453444, by rfl⟩ : syracuseStep 3271259 = 4906889) B4906889
theorem B2180839 : Blo 2179435 2180839 := bstep (se 1 (by rfl) ⟨1635629, by rfl⟩ : syracuseStep 2180839 = 3271259) B3271259
theorem B2453449 : Blo 2179435 2453449 := bbase (se 2 (by rfl) ⟨920043, by rfl⟩ : syracuseStep 2453449 = 1840087) (by norm_num)
theorem B3271265 : Blo 2179435 3271265 := bstep (se 2 (by rfl) ⟨1226724, by rfl⟩ : syracuseStep 3271265 = 2453449) B2453449
theorem B2180843 : Blo 2179435 2180843 := bstep (se 1 (by rfl) ⟨1635632, by rfl⟩ : syracuseStep 2180843 = 3271265) B3271265
theorem B2619973 : Blo 2179435 2619973 := bbase (se 4 (by rfl) ⟨245622, by rfl⟩ : syracuseStep 2619973 = 491245) (by norm_num)
theorem B3493297 : Blo 2179435 3493297 := bstep (se 2 (by rfl) ⟨1309986, by rfl⟩ : syracuseStep 3493297 = 2619973) B2619973
theorem B18630917 : Blo 2179435 18630917 := bstep (se 4 (by rfl) ⟨1746648, by rfl⟩ : syracuseStep 18630917 = 3493297) B3493297
theorem B12420611 : Blo 2179435 12420611 := bstep (se 1 (by rfl) ⟨9315458, by rfl⟩ : syracuseStep 12420611 = 18630917) B18630917
theorem B8280407 : Blo 2179435 8280407 := bstep (se 1 (by rfl) ⟨6210305, by rfl⟩ : syracuseStep 8280407 = 12420611) B12420611
theorem B5520271 : Blo 2179435 5520271 := bstep (se 1 (by rfl) ⟨4140203, by rfl⟩ : syracuseStep 5520271 = 8280407) B8280407
theorem B7360361 : Blo 2179435 7360361 := bstep (se 2 (by rfl) ⟨2760135, by rfl⟩ : syracuseStep 7360361 = 5520271) B5520271
theorem B4906907 : Blo 2179435 4906907 := bstep (se 1 (by rfl) ⟨3680180, by rfl⟩ : syracuseStep 4906907 = 7360361) B7360361
theorem B3271271 : Blo 2179435 3271271 := bstep (se 1 (by rfl) ⟨2453453, by rfl⟩ : syracuseStep 3271271 = 4906907) B4906907
theorem B2180847 : Blo 2179435 2180847 := bstep (se 1 (by rfl) ⟨1635635, by rfl⟩ : syracuseStep 2180847 = 3271271) B3271271
theorem B3271277 : Blo 2179435 3271277 := bbase (se 3 (by rfl) ⟨613364, by rfl⟩ : syracuseStep 3271277 = 1226729) (by norm_num)
theorem B2180851 : Blo 2179435 2180851 := bstep (se 1 (by rfl) ⟨1635638, by rfl⟩ : syracuseStep 2180851 = 3271277) B3271277
theorem B4906925 : Blo 2179435 4906925 := bbase (se 3 (by rfl) ⟨920048, by rfl⟩ : syracuseStep 4906925 = 1840097) (by norm_num)
theorem B3271283 : Blo 2179435 3271283 := bstep (se 1 (by rfl) ⟨2453462, by rfl⟩ : syracuseStep 3271283 = 4906925) B4906925
theorem B2180855 : Blo 2179435 2180855 := bstep (se 1 (by rfl) ⟨1635641, by rfl⟩ : syracuseStep 2180855 = 3271283) B3271283
theorem B6210341 : Blo 2179435 6210341 := bbase (se 4 (by rfl) ⟨582219, by rfl⟩ : syracuseStep 6210341 = 1164439) (by norm_num)
theorem B4140227 : Blo 2179435 4140227 := bstep (se 1 (by rfl) ⟨3105170, by rfl⟩ : syracuseStep 4140227 = 6210341) B6210341
theorem B2760151 : Blo 2179435 2760151 := bstep (se 1 (by rfl) ⟨2070113, by rfl⟩ : syracuseStep 2760151 = 4140227) B4140227
theorem B3680201 : Blo 2179435 3680201 := bstep (se 2 (by rfl) ⟨1380075, by rfl⟩ : syracuseStep 3680201 = 2760151) B2760151
theorem B2453467 : Blo 2179435 2453467 := bstep (se 1 (by rfl) ⟨1840100, by rfl⟩ : syracuseStep 2453467 = 3680201) B3680201
theorem B3271289 : Blo 2179435 3271289 := bstep (se 2 (by rfl) ⟨1226733, by rfl⟩ : syracuseStep 3271289 = 2453467) B2453467
theorem B2180859 : Blo 2179435 2180859 := bstep (se 1 (by rfl) ⟨1635644, by rfl⟩ : syracuseStep 2180859 = 3271289) B3271289
theorem B7460837 : Blo 2179435 7460837 := bbase (se 4 (by rfl) ⟨699453, by rfl⟩ : syracuseStep 7460837 = 1398907) (by norm_num)
theorem B4973891 : Blo 2179435 4973891 := bstep (se 1 (by rfl) ⟨3730418, by rfl⟩ : syracuseStep 4973891 = 7460837) B7460837
theorem B53054837 : Blo 2179435 53054837 := bstep (se 5 (by rfl) ⟨2486945, by rfl⟩ : syracuseStep 53054837 = 4973891) B4973891
theorem B35369891 : Blo 2179435 35369891 := bstep (se 1 (by rfl) ⟨26527418, by rfl⟩ : syracuseStep 35369891 = 53054837) B53054837
theorem B23579927 : Blo 2179435 23579927 := bstep (se 1 (by rfl) ⟨17684945, by rfl⟩ : syracuseStep 23579927 = 35369891) B35369891
theorem B15719951 : Blo 2179435 15719951 := bstep (se 1 (by rfl) ⟨11789963, by rfl⟩ : syracuseStep 15719951 = 23579927) B23579927
theorem B41919869 : Blo 2179435 41919869 := bstep (se 3 (by rfl) ⟨7859975, by rfl⟩ : syracuseStep 41919869 = 15719951) B15719951
theorem B27946579 : Blo 2179435 27946579 := bstep (se 1 (by rfl) ⟨20959934, by rfl⟩ : syracuseStep 27946579 = 41919869) B41919869
theorem B37262105 : Blo 2179435 37262105 := bstep (se 2 (by rfl) ⟨13973289, by rfl⟩ : syracuseStep 37262105 = 27946579) B27946579
theorem B24841403 : Blo 2179435 24841403 := bstep (se 1 (by rfl) ⟨18631052, by rfl⟩ : syracuseStep 24841403 = 37262105) B37262105
theorem B16560935 : Blo 2179435 16560935 := bstep (se 1 (by rfl) ⟨12420701, by rfl⟩ : syracuseStep 16560935 = 24841403) B24841403
theorem B11040623 : Blo 2179435 11040623 := bstep (se 1 (by rfl) ⟨8280467, by rfl⟩ : syracuseStep 11040623 = 16560935) B16560935
theorem B7360415 : Blo 2179435 7360415 := bstep (se 1 (by rfl) ⟨5520311, by rfl⟩ : syracuseStep 7360415 = 11040623) B11040623
theorem B4906943 : Blo 2179435 4906943 := bstep (se 1 (by rfl) ⟨3680207, by rfl⟩ : syracuseStep 4906943 = 7360415) B7360415
theorem B3271295 : Blo 2179435 3271295 := bstep (se 1 (by rfl) ⟨2453471, by rfl⟩ : syracuseStep 3271295 = 4906943) B4906943
theorem B2180863 : Blo 2179435 2180863 := bstep (se 1 (by rfl) ⟨1635647, by rfl⟩ : syracuseStep 2180863 = 3271295) B3271295
theorem B3271301 : Blo 2179435 3271301 := bbase (se 4 (by rfl) ⟨306684, by rfl⟩ : syracuseStep 3271301 = 613369) (by norm_num)
theorem B2180867 : Blo 2179435 2180867 := bstep (se 1 (by rfl) ⟨1635650, by rfl⟩ : syracuseStep 2180867 = 3271301) B3271301
theorem B3680221 : Blo 2179435 3680221 := bbase (se 3 (by rfl) ⟨690041, by rfl⟩ : syracuseStep 3680221 = 1380083) (by norm_num)
theorem B4906961 : Blo 2179435 4906961 := bstep (se 2 (by rfl) ⟨1840110, by rfl⟩ : syracuseStep 4906961 = 3680221) B3680221
theorem B3271307 : Blo 2179435 3271307 := bstep (se 1 (by rfl) ⟨2453480, by rfl⟩ : syracuseStep 3271307 = 4906961) B4906961
theorem B2180871 : Blo 2179435 2180871 := bstep (se 1 (by rfl) ⟨1635653, by rfl⟩ : syracuseStep 2180871 = 3271307) B3271307
theorem B2453485 : Blo 2179435 2453485 := bbase (se 3 (by rfl) ⟨460028, by rfl⟩ : syracuseStep 2453485 = 920057) (by norm_num)
theorem B3271313 : Blo 2179435 3271313 := bstep (se 2 (by rfl) ⟨1226742, by rfl⟩ : syracuseStep 3271313 = 2453485) B2453485
theorem B2180875 : Blo 2179435 2180875 := bstep (se 1 (by rfl) ⟨1635656, by rfl⟩ : syracuseStep 2180875 = 3271313) B3271313
theorem B7360469 : Blo 2179435 7360469 := bbase (se 7 (by rfl) ⟨86255, by rfl⟩ : syracuseStep 7360469 = 172511) (by norm_num)
theorem B4906979 : Blo 2179435 4906979 := bstep (se 1 (by rfl) ⟨3680234, by rfl⟩ : syracuseStep 4906979 = 7360469) B7360469
theorem B3271319 : Blo 2179435 3271319 := bstep (se 1 (by rfl) ⟨2453489, by rfl⟩ : syracuseStep 3271319 = 4906979) B4906979
theorem B2180879 : Blo 2179435 2180879 := bstep (se 1 (by rfl) ⟨1635659, by rfl⟩ : syracuseStep 2180879 = 3271319) B3271319
theorem B3271325 : Blo 2179435 3271325 := bbase (se 3 (by rfl) ⟨613373, by rfl⟩ : syracuseStep 3271325 = 1226747) (by norm_num)
theorem B2180883 : Blo 2179435 2180883 := bstep (se 1 (by rfl) ⟨1635662, by rfl⟩ : syracuseStep 2180883 = 3271325) B3271325
theorem B4906997 : Blo 2179435 4906997 := bbase (se 5 (by rfl) ⟨230015, by rfl⟩ : syracuseStep 4906997 = 460031) (by norm_num)
theorem B3271331 : Blo 2179435 3271331 := bstep (se 1 (by rfl) ⟨2453498, by rfl⟩ : syracuseStep 3271331 = 4906997) B4906997
theorem B2180887 : Blo 2179435 2180887 := bstep (se 1 (by rfl) ⟨1635665, by rfl⟩ : syracuseStep 2180887 = 3271331) B3271331
theorem B50361301 : Blo 2179435 50361301 := bbase (se 7 (by rfl) ⟨590171, by rfl⟩ : syracuseStep 50361301 = 1180343) (by norm_num)
theorem B67148401 : Blo 2179435 67148401 := bstep (se 2 (by rfl) ⟨25180650, by rfl⟩ : syracuseStep 67148401 = 50361301) B50361301
theorem B89531201 : Blo 2179435 89531201 := bstep (se 2 (by rfl) ⟨33574200, by rfl⟩ : syracuseStep 89531201 = 67148401) B67148401
theorem B238749869 : Blo 2179435 238749869 := bstep (se 3 (by rfl) ⟨44765600, by rfl⟩ : syracuseStep 238749869 = 89531201) B89531201
theorem B159166579 : Blo 2179435 159166579 := bstep (se 1 (by rfl) ⟨119374934, by rfl⟩ : syracuseStep 159166579 = 238749869) B238749869
theorem B212222105 : Blo 2179435 212222105 := bstep (se 2 (by rfl) ⟨79583289, by rfl⟩ : syracuseStep 212222105 = 159166579) B159166579
theorem B141481403 : Blo 2179435 141481403 := bstep (se 1 (by rfl) ⟨106111052, by rfl⟩ : syracuseStep 141481403 = 212222105) B212222105
theorem B94320935 : Blo 2179435 94320935 := bstep (se 1 (by rfl) ⟨70740701, by rfl⟩ : syracuseStep 94320935 = 141481403) B141481403
theorem B62880623 : Blo 2179435 62880623 := bstep (se 1 (by rfl) ⟨47160467, by rfl⟩ : syracuseStep 62880623 = 94320935) B94320935
theorem B41920415 : Blo 2179435 41920415 := bstep (se 1 (by rfl) ⟨31440311, by rfl⟩ : syracuseStep 41920415 = 62880623) B62880623
theorem B27946943 : Blo 2179435 27946943 := bstep (se 1 (by rfl) ⟨20960207, by rfl⟩ : syracuseStep 27946943 = 41920415) B41920415
theorem B18631295 : Blo 2179435 18631295 := bstep (se 1 (by rfl) ⟨13973471, by rfl⟩ : syracuseStep 18631295 = 27946943) B27946943
theorem B12420863 : Blo 2179435 12420863 := bstep (se 1 (by rfl) ⟨9315647, by rfl⟩ : syracuseStep 12420863 = 18631295) B18631295
theorem B8280575 : Blo 2179435 8280575 := bstep (se 1 (by rfl) ⟨6210431, by rfl⟩ : syracuseStep 8280575 = 12420863) B12420863
theorem B5520383 : Blo 2179435 5520383 := bstep (se 1 (by rfl) ⟨4140287, by rfl⟩ : syracuseStep 5520383 = 8280575) B8280575
theorem B3680255 : Blo 2179435 3680255 := bstep (se 1 (by rfl) ⟨2760191, by rfl⟩ : syracuseStep 3680255 = 5520383) B5520383
theorem B2453503 : Blo 2179435 2453503 := bstep (se 1 (by rfl) ⟨1840127, by rfl⟩ : syracuseStep 2453503 = 3680255) B3680255
theorem B3271337 : Blo 2179435 3271337 := bstep (se 2 (by rfl) ⟨1226751, by rfl⟩ : syracuseStep 3271337 = 2453503) B2453503
theorem B2180891 : Blo 2179435 2180891 := bstep (se 1 (by rfl) ⟨1635668, by rfl⟩ : syracuseStep 2180891 = 3271337) B3271337
theorem B3105221 : Blo 2179435 3105221 := bbase (se 4 (by rfl) ⟨291114, by rfl⟩ : syracuseStep 3105221 = 582229) (by norm_num)
theorem B8280589 : Blo 2179435 8280589 := bstep (se 3 (by rfl) ⟨1552610, by rfl⟩ : syracuseStep 8280589 = 3105221) B3105221
theorem B11040785 : Blo 2179435 11040785 := bstep (se 2 (by rfl) ⟨4140294, by rfl⟩ : syracuseStep 11040785 = 8280589) B8280589
theorem B7360523 : Blo 2179435 7360523 := bstep (se 1 (by rfl) ⟨5520392, by rfl⟩ : syracuseStep 7360523 = 11040785) B11040785
theorem B4907015 : Blo 2179435 4907015 := bstep (se 1 (by rfl) ⟨3680261, by rfl⟩ : syracuseStep 4907015 = 7360523) B7360523
theorem B3271343 : Blo 2179435 3271343 := bstep (se 1 (by rfl) ⟨2453507, by rfl⟩ : syracuseStep 3271343 = 4907015) B4907015
theorem B2180895 : Blo 2179435 2180895 := bstep (se 1 (by rfl) ⟨1635671, by rfl⟩ : syracuseStep 2180895 = 3271343) B3271343
theorem B3271349 : Blo 2179435 3271349 := bbase (se 5 (by rfl) ⟨153344, by rfl⟩ : syracuseStep 3271349 = 306689) (by norm_num)
theorem B2180899 : Blo 2179435 2180899 := bstep (se 1 (by rfl) ⟨1635674, by rfl⟩ : syracuseStep 2180899 = 3271349) B3271349
theorem B5520413 : Blo 2179435 5520413 := bbase (se 3 (by rfl) ⟨1035077, by rfl⟩ : syracuseStep 5520413 = 2070155) (by norm_num)
theorem B3680275 : Blo 2179435 3680275 := bstep (se 1 (by rfl) ⟨2760206, by rfl⟩ : syracuseStep 3680275 = 5520413) B5520413
theorem B4907033 : Blo 2179435 4907033 := bstep (se 2 (by rfl) ⟨1840137, by rfl⟩ : syracuseStep 4907033 = 3680275) B3680275
theorem B3271355 : Blo 2179435 3271355 := bstep (se 1 (by rfl) ⟨2453516, by rfl⟩ : syracuseStep 3271355 = 4907033) B4907033
theorem B2180903 : Blo 2179435 2180903 := bstep (se 1 (by rfl) ⟨1635677, by rfl⟩ : syracuseStep 2180903 = 3271355) B3271355
theorem B2453521 : Blo 2179435 2453521 := bbase (se 2 (by rfl) ⟨920070, by rfl⟩ : syracuseStep 2453521 = 1840141) (by norm_num)
theorem B3271361 : Blo 2179435 3271361 := bstep (se 2 (by rfl) ⟨1226760, by rfl⟩ : syracuseStep 3271361 = 2453521) B2453521
theorem B2180907 : Blo 2179435 2180907 := bstep (se 1 (by rfl) ⟨1635680, by rfl⟩ : syracuseStep 2180907 = 3271361) B3271361
theorem B4140325 : Blo 2179435 4140325 := bbase (se 4 (by rfl) ⟨388155, by rfl⟩ : syracuseStep 4140325 = 776311) (by norm_num)
theorem B5520433 : Blo 2179435 5520433 := bstep (se 2 (by rfl) ⟨2070162, by rfl⟩ : syracuseStep 5520433 = 4140325) B4140325
theorem B7360577 : Blo 2179435 7360577 := bstep (se 2 (by rfl) ⟨2760216, by rfl⟩ : syracuseStep 7360577 = 5520433) B5520433
theorem B4907051 : Blo 2179435 4907051 := bstep (se 1 (by rfl) ⟨3680288, by rfl⟩ : syracuseStep 4907051 = 7360577) B7360577
theorem B3271367 : Blo 2179435 3271367 := bstep (se 1 (by rfl) ⟨2453525, by rfl⟩ : syracuseStep 3271367 = 4907051) B4907051
theorem B2180911 : Blo 2179435 2180911 := bstep (se 1 (by rfl) ⟨1635683, by rfl⟩ : syracuseStep 2180911 = 3271367) B3271367
theorem B3271373 : Blo 2179435 3271373 := bbase (se 3 (by rfl) ⟨613382, by rfl⟩ : syracuseStep 3271373 = 1226765) (by norm_num)
theorem B2180915 : Blo 2179435 2180915 := bstep (se 1 (by rfl) ⟨1635686, by rfl⟩ : syracuseStep 2180915 = 3271373) B3271373
theorem B4907069 : Blo 2179435 4907069 := bbase (se 3 (by rfl) ⟨920075, by rfl⟩ : syracuseStep 4907069 = 1840151) (by norm_num)
theorem B3271379 : Blo 2179435 3271379 := bstep (se 1 (by rfl) ⟨2453534, by rfl⟩ : syracuseStep 3271379 = 4907069) B4907069
theorem B2180919 : Blo 2179435 2180919 := bstep (se 1 (by rfl) ⟨1635689, by rfl⟩ : syracuseStep 2180919 = 3271379) B3271379
theorem B3680309 : Blo 2179435 3680309 := bbase (se 5 (by rfl) ⟨172514, by rfl⟩ : syracuseStep 3680309 = 345029) (by norm_num)
theorem B2453539 : Blo 2179435 2453539 := bstep (se 1 (by rfl) ⟨1840154, by rfl⟩ : syracuseStep 2453539 = 3680309) B3680309
theorem B3271385 : Blo 2179435 3271385 := bstep (se 2 (by rfl) ⟨1226769, by rfl⟩ : syracuseStep 3271385 = 2453539) B2453539
theorem B2180923 : Blo 2179435 2180923 := bstep (se 1 (by rfl) ⟨1635692, by rfl⟩ : syracuseStep 2180923 = 3271385) B3271385
theorem B6210533 : Blo 2179435 6210533 := bbase (se 4 (by rfl) ⟨582237, by rfl⟩ : syracuseStep 6210533 = 1164475) (by norm_num)
theorem B16561421 : Blo 2179435 16561421 := bstep (se 3 (by rfl) ⟨3105266, by rfl⟩ : syracuseStep 16561421 = 6210533) B6210533
theorem B11040947 : Blo 2179435 11040947 := bstep (se 1 (by rfl) ⟨8280710, by rfl⟩ : syracuseStep 11040947 = 16561421) B16561421
theorem B7360631 : Blo 2179435 7360631 := bstep (se 1 (by rfl) ⟨5520473, by rfl⟩ : syracuseStep 7360631 = 11040947) B11040947
theorem B4907087 : Blo 2179435 4907087 := bstep (se 1 (by rfl) ⟨3680315, by rfl⟩ : syracuseStep 4907087 = 7360631) B7360631
theorem B3271391 : Blo 2179435 3271391 := bstep (se 1 (by rfl) ⟨2453543, by rfl⟩ : syracuseStep 3271391 = 4907087) B4907087
theorem B2180927 : Blo 2179435 2180927 := bstep (se 1 (by rfl) ⟨1635695, by rfl⟩ : syracuseStep 2180927 = 3271391) B3271391
theorem B3271397 : Blo 2179435 3271397 := bbase (se 4 (by rfl) ⟨306693, by rfl⟩ : syracuseStep 3271397 = 613387) (by norm_num)
theorem B2180931 : Blo 2179435 2180931 := bstep (se 1 (by rfl) ⟨1635698, by rfl⟩ : syracuseStep 2180931 = 3271397) B3271397
theorem B2487029 : Blo 2179435 2487029 := bbase (se 5 (by rfl) ⟨116579, by rfl⟩ : syracuseStep 2487029 = 233159) (by norm_num)
theorem B26528309 : Blo 2179435 26528309 := bstep (se 5 (by rfl) ⟨1243514, by rfl⟩ : syracuseStep 26528309 = 2487029) B2487029
theorem B17685539 : Blo 2179435 17685539 := bstep (se 1 (by rfl) ⟨13264154, by rfl⟩ : syracuseStep 17685539 = 26528309) B26528309
theorem B11790359 : Blo 2179435 11790359 := bstep (se 1 (by rfl) ⟨8842769, by rfl⟩ : syracuseStep 11790359 = 17685539) B17685539
theorem B7860239 : Blo 2179435 7860239 := bstep (se 1 (by rfl) ⟨5895179, by rfl⟩ : syracuseStep 7860239 = 11790359) B11790359
theorem B5240159 : Blo 2179435 5240159 := bstep (se 1 (by rfl) ⟨3930119, by rfl⟩ : syracuseStep 5240159 = 7860239) B7860239
theorem B3493439 : Blo 2179435 3493439 := bstep (se 1 (by rfl) ⟨2620079, by rfl⟩ : syracuseStep 3493439 = 5240159) B5240159
theorem B2328959 : Blo 2179435 2328959 := bstep (se 1 (by rfl) ⟨1746719, by rfl⟩ : syracuseStep 2328959 = 3493439) B3493439
theorem B6210557 : Blo 2179435 6210557 := bstep (se 3 (by rfl) ⟨1164479, by rfl⟩ : syracuseStep 6210557 = 2328959) B2328959
theorem B4140371 : Blo 2179435 4140371 := bstep (se 1 (by rfl) ⟨3105278, by rfl⟩ : syracuseStep 4140371 = 6210557) B6210557
theorem B2760247 : Blo 2179435 2760247 := bstep (se 1 (by rfl) ⟨2070185, by rfl⟩ : syracuseStep 2760247 = 4140371) B4140371
theorem B3680329 : Blo 2179435 3680329 := bstep (se 2 (by rfl) ⟨1380123, by rfl⟩ : syracuseStep 3680329 = 2760247) B2760247
theorem B4907105 : Blo 2179435 4907105 := bstep (se 2 (by rfl) ⟨1840164, by rfl⟩ : syracuseStep 4907105 = 3680329) B3680329
theorem B3271403 : Blo 2179435 3271403 := bstep (se 1 (by rfl) ⟨2453552, by rfl⟩ : syracuseStep 3271403 = 4907105) B4907105
theorem B2180935 : Blo 2179435 2180935 := bstep (se 1 (by rfl) ⟨1635701, by rfl⟩ : syracuseStep 2180935 = 3271403) B3271403
theorem B2453557 : Blo 2179435 2453557 := bbase (se 5 (by rfl) ⟨115010, by rfl⟩ : syracuseStep 2453557 = 230021) (by norm_num)
theorem B3271409 : Blo 2179435 3271409 := bstep (se 2 (by rfl) ⟨1226778, by rfl⟩ : syracuseStep 3271409 = 2453557) B2453557
theorem B2180939 : Blo 2179435 2180939 := bstep (se 1 (by rfl) ⟨1635704, by rfl⟩ : syracuseStep 2180939 = 3271409) B3271409
theorem B2760257 : Blo 2179435 2760257 := bbase (se 2 (by rfl) ⟨1035096, by rfl⟩ : syracuseStep 2760257 = 2070193) (by norm_num)
theorem B7360685 : Blo 2179435 7360685 := bstep (se 3 (by rfl) ⟨1380128, by rfl⟩ : syracuseStep 7360685 = 2760257) B2760257
theorem B4907123 : Blo 2179435 4907123 := bstep (se 1 (by rfl) ⟨3680342, by rfl⟩ : syracuseStep 4907123 = 7360685) B7360685
theorem B3271415 : Blo 2179435 3271415 := bstep (se 1 (by rfl) ⟨2453561, by rfl⟩ : syracuseStep 3271415 = 4907123) B4907123
theorem B2180943 : Blo 2179435 2180943 := bstep (se 1 (by rfl) ⟨1635707, by rfl⟩ : syracuseStep 2180943 = 3271415) B3271415
theorem B3271421 : Blo 2179435 3271421 := bbase (se 3 (by rfl) ⟨613391, by rfl⟩ : syracuseStep 3271421 = 1226783) (by norm_num)
theorem B2180947 : Blo 2179435 2180947 := bstep (se 1 (by rfl) ⟨1635710, by rfl⟩ : syracuseStep 2180947 = 3271421) B3271421
theorem B4907141 : Blo 2179435 4907141 := bbase (se 4 (by rfl) ⟨460044, by rfl⟩ : syracuseStep 4907141 = 920089) (by norm_num)
theorem B3271427 : Blo 2179435 3271427 := bstep (se 1 (by rfl) ⟨2453570, by rfl⟩ : syracuseStep 3271427 = 4907141) B4907141
theorem B2180951 : Blo 2179435 2180951 := bstep (se 1 (by rfl) ⟨1635713, by rfl⟩ : syracuseStep 2180951 = 3271427) B3271427
theorem B3316069 : Blo 2179435 3316069 := bbase (se 4 (by rfl) ⟨310881, by rfl⟩ : syracuseStep 3316069 = 621763) (by norm_num)
theorem B17685701 : Blo 2179435 17685701 := bstep (se 4 (by rfl) ⟨1658034, by rfl⟩ : syracuseStep 17685701 = 3316069) B3316069
theorem B11790467 : Blo 2179435 11790467 := bstep (se 1 (by rfl) ⟨8842850, by rfl⟩ : syracuseStep 11790467 = 17685701) B17685701
theorem B7860311 : Blo 2179435 7860311 := bstep (se 1 (by rfl) ⟨5895233, by rfl⟩ : syracuseStep 7860311 = 11790467) B11790467
theorem B5240207 : Blo 2179435 5240207 := bstep (se 1 (by rfl) ⟨3930155, by rfl⟩ : syracuseStep 5240207 = 7860311) B7860311
theorem B3493471 : Blo 2179435 3493471 := bstep (se 1 (by rfl) ⟨2620103, by rfl⟩ : syracuseStep 3493471 = 5240207) B5240207
theorem B4657961 : Blo 2179435 4657961 := bstep (se 2 (by rfl) ⟨1746735, by rfl⟩ : syracuseStep 4657961 = 3493471) B3493471
theorem B3105307 : Blo 2179435 3105307 := bstep (se 1 (by rfl) ⟨2328980, by rfl⟩ : syracuseStep 3105307 = 4657961) B4657961
theorem B4140409 : Blo 2179435 4140409 := bstep (se 2 (by rfl) ⟨1552653, by rfl⟩ : syracuseStep 4140409 = 3105307) B3105307
theorem B5520545 : Blo 2179435 5520545 := bstep (se 2 (by rfl) ⟨2070204, by rfl⟩ : syracuseStep 5520545 = 4140409) B4140409
theorem B3680363 : Blo 2179435 3680363 := bstep (se 1 (by rfl) ⟨2760272, by rfl⟩ : syracuseStep 3680363 = 5520545) B5520545
theorem B2453575 : Blo 2179435 2453575 := bstep (se 1 (by rfl) ⟨1840181, by rfl⟩ : syracuseStep 2453575 = 3680363) B3680363
theorem B3271433 : Blo 2179435 3271433 := bstep (se 2 (by rfl) ⟨1226787, by rfl⟩ : syracuseStep 3271433 = 2453575) B2453575
theorem B2180955 : Blo 2179435 2180955 := bstep (se 1 (by rfl) ⟨1635716, by rfl⟩ : syracuseStep 2180955 = 3271433) B3271433
theorem B11041109 : Blo 2179435 11041109 := bbase (se 10 (by rfl) ⟨16173, by rfl⟩ : syracuseStep 11041109 = 32347) (by norm_num)
theorem B7360739 : Blo 2179435 7360739 := bstep (se 1 (by rfl) ⟨5520554, by rfl⟩ : syracuseStep 7360739 = 11041109) B11041109
theorem B4907159 : Blo 2179435 4907159 := bstep (se 1 (by rfl) ⟨3680369, by rfl⟩ : syracuseStep 4907159 = 7360739) B7360739
theorem B3271439 : Blo 2179435 3271439 := bstep (se 1 (by rfl) ⟨2453579, by rfl⟩ : syracuseStep 3271439 = 4907159) B4907159
theorem B2180959 : Blo 2179435 2180959 := bstep (se 1 (by rfl) ⟨1635719, by rfl⟩ : syracuseStep 2180959 = 3271439) B3271439
theorem B3271445 : Blo 2179435 3271445 := bbase (se 6 (by rfl) ⟨76674, by rfl⟩ : syracuseStep 3271445 = 153349) (by norm_num)
theorem B2180963 : Blo 2179435 2180963 := bstep (se 1 (by rfl) ⟨1635722, by rfl⟩ : syracuseStep 2180963 = 3271445) B3271445
theorem B2655865 : Blo 2179435 2655865 := bbase (se 2 (by rfl) ⟨995949, by rfl⟩ : syracuseStep 2655865 = 1991899) (by norm_num)
theorem B3541153 : Blo 2179435 3541153 := bstep (se 2 (by rfl) ⟨1327932, by rfl⟩ : syracuseStep 3541153 = 2655865) B2655865
theorem B4721537 : Blo 2179435 4721537 := bstep (se 2 (by rfl) ⟨1770576, by rfl⟩ : syracuseStep 4721537 = 3541153) B3541153
theorem B3147691 : Blo 2179435 3147691 := bstep (se 1 (by rfl) ⟨2360768, by rfl⟩ : syracuseStep 3147691 = 4721537) B4721537
theorem B67150741 : Blo 2179435 67150741 := bstep (se 6 (by rfl) ⟨1573845, by rfl⟩ : syracuseStep 67150741 = 3147691) B3147691
theorem B89534321 : Blo 2179435 89534321 := bstep (se 2 (by rfl) ⟨33575370, by rfl⟩ : syracuseStep 89534321 = 67150741) B67150741
theorem B59689547 : Blo 2179435 59689547 := bstep (se 1 (by rfl) ⟨44767160, by rfl⟩ : syracuseStep 59689547 = 89534321) B89534321
theorem B39793031 : Blo 2179435 39793031 := bstep (se 1 (by rfl) ⟨29844773, by rfl⟩ : syracuseStep 39793031 = 59689547) B59689547
theorem B26528687 : Blo 2179435 26528687 := bstep (se 1 (by rfl) ⟨19896515, by rfl⟩ : syracuseStep 26528687 = 39793031) B39793031
theorem B17685791 : Blo 2179435 17685791 := bstep (se 1 (by rfl) ⟨13264343, by rfl⟩ : syracuseStep 17685791 = 26528687) B26528687
theorem B11790527 : Blo 2179435 11790527 := bstep (se 1 (by rfl) ⟨8842895, by rfl⟩ : syracuseStep 11790527 = 17685791) B17685791
theorem B31441405 : Blo 2179435 31441405 := bstep (se 3 (by rfl) ⟨5895263, by rfl⟩ : syracuseStep 31441405 = 11790527) B11790527
theorem B41921873 : Blo 2179435 41921873 := bstep (se 2 (by rfl) ⟨15720702, by rfl⟩ : syracuseStep 41921873 = 31441405) B31441405
theorem B27947915 : Blo 2179435 27947915 := bstep (se 1 (by rfl) ⟨20960936, by rfl⟩ : syracuseStep 27947915 = 41921873) B41921873
theorem B18631943 : Blo 2179435 18631943 := bstep (se 1 (by rfl) ⟨13973957, by rfl⟩ : syracuseStep 18631943 = 27947915) B27947915
theorem B12421295 : Blo 2179435 12421295 := bstep (se 1 (by rfl) ⟨9315971, by rfl⟩ : syracuseStep 12421295 = 18631943) B18631943
theorem B8280863 : Blo 2179435 8280863 := bstep (se 1 (by rfl) ⟨6210647, by rfl⟩ : syracuseStep 8280863 = 12421295) B12421295
theorem B5520575 : Blo 2179435 5520575 := bstep (se 1 (by rfl) ⟨4140431, by rfl⟩ : syracuseStep 5520575 = 8280863) B8280863
theorem B3680383 : Blo 2179435 3680383 := bstep (se 1 (by rfl) ⟨2760287, by rfl⟩ : syracuseStep 3680383 = 5520575) B5520575
theorem B4907177 : Blo 2179435 4907177 := bstep (se 2 (by rfl) ⟨1840191, by rfl⟩ : syracuseStep 4907177 = 3680383) B3680383
theorem B3271451 : Blo 2179435 3271451 := bstep (se 1 (by rfl) ⟨2453588, by rfl⟩ : syracuseStep 3271451 = 4907177) B4907177
theorem B2180967 : Blo 2179435 2180967 := bstep (se 1 (by rfl) ⟨1635725, by rfl⟩ : syracuseStep 2180967 = 3271451) B3271451
theorem B2453593 : Blo 2179435 2453593 := bbase (se 2 (by rfl) ⟨920097, by rfl⟩ : syracuseStep 2453593 = 1840195) (by norm_num)
theorem B3271457 : Blo 2179435 3271457 := bstep (se 2 (by rfl) ⟨1226796, by rfl⟩ : syracuseStep 3271457 = 2453593) B2453593
theorem B2180971 : Blo 2179435 2180971 := bstep (se 1 (by rfl) ⟨1635728, by rfl⟩ : syracuseStep 2180971 = 3271457) B3271457
theorem B4974149 : Blo 2179435 4974149 := bbase (se 4 (by rfl) ⟨466326, by rfl⟩ : syracuseStep 4974149 = 932653) (by norm_num)
theorem B13264397 : Blo 2179435 13264397 := bstep (se 3 (by rfl) ⟨2487074, by rfl⟩ : syracuseStep 13264397 = 4974149) B4974149
theorem B8842931 : Blo 2179435 8842931 := bstep (se 1 (by rfl) ⟨6632198, by rfl⟩ : syracuseStep 8842931 = 13264397) B13264397
theorem B5895287 : Blo 2179435 5895287 := bstep (se 1 (by rfl) ⟨4421465, by rfl⟩ : syracuseStep 5895287 = 8842931) B8842931
theorem B3930191 : Blo 2179435 3930191 := bstep (se 1 (by rfl) ⟨2947643, by rfl⟩ : syracuseStep 3930191 = 5895287) B5895287
theorem B2620127 : Blo 2179435 2620127 := bstep (se 1 (by rfl) ⟨1965095, by rfl⟩ : syracuseStep 2620127 = 3930191) B3930191
theorem B6987005 : Blo 2179435 6987005 := bstep (se 3 (by rfl) ⟨1310063, by rfl⟩ : syracuseStep 6987005 = 2620127) B2620127
theorem B4658003 : Blo 2179435 4658003 := bstep (se 1 (by rfl) ⟨3493502, by rfl⟩ : syracuseStep 4658003 = 6987005) B6987005
theorem B3105335 : Blo 2179435 3105335 := bstep (se 1 (by rfl) ⟨2329001, by rfl⟩ : syracuseStep 3105335 = 4658003) B4658003
theorem B8280893 : Blo 2179435 8280893 := bstep (se 3 (by rfl) ⟨1552667, by rfl⟩ : syracuseStep 8280893 = 3105335) B3105335
theorem B5520595 : Blo 2179435 5520595 := bstep (se 1 (by rfl) ⟨4140446, by rfl⟩ : syracuseStep 5520595 = 8280893) B8280893
theorem B7360793 : Blo 2179435 7360793 := bstep (se 2 (by rfl) ⟨2760297, by rfl⟩ : syracuseStep 7360793 = 5520595) B5520595
theorem B4907195 : Blo 2179435 4907195 := bstep (se 1 (by rfl) ⟨3680396, by rfl⟩ : syracuseStep 4907195 = 7360793) B7360793
theorem B3271463 : Blo 2179435 3271463 := bstep (se 1 (by rfl) ⟨2453597, by rfl⟩ : syracuseStep 3271463 = 4907195) B4907195
theorem B2180975 : Blo 2179435 2180975 := bstep (se 1 (by rfl) ⟨1635731, by rfl⟩ : syracuseStep 2180975 = 3271463) B3271463
theorem B3271469 : Blo 2179435 3271469 := bbase (se 3 (by rfl) ⟨613400, by rfl⟩ : syracuseStep 3271469 = 1226801) (by norm_num)
theorem B2180979 : Blo 2179435 2180979 := bstep (se 1 (by rfl) ⟨1635734, by rfl⟩ : syracuseStep 2180979 = 3271469) B3271469
theorem B4907213 : Blo 2179435 4907213 := bbase (se 3 (by rfl) ⟨920102, by rfl⟩ : syracuseStep 4907213 = 1840205) (by norm_num)
theorem B3271475 : Blo 2179435 3271475 := bstep (se 1 (by rfl) ⟨2453606, by rfl⟩ : syracuseStep 3271475 = 4907213) B4907213
theorem B2180983 : Blo 2179435 2180983 := bstep (se 1 (by rfl) ⟨1635737, by rfl⟩ : syracuseStep 2180983 = 3271475) B3271475
theorem B2760313 : Blo 2179435 2760313 := bbase (se 2 (by rfl) ⟨1035117, by rfl⟩ : syracuseStep 2760313 = 2070235) (by norm_num)
theorem B3680417 : Blo 2179435 3680417 := bstep (se 2 (by rfl) ⟨1380156, by rfl⟩ : syracuseStep 3680417 = 2760313) B2760313
theorem B2453611 : Blo 2179435 2453611 := bstep (se 1 (by rfl) ⟨1840208, by rfl⟩ : syracuseStep 2453611 = 3680417) B3680417
theorem B3271481 : Blo 2179435 3271481 := bstep (se 2 (by rfl) ⟨1226805, by rfl⟩ : syracuseStep 3271481 = 2453611) B2453611
theorem B2180987 : Blo 2179435 2180987 := bstep (se 1 (by rfl) ⟨1635740, by rfl⟩ : syracuseStep 2180987 = 3271481) B3271481
theorem B4481821 : Blo 2179435 4481821 := bbase (se 3 (by rfl) ⟨840341, by rfl⟩ : syracuseStep 4481821 = 1680683) (by norm_num)
theorem B23903045 : Blo 2179435 23903045 := bstep (se 4 (by rfl) ⟨2240910, by rfl⟩ : syracuseStep 23903045 = 4481821) B4481821
theorem B15935363 : Blo 2179435 15935363 := bstep (se 1 (by rfl) ⟨11951522, by rfl⟩ : syracuseStep 15935363 = 23903045) B23903045
theorem B10623575 : Blo 2179435 10623575 := bstep (se 1 (by rfl) ⟨7967681, by rfl⟩ : syracuseStep 10623575 = 15935363) B15935363
theorem B28329533 : Blo 2179435 28329533 := bstep (se 3 (by rfl) ⟨5311787, by rfl⟩ : syracuseStep 28329533 = 10623575) B10623575
theorem B18886355 : Blo 2179435 18886355 := bstep (se 1 (by rfl) ⟨14164766, by rfl⟩ : syracuseStep 18886355 = 28329533) B28329533
theorem B12590903 : Blo 2179435 12590903 := bstep (se 1 (by rfl) ⟨9443177, by rfl⟩ : syracuseStep 12590903 = 18886355) B18886355
theorem B33575741 : Blo 2179435 33575741 := bstep (se 3 (by rfl) ⟨6295451, by rfl⟩ : syracuseStep 33575741 = 12590903) B12590903
theorem B22383827 : Blo 2179435 22383827 := bstep (se 1 (by rfl) ⟨16787870, by rfl⟩ : syracuseStep 22383827 = 33575741) B33575741
theorem B14922551 : Blo 2179435 14922551 := bstep (se 1 (by rfl) ⟨11191913, by rfl⟩ : syracuseStep 14922551 = 22383827) B22383827
theorem B9948367 : Blo 2179435 9948367 := bstep (se 1 (by rfl) ⟨7461275, by rfl⟩ : syracuseStep 9948367 = 14922551) B14922551
theorem B13264489 : Blo 2179435 13264489 := bstep (se 2 (by rfl) ⟨4974183, by rfl⟩ : syracuseStep 13264489 = 9948367) B9948367
theorem B17685985 : Blo 2179435 17685985 := bstep (se 2 (by rfl) ⟨6632244, by rfl⟩ : syracuseStep 17685985 = 13264489) B13264489
theorem B23581313 : Blo 2179435 23581313 := bstep (se 2 (by rfl) ⟨8842992, by rfl⟩ : syracuseStep 23581313 = 17685985) B17685985
theorem B15720875 : Blo 2179435 15720875 := bstep (se 1 (by rfl) ⟨11790656, by rfl⟩ : syracuseStep 15720875 = 23581313) B23581313
theorem B10480583 : Blo 2179435 10480583 := bstep (se 1 (by rfl) ⟨7860437, by rfl⟩ : syracuseStep 10480583 = 15720875) B15720875
theorem B6987055 : Blo 2179435 6987055 := bstep (se 1 (by rfl) ⟨5240291, by rfl⟩ : syracuseStep 6987055 = 10480583) B10480583
theorem B9316073 : Blo 2179435 9316073 := bstep (se 2 (by rfl) ⟨3493527, by rfl⟩ : syracuseStep 9316073 = 6987055) B6987055
theorem B24842861 : Blo 2179435 24842861 := bstep (se 3 (by rfl) ⟨4658036, by rfl⟩ : syracuseStep 24842861 = 9316073) B9316073
theorem B16561907 : Blo 2179435 16561907 := bstep (se 1 (by rfl) ⟨12421430, by rfl⟩ : syracuseStep 16561907 = 24842861) B24842861
theorem B11041271 : Blo 2179435 11041271 := bstep (se 1 (by rfl) ⟨8280953, by rfl⟩ : syracuseStep 11041271 = 16561907) B16561907
theorem B7360847 : Blo 2179435 7360847 := bstep (se 1 (by rfl) ⟨5520635, by rfl⟩ : syracuseStep 7360847 = 11041271) B11041271
theorem B4907231 : Blo 2179435 4907231 := bstep (se 1 (by rfl) ⟨3680423, by rfl⟩ : syracuseStep 4907231 = 7360847) B7360847
theorem B3271487 : Blo 2179435 3271487 := bstep (se 1 (by rfl) ⟨2453615, by rfl⟩ : syracuseStep 3271487 = 4907231) B4907231
theorem B2180991 : Blo 2179435 2180991 := bstep (se 1 (by rfl) ⟨1635743, by rfl⟩ : syracuseStep 2180991 = 3271487) B3271487
theorem B3271493 : Blo 2179435 3271493 := bbase (se 4 (by rfl) ⟨306702, by rfl⟩ : syracuseStep 3271493 = 613405) (by norm_num)
theorem B2180995 : Blo 2179435 2180995 := bstep (se 1 (by rfl) ⟨1635746, by rfl⟩ : syracuseStep 2180995 = 3271493) B3271493
theorem B3680437 : Blo 2179435 3680437 := bbase (se 5 (by rfl) ⟨172520, by rfl⟩ : syracuseStep 3680437 = 345041) (by norm_num)
theorem B4907249 : Blo 2179435 4907249 := bstep (se 2 (by rfl) ⟨1840218, by rfl⟩ : syracuseStep 4907249 = 3680437) B3680437
theorem B3271499 : Blo 2179435 3271499 := bstep (se 1 (by rfl) ⟨2453624, by rfl⟩ : syracuseStep 3271499 = 4907249) B4907249
theorem B2180999 : Blo 2179435 2180999 := bstep (se 1 (by rfl) ⟨1635749, by rfl⟩ : syracuseStep 2180999 = 3271499) B3271499
theorem B2453629 : Blo 2179435 2453629 := bbase (se 3 (by rfl) ⟨460055, by rfl⟩ : syracuseStep 2453629 = 920111) (by norm_num)
theorem B3271505 : Blo 2179435 3271505 := bstep (se 2 (by rfl) ⟨1226814, by rfl⟩ : syracuseStep 3271505 = 2453629) B2453629
theorem B2181003 : Blo 2179435 2181003 := bstep (se 1 (by rfl) ⟨1635752, by rfl⟩ : syracuseStep 2181003 = 3271505) B3271505
theorem B7360901 : Blo 2179435 7360901 := bbase (se 4 (by rfl) ⟨690084, by rfl⟩ : syracuseStep 7360901 = 1380169) (by norm_num)
theorem B4907267 : Blo 2179435 4907267 := bstep (se 1 (by rfl) ⟨3680450, by rfl⟩ : syracuseStep 4907267 = 7360901) B7360901
theorem B3271511 : Blo 2179435 3271511 := bstep (se 1 (by rfl) ⟨2453633, by rfl⟩ : syracuseStep 3271511 = 4907267) B4907267
theorem B2181007 : Blo 2179435 2181007 := bstep (se 1 (by rfl) ⟨1635755, by rfl⟩ : syracuseStep 2181007 = 3271511) B3271511
theorem B3271517 : Blo 2179435 3271517 := bbase (se 3 (by rfl) ⟨613409, by rfl⟩ : syracuseStep 3271517 = 1226819) (by norm_num)
theorem B2181011 : Blo 2179435 2181011 := bstep (se 1 (by rfl) ⟨1635758, by rfl⟩ : syracuseStep 2181011 = 3271517) B3271517
theorem B4907285 : Blo 2179435 4907285 := bbase (se 6 (by rfl) ⟨115014, by rfl⟩ : syracuseStep 4907285 = 230029) (by norm_num)
theorem B3271523 : Blo 2179435 3271523 := bstep (se 1 (by rfl) ⟨2453642, by rfl⟩ : syracuseStep 3271523 = 4907285) B4907285
theorem B2181015 : Blo 2179435 2181015 := bstep (se 1 (by rfl) ⟨1635761, by rfl⟩ : syracuseStep 2181015 = 3271523) B3271523
theorem B8281061 : Blo 2179435 8281061 := bbase (se 4 (by rfl) ⟨776349, by rfl⟩ : syracuseStep 8281061 = 1552699) (by norm_num)
theorem B5520707 : Blo 2179435 5520707 := bstep (se 1 (by rfl) ⟨4140530, by rfl⟩ : syracuseStep 5520707 = 8281061) B8281061
theorem B3680471 : Blo 2179435 3680471 := bstep (se 1 (by rfl) ⟨2760353, by rfl⟩ : syracuseStep 3680471 = 5520707) B5520707
theorem B2453647 : Blo 2179435 2453647 := bstep (se 1 (by rfl) ⟨1840235, by rfl⟩ : syracuseStep 2453647 = 3680471) B3680471
theorem B3271529 : Blo 2179435 3271529 := bstep (se 2 (by rfl) ⟨1226823, by rfl⟩ : syracuseStep 3271529 = 2453647) B2453647
theorem B2181019 : Blo 2179435 2181019 := bstep (se 1 (by rfl) ⟨1635764, by rfl⟩ : syracuseStep 2181019 = 3271529) B3271529
theorem B3930277 : Blo 2179435 3930277 := bbase (se 4 (by rfl) ⟨368463, by rfl⟩ : syracuseStep 3930277 = 736927) (by norm_num)
theorem B5240369 : Blo 2179435 5240369 := bstep (se 2 (by rfl) ⟨1965138, by rfl⟩ : syracuseStep 5240369 = 3930277) B3930277
theorem B3493579 : Blo 2179435 3493579 := bstep (se 1 (by rfl) ⟨2620184, by rfl⟩ : syracuseStep 3493579 = 5240369) B5240369
theorem B4658105 : Blo 2179435 4658105 := bstep (se 2 (by rfl) ⟨1746789, by rfl⟩ : syracuseStep 4658105 = 3493579) B3493579
theorem B12421613 : Blo 2179435 12421613 := bstep (se 3 (by rfl) ⟨2329052, by rfl⟩ : syracuseStep 12421613 = 4658105) B4658105
theorem B8281075 : Blo 2179435 8281075 := bstep (se 1 (by rfl) ⟨6210806, by rfl⟩ : syracuseStep 8281075 = 12421613) B12421613
theorem B11041433 : Blo 2179435 11041433 := bstep (se 2 (by rfl) ⟨4140537, by rfl⟩ : syracuseStep 11041433 = 8281075) B8281075
theorem B7360955 : Blo 2179435 7360955 := bstep (se 1 (by rfl) ⟨5520716, by rfl⟩ : syracuseStep 7360955 = 11041433) B11041433
theorem B4907303 : Blo 2179435 4907303 := bstep (se 1 (by rfl) ⟨3680477, by rfl⟩ : syracuseStep 4907303 = 7360955) B7360955
theorem B3271535 : Blo 2179435 3271535 := bstep (se 1 (by rfl) ⟨2453651, by rfl⟩ : syracuseStep 3271535 = 4907303) B4907303
theorem B2181023 : Blo 2179435 2181023 := bstep (se 1 (by rfl) ⟨1635767, by rfl⟩ : syracuseStep 2181023 = 3271535) B3271535
theorem B3271541 : Blo 2179435 3271541 := bbase (se 5 (by rfl) ⟨153353, by rfl⟩ : syracuseStep 3271541 = 306707) (by norm_num)
theorem B2181027 : Blo 2179435 2181027 := bstep (se 1 (by rfl) ⟨1635770, by rfl⟩ : syracuseStep 2181027 = 3271541) B3271541
theorem B5240389 : Blo 2179435 5240389 := bbase (se 4 (by rfl) ⟨491286, by rfl⟩ : syracuseStep 5240389 = 982573) (by norm_num)
theorem B6987185 : Blo 2179435 6987185 := bstep (se 2 (by rfl) ⟨2620194, by rfl⟩ : syracuseStep 6987185 = 5240389) B5240389
theorem B4658123 : Blo 2179435 4658123 := bstep (se 1 (by rfl) ⟨3493592, by rfl⟩ : syracuseStep 4658123 = 6987185) B6987185
theorem B3105415 : Blo 2179435 3105415 := bstep (se 1 (by rfl) ⟨2329061, by rfl⟩ : syracuseStep 3105415 = 4658123) B4658123
theorem B4140553 : Blo 2179435 4140553 := bstep (se 2 (by rfl) ⟨1552707, by rfl⟩ : syracuseStep 4140553 = 3105415) B3105415
theorem B5520737 : Blo 2179435 5520737 := bstep (se 2 (by rfl) ⟨2070276, by rfl⟩ : syracuseStep 5520737 = 4140553) B4140553
theorem B3680491 : Blo 2179435 3680491 := bstep (se 1 (by rfl) ⟨2760368, by rfl⟩ : syracuseStep 3680491 = 5520737) B5520737
theorem B4907321 : Blo 2179435 4907321 := bstep (se 2 (by rfl) ⟨1840245, by rfl⟩ : syracuseStep 4907321 = 3680491) B3680491
theorem B3271547 : Blo 2179435 3271547 := bstep (se 1 (by rfl) ⟨2453660, by rfl⟩ : syracuseStep 3271547 = 4907321) B4907321
theorem B2181031 : Blo 2179435 2181031 := bstep (se 1 (by rfl) ⟨1635773, by rfl⟩ : syracuseStep 2181031 = 3271547) B3271547
theorem B2453665 : Blo 2179435 2453665 := bbase (se 2 (by rfl) ⟨920124, by rfl⟩ : syracuseStep 2453665 = 1840249) (by norm_num)
theorem B3271553 : Blo 2179435 3271553 := bstep (se 2 (by rfl) ⟨1226832, by rfl⟩ : syracuseStep 3271553 = 2453665) B2453665
theorem B2181035 : Blo 2179435 2181035 := bstep (se 1 (by rfl) ⟨1635776, by rfl⟩ : syracuseStep 2181035 = 3271553) B3271553
theorem B5520757 : Blo 2179435 5520757 := bbase (se 5 (by rfl) ⟨258785, by rfl⟩ : syracuseStep 5520757 = 517571) (by norm_num)
theorem B7361009 : Blo 2179435 7361009 := bstep (se 2 (by rfl) ⟨2760378, by rfl⟩ : syracuseStep 7361009 = 5520757) B5520757
theorem B4907339 : Blo 2179435 4907339 := bstep (se 1 (by rfl) ⟨3680504, by rfl⟩ : syracuseStep 4907339 = 7361009) B7361009
theorem B3271559 : Blo 2179435 3271559 := bstep (se 1 (by rfl) ⟨2453669, by rfl⟩ : syracuseStep 3271559 = 4907339) B4907339
theorem B2181039 : Blo 2179435 2181039 := bstep (se 1 (by rfl) ⟨1635779, by rfl⟩ : syracuseStep 2181039 = 3271559) B3271559
theorem B3271565 : Blo 2179435 3271565 := bbase (se 3 (by rfl) ⟨613418, by rfl⟩ : syracuseStep 3271565 = 1226837) (by norm_num)
theorem B2181043 : Blo 2179435 2181043 := bstep (se 1 (by rfl) ⟨1635782, by rfl⟩ : syracuseStep 2181043 = 3271565) B3271565
theorem B4907357 : Blo 2179435 4907357 := bbase (se 3 (by rfl) ⟨920129, by rfl⟩ : syracuseStep 4907357 = 1840259) (by norm_num)
theorem B3271571 : Blo 2179435 3271571 := bstep (se 1 (by rfl) ⟨2453678, by rfl⟩ : syracuseStep 3271571 = 4907357) B4907357
theorem B2181047 : Blo 2179435 2181047 := bstep (se 1 (by rfl) ⟨1635785, by rfl⟩ : syracuseStep 2181047 = 3271571) B3271571
theorem B3680525 : Blo 2179435 3680525 := bbase (se 3 (by rfl) ⟨690098, by rfl⟩ : syracuseStep 3680525 = 1380197) (by norm_num)
theorem B2453683 : Blo 2179435 2453683 := bstep (se 1 (by rfl) ⟨1840262, by rfl⟩ : syracuseStep 2453683 = 3680525) B3680525
theorem B3271577 : Blo 2179435 3271577 := bstep (se 2 (by rfl) ⟨1226841, by rfl⟩ : syracuseStep 3271577 = 2453683) B2453683
theorem B2181051 : Blo 2179435 2181051 := bstep (se 1 (by rfl) ⟨1635788, by rfl⟩ : syracuseStep 2181051 = 3271577) B3271577
theorem B18632693 : Blo 2179435 18632693 := bbase (se 5 (by rfl) ⟨873407, by rfl⟩ : syracuseStep 18632693 = 1746815) (by norm_num)
theorem B12421795 : Blo 2179435 12421795 := bstep (se 1 (by rfl) ⟨9316346, by rfl⟩ : syracuseStep 12421795 = 18632693) B18632693
theorem B16562393 : Blo 2179435 16562393 := bstep (se 2 (by rfl) ⟨6210897, by rfl⟩ : syracuseStep 16562393 = 12421795) B12421795
theorem B11041595 : Blo 2179435 11041595 := bstep (se 1 (by rfl) ⟨8281196, by rfl⟩ : syracuseStep 11041595 = 16562393) B16562393
theorem B7361063 : Blo 2179435 7361063 := bstep (se 1 (by rfl) ⟨5520797, by rfl⟩ : syracuseStep 7361063 = 11041595) B11041595
theorem B4907375 : Blo 2179435 4907375 := bstep (se 1 (by rfl) ⟨3680531, by rfl⟩ : syracuseStep 4907375 = 7361063) B7361063
theorem B3271583 : Blo 2179435 3271583 := bstep (se 1 (by rfl) ⟨2453687, by rfl⟩ : syracuseStep 3271583 = 4907375) B4907375
theorem B2181055 : Blo 2179435 2181055 := bstep (se 1 (by rfl) ⟨1635791, by rfl⟩ : syracuseStep 2181055 = 3271583) B3271583
theorem B3271589 : Blo 2179435 3271589 := bbase (se 4 (by rfl) ⟨306711, by rfl⟩ : syracuseStep 3271589 = 613423) (by norm_num)
theorem B2181059 : Blo 2179435 2181059 := bstep (se 1 (by rfl) ⟨1635794, by rfl⟩ : syracuseStep 2181059 = 3271589) B3271589
theorem B2760409 : Blo 2179435 2760409 := bbase (se 2 (by rfl) ⟨1035153, by rfl⟩ : syracuseStep 2760409 = 2070307) (by norm_num)
theorem B3680545 : Blo 2179435 3680545 := bstep (se 2 (by rfl) ⟨1380204, by rfl⟩ : syracuseStep 3680545 = 2760409) B2760409
theorem B4907393 : Blo 2179435 4907393 := bstep (se 2 (by rfl) ⟨1840272, by rfl⟩ : syracuseStep 4907393 = 3680545) B3680545
theorem B3271595 : Blo 2179435 3271595 := bstep (se 1 (by rfl) ⟨2453696, by rfl⟩ : syracuseStep 3271595 = 4907393) B4907393
theorem B2181063 : Blo 2179435 2181063 := bstep (se 1 (by rfl) ⟨1635797, by rfl⟩ : syracuseStep 2181063 = 3271595) B3271595
theorem B2453701 : Blo 2179435 2453701 := bbase (se 4 (by rfl) ⟨230034, by rfl⟩ : syracuseStep 2453701 = 460069) (by norm_num)
theorem B3271601 : Blo 2179435 3271601 := bstep (se 2 (by rfl) ⟨1226850, by rfl⟩ : syracuseStep 3271601 = 2453701) B2453701
theorem B2181067 : Blo 2179435 2181067 := bstep (se 1 (by rfl) ⟨1635800, by rfl⟩ : syracuseStep 2181067 = 3271601) B3271601
theorem B4140629 : Blo 2179435 4140629 := bbase (se 8 (by rfl) ⟨24261, by rfl⟩ : syracuseStep 4140629 = 48523) (by norm_num)
theorem B2760419 : Blo 2179435 2760419 := bstep (se 1 (by rfl) ⟨2070314, by rfl⟩ : syracuseStep 2760419 = 4140629) B4140629
theorem B7361117 : Blo 2179435 7361117 := bstep (se 3 (by rfl) ⟨1380209, by rfl⟩ : syracuseStep 7361117 = 2760419) B2760419
theorem B4907411 : Blo 2179435 4907411 := bstep (se 1 (by rfl) ⟨3680558, by rfl⟩ : syracuseStep 4907411 = 7361117) B7361117
theorem B3271607 : Blo 2179435 3271607 := bstep (se 1 (by rfl) ⟨2453705, by rfl⟩ : syracuseStep 3271607 = 4907411) B4907411
theorem B2181071 : Blo 2179435 2181071 := bstep (se 1 (by rfl) ⟨1635803, by rfl⟩ : syracuseStep 2181071 = 3271607) B3271607
theorem B3271613 : Blo 2179435 3271613 := bbase (se 3 (by rfl) ⟨613427, by rfl⟩ : syracuseStep 3271613 = 1226855) (by norm_num)
theorem B2181075 : Blo 2179435 2181075 := bstep (se 1 (by rfl) ⟨1635806, by rfl⟩ : syracuseStep 2181075 = 3271613) B3271613
theorem B4907429 : Blo 2179435 4907429 := bbase (se 4 (by rfl) ⟨460071, by rfl⟩ : syracuseStep 4907429 = 920143) (by norm_num)
theorem B3271619 : Blo 2179435 3271619 := bstep (se 1 (by rfl) ⟨2453714, by rfl⟩ : syracuseStep 3271619 = 4907429) B4907429
theorem B2181079 : Blo 2179435 2181079 := bstep (se 1 (by rfl) ⟨1635809, by rfl⟩ : syracuseStep 2181079 = 3271619) B3271619
theorem B5520869 : Blo 2179435 5520869 := bbase (se 4 (by rfl) ⟨517581, by rfl⟩ : syracuseStep 5520869 = 1035163) (by norm_num)
theorem B3680579 : Blo 2179435 3680579 := bstep (se 1 (by rfl) ⟨2760434, by rfl⟩ : syracuseStep 3680579 = 5520869) B5520869
theorem B2453719 : Blo 2179435 2453719 := bstep (se 1 (by rfl) ⟨1840289, by rfl⟩ : syracuseStep 2453719 = 3680579) B3680579
theorem B3271625 : Blo 2179435 3271625 := bstep (se 2 (by rfl) ⟨1226859, by rfl⟩ : syracuseStep 3271625 = 2453719) B2453719
theorem B2181083 : Blo 2179435 2181083 := bstep (se 1 (by rfl) ⟨1635812, by rfl⟩ : syracuseStep 2181083 = 3271625) B3271625
theorem B2329121 : Blo 2179435 2329121 := bbase (se 2 (by rfl) ⟨873420, by rfl⟩ : syracuseStep 2329121 = 1746841) (by norm_num)
theorem B6210989 : Blo 2179435 6210989 := bstep (se 3 (by rfl) ⟨1164560, by rfl⟩ : syracuseStep 6210989 = 2329121) B2329121
theorem B4140659 : Blo 2179435 4140659 := bstep (se 1 (by rfl) ⟨3105494, by rfl⟩ : syracuseStep 4140659 = 6210989) B6210989
theorem B11041757 : Blo 2179435 11041757 := bstep (se 3 (by rfl) ⟨2070329, by rfl⟩ : syracuseStep 11041757 = 4140659) B4140659
theorem B7361171 : Blo 2179435 7361171 := bstep (se 1 (by rfl) ⟨5520878, by rfl⟩ : syracuseStep 7361171 = 11041757) B11041757
theorem B4907447 : Blo 2179435 4907447 := bstep (se 1 (by rfl) ⟨3680585, by rfl⟩ : syracuseStep 4907447 = 7361171) B7361171
theorem B3271631 : Blo 2179435 3271631 := bstep (se 1 (by rfl) ⟨2453723, by rfl⟩ : syracuseStep 3271631 = 4907447) B4907447
theorem B2181087 : Blo 2179435 2181087 := bstep (se 1 (by rfl) ⟨1635815, by rfl⟩ : syracuseStep 2181087 = 3271631) B3271631
theorem B3271637 : Blo 2179435 3271637 := bbase (se 7 (by rfl) ⟨38339, by rfl⟩ : syracuseStep 3271637 = 76679) (by norm_num)
theorem B2181091 : Blo 2179435 2181091 := bstep (se 1 (by rfl) ⟨1635818, by rfl⟩ : syracuseStep 2181091 = 3271637) B3271637
theorem B8281349 : Blo 2179435 8281349 := bbase (se 4 (by rfl) ⟨776376, by rfl⟩ : syracuseStep 8281349 = 1552753) (by norm_num)
theorem B5520899 : Blo 2179435 5520899 := bstep (se 1 (by rfl) ⟨4140674, by rfl⟩ : syracuseStep 5520899 = 8281349) B8281349
theorem B3680599 : Blo 2179435 3680599 := bstep (se 1 (by rfl) ⟨2760449, by rfl⟩ : syracuseStep 3680599 = 5520899) B5520899
theorem B4907465 : Blo 2179435 4907465 := bstep (se 2 (by rfl) ⟨1840299, by rfl⟩ : syracuseStep 4907465 = 3680599) B3680599
theorem B3271643 : Blo 2179435 3271643 := bstep (se 1 (by rfl) ⟨2453732, by rfl⟩ : syracuseStep 3271643 = 4907465) B4907465
theorem B2181095 : Blo 2179435 2181095 := bstep (se 1 (by rfl) ⟨1635821, by rfl⟩ : syracuseStep 2181095 = 3271643) B3271643
theorem B2453737 : Blo 2179435 2453737 := bbase (se 2 (by rfl) ⟨920151, by rfl⟩ : syracuseStep 2453737 = 1840303) (by norm_num)
theorem B3271649 : Blo 2179435 3271649 := bstep (se 2 (by rfl) ⟨1226868, by rfl⟩ : syracuseStep 3271649 = 2453737) B2453737
theorem B2181099 : Blo 2179435 2181099 := bstep (se 1 (by rfl) ⟨1635824, by rfl⟩ : syracuseStep 2181099 = 3271649) B3271649
theorem B12422069 : Blo 2179435 12422069 := bbase (se 5 (by rfl) ⟨582284, by rfl⟩ : syracuseStep 12422069 = 1164569) (by norm_num)
theorem B8281379 : Blo 2179435 8281379 := bstep (se 1 (by rfl) ⟨6211034, by rfl⟩ : syracuseStep 8281379 = 12422069) B12422069
theorem B5520919 : Blo 2179435 5520919 := bstep (se 1 (by rfl) ⟨4140689, by rfl⟩ : syracuseStep 5520919 = 8281379) B8281379
theorem B7361225 : Blo 2179435 7361225 := bstep (se 2 (by rfl) ⟨2760459, by rfl⟩ : syracuseStep 7361225 = 5520919) B5520919
theorem B4907483 : Blo 2179435 4907483 := bstep (se 1 (by rfl) ⟨3680612, by rfl⟩ : syracuseStep 4907483 = 7361225) B7361225
theorem B3271655 : Blo 2179435 3271655 := bstep (se 1 (by rfl) ⟨2453741, by rfl⟩ : syracuseStep 3271655 = 4907483) B4907483
theorem B2181103 : Blo 2179435 2181103 := bstep (se 1 (by rfl) ⟨1635827, by rfl⟩ : syracuseStep 2181103 = 3271655) B3271655
theorem B3271661 : Blo 2179435 3271661 := bbase (se 3 (by rfl) ⟨613436, by rfl⟩ : syracuseStep 3271661 = 1226873) (by norm_num)
theorem B2181107 : Blo 2179435 2181107 := bstep (se 1 (by rfl) ⟨1635830, by rfl⟩ : syracuseStep 2181107 = 3271661) B3271661
theorem B4907501 : Blo 2179435 4907501 := bbase (se 3 (by rfl) ⟨920156, by rfl⟩ : syracuseStep 4907501 = 1840313) (by norm_num)
theorem B3271667 : Blo 2179435 3271667 := bstep (se 1 (by rfl) ⟨2453750, by rfl⟩ : syracuseStep 3271667 = 4907501) B4907501
theorem B2181111 : Blo 2179435 2181111 := bstep (se 1 (by rfl) ⟨1635833, by rfl⟩ : syracuseStep 2181111 = 3271667) B3271667
theorem B5180869 : Blo 2179435 5180869 := bbase (se 4 (by rfl) ⟨485706, by rfl⟩ : syracuseStep 5180869 = 971413) (by norm_num)
theorem B6907825 : Blo 2179435 6907825 := bstep (se 2 (by rfl) ⟨2590434, by rfl⟩ : syracuseStep 6907825 = 5180869) B5180869
theorem B36841733 : Blo 2179435 36841733 := bstep (se 4 (by rfl) ⟨3453912, by rfl⟩ : syracuseStep 36841733 = 6907825) B6907825
theorem B24561155 : Blo 2179435 24561155 := bstep (se 1 (by rfl) ⟨18420866, by rfl⟩ : syracuseStep 24561155 = 36841733) B36841733
theorem B65496413 : Blo 2179435 65496413 := bstep (se 3 (by rfl) ⟨12280577, by rfl⟩ : syracuseStep 65496413 = 24561155) B24561155
theorem B43664275 : Blo 2179435 43664275 := bstep (se 1 (by rfl) ⟨32748206, by rfl⟩ : syracuseStep 43664275 = 65496413) B65496413
theorem B58219033 : Blo 2179435 58219033 := bstep (se 2 (by rfl) ⟨21832137, by rfl⟩ : syracuseStep 58219033 = 43664275) B43664275
theorem B77625377 : Blo 2179435 77625377 := bstep (se 2 (by rfl) ⟨29109516, by rfl⟩ : syracuseStep 77625377 = 58219033) B58219033
theorem B51750251 : Blo 2179435 51750251 := bstep (se 1 (by rfl) ⟨38812688, by rfl⟩ : syracuseStep 51750251 = 77625377) B77625377
theorem B34500167 : Blo 2179435 34500167 := bstep (se 1 (by rfl) ⟨25875125, by rfl⟩ : syracuseStep 34500167 = 51750251) B51750251
theorem B23000111 : Blo 2179435 23000111 := bstep (se 1 (by rfl) ⟨17250083, by rfl⟩ : syracuseStep 23000111 = 34500167) B34500167
theorem B15333407 : Blo 2179435 15333407 := bstep (se 1 (by rfl) ⟨11500055, by rfl⟩ : syracuseStep 15333407 = 23000111) B23000111
theorem B10222271 : Blo 2179435 10222271 := bstep (se 1 (by rfl) ⟨7666703, by rfl⟩ : syracuseStep 10222271 = 15333407) B15333407
theorem B6814847 : Blo 2179435 6814847 := bstep (se 1 (by rfl) ⟨5111135, by rfl⟩ : syracuseStep 6814847 = 10222271) B10222271
theorem B4543231 : Blo 2179435 4543231 := bstep (se 1 (by rfl) ⟨3407423, by rfl⟩ : syracuseStep 4543231 = 6814847) B6814847
theorem B6057641 : Blo 2179435 6057641 := bstep (se 2 (by rfl) ⟨2271615, by rfl⟩ : syracuseStep 6057641 = 4543231) B4543231
theorem B4038427 : Blo 2179435 4038427 := bstep (se 1 (by rfl) ⟨3028820, by rfl⟩ : syracuseStep 4038427 = 6057641) B6057641
theorem B5384569 : Blo 2179435 5384569 := bstep (se 2 (by rfl) ⟨2019213, by rfl⟩ : syracuseStep 5384569 = 4038427) B4038427
theorem B7179425 : Blo 2179435 7179425 := bstep (se 2 (by rfl) ⟨2692284, by rfl⟩ : syracuseStep 7179425 = 5384569) B5384569
theorem B4786283 : Blo 2179435 4786283 := bstep (se 1 (by rfl) ⟨3589712, by rfl⟩ : syracuseStep 4786283 = 7179425) B7179425
theorem B3190855 : Blo 2179435 3190855 := bstep (se 1 (by rfl) ⟨2393141, by rfl⟩ : syracuseStep 3190855 = 4786283) B4786283
theorem B4254473 : Blo 2179435 4254473 := bstep (se 2 (by rfl) ⟨1595427, by rfl⟩ : syracuseStep 4254473 = 3190855) B3190855
theorem B2836315 : Blo 2179435 2836315 := bstep (se 1 (by rfl) ⟨2127236, by rfl⟩ : syracuseStep 2836315 = 4254473) B4254473
theorem B15127013 : Blo 2179435 15127013 := bstep (se 4 (by rfl) ⟨1418157, by rfl⟩ : syracuseStep 15127013 = 2836315) B2836315
theorem B10084675 : Blo 2179435 10084675 := bstep (se 1 (by rfl) ⟨7563506, by rfl⟩ : syracuseStep 10084675 = 15127013) B15127013
theorem B13446233 : Blo 2179435 13446233 := bstep (se 2 (by rfl) ⟨5042337, by rfl⟩ : syracuseStep 13446233 = 10084675) B10084675
theorem B8964155 : Blo 2179435 8964155 := bstep (se 1 (by rfl) ⟨6723116, by rfl⟩ : syracuseStep 8964155 = 13446233) B13446233
theorem B5976103 : Blo 2179435 5976103 := bstep (se 1 (by rfl) ⟨4482077, by rfl⟩ : syracuseStep 5976103 = 8964155) B8964155
theorem B7968137 : Blo 2179435 7968137 := bstep (se 2 (by rfl) ⟨2988051, by rfl⟩ : syracuseStep 7968137 = 5976103) B5976103
theorem B21248365 : Blo 2179435 21248365 := bstep (se 3 (by rfl) ⟨3984068, by rfl⟩ : syracuseStep 21248365 = 7968137) B7968137
theorem B28331153 : Blo 2179435 28331153 := bstep (se 2 (by rfl) ⟨10624182, by rfl⟩ : syracuseStep 28331153 = 21248365) B21248365
theorem B18887435 : Blo 2179435 18887435 := bstep (se 1 (by rfl) ⟨14165576, by rfl⟩ : syracuseStep 18887435 = 28331153) B28331153
theorem B12591623 : Blo 2179435 12591623 := bstep (se 1 (by rfl) ⟨9443717, by rfl⟩ : syracuseStep 12591623 = 18887435) B18887435
theorem B33577661 : Blo 2179435 33577661 := bstep (se 3 (by rfl) ⟨6295811, by rfl⟩ : syracuseStep 33577661 = 12591623) B12591623
theorem B22385107 : Blo 2179435 22385107 := bstep (se 1 (by rfl) ⟨16788830, by rfl⟩ : syracuseStep 22385107 = 33577661) B33577661
theorem B29846809 : Blo 2179435 29846809 := bstep (se 2 (by rfl) ⟨11192553, by rfl⟩ : syracuseStep 29846809 = 22385107) B22385107
theorem B39795745 : Blo 2179435 39795745 := bstep (se 2 (by rfl) ⟨14923404, by rfl⟩ : syracuseStep 39795745 = 29846809) B29846809
theorem B53060993 : Blo 2179435 53060993 := bstep (se 2 (by rfl) ⟨19897872, by rfl⟩ : syracuseStep 53060993 = 39795745) B39795745
theorem B35373995 : Blo 2179435 35373995 := bstep (se 1 (by rfl) ⟨26530496, by rfl⟩ : syracuseStep 35373995 = 53060993) B53060993
theorem B23582663 : Blo 2179435 23582663 := bstep (se 1 (by rfl) ⟨17686997, by rfl⟩ : syracuseStep 23582663 = 35373995) B35373995
theorem B15721775 : Blo 2179435 15721775 := bstep (se 1 (by rfl) ⟨11791331, by rfl⟩ : syracuseStep 15721775 = 23582663) B23582663
theorem B10481183 : Blo 2179435 10481183 := bstep (se 1 (by rfl) ⟨7860887, by rfl⟩ : syracuseStep 10481183 = 15721775) B15721775
theorem B6987455 : Blo 2179435 6987455 := bstep (se 1 (by rfl) ⟨5240591, by rfl⟩ : syracuseStep 6987455 = 10481183) B10481183
theorem B4658303 : Blo 2179435 4658303 := bstep (se 1 (by rfl) ⟨3493727, by rfl⟩ : syracuseStep 4658303 = 6987455) B6987455
theorem B3105535 : Blo 2179435 3105535 := bstep (se 1 (by rfl) ⟨2329151, by rfl⟩ : syracuseStep 3105535 = 4658303) B4658303
theorem B4140713 : Blo 2179435 4140713 := bstep (se 2 (by rfl) ⟨1552767, by rfl⟩ : syracuseStep 4140713 = 3105535) B3105535
theorem B2760475 : Blo 2179435 2760475 := bstep (se 1 (by rfl) ⟨2070356, by rfl⟩ : syracuseStep 2760475 = 4140713) B4140713
theorem B3680633 : Blo 2179435 3680633 := bstep (se 2 (by rfl) ⟨1380237, by rfl⟩ : syracuseStep 3680633 = 2760475) B2760475
theorem B2453755 : Blo 2179435 2453755 := bstep (se 1 (by rfl) ⟨1840316, by rfl⟩ : syracuseStep 2453755 = 3680633) B3680633
theorem B3271673 : Blo 2179435 3271673 := bstep (se 2 (by rfl) ⟨1226877, by rfl⟩ : syracuseStep 3271673 = 2453755) B2453755
theorem B2181115 : Blo 2179435 2181115 := bstep (se 1 (by rfl) ⟨1635836, by rfl⟩ : syracuseStep 2181115 = 3271673) B3271673
theorem B39795797 : Blo 2179435 39795797 := bbase (se 8 (by rfl) ⟨233178, by rfl⟩ : syracuseStep 39795797 = 466357) (by norm_num)
theorem B106122125 : Blo 2179435 106122125 := bstep (se 3 (by rfl) ⟨19897898, by rfl⟩ : syracuseStep 106122125 = 39795797) B39795797
theorem B70748083 : Blo 2179435 70748083 := bstep (se 1 (by rfl) ⟨53061062, by rfl⟩ : syracuseStep 70748083 = 106122125) B106122125
theorem B94330777 : Blo 2179435 94330777 := bstep (se 2 (by rfl) ⟨35374041, by rfl⟩ : syracuseStep 94330777 = 70748083) B70748083
theorem B125774369 : Blo 2179435 125774369 := bstep (se 2 (by rfl) ⟨47165388, by rfl⟩ : syracuseStep 125774369 = 94330777) B94330777
theorem B83849579 : Blo 2179435 83849579 := bstep (se 1 (by rfl) ⟨62887184, by rfl⟩ : syracuseStep 83849579 = 125774369) B125774369
theorem B55899719 : Blo 2179435 55899719 := bstep (se 1 (by rfl) ⟨41924789, by rfl⟩ : syracuseStep 55899719 = 83849579) B83849579
theorem B37266479 : Blo 2179435 37266479 := bstep (se 1 (by rfl) ⟨27949859, by rfl⟩ : syracuseStep 37266479 = 55899719) B55899719
theorem B24844319 : Blo 2179435 24844319 := bstep (se 1 (by rfl) ⟨18633239, by rfl⟩ : syracuseStep 24844319 = 37266479) B37266479
theorem B16562879 : Blo 2179435 16562879 := bstep (se 1 (by rfl) ⟨12422159, by rfl⟩ : syracuseStep 16562879 = 24844319) B24844319
theorem B11041919 : Blo 2179435 11041919 := bstep (se 1 (by rfl) ⟨8281439, by rfl⟩ : syracuseStep 11041919 = 16562879) B16562879
theorem B7361279 : Blo 2179435 7361279 := bstep (se 1 (by rfl) ⟨5520959, by rfl⟩ : syracuseStep 7361279 = 11041919) B11041919
theorem B4907519 : Blo 2179435 4907519 := bstep (se 1 (by rfl) ⟨3680639, by rfl⟩ : syracuseStep 4907519 = 7361279) B7361279
theorem B3271679 : Blo 2179435 3271679 := bstep (se 1 (by rfl) ⟨2453759, by rfl⟩ : syracuseStep 3271679 = 4907519) B4907519
theorem B2181119 : Blo 2179435 2181119 := bstep (se 1 (by rfl) ⟨1635839, by rfl⟩ : syracuseStep 2181119 = 3271679) B3271679
theorem B3271685 : Blo 2179435 3271685 := bbase (se 4 (by rfl) ⟨306720, by rfl⟩ : syracuseStep 3271685 = 613441) (by norm_num)
theorem B2181123 : Blo 2179435 2181123 := bstep (se 1 (by rfl) ⟨1635842, by rfl⟩ : syracuseStep 2181123 = 3271685) B3271685
theorem B3680653 : Blo 2179435 3680653 := bbase (se 3 (by rfl) ⟨690122, by rfl⟩ : syracuseStep 3680653 = 1380245) (by norm_num)
theorem B4907537 : Blo 2179435 4907537 := bstep (se 2 (by rfl) ⟨1840326, by rfl⟩ : syracuseStep 4907537 = 3680653) B3680653
theorem B3271691 : Blo 2179435 3271691 := bstep (se 1 (by rfl) ⟨2453768, by rfl⟩ : syracuseStep 3271691 = 4907537) B4907537
theorem B2181127 : Blo 2179435 2181127 := bstep (se 1 (by rfl) ⟨1635845, by rfl⟩ : syracuseStep 2181127 = 3271691) B3271691
theorem B2453773 : Blo 2179435 2453773 := bbase (se 3 (by rfl) ⟨460082, by rfl⟩ : syracuseStep 2453773 = 920165) (by norm_num)
theorem B3271697 : Blo 2179435 3271697 := bstep (se 2 (by rfl) ⟨1226886, by rfl⟩ : syracuseStep 3271697 = 2453773) B2453773
theorem B2181131 : Blo 2179435 2181131 := bstep (se 1 (by rfl) ⟨1635848, by rfl⟩ : syracuseStep 2181131 = 3271697) B3271697
theorem B7361333 : Blo 2179435 7361333 := bbase (se 5 (by rfl) ⟨345062, by rfl⟩ : syracuseStep 7361333 = 690125) (by norm_num)
theorem B4907555 : Blo 2179435 4907555 := bstep (se 1 (by rfl) ⟨3680666, by rfl⟩ : syracuseStep 4907555 = 7361333) B7361333
theorem B3271703 : Blo 2179435 3271703 := bstep (se 1 (by rfl) ⟨2453777, by rfl⟩ : syracuseStep 3271703 = 4907555) B4907555
theorem B2181135 : Blo 2179435 2181135 := bstep (se 1 (by rfl) ⟨1635851, by rfl⟩ : syracuseStep 2181135 = 3271703) B3271703
theorem B3271709 : Blo 2179435 3271709 := bbase (se 3 (by rfl) ⟨613445, by rfl⟩ : syracuseStep 3271709 = 1226891) (by norm_num)
theorem B2181139 : Blo 2179435 2181139 := bstep (se 1 (by rfl) ⟨1635854, by rfl⟩ : syracuseStep 2181139 = 3271709) B3271709
theorem B4907573 : Blo 2179435 4907573 := bbase (se 5 (by rfl) ⟨230042, by rfl⟩ : syracuseStep 4907573 = 460085) (by norm_num)
theorem B3271715 : Blo 2179435 3271715 := bstep (se 1 (by rfl) ⟨2453786, by rfl⟩ : syracuseStep 3271715 = 4907573) B4907573
theorem B2181143 : Blo 2179435 2181143 := bstep (se 1 (by rfl) ⟨1635857, by rfl⟩ : syracuseStep 2181143 = 3271715) B3271715
theorem B9316741 : Blo 2179435 9316741 := bbase (se 4 (by rfl) ⟨873444, by rfl⟩ : syracuseStep 9316741 = 1746889) (by norm_num)
theorem B12422321 : Blo 2179435 12422321 := bstep (se 2 (by rfl) ⟨4658370, by rfl⟩ : syracuseStep 12422321 = 9316741) B9316741
theorem B8281547 : Blo 2179435 8281547 := bstep (se 1 (by rfl) ⟨6211160, by rfl⟩ : syracuseStep 8281547 = 12422321) B12422321
theorem B5521031 : Blo 2179435 5521031 := bstep (se 1 (by rfl) ⟨4140773, by rfl⟩ : syracuseStep 5521031 = 8281547) B8281547
theorem B3680687 : Blo 2179435 3680687 := bstep (se 1 (by rfl) ⟨2760515, by rfl⟩ : syracuseStep 3680687 = 5521031) B5521031
theorem B2453791 : Blo 2179435 2453791 := bstep (se 1 (by rfl) ⟨1840343, by rfl⟩ : syracuseStep 2453791 = 3680687) B3680687
theorem B3271721 : Blo 2179435 3271721 := bstep (se 2 (by rfl) ⟨1226895, by rfl⟩ : syracuseStep 3271721 = 2453791) B2453791
theorem B2181147 : Blo 2179435 2181147 := bstep (se 1 (by rfl) ⟨1635860, by rfl⟩ : syracuseStep 2181147 = 3271721) B3271721
theorem B9316757 : Blo 2179435 9316757 := bbase (se 6 (by rfl) ⟨218361, by rfl⟩ : syracuseStep 9316757 = 436723) (by norm_num)
theorem B6211171 : Blo 2179435 6211171 := bstep (se 1 (by rfl) ⟨4658378, by rfl⟩ : syracuseStep 6211171 = 9316757) B9316757
theorem B8281561 : Blo 2179435 8281561 := bstep (se 2 (by rfl) ⟨3105585, by rfl⟩ : syracuseStep 8281561 = 6211171) B6211171
theorem B11042081 : Blo 2179435 11042081 := bstep (se 2 (by rfl) ⟨4140780, by rfl⟩ : syracuseStep 11042081 = 8281561) B8281561
theorem B7361387 : Blo 2179435 7361387 := bstep (se 1 (by rfl) ⟨5521040, by rfl⟩ : syracuseStep 7361387 = 11042081) B11042081
theorem B4907591 : Blo 2179435 4907591 := bstep (se 1 (by rfl) ⟨3680693, by rfl⟩ : syracuseStep 4907591 = 7361387) B7361387
theorem B3271727 : Blo 2179435 3271727 := bstep (se 1 (by rfl) ⟨2453795, by rfl⟩ : syracuseStep 3271727 = 4907591) B4907591
theorem B2181151 : Blo 2179435 2181151 := bstep (se 1 (by rfl) ⟨1635863, by rfl⟩ : syracuseStep 2181151 = 3271727) B3271727
theorem B3271733 : Blo 2179435 3271733 := bbase (se 5 (by rfl) ⟨153362, by rfl⟩ : syracuseStep 3271733 = 306725) (by norm_num)
theorem B2181155 : Blo 2179435 2181155 := bstep (se 1 (by rfl) ⟨1635866, by rfl⟩ : syracuseStep 2181155 = 3271733) B3271733
theorem B5521061 : Blo 2179435 5521061 := bbase (se 4 (by rfl) ⟨517599, by rfl⟩ : syracuseStep 5521061 = 1035199) (by norm_num)
theorem B3680707 : Blo 2179435 3680707 := bstep (se 1 (by rfl) ⟨2760530, by rfl⟩ : syracuseStep 3680707 = 5521061) B5521061
theorem B4907609 : Blo 2179435 4907609 := bstep (se 2 (by rfl) ⟨1840353, by rfl⟩ : syracuseStep 4907609 = 3680707) B3680707
theorem B3271739 : Blo 2179435 3271739 := bstep (se 1 (by rfl) ⟨2453804, by rfl⟩ : syracuseStep 3271739 = 4907609) B4907609
theorem B2181159 : Blo 2179435 2181159 := bstep (se 1 (by rfl) ⟨1635869, by rfl⟩ : syracuseStep 2181159 = 3271739) B3271739
theorem B2453809 : Blo 2179435 2453809 := bbase (se 2 (by rfl) ⟨920178, by rfl⟩ : syracuseStep 2453809 = 1840357) (by norm_num)
theorem B3271745 : Blo 2179435 3271745 := bstep (se 2 (by rfl) ⟨1226904, by rfl⟩ : syracuseStep 3271745 = 2453809) B2453809
theorem B2181163 : Blo 2179435 2181163 := bstep (se 1 (by rfl) ⟨1635872, by rfl⟩ : syracuseStep 2181163 = 3271745) B3271745
theorem B4658413 : Blo 2179435 4658413 := bbase (se 3 (by rfl) ⟨873452, by rfl⟩ : syracuseStep 4658413 = 1746905) (by norm_num)
theorem B6211217 : Blo 2179435 6211217 := bstep (se 2 (by rfl) ⟨2329206, by rfl⟩ : syracuseStep 6211217 = 4658413) B4658413
theorem B4140811 : Blo 2179435 4140811 := bstep (se 1 (by rfl) ⟨3105608, by rfl⟩ : syracuseStep 4140811 = 6211217) B6211217
theorem B5521081 : Blo 2179435 5521081 := bstep (se 2 (by rfl) ⟨2070405, by rfl⟩ : syracuseStep 5521081 = 4140811) B4140811
theorem B7361441 : Blo 2179435 7361441 := bstep (se 2 (by rfl) ⟨2760540, by rfl⟩ : syracuseStep 7361441 = 5521081) B5521081
theorem B4907627 : Blo 2179435 4907627 := bstep (se 1 (by rfl) ⟨3680720, by rfl⟩ : syracuseStep 4907627 = 7361441) B7361441
theorem B3271751 : Blo 2179435 3271751 := bstep (se 1 (by rfl) ⟨2453813, by rfl⟩ : syracuseStep 3271751 = 4907627) B4907627
theorem B2181167 : Blo 2179435 2181167 := bstep (se 1 (by rfl) ⟨1635875, by rfl⟩ : syracuseStep 2181167 = 3271751) B3271751
theorem B3271757 : Blo 2179435 3271757 := bbase (se 3 (by rfl) ⟨613454, by rfl⟩ : syracuseStep 3271757 = 1226909) (by norm_num)
theorem B2181171 : Blo 2179435 2181171 := bstep (se 1 (by rfl) ⟨1635878, by rfl⟩ : syracuseStep 2181171 = 3271757) B3271757
theorem B4907645 : Blo 2179435 4907645 := bbase (se 3 (by rfl) ⟨920183, by rfl⟩ : syracuseStep 4907645 = 1840367) (by norm_num)
theorem B3271763 : Blo 2179435 3271763 := bstep (se 1 (by rfl) ⟨2453822, by rfl⟩ : syracuseStep 3271763 = 4907645) B4907645
theorem B2181175 : Blo 2179435 2181175 := bstep (se 1 (by rfl) ⟨1635881, by rfl⟩ : syracuseStep 2181175 = 3271763) B3271763
theorem B3680741 : Blo 2179435 3680741 := bbase (se 4 (by rfl) ⟨345069, by rfl⟩ : syracuseStep 3680741 = 690139) (by norm_num)
theorem B2453827 : Blo 2179435 2453827 := bstep (se 1 (by rfl) ⟨1840370, by rfl⟩ : syracuseStep 2453827 = 3680741) B3680741
theorem B3271769 : Blo 2179435 3271769 := bstep (se 2 (by rfl) ⟨1226913, by rfl⟩ : syracuseStep 3271769 = 2453827) B2453827
theorem B2181179 : Blo 2179435 2181179 := bstep (se 1 (by rfl) ⟨1635884, by rfl⟩ : syracuseStep 2181179 = 3271769) B3271769
theorem B15722261 : Blo 2179435 15722261 := bbase (se 6 (by rfl) ⟨368490, by rfl⟩ : syracuseStep 15722261 = 736981) (by norm_num)
theorem B10481507 : Blo 2179435 10481507 := bstep (se 1 (by rfl) ⟨7861130, by rfl⟩ : syracuseStep 10481507 = 15722261) B15722261
theorem B6987671 : Blo 2179435 6987671 := bstep (se 1 (by rfl) ⟨5240753, by rfl⟩ : syracuseStep 6987671 = 10481507) B10481507
theorem B4658447 : Blo 2179435 4658447 := bstep (se 1 (by rfl) ⟨3493835, by rfl⟩ : syracuseStep 4658447 = 6987671) B6987671
theorem B3105631 : Blo 2179435 3105631 := bstep (se 1 (by rfl) ⟨2329223, by rfl⟩ : syracuseStep 3105631 = 4658447) B4658447
theorem B16563365 : Blo 2179435 16563365 := bstep (se 4 (by rfl) ⟨1552815, by rfl⟩ : syracuseStep 16563365 = 3105631) B3105631
theorem B11042243 : Blo 2179435 11042243 := bstep (se 1 (by rfl) ⟨8281682, by rfl⟩ : syracuseStep 11042243 = 16563365) B16563365
theorem B7361495 : Blo 2179435 7361495 := bstep (se 1 (by rfl) ⟨5521121, by rfl⟩ : syracuseStep 7361495 = 11042243) B11042243
theorem B4907663 : Blo 2179435 4907663 := bstep (se 1 (by rfl) ⟨3680747, by rfl⟩ : syracuseStep 4907663 = 7361495) B7361495
theorem B3271775 : Blo 2179435 3271775 := bstep (se 1 (by rfl) ⟨2453831, by rfl⟩ : syracuseStep 3271775 = 4907663) B4907663
theorem B2181183 : Blo 2179435 2181183 := bstep (se 1 (by rfl) ⟨1635887, by rfl⟩ : syracuseStep 2181183 = 3271775) B3271775
theorem B3271781 : Blo 2179435 3271781 := bbase (se 4 (by rfl) ⟨306729, by rfl⟩ : syracuseStep 3271781 = 613459) (by norm_num)
theorem B2181187 : Blo 2179435 2181187 := bstep (se 1 (by rfl) ⟨1635890, by rfl⟩ : syracuseStep 2181187 = 3271781) B3271781
theorem B3930581 : Blo 2179435 3930581 := bbase (se 7 (by rfl) ⟨46061, by rfl⟩ : syracuseStep 3930581 = 92123) (by norm_num)
theorem B2620387 : Blo 2179435 2620387 := bstep (se 1 (by rfl) ⟨1965290, by rfl⟩ : syracuseStep 2620387 = 3930581) B3930581
theorem B3493849 : Blo 2179435 3493849 := bstep (se 2 (by rfl) ⟨1310193, by rfl⟩ : syracuseStep 3493849 = 2620387) B2620387
theorem B4658465 : Blo 2179435 4658465 := bstep (se 2 (by rfl) ⟨1746924, by rfl⟩ : syracuseStep 4658465 = 3493849) B3493849
theorem B3105643 : Blo 2179435 3105643 := bstep (se 1 (by rfl) ⟨2329232, by rfl⟩ : syracuseStep 3105643 = 4658465) B4658465
theorem B4140857 : Blo 2179435 4140857 := bstep (se 2 (by rfl) ⟨1552821, by rfl⟩ : syracuseStep 4140857 = 3105643) B3105643
theorem B2760571 : Blo 2179435 2760571 := bstep (se 1 (by rfl) ⟨2070428, by rfl⟩ : syracuseStep 2760571 = 4140857) B4140857
theorem B3680761 : Blo 2179435 3680761 := bstep (se 2 (by rfl) ⟨1380285, by rfl⟩ : syracuseStep 3680761 = 2760571) B2760571
theorem B4907681 : Blo 2179435 4907681 := bstep (se 2 (by rfl) ⟨1840380, by rfl⟩ : syracuseStep 4907681 = 3680761) B3680761
theorem B3271787 : Blo 2179435 3271787 := bstep (se 1 (by rfl) ⟨2453840, by rfl⟩ : syracuseStep 3271787 = 4907681) B4907681
theorem B2181191 : Blo 2179435 2181191 := bstep (se 1 (by rfl) ⟨1635893, by rfl⟩ : syracuseStep 2181191 = 3271787) B3271787
theorem B2453845 : Blo 2179435 2453845 := bbase (se 10 (by rfl) ⟨3594, by rfl⟩ : syracuseStep 2453845 = 7189) (by norm_num)
theorem B3271793 : Blo 2179435 3271793 := bstep (se 2 (by rfl) ⟨1226922, by rfl⟩ : syracuseStep 3271793 = 2453845) B2453845
theorem B2181195 : Blo 2179435 2181195 := bstep (se 1 (by rfl) ⟨1635896, by rfl⟩ : syracuseStep 2181195 = 3271793) B3271793
theorem B2760581 : Blo 2179435 2760581 := bbase (se 4 (by rfl) ⟨258804, by rfl⟩ : syracuseStep 2760581 = 517609) (by norm_num)
theorem B7361549 : Blo 2179435 7361549 := bstep (se 3 (by rfl) ⟨1380290, by rfl⟩ : syracuseStep 7361549 = 2760581) B2760581
theorem B4907699 : Blo 2179435 4907699 := bstep (se 1 (by rfl) ⟨3680774, by rfl⟩ : syracuseStep 4907699 = 7361549) B7361549
theorem B3271799 : Blo 2179435 3271799 := bstep (se 1 (by rfl) ⟨2453849, by rfl⟩ : syracuseStep 3271799 = 4907699) B4907699
theorem B2181199 : Blo 2179435 2181199 := bstep (se 1 (by rfl) ⟨1635899, by rfl⟩ : syracuseStep 2181199 = 3271799) B3271799
theorem B3271805 : Blo 2179435 3271805 := bbase (se 3 (by rfl) ⟨613463, by rfl⟩ : syracuseStep 3271805 = 1226927) (by norm_num)
theorem B2181203 : Blo 2179435 2181203 := bstep (se 1 (by rfl) ⟨1635902, by rfl⟩ : syracuseStep 2181203 = 3271805) B3271805
theorem B4907717 : Blo 2179435 4907717 := bbase (se 4 (by rfl) ⟨460098, by rfl⟩ : syracuseStep 4907717 = 920197) (by norm_num)
theorem B3271811 : Blo 2179435 3271811 := bstep (se 1 (by rfl) ⟨2453858, by rfl⟩ : syracuseStep 3271811 = 4907717) B4907717
theorem B2181207 : Blo 2179435 2181207 := bstep (se 1 (by rfl) ⟨1635905, by rfl⟩ : syracuseStep 2181207 = 3271811) B3271811
theorem B20963285 : Blo 2179435 20963285 := bbase (se 7 (by rfl) ⟨245663, by rfl⟩ : syracuseStep 20963285 = 491327) (by norm_num)
theorem B13975523 : Blo 2179435 13975523 := bstep (se 1 (by rfl) ⟨10481642, by rfl⟩ : syracuseStep 13975523 = 20963285) B20963285
theorem B9317015 : Blo 2179435 9317015 := bstep (se 1 (by rfl) ⟨6987761, by rfl⟩ : syracuseStep 9317015 = 13975523) B13975523
theorem B6211343 : Blo 2179435 6211343 := bstep (se 1 (by rfl) ⟨4658507, by rfl⟩ : syracuseStep 6211343 = 9317015) B9317015
theorem B4140895 : Blo 2179435 4140895 := bstep (se 1 (by rfl) ⟨3105671, by rfl⟩ : syracuseStep 4140895 = 6211343) B6211343
theorem B5521193 : Blo 2179435 5521193 := bstep (se 2 (by rfl) ⟨2070447, by rfl⟩ : syracuseStep 5521193 = 4140895) B4140895
theorem B3680795 : Blo 2179435 3680795 := bstep (se 1 (by rfl) ⟨2760596, by rfl⟩ : syracuseStep 3680795 = 5521193) B5521193
theorem B2453863 : Blo 2179435 2453863 := bstep (se 1 (by rfl) ⟨1840397, by rfl⟩ : syracuseStep 2453863 = 3680795) B3680795
theorem B3271817 : Blo 2179435 3271817 := bstep (se 2 (by rfl) ⟨1226931, by rfl⟩ : syracuseStep 3271817 = 2453863) B2453863
theorem B2181211 : Blo 2179435 2181211 := bstep (se 1 (by rfl) ⟨1635908, by rfl⟩ : syracuseStep 2181211 = 3271817) B3271817
theorem B11042405 : Blo 2179435 11042405 := bbase (se 4 (by rfl) ⟨1035225, by rfl⟩ : syracuseStep 11042405 = 2070451) (by norm_num)
theorem B7361603 : Blo 2179435 7361603 := bstep (se 1 (by rfl) ⟨5521202, by rfl⟩ : syracuseStep 7361603 = 11042405) B11042405
theorem B4907735 : Blo 2179435 4907735 := bstep (se 1 (by rfl) ⟨3680801, by rfl⟩ : syracuseStep 4907735 = 7361603) B7361603
theorem B3271823 : Blo 2179435 3271823 := bstep (se 1 (by rfl) ⟨2453867, by rfl⟩ : syracuseStep 3271823 = 4907735) B4907735
theorem B2181215 : Blo 2179435 2181215 := bstep (se 1 (by rfl) ⟨1635911, by rfl⟩ : syracuseStep 2181215 = 3271823) B3271823
theorem B3271829 : Blo 2179435 3271829 := bbase (se 6 (by rfl) ⟨76683, by rfl⟩ : syracuseStep 3271829 = 153367) (by norm_num)
theorem B2181219 : Blo 2179435 2181219 := bstep (se 1 (by rfl) ⟨1635914, by rfl⟩ : syracuseStep 2181219 = 3271829) B3271829
theorem B15722549 : Blo 2179435 15722549 := bbase (se 5 (by rfl) ⟨736994, by rfl⟩ : syracuseStep 15722549 = 1473989) (by norm_num)
theorem B10481699 : Blo 2179435 10481699 := bstep (se 1 (by rfl) ⟨7861274, by rfl⟩ : syracuseStep 10481699 = 15722549) B15722549
theorem B6987799 : Blo 2179435 6987799 := bstep (se 1 (by rfl) ⟨5240849, by rfl⟩ : syracuseStep 6987799 = 10481699) B10481699
theorem B9317065 : Blo 2179435 9317065 := bstep (se 2 (by rfl) ⟨3493899, by rfl⟩ : syracuseStep 9317065 = 6987799) B6987799
theorem B12422753 : Blo 2179435 12422753 := bstep (se 2 (by rfl) ⟨4658532, by rfl⟩ : syracuseStep 12422753 = 9317065) B9317065
theorem B8281835 : Blo 2179435 8281835 := bstep (se 1 (by rfl) ⟨6211376, by rfl⟩ : syracuseStep 8281835 = 12422753) B12422753
theorem B5521223 : Blo 2179435 5521223 := bstep (se 1 (by rfl) ⟨4140917, by rfl⟩ : syracuseStep 5521223 = 8281835) B8281835
theorem B3680815 : Blo 2179435 3680815 := bstep (se 1 (by rfl) ⟨2760611, by rfl⟩ : syracuseStep 3680815 = 5521223) B5521223
theorem B4907753 : Blo 2179435 4907753 := bstep (se 2 (by rfl) ⟨1840407, by rfl⟩ : syracuseStep 4907753 = 3680815) B3680815
theorem B3271835 : Blo 2179435 3271835 := bstep (se 1 (by rfl) ⟨2453876, by rfl⟩ : syracuseStep 3271835 = 4907753) B4907753
theorem B2181223 : Blo 2179435 2181223 := bstep (se 1 (by rfl) ⟨1635917, by rfl⟩ : syracuseStep 2181223 = 3271835) B3271835
theorem B2453881 : Blo 2179435 2453881 := bbase (se 2 (by rfl) ⟨920205, by rfl⟩ : syracuseStep 2453881 = 1840411) (by norm_num)
theorem B3271841 : Blo 2179435 3271841 := bstep (se 2 (by rfl) ⟨1226940, by rfl⟩ : syracuseStep 3271841 = 2453881) B2453881
theorem B2181227 : Blo 2179435 2181227 := bstep (se 1 (by rfl) ⟨1635920, by rfl⟩ : syracuseStep 2181227 = 3271841) B3271841
theorem B22386293 : Blo 2179435 22386293 := bbase (se 5 (by rfl) ⟨1049357, by rfl⟩ : syracuseStep 22386293 = 2098715) (by norm_num)
theorem B14924195 : Blo 2179435 14924195 := bstep (se 1 (by rfl) ⟨11193146, by rfl⟩ : syracuseStep 14924195 = 22386293) B22386293
theorem B9949463 : Blo 2179435 9949463 := bstep (se 1 (by rfl) ⟨7462097, by rfl⟩ : syracuseStep 9949463 = 14924195) B14924195
theorem B6632975 : Blo 2179435 6632975 := bstep (se 1 (by rfl) ⟨4974731, by rfl⟩ : syracuseStep 6632975 = 9949463) B9949463
theorem B17687933 : Blo 2179435 17687933 := bstep (se 3 (by rfl) ⟨3316487, by rfl⟩ : syracuseStep 17687933 = 6632975) B6632975
theorem B11791955 : Blo 2179435 11791955 := bstep (se 1 (by rfl) ⟨8843966, by rfl⟩ : syracuseStep 11791955 = 17687933) B17687933
theorem B7861303 : Blo 2179435 7861303 := bstep (se 1 (by rfl) ⟨5895977, by rfl⟩ : syracuseStep 7861303 = 11791955) B11791955
theorem B10481737 : Blo 2179435 10481737 := bstep (se 2 (by rfl) ⟨3930651, by rfl⟩ : syracuseStep 10481737 = 7861303) B7861303
theorem B13975649 : Blo 2179435 13975649 := bstep (se 2 (by rfl) ⟨5240868, by rfl⟩ : syracuseStep 13975649 = 10481737) B10481737
theorem B9317099 : Blo 2179435 9317099 := bstep (se 1 (by rfl) ⟨6987824, by rfl⟩ : syracuseStep 9317099 = 13975649) B13975649
theorem B6211399 : Blo 2179435 6211399 := bstep (se 1 (by rfl) ⟨4658549, by rfl⟩ : syracuseStep 6211399 = 9317099) B9317099
theorem B8281865 : Blo 2179435 8281865 := bstep (se 2 (by rfl) ⟨3105699, by rfl⟩ : syracuseStep 8281865 = 6211399) B6211399
theorem B5521243 : Blo 2179435 5521243 := bstep (se 1 (by rfl) ⟨4140932, by rfl⟩ : syracuseStep 5521243 = 8281865) B8281865
theorem B7361657 : Blo 2179435 7361657 := bstep (se 2 (by rfl) ⟨2760621, by rfl⟩ : syracuseStep 7361657 = 5521243) B5521243
theorem B4907771 : Blo 2179435 4907771 := bstep (se 1 (by rfl) ⟨3680828, by rfl⟩ : syracuseStep 4907771 = 7361657) B7361657
theorem B3271847 : Blo 2179435 3271847 := bstep (se 1 (by rfl) ⟨2453885, by rfl⟩ : syracuseStep 3271847 = 4907771) B4907771
theorem B2181231 : Blo 2179435 2181231 := bstep (se 1 (by rfl) ⟨1635923, by rfl⟩ : syracuseStep 2181231 = 3271847) B3271847
theorem B3271853 : Blo 2179435 3271853 := bbase (se 3 (by rfl) ⟨613472, by rfl⟩ : syracuseStep 3271853 = 1226945) (by norm_num)
theorem B2181235 : Blo 2179435 2181235 := bstep (se 1 (by rfl) ⟨1635926, by rfl⟩ : syracuseStep 2181235 = 3271853) B3271853
theorem B4907789 : Blo 2179435 4907789 := bbase (se 3 (by rfl) ⟨920210, by rfl⟩ : syracuseStep 4907789 = 1840421) (by norm_num)
theorem B3271859 : Blo 2179435 3271859 := bstep (se 1 (by rfl) ⟨2453894, by rfl⟩ : syracuseStep 3271859 = 4907789) B4907789
theorem B2181239 : Blo 2179435 2181239 := bstep (se 1 (by rfl) ⟨1635929, by rfl⟩ : syracuseStep 2181239 = 3271859) B3271859
theorem B2760637 : Blo 2179435 2760637 := bbase (se 3 (by rfl) ⟨517619, by rfl⟩ : syracuseStep 2760637 = 1035239) (by norm_num)
theorem B3680849 : Blo 2179435 3680849 := bstep (se 2 (by rfl) ⟨1380318, by rfl⟩ : syracuseStep 3680849 = 2760637) B2760637
theorem B2453899 : Blo 2179435 2453899 := bstep (se 1 (by rfl) ⟨1840424, by rfl⟩ : syracuseStep 2453899 = 3680849) B3680849
theorem B3271865 : Blo 2179435 3271865 := bstep (se 2 (by rfl) ⟨1226949, by rfl⟩ : syracuseStep 3271865 = 2453899) B2453899
theorem B2181243 : Blo 2179435 2181243 := bstep (se 1 (by rfl) ⟨1635932, by rfl⟩ : syracuseStep 2181243 = 3271865) B3271865
theorem B10481813 : Blo 2179435 10481813 := bbase (se 6 (by rfl) ⟨245667, by rfl⟩ : syracuseStep 10481813 = 491335) (by norm_num)
theorem B6987875 : Blo 2179435 6987875 := bstep (se 1 (by rfl) ⟨5240906, by rfl⟩ : syracuseStep 6987875 = 10481813) B10481813
theorem B18634333 : Blo 2179435 18634333 := bstep (se 3 (by rfl) ⟨3493937, by rfl⟩ : syracuseStep 18634333 = 6987875) B6987875
theorem B24845777 : Blo 2179435 24845777 := bstep (se 2 (by rfl) ⟨9317166, by rfl⟩ : syracuseStep 24845777 = 18634333) B18634333
theorem B16563851 : Blo 2179435 16563851 := bstep (se 1 (by rfl) ⟨12422888, by rfl⟩ : syracuseStep 16563851 = 24845777) B24845777
theorem B11042567 : Blo 2179435 11042567 := bstep (se 1 (by rfl) ⟨8281925, by rfl⟩ : syracuseStep 11042567 = 16563851) B16563851
theorem B7361711 : Blo 2179435 7361711 := bstep (se 1 (by rfl) ⟨5521283, by rfl⟩ : syracuseStep 7361711 = 11042567) B11042567
theorem B4907807 : Blo 2179435 4907807 := bstep (se 1 (by rfl) ⟨3680855, by rfl⟩ : syracuseStep 4907807 = 7361711) B7361711
theorem B3271871 : Blo 2179435 3271871 := bstep (se 1 (by rfl) ⟨2453903, by rfl⟩ : syracuseStep 3271871 = 4907807) B4907807
theorem B2181247 : Blo 2179435 2181247 := bstep (se 1 (by rfl) ⟨1635935, by rfl⟩ : syracuseStep 2181247 = 3271871) B3271871
theorem B3271877 : Blo 2179435 3271877 := bbase (se 4 (by rfl) ⟨306738, by rfl⟩ : syracuseStep 3271877 = 613477) (by norm_num)
theorem B2181251 : Blo 2179435 2181251 := bstep (se 1 (by rfl) ⟨1635938, by rfl⟩ : syracuseStep 2181251 = 3271877) B3271877
theorem B3680869 : Blo 2179435 3680869 := bbase (se 4 (by rfl) ⟨345081, by rfl⟩ : syracuseStep 3680869 = 690163) (by norm_num)
theorem B4907825 : Blo 2179435 4907825 := bstep (se 2 (by rfl) ⟨1840434, by rfl⟩ : syracuseStep 4907825 = 3680869) B3680869
theorem B3271883 : Blo 2179435 3271883 := bstep (se 1 (by rfl) ⟨2453912, by rfl⟩ : syracuseStep 3271883 = 4907825) B4907825
theorem B2181255 : Blo 2179435 2181255 := bstep (se 1 (by rfl) ⟨1635941, by rfl⟩ : syracuseStep 2181255 = 3271883) B3271883
theorem B2453917 : Blo 2179435 2453917 := bbase (se 3 (by rfl) ⟨460109, by rfl⟩ : syracuseStep 2453917 = 920219) (by norm_num)
theorem B3271889 : Blo 2179435 3271889 := bstep (se 2 (by rfl) ⟨1226958, by rfl⟩ : syracuseStep 3271889 = 2453917) B2453917
theorem B2181259 : Blo 2179435 2181259 := bstep (se 1 (by rfl) ⟨1635944, by rfl⟩ : syracuseStep 2181259 = 3271889) B3271889
theorem B7361765 : Blo 2179435 7361765 := bbase (se 4 (by rfl) ⟨690165, by rfl⟩ : syracuseStep 7361765 = 1380331) (by norm_num)
theorem B4907843 : Blo 2179435 4907843 := bstep (se 1 (by rfl) ⟨3680882, by rfl⟩ : syracuseStep 4907843 = 7361765) B7361765
theorem B3271895 : Blo 2179435 3271895 := bstep (se 1 (by rfl) ⟨2453921, by rfl⟩ : syracuseStep 3271895 = 4907843) B4907843
theorem B2181263 : Blo 2179435 2181263 := bstep (se 1 (by rfl) ⟨1635947, by rfl⟩ : syracuseStep 2181263 = 3271895) B3271895
theorem B3271901 : Blo 2179435 3271901 := bbase (se 3 (by rfl) ⟨613481, by rfl⟩ : syracuseStep 3271901 = 1226963) (by norm_num)
theorem B2181267 : Blo 2179435 2181267 := bstep (se 1 (by rfl) ⟨1635950, by rfl⟩ : syracuseStep 2181267 = 3271901) B3271901
theorem B4907861 : Blo 2179435 4907861 := bbase (se 9 (by rfl) ⟨14378, by rfl⟩ : syracuseStep 4907861 = 28757) (by norm_num)
theorem B3271907 : Blo 2179435 3271907 := bstep (se 1 (by rfl) ⟨2453930, by rfl⟩ : syracuseStep 3271907 = 4907861) B4907861
theorem B2181271 : Blo 2179435 2181271 := bstep (se 1 (by rfl) ⟨1635953, by rfl⟩ : syracuseStep 2181271 = 3271907) B3271907
theorem B6211525 : Blo 2179435 6211525 := bbase (se 4 (by rfl) ⟨582330, by rfl⟩ : syracuseStep 6211525 = 1164661) (by norm_num)
theorem B8282033 : Blo 2179435 8282033 := bstep (se 2 (by rfl) ⟨3105762, by rfl⟩ : syracuseStep 8282033 = 6211525) B6211525
theorem B5521355 : Blo 2179435 5521355 := bstep (se 1 (by rfl) ⟨4141016, by rfl⟩ : syracuseStep 5521355 = 8282033) B8282033
theorem B3680903 : Blo 2179435 3680903 := bstep (se 1 (by rfl) ⟨2760677, by rfl⟩ : syracuseStep 3680903 = 5521355) B5521355
theorem B2453935 : Blo 2179435 2453935 := bstep (se 1 (by rfl) ⟨1840451, by rfl⟩ : syracuseStep 2453935 = 3680903) B3680903
theorem B3271913 : Blo 2179435 3271913 := bstep (se 2 (by rfl) ⟨1226967, by rfl⟩ : syracuseStep 3271913 = 2453935) B2453935
theorem B2181275 : Blo 2179435 2181275 := bstep (se 1 (by rfl) ⟨1635956, by rfl⟩ : syracuseStep 2181275 = 3271913) B3271913
theorem B68076629 : Blo 2179435 68076629 := bbase (se 8 (by rfl) ⟨398886, by rfl⟩ : syracuseStep 68076629 = 797773) (by norm_num)
theorem B45384419 : Blo 2179435 45384419 := bstep (se 1 (by rfl) ⟨34038314, by rfl⟩ : syracuseStep 45384419 = 68076629) B68076629
theorem B121025117 : Blo 2179435 121025117 := bstep (se 3 (by rfl) ⟨22692209, by rfl⟩ : syracuseStep 121025117 = 45384419) B45384419
theorem B80683411 : Blo 2179435 80683411 := bstep (se 1 (by rfl) ⟨60512558, by rfl⟩ : syracuseStep 80683411 = 121025117) B121025117
theorem B107577881 : Blo 2179435 107577881 := bstep (se 2 (by rfl) ⟨40341705, by rfl⟩ : syracuseStep 107577881 = 80683411) B80683411
theorem B71718587 : Blo 2179435 71718587 := bstep (se 1 (by rfl) ⟨53788940, by rfl⟩ : syracuseStep 71718587 = 107577881) B107577881
theorem B47812391 : Blo 2179435 47812391 := bstep (se 1 (by rfl) ⟨35859293, by rfl⟩ : syracuseStep 47812391 = 71718587) B71718587
theorem B31874927 : Blo 2179435 31874927 := bstep (se 1 (by rfl) ⟨23906195, by rfl⟩ : syracuseStep 31874927 = 47812391) B47812391
theorem B339999221 : Blo 2179435 339999221 := bstep (se 5 (by rfl) ⟨15937463, by rfl⟩ : syracuseStep 339999221 = 31874927) B31874927
theorem B226666147 : Blo 2179435 226666147 := bstep (se 1 (by rfl) ⟨169999610, by rfl⟩ : syracuseStep 226666147 = 339999221) B339999221
theorem B302221529 : Blo 2179435 302221529 := bstep (se 2 (by rfl) ⟨113333073, by rfl⟩ : syracuseStep 302221529 = 226666147) B226666147
theorem B201481019 : Blo 2179435 201481019 := bstep (se 1 (by rfl) ⟨151110764, by rfl⟩ : syracuseStep 201481019 = 302221529) B302221529
theorem B134320679 : Blo 2179435 134320679 := bstep (se 1 (by rfl) ⟨100740509, by rfl⟩ : syracuseStep 134320679 = 201481019) B201481019
theorem B89547119 : Blo 2179435 89547119 := bstep (se 1 (by rfl) ⟨67160339, by rfl⟩ : syracuseStep 89547119 = 134320679) B134320679
theorem B59698079 : Blo 2179435 59698079 := bstep (se 1 (by rfl) ⟨44773559, by rfl⟩ : syracuseStep 59698079 = 89547119) B89547119
theorem B39798719 : Blo 2179435 39798719 := bstep (se 1 (by rfl) ⟨29849039, by rfl⟩ : syracuseStep 39798719 = 59698079) B59698079
theorem B26532479 : Blo 2179435 26532479 := bstep (se 1 (by rfl) ⟨19899359, by rfl⟩ : syracuseStep 26532479 = 39798719) B39798719
theorem B70753277 : Blo 2179435 70753277 := bstep (se 3 (by rfl) ⟨13266239, by rfl⟩ : syracuseStep 70753277 = 26532479) B26532479
theorem B47168851 : Blo 2179435 47168851 := bstep (se 1 (by rfl) ⟨35376638, by rfl⟩ : syracuseStep 47168851 = 70753277) B70753277
theorem B62891801 : Blo 2179435 62891801 := bstep (se 2 (by rfl) ⟨23584425, by rfl⟩ : syracuseStep 62891801 = 47168851) B47168851
theorem B41927867 : Blo 2179435 41927867 := bstep (se 1 (by rfl) ⟨31445900, by rfl⟩ : syracuseStep 41927867 = 62891801) B62891801
theorem B27951911 : Blo 2179435 27951911 := bstep (se 1 (by rfl) ⟨20963933, by rfl⟩ : syracuseStep 27951911 = 41927867) B41927867
theorem B18634607 : Blo 2179435 18634607 := bstep (se 1 (by rfl) ⟨13975955, by rfl⟩ : syracuseStep 18634607 = 27951911) B27951911
theorem B12423071 : Blo 2179435 12423071 := bstep (se 1 (by rfl) ⟨9317303, by rfl⟩ : syracuseStep 12423071 = 18634607) B18634607
theorem B8282047 : Blo 2179435 8282047 := bstep (se 1 (by rfl) ⟨6211535, by rfl⟩ : syracuseStep 8282047 = 12423071) B12423071
theorem B11042729 : Blo 2179435 11042729 := bstep (se 2 (by rfl) ⟨4141023, by rfl⟩ : syracuseStep 11042729 = 8282047) B8282047
theorem B7361819 : Blo 2179435 7361819 := bstep (se 1 (by rfl) ⟨5521364, by rfl⟩ : syracuseStep 7361819 = 11042729) B11042729
theorem B4907879 : Blo 2179435 4907879 := bstep (se 1 (by rfl) ⟨3680909, by rfl⟩ : syracuseStep 4907879 = 7361819) B7361819
theorem B3271919 : Blo 2179435 3271919 := bstep (se 1 (by rfl) ⟨2453939, by rfl⟩ : syracuseStep 3271919 = 4907879) B4907879
theorem B2181279 : Blo 2179435 2181279 := bstep (se 1 (by rfl) ⟨1635959, by rfl⟩ : syracuseStep 2181279 = 3271919) B3271919
theorem B3271925 : Blo 2179435 3271925 := bbase (se 5 (by rfl) ⟨153371, by rfl⟩ : syracuseStep 3271925 = 306743) (by norm_num)
theorem B2181283 : Blo 2179435 2181283 := bstep (se 1 (by rfl) ⟨1635962, by rfl⟩ : syracuseStep 2181283 = 3271925) B3271925
theorem B3316573 : Blo 2179435 3316573 := bbase (se 3 (by rfl) ⟨621857, by rfl⟩ : syracuseStep 3316573 = 1243715) (by norm_num)
theorem B4422097 : Blo 2179435 4422097 := bstep (se 2 (by rfl) ⟨1658286, by rfl⟩ : syracuseStep 4422097 = 3316573) B3316573
theorem B23584517 : Blo 2179435 23584517 := bstep (se 4 (by rfl) ⟨2211048, by rfl⟩ : syracuseStep 23584517 = 4422097) B4422097
theorem B15723011 : Blo 2179435 15723011 := bstep (se 1 (by rfl) ⟨11792258, by rfl⟩ : syracuseStep 15723011 = 23584517) B23584517
theorem B10482007 : Blo 2179435 10482007 := bstep (se 1 (by rfl) ⟨7861505, by rfl⟩ : syracuseStep 10482007 = 15723011) B15723011
theorem B13976009 : Blo 2179435 13976009 := bstep (se 2 (by rfl) ⟨5241003, by rfl⟩ : syracuseStep 13976009 = 10482007) B10482007
theorem B9317339 : Blo 2179435 9317339 := bstep (se 1 (by rfl) ⟨6988004, by rfl⟩ : syracuseStep 9317339 = 13976009) B13976009
theorem B6211559 : Blo 2179435 6211559 := bstep (se 1 (by rfl) ⟨4658669, by rfl⟩ : syracuseStep 6211559 = 9317339) B9317339
theorem B4141039 : Blo 2179435 4141039 := bstep (se 1 (by rfl) ⟨3105779, by rfl⟩ : syracuseStep 4141039 = 6211559) B6211559
theorem B5521385 : Blo 2179435 5521385 := bstep (se 2 (by rfl) ⟨2070519, by rfl⟩ : syracuseStep 5521385 = 4141039) B4141039
theorem B3680923 : Blo 2179435 3680923 := bstep (se 1 (by rfl) ⟨2760692, by rfl⟩ : syracuseStep 3680923 = 5521385) B5521385
theorem B4907897 : Blo 2179435 4907897 := bstep (se 2 (by rfl) ⟨1840461, by rfl⟩ : syracuseStep 4907897 = 3680923) B3680923
theorem B3271931 : Blo 2179435 3271931 := bstep (se 1 (by rfl) ⟨2453948, by rfl⟩ : syracuseStep 3271931 = 4907897) B4907897
theorem B2181287 : Blo 2179435 2181287 := bstep (se 1 (by rfl) ⟨1635965, by rfl⟩ : syracuseStep 2181287 = 3271931) B3271931
theorem B2453953 : Blo 2179435 2453953 := bbase (se 2 (by rfl) ⟨920232, by rfl⟩ : syracuseStep 2453953 = 1840465) (by norm_num)
theorem B3271937 : Blo 2179435 3271937 := bstep (se 2 (by rfl) ⟨1226976, by rfl⟩ : syracuseStep 3271937 = 2453953) B2453953
theorem B2181291 : Blo 2179435 2181291 := bstep (se 1 (by rfl) ⟨1635968, by rfl⟩ : syracuseStep 2181291 = 3271937) B3271937
theorem B5521405 : Blo 2179435 5521405 := bbase (se 3 (by rfl) ⟨1035263, by rfl⟩ : syracuseStep 5521405 = 2070527) (by norm_num)
theorem B7361873 : Blo 2179435 7361873 := bstep (se 2 (by rfl) ⟨2760702, by rfl⟩ : syracuseStep 7361873 = 5521405) B5521405
theorem B4907915 : Blo 2179435 4907915 := bstep (se 1 (by rfl) ⟨3680936, by rfl⟩ : syracuseStep 4907915 = 7361873) B7361873
theorem B3271943 : Blo 2179435 3271943 := bstep (se 1 (by rfl) ⟨2453957, by rfl⟩ : syracuseStep 3271943 = 4907915) B4907915
theorem B2181295 : Blo 2179435 2181295 := bstep (se 1 (by rfl) ⟨1635971, by rfl⟩ : syracuseStep 2181295 = 3271943) B3271943
theorem B3271949 : Blo 2179435 3271949 := bbase (se 3 (by rfl) ⟨613490, by rfl⟩ : syracuseStep 3271949 = 1226981) (by norm_num)
theorem B2181299 : Blo 2179435 2181299 := bstep (se 1 (by rfl) ⟨1635974, by rfl⟩ : syracuseStep 2181299 = 3271949) B3271949
theorem B4907933 : Blo 2179435 4907933 := bbase (se 3 (by rfl) ⟨920237, by rfl⟩ : syracuseStep 4907933 = 1840475) (by norm_num)
theorem B3271955 : Blo 2179435 3271955 := bstep (se 1 (by rfl) ⟨2453966, by rfl⟩ : syracuseStep 3271955 = 4907933) B4907933
theorem B2181303 : Blo 2179435 2181303 := bstep (se 1 (by rfl) ⟨1635977, by rfl⟩ : syracuseStep 2181303 = 3271955) B3271955
theorem B3680957 : Blo 2179435 3680957 := bbase (se 3 (by rfl) ⟨690179, by rfl⟩ : syracuseStep 3680957 = 1380359) (by norm_num)
theorem B2453971 : Blo 2179435 2453971 := bstep (se 1 (by rfl) ⟨1840478, by rfl⟩ : syracuseStep 2453971 = 3680957) B3680957
theorem B3271961 : Blo 2179435 3271961 := bstep (se 2 (by rfl) ⟨1226985, by rfl⟩ : syracuseStep 3271961 = 2453971) B2453971
theorem B2181307 : Blo 2179435 2181307 := bstep (se 1 (by rfl) ⟨1635980, by rfl⟩ : syracuseStep 2181307 = 3271961) B3271961
theorem B12423253 : Blo 2179435 12423253 := bbase (se 8 (by rfl) ⟨72792, by rfl⟩ : syracuseStep 12423253 = 145585) (by norm_num)
theorem B16564337 : Blo 2179435 16564337 := bstep (se 2 (by rfl) ⟨6211626, by rfl⟩ : syracuseStep 16564337 = 12423253) B12423253
theorem B11042891 : Blo 2179435 11042891 := bstep (se 1 (by rfl) ⟨8282168, by rfl⟩ : syracuseStep 11042891 = 16564337) B16564337
theorem B7361927 : Blo 2179435 7361927 := bstep (se 1 (by rfl) ⟨5521445, by rfl⟩ : syracuseStep 7361927 = 11042891) B11042891
theorem B4907951 : Blo 2179435 4907951 := bstep (se 1 (by rfl) ⟨3680963, by rfl⟩ : syracuseStep 4907951 = 7361927) B7361927
theorem B3271967 : Blo 2179435 3271967 := bstep (se 1 (by rfl) ⟨2453975, by rfl⟩ : syracuseStep 3271967 = 4907951) B4907951
theorem B2181311 : Blo 2179435 2181311 := bstep (se 1 (by rfl) ⟨1635983, by rfl⟩ : syracuseStep 2181311 = 3271967) B3271967
theorem B3271973 : Blo 2179435 3271973 := bbase (se 4 (by rfl) ⟨306747, by rfl⟩ : syracuseStep 3271973 = 613495) (by norm_num)
theorem B2181315 : Blo 2179435 2181315 := bstep (se 1 (by rfl) ⟨1635986, by rfl⟩ : syracuseStep 2181315 = 3271973) B3271973
theorem B2760733 : Blo 2179435 2760733 := bbase (se 3 (by rfl) ⟨517637, by rfl⟩ : syracuseStep 2760733 = 1035275) (by norm_num)
theorem B3680977 : Blo 2179435 3680977 := bstep (se 2 (by rfl) ⟨1380366, by rfl⟩ : syracuseStep 3680977 = 2760733) B2760733
theorem B4907969 : Blo 2179435 4907969 := bstep (se 2 (by rfl) ⟨1840488, by rfl⟩ : syracuseStep 4907969 = 3680977) B3680977
theorem B3271979 : Blo 2179435 3271979 := bstep (se 1 (by rfl) ⟨2453984, by rfl⟩ : syracuseStep 3271979 = 4907969) B4907969
theorem B2181319 : Blo 2179435 2181319 := bstep (se 1 (by rfl) ⟨1635989, by rfl⟩ : syracuseStep 2181319 = 3271979) B3271979
theorem B2453989 : Blo 2179435 2453989 := bbase (se 4 (by rfl) ⟨230061, by rfl⟩ : syracuseStep 2453989 = 460123) (by norm_num)
theorem B3271985 : Blo 2179435 3271985 := bstep (se 2 (by rfl) ⟨1226994, by rfl⟩ : syracuseStep 3271985 = 2453989) B2453989
theorem B2181323 : Blo 2179435 2181323 := bstep (se 1 (by rfl) ⟨1635992, by rfl⟩ : syracuseStep 2181323 = 3271985) B3271985
theorem B6988133 : Blo 2179435 6988133 := bbase (se 4 (by rfl) ⟨655137, by rfl⟩ : syracuseStep 6988133 = 1310275) (by norm_num)
theorem B4658755 : Blo 2179435 4658755 := bstep (se 1 (by rfl) ⟨3494066, by rfl⟩ : syracuseStep 4658755 = 6988133) B6988133
theorem B6211673 : Blo 2179435 6211673 := bstep (se 2 (by rfl) ⟨2329377, by rfl⟩ : syracuseStep 6211673 = 4658755) B4658755
theorem B4141115 : Blo 2179435 4141115 := bstep (se 1 (by rfl) ⟨3105836, by rfl⟩ : syracuseStep 4141115 = 6211673) B6211673
theorem B2760743 : Blo 2179435 2760743 := bstep (se 1 (by rfl) ⟨2070557, by rfl⟩ : syracuseStep 2760743 = 4141115) B4141115
theorem B7361981 : Blo 2179435 7361981 := bstep (se 3 (by rfl) ⟨1380371, by rfl⟩ : syracuseStep 7361981 = 2760743) B2760743
theorem B4907987 : Blo 2179435 4907987 := bstep (se 1 (by rfl) ⟨3680990, by rfl⟩ : syracuseStep 4907987 = 7361981) B7361981
theorem B3271991 : Blo 2179435 3271991 := bstep (se 1 (by rfl) ⟨2453993, by rfl⟩ : syracuseStep 3271991 = 4907987) B4907987
theorem B2181327 : Blo 2179435 2181327 := bstep (se 1 (by rfl) ⟨1635995, by rfl⟩ : syracuseStep 2181327 = 3271991) B3271991
theorem B3271997 : Blo 2179435 3271997 := bbase (se 3 (by rfl) ⟨613499, by rfl⟩ : syracuseStep 3271997 = 1226999) (by norm_num)
theorem B2181331 : Blo 2179435 2181331 := bstep (se 1 (by rfl) ⟨1635998, by rfl⟩ : syracuseStep 2181331 = 3271997) B3271997
theorem B4908005 : Blo 2179435 4908005 := bbase (se 4 (by rfl) ⟨460125, by rfl⟩ : syracuseStep 4908005 = 920251) (by norm_num)
theorem B3272003 : Blo 2179435 3272003 := bstep (se 1 (by rfl) ⟨2454002, by rfl⟩ : syracuseStep 3272003 = 4908005) B4908005
theorem B2181335 : Blo 2179435 2181335 := bstep (se 1 (by rfl) ⟨1636001, by rfl⟩ : syracuseStep 2181335 = 3272003) B3272003
theorem B5521517 : Blo 2179435 5521517 := bbase (se 3 (by rfl) ⟨1035284, by rfl⟩ : syracuseStep 5521517 = 2070569) (by norm_num)
theorem B3681011 : Blo 2179435 3681011 := bstep (se 1 (by rfl) ⟨2760758, by rfl⟩ : syracuseStep 3681011 = 5521517) B5521517
theorem B2454007 : Blo 2179435 2454007 := bstep (se 1 (by rfl) ⟨1840505, by rfl⟩ : syracuseStep 2454007 = 3681011) B3681011
theorem B3272009 : Blo 2179435 3272009 := bstep (se 2 (by rfl) ⟨1227003, by rfl⟩ : syracuseStep 3272009 = 2454007) B2454007
theorem B2181339 : Blo 2179435 2181339 := bstep (se 1 (by rfl) ⟨1636004, by rfl⟩ : syracuseStep 2181339 = 3272009) B3272009
theorem B4658789 : Blo 2179435 4658789 := bbase (se 4 (by rfl) ⟨436761, by rfl⟩ : syracuseStep 4658789 = 873523) (by norm_num)
theorem B3105859 : Blo 2179435 3105859 := bstep (se 1 (by rfl) ⟨2329394, by rfl⟩ : syracuseStep 3105859 = 4658789) B4658789
theorem B4141145 : Blo 2179435 4141145 := bstep (se 2 (by rfl) ⟨1552929, by rfl⟩ : syracuseStep 4141145 = 3105859) B3105859
theorem B11043053 : Blo 2179435 11043053 := bstep (se 3 (by rfl) ⟨2070572, by rfl⟩ : syracuseStep 11043053 = 4141145) B4141145
theorem B7362035 : Blo 2179435 7362035 := bstep (se 1 (by rfl) ⟨5521526, by rfl⟩ : syracuseStep 7362035 = 11043053) B11043053
theorem B4908023 : Blo 2179435 4908023 := bstep (se 1 (by rfl) ⟨3681017, by rfl⟩ : syracuseStep 4908023 = 7362035) B7362035
theorem B3272015 : Blo 2179435 3272015 := bstep (se 1 (by rfl) ⟨2454011, by rfl⟩ : syracuseStep 3272015 = 4908023) B4908023
theorem B2181343 : Blo 2179435 2181343 := bstep (se 1 (by rfl) ⟨1636007, by rfl⟩ : syracuseStep 2181343 = 3272015) B3272015
theorem B3272021 : Blo 2179435 3272021 := bbase (se 11 (by rfl) ⟨2396, by rfl⟩ : syracuseStep 3272021 = 4793) (by norm_num)
theorem B2181347 : Blo 2179435 2181347 := bstep (se 1 (by rfl) ⟨1636010, by rfl⟩ : syracuseStep 2181347 = 3272021) B3272021
theorem B3930869 : Blo 2179435 3930869 := bbase (se 5 (by rfl) ⟨184259, by rfl⟩ : syracuseStep 3930869 = 368519) (by norm_num)
theorem B2620579 : Blo 2179435 2620579 := bstep (se 1 (by rfl) ⟨1965434, by rfl⟩ : syracuseStep 2620579 = 3930869) B3930869
theorem B3494105 : Blo 2179435 3494105 := bstep (se 2 (by rfl) ⟨1310289, by rfl⟩ : syracuseStep 3494105 = 2620579) B2620579
theorem B2329403 : Blo 2179435 2329403 := bstep (se 1 (by rfl) ⟨1747052, by rfl⟩ : syracuseStep 2329403 = 3494105) B3494105
theorem B6211741 : Blo 2179435 6211741 := bstep (se 3 (by rfl) ⟨1164701, by rfl⟩ : syracuseStep 6211741 = 2329403) B2329403
theorem B8282321 : Blo 2179435 8282321 := bstep (se 2 (by rfl) ⟨3105870, by rfl⟩ : syracuseStep 8282321 = 6211741) B6211741
theorem B5521547 : Blo 2179435 5521547 := bstep (se 1 (by rfl) ⟨4141160, by rfl⟩ : syracuseStep 5521547 = 8282321) B8282321
theorem B3681031 : Blo 2179435 3681031 := bstep (se 1 (by rfl) ⟨2760773, by rfl⟩ : syracuseStep 3681031 = 5521547) B5521547
theorem B4908041 : Blo 2179435 4908041 := bstep (se 2 (by rfl) ⟨1840515, by rfl⟩ : syracuseStep 4908041 = 3681031) B3681031
theorem B3272027 : Blo 2179435 3272027 := bstep (se 1 (by rfl) ⟨2454020, by rfl⟩ : syracuseStep 3272027 = 4908041) B4908041
theorem B2181351 : Blo 2179435 2181351 := bstep (se 1 (by rfl) ⟨1636013, by rfl⟩ : syracuseStep 2181351 = 3272027) B3272027
theorem B2454025 : Blo 2179435 2454025 := bbase (se 2 (by rfl) ⟨920259, by rfl⟩ : syracuseStep 2454025 = 1840519) (by norm_num)
theorem B3272033 : Blo 2179435 3272033 := bstep (se 2 (by rfl) ⟨1227012, by rfl⟩ : syracuseStep 3272033 = 2454025) B2454025
theorem B2181355 : Blo 2179435 2181355 := bstep (se 1 (by rfl) ⟨1636016, by rfl⟩ : syracuseStep 2181355 = 3272033) B3272033
theorem B5596901 : Blo 2179435 5596901 := bbase (se 4 (by rfl) ⟨524709, by rfl⟩ : syracuseStep 5596901 = 1049419) (by norm_num)
theorem B3731267 : Blo 2179435 3731267 := bstep (se 1 (by rfl) ⟨2798450, by rfl⟩ : syracuseStep 3731267 = 5596901) B5596901
theorem B9950045 : Blo 2179435 9950045 := bstep (se 3 (by rfl) ⟨1865633, by rfl⟩ : syracuseStep 9950045 = 3731267) B3731267
theorem B106133813 : Blo 2179435 106133813 := bstep (se 5 (by rfl) ⟨4975022, by rfl⟩ : syracuseStep 106133813 = 9950045) B9950045
theorem B70755875 : Blo 2179435 70755875 := bstep (se 1 (by rfl) ⟨53066906, by rfl⟩ : syracuseStep 70755875 = 106133813) B106133813
theorem B47170583 : Blo 2179435 47170583 := bstep (se 1 (by rfl) ⟨35377937, by rfl⟩ : syracuseStep 47170583 = 70755875) B70755875
theorem B31447055 : Blo 2179435 31447055 := bstep (se 1 (by rfl) ⟨23585291, by rfl⟩ : syracuseStep 31447055 = 47170583) B47170583
theorem B20964703 : Blo 2179435 20964703 := bstep (se 1 (by rfl) ⟨15723527, by rfl⟩ : syracuseStep 20964703 = 31447055) B31447055
theorem B27952937 : Blo 2179435 27952937 := bstep (se 2 (by rfl) ⟨10482351, by rfl⟩ : syracuseStep 27952937 = 20964703) B20964703
theorem B18635291 : Blo 2179435 18635291 := bstep (se 1 (by rfl) ⟨13976468, by rfl⟩ : syracuseStep 18635291 = 27952937) B27952937
theorem B12423527 : Blo 2179435 12423527 := bstep (se 1 (by rfl) ⟨9317645, by rfl⟩ : syracuseStep 12423527 = 18635291) B18635291
theorem B8282351 : Blo 2179435 8282351 := bstep (se 1 (by rfl) ⟨6211763, by rfl⟩ : syracuseStep 8282351 = 12423527) B12423527
theorem B5521567 : Blo 2179435 5521567 := bstep (se 1 (by rfl) ⟨4141175, by rfl⟩ : syracuseStep 5521567 = 8282351) B8282351
theorem B7362089 : Blo 2179435 7362089 := bstep (se 2 (by rfl) ⟨2760783, by rfl⟩ : syracuseStep 7362089 = 5521567) B5521567
theorem B4908059 : Blo 2179435 4908059 := bstep (se 1 (by rfl) ⟨3681044, by rfl⟩ : syracuseStep 4908059 = 7362089) B7362089
theorem B3272039 : Blo 2179435 3272039 := bstep (se 1 (by rfl) ⟨2454029, by rfl⟩ : syracuseStep 3272039 = 4908059) B4908059
theorem B2181359 : Blo 2179435 2181359 := bstep (se 1 (by rfl) ⟨1636019, by rfl⟩ : syracuseStep 2181359 = 3272039) B3272039
theorem B3272045 : Blo 2179435 3272045 := bbase (se 3 (by rfl) ⟨613508, by rfl⟩ : syracuseStep 3272045 = 1227017) (by norm_num)
theorem B2181363 : Blo 2179435 2181363 := bstep (se 1 (by rfl) ⟨1636022, by rfl⟩ : syracuseStep 2181363 = 3272045) B3272045
theorem B4908077 : Blo 2179435 4908077 := bbase (se 3 (by rfl) ⟨920264, by rfl⟩ : syracuseStep 4908077 = 1840529) (by norm_num)
theorem B3272051 : Blo 2179435 3272051 := bstep (se 1 (by rfl) ⟨2454038, by rfl⟩ : syracuseStep 3272051 = 4908077) B4908077
theorem B2181367 : Blo 2179435 2181367 := bstep (se 1 (by rfl) ⟨1636025, by rfl⟩ : syracuseStep 2181367 = 3272051) B3272051
theorem B4422269 : Blo 2179435 4422269 := bbase (se 3 (by rfl) ⟨829175, by rfl⟩ : syracuseStep 4422269 = 1658351) (by norm_num)
theorem B2948179 : Blo 2179435 2948179 := bstep (se 1 (by rfl) ⟨2211134, by rfl⟩ : syracuseStep 2948179 = 4422269) B4422269
theorem B3930905 : Blo 2179435 3930905 := bstep (se 2 (by rfl) ⟨1474089, by rfl⟩ : syracuseStep 3930905 = 2948179) B2948179
theorem B2620603 : Blo 2179435 2620603 := bstep (se 1 (by rfl) ⟨1965452, by rfl⟩ : syracuseStep 2620603 = 3930905) B3930905
theorem B13976549 : Blo 2179435 13976549 := bstep (se 4 (by rfl) ⟨1310301, by rfl⟩ : syracuseStep 13976549 = 2620603) B2620603
theorem B9317699 : Blo 2179435 9317699 := bstep (se 1 (by rfl) ⟨6988274, by rfl⟩ : syracuseStep 9317699 = 13976549) B13976549
theorem B6211799 : Blo 2179435 6211799 := bstep (se 1 (by rfl) ⟨4658849, by rfl⟩ : syracuseStep 6211799 = 9317699) B9317699
theorem B4141199 : Blo 2179435 4141199 := bstep (se 1 (by rfl) ⟨3105899, by rfl⟩ : syracuseStep 4141199 = 6211799) B6211799
theorem B2760799 : Blo 2179435 2760799 := bstep (se 1 (by rfl) ⟨2070599, by rfl⟩ : syracuseStep 2760799 = 4141199) B4141199
theorem B3681065 : Blo 2179435 3681065 := bstep (se 2 (by rfl) ⟨1380399, by rfl⟩ : syracuseStep 3681065 = 2760799) B2760799
theorem B2454043 : Blo 2179435 2454043 := bstep (se 1 (by rfl) ⟨1840532, by rfl⟩ : syracuseStep 2454043 = 3681065) B3681065
theorem B3272057 : Blo 2179435 3272057 := bstep (se 2 (by rfl) ⟨1227021, by rfl⟩ : syracuseStep 3272057 = 2454043) B2454043
theorem B2181371 : Blo 2179435 2181371 := bstep (se 1 (by rfl) ⟨1636028, by rfl⟩ : syracuseStep 2181371 = 3272057) B3272057
theorem B18889685 : Blo 2179435 18889685 := bbase (se 7 (by rfl) ⟨221363, by rfl⟩ : syracuseStep 18889685 = 442727) (by norm_num)
theorem B12593123 : Blo 2179435 12593123 := bstep (se 1 (by rfl) ⟨9444842, by rfl⟩ : syracuseStep 12593123 = 18889685) B18889685
theorem B8395415 : Blo 2179435 8395415 := bstep (se 1 (by rfl) ⟨6296561, by rfl⟩ : syracuseStep 8395415 = 12593123) B12593123
theorem B5596943 : Blo 2179435 5596943 := bstep (se 1 (by rfl) ⟨4197707, by rfl⟩ : syracuseStep 5596943 = 8395415) B8395415
theorem B14925181 : Blo 2179435 14925181 := bstep (se 3 (by rfl) ⟨2798471, by rfl⟩ : syracuseStep 14925181 = 5596943) B5596943
theorem B19900241 : Blo 2179435 19900241 := bstep (se 2 (by rfl) ⟨7462590, by rfl⟩ : syracuseStep 19900241 = 14925181) B14925181
theorem B13266827 : Blo 2179435 13266827 := bstep (se 1 (by rfl) ⟨9950120, by rfl⟩ : syracuseStep 13266827 = 19900241) B19900241
theorem B8844551 : Blo 2179435 8844551 := bstep (se 1 (by rfl) ⟨6633413, by rfl⟩ : syracuseStep 8844551 = 13266827) B13266827
theorem B5896367 : Blo 2179435 5896367 := bstep (se 1 (by rfl) ⟨4422275, by rfl⟩ : syracuseStep 5896367 = 8844551) B8844551
theorem B3930911 : Blo 2179435 3930911 := bstep (se 1 (by rfl) ⟨2948183, by rfl⟩ : syracuseStep 3930911 = 5896367) B5896367
theorem B2620607 : Blo 2179435 2620607 := bstep (se 1 (by rfl) ⟨1965455, by rfl⟩ : syracuseStep 2620607 = 3930911) B3930911
theorem B6988285 : Blo 2179435 6988285 := bstep (se 3 (by rfl) ⟨1310303, by rfl⟩ : syracuseStep 6988285 = 2620607) B2620607
theorem B37270853 : Blo 2179435 37270853 := bstep (se 4 (by rfl) ⟨3494142, by rfl⟩ : syracuseStep 37270853 = 6988285) B6988285
theorem B24847235 : Blo 2179435 24847235 := bstep (se 1 (by rfl) ⟨18635426, by rfl⟩ : syracuseStep 24847235 = 37270853) B37270853
theorem B16564823 : Blo 2179435 16564823 := bstep (se 1 (by rfl) ⟨12423617, by rfl⟩ : syracuseStep 16564823 = 24847235) B24847235
theorem B11043215 : Blo 2179435 11043215 := bstep (se 1 (by rfl) ⟨8282411, by rfl⟩ : syracuseStep 11043215 = 16564823) B16564823
theorem B7362143 : Blo 2179435 7362143 := bstep (se 1 (by rfl) ⟨5521607, by rfl⟩ : syracuseStep 7362143 = 11043215) B11043215
theorem B4908095 : Blo 2179435 4908095 := bstep (se 1 (by rfl) ⟨3681071, by rfl⟩ : syracuseStep 4908095 = 7362143) B7362143
theorem B3272063 : Blo 2179435 3272063 := bstep (se 1 (by rfl) ⟨2454047, by rfl⟩ : syracuseStep 3272063 = 4908095) B4908095
theorem B2181375 : Blo 2179435 2181375 := bstep (se 1 (by rfl) ⟨1636031, by rfl⟩ : syracuseStep 2181375 = 3272063) B3272063
theorem B3272069 : Blo 2179435 3272069 := bbase (se 4 (by rfl) ⟨306756, by rfl⟩ : syracuseStep 3272069 = 613513) (by norm_num)
theorem B2181379 : Blo 2179435 2181379 := bstep (se 1 (by rfl) ⟨1636034, by rfl⟩ : syracuseStep 2181379 = 3272069) B3272069
theorem B3681085 : Blo 2179435 3681085 := bbase (se 3 (by rfl) ⟨690203, by rfl⟩ : syracuseStep 3681085 = 1380407) (by norm_num)
theorem B4908113 : Blo 2179435 4908113 := bstep (se 2 (by rfl) ⟨1840542, by rfl⟩ : syracuseStep 4908113 = 3681085) B3681085
theorem B3272075 : Blo 2179435 3272075 := bstep (se 1 (by rfl) ⟨2454056, by rfl⟩ : syracuseStep 3272075 = 4908113) B4908113
theorem B2181383 : Blo 2179435 2181383 := bstep (se 1 (by rfl) ⟨1636037, by rfl⟩ : syracuseStep 2181383 = 3272075) B3272075
theorem B2454061 : Blo 2179435 2454061 := bbase (se 3 (by rfl) ⟨460136, by rfl⟩ : syracuseStep 2454061 = 920273) (by norm_num)
theorem B3272081 : Blo 2179435 3272081 := bstep (se 2 (by rfl) ⟨1227030, by rfl⟩ : syracuseStep 3272081 = 2454061) B2454061
theorem B2181387 : Blo 2179435 2181387 := bstep (se 1 (by rfl) ⟨1636040, by rfl⟩ : syracuseStep 2181387 = 3272081) B3272081
theorem B7362197 : Blo 2179435 7362197 := bbase (se 6 (by rfl) ⟨172551, by rfl⟩ : syracuseStep 7362197 = 345103) (by norm_num)
theorem B4908131 : Blo 2179435 4908131 := bstep (se 1 (by rfl) ⟨3681098, by rfl⟩ : syracuseStep 4908131 = 7362197) B7362197
theorem B3272087 : Blo 2179435 3272087 := bstep (se 1 (by rfl) ⟨2454065, by rfl⟩ : syracuseStep 3272087 = 4908131) B4908131
theorem B2181391 : Blo 2179435 2181391 := bstep (se 1 (by rfl) ⟨1636043, by rfl⟩ : syracuseStep 2181391 = 3272087) B3272087
theorem B3272093 : Blo 2179435 3272093 := bbase (se 3 (by rfl) ⟨613517, by rfl⟩ : syracuseStep 3272093 = 1227035) (by norm_num)
theorem B2181395 : Blo 2179435 2181395 := bstep (se 1 (by rfl) ⟨1636046, by rfl⟩ : syracuseStep 2181395 = 3272093) B3272093
theorem B4908149 : Blo 2179435 4908149 := bbase (se 5 (by rfl) ⟨230069, by rfl⟩ : syracuseStep 4908149 = 460139) (by norm_num)
theorem B3272099 : Blo 2179435 3272099 := bstep (se 1 (by rfl) ⟨2454074, by rfl⟩ : syracuseStep 3272099 = 4908149) B4908149
theorem B2181399 : Blo 2179435 2181399 := bstep (se 1 (by rfl) ⟨1636049, by rfl⟩ : syracuseStep 2181399 = 3272099) B3272099
theorem B18635669 : Blo 2179435 18635669 := bbase (se 6 (by rfl) ⟨436773, by rfl⟩ : syracuseStep 18635669 = 873547) (by norm_num)
theorem B12423779 : Blo 2179435 12423779 := bstep (se 1 (by rfl) ⟨9317834, by rfl⟩ : syracuseStep 12423779 = 18635669) B18635669
theorem B8282519 : Blo 2179435 8282519 := bstep (se 1 (by rfl) ⟨6211889, by rfl⟩ : syracuseStep 8282519 = 12423779) B12423779
theorem B5521679 : Blo 2179435 5521679 := bstep (se 1 (by rfl) ⟨4141259, by rfl⟩ : syracuseStep 5521679 = 8282519) B8282519
theorem B3681119 : Blo 2179435 3681119 := bstep (se 1 (by rfl) ⟨2760839, by rfl⟩ : syracuseStep 3681119 = 5521679) B5521679
theorem B2454079 : Blo 2179435 2454079 := bstep (se 1 (by rfl) ⟨1840559, by rfl⟩ : syracuseStep 2454079 = 3681119) B3681119
theorem B3272105 : Blo 2179435 3272105 := bstep (se 2 (by rfl) ⟨1227039, by rfl⟩ : syracuseStep 3272105 = 2454079) B2454079
theorem B2181403 : Blo 2179435 2181403 := bstep (se 1 (by rfl) ⟨1636052, by rfl⟩ : syracuseStep 2181403 = 3272105) B3272105
theorem B8282533 : Blo 2179435 8282533 := bbase (se 4 (by rfl) ⟨776487, by rfl⟩ : syracuseStep 8282533 = 1552975) (by norm_num)
theorem B11043377 : Blo 2179435 11043377 := bstep (se 2 (by rfl) ⟨4141266, by rfl⟩ : syracuseStep 11043377 = 8282533) B8282533
theorem B7362251 : Blo 2179435 7362251 := bstep (se 1 (by rfl) ⟨5521688, by rfl⟩ : syracuseStep 7362251 = 11043377) B11043377
theorem B4908167 : Blo 2179435 4908167 := bstep (se 1 (by rfl) ⟨3681125, by rfl⟩ : syracuseStep 4908167 = 7362251) B7362251
theorem B3272111 : Blo 2179435 3272111 := bstep (se 1 (by rfl) ⟨2454083, by rfl⟩ : syracuseStep 3272111 = 4908167) B4908167
theorem B2181407 : Blo 2179435 2181407 := bstep (se 1 (by rfl) ⟨1636055, by rfl⟩ : syracuseStep 2181407 = 3272111) B3272111
theorem B3272117 : Blo 2179435 3272117 := bbase (se 5 (by rfl) ⟨153380, by rfl⟩ : syracuseStep 3272117 = 306761) (by norm_num)
theorem B2181411 : Blo 2179435 2181411 := bstep (se 1 (by rfl) ⟨1636058, by rfl⟩ : syracuseStep 2181411 = 3272117) B3272117
theorem B5521709 : Blo 2179435 5521709 := bbase (se 3 (by rfl) ⟨1035320, by rfl⟩ : syracuseStep 5521709 = 2070641) (by norm_num)
theorem B3681139 : Blo 2179435 3681139 := bstep (se 1 (by rfl) ⟨2760854, by rfl⟩ : syracuseStep 3681139 = 5521709) B5521709
theorem B4908185 : Blo 2179435 4908185 := bstep (se 2 (by rfl) ⟨1840569, by rfl⟩ : syracuseStep 4908185 = 3681139) B3681139
theorem B3272123 : Blo 2179435 3272123 := bstep (se 1 (by rfl) ⟨2454092, by rfl⟩ : syracuseStep 3272123 = 4908185) B4908185
theorem B2181415 : Blo 2179435 2181415 := bstep (se 1 (by rfl) ⟨1636061, by rfl⟩ : syracuseStep 2181415 = 3272123) B3272123
theorem B2454097 : Blo 2179435 2454097 := bbase (se 2 (by rfl) ⟨920286, by rfl⟩ : syracuseStep 2454097 = 1840573) (by norm_num)
theorem B3272129 : Blo 2179435 3272129 := bstep (se 2 (by rfl) ⟨1227048, by rfl⟩ : syracuseStep 3272129 = 2454097) B2454097
theorem B2181419 : Blo 2179435 2181419 := bstep (se 1 (by rfl) ⟨1636064, by rfl⟩ : syracuseStep 2181419 = 3272129) B3272129
theorem B3105973 : Blo 2179435 3105973 := bbase (se 5 (by rfl) ⟨145592, by rfl⟩ : syracuseStep 3105973 = 291185) (by norm_num)
theorem B4141297 : Blo 2179435 4141297 := bstep (se 2 (by rfl) ⟨1552986, by rfl⟩ : syracuseStep 4141297 = 3105973) B3105973
theorem B5521729 : Blo 2179435 5521729 := bstep (se 2 (by rfl) ⟨2070648, by rfl⟩ : syracuseStep 5521729 = 4141297) B4141297
theorem B7362305 : Blo 2179435 7362305 := bstep (se 2 (by rfl) ⟨2760864, by rfl⟩ : syracuseStep 7362305 = 5521729) B5521729
theorem B4908203 : Blo 2179435 4908203 := bstep (se 1 (by rfl) ⟨3681152, by rfl⟩ : syracuseStep 4908203 = 7362305) B7362305
theorem B3272135 : Blo 2179435 3272135 := bstep (se 1 (by rfl) ⟨2454101, by rfl⟩ : syracuseStep 3272135 = 4908203) B4908203
theorem B2181423 : Blo 2179435 2181423 := bstep (se 1 (by rfl) ⟨1636067, by rfl⟩ : syracuseStep 2181423 = 3272135) B3272135
theorem B3272141 : Blo 2179435 3272141 := bbase (se 3 (by rfl) ⟨613526, by rfl⟩ : syracuseStep 3272141 = 1227053) (by norm_num)
theorem B2181427 : Blo 2179435 2181427 := bstep (se 1 (by rfl) ⟨1636070, by rfl⟩ : syracuseStep 2181427 = 3272141) B3272141
theorem B4908221 : Blo 2179435 4908221 := bbase (se 3 (by rfl) ⟨920291, by rfl⟩ : syracuseStep 4908221 = 1840583) (by norm_num)
theorem B3272147 : Blo 2179435 3272147 := bstep (se 1 (by rfl) ⟨2454110, by rfl⟩ : syracuseStep 3272147 = 4908221) B4908221
theorem B2181431 : Blo 2179435 2181431 := bstep (se 1 (by rfl) ⟨1636073, by rfl⟩ : syracuseStep 2181431 = 3272147) B3272147
theorem B3681173 : Blo 2179435 3681173 := bbase (se 6 (by rfl) ⟨86277, by rfl⟩ : syracuseStep 3681173 = 172555) (by norm_num)
theorem B2454115 : Blo 2179435 2454115 := bstep (se 1 (by rfl) ⟨1840586, by rfl⟩ : syracuseStep 2454115 = 3681173) B3681173
theorem B3272153 : Blo 2179435 3272153 := bstep (se 2 (by rfl) ⟨1227057, by rfl⟩ : syracuseStep 3272153 = 2454115) B2454115
theorem B2181435 : Blo 2179435 2181435 := bstep (se 1 (by rfl) ⟨1636076, by rfl⟩ : syracuseStep 2181435 = 3272153) B3272153
theorem C0 (j : ℕ) (h1 : 544858 ≤ j) (h2 : j ≤ 545358) : Blo 2179435 (4 * j + 3) := by
  interval_cases j
  · exact B2179435
  · exact B2179439
  · exact B2179443
  · exact B2179447
  · exact B2179451
  · exact B2179455
  · exact B2179459
  · exact B2179463
  · exact B2179467
  · exact B2179471
  · exact B2179475
  · exact B2179479
  · exact B2179483
  · exact B2179487
  · exact B2179491
  · exact B2179495
  · exact B2179499
  · exact B2179503
  · exact B2179507
  · exact B2179511
  · exact B2179515
  · exact B2179519
  · exact B2179523
  · exact B2179527
  · exact B2179531
  · exact B2179535
  · exact B2179539
  · exact B2179543
  · exact B2179547
  · exact B2179551
  · exact B2179555
  · exact B2179559
  · exact B2179563
  · exact B2179567
  · exact B2179571
  · exact B2179575
  · exact B2179579
  · exact B2179583
  · exact B2179587
  · exact B2179591
  · exact B2179595
  · exact B2179599
  · exact B2179603
  · exact B2179607
  · exact B2179611
  · exact B2179615
  · exact B2179619
  · exact B2179623
  · exact B2179627
  · exact B2179631
  · exact B2179635
  · exact B2179639
  · exact B2179643
  · exact B2179647
  · exact B2179651
  · exact B2179655
  · exact B2179659
  · exact B2179663
  · exact B2179667
  · exact B2179671
  · exact B2179675
  · exact B2179679
  · exact B2179683
  · exact B2179687
  · exact B2179691
  · exact B2179695
  · exact B2179699
  · exact B2179703
  · exact B2179707
  · exact B2179711
  · exact B2179715
  · exact B2179719
  · exact B2179723
  · exact B2179727
  · exact B2179731
  · exact B2179735
  · exact B2179739
  · exact B2179743
  · exact B2179747
  · exact B2179751
  · exact B2179755
  · exact B2179759
  · exact B2179763
  · exact B2179767
  · exact B2179771
  · exact B2179775
  · exact B2179779
  · exact B2179783
  · exact B2179787
  · exact B2179791
  · exact B2179795
  · exact B2179799
  · exact B2179803
  · exact B2179807
  · exact B2179811
  · exact B2179815
  · exact B2179819
  · exact B2179823
  · exact B2179827
  · exact B2179831
  · exact B2179835
  · exact B2179839
  · exact B2179843
  · exact B2179847
  · exact B2179851
  · exact B2179855
  · exact B2179859
  · exact B2179863
  · exact B2179867
  · exact B2179871
  · exact B2179875
  · exact B2179879
  · exact B2179883
  · exact B2179887
  · exact B2179891
  · exact B2179895
  · exact B2179899
  · exact B2179903
  · exact B2179907
  · exact B2179911
  · exact B2179915
  · exact B2179919
  · exact B2179923
  · exact B2179927
  · exact B2179931
  · exact B2179935
  · exact B2179939
  · exact B2179943
  · exact B2179947
  · exact B2179951
  · exact B2179955
  · exact B2179959
  · exact B2179963
  · exact B2179967
  · exact B2179971
  · exact B2179975
  · exact B2179979
  · exact B2179983
  · exact B2179987
  · exact B2179991
  · exact B2179995
  · exact B2179999
  · exact B2180003
  · exact B2180007
  · exact B2180011
  · exact B2180015
  · exact B2180019
  · exact B2180023
  · exact B2180027
  · exact B2180031
  · exact B2180035
  · exact B2180039
  · exact B2180043
  · exact B2180047
  · exact B2180051
  · exact B2180055
  · exact B2180059
  · exact B2180063
  · exact B2180067
  · exact B2180071
  · exact B2180075
  · exact B2180079
  · exact B2180083
  · exact B2180087
  · exact B2180091
  · exact B2180095
  · exact B2180099
  · exact B2180103
  · exact B2180107
  · exact B2180111
  · exact B2180115
  · exact B2180119
  · exact B2180123
  · exact B2180127
  · exact B2180131
  · exact B2180135
  · exact B2180139
  · exact B2180143
  · exact B2180147
  · exact B2180151
  · exact B2180155
  · exact B2180159
  · exact B2180163
  · exact B2180167
  · exact B2180171
  · exact B2180175
  · exact B2180179
  · exact B2180183
  · exact B2180187
  · exact B2180191
  · exact B2180195
  · exact B2180199
  · exact B2180203
  · exact B2180207
  · exact B2180211
  · exact B2180215
  · exact B2180219
  · exact B2180223
  · exact B2180227
  · exact B2180231
  · exact B2180235
  · exact B2180239
  · exact B2180243
  · exact B2180247
  · exact B2180251
  · exact B2180255
  · exact B2180259
  · exact B2180263
  · exact B2180267
  · exact B2180271
  · exact B2180275
  · exact B2180279
  · exact B2180283
  · exact B2180287
  · exact B2180291
  · exact B2180295
  · exact B2180299
  · exact B2180303
  · exact B2180307
  · exact B2180311
  · exact B2180315
  · exact B2180319
  · exact B2180323
  · exact B2180327
  · exact B2180331
  · exact B2180335
  · exact B2180339
  · exact B2180343
  · exact B2180347
  · exact B2180351
  · exact B2180355
  · exact B2180359
  · exact B2180363
  · exact B2180367
  · exact B2180371
  · exact B2180375
  · exact B2180379
  · exact B2180383
  · exact B2180387
  · exact B2180391
  · exact B2180395
  · exact B2180399
  · exact B2180403
  · exact B2180407
  · exact B2180411
  · exact B2180415
  · exact B2180419
  · exact B2180423
  · exact B2180427
  · exact B2180431
  · exact B2180435
  · exact B2180439
  · exact B2180443
  · exact B2180447
  · exact B2180451
  · exact B2180455
  · exact B2180459
  · exact B2180463
  · exact B2180467
  · exact B2180471
  · exact B2180475
  · exact B2180479
  · exact B2180483
  · exact B2180487
  · exact B2180491
  · exact B2180495
  · exact B2180499
  · exact B2180503
  · exact B2180507
  · exact B2180511
  · exact B2180515
  · exact B2180519
  · exact B2180523
  · exact B2180527
  · exact B2180531
  · exact B2180535
  · exact B2180539
  · exact B2180543
  · exact B2180547
  · exact B2180551
  · exact B2180555
  · exact B2180559
  · exact B2180563
  · exact B2180567
  · exact B2180571
  · exact B2180575
  · exact B2180579
  · exact B2180583
  · exact B2180587
  · exact B2180591
  · exact B2180595
  · exact B2180599
  · exact B2180603
  · exact B2180607
  · exact B2180611
  · exact B2180615
  · exact B2180619
  · exact B2180623
  · exact B2180627
  · exact B2180631
  · exact B2180635
  · exact B2180639
  · exact B2180643
  · exact B2180647
  · exact B2180651
  · exact B2180655
  · exact B2180659
  · exact B2180663
  · exact B2180667
  · exact B2180671
  · exact B2180675
  · exact B2180679
  · exact B2180683
  · exact B2180687
  · exact B2180691
  · exact B2180695
  · exact B2180699
  · exact B2180703
  · exact B2180707
  · exact B2180711
  · exact B2180715
  · exact B2180719
  · exact B2180723
  · exact B2180727
  · exact B2180731
  · exact B2180735
  · exact B2180739
  · exact B2180743
  · exact B2180747
  · exact B2180751
  · exact B2180755
  · exact B2180759
  · exact B2180763
  · exact B2180767
  · exact B2180771
  · exact B2180775
  · exact B2180779
  · exact B2180783
  · exact B2180787
  · exact B2180791
  · exact B2180795
  · exact B2180799
  · exact B2180803
  · exact B2180807
  · exact B2180811
  · exact B2180815
  · exact B2180819
  · exact B2180823
  · exact B2180827
  · exact B2180831
  · exact B2180835
  · exact B2180839
  · exact B2180843
  · exact B2180847
  · exact B2180851
  · exact B2180855
  · exact B2180859
  · exact B2180863
  · exact B2180867
  · exact B2180871
  · exact B2180875
  · exact B2180879
  · exact B2180883
  · exact B2180887
  · exact B2180891
  · exact B2180895
  · exact B2180899
  · exact B2180903
  · exact B2180907
  · exact B2180911
  · exact B2180915
  · exact B2180919
  · exact B2180923
  · exact B2180927
  · exact B2180931
  · exact B2180935
  · exact B2180939
  · exact B2180943
  · exact B2180947
  · exact B2180951
  · exact B2180955
  · exact B2180959
  · exact B2180963
  · exact B2180967
  · exact B2180971
  · exact B2180975
  · exact B2180979
  · exact B2180983
  · exact B2180987
  · exact B2180991
  · exact B2180995
  · exact B2180999
  · exact B2181003
  · exact B2181007
  · exact B2181011
  · exact B2181015
  · exact B2181019
  · exact B2181023
  · exact B2181027
  · exact B2181031
  · exact B2181035
  · exact B2181039
  · exact B2181043
  · exact B2181047
  · exact B2181051
  · exact B2181055
  · exact B2181059
  · exact B2181063
  · exact B2181067
  · exact B2181071
  · exact B2181075
  · exact B2181079
  · exact B2181083
  · exact B2181087
  · exact B2181091
  · exact B2181095
  · exact B2181099
  · exact B2181103
  · exact B2181107
  · exact B2181111
  · exact B2181115
  · exact B2181119
  · exact B2181123
  · exact B2181127
  · exact B2181131
  · exact B2181135
  · exact B2181139
  · exact B2181143
  · exact B2181147
  · exact B2181151
  · exact B2181155
  · exact B2181159
  · exact B2181163
  · exact B2181167
  · exact B2181171
  · exact B2181175
  · exact B2181179
  · exact B2181183
  · exact B2181187
  · exact B2181191
  · exact B2181195
  · exact B2181199
  · exact B2181203
  · exact B2181207
  · exact B2181211
  · exact B2181215
  · exact B2181219
  · exact B2181223
  · exact B2181227
  · exact B2181231
  · exact B2181235
  · exact B2181239
  · exact B2181243
  · exact B2181247
  · exact B2181251
  · exact B2181255
  · exact B2181259
  · exact B2181263
  · exact B2181267
  · exact B2181271
  · exact B2181275
  · exact B2181279
  · exact B2181283
  · exact B2181287
  · exact B2181291
  · exact B2181295
  · exact B2181299
  · exact B2181303
  · exact B2181307
  · exact B2181311
  · exact B2181315
  · exact B2181319
  · exact B2181323
  · exact B2181327
  · exact B2181331
  · exact B2181335
  · exact B2181339
  · exact B2181343
  · exact B2181347
  · exact B2181351
  · exact B2181355
  · exact B2181359
  · exact B2181363
  · exact B2181367
  · exact B2181371
  · exact B2181375
  · exact B2181379
  · exact B2181383
  · exact B2181387
  · exact B2181391
  · exact B2181395
  · exact B2181399
  · exact B2181403
  · exact B2181407
  · exact B2181411
  · exact B2181415
  · exact B2181419
  · exact B2181423
  · exact B2181427
  · exact B2181431
  · exact B2181435
theorem solution (m : ℕ) (hlo : 2179435 ≤ m) (hhi : m ≤ 2181435) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 544858 ≤ j := by omega
    have hj2 : j ≤ 545358 := by omega
    have hb : Blo 2179435 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
