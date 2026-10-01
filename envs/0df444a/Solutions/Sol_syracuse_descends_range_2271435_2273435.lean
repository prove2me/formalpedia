-- Prove2me | solution 1 for syracuse_descends_range_2271435_2273435
-- status  : ACCEPTED   (prove)
-- author  : @chstdu
-- created : 2026-09-23T17:49:27.810366+00:00
-- url     : https://prove2.me/submissions/132e5516-e1ee-40f1-8aa4-ae65251231e1

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

theorem B2555365 : Blo 2271435 2555365 := bbase (se 4 (by rfl) ⟨239565, by rfl⟩ : syracuseStep 2555365 = 479131) (by norm_num)
theorem B3407153 : Blo 2271435 3407153 := bstep (se 2 (by rfl) ⟨1277682, by rfl⟩ : syracuseStep 3407153 = 2555365) B2555365
theorem B2271435 : Blo 2271435 2271435 := bstep (se 1 (by rfl) ⟨1703576, by rfl⟩ : syracuseStep 2271435 = 3407153) B3407153
theorem B5457613 : Blo 2271435 5457613 := bbase (se 3 (by rfl) ⟨1023302, by rfl⟩ : syracuseStep 5457613 = 2046605) (by norm_num)
theorem B7276817 : Blo 2271435 7276817 := bstep (se 2 (by rfl) ⟨2728806, by rfl⟩ : syracuseStep 7276817 = 5457613) B5457613
theorem B4851211 : Blo 2271435 4851211 := bstep (se 1 (by rfl) ⟨3638408, by rfl⟩ : syracuseStep 4851211 = 7276817) B7276817
theorem B6468281 : Blo 2271435 6468281 := bstep (se 2 (by rfl) ⟨2425605, by rfl⟩ : syracuseStep 6468281 = 4851211) B4851211
theorem B4312187 : Blo 2271435 4312187 := bstep (se 1 (by rfl) ⟨3234140, by rfl⟩ : syracuseStep 4312187 = 6468281) B6468281
theorem B2874791 : Blo 2271435 2874791 := bstep (se 1 (by rfl) ⟨2156093, by rfl⟩ : syracuseStep 2874791 = 4312187) B4312187
theorem B7666109 : Blo 2271435 7666109 := bstep (se 3 (by rfl) ⟨1437395, by rfl⟩ : syracuseStep 7666109 = 2874791) B2874791
theorem B5110739 : Blo 2271435 5110739 := bstep (se 1 (by rfl) ⟨3833054, by rfl⟩ : syracuseStep 5110739 = 7666109) B7666109
theorem B3407159 : Blo 2271435 3407159 := bstep (se 1 (by rfl) ⟨2555369, by rfl⟩ : syracuseStep 3407159 = 5110739) B5110739
theorem B2271439 : Blo 2271435 2271439 := bstep (se 1 (by rfl) ⟨1703579, by rfl⟩ : syracuseStep 2271439 = 3407159) B3407159
theorem B3407165 : Blo 2271435 3407165 := bbase (se 3 (by rfl) ⟨638843, by rfl⟩ : syracuseStep 3407165 = 1277687) (by norm_num)
theorem B2271443 : Blo 2271435 2271443 := bstep (se 1 (by rfl) ⟨1703582, by rfl⟩ : syracuseStep 2271443 = 3407165) B3407165
theorem B5110757 : Blo 2271435 5110757 := bbase (se 4 (by rfl) ⟨479133, by rfl⟩ : syracuseStep 5110757 = 958267) (by norm_num)
theorem B3407171 : Blo 2271435 3407171 := bstep (se 1 (by rfl) ⟨2555378, by rfl⟩ : syracuseStep 3407171 = 5110757) B5110757
theorem B2271447 : Blo 2271435 2271447 := bstep (se 1 (by rfl) ⟨1703585, by rfl⟩ : syracuseStep 2271447 = 3407171) B3407171
theorem B5749613 : Blo 2271435 5749613 := bbase (se 3 (by rfl) ⟨1078052, by rfl⟩ : syracuseStep 5749613 = 2156105) (by norm_num)
theorem B3833075 : Blo 2271435 3833075 := bstep (se 1 (by rfl) ⟨2874806, by rfl⟩ : syracuseStep 3833075 = 5749613) B5749613
theorem B2555383 : Blo 2271435 2555383 := bstep (se 1 (by rfl) ⟨1916537, by rfl⟩ : syracuseStep 2555383 = 3833075) B3833075
theorem B3407177 : Blo 2271435 3407177 := bstep (se 2 (by rfl) ⟨1277691, by rfl⟩ : syracuseStep 3407177 = 2555383) B2555383
theorem B2271451 : Blo 2271435 2271451 := bstep (se 1 (by rfl) ⟨1703588, by rfl⟩ : syracuseStep 2271451 = 3407177) B3407177
theorem B4851245 : Blo 2271435 4851245 := bbase (se 3 (by rfl) ⟨909608, by rfl⟩ : syracuseStep 4851245 = 1819217) (by norm_num)
theorem B3234163 : Blo 2271435 3234163 := bstep (se 1 (by rfl) ⟨2425622, by rfl⟩ : syracuseStep 3234163 = 4851245) B4851245
theorem B4312217 : Blo 2271435 4312217 := bstep (se 2 (by rfl) ⟨1617081, by rfl⟩ : syracuseStep 4312217 = 3234163) B3234163
theorem B11499245 : Blo 2271435 11499245 := bstep (se 3 (by rfl) ⟨2156108, by rfl⟩ : syracuseStep 11499245 = 4312217) B4312217
theorem B7666163 : Blo 2271435 7666163 := bstep (se 1 (by rfl) ⟨5749622, by rfl⟩ : syracuseStep 7666163 = 11499245) B11499245
theorem B5110775 : Blo 2271435 5110775 := bstep (se 1 (by rfl) ⟨3833081, by rfl⟩ : syracuseStep 5110775 = 7666163) B7666163
theorem B3407183 : Blo 2271435 3407183 := bstep (se 1 (by rfl) ⟨2555387, by rfl⟩ : syracuseStep 3407183 = 5110775) B5110775
theorem B2271455 : Blo 2271435 2271455 := bstep (se 1 (by rfl) ⟨1703591, by rfl⟩ : syracuseStep 2271455 = 3407183) B3407183
theorem B3407189 : Blo 2271435 3407189 := bbase (se 11 (by rfl) ⟨2495, by rfl⟩ : syracuseStep 3407189 = 4991) (by norm_num)
theorem B2271459 : Blo 2271435 2271459 := bstep (se 1 (by rfl) ⟨1703594, by rfl⟩ : syracuseStep 2271459 = 3407189) B3407189
theorem B5180525 : Blo 2271435 5180525 := bbase (se 3 (by rfl) ⟨971348, by rfl⟩ : syracuseStep 5180525 = 1942697) (by norm_num)
theorem B3453683 : Blo 2271435 3453683 := bstep (se 1 (by rfl) ⟨2590262, by rfl⟩ : syracuseStep 3453683 = 5180525) B5180525
theorem B9209821 : Blo 2271435 9209821 := bstep (se 3 (by rfl) ⟨1726841, by rfl⟩ : syracuseStep 9209821 = 3453683) B3453683
theorem B12279761 : Blo 2271435 12279761 := bstep (se 2 (by rfl) ⟨4604910, by rfl⟩ : syracuseStep 12279761 = 9209821) B9209821
theorem B8186507 : Blo 2271435 8186507 := bstep (se 1 (by rfl) ⟨6139880, by rfl⟩ : syracuseStep 8186507 = 12279761) B12279761
theorem B5457671 : Blo 2271435 5457671 := bstep (se 1 (by rfl) ⟨4093253, by rfl⟩ : syracuseStep 5457671 = 8186507) B8186507
theorem B3638447 : Blo 2271435 3638447 := bstep (se 1 (by rfl) ⟨2728835, by rfl⟩ : syracuseStep 3638447 = 5457671) B5457671
theorem B2425631 : Blo 2271435 2425631 := bstep (se 1 (by rfl) ⟨1819223, by rfl⟩ : syracuseStep 2425631 = 3638447) B3638447
theorem B6468349 : Blo 2271435 6468349 := bstep (se 3 (by rfl) ⟨1212815, by rfl⟩ : syracuseStep 6468349 = 2425631) B2425631
theorem B8624465 : Blo 2271435 8624465 := bstep (se 2 (by rfl) ⟨3234174, by rfl⟩ : syracuseStep 8624465 = 6468349) B6468349
theorem B5749643 : Blo 2271435 5749643 := bstep (se 1 (by rfl) ⟨4312232, by rfl⟩ : syracuseStep 5749643 = 8624465) B8624465
theorem B3833095 : Blo 2271435 3833095 := bstep (se 1 (by rfl) ⟨2874821, by rfl⟩ : syracuseStep 3833095 = 5749643) B5749643
theorem B5110793 : Blo 2271435 5110793 := bstep (se 2 (by rfl) ⟨1916547, by rfl⟩ : syracuseStep 5110793 = 3833095) B3833095
theorem B3407195 : Blo 2271435 3407195 := bstep (se 1 (by rfl) ⟨2555396, by rfl⟩ : syracuseStep 3407195 = 5110793) B5110793
theorem B2271463 : Blo 2271435 2271463 := bstep (se 1 (by rfl) ⟨1703597, by rfl⟩ : syracuseStep 2271463 = 3407195) B3407195
theorem B2555401 : Blo 2271435 2555401 := bbase (se 2 (by rfl) ⟨958275, by rfl⟩ : syracuseStep 2555401 = 1916551) (by norm_num)
theorem B3407201 : Blo 2271435 3407201 := bstep (se 2 (by rfl) ⟨1277700, by rfl⟩ : syracuseStep 3407201 = 2555401) B2555401
theorem B2271467 : Blo 2271435 2271467 := bstep (se 1 (by rfl) ⟨1703600, by rfl⟩ : syracuseStep 2271467 = 3407201) B3407201
theorem B32746133 : Blo 2271435 32746133 := bbase (se 6 (by rfl) ⟨767487, by rfl⟩ : syracuseStep 32746133 = 1534975) (by norm_num)
theorem B21830755 : Blo 2271435 21830755 := bstep (se 1 (by rfl) ⟨16373066, by rfl⟩ : syracuseStep 21830755 = 32746133) B32746133
theorem B29107673 : Blo 2271435 29107673 := bstep (se 2 (by rfl) ⟨10915377, by rfl⟩ : syracuseStep 29107673 = 21830755) B21830755
theorem B19405115 : Blo 2271435 19405115 := bstep (se 1 (by rfl) ⟨14553836, by rfl⟩ : syracuseStep 19405115 = 29107673) B29107673
theorem B12936743 : Blo 2271435 12936743 := bstep (se 1 (by rfl) ⟨9702557, by rfl⟩ : syracuseStep 12936743 = 19405115) B19405115
theorem B8624495 : Blo 2271435 8624495 := bstep (se 1 (by rfl) ⟨6468371, by rfl⟩ : syracuseStep 8624495 = 12936743) B12936743
theorem B5749663 : Blo 2271435 5749663 := bstep (se 1 (by rfl) ⟨4312247, by rfl⟩ : syracuseStep 5749663 = 8624495) B8624495
theorem B7666217 : Blo 2271435 7666217 := bstep (se 2 (by rfl) ⟨2874831, by rfl⟩ : syracuseStep 7666217 = 5749663) B5749663
theorem B5110811 : Blo 2271435 5110811 := bstep (se 1 (by rfl) ⟨3833108, by rfl⟩ : syracuseStep 5110811 = 7666217) B7666217
theorem B3407207 : Blo 2271435 3407207 := bstep (se 1 (by rfl) ⟨2555405, by rfl⟩ : syracuseStep 3407207 = 5110811) B5110811
theorem B2271471 : Blo 2271435 2271471 := bstep (se 1 (by rfl) ⟨1703603, by rfl⟩ : syracuseStep 2271471 = 3407207) B3407207
theorem B3407213 : Blo 2271435 3407213 := bbase (se 3 (by rfl) ⟨638852, by rfl⟩ : syracuseStep 3407213 = 1277705) (by norm_num)
theorem B2271475 : Blo 2271435 2271475 := bstep (se 1 (by rfl) ⟨1703606, by rfl⟩ : syracuseStep 2271475 = 3407213) B3407213
theorem B5110829 : Blo 2271435 5110829 := bbase (se 3 (by rfl) ⟨958280, by rfl⟩ : syracuseStep 5110829 = 1916561) (by norm_num)
theorem B3407219 : Blo 2271435 3407219 := bstep (se 1 (by rfl) ⟨2555414, by rfl⟩ : syracuseStep 3407219 = 5110829) B5110829
theorem B2271479 : Blo 2271435 2271479 := bstep (se 1 (by rfl) ⟨1703609, by rfl⟩ : syracuseStep 2271479 = 3407219) B3407219
theorem B10361141 : Blo 2271435 10361141 := bbase (se 5 (by rfl) ⟨485678, by rfl⟩ : syracuseStep 10361141 = 971357) (by norm_num)
theorem B6907427 : Blo 2271435 6907427 := bstep (se 1 (by rfl) ⟨5180570, by rfl⟩ : syracuseStep 6907427 = 10361141) B10361141
theorem B4604951 : Blo 2271435 4604951 := bstep (se 1 (by rfl) ⟨3453713, by rfl⟩ : syracuseStep 4604951 = 6907427) B6907427
theorem B12279869 : Blo 2271435 12279869 := bstep (se 3 (by rfl) ⟨2302475, by rfl⟩ : syracuseStep 12279869 = 4604951) B4604951
theorem B8186579 : Blo 2271435 8186579 := bstep (se 1 (by rfl) ⟨6139934, by rfl⟩ : syracuseStep 8186579 = 12279869) B12279869
theorem B5457719 : Blo 2271435 5457719 := bstep (se 1 (by rfl) ⟨4093289, by rfl⟩ : syracuseStep 5457719 = 8186579) B8186579
theorem B14553917 : Blo 2271435 14553917 := bstep (se 3 (by rfl) ⟨2728859, by rfl⟩ : syracuseStep 14553917 = 5457719) B5457719
theorem B9702611 : Blo 2271435 9702611 := bstep (se 1 (by rfl) ⟨7276958, by rfl⟩ : syracuseStep 9702611 = 14553917) B14553917
theorem B6468407 : Blo 2271435 6468407 := bstep (se 1 (by rfl) ⟨4851305, by rfl⟩ : syracuseStep 6468407 = 9702611) B9702611
theorem B4312271 : Blo 2271435 4312271 := bstep (se 1 (by rfl) ⟨3234203, by rfl⟩ : syracuseStep 4312271 = 6468407) B6468407
theorem B2874847 : Blo 2271435 2874847 := bstep (se 1 (by rfl) ⟨2156135, by rfl⟩ : syracuseStep 2874847 = 4312271) B4312271
theorem B3833129 : Blo 2271435 3833129 := bstep (se 2 (by rfl) ⟨1437423, by rfl⟩ : syracuseStep 3833129 = 2874847) B2874847
theorem B2555419 : Blo 2271435 2555419 := bstep (se 1 (by rfl) ⟨1916564, by rfl⟩ : syracuseStep 2555419 = 3833129) B3833129
theorem B3407225 : Blo 2271435 3407225 := bstep (se 2 (by rfl) ⟨1277709, by rfl⟩ : syracuseStep 3407225 = 2555419) B2555419
theorem B2271483 : Blo 2271435 2271483 := bstep (se 1 (by rfl) ⟨1703612, by rfl⟩ : syracuseStep 2271483 = 3407225) B3407225
theorem B15753781 : Blo 2271435 15753781 := bbase (se 5 (by rfl) ⟨738458, by rfl⟩ : syracuseStep 15753781 = 1476917) (by norm_num)
theorem B84020165 : Blo 2271435 84020165 := bstep (se 4 (by rfl) ⟨7876890, by rfl⟩ : syracuseStep 84020165 = 15753781) B15753781
theorem B56013443 : Blo 2271435 56013443 := bstep (se 1 (by rfl) ⟨42010082, by rfl⟩ : syracuseStep 56013443 = 84020165) B84020165
theorem B37342295 : Blo 2271435 37342295 := bstep (se 1 (by rfl) ⟨28006721, by rfl⟩ : syracuseStep 37342295 = 56013443) B56013443
theorem B24894863 : Blo 2271435 24894863 := bstep (se 1 (by rfl) ⟨18671147, by rfl⟩ : syracuseStep 24894863 = 37342295) B37342295
theorem B16596575 : Blo 2271435 16596575 := bstep (se 1 (by rfl) ⟨12447431, by rfl⟩ : syracuseStep 16596575 = 24894863) B24894863
theorem B11064383 : Blo 2271435 11064383 := bstep (se 1 (by rfl) ⟨8298287, by rfl⟩ : syracuseStep 11064383 = 16596575) B16596575
theorem B7376255 : Blo 2271435 7376255 := bstep (se 1 (by rfl) ⟨5532191, by rfl⟩ : syracuseStep 7376255 = 11064383) B11064383
theorem B4917503 : Blo 2271435 4917503 := bstep (se 1 (by rfl) ⟨3688127, by rfl⟩ : syracuseStep 4917503 = 7376255) B7376255
theorem B3278335 : Blo 2271435 3278335 := bstep (se 1 (by rfl) ⟨2458751, by rfl⟩ : syracuseStep 3278335 = 4917503) B4917503
theorem B4371113 : Blo 2271435 4371113 := bstep (se 2 (by rfl) ⟨1639167, by rfl⟩ : syracuseStep 4371113 = 3278335) B3278335
theorem B2914075 : Blo 2271435 2914075 := bstep (se 1 (by rfl) ⟨2185556, by rfl⟩ : syracuseStep 2914075 = 4371113) B4371113
theorem B15541733 : Blo 2271435 15541733 := bstep (se 4 (by rfl) ⟨1457037, by rfl⟩ : syracuseStep 15541733 = 2914075) B2914075
theorem B41444621 : Blo 2271435 41444621 := bstep (se 3 (by rfl) ⟨7770866, by rfl⟩ : syracuseStep 41444621 = 15541733) B15541733
theorem B27629747 : Blo 2271435 27629747 := bstep (se 1 (by rfl) ⟨20722310, by rfl⟩ : syracuseStep 27629747 = 41444621) B41444621
theorem B18419831 : Blo 2271435 18419831 := bstep (se 1 (by rfl) ⟨13814873, by rfl⟩ : syracuseStep 18419831 = 27629747) B27629747
theorem B12279887 : Blo 2271435 12279887 := bstep (se 1 (by rfl) ⟨9209915, by rfl⟩ : syracuseStep 12279887 = 18419831) B18419831
theorem B8186591 : Blo 2271435 8186591 := bstep (se 1 (by rfl) ⟨6139943, by rfl⟩ : syracuseStep 8186591 = 12279887) B12279887
theorem B5457727 : Blo 2271435 5457727 := bstep (se 1 (by rfl) ⟨4093295, by rfl⟩ : syracuseStep 5457727 = 8186591) B8186591
theorem B7276969 : Blo 2271435 7276969 := bstep (se 2 (by rfl) ⟨2728863, by rfl⟩ : syracuseStep 7276969 = 5457727) B5457727
theorem B38810501 : Blo 2271435 38810501 := bstep (se 4 (by rfl) ⟨3638484, by rfl⟩ : syracuseStep 38810501 = 7276969) B7276969
theorem B25873667 : Blo 2271435 25873667 := bstep (se 1 (by rfl) ⟨19405250, by rfl⟩ : syracuseStep 25873667 = 38810501) B38810501
theorem B17249111 : Blo 2271435 17249111 := bstep (se 1 (by rfl) ⟨12936833, by rfl⟩ : syracuseStep 17249111 = 25873667) B25873667
theorem B11499407 : Blo 2271435 11499407 := bstep (se 1 (by rfl) ⟨8624555, by rfl⟩ : syracuseStep 11499407 = 17249111) B17249111
theorem B7666271 : Blo 2271435 7666271 := bstep (se 1 (by rfl) ⟨5749703, by rfl⟩ : syracuseStep 7666271 = 11499407) B11499407
theorem B5110847 : Blo 2271435 5110847 := bstep (se 1 (by rfl) ⟨3833135, by rfl⟩ : syracuseStep 5110847 = 7666271) B7666271
theorem B3407231 : Blo 2271435 3407231 := bstep (se 1 (by rfl) ⟨2555423, by rfl⟩ : syracuseStep 3407231 = 5110847) B5110847
theorem B2271487 : Blo 2271435 2271487 := bstep (se 1 (by rfl) ⟨1703615, by rfl⟩ : syracuseStep 2271487 = 3407231) B3407231
theorem B3407237 : Blo 2271435 3407237 := bbase (se 4 (by rfl) ⟨319428, by rfl⟩ : syracuseStep 3407237 = 638857) (by norm_num)
theorem B2271491 : Blo 2271435 2271491 := bstep (se 1 (by rfl) ⟨1703618, by rfl⟩ : syracuseStep 2271491 = 3407237) B3407237
theorem B3833149 : Blo 2271435 3833149 := bbase (se 3 (by rfl) ⟨718715, by rfl⟩ : syracuseStep 3833149 = 1437431) (by norm_num)
theorem B5110865 : Blo 2271435 5110865 := bstep (se 2 (by rfl) ⟨1916574, by rfl⟩ : syracuseStep 5110865 = 3833149) B3833149
theorem B3407243 : Blo 2271435 3407243 := bstep (se 1 (by rfl) ⟨2555432, by rfl⟩ : syracuseStep 3407243 = 5110865) B5110865
theorem B2271495 : Blo 2271435 2271495 := bstep (se 1 (by rfl) ⟨1703621, by rfl⟩ : syracuseStep 2271495 = 3407243) B3407243
theorem B2555437 : Blo 2271435 2555437 := bbase (se 3 (by rfl) ⟨479144, by rfl⟩ : syracuseStep 2555437 = 958289) (by norm_num)
theorem B3407249 : Blo 2271435 3407249 := bstep (se 2 (by rfl) ⟨1277718, by rfl⟩ : syracuseStep 3407249 = 2555437) B2555437
theorem B2271499 : Blo 2271435 2271499 := bstep (se 1 (by rfl) ⟨1703624, by rfl⟩ : syracuseStep 2271499 = 3407249) B3407249
theorem B7666325 : Blo 2271435 7666325 := bbase (se 6 (by rfl) ⟨179679, by rfl⟩ : syracuseStep 7666325 = 359359) (by norm_num)
theorem B5110883 : Blo 2271435 5110883 := bstep (se 1 (by rfl) ⟨3833162, by rfl⟩ : syracuseStep 5110883 = 7666325) B7666325
theorem B3407255 : Blo 2271435 3407255 := bstep (se 1 (by rfl) ⟨2555441, by rfl⟩ : syracuseStep 3407255 = 5110883) B5110883
theorem B2271503 : Blo 2271435 2271503 := bstep (se 1 (by rfl) ⟨1703627, by rfl⟩ : syracuseStep 2271503 = 3407255) B3407255
theorem B3407261 : Blo 2271435 3407261 := bbase (se 3 (by rfl) ⟨638861, by rfl⟩ : syracuseStep 3407261 = 1277723) (by norm_num)
theorem B2271507 : Blo 2271435 2271507 := bstep (se 1 (by rfl) ⟨1703630, by rfl⟩ : syracuseStep 2271507 = 3407261) B3407261
theorem B5110901 : Blo 2271435 5110901 := bbase (se 5 (by rfl) ⟨239573, by rfl⟩ : syracuseStep 5110901 = 479147) (by norm_num)
theorem B3407267 : Blo 2271435 3407267 := bstep (se 1 (by rfl) ⟨2555450, by rfl⟩ : syracuseStep 3407267 = 5110901) B5110901
theorem B2271511 : Blo 2271435 2271511 := bstep (se 1 (by rfl) ⟨1703633, by rfl⟩ : syracuseStep 2271511 = 3407267) B3407267
theorem B19405493 : Blo 2271435 19405493 := bbase (se 5 (by rfl) ⟨909632, by rfl⟩ : syracuseStep 19405493 = 1819265) (by norm_num)
theorem B12936995 : Blo 2271435 12936995 := bstep (se 1 (by rfl) ⟨9702746, by rfl⟩ : syracuseStep 12936995 = 19405493) B19405493
theorem B8624663 : Blo 2271435 8624663 := bstep (se 1 (by rfl) ⟨6468497, by rfl⟩ : syracuseStep 8624663 = 12936995) B12936995
theorem B5749775 : Blo 2271435 5749775 := bstep (se 1 (by rfl) ⟨4312331, by rfl⟩ : syracuseStep 5749775 = 8624663) B8624663
theorem B3833183 : Blo 2271435 3833183 := bstep (se 1 (by rfl) ⟨2874887, by rfl⟩ : syracuseStep 3833183 = 5749775) B5749775
theorem B2555455 : Blo 2271435 2555455 := bstep (se 1 (by rfl) ⟨1916591, by rfl⟩ : syracuseStep 2555455 = 3833183) B3833183
theorem B3407273 : Blo 2271435 3407273 := bstep (se 2 (by rfl) ⟨1277727, by rfl⟩ : syracuseStep 3407273 = 2555455) B2555455
theorem B2271515 : Blo 2271435 2271515 := bstep (se 1 (by rfl) ⟨1703636, by rfl⟩ : syracuseStep 2271515 = 3407273) B3407273
theorem B8624677 : Blo 2271435 8624677 := bbase (se 4 (by rfl) ⟨808563, by rfl⟩ : syracuseStep 8624677 = 1617127) (by norm_num)
theorem B11499569 : Blo 2271435 11499569 := bstep (se 2 (by rfl) ⟨4312338, by rfl⟩ : syracuseStep 11499569 = 8624677) B8624677
theorem B7666379 : Blo 2271435 7666379 := bstep (se 1 (by rfl) ⟨5749784, by rfl⟩ : syracuseStep 7666379 = 11499569) B11499569
theorem B5110919 : Blo 2271435 5110919 := bstep (se 1 (by rfl) ⟨3833189, by rfl⟩ : syracuseStep 5110919 = 7666379) B7666379
theorem B3407279 : Blo 2271435 3407279 := bstep (se 1 (by rfl) ⟨2555459, by rfl⟩ : syracuseStep 3407279 = 5110919) B5110919
theorem B2271519 : Blo 2271435 2271519 := bstep (se 1 (by rfl) ⟨1703639, by rfl⟩ : syracuseStep 2271519 = 3407279) B3407279
theorem B3407285 : Blo 2271435 3407285 := bbase (se 5 (by rfl) ⟨159716, by rfl⟩ : syracuseStep 3407285 = 319433) (by norm_num)
theorem B2271523 : Blo 2271435 2271523 := bstep (se 1 (by rfl) ⟨1703642, by rfl⟩ : syracuseStep 2271523 = 3407285) B3407285
theorem B5749805 : Blo 2271435 5749805 := bbase (se 3 (by rfl) ⟨1078088, by rfl⟩ : syracuseStep 5749805 = 2156177) (by norm_num)
theorem B3833203 : Blo 2271435 3833203 := bstep (se 1 (by rfl) ⟨2874902, by rfl⟩ : syracuseStep 3833203 = 5749805) B5749805
theorem B5110937 : Blo 2271435 5110937 := bstep (se 2 (by rfl) ⟨1916601, by rfl⟩ : syracuseStep 5110937 = 3833203) B3833203
theorem B3407291 : Blo 2271435 3407291 := bstep (se 1 (by rfl) ⟨2555468, by rfl⟩ : syracuseStep 3407291 = 5110937) B5110937
theorem B2271527 : Blo 2271435 2271527 := bstep (se 1 (by rfl) ⟨1703645, by rfl⟩ : syracuseStep 2271527 = 3407291) B3407291
theorem B2555473 : Blo 2271435 2555473 := bbase (se 2 (by rfl) ⟨958302, by rfl⟩ : syracuseStep 2555473 = 1916605) (by norm_num)
theorem B3407297 : Blo 2271435 3407297 := bstep (se 2 (by rfl) ⟨1277736, by rfl⟩ : syracuseStep 3407297 = 2555473) B2555473
theorem B2271531 : Blo 2271435 2271531 := bstep (se 1 (by rfl) ⟨1703648, by rfl⟩ : syracuseStep 2271531 = 3407297) B3407297
theorem B3234277 : Blo 2271435 3234277 := bbase (se 4 (by rfl) ⟨303213, by rfl⟩ : syracuseStep 3234277 = 606427) (by norm_num)
theorem B4312369 : Blo 2271435 4312369 := bstep (se 2 (by rfl) ⟨1617138, by rfl⟩ : syracuseStep 4312369 = 3234277) B3234277
theorem B5749825 : Blo 2271435 5749825 := bstep (se 2 (by rfl) ⟨2156184, by rfl⟩ : syracuseStep 5749825 = 4312369) B4312369
theorem B7666433 : Blo 2271435 7666433 := bstep (se 2 (by rfl) ⟨2874912, by rfl⟩ : syracuseStep 7666433 = 5749825) B5749825
theorem B5110955 : Blo 2271435 5110955 := bstep (se 1 (by rfl) ⟨3833216, by rfl⟩ : syracuseStep 5110955 = 7666433) B7666433
theorem B3407303 : Blo 2271435 3407303 := bstep (se 1 (by rfl) ⟨2555477, by rfl⟩ : syracuseStep 3407303 = 5110955) B5110955
theorem B2271535 : Blo 2271435 2271535 := bstep (se 1 (by rfl) ⟨1703651, by rfl⟩ : syracuseStep 2271535 = 3407303) B3407303
theorem B3407309 : Blo 2271435 3407309 := bbase (se 3 (by rfl) ⟨638870, by rfl⟩ : syracuseStep 3407309 = 1277741) (by norm_num)
theorem B2271539 : Blo 2271435 2271539 := bstep (se 1 (by rfl) ⟨1703654, by rfl⟩ : syracuseStep 2271539 = 3407309) B3407309
theorem B5110973 : Blo 2271435 5110973 := bbase (se 3 (by rfl) ⟨958307, by rfl⟩ : syracuseStep 5110973 = 1916615) (by norm_num)
theorem B3407315 : Blo 2271435 3407315 := bstep (se 1 (by rfl) ⟨2555486, by rfl⟩ : syracuseStep 3407315 = 5110973) B5110973
theorem B2271543 : Blo 2271435 2271543 := bstep (se 1 (by rfl) ⟨1703657, by rfl⟩ : syracuseStep 2271543 = 3407315) B3407315
theorem B3833237 : Blo 2271435 3833237 := bbase (se 6 (by rfl) ⟨89841, by rfl⟩ : syracuseStep 3833237 = 179683) (by norm_num)
theorem B2555491 : Blo 2271435 2555491 := bstep (se 1 (by rfl) ⟨1916618, by rfl⟩ : syracuseStep 2555491 = 3833237) B3833237
theorem B3407321 : Blo 2271435 3407321 := bstep (se 2 (by rfl) ⟨1277745, by rfl⟩ : syracuseStep 3407321 = 2555491) B2555491
theorem B2271547 : Blo 2271435 2271547 := bstep (se 1 (by rfl) ⟨1703660, by rfl⟩ : syracuseStep 2271547 = 3407321) B3407321
theorem B6140117 : Blo 2271435 6140117 := bbase (se 7 (by rfl) ⟨71954, by rfl⟩ : syracuseStep 6140117 = 143909) (by norm_num)
theorem B4093411 : Blo 2271435 4093411 := bstep (se 1 (by rfl) ⟨3070058, by rfl⟩ : syracuseStep 4093411 = 6140117) B6140117
theorem B5457881 : Blo 2271435 5457881 := bstep (se 2 (by rfl) ⟨2046705, by rfl⟩ : syracuseStep 5457881 = 4093411) B4093411
theorem B14554349 : Blo 2271435 14554349 := bstep (se 3 (by rfl) ⟨2728940, by rfl⟩ : syracuseStep 14554349 = 5457881) B5457881
theorem B9702899 : Blo 2271435 9702899 := bstep (se 1 (by rfl) ⟨7277174, by rfl⟩ : syracuseStep 9702899 = 14554349) B14554349
theorem B6468599 : Blo 2271435 6468599 := bstep (se 1 (by rfl) ⟨4851449, by rfl⟩ : syracuseStep 6468599 = 9702899) B9702899
theorem B17249597 : Blo 2271435 17249597 := bstep (se 3 (by rfl) ⟨3234299, by rfl⟩ : syracuseStep 17249597 = 6468599) B6468599
theorem B11499731 : Blo 2271435 11499731 := bstep (se 1 (by rfl) ⟨8624798, by rfl⟩ : syracuseStep 11499731 = 17249597) B17249597
theorem B7666487 : Blo 2271435 7666487 := bstep (se 1 (by rfl) ⟨5749865, by rfl⟩ : syracuseStep 7666487 = 11499731) B11499731
theorem B5110991 : Blo 2271435 5110991 := bstep (se 1 (by rfl) ⟨3833243, by rfl⟩ : syracuseStep 5110991 = 7666487) B7666487
theorem B3407327 : Blo 2271435 3407327 := bstep (se 1 (by rfl) ⟨2555495, by rfl⟩ : syracuseStep 3407327 = 5110991) B5110991
theorem B2271551 : Blo 2271435 2271551 := bstep (se 1 (by rfl) ⟨1703663, by rfl⟩ : syracuseStep 2271551 = 3407327) B3407327
theorem B3407333 : Blo 2271435 3407333 := bbase (se 4 (by rfl) ⟨319437, by rfl⟩ : syracuseStep 3407333 = 638875) (by norm_num)
theorem B2271555 : Blo 2271435 2271555 := bstep (se 1 (by rfl) ⟨1703666, by rfl⟩ : syracuseStep 2271555 = 3407333) B3407333
theorem B21831605 : Blo 2271435 21831605 := bbase (se 5 (by rfl) ⟨1023356, by rfl⟩ : syracuseStep 21831605 = 2046713) (by norm_num)
theorem B14554403 : Blo 2271435 14554403 := bstep (se 1 (by rfl) ⟨10915802, by rfl⟩ : syracuseStep 14554403 = 21831605) B21831605
theorem B9702935 : Blo 2271435 9702935 := bstep (se 1 (by rfl) ⟨7277201, by rfl⟩ : syracuseStep 9702935 = 14554403) B14554403
theorem B6468623 : Blo 2271435 6468623 := bstep (se 1 (by rfl) ⟨4851467, by rfl⟩ : syracuseStep 6468623 = 9702935) B9702935
theorem B4312415 : Blo 2271435 4312415 := bstep (se 1 (by rfl) ⟨3234311, by rfl⟩ : syracuseStep 4312415 = 6468623) B6468623
theorem B2874943 : Blo 2271435 2874943 := bstep (se 1 (by rfl) ⟨2156207, by rfl⟩ : syracuseStep 2874943 = 4312415) B4312415
theorem B3833257 : Blo 2271435 3833257 := bstep (se 2 (by rfl) ⟨1437471, by rfl⟩ : syracuseStep 3833257 = 2874943) B2874943
theorem B5111009 : Blo 2271435 5111009 := bstep (se 2 (by rfl) ⟨1916628, by rfl⟩ : syracuseStep 5111009 = 3833257) B3833257
theorem B3407339 : Blo 2271435 3407339 := bstep (se 1 (by rfl) ⟨2555504, by rfl⟩ : syracuseStep 3407339 = 5111009) B5111009
theorem B2271559 : Blo 2271435 2271559 := bstep (se 1 (by rfl) ⟨1703669, by rfl⟩ : syracuseStep 2271559 = 3407339) B3407339
theorem B2555509 : Blo 2271435 2555509 := bbase (se 5 (by rfl) ⟨119789, by rfl⟩ : syracuseStep 2555509 = 239579) (by norm_num)
theorem B3407345 : Blo 2271435 3407345 := bstep (se 2 (by rfl) ⟨1277754, by rfl⟩ : syracuseStep 3407345 = 2555509) B2555509
theorem B2271563 : Blo 2271435 2271563 := bstep (se 1 (by rfl) ⟨1703672, by rfl⟩ : syracuseStep 2271563 = 3407345) B3407345
theorem B2874953 : Blo 2271435 2874953 := bbase (se 2 (by rfl) ⟨1078107, by rfl⟩ : syracuseStep 2874953 = 2156215) (by norm_num)
theorem B7666541 : Blo 2271435 7666541 := bstep (se 3 (by rfl) ⟨1437476, by rfl⟩ : syracuseStep 7666541 = 2874953) B2874953
theorem B5111027 : Blo 2271435 5111027 := bstep (se 1 (by rfl) ⟨3833270, by rfl⟩ : syracuseStep 5111027 = 7666541) B7666541
theorem B3407351 : Blo 2271435 3407351 := bstep (se 1 (by rfl) ⟨2555513, by rfl⟩ : syracuseStep 3407351 = 5111027) B5111027
theorem B2271567 : Blo 2271435 2271567 := bstep (se 1 (by rfl) ⟨1703675, by rfl⟩ : syracuseStep 2271567 = 3407351) B3407351
theorem B3407357 : Blo 2271435 3407357 := bbase (se 3 (by rfl) ⟨638879, by rfl⟩ : syracuseStep 3407357 = 1277759) (by norm_num)
theorem B2271571 : Blo 2271435 2271571 := bstep (se 1 (by rfl) ⟨1703678, by rfl⟩ : syracuseStep 2271571 = 3407357) B3407357
theorem B5111045 : Blo 2271435 5111045 := bbase (se 4 (by rfl) ⟨479160, by rfl⟩ : syracuseStep 5111045 = 958321) (by norm_num)
theorem B3407363 : Blo 2271435 3407363 := bstep (se 1 (by rfl) ⟨2555522, by rfl⟩ : syracuseStep 3407363 = 5111045) B5111045
theorem B2271575 : Blo 2271435 2271575 := bstep (se 1 (by rfl) ⟨1703681, by rfl⟩ : syracuseStep 2271575 = 3407363) B3407363
theorem B4312453 : Blo 2271435 4312453 := bbase (se 4 (by rfl) ⟨404292, by rfl⟩ : syracuseStep 4312453 = 808585) (by norm_num)
theorem B5749937 : Blo 2271435 5749937 := bstep (se 2 (by rfl) ⟨2156226, by rfl⟩ : syracuseStep 5749937 = 4312453) B4312453
theorem B3833291 : Blo 2271435 3833291 := bstep (se 1 (by rfl) ⟨2874968, by rfl⟩ : syracuseStep 3833291 = 5749937) B5749937
theorem B2555527 : Blo 2271435 2555527 := bstep (se 1 (by rfl) ⟨1916645, by rfl⟩ : syracuseStep 2555527 = 3833291) B3833291
theorem B3407369 : Blo 2271435 3407369 := bstep (se 2 (by rfl) ⟨1277763, by rfl⟩ : syracuseStep 3407369 = 2555527) B2555527
theorem B2271579 : Blo 2271435 2271579 := bstep (se 1 (by rfl) ⟨1703684, by rfl⟩ : syracuseStep 2271579 = 3407369) B3407369
theorem B11499893 : Blo 2271435 11499893 := bbase (se 5 (by rfl) ⟨539057, by rfl⟩ : syracuseStep 11499893 = 1078115) (by norm_num)
theorem B7666595 : Blo 2271435 7666595 := bstep (se 1 (by rfl) ⟨5749946, by rfl⟩ : syracuseStep 7666595 = 11499893) B11499893
theorem B5111063 : Blo 2271435 5111063 := bstep (se 1 (by rfl) ⟨3833297, by rfl⟩ : syracuseStep 5111063 = 7666595) B7666595
theorem B3407375 : Blo 2271435 3407375 := bstep (se 1 (by rfl) ⟨2555531, by rfl⟩ : syracuseStep 3407375 = 5111063) B5111063
theorem B2271583 : Blo 2271435 2271583 := bstep (se 1 (by rfl) ⟨1703687, by rfl⟩ : syracuseStep 2271583 = 3407375) B3407375
theorem B3407381 : Blo 2271435 3407381 := bbase (se 6 (by rfl) ⟨79860, by rfl⟩ : syracuseStep 3407381 = 159721) (by norm_num)
theorem B2271587 : Blo 2271435 2271587 := bstep (se 1 (by rfl) ⟨1703690, by rfl⟩ : syracuseStep 2271587 = 3407381) B3407381
theorem B3453877 : Blo 2271435 3453877 := bbase (se 5 (by rfl) ⟨161900, by rfl⟩ : syracuseStep 3453877 = 323801) (by norm_num)
theorem B4605169 : Blo 2271435 4605169 := bstep (se 2 (by rfl) ⟨1726938, by rfl⟩ : syracuseStep 4605169 = 3453877) B3453877
theorem B6140225 : Blo 2271435 6140225 := bstep (se 2 (by rfl) ⟨2302584, by rfl⟩ : syracuseStep 6140225 = 4605169) B4605169
theorem B16373933 : Blo 2271435 16373933 := bstep (se 3 (by rfl) ⟨3070112, by rfl⟩ : syracuseStep 16373933 = 6140225) B6140225
theorem B10915955 : Blo 2271435 10915955 := bstep (se 1 (by rfl) ⟨8186966, by rfl⟩ : syracuseStep 10915955 = 16373933) B16373933
theorem B7277303 : Blo 2271435 7277303 := bstep (se 1 (by rfl) ⟨5457977, by rfl⟩ : syracuseStep 7277303 = 10915955) B10915955
theorem B19406141 : Blo 2271435 19406141 := bstep (se 3 (by rfl) ⟨3638651, by rfl⟩ : syracuseStep 19406141 = 7277303) B7277303
theorem B12937427 : Blo 2271435 12937427 := bstep (se 1 (by rfl) ⟨9703070, by rfl⟩ : syracuseStep 12937427 = 19406141) B19406141
theorem B8624951 : Blo 2271435 8624951 := bstep (se 1 (by rfl) ⟨6468713, by rfl⟩ : syracuseStep 8624951 = 12937427) B12937427
theorem B5749967 : Blo 2271435 5749967 := bstep (se 1 (by rfl) ⟨4312475, by rfl⟩ : syracuseStep 5749967 = 8624951) B8624951
theorem B3833311 : Blo 2271435 3833311 := bstep (se 1 (by rfl) ⟨2874983, by rfl⟩ : syracuseStep 3833311 = 5749967) B5749967
theorem B5111081 : Blo 2271435 5111081 := bstep (se 2 (by rfl) ⟨1916655, by rfl⟩ : syracuseStep 5111081 = 3833311) B3833311
theorem B3407387 : Blo 2271435 3407387 := bstep (se 1 (by rfl) ⟨2555540, by rfl⟩ : syracuseStep 3407387 = 5111081) B5111081
theorem B2271591 : Blo 2271435 2271591 := bstep (se 1 (by rfl) ⟨1703693, by rfl⟩ : syracuseStep 2271591 = 3407387) B3407387
theorem B2555545 : Blo 2271435 2555545 := bbase (se 2 (by rfl) ⟨958329, by rfl⟩ : syracuseStep 2555545 = 1916659) (by norm_num)
theorem B3407393 : Blo 2271435 3407393 := bstep (se 2 (by rfl) ⟨1277772, by rfl⟩ : syracuseStep 3407393 = 2555545) B2555545
theorem B2271595 : Blo 2271435 2271595 := bstep (se 1 (by rfl) ⟨1703696, by rfl⟩ : syracuseStep 2271595 = 3407393) B3407393
theorem B8624981 : Blo 2271435 8624981 := bbase (se 9 (by rfl) ⟨25268, by rfl⟩ : syracuseStep 8624981 = 50537) (by norm_num)
theorem B5749987 : Blo 2271435 5749987 := bstep (se 1 (by rfl) ⟨4312490, by rfl⟩ : syracuseStep 5749987 = 8624981) B8624981
theorem B7666649 : Blo 2271435 7666649 := bstep (se 2 (by rfl) ⟨2874993, by rfl⟩ : syracuseStep 7666649 = 5749987) B5749987
theorem B5111099 : Blo 2271435 5111099 := bstep (se 1 (by rfl) ⟨3833324, by rfl⟩ : syracuseStep 5111099 = 7666649) B7666649
theorem B3407399 : Blo 2271435 3407399 := bstep (se 1 (by rfl) ⟨2555549, by rfl⟩ : syracuseStep 3407399 = 5111099) B5111099
theorem B2271599 : Blo 2271435 2271599 := bstep (se 1 (by rfl) ⟨1703699, by rfl⟩ : syracuseStep 2271599 = 3407399) B3407399
theorem B3407405 : Blo 2271435 3407405 := bbase (se 3 (by rfl) ⟨638888, by rfl⟩ : syracuseStep 3407405 = 1277777) (by norm_num)
theorem B2271603 : Blo 2271435 2271603 := bstep (se 1 (by rfl) ⟨1703702, by rfl⟩ : syracuseStep 2271603 = 3407405) B3407405
theorem B5111117 : Blo 2271435 5111117 := bbase (se 3 (by rfl) ⟨958334, by rfl⟩ : syracuseStep 5111117 = 1916669) (by norm_num)
theorem B3407411 : Blo 2271435 3407411 := bstep (se 1 (by rfl) ⟨2555558, by rfl⟩ : syracuseStep 3407411 = 5111117) B5111117
theorem B2271607 : Blo 2271435 2271607 := bstep (se 1 (by rfl) ⟨1703705, by rfl⟩ : syracuseStep 2271607 = 3407411) B3407411
theorem B2875009 : Blo 2271435 2875009 := bbase (se 2 (by rfl) ⟨1078128, by rfl⟩ : syracuseStep 2875009 = 2156257) (by norm_num)
theorem B3833345 : Blo 2271435 3833345 := bstep (se 2 (by rfl) ⟨1437504, by rfl⟩ : syracuseStep 3833345 = 2875009) B2875009
theorem B2555563 : Blo 2271435 2555563 := bstep (se 1 (by rfl) ⟨1916672, by rfl⟩ : syracuseStep 2555563 = 3833345) B3833345
theorem B3407417 : Blo 2271435 3407417 := bstep (se 2 (by rfl) ⟨1277781, by rfl⟩ : syracuseStep 3407417 = 2555563) B2555563
theorem B2271611 : Blo 2271435 2271611 := bstep (se 1 (by rfl) ⟨1703708, by rfl⟩ : syracuseStep 2271611 = 3407417) B3407417
theorem B2425793 : Blo 2271435 2425793 := bbase (se 2 (by rfl) ⟨909672, by rfl⟩ : syracuseStep 2425793 = 1819345) (by norm_num)
theorem B25875125 : Blo 2271435 25875125 := bstep (se 5 (by rfl) ⟨1212896, by rfl⟩ : syracuseStep 25875125 = 2425793) B2425793
theorem B17250083 : Blo 2271435 17250083 := bstep (se 1 (by rfl) ⟨12937562, by rfl⟩ : syracuseStep 17250083 = 25875125) B25875125
theorem B11500055 : Blo 2271435 11500055 := bstep (se 1 (by rfl) ⟨8625041, by rfl⟩ : syracuseStep 11500055 = 17250083) B17250083
theorem B7666703 : Blo 2271435 7666703 := bstep (se 1 (by rfl) ⟨5750027, by rfl⟩ : syracuseStep 7666703 = 11500055) B11500055
theorem B5111135 : Blo 2271435 5111135 := bstep (se 1 (by rfl) ⟨3833351, by rfl⟩ : syracuseStep 5111135 = 7666703) B7666703
theorem B3407423 : Blo 2271435 3407423 := bstep (se 1 (by rfl) ⟨2555567, by rfl⟩ : syracuseStep 3407423 = 5111135) B5111135
theorem B2271615 : Blo 2271435 2271615 := bstep (se 1 (by rfl) ⟨1703711, by rfl⟩ : syracuseStep 2271615 = 3407423) B3407423
theorem B3407429 : Blo 2271435 3407429 := bbase (se 4 (by rfl) ⟨319446, by rfl⟩ : syracuseStep 3407429 = 638893) (by norm_num)
theorem B2271619 : Blo 2271435 2271619 := bstep (se 1 (by rfl) ⟨1703714, by rfl⟩ : syracuseStep 2271619 = 3407429) B3407429
theorem B3833365 : Blo 2271435 3833365 := bbase (se 6 (by rfl) ⟨89844, by rfl⟩ : syracuseStep 3833365 = 179689) (by norm_num)
theorem B5111153 : Blo 2271435 5111153 := bstep (se 2 (by rfl) ⟨1916682, by rfl⟩ : syracuseStep 5111153 = 3833365) B3833365
theorem B3407435 : Blo 2271435 3407435 := bstep (se 1 (by rfl) ⟨2555576, by rfl⟩ : syracuseStep 3407435 = 5111153) B5111153
theorem B2271623 : Blo 2271435 2271623 := bstep (se 1 (by rfl) ⟨1703717, by rfl⟩ : syracuseStep 2271623 = 3407435) B3407435
theorem B2555581 : Blo 2271435 2555581 := bbase (se 3 (by rfl) ⟨479171, by rfl⟩ : syracuseStep 2555581 = 958343) (by norm_num)
theorem B3407441 : Blo 2271435 3407441 := bstep (se 2 (by rfl) ⟨1277790, by rfl⟩ : syracuseStep 3407441 = 2555581) B2555581
theorem B2271627 : Blo 2271435 2271627 := bstep (se 1 (by rfl) ⟨1703720, by rfl⟩ : syracuseStep 2271627 = 3407441) B3407441
theorem B7666757 : Blo 2271435 7666757 := bbase (se 4 (by rfl) ⟨718758, by rfl⟩ : syracuseStep 7666757 = 1437517) (by norm_num)
theorem B5111171 : Blo 2271435 5111171 := bstep (se 1 (by rfl) ⟨3833378, by rfl⟩ : syracuseStep 5111171 = 7666757) B7666757
theorem B3407447 : Blo 2271435 3407447 := bstep (se 1 (by rfl) ⟨2555585, by rfl⟩ : syracuseStep 3407447 = 5111171) B5111171
theorem B2271631 : Blo 2271435 2271631 := bstep (se 1 (by rfl) ⟨1703723, by rfl⟩ : syracuseStep 2271631 = 3407447) B3407447
theorem B3407453 : Blo 2271435 3407453 := bbase (se 3 (by rfl) ⟨638897, by rfl⟩ : syracuseStep 3407453 = 1277795) (by norm_num)
theorem B2271635 : Blo 2271435 2271635 := bstep (se 1 (by rfl) ⟨1703726, by rfl⟩ : syracuseStep 2271635 = 3407453) B3407453
theorem B5111189 : Blo 2271435 5111189 := bbase (se 6 (by rfl) ⟨119793, by rfl⟩ : syracuseStep 5111189 = 239587) (by norm_num)
theorem B3407459 : Blo 2271435 3407459 := bstep (se 1 (by rfl) ⟨2555594, by rfl⟩ : syracuseStep 3407459 = 5111189) B5111189
theorem B2271639 : Blo 2271435 2271639 := bstep (se 1 (by rfl) ⟨1703729, by rfl⟩ : syracuseStep 2271639 = 3407459) B3407459
theorem B3885701 : Blo 2271435 3885701 := bbase (se 4 (by rfl) ⟨364284, by rfl⟩ : syracuseStep 3885701 = 728569) (by norm_num)
theorem B41447477 : Blo 2271435 41447477 := bstep (se 5 (by rfl) ⟨1942850, by rfl⟩ : syracuseStep 41447477 = 3885701) B3885701
theorem B27631651 : Blo 2271435 27631651 := bstep (se 1 (by rfl) ⟨20723738, by rfl⟩ : syracuseStep 27631651 = 41447477) B41447477
theorem B36842201 : Blo 2271435 36842201 := bstep (se 2 (by rfl) ⟨13815825, by rfl⟩ : syracuseStep 36842201 = 27631651) B27631651
theorem B24561467 : Blo 2271435 24561467 := bstep (se 1 (by rfl) ⟨18421100, by rfl⟩ : syracuseStep 24561467 = 36842201) B36842201
theorem B16374311 : Blo 2271435 16374311 := bstep (se 1 (by rfl) ⟨12280733, by rfl⟩ : syracuseStep 16374311 = 24561467) B24561467
theorem B10916207 : Blo 2271435 10916207 := bstep (se 1 (by rfl) ⟨8187155, by rfl⟩ : syracuseStep 10916207 = 16374311) B16374311
theorem B7277471 : Blo 2271435 7277471 := bstep (se 1 (by rfl) ⟨5458103, by rfl⟩ : syracuseStep 7277471 = 10916207) B10916207
theorem B4851647 : Blo 2271435 4851647 := bstep (se 1 (by rfl) ⟨3638735, by rfl⟩ : syracuseStep 4851647 = 7277471) B7277471
theorem B3234431 : Blo 2271435 3234431 := bstep (se 1 (by rfl) ⟨2425823, by rfl⟩ : syracuseStep 3234431 = 4851647) B4851647
theorem B8625149 : Blo 2271435 8625149 := bstep (se 3 (by rfl) ⟨1617215, by rfl⟩ : syracuseStep 8625149 = 3234431) B3234431
theorem B5750099 : Blo 2271435 5750099 := bstep (se 1 (by rfl) ⟨4312574, by rfl⟩ : syracuseStep 5750099 = 8625149) B8625149
theorem B3833399 : Blo 2271435 3833399 := bstep (se 1 (by rfl) ⟨2875049, by rfl⟩ : syracuseStep 3833399 = 5750099) B5750099
theorem B2555599 : Blo 2271435 2555599 := bstep (se 1 (by rfl) ⟨1916699, by rfl⟩ : syracuseStep 2555599 = 3833399) B3833399
theorem B3407465 : Blo 2271435 3407465 := bstep (se 2 (by rfl) ⟨1277799, by rfl⟩ : syracuseStep 3407465 = 2555599) B2555599
theorem B2271643 : Blo 2271435 2271643 := bstep (se 1 (by rfl) ⟨1703732, by rfl⟩ : syracuseStep 2271643 = 3407465) B3407465
theorem B3638741 : Blo 2271435 3638741 := bbase (se 7 (by rfl) ⟨42641, by rfl⟩ : syracuseStep 3638741 = 85283) (by norm_num)
theorem B9703309 : Blo 2271435 9703309 := bstep (se 3 (by rfl) ⟨1819370, by rfl⟩ : syracuseStep 9703309 = 3638741) B3638741
theorem B12937745 : Blo 2271435 12937745 := bstep (se 2 (by rfl) ⟨4851654, by rfl⟩ : syracuseStep 12937745 = 9703309) B9703309
theorem B8625163 : Blo 2271435 8625163 := bstep (se 1 (by rfl) ⟨6468872, by rfl⟩ : syracuseStep 8625163 = 12937745) B12937745
theorem B11500217 : Blo 2271435 11500217 := bstep (se 2 (by rfl) ⟨4312581, by rfl⟩ : syracuseStep 11500217 = 8625163) B8625163
theorem B7666811 : Blo 2271435 7666811 := bstep (se 1 (by rfl) ⟨5750108, by rfl⟩ : syracuseStep 7666811 = 11500217) B11500217
theorem B5111207 : Blo 2271435 5111207 := bstep (se 1 (by rfl) ⟨3833405, by rfl⟩ : syracuseStep 5111207 = 7666811) B7666811
theorem B3407471 : Blo 2271435 3407471 := bstep (se 1 (by rfl) ⟨2555603, by rfl⟩ : syracuseStep 3407471 = 5111207) B5111207
theorem B2271647 : Blo 2271435 2271647 := bstep (se 1 (by rfl) ⟨1703735, by rfl⟩ : syracuseStep 2271647 = 3407471) B3407471
theorem B3407477 : Blo 2271435 3407477 := bbase (se 5 (by rfl) ⟨159725, by rfl⟩ : syracuseStep 3407477 = 319451) (by norm_num)
theorem B2271651 : Blo 2271435 2271651 := bstep (se 1 (by rfl) ⟨1703738, by rfl⟩ : syracuseStep 2271651 = 3407477) B3407477
theorem B4312597 : Blo 2271435 4312597 := bbase (se 6 (by rfl) ⟨101076, by rfl⟩ : syracuseStep 4312597 = 202153) (by norm_num)
theorem B5750129 : Blo 2271435 5750129 := bstep (se 2 (by rfl) ⟨2156298, by rfl⟩ : syracuseStep 5750129 = 4312597) B4312597
theorem B3833419 : Blo 2271435 3833419 := bstep (se 1 (by rfl) ⟨2875064, by rfl⟩ : syracuseStep 3833419 = 5750129) B5750129
theorem B5111225 : Blo 2271435 5111225 := bstep (se 2 (by rfl) ⟨1916709, by rfl⟩ : syracuseStep 5111225 = 3833419) B3833419
theorem B3407483 : Blo 2271435 3407483 := bstep (se 1 (by rfl) ⟨2555612, by rfl⟩ : syracuseStep 3407483 = 5111225) B5111225
theorem B2271655 : Blo 2271435 2271655 := bstep (se 1 (by rfl) ⟨1703741, by rfl⟩ : syracuseStep 2271655 = 3407483) B3407483
theorem B2555617 : Blo 2271435 2555617 := bbase (se 2 (by rfl) ⟨958356, by rfl⟩ : syracuseStep 2555617 = 1916713) (by norm_num)
theorem B3407489 : Blo 2271435 3407489 := bstep (se 2 (by rfl) ⟨1277808, by rfl⟩ : syracuseStep 3407489 = 2555617) B2555617
theorem B2271659 : Blo 2271435 2271659 := bstep (se 1 (by rfl) ⟨1703744, by rfl⟩ : syracuseStep 2271659 = 3407489) B3407489
theorem B5750149 : Blo 2271435 5750149 := bbase (se 4 (by rfl) ⟨539076, by rfl⟩ : syracuseStep 5750149 = 1078153) (by norm_num)
theorem B7666865 : Blo 2271435 7666865 := bstep (se 2 (by rfl) ⟨2875074, by rfl⟩ : syracuseStep 7666865 = 5750149) B5750149
theorem B5111243 : Blo 2271435 5111243 := bstep (se 1 (by rfl) ⟨3833432, by rfl⟩ : syracuseStep 5111243 = 7666865) B7666865
theorem B3407495 : Blo 2271435 3407495 := bstep (se 1 (by rfl) ⟨2555621, by rfl⟩ : syracuseStep 3407495 = 5111243) B5111243
theorem B2271663 : Blo 2271435 2271663 := bstep (se 1 (by rfl) ⟨1703747, by rfl⟩ : syracuseStep 2271663 = 3407495) B3407495
theorem B3407501 : Blo 2271435 3407501 := bbase (se 3 (by rfl) ⟨638906, by rfl⟩ : syracuseStep 3407501 = 1277813) (by norm_num)
theorem B2271667 : Blo 2271435 2271667 := bstep (se 1 (by rfl) ⟨1703750, by rfl⟩ : syracuseStep 2271667 = 3407501) B3407501
theorem B5111261 : Blo 2271435 5111261 := bbase (se 3 (by rfl) ⟨958361, by rfl⟩ : syracuseStep 5111261 = 1916723) (by norm_num)
theorem B3407507 : Blo 2271435 3407507 := bstep (se 1 (by rfl) ⟨2555630, by rfl⟩ : syracuseStep 3407507 = 5111261) B5111261
theorem B2271671 : Blo 2271435 2271671 := bstep (se 1 (by rfl) ⟨1703753, by rfl⟩ : syracuseStep 2271671 = 3407507) B3407507
theorem B3833453 : Blo 2271435 3833453 := bbase (se 3 (by rfl) ⟨718772, by rfl⟩ : syracuseStep 3833453 = 1437545) (by norm_num)
theorem B2555635 : Blo 2271435 2555635 := bstep (se 1 (by rfl) ⟨1916726, by rfl⟩ : syracuseStep 2555635 = 3833453) B3833453
theorem B3407513 : Blo 2271435 3407513 := bstep (se 2 (by rfl) ⟨1277817, by rfl⟩ : syracuseStep 3407513 = 2555635) B2555635
theorem B2271675 : Blo 2271435 2271675 := bstep (se 1 (by rfl) ⟨1703756, by rfl⟩ : syracuseStep 2271675 = 3407513) B3407513
theorem B6908021 : Blo 2271435 6908021 := bbase (se 5 (by rfl) ⟨323813, by rfl⟩ : syracuseStep 6908021 = 647627) (by norm_num)
theorem B4605347 : Blo 2271435 4605347 := bstep (se 1 (by rfl) ⟨3454010, by rfl⟩ : syracuseStep 4605347 = 6908021) B6908021
theorem B3070231 : Blo 2271435 3070231 := bstep (se 1 (by rfl) ⟨2302673, by rfl⟩ : syracuseStep 3070231 = 4605347) B4605347
theorem B16374565 : Blo 2271435 16374565 := bstep (se 4 (by rfl) ⟨1535115, by rfl⟩ : syracuseStep 16374565 = 3070231) B3070231
theorem B21832753 : Blo 2271435 21832753 := bstep (se 2 (by rfl) ⟨8187282, by rfl⟩ : syracuseStep 21832753 = 16374565) B16374565
theorem B29110337 : Blo 2271435 29110337 := bstep (se 2 (by rfl) ⟨10916376, by rfl⟩ : syracuseStep 29110337 = 21832753) B21832753
theorem B19406891 : Blo 2271435 19406891 := bstep (se 1 (by rfl) ⟨14555168, by rfl⟩ : syracuseStep 19406891 = 29110337) B29110337
theorem B12937927 : Blo 2271435 12937927 := bstep (se 1 (by rfl) ⟨9703445, by rfl⟩ : syracuseStep 12937927 = 19406891) B19406891
theorem B17250569 : Blo 2271435 17250569 := bstep (se 2 (by rfl) ⟨6468963, by rfl⟩ : syracuseStep 17250569 = 12937927) B12937927
theorem B11500379 : Blo 2271435 11500379 := bstep (se 1 (by rfl) ⟨8625284, by rfl⟩ : syracuseStep 11500379 = 17250569) B17250569
theorem B7666919 : Blo 2271435 7666919 := bstep (se 1 (by rfl) ⟨5750189, by rfl⟩ : syracuseStep 7666919 = 11500379) B11500379
theorem B5111279 : Blo 2271435 5111279 := bstep (se 1 (by rfl) ⟨3833459, by rfl⟩ : syracuseStep 5111279 = 7666919) B7666919
theorem B3407519 : Blo 2271435 3407519 := bstep (se 1 (by rfl) ⟨2555639, by rfl⟩ : syracuseStep 3407519 = 5111279) B5111279
theorem B2271679 : Blo 2271435 2271679 := bstep (se 1 (by rfl) ⟨1703759, by rfl⟩ : syracuseStep 2271679 = 3407519) B3407519
theorem B3407525 : Blo 2271435 3407525 := bbase (se 4 (by rfl) ⟨319455, by rfl⟩ : syracuseStep 3407525 = 638911) (by norm_num)
theorem B2271683 : Blo 2271435 2271683 := bstep (se 1 (by rfl) ⟨1703762, by rfl⟩ : syracuseStep 2271683 = 3407525) B3407525
theorem B2875105 : Blo 2271435 2875105 := bbase (se 2 (by rfl) ⟨1078164, by rfl⟩ : syracuseStep 2875105 = 2156329) (by norm_num)
theorem B3833473 : Blo 2271435 3833473 := bstep (se 2 (by rfl) ⟨1437552, by rfl⟩ : syracuseStep 3833473 = 2875105) B2875105
theorem B5111297 : Blo 2271435 5111297 := bstep (se 2 (by rfl) ⟨1916736, by rfl⟩ : syracuseStep 5111297 = 3833473) B3833473
theorem B3407531 : Blo 2271435 3407531 := bstep (se 1 (by rfl) ⟨2555648, by rfl⟩ : syracuseStep 3407531 = 5111297) B5111297
theorem B2271687 : Blo 2271435 2271687 := bstep (se 1 (by rfl) ⟨1703765, by rfl⟩ : syracuseStep 2271687 = 3407531) B3407531
theorem B2555653 : Blo 2271435 2555653 := bbase (se 4 (by rfl) ⟨239592, by rfl⟩ : syracuseStep 2555653 = 479185) (by norm_num)
theorem B3407537 : Blo 2271435 3407537 := bstep (se 2 (by rfl) ⟨1277826, by rfl⟩ : syracuseStep 3407537 = 2555653) B2555653
theorem B2271691 : Blo 2271435 2271691 := bstep (se 1 (by rfl) ⟨1703768, by rfl⟩ : syracuseStep 2271691 = 3407537) B3407537
theorem B5458229 : Blo 2271435 5458229 := bbase (se 5 (by rfl) ⟨255854, by rfl⟩ : syracuseStep 5458229 = 511709) (by norm_num)
theorem B3638819 : Blo 2271435 3638819 := bstep (se 1 (by rfl) ⟨2729114, by rfl⟩ : syracuseStep 3638819 = 5458229) B5458229
theorem B2425879 : Blo 2271435 2425879 := bstep (se 1 (by rfl) ⟨1819409, by rfl⟩ : syracuseStep 2425879 = 3638819) B3638819
theorem B3234505 : Blo 2271435 3234505 := bstep (se 2 (by rfl) ⟨1212939, by rfl⟩ : syracuseStep 3234505 = 2425879) B2425879
theorem B4312673 : Blo 2271435 4312673 := bstep (se 2 (by rfl) ⟨1617252, by rfl⟩ : syracuseStep 4312673 = 3234505) B3234505
theorem B2875115 : Blo 2271435 2875115 := bstep (se 1 (by rfl) ⟨2156336, by rfl⟩ : syracuseStep 2875115 = 4312673) B4312673
theorem B7666973 : Blo 2271435 7666973 := bstep (se 3 (by rfl) ⟨1437557, by rfl⟩ : syracuseStep 7666973 = 2875115) B2875115
theorem B5111315 : Blo 2271435 5111315 := bstep (se 1 (by rfl) ⟨3833486, by rfl⟩ : syracuseStep 5111315 = 7666973) B7666973
theorem B3407543 : Blo 2271435 3407543 := bstep (se 1 (by rfl) ⟨2555657, by rfl⟩ : syracuseStep 3407543 = 5111315) B5111315
theorem B2271695 : Blo 2271435 2271695 := bstep (se 1 (by rfl) ⟨1703771, by rfl⟩ : syracuseStep 2271695 = 3407543) B3407543
theorem B3407549 : Blo 2271435 3407549 := bbase (se 3 (by rfl) ⟨638915, by rfl⟩ : syracuseStep 3407549 = 1277831) (by norm_num)
theorem B2271699 : Blo 2271435 2271699 := bstep (se 1 (by rfl) ⟨1703774, by rfl⟩ : syracuseStep 2271699 = 3407549) B3407549
theorem B5111333 : Blo 2271435 5111333 := bbase (se 4 (by rfl) ⟨479187, by rfl⟩ : syracuseStep 5111333 = 958375) (by norm_num)
theorem B3407555 : Blo 2271435 3407555 := bstep (se 1 (by rfl) ⟨2555666, by rfl⟩ : syracuseStep 3407555 = 5111333) B5111333
theorem B2271703 : Blo 2271435 2271703 := bstep (se 1 (by rfl) ⟨1703777, by rfl⟩ : syracuseStep 2271703 = 3407555) B3407555
theorem B5750261 : Blo 2271435 5750261 := bbase (se 5 (by rfl) ⟨269543, by rfl⟩ : syracuseStep 5750261 = 539087) (by norm_num)
theorem B3833507 : Blo 2271435 3833507 := bstep (se 1 (by rfl) ⟨2875130, by rfl⟩ : syracuseStep 3833507 = 5750261) B5750261
theorem B2555671 : Blo 2271435 2555671 := bstep (se 1 (by rfl) ⟨1916753, by rfl⟩ : syracuseStep 2555671 = 3833507) B3833507
theorem B3407561 : Blo 2271435 3407561 := bstep (se 2 (by rfl) ⟨1277835, by rfl⟩ : syracuseStep 3407561 = 2555671) B2555671
theorem B2271707 : Blo 2271435 2271707 := bstep (se 1 (by rfl) ⟨1703780, by rfl⟩ : syracuseStep 2271707 = 3407561) B3407561
theorem B3646453 : Blo 2271435 3646453 := bbase (se 5 (by rfl) ⟨170927, by rfl⟩ : syracuseStep 3646453 = 341855) (by norm_num)
theorem B4861937 : Blo 2271435 4861937 := bstep (se 2 (by rfl) ⟨1823226, by rfl⟩ : syracuseStep 4861937 = 3646453) B3646453
theorem B3241291 : Blo 2271435 3241291 := bstep (se 1 (by rfl) ⟨2430968, by rfl⟩ : syracuseStep 3241291 = 4861937) B4861937
theorem B4321721 : Blo 2271435 4321721 := bstep (se 2 (by rfl) ⟨1620645, by rfl⟩ : syracuseStep 4321721 = 3241291) B3241291
theorem B11524589 : Blo 2271435 11524589 := bstep (se 3 (by rfl) ⟨2160860, by rfl⟩ : syracuseStep 11524589 = 4321721) B4321721
theorem B7683059 : Blo 2271435 7683059 := bstep (se 1 (by rfl) ⟨5762294, by rfl⟩ : syracuseStep 7683059 = 11524589) B11524589
theorem B20488157 : Blo 2271435 20488157 := bstep (se 3 (by rfl) ⟨3841529, by rfl⟩ : syracuseStep 20488157 = 7683059) B7683059
theorem B13658771 : Blo 2271435 13658771 := bstep (se 1 (by rfl) ⟨10244078, by rfl⟩ : syracuseStep 13658771 = 20488157) B20488157
theorem B9105847 : Blo 2271435 9105847 := bstep (se 1 (by rfl) ⟨6829385, by rfl⟩ : syracuseStep 9105847 = 13658771) B13658771
theorem B48564517 : Blo 2271435 48564517 := bstep (se 4 (by rfl) ⟨4552923, by rfl⟩ : syracuseStep 48564517 = 9105847) B9105847
theorem B64752689 : Blo 2271435 64752689 := bstep (se 2 (by rfl) ⟨24282258, by rfl⟩ : syracuseStep 64752689 = 48564517) B48564517
theorem B43168459 : Blo 2271435 43168459 := bstep (se 1 (by rfl) ⟨32376344, by rfl⟩ : syracuseStep 43168459 = 64752689) B64752689
theorem B57557945 : Blo 2271435 57557945 := bstep (se 2 (by rfl) ⟨21584229, by rfl⟩ : syracuseStep 57557945 = 43168459) B43168459
theorem B38371963 : Blo 2271435 38371963 := bstep (se 1 (by rfl) ⟨28778972, by rfl⟩ : syracuseStep 38371963 = 57557945) B57557945
theorem B51162617 : Blo 2271435 51162617 := bstep (se 2 (by rfl) ⟨19185981, by rfl⟩ : syracuseStep 51162617 = 38371963) B38371963
theorem B34108411 : Blo 2271435 34108411 := bstep (se 1 (by rfl) ⟨25581308, by rfl⟩ : syracuseStep 34108411 = 51162617) B51162617
theorem B45477881 : Blo 2271435 45477881 := bstep (se 2 (by rfl) ⟨17054205, by rfl⟩ : syracuseStep 45477881 = 34108411) B34108411
theorem B30318587 : Blo 2271435 30318587 := bstep (se 1 (by rfl) ⟨22738940, by rfl⟩ : syracuseStep 30318587 = 45477881) B45477881
theorem B20212391 : Blo 2271435 20212391 := bstep (se 1 (by rfl) ⟨15159293, by rfl⟩ : syracuseStep 20212391 = 30318587) B30318587
theorem B13474927 : Blo 2271435 13474927 := bstep (se 1 (by rfl) ⟨10106195, by rfl⟩ : syracuseStep 13474927 = 20212391) B20212391
theorem B71866277 : Blo 2271435 71866277 := bstep (se 4 (by rfl) ⟨6737463, by rfl⟩ : syracuseStep 71866277 = 13474927) B13474927
theorem B47910851 : Blo 2271435 47910851 := bstep (se 1 (by rfl) ⟨35933138, by rfl⟩ : syracuseStep 47910851 = 71866277) B71866277
theorem B31940567 : Blo 2271435 31940567 := bstep (se 1 (by rfl) ⟨23955425, by rfl⟩ : syracuseStep 31940567 = 47910851) B47910851
theorem B21293711 : Blo 2271435 21293711 := bstep (se 1 (by rfl) ⟨15970283, by rfl⟩ : syracuseStep 21293711 = 31940567) B31940567
theorem B14195807 : Blo 2271435 14195807 := bstep (se 1 (by rfl) ⟨10646855, by rfl⟩ : syracuseStep 14195807 = 21293711) B21293711
theorem B9463871 : Blo 2271435 9463871 := bstep (se 1 (by rfl) ⟨7097903, by rfl⟩ : syracuseStep 9463871 = 14195807) B14195807
theorem B25236989 : Blo 2271435 25236989 := bstep (se 3 (by rfl) ⟨4731935, by rfl⟩ : syracuseStep 25236989 = 9463871) B9463871
theorem B1076778197 : Blo 2271435 1076778197 := bstep (se 7 (by rfl) ⟨12618494, by rfl⟩ : syracuseStep 1076778197 = 25236989) B25236989
theorem B717852131 : Blo 2271435 717852131 := bstep (se 1 (by rfl) ⟨538389098, by rfl⟩ : syracuseStep 717852131 = 1076778197) B1076778197
theorem B478568087 : Blo 2271435 478568087 := bstep (se 1 (by rfl) ⟨358926065, by rfl⟩ : syracuseStep 478568087 = 717852131) B717852131
theorem B319045391 : Blo 2271435 319045391 := bstep (se 1 (by rfl) ⟨239284043, by rfl⟩ : syracuseStep 319045391 = 478568087) B478568087
theorem B212696927 : Blo 2271435 212696927 := bstep (se 1 (by rfl) ⟨159522695, by rfl⟩ : syracuseStep 212696927 = 319045391) B319045391
theorem B141797951 : Blo 2271435 141797951 := bstep (se 1 (by rfl) ⟨106348463, by rfl⟩ : syracuseStep 141797951 = 212696927) B212696927
theorem B94531967 : Blo 2271435 94531967 := bstep (se 1 (by rfl) ⟨70898975, by rfl⟩ : syracuseStep 94531967 = 141797951) B141797951
theorem B63021311 : Blo 2271435 63021311 := bstep (se 1 (by rfl) ⟨47265983, by rfl⟩ : syracuseStep 63021311 = 94531967) B94531967
theorem B42014207 : Blo 2271435 42014207 := bstep (se 1 (by rfl) ⟨31510655, by rfl⟩ : syracuseStep 42014207 = 63021311) B63021311
theorem B28009471 : Blo 2271435 28009471 := bstep (se 1 (by rfl) ⟨21007103, by rfl⟩ : syracuseStep 28009471 = 42014207) B42014207
theorem B37345961 : Blo 2271435 37345961 := bstep (se 2 (by rfl) ⟨14004735, by rfl⟩ : syracuseStep 37345961 = 28009471) B28009471
theorem B24897307 : Blo 2271435 24897307 := bstep (se 1 (by rfl) ⟨18672980, by rfl⟩ : syracuseStep 24897307 = 37345961) B37345961
theorem B33196409 : Blo 2271435 33196409 := bstep (se 2 (by rfl) ⟨12448653, by rfl⟩ : syracuseStep 33196409 = 24897307) B24897307
theorem B22130939 : Blo 2271435 22130939 := bstep (se 1 (by rfl) ⟨16598204, by rfl⟩ : syracuseStep 22130939 = 33196409) B33196409
theorem B59015837 : Blo 2271435 59015837 := bstep (se 3 (by rfl) ⟨11065469, by rfl⟩ : syracuseStep 59015837 = 22130939) B22130939
theorem B39343891 : Blo 2271435 39343891 := bstep (se 1 (by rfl) ⟨29507918, by rfl⟩ : syracuseStep 39343891 = 59015837) B59015837
theorem B52458521 : Blo 2271435 52458521 := bstep (se 2 (by rfl) ⟨19671945, by rfl⟩ : syracuseStep 52458521 = 39343891) B39343891
theorem B139889389 : Blo 2271435 139889389 := bstep (se 3 (by rfl) ⟨26229260, by rfl⟩ : syracuseStep 139889389 = 52458521) B52458521
theorem B186519185 : Blo 2271435 186519185 := bstep (se 2 (by rfl) ⟨69944694, by rfl⟩ : syracuseStep 186519185 = 139889389) B139889389
theorem B124346123 : Blo 2271435 124346123 := bstep (se 1 (by rfl) ⟨93259592, by rfl⟩ : syracuseStep 124346123 = 186519185) B186519185
theorem B82897415 : Blo 2271435 82897415 := bstep (se 1 (by rfl) ⟨62173061, by rfl⟩ : syracuseStep 82897415 = 124346123) B124346123
theorem B55264943 : Blo 2271435 55264943 := bstep (se 1 (by rfl) ⟨41448707, by rfl⟩ : syracuseStep 55264943 = 82897415) B82897415
theorem B36843295 : Blo 2271435 36843295 := bstep (se 1 (by rfl) ⟨27632471, by rfl⟩ : syracuseStep 36843295 = 55264943) B55264943
theorem B49124393 : Blo 2271435 49124393 := bstep (se 2 (by rfl) ⟨18421647, by rfl⟩ : syracuseStep 49124393 = 36843295) B36843295
theorem B32749595 : Blo 2271435 32749595 := bstep (se 1 (by rfl) ⟨24562196, by rfl⟩ : syracuseStep 32749595 = 49124393) B49124393
theorem B21833063 : Blo 2271435 21833063 := bstep (se 1 (by rfl) ⟨16374797, by rfl⟩ : syracuseStep 21833063 = 32749595) B32749595
theorem B14555375 : Blo 2271435 14555375 := bstep (se 1 (by rfl) ⟨10916531, by rfl⟩ : syracuseStep 14555375 = 21833063) B21833063
theorem B9703583 : Blo 2271435 9703583 := bstep (se 1 (by rfl) ⟨7277687, by rfl⟩ : syracuseStep 9703583 = 14555375) B14555375
theorem B6469055 : Blo 2271435 6469055 := bstep (se 1 (by rfl) ⟨4851791, by rfl⟩ : syracuseStep 6469055 = 9703583) B9703583
theorem B4312703 : Blo 2271435 4312703 := bstep (se 1 (by rfl) ⟨3234527, by rfl⟩ : syracuseStep 4312703 = 6469055) B6469055
theorem B11500541 : Blo 2271435 11500541 := bstep (se 3 (by rfl) ⟨2156351, by rfl⟩ : syracuseStep 11500541 = 4312703) B4312703
theorem B7667027 : Blo 2271435 7667027 := bstep (se 1 (by rfl) ⟨5750270, by rfl⟩ : syracuseStep 7667027 = 11500541) B11500541
theorem B5111351 : Blo 2271435 5111351 := bstep (se 1 (by rfl) ⟨3833513, by rfl⟩ : syracuseStep 5111351 = 7667027) B7667027
theorem B3407567 : Blo 2271435 3407567 := bstep (se 1 (by rfl) ⟨2555675, by rfl⟩ : syracuseStep 3407567 = 5111351) B5111351
theorem B2271711 : Blo 2271435 2271711 := bstep (se 1 (by rfl) ⟨1703783, by rfl⟩ : syracuseStep 2271711 = 3407567) B3407567
theorem B3407573 : Blo 2271435 3407573 := bbase (se 7 (by rfl) ⟨39932, by rfl⟩ : syracuseStep 3407573 = 79865) (by norm_num)
theorem B2271715 : Blo 2271435 2271715 := bstep (se 1 (by rfl) ⟨1703786, by rfl⟩ : syracuseStep 2271715 = 3407573) B3407573
theorem B6224357 : Blo 2271435 6224357 := bbase (se 4 (by rfl) ⟨583533, by rfl⟩ : syracuseStep 6224357 = 1167067) (by norm_num)
theorem B4149571 : Blo 2271435 4149571 := bstep (se 1 (by rfl) ⟨3112178, by rfl⟩ : syracuseStep 4149571 = 6224357) B6224357
theorem B5532761 : Blo 2271435 5532761 := bstep (se 2 (by rfl) ⟨2074785, by rfl⟩ : syracuseStep 5532761 = 4149571) B4149571
theorem B3688507 : Blo 2271435 3688507 := bstep (se 1 (by rfl) ⟨2766380, by rfl⟩ : syracuseStep 3688507 = 5532761) B5532761
theorem B4918009 : Blo 2271435 4918009 := bstep (se 2 (by rfl) ⟨1844253, by rfl⟩ : syracuseStep 4918009 = 3688507) B3688507
theorem B6557345 : Blo 2271435 6557345 := bstep (se 2 (by rfl) ⟨2459004, by rfl⟩ : syracuseStep 6557345 = 4918009) B4918009
theorem B4371563 : Blo 2271435 4371563 := bstep (se 1 (by rfl) ⟨3278672, by rfl⟩ : syracuseStep 4371563 = 6557345) B6557345
theorem B2914375 : Blo 2271435 2914375 := bstep (se 1 (by rfl) ⟨2185781, by rfl⟩ : syracuseStep 2914375 = 4371563) B4371563
theorem B3885833 : Blo 2271435 3885833 := bstep (se 2 (by rfl) ⟨1457187, by rfl⟩ : syracuseStep 3885833 = 2914375) B2914375
theorem B2590555 : Blo 2271435 2590555 := bstep (se 1 (by rfl) ⟨1942916, by rfl⟩ : syracuseStep 2590555 = 3885833) B3885833
theorem B3454073 : Blo 2271435 3454073 := bstep (se 2 (by rfl) ⟨1295277, by rfl⟩ : syracuseStep 3454073 = 2590555) B2590555
theorem B2302715 : Blo 2271435 2302715 := bstep (se 1 (by rfl) ⟨1727036, by rfl⟩ : syracuseStep 2302715 = 3454073) B3454073
theorem B6140573 : Blo 2271435 6140573 := bstep (se 3 (by rfl) ⟨1151357, by rfl⟩ : syracuseStep 6140573 = 2302715) B2302715
theorem B4093715 : Blo 2271435 4093715 := bstep (se 1 (by rfl) ⟨3070286, by rfl⟩ : syracuseStep 4093715 = 6140573) B6140573
theorem B2729143 : Blo 2271435 2729143 := bstep (se 1 (by rfl) ⟨2046857, by rfl⟩ : syracuseStep 2729143 = 4093715) B4093715
theorem B3638857 : Blo 2271435 3638857 := bstep (se 2 (by rfl) ⟨1364571, by rfl⟩ : syracuseStep 3638857 = 2729143) B2729143
theorem B4851809 : Blo 2271435 4851809 := bstep (se 2 (by rfl) ⟨1819428, by rfl⟩ : syracuseStep 4851809 = 3638857) B3638857
theorem B3234539 : Blo 2271435 3234539 := bstep (se 1 (by rfl) ⟨2425904, by rfl⟩ : syracuseStep 3234539 = 4851809) B4851809
theorem B8625437 : Blo 2271435 8625437 := bstep (se 3 (by rfl) ⟨1617269, by rfl⟩ : syracuseStep 8625437 = 3234539) B3234539
theorem B5750291 : Blo 2271435 5750291 := bstep (se 1 (by rfl) ⟨4312718, by rfl⟩ : syracuseStep 5750291 = 8625437) B8625437
theorem B3833527 : Blo 2271435 3833527 := bstep (se 1 (by rfl) ⟨2875145, by rfl⟩ : syracuseStep 3833527 = 5750291) B5750291
theorem B5111369 : Blo 2271435 5111369 := bstep (se 2 (by rfl) ⟨1916763, by rfl⟩ : syracuseStep 5111369 = 3833527) B3833527
theorem B3407579 : Blo 2271435 3407579 := bstep (se 1 (by rfl) ⟨2555684, by rfl⟩ : syracuseStep 3407579 = 5111369) B5111369
theorem B2271719 : Blo 2271435 2271719 := bstep (se 1 (by rfl) ⟨1703789, by rfl⟩ : syracuseStep 2271719 = 3407579) B3407579
theorem B2555689 : Blo 2271435 2555689 := bbase (se 2 (by rfl) ⟨958383, by rfl⟩ : syracuseStep 2555689 = 1916767) (by norm_num)
theorem B3407585 : Blo 2271435 3407585 := bstep (se 2 (by rfl) ⟨1277844, by rfl⟩ : syracuseStep 3407585 = 2555689) B2555689
theorem B2271723 : Blo 2271435 2271723 := bstep (se 1 (by rfl) ⟨1703792, by rfl⟩ : syracuseStep 2271723 = 3407585) B3407585
theorem B14555477 : Blo 2271435 14555477 := bbase (se 10 (by rfl) ⟨21321, by rfl⟩ : syracuseStep 14555477 = 42643) (by norm_num)
theorem B9703651 : Blo 2271435 9703651 := bstep (se 1 (by rfl) ⟨7277738, by rfl⟩ : syracuseStep 9703651 = 14555477) B14555477
theorem B12938201 : Blo 2271435 12938201 := bstep (se 2 (by rfl) ⟨4851825, by rfl⟩ : syracuseStep 12938201 = 9703651) B9703651
theorem B8625467 : Blo 2271435 8625467 := bstep (se 1 (by rfl) ⟨6469100, by rfl⟩ : syracuseStep 8625467 = 12938201) B12938201
theorem B5750311 : Blo 2271435 5750311 := bstep (se 1 (by rfl) ⟨4312733, by rfl⟩ : syracuseStep 5750311 = 8625467) B8625467
theorem B7667081 : Blo 2271435 7667081 := bstep (se 2 (by rfl) ⟨2875155, by rfl⟩ : syracuseStep 7667081 = 5750311) B5750311
theorem B5111387 : Blo 2271435 5111387 := bstep (se 1 (by rfl) ⟨3833540, by rfl⟩ : syracuseStep 5111387 = 7667081) B7667081
theorem B3407591 : Blo 2271435 3407591 := bstep (se 1 (by rfl) ⟨2555693, by rfl⟩ : syracuseStep 3407591 = 5111387) B5111387
theorem B2271727 : Blo 2271435 2271727 := bstep (se 1 (by rfl) ⟨1703795, by rfl⟩ : syracuseStep 2271727 = 3407591) B3407591
theorem B3407597 : Blo 2271435 3407597 := bbase (se 3 (by rfl) ⟨638924, by rfl⟩ : syracuseStep 3407597 = 1277849) (by norm_num)
theorem B2271731 : Blo 2271435 2271731 := bstep (se 1 (by rfl) ⟨1703798, by rfl⟩ : syracuseStep 2271731 = 3407597) B3407597
theorem B5111405 : Blo 2271435 5111405 := bbase (se 3 (by rfl) ⟨958388, by rfl⟩ : syracuseStep 5111405 = 1916777) (by norm_num)
theorem B3407603 : Blo 2271435 3407603 := bstep (se 1 (by rfl) ⟨2555702, by rfl⟩ : syracuseStep 3407603 = 5111405) B5111405
theorem B2271735 : Blo 2271435 2271735 := bstep (se 1 (by rfl) ⟨1703801, by rfl⟩ : syracuseStep 2271735 = 3407603) B3407603
theorem B4312757 : Blo 2271435 4312757 := bbase (se 5 (by rfl) ⟨202160, by rfl⟩ : syracuseStep 4312757 = 404321) (by norm_num)
theorem B2875171 : Blo 2271435 2875171 := bstep (se 1 (by rfl) ⟨2156378, by rfl⟩ : syracuseStep 2875171 = 4312757) B4312757
theorem B3833561 : Blo 2271435 3833561 := bstep (se 2 (by rfl) ⟨1437585, by rfl⟩ : syracuseStep 3833561 = 2875171) B2875171
theorem B2555707 : Blo 2271435 2555707 := bstep (se 1 (by rfl) ⟨1916780, by rfl⟩ : syracuseStep 2555707 = 3833561) B3833561
theorem B3407609 : Blo 2271435 3407609 := bstep (se 2 (by rfl) ⟨1277853, by rfl⟩ : syracuseStep 3407609 = 2555707) B2555707
theorem B2271739 : Blo 2271435 2271739 := bstep (se 1 (by rfl) ⟨1703804, by rfl⟩ : syracuseStep 2271739 = 3407609) B3407609
theorem B5988941 : Blo 2271435 5988941 := bbase (se 3 (by rfl) ⟨1122926, by rfl⟩ : syracuseStep 5988941 = 2245853) (by norm_num)
theorem B3992627 : Blo 2271435 3992627 := bstep (se 1 (by rfl) ⟨2994470, by rfl⟩ : syracuseStep 3992627 = 5988941) B5988941
theorem B2661751 : Blo 2271435 2661751 := bstep (se 1 (by rfl) ⟨1996313, by rfl⟩ : syracuseStep 2661751 = 3992627) B3992627
theorem B14196005 : Blo 2271435 14196005 := bstep (se 4 (by rfl) ⟨1330875, by rfl⟩ : syracuseStep 14196005 = 2661751) B2661751
theorem B9464003 : Blo 2271435 9464003 := bstep (se 1 (by rfl) ⟨7098002, by rfl⟩ : syracuseStep 9464003 = 14196005) B14196005
theorem B6309335 : Blo 2271435 6309335 := bstep (se 1 (by rfl) ⟨4732001, by rfl⟩ : syracuseStep 6309335 = 9464003) B9464003
theorem B16824893 : Blo 2271435 16824893 := bstep (se 3 (by rfl) ⟨3154667, by rfl⟩ : syracuseStep 16824893 = 6309335) B6309335
theorem B44866381 : Blo 2271435 44866381 := bstep (se 3 (by rfl) ⟨8412446, by rfl⟩ : syracuseStep 44866381 = 16824893) B16824893
theorem B59821841 : Blo 2271435 59821841 := bstep (se 2 (by rfl) ⟨22433190, by rfl⟩ : syracuseStep 59821841 = 44866381) B44866381
theorem B39881227 : Blo 2271435 39881227 := bstep (se 1 (by rfl) ⟨29910920, by rfl⟩ : syracuseStep 39881227 = 59821841) B59821841
theorem B53174969 : Blo 2271435 53174969 := bstep (se 2 (by rfl) ⟨19940613, by rfl⟩ : syracuseStep 53174969 = 39881227) B39881227
theorem B35449979 : Blo 2271435 35449979 := bstep (se 1 (by rfl) ⟨26587484, by rfl⟩ : syracuseStep 35449979 = 53174969) B53174969
theorem B94533277 : Blo 2271435 94533277 := bstep (se 3 (by rfl) ⟨17724989, by rfl⟩ : syracuseStep 94533277 = 35449979) B35449979
theorem B126044369 : Blo 2271435 126044369 := bstep (se 2 (by rfl) ⟨47266638, by rfl⟩ : syracuseStep 126044369 = 94533277) B94533277
theorem B84029579 : Blo 2271435 84029579 := bstep (se 1 (by rfl) ⟨63022184, by rfl⟩ : syracuseStep 84029579 = 126044369) B126044369
theorem B56019719 : Blo 2271435 56019719 := bstep (se 1 (by rfl) ⟨42014789, by rfl⟩ : syracuseStep 56019719 = 84029579) B84029579
theorem B149385917 : Blo 2271435 149385917 := bstep (se 3 (by rfl) ⟨28009859, by rfl⟩ : syracuseStep 149385917 = 56019719) B56019719
theorem B398362445 : Blo 2271435 398362445 := bstep (se 3 (by rfl) ⟨74692958, by rfl⟩ : syracuseStep 398362445 = 149385917) B149385917
theorem B265574963 : Blo 2271435 265574963 := bstep (se 1 (by rfl) ⟨199181222, by rfl⟩ : syracuseStep 265574963 = 398362445) B398362445
theorem B177049975 : Blo 2271435 177049975 := bstep (se 1 (by rfl) ⟨132787481, by rfl⟩ : syracuseStep 177049975 = 265574963) B265574963
theorem B236066633 : Blo 2271435 236066633 := bstep (se 2 (by rfl) ⟨88524987, by rfl⟩ : syracuseStep 236066633 = 177049975) B177049975
theorem B157377755 : Blo 2271435 157377755 := bstep (se 1 (by rfl) ⟨118033316, by rfl⟩ : syracuseStep 157377755 = 236066633) B236066633
theorem B104918503 : Blo 2271435 104918503 := bstep (se 1 (by rfl) ⟨78688877, by rfl⟩ : syracuseStep 104918503 = 157377755) B157377755
theorem B139891337 : Blo 2271435 139891337 := bstep (se 2 (by rfl) ⟨52459251, by rfl⟩ : syracuseStep 139891337 = 104918503) B104918503
theorem B93260891 : Blo 2271435 93260891 := bstep (se 1 (by rfl) ⟨69945668, by rfl⟩ : syracuseStep 93260891 = 139891337) B139891337
theorem B62173927 : Blo 2271435 62173927 := bstep (se 1 (by rfl) ⟨46630445, by rfl⟩ : syracuseStep 62173927 = 93260891) B93260891
theorem B82898569 : Blo 2271435 82898569 := bstep (se 2 (by rfl) ⟨31086963, by rfl⟩ : syracuseStep 82898569 = 62173927) B62173927
theorem B110531425 : Blo 2271435 110531425 := bstep (se 2 (by rfl) ⟨41449284, by rfl⟩ : syracuseStep 110531425 = 82898569) B82898569
theorem B147375233 : Blo 2271435 147375233 := bstep (se 2 (by rfl) ⟨55265712, by rfl⟩ : syracuseStep 147375233 = 110531425) B110531425
theorem B98250155 : Blo 2271435 98250155 := bstep (se 1 (by rfl) ⟨73687616, by rfl⟩ : syracuseStep 98250155 = 147375233) B147375233
theorem B65500103 : Blo 2271435 65500103 := bstep (se 1 (by rfl) ⟨49125077, by rfl⟩ : syracuseStep 65500103 = 98250155) B98250155
theorem B43666735 : Blo 2271435 43666735 := bstep (se 1 (by rfl) ⟨32750051, by rfl⟩ : syracuseStep 43666735 = 65500103) B65500103
theorem B58222313 : Blo 2271435 58222313 := bstep (se 2 (by rfl) ⟨21833367, by rfl⟩ : syracuseStep 58222313 = 43666735) B43666735
theorem B38814875 : Blo 2271435 38814875 := bstep (se 1 (by rfl) ⟨29111156, by rfl⟩ : syracuseStep 38814875 = 58222313) B58222313
theorem B25876583 : Blo 2271435 25876583 := bstep (se 1 (by rfl) ⟨19407437, by rfl⟩ : syracuseStep 25876583 = 38814875) B38814875
theorem B17251055 : Blo 2271435 17251055 := bstep (se 1 (by rfl) ⟨12938291, by rfl⟩ : syracuseStep 17251055 = 25876583) B25876583
theorem B11500703 : Blo 2271435 11500703 := bstep (se 1 (by rfl) ⟨8625527, by rfl⟩ : syracuseStep 11500703 = 17251055) B17251055
theorem B7667135 : Blo 2271435 7667135 := bstep (se 1 (by rfl) ⟨5750351, by rfl⟩ : syracuseStep 7667135 = 11500703) B11500703
theorem B5111423 : Blo 2271435 5111423 := bstep (se 1 (by rfl) ⟨3833567, by rfl⟩ : syracuseStep 5111423 = 7667135) B7667135
theorem B3407615 : Blo 2271435 3407615 := bstep (se 1 (by rfl) ⟨2555711, by rfl⟩ : syracuseStep 3407615 = 5111423) B5111423
theorem B2271743 : Blo 2271435 2271743 := bstep (se 1 (by rfl) ⟨1703807, by rfl⟩ : syracuseStep 2271743 = 3407615) B3407615
theorem B3407621 : Blo 2271435 3407621 := bbase (se 4 (by rfl) ⟨319464, by rfl⟩ : syracuseStep 3407621 = 638929) (by norm_num)
theorem B2271747 : Blo 2271435 2271747 := bstep (se 1 (by rfl) ⟨1703810, by rfl⟩ : syracuseStep 2271747 = 3407621) B3407621
theorem B3833581 : Blo 2271435 3833581 := bbase (se 3 (by rfl) ⟨718796, by rfl⟩ : syracuseStep 3833581 = 1437593) (by norm_num)
theorem B5111441 : Blo 2271435 5111441 := bstep (se 2 (by rfl) ⟨1916790, by rfl⟩ : syracuseStep 5111441 = 3833581) B3833581
theorem B3407627 : Blo 2271435 3407627 := bstep (se 1 (by rfl) ⟨2555720, by rfl⟩ : syracuseStep 3407627 = 5111441) B5111441
theorem B2271751 : Blo 2271435 2271751 := bstep (se 1 (by rfl) ⟨1703813, by rfl⟩ : syracuseStep 2271751 = 3407627) B3407627
theorem B2555725 : Blo 2271435 2555725 := bbase (se 3 (by rfl) ⟨479198, by rfl⟩ : syracuseStep 2555725 = 958397) (by norm_num)
theorem B3407633 : Blo 2271435 3407633 := bstep (se 2 (by rfl) ⟨1277862, by rfl⟩ : syracuseStep 3407633 = 2555725) B2555725
theorem B2271755 : Blo 2271435 2271755 := bstep (se 1 (by rfl) ⟨1703816, by rfl⟩ : syracuseStep 2271755 = 3407633) B3407633
theorem B7667189 : Blo 2271435 7667189 := bbase (se 5 (by rfl) ⟨359399, by rfl⟩ : syracuseStep 7667189 = 718799) (by norm_num)
theorem B5111459 : Blo 2271435 5111459 := bstep (se 1 (by rfl) ⟨3833594, by rfl⟩ : syracuseStep 5111459 = 7667189) B7667189
theorem B3407639 : Blo 2271435 3407639 := bstep (se 1 (by rfl) ⟨2555729, by rfl⟩ : syracuseStep 3407639 = 5111459) B5111459
theorem B2271759 : Blo 2271435 2271759 := bstep (se 1 (by rfl) ⟨1703819, by rfl⟩ : syracuseStep 2271759 = 3407639) B3407639
theorem B3407645 : Blo 2271435 3407645 := bbase (se 3 (by rfl) ⟨638933, by rfl⟩ : syracuseStep 3407645 = 1277867) (by norm_num)
theorem B2271763 : Blo 2271435 2271763 := bstep (se 1 (by rfl) ⟨1703822, by rfl⟩ : syracuseStep 2271763 = 3407645) B3407645
theorem B5111477 : Blo 2271435 5111477 := bbase (se 5 (by rfl) ⟨239600, by rfl⟩ : syracuseStep 5111477 = 479201) (by norm_num)
theorem B3407651 : Blo 2271435 3407651 := bstep (se 1 (by rfl) ⟨2555738, by rfl⟩ : syracuseStep 3407651 = 5111477) B5111477
theorem B2271767 : Blo 2271435 2271767 := bstep (se 1 (by rfl) ⟨1703825, by rfl⟩ : syracuseStep 2271767 = 3407651) B3407651
theorem B12938453 : Blo 2271435 12938453 := bbase (se 7 (by rfl) ⟨151622, by rfl⟩ : syracuseStep 12938453 = 303245) (by norm_num)
theorem B8625635 : Blo 2271435 8625635 := bstep (se 1 (by rfl) ⟨6469226, by rfl⟩ : syracuseStep 8625635 = 12938453) B12938453
theorem B5750423 : Blo 2271435 5750423 := bstep (se 1 (by rfl) ⟨4312817, by rfl⟩ : syracuseStep 5750423 = 8625635) B8625635
theorem B3833615 : Blo 2271435 3833615 := bstep (se 1 (by rfl) ⟨2875211, by rfl⟩ : syracuseStep 3833615 = 5750423) B5750423
theorem B2555743 : Blo 2271435 2555743 := bstep (se 1 (by rfl) ⟨1916807, by rfl⟩ : syracuseStep 2555743 = 3833615) B3833615
theorem B3407657 : Blo 2271435 3407657 := bstep (se 2 (by rfl) ⟨1277871, by rfl⟩ : syracuseStep 3407657 = 2555743) B2555743
theorem B2271771 : Blo 2271435 2271771 := bstep (se 1 (by rfl) ⟨1703828, by rfl⟩ : syracuseStep 2271771 = 3407657) B3407657
theorem B6469237 : Blo 2271435 6469237 := bbase (se 5 (by rfl) ⟨303245, by rfl⟩ : syracuseStep 6469237 = 606491) (by norm_num)
theorem B8625649 : Blo 2271435 8625649 := bstep (se 2 (by rfl) ⟨3234618, by rfl⟩ : syracuseStep 8625649 = 6469237) B6469237
theorem B11500865 : Blo 2271435 11500865 := bstep (se 2 (by rfl) ⟨4312824, by rfl⟩ : syracuseStep 11500865 = 8625649) B8625649
theorem B7667243 : Blo 2271435 7667243 := bstep (se 1 (by rfl) ⟨5750432, by rfl⟩ : syracuseStep 7667243 = 11500865) B11500865
theorem B5111495 : Blo 2271435 5111495 := bstep (se 1 (by rfl) ⟨3833621, by rfl⟩ : syracuseStep 5111495 = 7667243) B7667243
theorem B3407663 : Blo 2271435 3407663 := bstep (se 1 (by rfl) ⟨2555747, by rfl⟩ : syracuseStep 3407663 = 5111495) B5111495
theorem B2271775 : Blo 2271435 2271775 := bstep (se 1 (by rfl) ⟨1703831, by rfl⟩ : syracuseStep 2271775 = 3407663) B3407663
theorem B3407669 : Blo 2271435 3407669 := bbase (se 5 (by rfl) ⟨159734, by rfl⟩ : syracuseStep 3407669 = 319469) (by norm_num)
theorem B2271779 : Blo 2271435 2271779 := bstep (se 1 (by rfl) ⟨1703834, by rfl⟩ : syracuseStep 2271779 = 3407669) B3407669
theorem B5750453 : Blo 2271435 5750453 := bbase (se 5 (by rfl) ⟨269552, by rfl⟩ : syracuseStep 5750453 = 539105) (by norm_num)
theorem B3833635 : Blo 2271435 3833635 := bstep (se 1 (by rfl) ⟨2875226, by rfl⟩ : syracuseStep 3833635 = 5750453) B5750453
theorem B5111513 : Blo 2271435 5111513 := bstep (se 2 (by rfl) ⟨1916817, by rfl⟩ : syracuseStep 5111513 = 3833635) B3833635
theorem B3407675 : Blo 2271435 3407675 := bstep (se 1 (by rfl) ⟨2555756, by rfl⟩ : syracuseStep 3407675 = 5111513) B5111513
theorem B2271783 : Blo 2271435 2271783 := bstep (se 1 (by rfl) ⟨1703837, by rfl⟩ : syracuseStep 2271783 = 3407675) B3407675
theorem B2555761 : Blo 2271435 2555761 := bbase (se 2 (by rfl) ⟨958410, by rfl⟩ : syracuseStep 2555761 = 1916821) (by norm_num)
theorem B3407681 : Blo 2271435 3407681 := bstep (se 2 (by rfl) ⟨1277880, by rfl⟩ : syracuseStep 3407681 = 2555761) B2555761
theorem B2271787 : Blo 2271435 2271787 := bstep (se 1 (by rfl) ⟨1703840, by rfl⟩ : syracuseStep 2271787 = 3407681) B3407681
theorem B9703925 : Blo 2271435 9703925 := bbase (se 5 (by rfl) ⟨454871, by rfl⟩ : syracuseStep 9703925 = 909743) (by norm_num)
theorem B6469283 : Blo 2271435 6469283 := bstep (se 1 (by rfl) ⟨4851962, by rfl⟩ : syracuseStep 6469283 = 9703925) B9703925
theorem B4312855 : Blo 2271435 4312855 := bstep (se 1 (by rfl) ⟨3234641, by rfl⟩ : syracuseStep 4312855 = 6469283) B6469283
theorem B5750473 : Blo 2271435 5750473 := bstep (se 2 (by rfl) ⟨2156427, by rfl⟩ : syracuseStep 5750473 = 4312855) B4312855
theorem B7667297 : Blo 2271435 7667297 := bstep (se 2 (by rfl) ⟨2875236, by rfl⟩ : syracuseStep 7667297 = 5750473) B5750473
theorem B5111531 : Blo 2271435 5111531 := bstep (se 1 (by rfl) ⟨3833648, by rfl⟩ : syracuseStep 5111531 = 7667297) B7667297
theorem B3407687 : Blo 2271435 3407687 := bstep (se 1 (by rfl) ⟨2555765, by rfl⟩ : syracuseStep 3407687 = 5111531) B5111531
theorem B2271791 : Blo 2271435 2271791 := bstep (se 1 (by rfl) ⟨1703843, by rfl⟩ : syracuseStep 2271791 = 3407687) B3407687
theorem B3407693 : Blo 2271435 3407693 := bbase (se 3 (by rfl) ⟨638942, by rfl⟩ : syracuseStep 3407693 = 1277885) (by norm_num)
theorem B2271795 : Blo 2271435 2271795 := bstep (se 1 (by rfl) ⟨1703846, by rfl⟩ : syracuseStep 2271795 = 3407693) B3407693
theorem B5111549 : Blo 2271435 5111549 := bbase (se 3 (by rfl) ⟨958415, by rfl⟩ : syracuseStep 5111549 = 1916831) (by norm_num)
theorem B3407699 : Blo 2271435 3407699 := bstep (se 1 (by rfl) ⟨2555774, by rfl⟩ : syracuseStep 3407699 = 5111549) B5111549
theorem B2271799 : Blo 2271435 2271799 := bstep (se 1 (by rfl) ⟨1703849, by rfl⟩ : syracuseStep 2271799 = 3407699) B3407699
theorem B3833669 : Blo 2271435 3833669 := bbase (se 4 (by rfl) ⟨359406, by rfl⟩ : syracuseStep 3833669 = 718813) (by norm_num)
theorem B2555779 : Blo 2271435 2555779 := bstep (se 1 (by rfl) ⟨1916834, by rfl⟩ : syracuseStep 2555779 = 3833669) B3833669
theorem B3407705 : Blo 2271435 3407705 := bstep (se 2 (by rfl) ⟨1277889, by rfl⟩ : syracuseStep 3407705 = 2555779) B2555779
theorem B2271803 : Blo 2271435 2271803 := bstep (se 1 (by rfl) ⟨1703852, by rfl⟩ : syracuseStep 2271803 = 3407705) B3407705
theorem B17251541 : Blo 2271435 17251541 := bbase (se 7 (by rfl) ⟨202166, by rfl⟩ : syracuseStep 17251541 = 404333) (by norm_num)
theorem B11501027 : Blo 2271435 11501027 := bstep (se 1 (by rfl) ⟨8625770, by rfl⟩ : syracuseStep 11501027 = 17251541) B17251541
theorem B7667351 : Blo 2271435 7667351 := bstep (se 1 (by rfl) ⟨5750513, by rfl⟩ : syracuseStep 7667351 = 11501027) B11501027
theorem B5111567 : Blo 2271435 5111567 := bstep (se 1 (by rfl) ⟨3833675, by rfl⟩ : syracuseStep 5111567 = 7667351) B7667351
theorem B3407711 : Blo 2271435 3407711 := bstep (se 1 (by rfl) ⟨2555783, by rfl⟩ : syracuseStep 3407711 = 5111567) B5111567
theorem B2271807 : Blo 2271435 2271807 := bstep (se 1 (by rfl) ⟨1703855, by rfl⟩ : syracuseStep 2271807 = 3407711) B3407711
theorem B3407717 : Blo 2271435 3407717 := bbase (se 4 (by rfl) ⟨319473, by rfl⟩ : syracuseStep 3407717 = 638947) (by norm_num)
theorem B2271811 : Blo 2271435 2271811 := bstep (se 1 (by rfl) ⟨1703858, by rfl⟩ : syracuseStep 2271811 = 3407717) B3407717
theorem B4312901 : Blo 2271435 4312901 := bbase (se 4 (by rfl) ⟨404334, by rfl⟩ : syracuseStep 4312901 = 808669) (by norm_num)
theorem B2875267 : Blo 2271435 2875267 := bstep (se 1 (by rfl) ⟨2156450, by rfl⟩ : syracuseStep 2875267 = 4312901) B4312901
theorem B3833689 : Blo 2271435 3833689 := bstep (se 2 (by rfl) ⟨1437633, by rfl⟩ : syracuseStep 3833689 = 2875267) B2875267
theorem B5111585 : Blo 2271435 5111585 := bstep (se 2 (by rfl) ⟨1916844, by rfl⟩ : syracuseStep 5111585 = 3833689) B3833689
theorem B3407723 : Blo 2271435 3407723 := bstep (se 1 (by rfl) ⟨2555792, by rfl⟩ : syracuseStep 3407723 = 5111585) B5111585
theorem B2271815 : Blo 2271435 2271815 := bstep (se 1 (by rfl) ⟨1703861, by rfl⟩ : syracuseStep 2271815 = 3407723) B3407723
theorem B2555797 : Blo 2271435 2555797 := bbase (se 6 (by rfl) ⟨59901, by rfl⟩ : syracuseStep 2555797 = 119803) (by norm_num)
theorem B3407729 : Blo 2271435 3407729 := bstep (se 2 (by rfl) ⟨1277898, by rfl⟩ : syracuseStep 3407729 = 2555797) B2555797
theorem B2271819 : Blo 2271435 2271819 := bstep (se 1 (by rfl) ⟨1703864, by rfl⟩ : syracuseStep 2271819 = 3407729) B3407729
theorem B2875277 : Blo 2271435 2875277 := bbase (se 3 (by rfl) ⟨539114, by rfl⟩ : syracuseStep 2875277 = 1078229) (by norm_num)
theorem B7667405 : Blo 2271435 7667405 := bstep (se 3 (by rfl) ⟨1437638, by rfl⟩ : syracuseStep 7667405 = 2875277) B2875277
theorem B5111603 : Blo 2271435 5111603 := bstep (se 1 (by rfl) ⟨3833702, by rfl⟩ : syracuseStep 5111603 = 7667405) B7667405
theorem B3407735 : Blo 2271435 3407735 := bstep (se 1 (by rfl) ⟨2555801, by rfl⟩ : syracuseStep 3407735 = 5111603) B5111603
theorem B2271823 : Blo 2271435 2271823 := bstep (se 1 (by rfl) ⟨1703867, by rfl⟩ : syracuseStep 2271823 = 3407735) B3407735
theorem B3407741 : Blo 2271435 3407741 := bbase (se 3 (by rfl) ⟨638951, by rfl⟩ : syracuseStep 3407741 = 1277903) (by norm_num)
theorem B2271827 : Blo 2271435 2271827 := bstep (se 1 (by rfl) ⟨1703870, by rfl⟩ : syracuseStep 2271827 = 3407741) B3407741
theorem B5111621 : Blo 2271435 5111621 := bbase (se 4 (by rfl) ⟨479214, by rfl⟩ : syracuseStep 5111621 = 958429) (by norm_num)
theorem B3407747 : Blo 2271435 3407747 := bstep (se 1 (by rfl) ⟨2555810, by rfl⟩ : syracuseStep 3407747 = 5111621) B5111621
theorem B2271831 : Blo 2271435 2271831 := bstep (se 1 (by rfl) ⟨1703873, by rfl⟩ : syracuseStep 2271831 = 3407747) B3407747
theorem B5458565 : Blo 2271435 5458565 := bbase (se 4 (by rfl) ⟨511740, by rfl⟩ : syracuseStep 5458565 = 1023481) (by norm_num)
theorem B3639043 : Blo 2271435 3639043 := bstep (se 1 (by rfl) ⟨2729282, by rfl⟩ : syracuseStep 3639043 = 5458565) B5458565
theorem B4852057 : Blo 2271435 4852057 := bstep (se 2 (by rfl) ⟨1819521, by rfl⟩ : syracuseStep 4852057 = 3639043) B3639043
theorem B6469409 : Blo 2271435 6469409 := bstep (se 2 (by rfl) ⟨2426028, by rfl⟩ : syracuseStep 6469409 = 4852057) B4852057
theorem B4312939 : Blo 2271435 4312939 := bstep (se 1 (by rfl) ⟨3234704, by rfl⟩ : syracuseStep 4312939 = 6469409) B6469409
theorem B5750585 : Blo 2271435 5750585 := bstep (se 2 (by rfl) ⟨2156469, by rfl⟩ : syracuseStep 5750585 = 4312939) B4312939
theorem B3833723 : Blo 2271435 3833723 := bstep (se 1 (by rfl) ⟨2875292, by rfl⟩ : syracuseStep 3833723 = 5750585) B5750585
theorem B2555815 : Blo 2271435 2555815 := bstep (se 1 (by rfl) ⟨1916861, by rfl⟩ : syracuseStep 2555815 = 3833723) B3833723
theorem B3407753 : Blo 2271435 3407753 := bstep (se 2 (by rfl) ⟨1277907, by rfl⟩ : syracuseStep 3407753 = 2555815) B2555815
theorem B2271835 : Blo 2271435 2271835 := bstep (se 1 (by rfl) ⟨1703876, by rfl⟩ : syracuseStep 2271835 = 3407753) B3407753
theorem B11501189 : Blo 2271435 11501189 := bbase (se 4 (by rfl) ⟨1078236, by rfl⟩ : syracuseStep 11501189 = 2156473) (by norm_num)
theorem B7667459 : Blo 2271435 7667459 := bstep (se 1 (by rfl) ⟨5750594, by rfl⟩ : syracuseStep 7667459 = 11501189) B11501189
theorem B5111639 : Blo 2271435 5111639 := bstep (se 1 (by rfl) ⟨3833729, by rfl⟩ : syracuseStep 5111639 = 7667459) B7667459
theorem B3407759 : Blo 2271435 3407759 := bstep (se 1 (by rfl) ⟨2555819, by rfl⟩ : syracuseStep 3407759 = 5111639) B5111639
theorem B2271839 : Blo 2271435 2271839 := bstep (se 1 (by rfl) ⟨1703879, by rfl⟩ : syracuseStep 2271839 = 3407759) B3407759
theorem B3407765 : Blo 2271435 3407765 := bbase (se 6 (by rfl) ⟨79869, by rfl⟩ : syracuseStep 3407765 = 159739) (by norm_num)
theorem B2271843 : Blo 2271435 2271843 := bstep (se 1 (by rfl) ⟨1703882, by rfl⟩ : syracuseStep 2271843 = 3407765) B3407765
theorem B2426041 : Blo 2271435 2426041 := bbase (se 2 (by rfl) ⟨909765, by rfl⟩ : syracuseStep 2426041 = 1819531) (by norm_num)
theorem B12938885 : Blo 2271435 12938885 := bstep (se 4 (by rfl) ⟨1213020, by rfl⟩ : syracuseStep 12938885 = 2426041) B2426041
theorem B8625923 : Blo 2271435 8625923 := bstep (se 1 (by rfl) ⟨6469442, by rfl⟩ : syracuseStep 8625923 = 12938885) B12938885
theorem B5750615 : Blo 2271435 5750615 := bstep (se 1 (by rfl) ⟨4312961, by rfl⟩ : syracuseStep 5750615 = 8625923) B8625923
theorem B3833743 : Blo 2271435 3833743 := bstep (se 1 (by rfl) ⟨2875307, by rfl⟩ : syracuseStep 3833743 = 5750615) B5750615
theorem B5111657 : Blo 2271435 5111657 := bstep (se 2 (by rfl) ⟨1916871, by rfl⟩ : syracuseStep 5111657 = 3833743) B3833743
theorem B3407771 : Blo 2271435 3407771 := bstep (se 1 (by rfl) ⟨2555828, by rfl⟩ : syracuseStep 3407771 = 5111657) B5111657
theorem B2271847 : Blo 2271435 2271847 := bstep (se 1 (by rfl) ⟨1703885, by rfl⟩ : syracuseStep 2271847 = 3407771) B3407771
theorem B2555833 : Blo 2271435 2555833 := bbase (se 2 (by rfl) ⟨958437, by rfl⟩ : syracuseStep 2555833 = 1916875) (by norm_num)
theorem B3407777 : Blo 2271435 3407777 := bstep (se 2 (by rfl) ⟨1277916, by rfl⟩ : syracuseStep 3407777 = 2555833) B2555833
theorem B2271851 : Blo 2271435 2271851 := bstep (se 1 (by rfl) ⟨1703888, by rfl⟩ : syracuseStep 2271851 = 3407777) B3407777
theorem B7278149 : Blo 2271435 7278149 := bbase (se 4 (by rfl) ⟨682326, by rfl⟩ : syracuseStep 7278149 = 1364653) (by norm_num)
theorem B4852099 : Blo 2271435 4852099 := bstep (se 1 (by rfl) ⟨3639074, by rfl⟩ : syracuseStep 4852099 = 7278149) B7278149
theorem B6469465 : Blo 2271435 6469465 := bstep (se 2 (by rfl) ⟨2426049, by rfl⟩ : syracuseStep 6469465 = 4852099) B4852099
theorem B8625953 : Blo 2271435 8625953 := bstep (se 2 (by rfl) ⟨3234732, by rfl⟩ : syracuseStep 8625953 = 6469465) B6469465
theorem B5750635 : Blo 2271435 5750635 := bstep (se 1 (by rfl) ⟨4312976, by rfl⟩ : syracuseStep 5750635 = 8625953) B8625953
theorem B7667513 : Blo 2271435 7667513 := bstep (se 2 (by rfl) ⟨2875317, by rfl⟩ : syracuseStep 7667513 = 5750635) B5750635
theorem B5111675 : Blo 2271435 5111675 := bstep (se 1 (by rfl) ⟨3833756, by rfl⟩ : syracuseStep 5111675 = 7667513) B7667513
theorem B3407783 : Blo 2271435 3407783 := bstep (se 1 (by rfl) ⟨2555837, by rfl⟩ : syracuseStep 3407783 = 5111675) B5111675
theorem B2271855 : Blo 2271435 2271855 := bstep (se 1 (by rfl) ⟨1703891, by rfl⟩ : syracuseStep 2271855 = 3407783) B3407783
theorem B3407789 : Blo 2271435 3407789 := bbase (se 3 (by rfl) ⟨638960, by rfl⟩ : syracuseStep 3407789 = 1277921) (by norm_num)
theorem B2271859 : Blo 2271435 2271859 := bstep (se 1 (by rfl) ⟨1703894, by rfl⟩ : syracuseStep 2271859 = 3407789) B3407789
theorem B5111693 : Blo 2271435 5111693 := bbase (se 3 (by rfl) ⟨958442, by rfl⟩ : syracuseStep 5111693 = 1916885) (by norm_num)
theorem B3407795 : Blo 2271435 3407795 := bstep (se 1 (by rfl) ⟨2555846, by rfl⟩ : syracuseStep 3407795 = 5111693) B5111693
theorem B2271863 : Blo 2271435 2271863 := bstep (se 1 (by rfl) ⟨1703897, by rfl⟩ : syracuseStep 2271863 = 3407795) B3407795
theorem B2875333 : Blo 2271435 2875333 := bbase (se 4 (by rfl) ⟨269562, by rfl⟩ : syracuseStep 2875333 = 539125) (by norm_num)
theorem B3833777 : Blo 2271435 3833777 := bstep (se 2 (by rfl) ⟨1437666, by rfl⟩ : syracuseStep 3833777 = 2875333) B2875333
theorem B2555851 : Blo 2271435 2555851 := bstep (se 1 (by rfl) ⟨1916888, by rfl⟩ : syracuseStep 2555851 = 3833777) B3833777
theorem B3407801 : Blo 2271435 3407801 := bstep (se 2 (by rfl) ⟨1277925, by rfl⟩ : syracuseStep 3407801 = 2555851) B2555851
theorem B2271867 : Blo 2271435 2271867 := bstep (se 1 (by rfl) ⟨1703900, by rfl⟩ : syracuseStep 2271867 = 3407801) B3407801
theorem B6140981 : Blo 2271435 6140981 := bbase (se 5 (by rfl) ⟨287858, by rfl⟩ : syracuseStep 6140981 = 575717) (by norm_num)
theorem B16375949 : Blo 2271435 16375949 := bstep (se 3 (by rfl) ⟨3070490, by rfl⟩ : syracuseStep 16375949 = 6140981) B6140981
theorem B10917299 : Blo 2271435 10917299 := bstep (se 1 (by rfl) ⟨8187974, by rfl⟩ : syracuseStep 10917299 = 16375949) B16375949
theorem B29112797 : Blo 2271435 29112797 := bstep (se 3 (by rfl) ⟨5458649, by rfl⟩ : syracuseStep 29112797 = 10917299) B10917299
theorem B19408531 : Blo 2271435 19408531 := bstep (se 1 (by rfl) ⟨14556398, by rfl⟩ : syracuseStep 19408531 = 29112797) B29112797
theorem B25878041 : Blo 2271435 25878041 := bstep (se 2 (by rfl) ⟨9704265, by rfl⟩ : syracuseStep 25878041 = 19408531) B19408531
theorem B17252027 : Blo 2271435 17252027 := bstep (se 1 (by rfl) ⟨12939020, by rfl⟩ : syracuseStep 17252027 = 25878041) B25878041
theorem B11501351 : Blo 2271435 11501351 := bstep (se 1 (by rfl) ⟨8626013, by rfl⟩ : syracuseStep 11501351 = 17252027) B17252027
theorem B7667567 : Blo 2271435 7667567 := bstep (se 1 (by rfl) ⟨5750675, by rfl⟩ : syracuseStep 7667567 = 11501351) B11501351
theorem B5111711 : Blo 2271435 5111711 := bstep (se 1 (by rfl) ⟨3833783, by rfl⟩ : syracuseStep 5111711 = 7667567) B7667567
theorem B3407807 : Blo 2271435 3407807 := bstep (se 1 (by rfl) ⟨2555855, by rfl⟩ : syracuseStep 3407807 = 5111711) B5111711
theorem B2271871 : Blo 2271435 2271871 := bstep (se 1 (by rfl) ⟨1703903, by rfl⟩ : syracuseStep 2271871 = 3407807) B3407807
theorem B3407813 : Blo 2271435 3407813 := bbase (se 4 (by rfl) ⟨319482, by rfl⟩ : syracuseStep 3407813 = 638965) (by norm_num)
theorem B2271875 : Blo 2271435 2271875 := bstep (se 1 (by rfl) ⟨1703906, by rfl⟩ : syracuseStep 2271875 = 3407813) B3407813
theorem B3833797 : Blo 2271435 3833797 := bbase (se 4 (by rfl) ⟨359418, by rfl⟩ : syracuseStep 3833797 = 718837) (by norm_num)
theorem B5111729 : Blo 2271435 5111729 := bstep (se 2 (by rfl) ⟨1916898, by rfl⟩ : syracuseStep 5111729 = 3833797) B3833797
theorem B3407819 : Blo 2271435 3407819 := bstep (se 1 (by rfl) ⟨2555864, by rfl⟩ : syracuseStep 3407819 = 5111729) B5111729
theorem B2271879 : Blo 2271435 2271879 := bstep (se 1 (by rfl) ⟨1703909, by rfl⟩ : syracuseStep 2271879 = 3407819) B3407819
theorem B2555869 : Blo 2271435 2555869 := bbase (se 3 (by rfl) ⟨479225, by rfl⟩ : syracuseStep 2555869 = 958451) (by norm_num)
theorem B3407825 : Blo 2271435 3407825 := bstep (se 2 (by rfl) ⟨1277934, by rfl⟩ : syracuseStep 3407825 = 2555869) B2555869
theorem B2271883 : Blo 2271435 2271883 := bstep (se 1 (by rfl) ⟨1703912, by rfl⟩ : syracuseStep 2271883 = 3407825) B3407825
theorem B7667621 : Blo 2271435 7667621 := bbase (se 4 (by rfl) ⟨718839, by rfl⟩ : syracuseStep 7667621 = 1437679) (by norm_num)
theorem B5111747 : Blo 2271435 5111747 := bstep (se 1 (by rfl) ⟨3833810, by rfl⟩ : syracuseStep 5111747 = 7667621) B7667621
theorem B3407831 : Blo 2271435 3407831 := bstep (se 1 (by rfl) ⟨2555873, by rfl⟩ : syracuseStep 3407831 = 5111747) B5111747
theorem B2271887 : Blo 2271435 2271887 := bstep (se 1 (by rfl) ⟨1703915, by rfl⟩ : syracuseStep 2271887 = 3407831) B3407831
theorem B3407837 : Blo 2271435 3407837 := bbase (se 3 (by rfl) ⟨638969, by rfl⟩ : syracuseStep 3407837 = 1277939) (by norm_num)
theorem B2271891 : Blo 2271435 2271891 := bstep (se 1 (by rfl) ⟨1703918, by rfl⟩ : syracuseStep 2271891 = 3407837) B3407837
theorem B5111765 : Blo 2271435 5111765 := bbase (se 7 (by rfl) ⟨59903, by rfl⟩ : syracuseStep 5111765 = 119807) (by norm_num)
theorem B3407843 : Blo 2271435 3407843 := bstep (se 1 (by rfl) ⟨2555882, by rfl⟩ : syracuseStep 3407843 = 5111765) B5111765
theorem B2271895 : Blo 2271435 2271895 := bstep (se 1 (by rfl) ⟨1703921, by rfl⟩ : syracuseStep 2271895 = 3407843) B3407843
theorem B9211589 : Blo 2271435 9211589 := bbase (se 4 (by rfl) ⟨863586, by rfl⟩ : syracuseStep 9211589 = 1727173) (by norm_num)
theorem B6141059 : Blo 2271435 6141059 := bstep (se 1 (by rfl) ⟨4605794, by rfl⟩ : syracuseStep 6141059 = 9211589) B9211589
theorem B4094039 : Blo 2271435 4094039 := bstep (se 1 (by rfl) ⟨3070529, by rfl⟩ : syracuseStep 4094039 = 6141059) B6141059
theorem B2729359 : Blo 2271435 2729359 := bstep (se 1 (by rfl) ⟨2047019, by rfl⟩ : syracuseStep 2729359 = 4094039) B4094039
theorem B14556581 : Blo 2271435 14556581 := bstep (se 4 (by rfl) ⟨1364679, by rfl⟩ : syracuseStep 14556581 = 2729359) B2729359
theorem B9704387 : Blo 2271435 9704387 := bstep (se 1 (by rfl) ⟨7278290, by rfl⟩ : syracuseStep 9704387 = 14556581) B14556581
theorem B6469591 : Blo 2271435 6469591 := bstep (se 1 (by rfl) ⟨4852193, by rfl⟩ : syracuseStep 6469591 = 9704387) B9704387
theorem B8626121 : Blo 2271435 8626121 := bstep (se 2 (by rfl) ⟨3234795, by rfl⟩ : syracuseStep 8626121 = 6469591) B6469591
theorem B5750747 : Blo 2271435 5750747 := bstep (se 1 (by rfl) ⟨4313060, by rfl⟩ : syracuseStep 5750747 = 8626121) B8626121
theorem B3833831 : Blo 2271435 3833831 := bstep (se 1 (by rfl) ⟨2875373, by rfl⟩ : syracuseStep 3833831 = 5750747) B5750747
theorem B2555887 : Blo 2271435 2555887 := bstep (se 1 (by rfl) ⟨1916915, by rfl⟩ : syracuseStep 2555887 = 3833831) B3833831
theorem B3407849 : Blo 2271435 3407849 := bstep (se 2 (by rfl) ⟨1277943, by rfl⟩ : syracuseStep 3407849 = 2555887) B2555887
theorem B2271899 : Blo 2271435 2271899 := bstep (se 1 (by rfl) ⟨1703924, by rfl⟩ : syracuseStep 2271899 = 3407849) B3407849
theorem B11658437 : Blo 2271435 11658437 := bbase (se 4 (by rfl) ⟨1092978, by rfl⟩ : syracuseStep 11658437 = 2185957) (by norm_num)
theorem B7772291 : Blo 2271435 7772291 := bstep (se 1 (by rfl) ⟨5829218, by rfl⟩ : syracuseStep 7772291 = 11658437) B11658437
theorem B5181527 : Blo 2271435 5181527 := bstep (se 1 (by rfl) ⟨3886145, by rfl⟩ : syracuseStep 5181527 = 7772291) B7772291
theorem B13817405 : Blo 2271435 13817405 := bstep (se 3 (by rfl) ⟨2590763, by rfl⟩ : syracuseStep 13817405 = 5181527) B5181527
theorem B9211603 : Blo 2271435 9211603 := bstep (se 1 (by rfl) ⟨6908702, by rfl⟩ : syracuseStep 9211603 = 13817405) B13817405
theorem B12282137 : Blo 2271435 12282137 := bstep (se 2 (by rfl) ⟨4605801, by rfl⟩ : syracuseStep 12282137 = 9211603) B9211603
theorem B8188091 : Blo 2271435 8188091 := bstep (se 1 (by rfl) ⟨6141068, by rfl⟩ : syracuseStep 8188091 = 12282137) B12282137
theorem B5458727 : Blo 2271435 5458727 := bstep (se 1 (by rfl) ⟨4094045, by rfl⟩ : syracuseStep 5458727 = 8188091) B8188091
theorem B3639151 : Blo 2271435 3639151 := bstep (se 1 (by rfl) ⟨2729363, by rfl⟩ : syracuseStep 3639151 = 5458727) B5458727
theorem B19408805 : Blo 2271435 19408805 := bstep (se 4 (by rfl) ⟨1819575, by rfl⟩ : syracuseStep 19408805 = 3639151) B3639151
theorem B12939203 : Blo 2271435 12939203 := bstep (se 1 (by rfl) ⟨9704402, by rfl⟩ : syracuseStep 12939203 = 19408805) B19408805
theorem B8626135 : Blo 2271435 8626135 := bstep (se 1 (by rfl) ⟨6469601, by rfl⟩ : syracuseStep 8626135 = 12939203) B12939203
theorem B11501513 : Blo 2271435 11501513 := bstep (se 2 (by rfl) ⟨4313067, by rfl⟩ : syracuseStep 11501513 = 8626135) B8626135
theorem B7667675 : Blo 2271435 7667675 := bstep (se 1 (by rfl) ⟨5750756, by rfl⟩ : syracuseStep 7667675 = 11501513) B11501513
theorem B5111783 : Blo 2271435 5111783 := bstep (se 1 (by rfl) ⟨3833837, by rfl⟩ : syracuseStep 5111783 = 7667675) B7667675
theorem B3407855 : Blo 2271435 3407855 := bstep (se 1 (by rfl) ⟨2555891, by rfl⟩ : syracuseStep 3407855 = 5111783) B5111783
theorem B2271903 : Blo 2271435 2271903 := bstep (se 1 (by rfl) ⟨1703927, by rfl⟩ : syracuseStep 2271903 = 3407855) B3407855
theorem B3407861 : Blo 2271435 3407861 := bbase (se 5 (by rfl) ⟨159743, by rfl⟩ : syracuseStep 3407861 = 319487) (by norm_num)
theorem B2271907 : Blo 2271435 2271907 := bstep (se 1 (by rfl) ⟨1703930, by rfl⟩ : syracuseStep 2271907 = 3407861) B3407861
theorem B9211637 : Blo 2271435 9211637 := bbase (se 5 (by rfl) ⟨431795, by rfl⟩ : syracuseStep 9211637 = 863591) (by norm_num)
theorem B6141091 : Blo 2271435 6141091 := bstep (se 1 (by rfl) ⟨4605818, by rfl⟩ : syracuseStep 6141091 = 9211637) B9211637
theorem B8188121 : Blo 2271435 8188121 := bstep (se 2 (by rfl) ⟨3070545, by rfl⟩ : syracuseStep 8188121 = 6141091) B6141091
theorem B5458747 : Blo 2271435 5458747 := bstep (se 1 (by rfl) ⟨4094060, by rfl⟩ : syracuseStep 5458747 = 8188121) B8188121
theorem B7278329 : Blo 2271435 7278329 := bstep (se 2 (by rfl) ⟨2729373, by rfl⟩ : syracuseStep 7278329 = 5458747) B5458747
theorem B4852219 : Blo 2271435 4852219 := bstep (se 1 (by rfl) ⟨3639164, by rfl⟩ : syracuseStep 4852219 = 7278329) B7278329
theorem B6469625 : Blo 2271435 6469625 := bstep (se 2 (by rfl) ⟨2426109, by rfl⟩ : syracuseStep 6469625 = 4852219) B4852219
theorem B4313083 : Blo 2271435 4313083 := bstep (se 1 (by rfl) ⟨3234812, by rfl⟩ : syracuseStep 4313083 = 6469625) B6469625
theorem B5750777 : Blo 2271435 5750777 := bstep (se 2 (by rfl) ⟨2156541, by rfl⟩ : syracuseStep 5750777 = 4313083) B4313083
theorem B3833851 : Blo 2271435 3833851 := bstep (se 1 (by rfl) ⟨2875388, by rfl⟩ : syracuseStep 3833851 = 5750777) B5750777
theorem B5111801 : Blo 2271435 5111801 := bstep (se 2 (by rfl) ⟨1916925, by rfl⟩ : syracuseStep 5111801 = 3833851) B3833851
theorem B3407867 : Blo 2271435 3407867 := bstep (se 1 (by rfl) ⟨2555900, by rfl⟩ : syracuseStep 3407867 = 5111801) B5111801
theorem B2271911 : Blo 2271435 2271911 := bstep (se 1 (by rfl) ⟨1703933, by rfl⟩ : syracuseStep 2271911 = 3407867) B3407867
theorem B2555905 : Blo 2271435 2555905 := bbase (se 2 (by rfl) ⟨958464, by rfl⟩ : syracuseStep 2555905 = 1916929) (by norm_num)
theorem B3407873 : Blo 2271435 3407873 := bstep (se 2 (by rfl) ⟨1277952, by rfl⟩ : syracuseStep 3407873 = 2555905) B2555905
theorem B2271915 : Blo 2271435 2271915 := bstep (se 1 (by rfl) ⟨1703936, by rfl⟩ : syracuseStep 2271915 = 3407873) B3407873
theorem B5750797 : Blo 2271435 5750797 := bbase (se 3 (by rfl) ⟨1078274, by rfl⟩ : syracuseStep 5750797 = 2156549) (by norm_num)
theorem B7667729 : Blo 2271435 7667729 := bstep (se 2 (by rfl) ⟨2875398, by rfl⟩ : syracuseStep 7667729 = 5750797) B5750797
theorem B5111819 : Blo 2271435 5111819 := bstep (se 1 (by rfl) ⟨3833864, by rfl⟩ : syracuseStep 5111819 = 7667729) B7667729
theorem B3407879 : Blo 2271435 3407879 := bstep (se 1 (by rfl) ⟨2555909, by rfl⟩ : syracuseStep 3407879 = 5111819) B5111819
theorem B2271919 : Blo 2271435 2271919 := bstep (se 1 (by rfl) ⟨1703939, by rfl⟩ : syracuseStep 2271919 = 3407879) B3407879
theorem B3407885 : Blo 2271435 3407885 := bbase (se 3 (by rfl) ⟨638978, by rfl⟩ : syracuseStep 3407885 = 1277957) (by norm_num)
theorem B2271923 : Blo 2271435 2271923 := bstep (se 1 (by rfl) ⟨1703942, by rfl⟩ : syracuseStep 2271923 = 3407885) B3407885
theorem B5111837 : Blo 2271435 5111837 := bbase (se 3 (by rfl) ⟨958469, by rfl⟩ : syracuseStep 5111837 = 1916939) (by norm_num)
theorem B3407891 : Blo 2271435 3407891 := bstep (se 1 (by rfl) ⟨2555918, by rfl⟩ : syracuseStep 3407891 = 5111837) B5111837
theorem B2271927 : Blo 2271435 2271927 := bstep (se 1 (by rfl) ⟨1703945, by rfl⟩ : syracuseStep 2271927 = 3407891) B3407891
theorem B3833885 : Blo 2271435 3833885 := bbase (se 3 (by rfl) ⟨718853, by rfl⟩ : syracuseStep 3833885 = 1437707) (by norm_num)
theorem B2555923 : Blo 2271435 2555923 := bstep (se 1 (by rfl) ⟨1916942, by rfl⟩ : syracuseStep 2555923 = 3833885) B3833885
theorem B3407897 : Blo 2271435 3407897 := bstep (se 2 (by rfl) ⟨1277961, by rfl⟩ : syracuseStep 3407897 = 2555923) B2555923
theorem B2271931 : Blo 2271435 2271931 := bstep (se 1 (by rfl) ⟨1703948, by rfl⟩ : syracuseStep 2271931 = 3407897) B3407897
theorem B2334353 : Blo 2271435 2334353 := bbase (se 2 (by rfl) ⟨875382, by rfl⟩ : syracuseStep 2334353 = 1750765) (by norm_num)
theorem B6224941 : Blo 2271435 6224941 := bstep (se 3 (by rfl) ⟨1167176, by rfl⟩ : syracuseStep 6224941 = 2334353) B2334353
theorem B8299921 : Blo 2271435 8299921 := bstep (se 2 (by rfl) ⟨3112470, by rfl⟩ : syracuseStep 8299921 = 6224941) B6224941
theorem B11066561 : Blo 2271435 11066561 := bstep (se 2 (by rfl) ⟨4149960, by rfl⟩ : syracuseStep 11066561 = 8299921) B8299921
theorem B7377707 : Blo 2271435 7377707 := bstep (se 1 (by rfl) ⟨5533280, by rfl⟩ : syracuseStep 7377707 = 11066561) B11066561
theorem B19673885 : Blo 2271435 19673885 := bstep (se 3 (by rfl) ⟨3688853, by rfl⟩ : syracuseStep 19673885 = 7377707) B7377707
theorem B52463693 : Blo 2271435 52463693 := bstep (se 3 (by rfl) ⟨9836942, by rfl⟩ : syracuseStep 52463693 = 19673885) B19673885
theorem B34975795 : Blo 2271435 34975795 := bstep (se 1 (by rfl) ⟨26231846, by rfl⟩ : syracuseStep 34975795 = 52463693) B52463693
theorem B46634393 : Blo 2271435 46634393 := bstep (se 2 (by rfl) ⟨17487897, by rfl⟩ : syracuseStep 46634393 = 34975795) B34975795
theorem B31089595 : Blo 2271435 31089595 := bstep (se 1 (by rfl) ⟨23317196, by rfl⟩ : syracuseStep 31089595 = 46634393) B46634393
theorem B41452793 : Blo 2271435 41452793 := bstep (se 2 (by rfl) ⟨15544797, by rfl⟩ : syracuseStep 41452793 = 31089595) B31089595
theorem B27635195 : Blo 2271435 27635195 := bstep (se 1 (by rfl) ⟨20726396, by rfl⟩ : syracuseStep 27635195 = 41452793) B41452793
theorem B18423463 : Blo 2271435 18423463 := bstep (se 1 (by rfl) ⟨13817597, by rfl⟩ : syracuseStep 18423463 = 27635195) B27635195
theorem B24564617 : Blo 2271435 24564617 := bstep (se 2 (by rfl) ⟨9211731, by rfl⟩ : syracuseStep 24564617 = 18423463) B18423463
theorem B16376411 : Blo 2271435 16376411 := bstep (se 1 (by rfl) ⟨12282308, by rfl⟩ : syracuseStep 16376411 = 24564617) B24564617
theorem B10917607 : Blo 2271435 10917607 := bstep (se 1 (by rfl) ⟨8188205, by rfl⟩ : syracuseStep 10917607 = 16376411) B16376411
theorem B14556809 : Blo 2271435 14556809 := bstep (se 2 (by rfl) ⟨5458803, by rfl⟩ : syracuseStep 14556809 = 10917607) B10917607
theorem B9704539 : Blo 2271435 9704539 := bstep (se 1 (by rfl) ⟨7278404, by rfl⟩ : syracuseStep 9704539 = 14556809) B14556809
theorem B12939385 : Blo 2271435 12939385 := bstep (se 2 (by rfl) ⟨4852269, by rfl⟩ : syracuseStep 12939385 = 9704539) B9704539
theorem B17252513 : Blo 2271435 17252513 := bstep (se 2 (by rfl) ⟨6469692, by rfl⟩ : syracuseStep 17252513 = 12939385) B12939385
theorem B11501675 : Blo 2271435 11501675 := bstep (se 1 (by rfl) ⟨8626256, by rfl⟩ : syracuseStep 11501675 = 17252513) B17252513
theorem B7667783 : Blo 2271435 7667783 := bstep (se 1 (by rfl) ⟨5750837, by rfl⟩ : syracuseStep 7667783 = 11501675) B11501675
theorem B5111855 : Blo 2271435 5111855 := bstep (se 1 (by rfl) ⟨3833891, by rfl⟩ : syracuseStep 5111855 = 7667783) B7667783
theorem B3407903 : Blo 2271435 3407903 := bstep (se 1 (by rfl) ⟨2555927, by rfl⟩ : syracuseStep 3407903 = 5111855) B5111855
theorem B2271935 : Blo 2271435 2271935 := bstep (se 1 (by rfl) ⟨1703951, by rfl⟩ : syracuseStep 2271935 = 3407903) B3407903
theorem B3407909 : Blo 2271435 3407909 := bbase (se 4 (by rfl) ⟨319491, by rfl⟩ : syracuseStep 3407909 = 638983) (by norm_num)
theorem B2271939 : Blo 2271435 2271939 := bstep (se 1 (by rfl) ⟨1703954, by rfl⟩ : syracuseStep 2271939 = 3407909) B3407909
theorem B2875429 : Blo 2271435 2875429 := bbase (se 4 (by rfl) ⟨269571, by rfl⟩ : syracuseStep 2875429 = 539143) (by norm_num)
theorem B3833905 : Blo 2271435 3833905 := bstep (se 2 (by rfl) ⟨1437714, by rfl⟩ : syracuseStep 3833905 = 2875429) B2875429
theorem B5111873 : Blo 2271435 5111873 := bstep (se 2 (by rfl) ⟨1916952, by rfl⟩ : syracuseStep 5111873 = 3833905) B3833905
theorem B3407915 : Blo 2271435 3407915 := bstep (se 1 (by rfl) ⟨2555936, by rfl⟩ : syracuseStep 3407915 = 5111873) B5111873
theorem B2271943 : Blo 2271435 2271943 := bstep (se 1 (by rfl) ⟨1703957, by rfl⟩ : syracuseStep 2271943 = 3407915) B3407915
theorem B2555941 : Blo 2271435 2555941 := bbase (se 4 (by rfl) ⟨239619, by rfl⟩ : syracuseStep 2555941 = 479239) (by norm_num)
theorem B3407921 : Blo 2271435 3407921 := bstep (se 2 (by rfl) ⟨1277970, by rfl⟩ : syracuseStep 3407921 = 2555941) B2555941
theorem B2271947 : Blo 2271435 2271947 := bstep (se 1 (by rfl) ⟨1703960, by rfl⟩ : syracuseStep 2271947 = 3407921) B3407921
theorem B20726549 : Blo 2271435 20726549 := bbase (se 6 (by rfl) ⟨485778, by rfl⟩ : syracuseStep 20726549 = 971557) (by norm_num)
theorem B13817699 : Blo 2271435 13817699 := bstep (se 1 (by rfl) ⟨10363274, by rfl⟩ : syracuseStep 13817699 = 20726549) B20726549
theorem B9211799 : Blo 2271435 9211799 := bstep (se 1 (by rfl) ⟨6908849, by rfl⟩ : syracuseStep 9211799 = 13817699) B13817699
theorem B6141199 : Blo 2271435 6141199 := bstep (se 1 (by rfl) ⟨4605899, by rfl⟩ : syracuseStep 6141199 = 9211799) B9211799
theorem B8188265 : Blo 2271435 8188265 := bstep (se 2 (by rfl) ⟨3070599, by rfl⟩ : syracuseStep 8188265 = 6141199) B6141199
theorem B5458843 : Blo 2271435 5458843 := bstep (se 1 (by rfl) ⟨4094132, by rfl⟩ : syracuseStep 5458843 = 8188265) B8188265
theorem B7278457 : Blo 2271435 7278457 := bstep (se 2 (by rfl) ⟨2729421, by rfl⟩ : syracuseStep 7278457 = 5458843) B5458843
theorem B9704609 : Blo 2271435 9704609 := bstep (se 2 (by rfl) ⟨3639228, by rfl⟩ : syracuseStep 9704609 = 7278457) B7278457
theorem B6469739 : Blo 2271435 6469739 := bstep (se 1 (by rfl) ⟨4852304, by rfl⟩ : syracuseStep 6469739 = 9704609) B9704609
theorem B4313159 : Blo 2271435 4313159 := bstep (se 1 (by rfl) ⟨3234869, by rfl⟩ : syracuseStep 4313159 = 6469739) B6469739
theorem B2875439 : Blo 2271435 2875439 := bstep (se 1 (by rfl) ⟨2156579, by rfl⟩ : syracuseStep 2875439 = 4313159) B4313159
theorem B7667837 : Blo 2271435 7667837 := bstep (se 3 (by rfl) ⟨1437719, by rfl⟩ : syracuseStep 7667837 = 2875439) B2875439
theorem B5111891 : Blo 2271435 5111891 := bstep (se 1 (by rfl) ⟨3833918, by rfl⟩ : syracuseStep 5111891 = 7667837) B7667837
theorem B3407927 : Blo 2271435 3407927 := bstep (se 1 (by rfl) ⟨2555945, by rfl⟩ : syracuseStep 3407927 = 5111891) B5111891
theorem B2271951 : Blo 2271435 2271951 := bstep (se 1 (by rfl) ⟨1703963, by rfl⟩ : syracuseStep 2271951 = 3407927) B3407927
theorem B3407933 : Blo 2271435 3407933 := bbase (se 3 (by rfl) ⟨638987, by rfl⟩ : syracuseStep 3407933 = 1277975) (by norm_num)
theorem B2271955 : Blo 2271435 2271955 := bstep (se 1 (by rfl) ⟨1703966, by rfl⟩ : syracuseStep 2271955 = 3407933) B3407933
theorem B5111909 : Blo 2271435 5111909 := bbase (se 4 (by rfl) ⟨479241, by rfl⟩ : syracuseStep 5111909 = 958483) (by norm_num)
theorem B3407939 : Blo 2271435 3407939 := bstep (se 1 (by rfl) ⟨2555954, by rfl⟩ : syracuseStep 3407939 = 5111909) B5111909
theorem B2271959 : Blo 2271435 2271959 := bstep (se 1 (by rfl) ⟨1703969, by rfl⟩ : syracuseStep 2271959 = 3407939) B3407939
theorem B5750909 : Blo 2271435 5750909 := bbase (se 3 (by rfl) ⟨1078295, by rfl⟩ : syracuseStep 5750909 = 2156591) (by norm_num)
theorem B3833939 : Blo 2271435 3833939 := bstep (se 1 (by rfl) ⟨2875454, by rfl⟩ : syracuseStep 3833939 = 5750909) B5750909
theorem B2555959 : Blo 2271435 2555959 := bstep (se 1 (by rfl) ⟨1916969, by rfl⟩ : syracuseStep 2555959 = 3833939) B3833939
theorem B3407945 : Blo 2271435 3407945 := bstep (se 2 (by rfl) ⟨1277979, by rfl⟩ : syracuseStep 3407945 = 2555959) B2555959
theorem B2271963 : Blo 2271435 2271963 := bstep (se 1 (by rfl) ⟨1703972, by rfl⟩ : syracuseStep 2271963 = 3407945) B3407945
theorem B4313189 : Blo 2271435 4313189 := bbase (se 4 (by rfl) ⟨404361, by rfl⟩ : syracuseStep 4313189 = 808723) (by norm_num)
theorem B11501837 : Blo 2271435 11501837 := bstep (se 3 (by rfl) ⟨2156594, by rfl⟩ : syracuseStep 11501837 = 4313189) B4313189
theorem B7667891 : Blo 2271435 7667891 := bstep (se 1 (by rfl) ⟨5750918, by rfl⟩ : syracuseStep 7667891 = 11501837) B11501837
theorem B5111927 : Blo 2271435 5111927 := bstep (se 1 (by rfl) ⟨3833945, by rfl⟩ : syracuseStep 5111927 = 7667891) B7667891
theorem B3407951 : Blo 2271435 3407951 := bstep (se 1 (by rfl) ⟨2555963, by rfl⟩ : syracuseStep 3407951 = 5111927) B5111927
theorem B2271967 : Blo 2271435 2271967 := bstep (se 1 (by rfl) ⟨1703975, by rfl⟩ : syracuseStep 2271967 = 3407951) B3407951
theorem B3407957 : Blo 2271435 3407957 := bbase (se 8 (by rfl) ⟨19968, by rfl⟩ : syracuseStep 3407957 = 39937) (by norm_num)
theorem B2271971 : Blo 2271435 2271971 := bstep (se 1 (by rfl) ⟨1703978, by rfl⟩ : syracuseStep 2271971 = 3407957) B3407957
theorem B74700629 : Blo 2271435 74700629 := bbase (se 9 (by rfl) ⟨218849, by rfl⟩ : syracuseStep 74700629 = 437699) (by norm_num)
theorem B49800419 : Blo 2271435 49800419 := bstep (se 1 (by rfl) ⟨37350314, by rfl⟩ : syracuseStep 49800419 = 74700629) B74700629
theorem B33200279 : Blo 2271435 33200279 := bstep (se 1 (by rfl) ⟨24900209, by rfl⟩ : syracuseStep 33200279 = 49800419) B49800419
theorem B22133519 : Blo 2271435 22133519 := bstep (se 1 (by rfl) ⟨16600139, by rfl⟩ : syracuseStep 22133519 = 33200279) B33200279
theorem B14755679 : Blo 2271435 14755679 := bstep (se 1 (by rfl) ⟨11066759, by rfl⟩ : syracuseStep 14755679 = 22133519) B22133519
theorem B9837119 : Blo 2271435 9837119 := bstep (se 1 (by rfl) ⟨7377839, by rfl⟩ : syracuseStep 9837119 = 14755679) B14755679
theorem B6558079 : Blo 2271435 6558079 := bstep (se 1 (by rfl) ⟨4918559, by rfl⟩ : syracuseStep 6558079 = 9837119) B9837119
theorem B8744105 : Blo 2271435 8744105 := bstep (se 2 (by rfl) ⟨3279039, by rfl⟩ : syracuseStep 8744105 = 6558079) B6558079
theorem B5829403 : Blo 2271435 5829403 := bstep (se 1 (by rfl) ⟨4372052, by rfl⟩ : syracuseStep 5829403 = 8744105) B8744105
theorem B7772537 : Blo 2271435 7772537 := bstep (se 2 (by rfl) ⟨2914701, by rfl⟩ : syracuseStep 7772537 = 5829403) B5829403
theorem B20726765 : Blo 2271435 20726765 := bstep (se 3 (by rfl) ⟨3886268, by rfl⟩ : syracuseStep 20726765 = 7772537) B7772537
theorem B13817843 : Blo 2271435 13817843 := bstep (se 1 (by rfl) ⟨10363382, by rfl⟩ : syracuseStep 13817843 = 20726765) B20726765
theorem B9211895 : Blo 2271435 9211895 := bstep (se 1 (by rfl) ⟨6908921, by rfl⟩ : syracuseStep 9211895 = 13817843) B13817843
theorem B6141263 : Blo 2271435 6141263 := bstep (se 1 (by rfl) ⟨4605947, by rfl⟩ : syracuseStep 6141263 = 9211895) B9211895
theorem B16376701 : Blo 2271435 16376701 := bstep (se 3 (by rfl) ⟨3070631, by rfl⟩ : syracuseStep 16376701 = 6141263) B6141263
theorem B21835601 : Blo 2271435 21835601 := bstep (se 2 (by rfl) ⟨8188350, by rfl⟩ : syracuseStep 21835601 = 16376701) B16376701
theorem B14557067 : Blo 2271435 14557067 := bstep (se 1 (by rfl) ⟨10917800, by rfl⟩ : syracuseStep 14557067 = 21835601) B21835601
theorem B9704711 : Blo 2271435 9704711 := bstep (se 1 (by rfl) ⟨7278533, by rfl⟩ : syracuseStep 9704711 = 14557067) B14557067
theorem B6469807 : Blo 2271435 6469807 := bstep (se 1 (by rfl) ⟨4852355, by rfl⟩ : syracuseStep 6469807 = 9704711) B9704711
theorem B8626409 : Blo 2271435 8626409 := bstep (se 2 (by rfl) ⟨3234903, by rfl⟩ : syracuseStep 8626409 = 6469807) B6469807
theorem B5750939 : Blo 2271435 5750939 := bstep (se 1 (by rfl) ⟨4313204, by rfl⟩ : syracuseStep 5750939 = 8626409) B8626409
theorem B3833959 : Blo 2271435 3833959 := bstep (se 1 (by rfl) ⟨2875469, by rfl⟩ : syracuseStep 3833959 = 5750939) B5750939
theorem B5111945 : Blo 2271435 5111945 := bstep (se 2 (by rfl) ⟨1916979, by rfl⟩ : syracuseStep 5111945 = 3833959) B3833959
theorem B3407963 : Blo 2271435 3407963 := bstep (se 1 (by rfl) ⟨2555972, by rfl⟩ : syracuseStep 3407963 = 5111945) B5111945
theorem B2271975 : Blo 2271435 2271975 := bstep (se 1 (by rfl) ⟨1703981, by rfl⟩ : syracuseStep 2271975 = 3407963) B3407963
theorem B2555977 : Blo 2271435 2555977 := bbase (se 2 (by rfl) ⟨958491, by rfl⟩ : syracuseStep 2555977 = 1916983) (by norm_num)
theorem B3407969 : Blo 2271435 3407969 := bstep (se 2 (by rfl) ⟨1277988, by rfl⟩ : syracuseStep 3407969 = 2555977) B2555977
theorem B2271979 : Blo 2271435 2271979 := bstep (se 1 (by rfl) ⟨1703984, by rfl⟩ : syracuseStep 2271979 = 3407969) B3407969
theorem B20726837 : Blo 2271435 20726837 := bbase (se 5 (by rfl) ⟨971570, by rfl⟩ : syracuseStep 20726837 = 1943141) (by norm_num)
theorem B13817891 : Blo 2271435 13817891 := bstep (se 1 (by rfl) ⟨10363418, by rfl⟩ : syracuseStep 13817891 = 20726837) B20726837
theorem B9211927 : Blo 2271435 9211927 := bstep (se 1 (by rfl) ⟨6908945, by rfl⟩ : syracuseStep 9211927 = 13817891) B13817891
theorem B12282569 : Blo 2271435 12282569 := bstep (se 2 (by rfl) ⟨4605963, by rfl⟩ : syracuseStep 12282569 = 9211927) B9211927
theorem B8188379 : Blo 2271435 8188379 := bstep (se 1 (by rfl) ⟨6141284, by rfl⟩ : syracuseStep 8188379 = 12282569) B12282569
theorem B5458919 : Blo 2271435 5458919 := bstep (se 1 (by rfl) ⟨4094189, by rfl⟩ : syracuseStep 5458919 = 8188379) B8188379
theorem B14557117 : Blo 2271435 14557117 := bstep (se 3 (by rfl) ⟨2729459, by rfl⟩ : syracuseStep 14557117 = 5458919) B5458919
theorem B19409489 : Blo 2271435 19409489 := bstep (se 2 (by rfl) ⟨7278558, by rfl⟩ : syracuseStep 19409489 = 14557117) B14557117
theorem B12939659 : Blo 2271435 12939659 := bstep (se 1 (by rfl) ⟨9704744, by rfl⟩ : syracuseStep 12939659 = 19409489) B19409489
theorem B8626439 : Blo 2271435 8626439 := bstep (se 1 (by rfl) ⟨6469829, by rfl⟩ : syracuseStep 8626439 = 12939659) B12939659
theorem B5750959 : Blo 2271435 5750959 := bstep (se 1 (by rfl) ⟨4313219, by rfl⟩ : syracuseStep 5750959 = 8626439) B8626439
theorem B7667945 : Blo 2271435 7667945 := bstep (se 2 (by rfl) ⟨2875479, by rfl⟩ : syracuseStep 7667945 = 5750959) B5750959
theorem B5111963 : Blo 2271435 5111963 := bstep (se 1 (by rfl) ⟨3833972, by rfl⟩ : syracuseStep 5111963 = 7667945) B7667945
theorem B3407975 : Blo 2271435 3407975 := bstep (se 1 (by rfl) ⟨2555981, by rfl⟩ : syracuseStep 3407975 = 5111963) B5111963
theorem B2271983 : Blo 2271435 2271983 := bstep (se 1 (by rfl) ⟨1703987, by rfl⟩ : syracuseStep 2271983 = 3407975) B3407975
theorem B3407981 : Blo 2271435 3407981 := bbase (se 3 (by rfl) ⟨638996, by rfl⟩ : syracuseStep 3407981 = 1277993) (by norm_num)
theorem B2271987 : Blo 2271435 2271987 := bstep (se 1 (by rfl) ⟨1703990, by rfl⟩ : syracuseStep 2271987 = 3407981) B3407981
theorem B5111981 : Blo 2271435 5111981 := bbase (se 3 (by rfl) ⟨958496, by rfl⟩ : syracuseStep 5111981 = 1916993) (by norm_num)
theorem B3407987 : Blo 2271435 3407987 := bstep (se 1 (by rfl) ⟨2555990, by rfl⟩ : syracuseStep 3407987 = 5111981) B5111981
theorem B2271991 : Blo 2271435 2271991 := bstep (se 1 (by rfl) ⟨1703993, by rfl⟩ : syracuseStep 2271991 = 3407987) B3407987
theorem B4605989 : Blo 2271435 4605989 := bbase (se 4 (by rfl) ⟨431811, by rfl⟩ : syracuseStep 4605989 = 863623) (by norm_num)
theorem B12282637 : Blo 2271435 12282637 := bstep (se 3 (by rfl) ⟨2302994, by rfl⟩ : syracuseStep 12282637 = 4605989) B4605989
theorem B16376849 : Blo 2271435 16376849 := bstep (se 2 (by rfl) ⟨6141318, by rfl⟩ : syracuseStep 16376849 = 12282637) B12282637
theorem B10917899 : Blo 2271435 10917899 := bstep (se 1 (by rfl) ⟨8188424, by rfl⟩ : syracuseStep 10917899 = 16376849) B16376849
theorem B7278599 : Blo 2271435 7278599 := bstep (se 1 (by rfl) ⟨5458949, by rfl⟩ : syracuseStep 7278599 = 10917899) B10917899
theorem B4852399 : Blo 2271435 4852399 := bstep (se 1 (by rfl) ⟨3639299, by rfl⟩ : syracuseStep 4852399 = 7278599) B7278599
theorem B6469865 : Blo 2271435 6469865 := bstep (se 2 (by rfl) ⟨2426199, by rfl⟩ : syracuseStep 6469865 = 4852399) B4852399
theorem B4313243 : Blo 2271435 4313243 := bstep (se 1 (by rfl) ⟨3234932, by rfl⟩ : syracuseStep 4313243 = 6469865) B6469865
theorem B2875495 : Blo 2271435 2875495 := bstep (se 1 (by rfl) ⟨2156621, by rfl⟩ : syracuseStep 2875495 = 4313243) B4313243
theorem B3833993 : Blo 2271435 3833993 := bstep (se 2 (by rfl) ⟨1437747, by rfl⟩ : syracuseStep 3833993 = 2875495) B2875495
theorem B2555995 : Blo 2271435 2555995 := bstep (se 1 (by rfl) ⟨1916996, by rfl⟩ : syracuseStep 2555995 = 3833993) B3833993
theorem B3407993 : Blo 2271435 3407993 := bstep (se 2 (by rfl) ⟨1277997, by rfl⟩ : syracuseStep 3407993 = 2555995) B2555995
theorem B2271995 : Blo 2271435 2271995 := bstep (se 1 (by rfl) ⟨1703996, by rfl⟩ : syracuseStep 2271995 = 3407993) B3407993
theorem B5458957 : Blo 2271435 5458957 := bbase (se 3 (by rfl) ⟨1023554, by rfl⟩ : syracuseStep 5458957 = 2047109) (by norm_num)
theorem B29114437 : Blo 2271435 29114437 := bstep (se 4 (by rfl) ⟨2729478, by rfl⟩ : syracuseStep 29114437 = 5458957) B5458957
theorem B38819249 : Blo 2271435 38819249 := bstep (se 2 (by rfl) ⟨14557218, by rfl⟩ : syracuseStep 38819249 = 29114437) B29114437
theorem B25879499 : Blo 2271435 25879499 := bstep (se 1 (by rfl) ⟨19409624, by rfl⟩ : syracuseStep 25879499 = 38819249) B38819249
theorem B17252999 : Blo 2271435 17252999 := bstep (se 1 (by rfl) ⟨12939749, by rfl⟩ : syracuseStep 17252999 = 25879499) B25879499
theorem B11501999 : Blo 2271435 11501999 := bstep (se 1 (by rfl) ⟨8626499, by rfl⟩ : syracuseStep 11501999 = 17252999) B17252999
theorem B7667999 : Blo 2271435 7667999 := bstep (se 1 (by rfl) ⟨5750999, by rfl⟩ : syracuseStep 7667999 = 11501999) B11501999
theorem B5111999 : Blo 2271435 5111999 := bstep (se 1 (by rfl) ⟨3833999, by rfl⟩ : syracuseStep 5111999 = 7667999) B7667999
theorem B3407999 : Blo 2271435 3407999 := bstep (se 1 (by rfl) ⟨2555999, by rfl⟩ : syracuseStep 3407999 = 5111999) B5111999
theorem B2271999 : Blo 2271435 2271999 := bstep (se 1 (by rfl) ⟨1703999, by rfl⟩ : syracuseStep 2271999 = 3407999) B3407999
theorem B3408005 : Blo 2271435 3408005 := bbase (se 4 (by rfl) ⟨319500, by rfl⟩ : syracuseStep 3408005 = 639001) (by norm_num)
theorem B2272003 : Blo 2271435 2272003 := bstep (se 1 (by rfl) ⟨1704002, by rfl⟩ : syracuseStep 2272003 = 3408005) B3408005
theorem B3834013 : Blo 2271435 3834013 := bbase (se 3 (by rfl) ⟨718877, by rfl⟩ : syracuseStep 3834013 = 1437755) (by norm_num)
theorem B5112017 : Blo 2271435 5112017 := bstep (se 2 (by rfl) ⟨1917006, by rfl⟩ : syracuseStep 5112017 = 3834013) B3834013
theorem B3408011 : Blo 2271435 3408011 := bstep (se 1 (by rfl) ⟨2556008, by rfl⟩ : syracuseStep 3408011 = 5112017) B5112017
theorem B2272007 : Blo 2271435 2272007 := bstep (se 1 (by rfl) ⟨1704005, by rfl⟩ : syracuseStep 2272007 = 3408011) B3408011
theorem B2556013 : Blo 2271435 2556013 := bbase (se 3 (by rfl) ⟨479252, by rfl⟩ : syracuseStep 2556013 = 958505) (by norm_num)
theorem B3408017 : Blo 2271435 3408017 := bstep (se 2 (by rfl) ⟨1278006, by rfl⟩ : syracuseStep 3408017 = 2556013) B2556013
theorem B2272011 : Blo 2271435 2272011 := bstep (se 1 (by rfl) ⟨1704008, by rfl⟩ : syracuseStep 2272011 = 3408017) B3408017
theorem B7668053 : Blo 2271435 7668053 := bbase (se 10 (by rfl) ⟨11232, by rfl⟩ : syracuseStep 7668053 = 22465) (by norm_num)
theorem B5112035 : Blo 2271435 5112035 := bstep (se 1 (by rfl) ⟨3834026, by rfl⟩ : syracuseStep 5112035 = 7668053) B7668053
theorem B3408023 : Blo 2271435 3408023 := bstep (se 1 (by rfl) ⟨2556017, by rfl⟩ : syracuseStep 3408023 = 5112035) B5112035
theorem B2272015 : Blo 2271435 2272015 := bstep (se 1 (by rfl) ⟨1704011, by rfl⟩ : syracuseStep 2272015 = 3408023) B3408023
theorem B3408029 : Blo 2271435 3408029 := bbase (se 3 (by rfl) ⟨639005, by rfl⟩ : syracuseStep 3408029 = 1278011) (by norm_num)
theorem B2272019 : Blo 2271435 2272019 := bstep (se 1 (by rfl) ⟨1704014, by rfl⟩ : syracuseStep 2272019 = 3408029) B3408029
theorem B5112053 : Blo 2271435 5112053 := bbase (se 5 (by rfl) ⟨239627, by rfl⟩ : syracuseStep 5112053 = 479255) (by norm_num)
theorem B3408035 : Blo 2271435 3408035 := bstep (se 1 (by rfl) ⟨2556026, by rfl⟩ : syracuseStep 3408035 = 5112053) B5112053
theorem B2272023 : Blo 2271435 2272023 := bstep (se 1 (by rfl) ⟨1704017, by rfl⟩ : syracuseStep 2272023 = 3408035) B3408035
theorem B4094269 : Blo 2271435 4094269 := bbase (se 3 (by rfl) ⟨767675, by rfl⟩ : syracuseStep 4094269 = 1535351) (by norm_num)
theorem B21836101 : Blo 2271435 21836101 := bstep (se 4 (by rfl) ⟨2047134, by rfl⟩ : syracuseStep 21836101 = 4094269) B4094269
theorem B29114801 : Blo 2271435 29114801 := bstep (se 2 (by rfl) ⟨10918050, by rfl⟩ : syracuseStep 29114801 = 21836101) B21836101
theorem B19409867 : Blo 2271435 19409867 := bstep (se 1 (by rfl) ⟨14557400, by rfl⟩ : syracuseStep 19409867 = 29114801) B29114801
theorem B12939911 : Blo 2271435 12939911 := bstep (se 1 (by rfl) ⟨9704933, by rfl⟩ : syracuseStep 12939911 = 19409867) B19409867
theorem B8626607 : Blo 2271435 8626607 := bstep (se 1 (by rfl) ⟨6469955, by rfl⟩ : syracuseStep 8626607 = 12939911) B12939911
theorem B5751071 : Blo 2271435 5751071 := bstep (se 1 (by rfl) ⟨4313303, by rfl⟩ : syracuseStep 5751071 = 8626607) B8626607
theorem B3834047 : Blo 2271435 3834047 := bstep (se 1 (by rfl) ⟨2875535, by rfl⟩ : syracuseStep 3834047 = 5751071) B5751071
theorem B2556031 : Blo 2271435 2556031 := bstep (se 1 (by rfl) ⟨1917023, by rfl⟩ : syracuseStep 2556031 = 3834047) B3834047
theorem B3408041 : Blo 2271435 3408041 := bstep (se 2 (by rfl) ⟨1278015, by rfl⟩ : syracuseStep 3408041 = 2556031) B2556031
theorem B2272027 : Blo 2271435 2272027 := bstep (se 1 (by rfl) ⟨1704020, by rfl⟩ : syracuseStep 2272027 = 3408041) B3408041
theorem B5533517 : Blo 2271435 5533517 := bbase (se 3 (by rfl) ⟨1037534, by rfl⟩ : syracuseStep 5533517 = 2075069) (by norm_num)
theorem B3689011 : Blo 2271435 3689011 := bstep (se 1 (by rfl) ⟨2766758, by rfl⟩ : syracuseStep 3689011 = 5533517) B5533517
theorem B4918681 : Blo 2271435 4918681 := bstep (se 2 (by rfl) ⟨1844505, by rfl⟩ : syracuseStep 4918681 = 3689011) B3689011
theorem B6558241 : Blo 2271435 6558241 := bstep (se 2 (by rfl) ⟨2459340, by rfl⟩ : syracuseStep 6558241 = 4918681) B4918681
theorem B8744321 : Blo 2271435 8744321 := bstep (se 2 (by rfl) ⟨3279120, by rfl⟩ : syracuseStep 8744321 = 6558241) B6558241
theorem B23318189 : Blo 2271435 23318189 := bstep (se 3 (by rfl) ⟨4372160, by rfl⟩ : syracuseStep 23318189 = 8744321) B8744321
theorem B15545459 : Blo 2271435 15545459 := bstep (se 1 (by rfl) ⟨11659094, by rfl⟩ : syracuseStep 15545459 = 23318189) B23318189
theorem B10363639 : Blo 2271435 10363639 := bstep (se 1 (by rfl) ⟨7772729, by rfl⟩ : syracuseStep 10363639 = 15545459) B15545459
theorem B13818185 : Blo 2271435 13818185 := bstep (se 2 (by rfl) ⟨5181819, by rfl⟩ : syracuseStep 13818185 = 10363639) B10363639
theorem B9212123 : Blo 2271435 9212123 := bstep (se 1 (by rfl) ⟨6909092, by rfl⟩ : syracuseStep 9212123 = 13818185) B13818185
theorem B6141415 : Blo 2271435 6141415 := bstep (se 1 (by rfl) ⟨4606061, by rfl⟩ : syracuseStep 6141415 = 9212123) B9212123
theorem B8188553 : Blo 2271435 8188553 := bstep (se 2 (by rfl) ⟨3070707, by rfl⟩ : syracuseStep 8188553 = 6141415) B6141415
theorem B5459035 : Blo 2271435 5459035 := bstep (se 1 (by rfl) ⟨4094276, by rfl⟩ : syracuseStep 5459035 = 8188553) B8188553
theorem B7278713 : Blo 2271435 7278713 := bstep (se 2 (by rfl) ⟨2729517, by rfl⟩ : syracuseStep 7278713 = 5459035) B5459035
theorem B4852475 : Blo 2271435 4852475 := bstep (se 1 (by rfl) ⟨3639356, by rfl⟩ : syracuseStep 4852475 = 7278713) B7278713
theorem B3234983 : Blo 2271435 3234983 := bstep (se 1 (by rfl) ⟨2426237, by rfl⟩ : syracuseStep 3234983 = 4852475) B4852475
theorem B8626621 : Blo 2271435 8626621 := bstep (se 3 (by rfl) ⟨1617491, by rfl⟩ : syracuseStep 8626621 = 3234983) B3234983
theorem B11502161 : Blo 2271435 11502161 := bstep (se 2 (by rfl) ⟨4313310, by rfl⟩ : syracuseStep 11502161 = 8626621) B8626621
theorem B7668107 : Blo 2271435 7668107 := bstep (se 1 (by rfl) ⟨5751080, by rfl⟩ : syracuseStep 7668107 = 11502161) B11502161
theorem B5112071 : Blo 2271435 5112071 := bstep (se 1 (by rfl) ⟨3834053, by rfl⟩ : syracuseStep 5112071 = 7668107) B7668107
theorem B3408047 : Blo 2271435 3408047 := bstep (se 1 (by rfl) ⟨2556035, by rfl⟩ : syracuseStep 3408047 = 5112071) B5112071
theorem B2272031 : Blo 2271435 2272031 := bstep (se 1 (by rfl) ⟨1704023, by rfl⟩ : syracuseStep 2272031 = 3408047) B3408047
theorem B3408053 : Blo 2271435 3408053 := bbase (se 5 (by rfl) ⟨159752, by rfl⟩ : syracuseStep 3408053 = 319505) (by norm_num)
theorem B2272035 : Blo 2271435 2272035 := bstep (se 1 (by rfl) ⟨1704026, by rfl⟩ : syracuseStep 2272035 = 3408053) B3408053
theorem B5751101 : Blo 2271435 5751101 := bbase (se 3 (by rfl) ⟨1078331, by rfl⟩ : syracuseStep 5751101 = 2156663) (by norm_num)
theorem B3834067 : Blo 2271435 3834067 := bstep (se 1 (by rfl) ⟨2875550, by rfl⟩ : syracuseStep 3834067 = 5751101) B5751101
theorem B5112089 : Blo 2271435 5112089 := bstep (se 2 (by rfl) ⟨1917033, by rfl⟩ : syracuseStep 5112089 = 3834067) B3834067
theorem B3408059 : Blo 2271435 3408059 := bstep (se 1 (by rfl) ⟨2556044, by rfl⟩ : syracuseStep 3408059 = 5112089) B5112089
theorem B2272039 : Blo 2271435 2272039 := bstep (se 1 (by rfl) ⟨1704029, by rfl⟩ : syracuseStep 2272039 = 3408059) B3408059
theorem B2556049 : Blo 2271435 2556049 := bbase (se 2 (by rfl) ⟨958518, by rfl⟩ : syracuseStep 2556049 = 1917037) (by norm_num)
theorem B3408065 : Blo 2271435 3408065 := bstep (se 2 (by rfl) ⟨1278024, by rfl⟩ : syracuseStep 3408065 = 2556049) B2556049
theorem B2272043 : Blo 2271435 2272043 := bstep (se 1 (by rfl) ⟨1704032, by rfl⟩ : syracuseStep 2272043 = 3408065) B3408065
theorem B4313341 : Blo 2271435 4313341 := bbase (se 3 (by rfl) ⟨808751, by rfl⟩ : syracuseStep 4313341 = 1617503) (by norm_num)
theorem B5751121 : Blo 2271435 5751121 := bstep (se 2 (by rfl) ⟨2156670, by rfl⟩ : syracuseStep 5751121 = 4313341) B4313341
theorem B7668161 : Blo 2271435 7668161 := bstep (se 2 (by rfl) ⟨2875560, by rfl⟩ : syracuseStep 7668161 = 5751121) B5751121
theorem B5112107 : Blo 2271435 5112107 := bstep (se 1 (by rfl) ⟨3834080, by rfl⟩ : syracuseStep 5112107 = 7668161) B7668161
theorem B3408071 : Blo 2271435 3408071 := bstep (se 1 (by rfl) ⟨2556053, by rfl⟩ : syracuseStep 3408071 = 5112107) B5112107
theorem B2272047 : Blo 2271435 2272047 := bstep (se 1 (by rfl) ⟨1704035, by rfl⟩ : syracuseStep 2272047 = 3408071) B3408071
theorem B3408077 : Blo 2271435 3408077 := bbase (se 3 (by rfl) ⟨639014, by rfl⟩ : syracuseStep 3408077 = 1278029) (by norm_num)
theorem B2272051 : Blo 2271435 2272051 := bstep (se 1 (by rfl) ⟨1704038, by rfl⟩ : syracuseStep 2272051 = 3408077) B3408077
theorem B5112125 : Blo 2271435 5112125 := bbase (se 3 (by rfl) ⟨958523, by rfl⟩ : syracuseStep 5112125 = 1917047) (by norm_num)
theorem B3408083 : Blo 2271435 3408083 := bstep (se 1 (by rfl) ⟨2556062, by rfl⟩ : syracuseStep 3408083 = 5112125) B5112125
theorem B2272055 : Blo 2271435 2272055 := bstep (se 1 (by rfl) ⟨1704041, by rfl⟩ : syracuseStep 2272055 = 3408083) B3408083
theorem B3834101 : Blo 2271435 3834101 := bbase (se 5 (by rfl) ⟨179723, by rfl⟩ : syracuseStep 3834101 = 359447) (by norm_num)
theorem B2556067 : Blo 2271435 2556067 := bstep (se 1 (by rfl) ⟨1917050, by rfl⟩ : syracuseStep 2556067 = 3834101) B3834101
theorem B3408089 : Blo 2271435 3408089 := bstep (se 2 (by rfl) ⟨1278033, by rfl⟩ : syracuseStep 3408089 = 2556067) B2556067
theorem B2272059 : Blo 2271435 2272059 := bstep (se 1 (by rfl) ⟨1704044, by rfl⟩ : syracuseStep 2272059 = 3408089) B3408089
theorem B17488885 : Blo 2271435 17488885 := bbase (se 5 (by rfl) ⟨819791, by rfl⟩ : syracuseStep 17488885 = 1639583) (by norm_num)
theorem B23318513 : Blo 2271435 23318513 := bstep (se 2 (by rfl) ⟨8744442, by rfl⟩ : syracuseStep 23318513 = 17488885) B17488885
theorem B15545675 : Blo 2271435 15545675 := bstep (se 1 (by rfl) ⟨11659256, by rfl⟩ : syracuseStep 15545675 = 23318513) B23318513
theorem B10363783 : Blo 2271435 10363783 := bstep (se 1 (by rfl) ⟨7772837, by rfl⟩ : syracuseStep 10363783 = 15545675) B15545675
theorem B13818377 : Blo 2271435 13818377 := bstep (se 2 (by rfl) ⟨5181891, by rfl⟩ : syracuseStep 13818377 = 10363783) B10363783
theorem B36849005 : Blo 2271435 36849005 := bstep (se 3 (by rfl) ⟨6909188, by rfl⟩ : syracuseStep 36849005 = 13818377) B13818377
theorem B24566003 : Blo 2271435 24566003 := bstep (se 1 (by rfl) ⟨18424502, by rfl⟩ : syracuseStep 24566003 = 36849005) B36849005
theorem B16377335 : Blo 2271435 16377335 := bstep (se 1 (by rfl) ⟨12283001, by rfl⟩ : syracuseStep 16377335 = 24566003) B24566003
theorem B10918223 : Blo 2271435 10918223 := bstep (se 1 (by rfl) ⟨8188667, by rfl⟩ : syracuseStep 10918223 = 16377335) B16377335
theorem B7278815 : Blo 2271435 7278815 := bstep (se 1 (by rfl) ⟨5459111, by rfl⟩ : syracuseStep 7278815 = 10918223) B10918223
theorem B4852543 : Blo 2271435 4852543 := bstep (se 1 (by rfl) ⟨3639407, by rfl⟩ : syracuseStep 4852543 = 7278815) B7278815
theorem B6470057 : Blo 2271435 6470057 := bstep (se 2 (by rfl) ⟨2426271, by rfl⟩ : syracuseStep 6470057 = 4852543) B4852543
theorem B17253485 : Blo 2271435 17253485 := bstep (se 3 (by rfl) ⟨3235028, by rfl⟩ : syracuseStep 17253485 = 6470057) B6470057
theorem B11502323 : Blo 2271435 11502323 := bstep (se 1 (by rfl) ⟨8626742, by rfl⟩ : syracuseStep 11502323 = 17253485) B17253485
theorem B7668215 : Blo 2271435 7668215 := bstep (se 1 (by rfl) ⟨5751161, by rfl⟩ : syracuseStep 7668215 = 11502323) B11502323
theorem B5112143 : Blo 2271435 5112143 := bstep (se 1 (by rfl) ⟨3834107, by rfl⟩ : syracuseStep 5112143 = 7668215) B7668215
theorem B3408095 : Blo 2271435 3408095 := bstep (se 1 (by rfl) ⟨2556071, by rfl⟩ : syracuseStep 3408095 = 5112143) B5112143
theorem B2272063 : Blo 2271435 2272063 := bstep (se 1 (by rfl) ⟨1704047, by rfl⟩ : syracuseStep 2272063 = 3408095) B3408095
theorem B3408101 : Blo 2271435 3408101 := bbase (se 4 (by rfl) ⟨319509, by rfl⟩ : syracuseStep 3408101 = 639019) (by norm_num)
theorem B2272067 : Blo 2271435 2272067 := bstep (se 1 (by rfl) ⟨1704050, by rfl⟩ : syracuseStep 2272067 = 3408101) B3408101
theorem B3639421 : Blo 2271435 3639421 := bbase (se 3 (by rfl) ⟨682391, by rfl⟩ : syracuseStep 3639421 = 1364783) (by norm_num)
theorem B4852561 : Blo 2271435 4852561 := bstep (se 2 (by rfl) ⟨1819710, by rfl⟩ : syracuseStep 4852561 = 3639421) B3639421
theorem B6470081 : Blo 2271435 6470081 := bstep (se 2 (by rfl) ⟨2426280, by rfl⟩ : syracuseStep 6470081 = 4852561) B4852561
theorem B4313387 : Blo 2271435 4313387 := bstep (se 1 (by rfl) ⟨3235040, by rfl⟩ : syracuseStep 4313387 = 6470081) B6470081
theorem B2875591 : Blo 2271435 2875591 := bstep (se 1 (by rfl) ⟨2156693, by rfl⟩ : syracuseStep 2875591 = 4313387) B4313387
theorem B3834121 : Blo 2271435 3834121 := bstep (se 2 (by rfl) ⟨1437795, by rfl⟩ : syracuseStep 3834121 = 2875591) B2875591
theorem B5112161 : Blo 2271435 5112161 := bstep (se 2 (by rfl) ⟨1917060, by rfl⟩ : syracuseStep 5112161 = 3834121) B3834121
theorem B3408107 : Blo 2271435 3408107 := bstep (se 1 (by rfl) ⟨2556080, by rfl⟩ : syracuseStep 3408107 = 5112161) B5112161
theorem B2272071 : Blo 2271435 2272071 := bstep (se 1 (by rfl) ⟨1704053, by rfl⟩ : syracuseStep 2272071 = 3408107) B3408107
theorem B2556085 : Blo 2271435 2556085 := bbase (se 5 (by rfl) ⟨119816, by rfl⟩ : syracuseStep 2556085 = 239633) (by norm_num)
theorem B3408113 : Blo 2271435 3408113 := bstep (se 2 (by rfl) ⟨1278042, by rfl⟩ : syracuseStep 3408113 = 2556085) B2556085
theorem B2272075 : Blo 2271435 2272075 := bstep (se 1 (by rfl) ⟨1704056, by rfl⟩ : syracuseStep 2272075 = 3408113) B3408113
theorem B2875601 : Blo 2271435 2875601 := bbase (se 2 (by rfl) ⟨1078350, by rfl⟩ : syracuseStep 2875601 = 2156701) (by norm_num)
theorem B7668269 : Blo 2271435 7668269 := bstep (se 3 (by rfl) ⟨1437800, by rfl⟩ : syracuseStep 7668269 = 2875601) B2875601
theorem B5112179 : Blo 2271435 5112179 := bstep (se 1 (by rfl) ⟨3834134, by rfl⟩ : syracuseStep 5112179 = 7668269) B7668269
theorem B3408119 : Blo 2271435 3408119 := bstep (se 1 (by rfl) ⟨2556089, by rfl⟩ : syracuseStep 3408119 = 5112179) B5112179
theorem B2272079 : Blo 2271435 2272079 := bstep (se 1 (by rfl) ⟨1704059, by rfl⟩ : syracuseStep 2272079 = 3408119) B3408119
theorem B3408125 : Blo 2271435 3408125 := bbase (se 3 (by rfl) ⟨639023, by rfl⟩ : syracuseStep 3408125 = 1278047) (by norm_num)
theorem B2272083 : Blo 2271435 2272083 := bstep (se 1 (by rfl) ⟨1704062, by rfl⟩ : syracuseStep 2272083 = 3408125) B3408125
theorem B5112197 : Blo 2271435 5112197 := bbase (se 4 (by rfl) ⟨479268, by rfl⟩ : syracuseStep 5112197 = 958537) (by norm_num)
theorem B3408131 : Blo 2271435 3408131 := bstep (se 1 (by rfl) ⟨2556098, by rfl⟩ : syracuseStep 3408131 = 5112197) B5112197
theorem B2272087 : Blo 2271435 2272087 := bstep (se 1 (by rfl) ⟨1704065, by rfl⟩ : syracuseStep 2272087 = 3408131) B3408131
theorem B3235069 : Blo 2271435 3235069 := bbase (se 3 (by rfl) ⟨606575, by rfl⟩ : syracuseStep 3235069 = 1213151) (by norm_num)
theorem B4313425 : Blo 2271435 4313425 := bstep (se 2 (by rfl) ⟨1617534, by rfl⟩ : syracuseStep 4313425 = 3235069) B3235069
theorem B5751233 : Blo 2271435 5751233 := bstep (se 2 (by rfl) ⟨2156712, by rfl⟩ : syracuseStep 5751233 = 4313425) B4313425
theorem B3834155 : Blo 2271435 3834155 := bstep (se 1 (by rfl) ⟨2875616, by rfl⟩ : syracuseStep 3834155 = 5751233) B5751233
theorem B2556103 : Blo 2271435 2556103 := bstep (se 1 (by rfl) ⟨1917077, by rfl⟩ : syracuseStep 2556103 = 3834155) B3834155
theorem B3408137 : Blo 2271435 3408137 := bstep (se 2 (by rfl) ⟨1278051, by rfl⟩ : syracuseStep 3408137 = 2556103) B2556103
theorem B2272091 : Blo 2271435 2272091 := bstep (se 1 (by rfl) ⟨1704068, by rfl⟩ : syracuseStep 2272091 = 3408137) B3408137
theorem B11502485 : Blo 2271435 11502485 := bbase (se 6 (by rfl) ⟨269589, by rfl⟩ : syracuseStep 11502485 = 539179) (by norm_num)
theorem B7668323 : Blo 2271435 7668323 := bstep (se 1 (by rfl) ⟨5751242, by rfl⟩ : syracuseStep 7668323 = 11502485) B11502485
theorem B5112215 : Blo 2271435 5112215 := bstep (se 1 (by rfl) ⟨3834161, by rfl⟩ : syracuseStep 5112215 = 7668323) B7668323
theorem B3408143 : Blo 2271435 3408143 := bstep (se 1 (by rfl) ⟨2556107, by rfl⟩ : syracuseStep 3408143 = 5112215) B5112215
theorem B2272095 : Blo 2271435 2272095 := bstep (se 1 (by rfl) ⟨1704071, by rfl⟩ : syracuseStep 2272095 = 3408143) B3408143
theorem B3408149 : Blo 2271435 3408149 := bbase (se 6 (by rfl) ⟨79878, by rfl⟩ : syracuseStep 3408149 = 159757) (by norm_num)
theorem B2272099 : Blo 2271435 2272099 := bstep (se 1 (by rfl) ⟨1704074, by rfl⟩ : syracuseStep 2272099 = 3408149) B3408149
theorem B3323965 : Blo 2271435 3323965 := bbase (se 3 (by rfl) ⟨623243, by rfl⟩ : syracuseStep 3323965 = 1246487) (by norm_num)
theorem B4431953 : Blo 2271435 4431953 := bstep (se 2 (by rfl) ⟨1661982, by rfl⟩ : syracuseStep 4431953 = 3323965) B3323965
theorem B11818541 : Blo 2271435 11818541 := bstep (se 3 (by rfl) ⟨2215976, by rfl⟩ : syracuseStep 11818541 = 4431953) B4431953
theorem B7879027 : Blo 2271435 7879027 := bstep (se 1 (by rfl) ⟨5909270, by rfl⟩ : syracuseStep 7879027 = 11818541) B11818541
theorem B10505369 : Blo 2271435 10505369 := bstep (se 2 (by rfl) ⟨3939513, by rfl⟩ : syracuseStep 10505369 = 7879027) B7879027
theorem B7003579 : Blo 2271435 7003579 := bstep (se 1 (by rfl) ⟨5252684, by rfl⟩ : syracuseStep 7003579 = 10505369) B10505369
theorem B9338105 : Blo 2271435 9338105 := bstep (se 2 (by rfl) ⟨3501789, by rfl⟩ : syracuseStep 9338105 = 7003579) B7003579
theorem B6225403 : Blo 2271435 6225403 := bstep (se 1 (by rfl) ⟨4669052, by rfl⟩ : syracuseStep 6225403 = 9338105) B9338105
theorem B8300537 : Blo 2271435 8300537 := bstep (se 2 (by rfl) ⟨3112701, by rfl⟩ : syracuseStep 8300537 = 6225403) B6225403
theorem B5533691 : Blo 2271435 5533691 := bstep (se 1 (by rfl) ⟨4150268, by rfl⟩ : syracuseStep 5533691 = 8300537) B8300537
theorem B14756509 : Blo 2271435 14756509 := bstep (se 3 (by rfl) ⟨2766845, by rfl⟩ : syracuseStep 14756509 = 5533691) B5533691
theorem B19675345 : Blo 2271435 19675345 := bstep (se 2 (by rfl) ⟨7378254, by rfl⟩ : syracuseStep 19675345 = 14756509) B14756509
theorem B26233793 : Blo 2271435 26233793 := bstep (se 2 (by rfl) ⟨9837672, by rfl⟩ : syracuseStep 26233793 = 19675345) B19675345
theorem B17489195 : Blo 2271435 17489195 := bstep (se 1 (by rfl) ⟨13116896, by rfl⟩ : syracuseStep 17489195 = 26233793) B26233793
theorem B11659463 : Blo 2271435 11659463 := bstep (se 1 (by rfl) ⟨8744597, by rfl⟩ : syracuseStep 11659463 = 17489195) B17489195
theorem B7772975 : Blo 2271435 7772975 := bstep (se 1 (by rfl) ⟨5829731, by rfl⟩ : syracuseStep 7772975 = 11659463) B11659463
theorem B5181983 : Blo 2271435 5181983 := bstep (se 1 (by rfl) ⟨3886487, by rfl⟩ : syracuseStep 5181983 = 7772975) B7772975
theorem B3454655 : Blo 2271435 3454655 := bstep (se 1 (by rfl) ⟨2590991, by rfl⟩ : syracuseStep 3454655 = 5181983) B5181983
theorem B36849653 : Blo 2271435 36849653 := bstep (se 5 (by rfl) ⟨1727327, by rfl⟩ : syracuseStep 36849653 = 3454655) B3454655
theorem B24566435 : Blo 2271435 24566435 := bstep (se 1 (by rfl) ⟨18424826, by rfl⟩ : syracuseStep 24566435 = 36849653) B36849653
theorem B16377623 : Blo 2271435 16377623 := bstep (se 1 (by rfl) ⟨12283217, by rfl⟩ : syracuseStep 16377623 = 24566435) B24566435
theorem B10918415 : Blo 2271435 10918415 := bstep (se 1 (by rfl) ⟨8188811, by rfl⟩ : syracuseStep 10918415 = 16377623) B16377623
theorem B29115773 : Blo 2271435 29115773 := bstep (se 3 (by rfl) ⟨5459207, by rfl⟩ : syracuseStep 29115773 = 10918415) B10918415
theorem B19410515 : Blo 2271435 19410515 := bstep (se 1 (by rfl) ⟨14557886, by rfl⟩ : syracuseStep 19410515 = 29115773) B29115773
theorem B12940343 : Blo 2271435 12940343 := bstep (se 1 (by rfl) ⟨9705257, by rfl⟩ : syracuseStep 12940343 = 19410515) B19410515
theorem B8626895 : Blo 2271435 8626895 := bstep (se 1 (by rfl) ⟨6470171, by rfl⟩ : syracuseStep 8626895 = 12940343) B12940343
theorem B5751263 : Blo 2271435 5751263 := bstep (se 1 (by rfl) ⟨4313447, by rfl⟩ : syracuseStep 5751263 = 8626895) B8626895
theorem B3834175 : Blo 2271435 3834175 := bstep (se 1 (by rfl) ⟨2875631, by rfl⟩ : syracuseStep 3834175 = 5751263) B5751263
theorem B5112233 : Blo 2271435 5112233 := bstep (se 2 (by rfl) ⟨1917087, by rfl⟩ : syracuseStep 5112233 = 3834175) B3834175
theorem B3408155 : Blo 2271435 3408155 := bstep (se 1 (by rfl) ⟨2556116, by rfl⟩ : syracuseStep 3408155 = 5112233) B5112233
theorem B2272103 : Blo 2271435 2272103 := bstep (se 1 (by rfl) ⟨1704077, by rfl⟩ : syracuseStep 2272103 = 3408155) B3408155
theorem B2556121 : Blo 2271435 2556121 := bbase (se 2 (by rfl) ⟨958545, by rfl⟩ : syracuseStep 2556121 = 1917091) (by norm_num)
theorem B3408161 : Blo 2271435 3408161 := bstep (se 2 (by rfl) ⟨1278060, by rfl⟩ : syracuseStep 3408161 = 2556121) B2556121
theorem B2272107 : Blo 2271435 2272107 := bstep (se 1 (by rfl) ⟨1704080, by rfl⟩ : syracuseStep 2272107 = 3408161) B3408161
theorem B3639485 : Blo 2271435 3639485 := bbase (se 3 (by rfl) ⟨682403, by rfl⟩ : syracuseStep 3639485 = 1364807) (by norm_num)
theorem B2426323 : Blo 2271435 2426323 := bstep (se 1 (by rfl) ⟨1819742, by rfl⟩ : syracuseStep 2426323 = 3639485) B3639485
theorem B3235097 : Blo 2271435 3235097 := bstep (se 2 (by rfl) ⟨1213161, by rfl⟩ : syracuseStep 3235097 = 2426323) B2426323
theorem B8626925 : Blo 2271435 8626925 := bstep (se 3 (by rfl) ⟨1617548, by rfl⟩ : syracuseStep 8626925 = 3235097) B3235097
theorem B5751283 : Blo 2271435 5751283 := bstep (se 1 (by rfl) ⟨4313462, by rfl⟩ : syracuseStep 5751283 = 8626925) B8626925
theorem B7668377 : Blo 2271435 7668377 := bstep (se 2 (by rfl) ⟨2875641, by rfl⟩ : syracuseStep 7668377 = 5751283) B5751283
theorem B5112251 : Blo 2271435 5112251 := bstep (se 1 (by rfl) ⟨3834188, by rfl⟩ : syracuseStep 5112251 = 7668377) B7668377
theorem B3408167 : Blo 2271435 3408167 := bstep (se 1 (by rfl) ⟨2556125, by rfl⟩ : syracuseStep 3408167 = 5112251) B5112251
theorem B2272111 : Blo 2271435 2272111 := bstep (se 1 (by rfl) ⟨1704083, by rfl⟩ : syracuseStep 2272111 = 3408167) B3408167
theorem B3408173 : Blo 2271435 3408173 := bbase (se 3 (by rfl) ⟨639032, by rfl⟩ : syracuseStep 3408173 = 1278065) (by norm_num)
theorem B2272115 : Blo 2271435 2272115 := bstep (se 1 (by rfl) ⟨1704086, by rfl⟩ : syracuseStep 2272115 = 3408173) B3408173
theorem B5112269 : Blo 2271435 5112269 := bbase (se 3 (by rfl) ⟨958550, by rfl⟩ : syracuseStep 5112269 = 1917101) (by norm_num)
theorem B3408179 : Blo 2271435 3408179 := bstep (se 1 (by rfl) ⟨2556134, by rfl⟩ : syracuseStep 3408179 = 5112269) B5112269
theorem B2272119 : Blo 2271435 2272119 := bstep (se 1 (by rfl) ⟨1704089, by rfl⟩ : syracuseStep 2272119 = 3408179) B3408179
theorem B2875657 : Blo 2271435 2875657 := bbase (se 2 (by rfl) ⟨1078371, by rfl⟩ : syracuseStep 2875657 = 2156743) (by norm_num)
theorem B3834209 : Blo 2271435 3834209 := bstep (se 2 (by rfl) ⟨1437828, by rfl⟩ : syracuseStep 3834209 = 2875657) B2875657
theorem B2556139 : Blo 2271435 2556139 := bstep (se 1 (by rfl) ⟨1917104, by rfl⟩ : syracuseStep 2556139 = 3834209) B3834209
theorem B3408185 : Blo 2271435 3408185 := bstep (se 2 (by rfl) ⟨1278069, by rfl⟩ : syracuseStep 3408185 = 2556139) B2556139
theorem B2272123 : Blo 2271435 2272123 := bstep (se 1 (by rfl) ⟨1704092, by rfl⟩ : syracuseStep 2272123 = 3408185) B3408185
theorem B6558517 : Blo 2271435 6558517 := bbase (se 5 (by rfl) ⟨307430, by rfl⟩ : syracuseStep 6558517 = 614861) (by norm_num)
theorem B8744689 : Blo 2271435 8744689 := bstep (se 2 (by rfl) ⟨3279258, by rfl⟩ : syracuseStep 8744689 = 6558517) B6558517
theorem B11659585 : Blo 2271435 11659585 := bstep (se 2 (by rfl) ⟨4372344, by rfl⟩ : syracuseStep 11659585 = 8744689) B8744689
theorem B15546113 : Blo 2271435 15546113 := bstep (se 2 (by rfl) ⟨5829792, by rfl⟩ : syracuseStep 15546113 = 11659585) B11659585
theorem B10364075 : Blo 2271435 10364075 := bstep (se 1 (by rfl) ⟨7773056, by rfl⟩ : syracuseStep 10364075 = 15546113) B15546113
theorem B6909383 : Blo 2271435 6909383 := bstep (se 1 (by rfl) ⟨5182037, by rfl⟩ : syracuseStep 6909383 = 10364075) B10364075
theorem B4606255 : Blo 2271435 4606255 := bstep (se 1 (by rfl) ⟨3454691, by rfl⟩ : syracuseStep 4606255 = 6909383) B6909383
theorem B6141673 : Blo 2271435 6141673 := bstep (se 2 (by rfl) ⟨2303127, by rfl⟩ : syracuseStep 6141673 = 4606255) B4606255
theorem B32755589 : Blo 2271435 32755589 := bstep (se 4 (by rfl) ⟨3070836, by rfl⟩ : syracuseStep 32755589 = 6141673) B6141673
theorem B21837059 : Blo 2271435 21837059 := bstep (se 1 (by rfl) ⟨16377794, by rfl⟩ : syracuseStep 21837059 = 32755589) B32755589
theorem B14558039 : Blo 2271435 14558039 := bstep (se 1 (by rfl) ⟨10918529, by rfl⟩ : syracuseStep 14558039 = 21837059) B21837059
theorem B9705359 : Blo 2271435 9705359 := bstep (se 1 (by rfl) ⟨7279019, by rfl⟩ : syracuseStep 9705359 = 14558039) B14558039
theorem B25880957 : Blo 2271435 25880957 := bstep (se 3 (by rfl) ⟨4852679, by rfl⟩ : syracuseStep 25880957 = 9705359) B9705359
theorem B17253971 : Blo 2271435 17253971 := bstep (se 1 (by rfl) ⟨12940478, by rfl⟩ : syracuseStep 17253971 = 25880957) B25880957
theorem B11502647 : Blo 2271435 11502647 := bstep (se 1 (by rfl) ⟨8626985, by rfl⟩ : syracuseStep 11502647 = 17253971) B17253971
theorem B7668431 : Blo 2271435 7668431 := bstep (se 1 (by rfl) ⟨5751323, by rfl⟩ : syracuseStep 7668431 = 11502647) B11502647
theorem B5112287 : Blo 2271435 5112287 := bstep (se 1 (by rfl) ⟨3834215, by rfl⟩ : syracuseStep 5112287 = 7668431) B7668431
theorem B3408191 : Blo 2271435 3408191 := bstep (se 1 (by rfl) ⟨2556143, by rfl⟩ : syracuseStep 3408191 = 5112287) B5112287
theorem B2272127 : Blo 2271435 2272127 := bstep (se 1 (by rfl) ⟨1704095, by rfl⟩ : syracuseStep 2272127 = 3408191) B3408191
theorem B3408197 : Blo 2271435 3408197 := bbase (se 4 (by rfl) ⟨319518, by rfl⟩ : syracuseStep 3408197 = 639037) (by norm_num)
theorem B2272131 : Blo 2271435 2272131 := bstep (se 1 (by rfl) ⟨1704098, by rfl⟩ : syracuseStep 2272131 = 3408197) B3408197
theorem B3834229 : Blo 2271435 3834229 := bbase (se 5 (by rfl) ⟨179729, by rfl⟩ : syracuseStep 3834229 = 359459) (by norm_num)
theorem B5112305 : Blo 2271435 5112305 := bstep (se 2 (by rfl) ⟨1917114, by rfl⟩ : syracuseStep 5112305 = 3834229) B3834229
theorem B3408203 : Blo 2271435 3408203 := bstep (se 1 (by rfl) ⟨2556152, by rfl⟩ : syracuseStep 3408203 = 5112305) B5112305
theorem B2272135 : Blo 2271435 2272135 := bstep (se 1 (by rfl) ⟨1704101, by rfl⟩ : syracuseStep 2272135 = 3408203) B3408203
theorem B2556157 : Blo 2271435 2556157 := bbase (se 3 (by rfl) ⟨479279, by rfl⟩ : syracuseStep 2556157 = 958559) (by norm_num)
theorem B3408209 : Blo 2271435 3408209 := bstep (se 2 (by rfl) ⟨1278078, by rfl⟩ : syracuseStep 3408209 = 2556157) B2556157
theorem B2272139 : Blo 2271435 2272139 := bstep (se 1 (by rfl) ⟨1704104, by rfl⟩ : syracuseStep 2272139 = 3408209) B3408209
theorem B7668485 : Blo 2271435 7668485 := bbase (se 4 (by rfl) ⟨718920, by rfl⟩ : syracuseStep 7668485 = 1437841) (by norm_num)
theorem B5112323 : Blo 2271435 5112323 := bstep (se 1 (by rfl) ⟨3834242, by rfl⟩ : syracuseStep 5112323 = 7668485) B7668485
theorem B3408215 : Blo 2271435 3408215 := bstep (se 1 (by rfl) ⟨2556161, by rfl⟩ : syracuseStep 3408215 = 5112323) B5112323
theorem B2272143 : Blo 2271435 2272143 := bstep (se 1 (by rfl) ⟨1704107, by rfl⟩ : syracuseStep 2272143 = 3408215) B3408215
theorem B3408221 : Blo 2271435 3408221 := bbase (se 3 (by rfl) ⟨639041, by rfl⟩ : syracuseStep 3408221 = 1278083) (by norm_num)
theorem B2272147 : Blo 2271435 2272147 := bstep (se 1 (by rfl) ⟨1704110, by rfl⟩ : syracuseStep 2272147 = 3408221) B3408221
theorem B5112341 : Blo 2271435 5112341 := bbase (se 6 (by rfl) ⟨119820, by rfl⟩ : syracuseStep 5112341 = 239641) (by norm_num)
theorem B3408227 : Blo 2271435 3408227 := bstep (se 1 (by rfl) ⟨2556170, by rfl⟩ : syracuseStep 3408227 = 5112341) B5112341
theorem B2272151 : Blo 2271435 2272151 := bstep (se 1 (by rfl) ⟨1704113, by rfl⟩ : syracuseStep 2272151 = 3408227) B3408227
theorem B8627093 : Blo 2271435 8627093 := bbase (se 6 (by rfl) ⟨202197, by rfl⟩ : syracuseStep 8627093 = 404395) (by norm_num)
theorem B5751395 : Blo 2271435 5751395 := bstep (se 1 (by rfl) ⟨4313546, by rfl⟩ : syracuseStep 5751395 = 8627093) B8627093
theorem B3834263 : Blo 2271435 3834263 := bstep (se 1 (by rfl) ⟨2875697, by rfl⟩ : syracuseStep 3834263 = 5751395) B5751395
theorem B2556175 : Blo 2271435 2556175 := bstep (se 1 (by rfl) ⟨1917131, by rfl⟩ : syracuseStep 2556175 = 3834263) B3834263
theorem B3408233 : Blo 2271435 3408233 := bstep (se 2 (by rfl) ⟨1278087, by rfl⟩ : syracuseStep 3408233 = 2556175) B2556175
theorem B2272155 : Blo 2271435 2272155 := bstep (se 1 (by rfl) ⟨1704116, by rfl⟩ : syracuseStep 2272155 = 3408233) B3408233
theorem B12940661 : Blo 2271435 12940661 := bbase (se 5 (by rfl) ⟨606593, by rfl⟩ : syracuseStep 12940661 = 1213187) (by norm_num)
theorem B8627107 : Blo 2271435 8627107 := bstep (se 1 (by rfl) ⟨6470330, by rfl⟩ : syracuseStep 8627107 = 12940661) B12940661
theorem B11502809 : Blo 2271435 11502809 := bstep (se 2 (by rfl) ⟨4313553, by rfl⟩ : syracuseStep 11502809 = 8627107) B8627107
theorem B7668539 : Blo 2271435 7668539 := bstep (se 1 (by rfl) ⟨5751404, by rfl⟩ : syracuseStep 7668539 = 11502809) B11502809
theorem B5112359 : Blo 2271435 5112359 := bstep (se 1 (by rfl) ⟨3834269, by rfl⟩ : syracuseStep 5112359 = 7668539) B7668539
theorem B3408239 : Blo 2271435 3408239 := bstep (se 1 (by rfl) ⟨2556179, by rfl⟩ : syracuseStep 3408239 = 5112359) B5112359
theorem B2272159 : Blo 2271435 2272159 := bstep (se 1 (by rfl) ⟨1704119, by rfl⟩ : syracuseStep 2272159 = 3408239) B3408239
theorem B3408245 : Blo 2271435 3408245 := bbase (se 5 (by rfl) ⟨159761, by rfl⟩ : syracuseStep 3408245 = 319523) (by norm_num)
theorem B2272163 : Blo 2271435 2272163 := bstep (se 1 (by rfl) ⟨1704122, by rfl⟩ : syracuseStep 2272163 = 3408245) B3408245
theorem B8189045 : Blo 2271435 8189045 := bbase (se 5 (by rfl) ⟨383861, by rfl⟩ : syracuseStep 8189045 = 767723) (by norm_num)
theorem B5459363 : Blo 2271435 5459363 := bstep (se 1 (by rfl) ⟨4094522, by rfl⟩ : syracuseStep 5459363 = 8189045) B8189045
theorem B3639575 : Blo 2271435 3639575 := bstep (se 1 (by rfl) ⟨2729681, by rfl⟩ : syracuseStep 3639575 = 5459363) B5459363
theorem B2426383 : Blo 2271435 2426383 := bstep (se 1 (by rfl) ⟨1819787, by rfl⟩ : syracuseStep 2426383 = 3639575) B3639575
theorem B3235177 : Blo 2271435 3235177 := bstep (se 2 (by rfl) ⟨1213191, by rfl⟩ : syracuseStep 3235177 = 2426383) B2426383
theorem B4313569 : Blo 2271435 4313569 := bstep (se 2 (by rfl) ⟨1617588, by rfl⟩ : syracuseStep 4313569 = 3235177) B3235177
theorem B5751425 : Blo 2271435 5751425 := bstep (se 2 (by rfl) ⟨2156784, by rfl⟩ : syracuseStep 5751425 = 4313569) B4313569
theorem B3834283 : Blo 2271435 3834283 := bstep (se 1 (by rfl) ⟨2875712, by rfl⟩ : syracuseStep 3834283 = 5751425) B5751425
theorem B5112377 : Blo 2271435 5112377 := bstep (se 2 (by rfl) ⟨1917141, by rfl⟩ : syracuseStep 5112377 = 3834283) B3834283
theorem B3408251 : Blo 2271435 3408251 := bstep (se 1 (by rfl) ⟨2556188, by rfl⟩ : syracuseStep 3408251 = 5112377) B5112377
theorem B2272167 : Blo 2271435 2272167 := bstep (se 1 (by rfl) ⟨1704125, by rfl⟩ : syracuseStep 2272167 = 3408251) B3408251
theorem B2556193 : Blo 2271435 2556193 := bbase (se 2 (by rfl) ⟨958572, by rfl⟩ : syracuseStep 2556193 = 1917145) (by norm_num)
theorem B3408257 : Blo 2271435 3408257 := bstep (se 2 (by rfl) ⟨1278096, by rfl⟩ : syracuseStep 3408257 = 2556193) B2556193
theorem B2272171 : Blo 2271435 2272171 := bstep (se 1 (by rfl) ⟨1704128, by rfl⟩ : syracuseStep 2272171 = 3408257) B3408257
theorem B5751445 : Blo 2271435 5751445 := bbase (se 6 (by rfl) ⟨134799, by rfl⟩ : syracuseStep 5751445 = 269599) (by norm_num)
theorem B7668593 : Blo 2271435 7668593 := bstep (se 2 (by rfl) ⟨2875722, by rfl⟩ : syracuseStep 7668593 = 5751445) B5751445
theorem B5112395 : Blo 2271435 5112395 := bstep (se 1 (by rfl) ⟨3834296, by rfl⟩ : syracuseStep 5112395 = 7668593) B7668593
theorem B3408263 : Blo 2271435 3408263 := bstep (se 1 (by rfl) ⟨2556197, by rfl⟩ : syracuseStep 3408263 = 5112395) B5112395
theorem B2272175 : Blo 2271435 2272175 := bstep (se 1 (by rfl) ⟨1704131, by rfl⟩ : syracuseStep 2272175 = 3408263) B3408263
theorem B3408269 : Blo 2271435 3408269 := bbase (se 3 (by rfl) ⟨639050, by rfl⟩ : syracuseStep 3408269 = 1278101) (by norm_num)
theorem B2272179 : Blo 2271435 2272179 := bstep (se 1 (by rfl) ⟨1704134, by rfl⟩ : syracuseStep 2272179 = 3408269) B3408269
theorem B5112413 : Blo 2271435 5112413 := bbase (se 3 (by rfl) ⟨958577, by rfl⟩ : syracuseStep 5112413 = 1917155) (by norm_num)
theorem B3408275 : Blo 2271435 3408275 := bstep (se 1 (by rfl) ⟨2556206, by rfl⟩ : syracuseStep 3408275 = 5112413) B5112413
theorem B2272183 : Blo 2271435 2272183 := bstep (se 1 (by rfl) ⟨1704137, by rfl⟩ : syracuseStep 2272183 = 3408275) B3408275
theorem B3834317 : Blo 2271435 3834317 := bbase (se 3 (by rfl) ⟨718934, by rfl⟩ : syracuseStep 3834317 = 1437869) (by norm_num)
theorem B2556211 : Blo 2271435 2556211 := bstep (se 1 (by rfl) ⟨1917158, by rfl⟩ : syracuseStep 2556211 = 3834317) B3834317
theorem B3408281 : Blo 2271435 3408281 := bstep (se 2 (by rfl) ⟨1278105, by rfl⟩ : syracuseStep 3408281 = 2556211) B2556211
theorem B2272187 : Blo 2271435 2272187 := bstep (se 1 (by rfl) ⟨1704140, by rfl⟩ : syracuseStep 2272187 = 3408281) B3408281
theorem B10918837 : Blo 2271435 10918837 := bbase (se 5 (by rfl) ⟨511820, by rfl⟩ : syracuseStep 10918837 = 1023641) (by norm_num)
theorem B14558449 : Blo 2271435 14558449 := bstep (se 2 (by rfl) ⟨5459418, by rfl⟩ : syracuseStep 14558449 = 10918837) B10918837
theorem B19411265 : Blo 2271435 19411265 := bstep (se 2 (by rfl) ⟨7279224, by rfl⟩ : syracuseStep 19411265 = 14558449) B14558449
theorem B12940843 : Blo 2271435 12940843 := bstep (se 1 (by rfl) ⟨9705632, by rfl⟩ : syracuseStep 12940843 = 19411265) B19411265
theorem B17254457 : Blo 2271435 17254457 := bstep (se 2 (by rfl) ⟨6470421, by rfl⟩ : syracuseStep 17254457 = 12940843) B12940843
theorem B11502971 : Blo 2271435 11502971 := bstep (se 1 (by rfl) ⟨8627228, by rfl⟩ : syracuseStep 11502971 = 17254457) B17254457
theorem B7668647 : Blo 2271435 7668647 := bstep (se 1 (by rfl) ⟨5751485, by rfl⟩ : syracuseStep 7668647 = 11502971) B11502971
theorem B5112431 : Blo 2271435 5112431 := bstep (se 1 (by rfl) ⟨3834323, by rfl⟩ : syracuseStep 5112431 = 7668647) B7668647
theorem B3408287 : Blo 2271435 3408287 := bstep (se 1 (by rfl) ⟨2556215, by rfl⟩ : syracuseStep 3408287 = 5112431) B5112431
theorem B2272191 : Blo 2271435 2272191 := bstep (se 1 (by rfl) ⟨1704143, by rfl⟩ : syracuseStep 2272191 = 3408287) B3408287
theorem B3408293 : Blo 2271435 3408293 := bbase (se 4 (by rfl) ⟨319527, by rfl⟩ : syracuseStep 3408293 = 639055) (by norm_num)
theorem B2272195 : Blo 2271435 2272195 := bstep (se 1 (by rfl) ⟨1704146, by rfl⟩ : syracuseStep 2272195 = 3408293) B3408293
theorem B2875753 : Blo 2271435 2875753 := bbase (se 2 (by rfl) ⟨1078407, by rfl⟩ : syracuseStep 2875753 = 2156815) (by norm_num)
theorem B3834337 : Blo 2271435 3834337 := bstep (se 2 (by rfl) ⟨1437876, by rfl⟩ : syracuseStep 3834337 = 2875753) B2875753
theorem B5112449 : Blo 2271435 5112449 := bstep (se 2 (by rfl) ⟨1917168, by rfl⟩ : syracuseStep 5112449 = 3834337) B3834337
theorem B3408299 : Blo 2271435 3408299 := bstep (se 1 (by rfl) ⟨2556224, by rfl⟩ : syracuseStep 3408299 = 5112449) B5112449
theorem B2272199 : Blo 2271435 2272199 := bstep (se 1 (by rfl) ⟨1704149, by rfl⟩ : syracuseStep 2272199 = 3408299) B3408299
theorem B2556229 : Blo 2271435 2556229 := bbase (se 4 (by rfl) ⟨239646, by rfl⟩ : syracuseStep 2556229 = 479293) (by norm_num)
theorem B3408305 : Blo 2271435 3408305 := bstep (se 2 (by rfl) ⟨1278114, by rfl⟩ : syracuseStep 3408305 = 2556229) B2556229
theorem B2272203 : Blo 2271435 2272203 := bstep (se 1 (by rfl) ⟨1704152, by rfl⟩ : syracuseStep 2272203 = 3408305) B3408305
theorem B4313645 : Blo 2271435 4313645 := bbase (se 3 (by rfl) ⟨808808, by rfl⟩ : syracuseStep 4313645 = 1617617) (by norm_num)
theorem B2875763 : Blo 2271435 2875763 := bstep (se 1 (by rfl) ⟨2156822, by rfl⟩ : syracuseStep 2875763 = 4313645) B4313645
theorem B7668701 : Blo 2271435 7668701 := bstep (se 3 (by rfl) ⟨1437881, by rfl⟩ : syracuseStep 7668701 = 2875763) B2875763
theorem B5112467 : Blo 2271435 5112467 := bstep (se 1 (by rfl) ⟨3834350, by rfl⟩ : syracuseStep 5112467 = 7668701) B7668701
theorem B3408311 : Blo 2271435 3408311 := bstep (se 1 (by rfl) ⟨2556233, by rfl⟩ : syracuseStep 3408311 = 5112467) B5112467
theorem B2272207 : Blo 2271435 2272207 := bstep (se 1 (by rfl) ⟨1704155, by rfl⟩ : syracuseStep 2272207 = 3408311) B3408311
theorem B3408317 : Blo 2271435 3408317 := bbase (se 3 (by rfl) ⟨639059, by rfl⟩ : syracuseStep 3408317 = 1278119) (by norm_num)
theorem B2272211 : Blo 2271435 2272211 := bstep (se 1 (by rfl) ⟨1704158, by rfl⟩ : syracuseStep 2272211 = 3408317) B3408317
theorem B5112485 : Blo 2271435 5112485 := bbase (se 4 (by rfl) ⟨479295, by rfl⟩ : syracuseStep 5112485 = 958591) (by norm_num)
theorem B3408323 : Blo 2271435 3408323 := bstep (se 1 (by rfl) ⟨2556242, by rfl⟩ : syracuseStep 3408323 = 5112485) B5112485
theorem B2272215 : Blo 2271435 2272215 := bstep (se 1 (by rfl) ⟨1704161, by rfl⟩ : syracuseStep 2272215 = 3408323) B3408323
theorem B5751557 : Blo 2271435 5751557 := bbase (se 4 (by rfl) ⟨539208, by rfl⟩ : syracuseStep 5751557 = 1078417) (by norm_num)
theorem B3834371 : Blo 2271435 3834371 := bstep (se 1 (by rfl) ⟨2875778, by rfl⟩ : syracuseStep 3834371 = 5751557) B5751557
theorem B2556247 : Blo 2271435 2556247 := bstep (se 1 (by rfl) ⟨1917185, by rfl⟩ : syracuseStep 2556247 = 3834371) B3834371
theorem B3408329 : Blo 2271435 3408329 := bstep (se 2 (by rfl) ⟨1278123, by rfl⟩ : syracuseStep 3408329 = 2556247) B2556247
theorem B2272219 : Blo 2271435 2272219 := bstep (se 1 (by rfl) ⟨1704164, by rfl⟩ : syracuseStep 2272219 = 3408329) B3408329
theorem B4852885 : Blo 2271435 4852885 := bbase (se 6 (by rfl) ⟨113739, by rfl⟩ : syracuseStep 4852885 = 227479) (by norm_num)
theorem B6470513 : Blo 2271435 6470513 := bstep (se 2 (by rfl) ⟨2426442, by rfl⟩ : syracuseStep 6470513 = 4852885) B4852885
theorem B4313675 : Blo 2271435 4313675 := bstep (se 1 (by rfl) ⟨3235256, by rfl⟩ : syracuseStep 4313675 = 6470513) B6470513
theorem B11503133 : Blo 2271435 11503133 := bstep (se 3 (by rfl) ⟨2156837, by rfl⟩ : syracuseStep 11503133 = 4313675) B4313675
theorem B7668755 : Blo 2271435 7668755 := bstep (se 1 (by rfl) ⟨5751566, by rfl⟩ : syracuseStep 7668755 = 11503133) B11503133
theorem B5112503 : Blo 2271435 5112503 := bstep (se 1 (by rfl) ⟨3834377, by rfl⟩ : syracuseStep 5112503 = 7668755) B7668755
theorem B3408335 : Blo 2271435 3408335 := bstep (se 1 (by rfl) ⟨2556251, by rfl⟩ : syracuseStep 3408335 = 5112503) B5112503
theorem B2272223 : Blo 2271435 2272223 := bstep (se 1 (by rfl) ⟨1704167, by rfl⟩ : syracuseStep 2272223 = 3408335) B3408335
theorem B3408341 : Blo 2271435 3408341 := bbase (se 7 (by rfl) ⟨39941, by rfl⟩ : syracuseStep 3408341 = 79883) (by norm_num)
theorem B2272227 : Blo 2271435 2272227 := bstep (se 1 (by rfl) ⟨1704170, by rfl⟩ : syracuseStep 2272227 = 3408341) B3408341
theorem B8627381 : Blo 2271435 8627381 := bbase (se 5 (by rfl) ⟨404408, by rfl⟩ : syracuseStep 8627381 = 808817) (by norm_num)
theorem B5751587 : Blo 2271435 5751587 := bstep (se 1 (by rfl) ⟨4313690, by rfl⟩ : syracuseStep 5751587 = 8627381) B8627381
theorem B3834391 : Blo 2271435 3834391 := bstep (se 1 (by rfl) ⟨2875793, by rfl⟩ : syracuseStep 3834391 = 5751587) B5751587
theorem B5112521 : Blo 2271435 5112521 := bstep (se 2 (by rfl) ⟨1917195, by rfl⟩ : syracuseStep 5112521 = 3834391) B3834391
theorem B3408347 : Blo 2271435 3408347 := bstep (se 1 (by rfl) ⟨2556260, by rfl⟩ : syracuseStep 3408347 = 5112521) B5112521
theorem B2272231 : Blo 2271435 2272231 := bstep (se 1 (by rfl) ⟨1704173, by rfl⟩ : syracuseStep 2272231 = 3408347) B3408347
theorem B2556265 : Blo 2271435 2556265 := bbase (se 2 (by rfl) ⟨958599, by rfl⟩ : syracuseStep 2556265 = 1917199) (by norm_num)
theorem B3408353 : Blo 2271435 3408353 := bstep (se 2 (by rfl) ⟨1278132, by rfl⟩ : syracuseStep 3408353 = 2556265) B2556265
theorem B2272235 : Blo 2271435 2272235 := bstep (se 1 (by rfl) ⟨1704176, by rfl⟩ : syracuseStep 2272235 = 3408353) B3408353
theorem B2915041 : Blo 2271435 2915041 := bbase (se 2 (by rfl) ⟨1093140, by rfl⟩ : syracuseStep 2915041 = 2186281) (by norm_num)
theorem B3886721 : Blo 2271435 3886721 := bstep (se 2 (by rfl) ⟨1457520, by rfl⟩ : syracuseStep 3886721 = 2915041) B2915041
theorem B2591147 : Blo 2271435 2591147 := bstep (se 1 (by rfl) ⟨1943360, by rfl⟩ : syracuseStep 2591147 = 3886721) B3886721
theorem B6909725 : Blo 2271435 6909725 := bstep (se 3 (by rfl) ⟨1295573, by rfl⟩ : syracuseStep 6909725 = 2591147) B2591147
theorem B4606483 : Blo 2271435 4606483 := bstep (se 1 (by rfl) ⟨3454862, by rfl⟩ : syracuseStep 4606483 = 6909725) B6909725
theorem B6141977 : Blo 2271435 6141977 := bstep (se 2 (by rfl) ⟨2303241, by rfl⟩ : syracuseStep 6141977 = 4606483) B4606483
theorem B4094651 : Blo 2271435 4094651 := bstep (se 1 (by rfl) ⟨3070988, by rfl⟩ : syracuseStep 4094651 = 6141977) B6141977
theorem B10919069 : Blo 2271435 10919069 := bstep (se 3 (by rfl) ⟨2047325, by rfl⟩ : syracuseStep 10919069 = 4094651) B4094651
theorem B7279379 : Blo 2271435 7279379 := bstep (se 1 (by rfl) ⟨5459534, by rfl⟩ : syracuseStep 7279379 = 10919069) B10919069
theorem B4852919 : Blo 2271435 4852919 := bstep (se 1 (by rfl) ⟨3639689, by rfl⟩ : syracuseStep 4852919 = 7279379) B7279379
theorem B12941117 : Blo 2271435 12941117 := bstep (se 3 (by rfl) ⟨2426459, by rfl⟩ : syracuseStep 12941117 = 4852919) B4852919
theorem B8627411 : Blo 2271435 8627411 := bstep (se 1 (by rfl) ⟨6470558, by rfl⟩ : syracuseStep 8627411 = 12941117) B12941117
theorem B5751607 : Blo 2271435 5751607 := bstep (se 1 (by rfl) ⟨4313705, by rfl⟩ : syracuseStep 5751607 = 8627411) B8627411
theorem B7668809 : Blo 2271435 7668809 := bstep (se 2 (by rfl) ⟨2875803, by rfl⟩ : syracuseStep 7668809 = 5751607) B5751607
theorem B5112539 : Blo 2271435 5112539 := bstep (se 1 (by rfl) ⟨3834404, by rfl⟩ : syracuseStep 5112539 = 7668809) B7668809
theorem B3408359 : Blo 2271435 3408359 := bstep (se 1 (by rfl) ⟨2556269, by rfl⟩ : syracuseStep 3408359 = 5112539) B5112539
theorem B2272239 : Blo 2271435 2272239 := bstep (se 1 (by rfl) ⟨1704179, by rfl⟩ : syracuseStep 2272239 = 3408359) B3408359
theorem B3408365 : Blo 2271435 3408365 := bbase (se 3 (by rfl) ⟨639068, by rfl⟩ : syracuseStep 3408365 = 1278137) (by norm_num)
theorem B2272243 : Blo 2271435 2272243 := bstep (se 1 (by rfl) ⟨1704182, by rfl⟩ : syracuseStep 2272243 = 3408365) B3408365
theorem B5112557 : Blo 2271435 5112557 := bbase (se 3 (by rfl) ⟨958604, by rfl⟩ : syracuseStep 5112557 = 1917209) (by norm_num)
theorem B3408371 : Blo 2271435 3408371 := bstep (se 1 (by rfl) ⟨2556278, by rfl⟩ : syracuseStep 3408371 = 5112557) B5112557
theorem B2272247 : Blo 2271435 2272247 := bstep (se 1 (by rfl) ⟨1704185, by rfl⟩ : syracuseStep 2272247 = 3408371) B3408371
theorem B2426473 : Blo 2271435 2426473 := bbase (se 2 (by rfl) ⟨909927, by rfl⟩ : syracuseStep 2426473 = 1819855) (by norm_num)
theorem B3235297 : Blo 2271435 3235297 := bstep (se 2 (by rfl) ⟨1213236, by rfl⟩ : syracuseStep 3235297 = 2426473) B2426473
theorem B4313729 : Blo 2271435 4313729 := bstep (se 2 (by rfl) ⟨1617648, by rfl⟩ : syracuseStep 4313729 = 3235297) B3235297
theorem B2875819 : Blo 2271435 2875819 := bstep (se 1 (by rfl) ⟨2156864, by rfl⟩ : syracuseStep 2875819 = 4313729) B4313729
theorem B3834425 : Blo 2271435 3834425 := bstep (se 2 (by rfl) ⟨1437909, by rfl⟩ : syracuseStep 3834425 = 2875819) B2875819
theorem B2556283 : Blo 2271435 2556283 := bstep (se 1 (by rfl) ⟨1917212, by rfl⟩ : syracuseStep 2556283 = 3834425) B3834425
theorem B3408377 : Blo 2271435 3408377 := bstep (se 2 (by rfl) ⟨1278141, by rfl⟩ : syracuseStep 3408377 = 2556283) B2556283
theorem B2272251 : Blo 2271435 2272251 := bstep (se 1 (by rfl) ⟨1704188, by rfl⟩ : syracuseStep 2272251 = 3408377) B3408377
theorem B2303257 : Blo 2271435 2303257 := bbase (se 2 (by rfl) ⟨863721, by rfl⟩ : syracuseStep 2303257 = 1727443) (by norm_num)
theorem B49136149 : Blo 2271435 49136149 := bstep (se 6 (by rfl) ⟨1151628, by rfl⟩ : syracuseStep 49136149 = 2303257) B2303257
theorem B65514865 : Blo 2271435 65514865 := bstep (se 2 (by rfl) ⟨24568074, by rfl⟩ : syracuseStep 65514865 = 49136149) B49136149
theorem B87353153 : Blo 2271435 87353153 := bstep (se 2 (by rfl) ⟨32757432, by rfl⟩ : syracuseStep 87353153 = 65514865) B65514865
theorem B58235435 : Blo 2271435 58235435 := bstep (se 1 (by rfl) ⟨43676576, by rfl⟩ : syracuseStep 58235435 = 87353153) B87353153
theorem B38823623 : Blo 2271435 38823623 := bstep (se 1 (by rfl) ⟨29117717, by rfl⟩ : syracuseStep 38823623 = 58235435) B58235435
theorem B25882415 : Blo 2271435 25882415 := bstep (se 1 (by rfl) ⟨19411811, by rfl⟩ : syracuseStep 25882415 = 38823623) B38823623
theorem B17254943 : Blo 2271435 17254943 := bstep (se 1 (by rfl) ⟨12941207, by rfl⟩ : syracuseStep 17254943 = 25882415) B25882415
theorem B11503295 : Blo 2271435 11503295 := bstep (se 1 (by rfl) ⟨8627471, by rfl⟩ : syracuseStep 11503295 = 17254943) B17254943
theorem B7668863 : Blo 2271435 7668863 := bstep (se 1 (by rfl) ⟨5751647, by rfl⟩ : syracuseStep 7668863 = 11503295) B11503295
theorem B5112575 : Blo 2271435 5112575 := bstep (se 1 (by rfl) ⟨3834431, by rfl⟩ : syracuseStep 5112575 = 7668863) B7668863
theorem B3408383 : Blo 2271435 3408383 := bstep (se 1 (by rfl) ⟨2556287, by rfl⟩ : syracuseStep 3408383 = 5112575) B5112575
theorem B2272255 : Blo 2271435 2272255 := bstep (se 1 (by rfl) ⟨1704191, by rfl⟩ : syracuseStep 2272255 = 3408383) B3408383
theorem B3408389 : Blo 2271435 3408389 := bbase (se 4 (by rfl) ⟨319536, by rfl⟩ : syracuseStep 3408389 = 639073) (by norm_num)
theorem B2272259 : Blo 2271435 2272259 := bstep (se 1 (by rfl) ⟨1704194, by rfl⟩ : syracuseStep 2272259 = 3408389) B3408389
theorem B3834445 : Blo 2271435 3834445 := bbase (se 3 (by rfl) ⟨718958, by rfl⟩ : syracuseStep 3834445 = 1437917) (by norm_num)
theorem B5112593 : Blo 2271435 5112593 := bstep (se 2 (by rfl) ⟨1917222, by rfl⟩ : syracuseStep 5112593 = 3834445) B3834445
theorem B3408395 : Blo 2271435 3408395 := bstep (se 1 (by rfl) ⟨2556296, by rfl⟩ : syracuseStep 3408395 = 5112593) B5112593
theorem B2272263 : Blo 2271435 2272263 := bstep (se 1 (by rfl) ⟨1704197, by rfl⟩ : syracuseStep 2272263 = 3408395) B3408395
theorem B2556301 : Blo 2271435 2556301 := bbase (se 3 (by rfl) ⟨479306, by rfl⟩ : syracuseStep 2556301 = 958613) (by norm_num)
theorem B3408401 : Blo 2271435 3408401 := bstep (se 2 (by rfl) ⟨1278150, by rfl⟩ : syracuseStep 3408401 = 2556301) B2556301
theorem B2272267 : Blo 2271435 2272267 := bstep (se 1 (by rfl) ⟨1704200, by rfl⟩ : syracuseStep 2272267 = 3408401) B3408401
theorem B7668917 : Blo 2271435 7668917 := bbase (se 5 (by rfl) ⟨359480, by rfl⟩ : syracuseStep 7668917 = 718961) (by norm_num)
theorem B5112611 : Blo 2271435 5112611 := bstep (se 1 (by rfl) ⟨3834458, by rfl⟩ : syracuseStep 5112611 = 7668917) B7668917
theorem B3408407 : Blo 2271435 3408407 := bstep (se 1 (by rfl) ⟨2556305, by rfl⟩ : syracuseStep 3408407 = 5112611) B5112611
theorem B2272271 : Blo 2271435 2272271 := bstep (se 1 (by rfl) ⟨1704203, by rfl⟩ : syracuseStep 2272271 = 3408407) B3408407
theorem B3408413 : Blo 2271435 3408413 := bbase (se 3 (by rfl) ⟨639077, by rfl⟩ : syracuseStep 3408413 = 1278155) (by norm_num)
theorem B2272275 : Blo 2271435 2272275 := bstep (se 1 (by rfl) ⟨1704206, by rfl⟩ : syracuseStep 2272275 = 3408413) B3408413
theorem B5112629 : Blo 2271435 5112629 := bbase (se 5 (by rfl) ⟨239654, by rfl⟩ : syracuseStep 5112629 = 479309) (by norm_num)
theorem B3408419 : Blo 2271435 3408419 := bstep (se 1 (by rfl) ⟨2556314, by rfl⟩ : syracuseStep 3408419 = 5112629) B5112629
theorem B2272279 : Blo 2271435 2272279 := bstep (se 1 (by rfl) ⟨1704209, by rfl⟩ : syracuseStep 2272279 = 3408419) B3408419
theorem B8189461 : Blo 2271435 8189461 := bbase (se 6 (by rfl) ⟨191940, by rfl⟩ : syracuseStep 8189461 = 383881) (by norm_num)
theorem B10919281 : Blo 2271435 10919281 := bstep (se 2 (by rfl) ⟨4094730, by rfl⟩ : syracuseStep 10919281 = 8189461) B8189461
theorem B14559041 : Blo 2271435 14559041 := bstep (se 2 (by rfl) ⟨5459640, by rfl⟩ : syracuseStep 14559041 = 10919281) B10919281
theorem B9706027 : Blo 2271435 9706027 := bstep (se 1 (by rfl) ⟨7279520, by rfl⟩ : syracuseStep 9706027 = 14559041) B14559041
theorem B12941369 : Blo 2271435 12941369 := bstep (se 2 (by rfl) ⟨4853013, by rfl⟩ : syracuseStep 12941369 = 9706027) B9706027
theorem B8627579 : Blo 2271435 8627579 := bstep (se 1 (by rfl) ⟨6470684, by rfl⟩ : syracuseStep 8627579 = 12941369) B12941369
theorem B5751719 : Blo 2271435 5751719 := bstep (se 1 (by rfl) ⟨4313789, by rfl⟩ : syracuseStep 5751719 = 8627579) B8627579
theorem B3834479 : Blo 2271435 3834479 := bstep (se 1 (by rfl) ⟨2875859, by rfl⟩ : syracuseStep 3834479 = 5751719) B5751719
theorem B2556319 : Blo 2271435 2556319 := bstep (se 1 (by rfl) ⟨1917239, by rfl⟩ : syracuseStep 2556319 = 3834479) B3834479
theorem B3408425 : Blo 2271435 3408425 := bstep (se 2 (by rfl) ⟨1278159, by rfl⟩ : syracuseStep 3408425 = 2556319) B2556319
theorem B2272283 : Blo 2271435 2272283 := bstep (se 1 (by rfl) ⟨1704212, by rfl⟩ : syracuseStep 2272283 = 3408425) B3408425
theorem B3071053 : Blo 2271435 3071053 := bbase (se 3 (by rfl) ⟨575822, by rfl⟩ : syracuseStep 3071053 = 1151645) (by norm_num)
theorem B16378949 : Blo 2271435 16378949 := bstep (se 4 (by rfl) ⟨1535526, by rfl⟩ : syracuseStep 16378949 = 3071053) B3071053
theorem B10919299 : Blo 2271435 10919299 := bstep (se 1 (by rfl) ⟨8189474, by rfl⟩ : syracuseStep 10919299 = 16378949) B16378949
theorem B14559065 : Blo 2271435 14559065 := bstep (se 2 (by rfl) ⟨5459649, by rfl⟩ : syracuseStep 14559065 = 10919299) B10919299
theorem B9706043 : Blo 2271435 9706043 := bstep (se 1 (by rfl) ⟨7279532, by rfl⟩ : syracuseStep 9706043 = 14559065) B14559065
theorem B6470695 : Blo 2271435 6470695 := bstep (se 1 (by rfl) ⟨4853021, by rfl⟩ : syracuseStep 6470695 = 9706043) B9706043
theorem B8627593 : Blo 2271435 8627593 := bstep (se 2 (by rfl) ⟨3235347, by rfl⟩ : syracuseStep 8627593 = 6470695) B6470695
theorem B11503457 : Blo 2271435 11503457 := bstep (se 2 (by rfl) ⟨4313796, by rfl⟩ : syracuseStep 11503457 = 8627593) B8627593
theorem B7668971 : Blo 2271435 7668971 := bstep (se 1 (by rfl) ⟨5751728, by rfl⟩ : syracuseStep 7668971 = 11503457) B11503457
theorem B5112647 : Blo 2271435 5112647 := bstep (se 1 (by rfl) ⟨3834485, by rfl⟩ : syracuseStep 5112647 = 7668971) B7668971
theorem B3408431 : Blo 2271435 3408431 := bstep (se 1 (by rfl) ⟨2556323, by rfl⟩ : syracuseStep 3408431 = 5112647) B5112647
theorem B2272287 : Blo 2271435 2272287 := bstep (se 1 (by rfl) ⟨1704215, by rfl⟩ : syracuseStep 2272287 = 3408431) B3408431
theorem B3408437 : Blo 2271435 3408437 := bbase (se 5 (by rfl) ⟨159770, by rfl⟩ : syracuseStep 3408437 = 319541) (by norm_num)
theorem B2272291 : Blo 2271435 2272291 := bstep (se 1 (by rfl) ⟨1704218, by rfl⟩ : syracuseStep 2272291 = 3408437) B3408437
theorem B5751749 : Blo 2271435 5751749 := bbase (se 4 (by rfl) ⟨539226, by rfl⟩ : syracuseStep 5751749 = 1078453) (by norm_num)
theorem B3834499 : Blo 2271435 3834499 := bstep (se 1 (by rfl) ⟨2875874, by rfl⟩ : syracuseStep 3834499 = 5751749) B5751749
theorem B5112665 : Blo 2271435 5112665 := bstep (se 2 (by rfl) ⟨1917249, by rfl⟩ : syracuseStep 5112665 = 3834499) B3834499
theorem B3408443 : Blo 2271435 3408443 := bstep (se 1 (by rfl) ⟨2556332, by rfl⟩ : syracuseStep 3408443 = 5112665) B5112665
theorem B2272295 : Blo 2271435 2272295 := bstep (se 1 (by rfl) ⟨1704221, by rfl⟩ : syracuseStep 2272295 = 3408443) B3408443
theorem B2556337 : Blo 2271435 2556337 := bbase (se 2 (by rfl) ⟨958626, by rfl⟩ : syracuseStep 2556337 = 1917253) (by norm_num)
theorem B3408449 : Blo 2271435 3408449 := bstep (se 2 (by rfl) ⟨1278168, by rfl⟩ : syracuseStep 3408449 = 2556337) B2556337
theorem B2272299 : Blo 2271435 2272299 := bstep (se 1 (by rfl) ⟨1704224, by rfl⟩ : syracuseStep 2272299 = 3408449) B3408449
theorem B6470741 : Blo 2271435 6470741 := bbase (se 8 (by rfl) ⟨37914, by rfl⟩ : syracuseStep 6470741 = 75829) (by norm_num)
theorem B4313827 : Blo 2271435 4313827 := bstep (se 1 (by rfl) ⟨3235370, by rfl⟩ : syracuseStep 4313827 = 6470741) B6470741
theorem B5751769 : Blo 2271435 5751769 := bstep (se 2 (by rfl) ⟨2156913, by rfl⟩ : syracuseStep 5751769 = 4313827) B4313827
theorem B7669025 : Blo 2271435 7669025 := bstep (se 2 (by rfl) ⟨2875884, by rfl⟩ : syracuseStep 7669025 = 5751769) B5751769
theorem B5112683 : Blo 2271435 5112683 := bstep (se 1 (by rfl) ⟨3834512, by rfl⟩ : syracuseStep 5112683 = 7669025) B7669025
theorem B3408455 : Blo 2271435 3408455 := bstep (se 1 (by rfl) ⟨2556341, by rfl⟩ : syracuseStep 3408455 = 5112683) B5112683
theorem B2272303 : Blo 2271435 2272303 := bstep (se 1 (by rfl) ⟨1704227, by rfl⟩ : syracuseStep 2272303 = 3408455) B3408455
theorem B3408461 : Blo 2271435 3408461 := bbase (se 3 (by rfl) ⟨639086, by rfl⟩ : syracuseStep 3408461 = 1278173) (by norm_num)
theorem B2272307 : Blo 2271435 2272307 := bstep (se 1 (by rfl) ⟨1704230, by rfl⟩ : syracuseStep 2272307 = 3408461) B3408461
theorem B5112701 : Blo 2271435 5112701 := bbase (se 3 (by rfl) ⟨958631, by rfl⟩ : syracuseStep 5112701 = 1917263) (by norm_num)
theorem B3408467 : Blo 2271435 3408467 := bstep (se 1 (by rfl) ⟨2556350, by rfl⟩ : syracuseStep 3408467 = 5112701) B5112701
theorem B2272311 : Blo 2271435 2272311 := bstep (se 1 (by rfl) ⟨1704233, by rfl⟩ : syracuseStep 2272311 = 3408467) B3408467
theorem B3834533 : Blo 2271435 3834533 := bbase (se 4 (by rfl) ⟨359487, by rfl⟩ : syracuseStep 3834533 = 718975) (by norm_num)
theorem B2556355 : Blo 2271435 2556355 := bstep (se 1 (by rfl) ⟨1917266, by rfl⟩ : syracuseStep 2556355 = 3834533) B3834533
theorem B3408473 : Blo 2271435 3408473 := bstep (se 2 (by rfl) ⟨1278177, by rfl⟩ : syracuseStep 3408473 = 2556355) B2556355
theorem B2272315 : Blo 2271435 2272315 := bstep (se 1 (by rfl) ⟨1704236, by rfl⟩ : syracuseStep 2272315 = 3408473) B3408473
theorem B2426545 : Blo 2271435 2426545 := bbase (se 2 (by rfl) ⟨909954, by rfl⟩ : syracuseStep 2426545 = 1819909) (by norm_num)
theorem B3235393 : Blo 2271435 3235393 := bstep (se 2 (by rfl) ⟨1213272, by rfl⟩ : syracuseStep 3235393 = 2426545) B2426545
theorem B17255429 : Blo 2271435 17255429 := bstep (se 4 (by rfl) ⟨1617696, by rfl⟩ : syracuseStep 17255429 = 3235393) B3235393
theorem B11503619 : Blo 2271435 11503619 := bstep (se 1 (by rfl) ⟨8627714, by rfl⟩ : syracuseStep 11503619 = 17255429) B17255429
theorem B7669079 : Blo 2271435 7669079 := bstep (se 1 (by rfl) ⟨5751809, by rfl⟩ : syracuseStep 7669079 = 11503619) B11503619
theorem B5112719 : Blo 2271435 5112719 := bstep (se 1 (by rfl) ⟨3834539, by rfl⟩ : syracuseStep 5112719 = 7669079) B7669079
theorem B3408479 : Blo 2271435 3408479 := bstep (se 1 (by rfl) ⟨2556359, by rfl⟩ : syracuseStep 3408479 = 5112719) B5112719
theorem B2272319 : Blo 2271435 2272319 := bstep (se 1 (by rfl) ⟨1704239, by rfl⟩ : syracuseStep 2272319 = 3408479) B3408479
theorem B3408485 : Blo 2271435 3408485 := bbase (se 4 (by rfl) ⟨319545, by rfl⟩ : syracuseStep 3408485 = 639091) (by norm_num)
theorem B2272323 : Blo 2271435 2272323 := bstep (se 1 (by rfl) ⟨1704242, by rfl⟩ : syracuseStep 2272323 = 3408485) B3408485
theorem B3235405 : Blo 2271435 3235405 := bbase (se 3 (by rfl) ⟨606638, by rfl⟩ : syracuseStep 3235405 = 1213277) (by norm_num)
theorem B4313873 : Blo 2271435 4313873 := bstep (se 2 (by rfl) ⟨1617702, by rfl⟩ : syracuseStep 4313873 = 3235405) B3235405
theorem B2875915 : Blo 2271435 2875915 := bstep (se 1 (by rfl) ⟨2156936, by rfl⟩ : syracuseStep 2875915 = 4313873) B4313873
theorem B3834553 : Blo 2271435 3834553 := bstep (se 2 (by rfl) ⟨1437957, by rfl⟩ : syracuseStep 3834553 = 2875915) B2875915
theorem B5112737 : Blo 2271435 5112737 := bstep (se 2 (by rfl) ⟨1917276, by rfl⟩ : syracuseStep 5112737 = 3834553) B3834553
theorem B3408491 : Blo 2271435 3408491 := bstep (se 1 (by rfl) ⟨2556368, by rfl⟩ : syracuseStep 3408491 = 5112737) B5112737
theorem B2272327 : Blo 2271435 2272327 := bstep (se 1 (by rfl) ⟨1704245, by rfl⟩ : syracuseStep 2272327 = 3408491) B3408491
theorem B2556373 : Blo 2271435 2556373 := bbase (se 7 (by rfl) ⟨29957, by rfl⟩ : syracuseStep 2556373 = 59915) (by norm_num)
theorem B3408497 : Blo 2271435 3408497 := bstep (se 2 (by rfl) ⟨1278186, by rfl⟩ : syracuseStep 3408497 = 2556373) B2556373
theorem B2272331 : Blo 2271435 2272331 := bstep (se 1 (by rfl) ⟨1704248, by rfl⟩ : syracuseStep 2272331 = 3408497) B3408497
theorem B2875925 : Blo 2271435 2875925 := bbase (se 6 (by rfl) ⟨67404, by rfl⟩ : syracuseStep 2875925 = 134809) (by norm_num)
theorem B7669133 : Blo 2271435 7669133 := bstep (se 3 (by rfl) ⟨1437962, by rfl⟩ : syracuseStep 7669133 = 2875925) B2875925
theorem B5112755 : Blo 2271435 5112755 := bstep (se 1 (by rfl) ⟨3834566, by rfl⟩ : syracuseStep 5112755 = 7669133) B7669133
theorem B3408503 : Blo 2271435 3408503 := bstep (se 1 (by rfl) ⟨2556377, by rfl⟩ : syracuseStep 3408503 = 5112755) B5112755
theorem B2272335 : Blo 2271435 2272335 := bstep (se 1 (by rfl) ⟨1704251, by rfl⟩ : syracuseStep 2272335 = 3408503) B3408503
theorem B3408509 : Blo 2271435 3408509 := bbase (se 3 (by rfl) ⟨639095, by rfl⟩ : syracuseStep 3408509 = 1278191) (by norm_num)
theorem B2272339 : Blo 2271435 2272339 := bstep (se 1 (by rfl) ⟨1704254, by rfl⟩ : syracuseStep 2272339 = 3408509) B3408509
theorem B5112773 : Blo 2271435 5112773 := bbase (se 4 (by rfl) ⟨479322, by rfl⟩ : syracuseStep 5112773 = 958645) (by norm_num)
theorem B3408515 : Blo 2271435 3408515 := bstep (se 1 (by rfl) ⟨2556386, by rfl⟩ : syracuseStep 3408515 = 5112773) B5112773
theorem B2272343 : Blo 2271435 2272343 := bstep (se 1 (by rfl) ⟨1704257, by rfl⟩ : syracuseStep 2272343 = 3408515) B3408515
theorem B2626625 : Blo 2271435 2626625 := bbase (se 2 (by rfl) ⟨984984, by rfl⟩ : syracuseStep 2626625 = 1969969) (by norm_num)
theorem B7004333 : Blo 2271435 7004333 := bstep (se 3 (by rfl) ⟨1313312, by rfl⟩ : syracuseStep 7004333 = 2626625) B2626625
theorem B18678221 : Blo 2271435 18678221 := bstep (se 3 (by rfl) ⟨3502166, by rfl⟩ : syracuseStep 18678221 = 7004333) B7004333
theorem B12452147 : Blo 2271435 12452147 := bstep (se 1 (by rfl) ⟨9339110, by rfl⟩ : syracuseStep 12452147 = 18678221) B18678221
theorem B8301431 : Blo 2271435 8301431 := bstep (se 1 (by rfl) ⟨6226073, by rfl⟩ : syracuseStep 8301431 = 12452147) B12452147
theorem B5534287 : Blo 2271435 5534287 := bstep (se 1 (by rfl) ⟨4150715, by rfl⟩ : syracuseStep 5534287 = 8301431) B8301431
theorem B29516197 : Blo 2271435 29516197 := bstep (se 4 (by rfl) ⟨2767143, by rfl⟩ : syracuseStep 29516197 = 5534287) B5534287
theorem B39354929 : Blo 2271435 39354929 := bstep (se 2 (by rfl) ⟨14758098, by rfl⟩ : syracuseStep 39354929 = 29516197) B29516197
theorem B26236619 : Blo 2271435 26236619 := bstep (se 1 (by rfl) ⟨19677464, by rfl⟩ : syracuseStep 26236619 = 39354929) B39354929
theorem B17491079 : Blo 2271435 17491079 := bstep (se 1 (by rfl) ⟨13118309, by rfl⟩ : syracuseStep 17491079 = 26236619) B26236619
theorem B11660719 : Blo 2271435 11660719 := bstep (se 1 (by rfl) ⟨8745539, by rfl⟩ : syracuseStep 11660719 = 17491079) B17491079
theorem B15547625 : Blo 2271435 15547625 := bstep (se 2 (by rfl) ⟨5830359, by rfl⟩ : syracuseStep 15547625 = 11660719) B11660719
theorem B10365083 : Blo 2271435 10365083 := bstep (se 1 (by rfl) ⟨7773812, by rfl⟩ : syracuseStep 10365083 = 15547625) B15547625
theorem B6910055 : Blo 2271435 6910055 := bstep (se 1 (by rfl) ⟨5182541, by rfl⟩ : syracuseStep 6910055 = 10365083) B10365083
theorem B4606703 : Blo 2271435 4606703 := bstep (se 1 (by rfl) ⟨3455027, by rfl⟩ : syracuseStep 4606703 = 6910055) B6910055
theorem B3071135 : Blo 2271435 3071135 := bstep (se 1 (by rfl) ⟨2303351, by rfl⟩ : syracuseStep 3071135 = 4606703) B4606703
theorem B8189693 : Blo 2271435 8189693 := bstep (se 3 (by rfl) ⟨1535567, by rfl⟩ : syracuseStep 8189693 = 3071135) B3071135
theorem B5459795 : Blo 2271435 5459795 := bstep (se 1 (by rfl) ⟨4094846, by rfl⟩ : syracuseStep 5459795 = 8189693) B8189693
theorem B3639863 : Blo 2271435 3639863 := bstep (se 1 (by rfl) ⟨2729897, by rfl⟩ : syracuseStep 3639863 = 5459795) B5459795
theorem B9706301 : Blo 2271435 9706301 := bstep (se 3 (by rfl) ⟨1819931, by rfl⟩ : syracuseStep 9706301 = 3639863) B3639863
theorem B6470867 : Blo 2271435 6470867 := bstep (se 1 (by rfl) ⟨4853150, by rfl⟩ : syracuseStep 6470867 = 9706301) B9706301
theorem B4313911 : Blo 2271435 4313911 := bstep (se 1 (by rfl) ⟨3235433, by rfl⟩ : syracuseStep 4313911 = 6470867) B6470867
theorem B5751881 : Blo 2271435 5751881 := bstep (se 2 (by rfl) ⟨2156955, by rfl⟩ : syracuseStep 5751881 = 4313911) B4313911
theorem B3834587 : Blo 2271435 3834587 := bstep (se 1 (by rfl) ⟨2875940, by rfl⟩ : syracuseStep 3834587 = 5751881) B5751881
theorem B2556391 : Blo 2271435 2556391 := bstep (se 1 (by rfl) ⟨1917293, by rfl⟩ : syracuseStep 2556391 = 3834587) B3834587
theorem B3408521 : Blo 2271435 3408521 := bstep (se 2 (by rfl) ⟨1278195, by rfl⟩ : syracuseStep 3408521 = 2556391) B2556391
theorem B2272347 : Blo 2271435 2272347 := bstep (se 1 (by rfl) ⟨1704260, by rfl⟩ : syracuseStep 2272347 = 3408521) B3408521
theorem B11503781 : Blo 2271435 11503781 := bbase (se 4 (by rfl) ⟨1078479, by rfl⟩ : syracuseStep 11503781 = 2156959) (by norm_num)
theorem B7669187 : Blo 2271435 7669187 := bstep (se 1 (by rfl) ⟨5751890, by rfl⟩ : syracuseStep 7669187 = 11503781) B11503781
theorem B5112791 : Blo 2271435 5112791 := bstep (se 1 (by rfl) ⟨3834593, by rfl⟩ : syracuseStep 5112791 = 7669187) B7669187
theorem B3408527 : Blo 2271435 3408527 := bstep (se 1 (by rfl) ⟨2556395, by rfl⟩ : syracuseStep 3408527 = 5112791) B5112791
theorem B2272351 : Blo 2271435 2272351 := bstep (se 1 (by rfl) ⟨1704263, by rfl⟩ : syracuseStep 2272351 = 3408527) B3408527
theorem B3408533 : Blo 2271435 3408533 := bbase (se 6 (by rfl) ⟨79887, by rfl⟩ : syracuseStep 3408533 = 159775) (by norm_num)
theorem B2272355 : Blo 2271435 2272355 := bstep (se 1 (by rfl) ⟨1704266, by rfl⟩ : syracuseStep 2272355 = 3408533) B3408533
theorem B3886925 : Blo 2271435 3886925 := bbase (se 3 (by rfl) ⟨728798, by rfl⟩ : syracuseStep 3886925 = 1457597) (by norm_num)
theorem B10365133 : Blo 2271435 10365133 := bstep (se 3 (by rfl) ⟨1943462, by rfl⟩ : syracuseStep 10365133 = 3886925) B3886925
theorem B13820177 : Blo 2271435 13820177 := bstep (se 2 (by rfl) ⟨5182566, by rfl⟩ : syracuseStep 13820177 = 10365133) B10365133
theorem B36853805 : Blo 2271435 36853805 := bstep (se 3 (by rfl) ⟨6910088, by rfl⟩ : syracuseStep 36853805 = 13820177) B13820177
theorem B24569203 : Blo 2271435 24569203 := bstep (se 1 (by rfl) ⟨18426902, by rfl⟩ : syracuseStep 24569203 = 36853805) B36853805
theorem B32758937 : Blo 2271435 32758937 := bstep (se 2 (by rfl) ⟨12284601, by rfl⟩ : syracuseStep 32758937 = 24569203) B24569203
theorem B21839291 : Blo 2271435 21839291 := bstep (se 1 (by rfl) ⟨16379468, by rfl⟩ : syracuseStep 21839291 = 32758937) B32758937
theorem B14559527 : Blo 2271435 14559527 := bstep (se 1 (by rfl) ⟨10919645, by rfl⟩ : syracuseStep 14559527 = 21839291) B21839291
theorem B9706351 : Blo 2271435 9706351 := bstep (se 1 (by rfl) ⟨7279763, by rfl⟩ : syracuseStep 9706351 = 14559527) B14559527
theorem B12941801 : Blo 2271435 12941801 := bstep (se 2 (by rfl) ⟨4853175, by rfl⟩ : syracuseStep 12941801 = 9706351) B9706351
theorem B8627867 : Blo 2271435 8627867 := bstep (se 1 (by rfl) ⟨6470900, by rfl⟩ : syracuseStep 8627867 = 12941801) B12941801
theorem B5751911 : Blo 2271435 5751911 := bstep (se 1 (by rfl) ⟨4313933, by rfl⟩ : syracuseStep 5751911 = 8627867) B8627867
theorem B3834607 : Blo 2271435 3834607 := bstep (se 1 (by rfl) ⟨2875955, by rfl⟩ : syracuseStep 3834607 = 5751911) B5751911
theorem B5112809 : Blo 2271435 5112809 := bstep (se 2 (by rfl) ⟨1917303, by rfl⟩ : syracuseStep 5112809 = 3834607) B3834607
theorem B3408539 : Blo 2271435 3408539 := bstep (se 1 (by rfl) ⟨2556404, by rfl⟩ : syracuseStep 3408539 = 5112809) B5112809
theorem B2272359 : Blo 2271435 2272359 := bstep (se 1 (by rfl) ⟨1704269, by rfl⟩ : syracuseStep 2272359 = 3408539) B3408539
theorem B2556409 : Blo 2271435 2556409 := bbase (se 2 (by rfl) ⟨958653, by rfl⟩ : syracuseStep 2556409 = 1917307) (by norm_num)
theorem B3408545 : Blo 2271435 3408545 := bstep (se 2 (by rfl) ⟨1278204, by rfl⟩ : syracuseStep 3408545 = 2556409) B2556409
theorem B2272363 : Blo 2271435 2272363 := bstep (se 1 (by rfl) ⟨1704272, by rfl⟩ : syracuseStep 2272363 = 3408545) B3408545
theorem B2729921 : Blo 2271435 2729921 := bbase (se 2 (by rfl) ⟨1023720, by rfl⟩ : syracuseStep 2729921 = 2047441) (by norm_num)
theorem B7279789 : Blo 2271435 7279789 := bstep (se 3 (by rfl) ⟨1364960, by rfl⟩ : syracuseStep 7279789 = 2729921) B2729921
theorem B9706385 : Blo 2271435 9706385 := bstep (se 2 (by rfl) ⟨3639894, by rfl⟩ : syracuseStep 9706385 = 7279789) B7279789
theorem B6470923 : Blo 2271435 6470923 := bstep (se 1 (by rfl) ⟨4853192, by rfl⟩ : syracuseStep 6470923 = 9706385) B9706385
theorem B8627897 : Blo 2271435 8627897 := bstep (se 2 (by rfl) ⟨3235461, by rfl⟩ : syracuseStep 8627897 = 6470923) B6470923
theorem B5751931 : Blo 2271435 5751931 := bstep (se 1 (by rfl) ⟨4313948, by rfl⟩ : syracuseStep 5751931 = 8627897) B8627897
theorem B7669241 : Blo 2271435 7669241 := bstep (se 2 (by rfl) ⟨2875965, by rfl⟩ : syracuseStep 7669241 = 5751931) B5751931
theorem B5112827 : Blo 2271435 5112827 := bstep (se 1 (by rfl) ⟨3834620, by rfl⟩ : syracuseStep 5112827 = 7669241) B7669241
theorem B3408551 : Blo 2271435 3408551 := bstep (se 1 (by rfl) ⟨2556413, by rfl⟩ : syracuseStep 3408551 = 5112827) B5112827
theorem B2272367 : Blo 2271435 2272367 := bstep (se 1 (by rfl) ⟨1704275, by rfl⟩ : syracuseStep 2272367 = 3408551) B3408551
theorem B3408557 : Blo 2271435 3408557 := bbase (se 3 (by rfl) ⟨639104, by rfl⟩ : syracuseStep 3408557 = 1278209) (by norm_num)
theorem B2272371 : Blo 2271435 2272371 := bstep (se 1 (by rfl) ⟨1704278, by rfl⟩ : syracuseStep 2272371 = 3408557) B3408557
theorem B5112845 : Blo 2271435 5112845 := bbase (se 3 (by rfl) ⟨958658, by rfl⟩ : syracuseStep 5112845 = 1917317) (by norm_num)
theorem B3408563 : Blo 2271435 3408563 := bstep (se 1 (by rfl) ⟨2556422, by rfl⟩ : syracuseStep 3408563 = 5112845) B5112845
theorem B2272375 : Blo 2271435 2272375 := bstep (se 1 (by rfl) ⟨1704281, by rfl⟩ : syracuseStep 2272375 = 3408563) B3408563
theorem B2875981 : Blo 2271435 2875981 := bbase (se 3 (by rfl) ⟨539246, by rfl⟩ : syracuseStep 2875981 = 1078493) (by norm_num)
theorem B3834641 : Blo 2271435 3834641 := bstep (se 2 (by rfl) ⟨1437990, by rfl⟩ : syracuseStep 3834641 = 2875981) B2875981
theorem B2556427 : Blo 2271435 2556427 := bstep (se 1 (by rfl) ⟨1917320, by rfl⟩ : syracuseStep 2556427 = 3834641) B3834641
theorem B3408569 : Blo 2271435 3408569 := bstep (se 2 (by rfl) ⟨1278213, by rfl⟩ : syracuseStep 3408569 = 2556427) B2556427
theorem B2272379 : Blo 2271435 2272379 := bstep (se 1 (by rfl) ⟨1704284, by rfl⟩ : syracuseStep 2272379 = 3408569) B3408569
theorem B3939997 : Blo 2271435 3939997 := bbase (se 3 (by rfl) ⟨738749, by rfl⟩ : syracuseStep 3939997 = 1477499) (by norm_num)
theorem B5253329 : Blo 2271435 5253329 := bstep (se 2 (by rfl) ⟨1969998, by rfl⟩ : syracuseStep 5253329 = 3939997) B3939997
theorem B3502219 : Blo 2271435 3502219 := bstep (se 1 (by rfl) ⟨2626664, by rfl⟩ : syracuseStep 3502219 = 5253329) B5253329
theorem B74714005 : Blo 2271435 74714005 := bstep (se 6 (by rfl) ⟨1751109, by rfl⟩ : syracuseStep 74714005 = 3502219) B3502219
theorem B99618673 : Blo 2271435 99618673 := bstep (se 2 (by rfl) ⟨37357002, by rfl⟩ : syracuseStep 99618673 = 74714005) B74714005
theorem B132824897 : Blo 2271435 132824897 := bstep (se 2 (by rfl) ⟨49809336, by rfl⟩ : syracuseStep 132824897 = 99618673) B99618673
theorem B88549931 : Blo 2271435 88549931 := bstep (se 1 (by rfl) ⟨66412448, by rfl⟩ : syracuseStep 88549931 = 132824897) B132824897
theorem B59033287 : Blo 2271435 59033287 := bstep (se 1 (by rfl) ⟨44274965, by rfl⟩ : syracuseStep 59033287 = 88549931) B88549931
theorem B78711049 : Blo 2271435 78711049 := bstep (se 2 (by rfl) ⟨29516643, by rfl⟩ : syracuseStep 78711049 = 59033287) B59033287
theorem B104948065 : Blo 2271435 104948065 := bstep (se 2 (by rfl) ⟨39355524, by rfl⟩ : syracuseStep 104948065 = 78711049) B78711049
theorem B139930753 : Blo 2271435 139930753 := bstep (se 2 (by rfl) ⟨52474032, by rfl⟩ : syracuseStep 139930753 = 104948065) B104948065
theorem B186574337 : Blo 2271435 186574337 := bstep (se 2 (by rfl) ⟨69965376, by rfl⟩ : syracuseStep 186574337 = 139930753) B139930753
theorem B124382891 : Blo 2271435 124382891 := bstep (se 1 (by rfl) ⟨93287168, by rfl⟩ : syracuseStep 124382891 = 186574337) B186574337
theorem B82921927 : Blo 2271435 82921927 := bstep (se 1 (by rfl) ⟨62191445, by rfl⟩ : syracuseStep 82921927 = 124382891) B124382891
theorem B110562569 : Blo 2271435 110562569 := bstep (se 2 (by rfl) ⟨41460963, by rfl⟩ : syracuseStep 110562569 = 82921927) B82921927
theorem B73708379 : Blo 2271435 73708379 := bstep (se 1 (by rfl) ⟨55281284, by rfl⟩ : syracuseStep 73708379 = 110562569) B110562569
theorem B49138919 : Blo 2271435 49138919 := bstep (se 1 (by rfl) ⟨36854189, by rfl⟩ : syracuseStep 49138919 = 73708379) B73708379
theorem B32759279 : Blo 2271435 32759279 := bstep (se 1 (by rfl) ⟨24569459, by rfl⟩ : syracuseStep 32759279 = 49138919) B49138919
theorem B21839519 : Blo 2271435 21839519 := bstep (se 1 (by rfl) ⟨16379639, by rfl⟩ : syracuseStep 21839519 = 32759279) B32759279
theorem B14559679 : Blo 2271435 14559679 := bstep (se 1 (by rfl) ⟨10919759, by rfl⟩ : syracuseStep 14559679 = 21839519) B21839519
theorem B19412905 : Blo 2271435 19412905 := bstep (se 2 (by rfl) ⟨7279839, by rfl⟩ : syracuseStep 19412905 = 14559679) B14559679
theorem B25883873 : Blo 2271435 25883873 := bstep (se 2 (by rfl) ⟨9706452, by rfl⟩ : syracuseStep 25883873 = 19412905) B19412905
theorem B17255915 : Blo 2271435 17255915 := bstep (se 1 (by rfl) ⟨12941936, by rfl⟩ : syracuseStep 17255915 = 25883873) B25883873
theorem B11503943 : Blo 2271435 11503943 := bstep (se 1 (by rfl) ⟨8627957, by rfl⟩ : syracuseStep 11503943 = 17255915) B17255915
theorem B7669295 : Blo 2271435 7669295 := bstep (se 1 (by rfl) ⟨5751971, by rfl⟩ : syracuseStep 7669295 = 11503943) B11503943
theorem B5112863 : Blo 2271435 5112863 := bstep (se 1 (by rfl) ⟨3834647, by rfl⟩ : syracuseStep 5112863 = 7669295) B7669295
theorem B3408575 : Blo 2271435 3408575 := bstep (se 1 (by rfl) ⟨2556431, by rfl⟩ : syracuseStep 3408575 = 5112863) B5112863
theorem B2272383 : Blo 2271435 2272383 := bstep (se 1 (by rfl) ⟨1704287, by rfl⟩ : syracuseStep 2272383 = 3408575) B3408575
theorem B3408581 : Blo 2271435 3408581 := bbase (se 4 (by rfl) ⟨319554, by rfl⟩ : syracuseStep 3408581 = 639109) (by norm_num)
theorem B2272387 : Blo 2271435 2272387 := bstep (se 1 (by rfl) ⟨1704290, by rfl⟩ : syracuseStep 2272387 = 3408581) B3408581
theorem B3834661 : Blo 2271435 3834661 := bbase (se 4 (by rfl) ⟨359499, by rfl⟩ : syracuseStep 3834661 = 718999) (by norm_num)
theorem B5112881 : Blo 2271435 5112881 := bstep (se 2 (by rfl) ⟨1917330, by rfl⟩ : syracuseStep 5112881 = 3834661) B3834661
theorem B3408587 : Blo 2271435 3408587 := bstep (se 1 (by rfl) ⟨2556440, by rfl⟩ : syracuseStep 3408587 = 5112881) B5112881
theorem B2272391 : Blo 2271435 2272391 := bstep (se 1 (by rfl) ⟨1704293, by rfl⟩ : syracuseStep 2272391 = 3408587) B3408587
theorem B2556445 : Blo 2271435 2556445 := bbase (se 3 (by rfl) ⟨479333, by rfl⟩ : syracuseStep 2556445 = 958667) (by norm_num)
theorem B3408593 : Blo 2271435 3408593 := bstep (se 2 (by rfl) ⟨1278222, by rfl⟩ : syracuseStep 3408593 = 2556445) B2556445
theorem B2272395 : Blo 2271435 2272395 := bstep (se 1 (by rfl) ⟨1704296, by rfl⟩ : syracuseStep 2272395 = 3408593) B3408593
theorem B7669349 : Blo 2271435 7669349 := bbase (se 4 (by rfl) ⟨719001, by rfl⟩ : syracuseStep 7669349 = 1438003) (by norm_num)
theorem B5112899 : Blo 2271435 5112899 := bstep (se 1 (by rfl) ⟨3834674, by rfl⟩ : syracuseStep 5112899 = 7669349) B7669349
theorem B3408599 : Blo 2271435 3408599 := bstep (se 1 (by rfl) ⟨2556449, by rfl⟩ : syracuseStep 3408599 = 5112899) B5112899
theorem B2272399 : Blo 2271435 2272399 := bstep (se 1 (by rfl) ⟨1704299, by rfl⟩ : syracuseStep 2272399 = 3408599) B3408599
theorem B3408605 : Blo 2271435 3408605 := bbase (se 3 (by rfl) ⟨639113, by rfl⟩ : syracuseStep 3408605 = 1278227) (by norm_num)
theorem B2272403 : Blo 2271435 2272403 := bstep (se 1 (by rfl) ⟨1704302, by rfl⟩ : syracuseStep 2272403 = 3408605) B3408605
theorem B5112917 : Blo 2271435 5112917 := bbase (se 8 (by rfl) ⟨29958, by rfl⟩ : syracuseStep 5112917 = 59917) (by norm_num)
theorem B3408611 : Blo 2271435 3408611 := bstep (se 1 (by rfl) ⟨2556458, by rfl⟩ : syracuseStep 3408611 = 5112917) B5112917
theorem B2272407 : Blo 2271435 2272407 := bstep (se 1 (by rfl) ⟨1704305, by rfl⟩ : syracuseStep 2272407 = 3408611) B3408611
theorem B12284885 : Blo 2271435 12284885 := bbase (se 7 (by rfl) ⟨143963, by rfl⟩ : syracuseStep 12284885 = 287927) (by norm_num)
theorem B8189923 : Blo 2271435 8189923 := bstep (se 1 (by rfl) ⟨6142442, by rfl⟩ : syracuseStep 8189923 = 12284885) B12284885
theorem B10919897 : Blo 2271435 10919897 := bstep (se 2 (by rfl) ⟨4094961, by rfl⟩ : syracuseStep 10919897 = 8189923) B8189923
theorem B7279931 : Blo 2271435 7279931 := bstep (se 1 (by rfl) ⟨5459948, by rfl⟩ : syracuseStep 7279931 = 10919897) B10919897
theorem B4853287 : Blo 2271435 4853287 := bstep (se 1 (by rfl) ⟨3639965, by rfl⟩ : syracuseStep 4853287 = 7279931) B7279931
theorem B6471049 : Blo 2271435 6471049 := bstep (se 2 (by rfl) ⟨2426643, by rfl⟩ : syracuseStep 6471049 = 4853287) B4853287
theorem B8628065 : Blo 2271435 8628065 := bstep (se 2 (by rfl) ⟨3235524, by rfl⟩ : syracuseStep 8628065 = 6471049) B6471049
theorem B5752043 : Blo 2271435 5752043 := bstep (se 1 (by rfl) ⟨4314032, by rfl⟩ : syracuseStep 5752043 = 8628065) B8628065
theorem B3834695 : Blo 2271435 3834695 := bstep (se 1 (by rfl) ⟨2876021, by rfl⟩ : syracuseStep 3834695 = 5752043) B5752043
theorem B2556463 : Blo 2271435 2556463 := bstep (se 1 (by rfl) ⟨1917347, by rfl⟩ : syracuseStep 2556463 = 3834695) B3834695
theorem B3408617 : Blo 2271435 3408617 := bstep (se 2 (by rfl) ⟨1278231, by rfl⟩ : syracuseStep 3408617 = 2556463) B2556463
theorem B2272411 : Blo 2271435 2272411 := bstep (se 1 (by rfl) ⟨1704308, by rfl⟩ : syracuseStep 2272411 = 3408617) B3408617
theorem B46644245 : Blo 2271435 46644245 := bbase (se 6 (by rfl) ⟨1093224, by rfl⟩ : syracuseStep 46644245 = 2186449) (by norm_num)
theorem B31096163 : Blo 2271435 31096163 := bstep (se 1 (by rfl) ⟨23322122, by rfl⟩ : syracuseStep 31096163 = 46644245) B46644245
theorem B20730775 : Blo 2271435 20730775 := bstep (se 1 (by rfl) ⟨15548081, by rfl⟩ : syracuseStep 20730775 = 31096163) B31096163
theorem B27641033 : Blo 2271435 27641033 := bstep (se 2 (by rfl) ⟨10365387, by rfl⟩ : syracuseStep 27641033 = 20730775) B20730775
theorem B18427355 : Blo 2271435 18427355 := bstep (se 1 (by rfl) ⟨13820516, by rfl⟩ : syracuseStep 18427355 = 27641033) B27641033
theorem B12284903 : Blo 2271435 12284903 := bstep (se 1 (by rfl) ⟨9213677, by rfl⟩ : syracuseStep 12284903 = 18427355) B18427355
theorem B32759741 : Blo 2271435 32759741 := bstep (se 3 (by rfl) ⟨6142451, by rfl⟩ : syracuseStep 32759741 = 12284903) B12284903
theorem B21839827 : Blo 2271435 21839827 := bstep (se 1 (by rfl) ⟨16379870, by rfl⟩ : syracuseStep 21839827 = 32759741) B32759741
theorem B29119769 : Blo 2271435 29119769 := bstep (se 2 (by rfl) ⟨10919913, by rfl⟩ : syracuseStep 29119769 = 21839827) B21839827
theorem B19413179 : Blo 2271435 19413179 := bstep (se 1 (by rfl) ⟨14559884, by rfl⟩ : syracuseStep 19413179 = 29119769) B29119769
theorem B12942119 : Blo 2271435 12942119 := bstep (se 1 (by rfl) ⟨9706589, by rfl⟩ : syracuseStep 12942119 = 19413179) B19413179
theorem B8628079 : Blo 2271435 8628079 := bstep (se 1 (by rfl) ⟨6471059, by rfl⟩ : syracuseStep 8628079 = 12942119) B12942119
theorem B11504105 : Blo 2271435 11504105 := bstep (se 2 (by rfl) ⟨4314039, by rfl⟩ : syracuseStep 11504105 = 8628079) B8628079
theorem B7669403 : Blo 2271435 7669403 := bstep (se 1 (by rfl) ⟨5752052, by rfl⟩ : syracuseStep 7669403 = 11504105) B11504105
theorem B5112935 : Blo 2271435 5112935 := bstep (se 1 (by rfl) ⟨3834701, by rfl⟩ : syracuseStep 5112935 = 7669403) B7669403
theorem B3408623 : Blo 2271435 3408623 := bstep (se 1 (by rfl) ⟨2556467, by rfl⟩ : syracuseStep 3408623 = 5112935) B5112935
theorem B2272415 : Blo 2271435 2272415 := bstep (se 1 (by rfl) ⟨1704311, by rfl⟩ : syracuseStep 2272415 = 3408623) B3408623
theorem B3408629 : Blo 2271435 3408629 := bbase (se 5 (by rfl) ⟨159779, by rfl⟩ : syracuseStep 3408629 = 319559) (by norm_num)
theorem B2272419 : Blo 2271435 2272419 := bstep (se 1 (by rfl) ⟨1704314, by rfl⟩ : syracuseStep 2272419 = 3408629) B3408629
theorem B2591357 : Blo 2271435 2591357 := bbase (se 3 (by rfl) ⟨485879, by rfl⟩ : syracuseStep 2591357 = 971759) (by norm_num)
theorem B6910285 : Blo 2271435 6910285 := bstep (se 3 (by rfl) ⟨1295678, by rfl⟩ : syracuseStep 6910285 = 2591357) B2591357
theorem B9213713 : Blo 2271435 9213713 := bstep (se 2 (by rfl) ⟨3455142, by rfl⟩ : syracuseStep 9213713 = 6910285) B6910285
theorem B6142475 : Blo 2271435 6142475 := bstep (se 1 (by rfl) ⟨4606856, by rfl⟩ : syracuseStep 6142475 = 9213713) B9213713
theorem B4094983 : Blo 2271435 4094983 := bstep (se 1 (by rfl) ⟨3071237, by rfl⟩ : syracuseStep 4094983 = 6142475) B6142475
theorem B5459977 : Blo 2271435 5459977 := bstep (se 2 (by rfl) ⟨2047491, by rfl⟩ : syracuseStep 5459977 = 4094983) B4094983
theorem B7279969 : Blo 2271435 7279969 := bstep (se 2 (by rfl) ⟨2729988, by rfl⟩ : syracuseStep 7279969 = 5459977) B5459977
theorem B9706625 : Blo 2271435 9706625 := bstep (se 2 (by rfl) ⟨3639984, by rfl⟩ : syracuseStep 9706625 = 7279969) B7279969
theorem B6471083 : Blo 2271435 6471083 := bstep (se 1 (by rfl) ⟨4853312, by rfl⟩ : syracuseStep 6471083 = 9706625) B9706625
theorem B4314055 : Blo 2271435 4314055 := bstep (se 1 (by rfl) ⟨3235541, by rfl⟩ : syracuseStep 4314055 = 6471083) B6471083
theorem B5752073 : Blo 2271435 5752073 := bstep (se 2 (by rfl) ⟨2157027, by rfl⟩ : syracuseStep 5752073 = 4314055) B4314055
theorem B3834715 : Blo 2271435 3834715 := bstep (se 1 (by rfl) ⟨2876036, by rfl⟩ : syracuseStep 3834715 = 5752073) B5752073
theorem B5112953 : Blo 2271435 5112953 := bstep (se 2 (by rfl) ⟨1917357, by rfl⟩ : syracuseStep 5112953 = 3834715) B3834715
theorem B3408635 : Blo 2271435 3408635 := bstep (se 1 (by rfl) ⟨2556476, by rfl⟩ : syracuseStep 3408635 = 5112953) B5112953
theorem B2272423 : Blo 2271435 2272423 := bstep (se 1 (by rfl) ⟨1704317, by rfl⟩ : syracuseStep 2272423 = 3408635) B3408635
theorem B2556481 : Blo 2271435 2556481 := bbase (se 2 (by rfl) ⟨958680, by rfl⟩ : syracuseStep 2556481 = 1917361) (by norm_num)
theorem B3408641 : Blo 2271435 3408641 := bstep (se 2 (by rfl) ⟨1278240, by rfl⟩ : syracuseStep 3408641 = 2556481) B2556481
theorem B2272427 : Blo 2271435 2272427 := bstep (se 1 (by rfl) ⟨1704320, by rfl⟩ : syracuseStep 2272427 = 3408641) B3408641
theorem B5752093 : Blo 2271435 5752093 := bbase (se 3 (by rfl) ⟨1078517, by rfl⟩ : syracuseStep 5752093 = 2157035) (by norm_num)
theorem B7669457 : Blo 2271435 7669457 := bstep (se 2 (by rfl) ⟨2876046, by rfl⟩ : syracuseStep 7669457 = 5752093) B5752093
theorem B5112971 : Blo 2271435 5112971 := bstep (se 1 (by rfl) ⟨3834728, by rfl⟩ : syracuseStep 5112971 = 7669457) B7669457
theorem B3408647 : Blo 2271435 3408647 := bstep (se 1 (by rfl) ⟨2556485, by rfl⟩ : syracuseStep 3408647 = 5112971) B5112971
theorem B2272431 : Blo 2271435 2272431 := bstep (se 1 (by rfl) ⟨1704323, by rfl⟩ : syracuseStep 2272431 = 3408647) B3408647
theorem B3408653 : Blo 2271435 3408653 := bbase (se 3 (by rfl) ⟨639122, by rfl⟩ : syracuseStep 3408653 = 1278245) (by norm_num)
theorem B2272435 : Blo 2271435 2272435 := bstep (se 1 (by rfl) ⟨1704326, by rfl⟩ : syracuseStep 2272435 = 3408653) B3408653
theorem B5112989 : Blo 2271435 5112989 := bbase (se 3 (by rfl) ⟨958685, by rfl⟩ : syracuseStep 5112989 = 1917371) (by norm_num)
theorem B3408659 : Blo 2271435 3408659 := bstep (se 1 (by rfl) ⟨2556494, by rfl⟩ : syracuseStep 3408659 = 5112989) B5112989
theorem B2272439 : Blo 2271435 2272439 := bstep (se 1 (by rfl) ⟨1704329, by rfl⟩ : syracuseStep 2272439 = 3408659) B3408659
theorem B3834749 : Blo 2271435 3834749 := bbase (se 3 (by rfl) ⟨719015, by rfl⟩ : syracuseStep 3834749 = 1438031) (by norm_num)
theorem B2556499 : Blo 2271435 2556499 := bstep (se 1 (by rfl) ⟨1917374, by rfl⟩ : syracuseStep 2556499 = 3834749) B3834749
theorem B3408665 : Blo 2271435 3408665 := bstep (se 2 (by rfl) ⟨1278249, by rfl⟩ : syracuseStep 3408665 = 2556499) B2556499
theorem B2272443 : Blo 2271435 2272443 := bstep (se 1 (by rfl) ⟨1704332, by rfl⟩ : syracuseStep 2272443 = 3408665) B3408665
theorem B2730017 : Blo 2271435 2730017 := bbase (se 2 (by rfl) ⟨1023756, by rfl⟩ : syracuseStep 2730017 = 2047513) (by norm_num)
theorem B7280045 : Blo 2271435 7280045 := bstep (se 3 (by rfl) ⟨1365008, by rfl⟩ : syracuseStep 7280045 = 2730017) B2730017
theorem B4853363 : Blo 2271435 4853363 := bstep (se 1 (by rfl) ⟨3640022, by rfl⟩ : syracuseStep 4853363 = 7280045) B7280045
theorem B12942301 : Blo 2271435 12942301 := bstep (se 3 (by rfl) ⟨2426681, by rfl⟩ : syracuseStep 12942301 = 4853363) B4853363
theorem B17256401 : Blo 2271435 17256401 := bstep (se 2 (by rfl) ⟨6471150, by rfl⟩ : syracuseStep 17256401 = 12942301) B12942301
theorem B11504267 : Blo 2271435 11504267 := bstep (se 1 (by rfl) ⟨8628200, by rfl⟩ : syracuseStep 11504267 = 17256401) B17256401
theorem B7669511 : Blo 2271435 7669511 := bstep (se 1 (by rfl) ⟨5752133, by rfl⟩ : syracuseStep 7669511 = 11504267) B11504267
theorem B5113007 : Blo 2271435 5113007 := bstep (se 1 (by rfl) ⟨3834755, by rfl⟩ : syracuseStep 5113007 = 7669511) B7669511
theorem B3408671 : Blo 2271435 3408671 := bstep (se 1 (by rfl) ⟨2556503, by rfl⟩ : syracuseStep 3408671 = 5113007) B5113007
theorem B2272447 : Blo 2271435 2272447 := bstep (se 1 (by rfl) ⟨1704335, by rfl⟩ : syracuseStep 2272447 = 3408671) B3408671
theorem B3408677 : Blo 2271435 3408677 := bbase (se 4 (by rfl) ⟨319563, by rfl⟩ : syracuseStep 3408677 = 639127) (by norm_num)
theorem B2272451 : Blo 2271435 2272451 := bstep (se 1 (by rfl) ⟨1704338, by rfl⟩ : syracuseStep 2272451 = 3408677) B3408677
theorem B2876077 : Blo 2271435 2876077 := bbase (se 3 (by rfl) ⟨539264, by rfl⟩ : syracuseStep 2876077 = 1078529) (by norm_num)
theorem B3834769 : Blo 2271435 3834769 := bstep (se 2 (by rfl) ⟨1438038, by rfl⟩ : syracuseStep 3834769 = 2876077) B2876077
theorem B5113025 : Blo 2271435 5113025 := bstep (se 2 (by rfl) ⟨1917384, by rfl⟩ : syracuseStep 5113025 = 3834769) B3834769
theorem B3408683 : Blo 2271435 3408683 := bstep (se 1 (by rfl) ⟨2556512, by rfl⟩ : syracuseStep 3408683 = 5113025) B5113025
theorem B2272455 : Blo 2271435 2272455 := bstep (se 1 (by rfl) ⟨1704341, by rfl⟩ : syracuseStep 2272455 = 3408683) B3408683
theorem B2556517 : Blo 2271435 2556517 := bbase (se 4 (by rfl) ⟨239673, by rfl⟩ : syracuseStep 2556517 = 479347) (by norm_num)
theorem B3408689 : Blo 2271435 3408689 := bstep (se 2 (by rfl) ⟨1278258, by rfl⟩ : syracuseStep 3408689 = 2556517) B2556517
theorem B2272459 : Blo 2271435 2272459 := bstep (se 1 (by rfl) ⟨1704344, by rfl⟩ : syracuseStep 2272459 = 3408689) B3408689
theorem B2730037 : Blo 2271435 2730037 := bbase (se 5 (by rfl) ⟨127970, by rfl⟩ : syracuseStep 2730037 = 255941) (by norm_num)
theorem B3640049 : Blo 2271435 3640049 := bstep (se 2 (by rfl) ⟨1365018, by rfl⟩ : syracuseStep 3640049 = 2730037) B2730037
theorem B2426699 : Blo 2271435 2426699 := bstep (se 1 (by rfl) ⟨1820024, by rfl⟩ : syracuseStep 2426699 = 3640049) B3640049
theorem B6471197 : Blo 2271435 6471197 := bstep (se 3 (by rfl) ⟨1213349, by rfl⟩ : syracuseStep 6471197 = 2426699) B2426699
theorem B4314131 : Blo 2271435 4314131 := bstep (se 1 (by rfl) ⟨3235598, by rfl⟩ : syracuseStep 4314131 = 6471197) B6471197
theorem B2876087 : Blo 2271435 2876087 := bstep (se 1 (by rfl) ⟨2157065, by rfl⟩ : syracuseStep 2876087 = 4314131) B4314131
theorem B7669565 : Blo 2271435 7669565 := bstep (se 3 (by rfl) ⟨1438043, by rfl⟩ : syracuseStep 7669565 = 2876087) B2876087
theorem B5113043 : Blo 2271435 5113043 := bstep (se 1 (by rfl) ⟨3834782, by rfl⟩ : syracuseStep 5113043 = 7669565) B7669565
theorem B3408695 : Blo 2271435 3408695 := bstep (se 1 (by rfl) ⟨2556521, by rfl⟩ : syracuseStep 3408695 = 5113043) B5113043
theorem B2272463 : Blo 2271435 2272463 := bstep (se 1 (by rfl) ⟨1704347, by rfl⟩ : syracuseStep 2272463 = 3408695) B3408695
theorem B3408701 : Blo 2271435 3408701 := bbase (se 3 (by rfl) ⟨639131, by rfl⟩ : syracuseStep 3408701 = 1278263) (by norm_num)
theorem B2272467 : Blo 2271435 2272467 := bstep (se 1 (by rfl) ⟨1704350, by rfl⟩ : syracuseStep 2272467 = 3408701) B3408701
theorem B5113061 : Blo 2271435 5113061 := bbase (se 4 (by rfl) ⟨479349, by rfl⟩ : syracuseStep 5113061 = 958699) (by norm_num)
theorem B3408707 : Blo 2271435 3408707 := bstep (se 1 (by rfl) ⟨2556530, by rfl⟩ : syracuseStep 3408707 = 5113061) B5113061
theorem B2272471 : Blo 2271435 2272471 := bstep (se 1 (by rfl) ⟨1704353, by rfl⟩ : syracuseStep 2272471 = 3408707) B3408707
theorem B5752205 : Blo 2271435 5752205 := bbase (se 3 (by rfl) ⟨1078538, by rfl⟩ : syracuseStep 5752205 = 2157077) (by norm_num)
theorem B3834803 : Blo 2271435 3834803 := bstep (se 1 (by rfl) ⟨2876102, by rfl⟩ : syracuseStep 3834803 = 5752205) B5752205
theorem B2556535 : Blo 2271435 2556535 := bstep (se 1 (by rfl) ⟨1917401, by rfl⟩ : syracuseStep 2556535 = 3834803) B3834803
theorem B3408713 : Blo 2271435 3408713 := bstep (se 2 (by rfl) ⟨1278267, by rfl⟩ : syracuseStep 3408713 = 2556535) B2556535
theorem B2272475 : Blo 2271435 2272475 := bstep (se 1 (by rfl) ⟨1704356, by rfl⟩ : syracuseStep 2272475 = 3408713) B3408713
theorem B3235621 : Blo 2271435 3235621 := bbase (se 4 (by rfl) ⟨303339, by rfl⟩ : syracuseStep 3235621 = 606679) (by norm_num)
theorem B4314161 : Blo 2271435 4314161 := bstep (se 2 (by rfl) ⟨1617810, by rfl⟩ : syracuseStep 4314161 = 3235621) B3235621
theorem B11504429 : Blo 2271435 11504429 := bstep (se 3 (by rfl) ⟨2157080, by rfl⟩ : syracuseStep 11504429 = 4314161) B4314161
theorem B7669619 : Blo 2271435 7669619 := bstep (se 1 (by rfl) ⟨5752214, by rfl⟩ : syracuseStep 7669619 = 11504429) B11504429
theorem B5113079 : Blo 2271435 5113079 := bstep (se 1 (by rfl) ⟨3834809, by rfl⟩ : syracuseStep 5113079 = 7669619) B7669619
theorem B3408719 : Blo 2271435 3408719 := bstep (se 1 (by rfl) ⟨2556539, by rfl⟩ : syracuseStep 3408719 = 5113079) B5113079
theorem B2272479 : Blo 2271435 2272479 := bstep (se 1 (by rfl) ⟨1704359, by rfl⟩ : syracuseStep 2272479 = 3408719) B3408719
theorem B3408725 : Blo 2271435 3408725 := bbase (se 9 (by rfl) ⟨9986, by rfl⟩ : syracuseStep 3408725 = 19973) (by norm_num)
theorem B2272483 : Blo 2271435 2272483 := bstep (se 1 (by rfl) ⟨1704362, by rfl⟩ : syracuseStep 2272483 = 3408725) B3408725
theorem B8190197 : Blo 2271435 8190197 := bbase (se 5 (by rfl) ⟨383915, by rfl⟩ : syracuseStep 8190197 = 767831) (by norm_num)
theorem B5460131 : Blo 2271435 5460131 := bstep (se 1 (by rfl) ⟨4095098, by rfl⟩ : syracuseStep 5460131 = 8190197) B8190197
theorem B3640087 : Blo 2271435 3640087 := bstep (se 1 (by rfl) ⟨2730065, by rfl⟩ : syracuseStep 3640087 = 5460131) B5460131
theorem B4853449 : Blo 2271435 4853449 := bstep (se 2 (by rfl) ⟨1820043, by rfl⟩ : syracuseStep 4853449 = 3640087) B3640087
theorem B6471265 : Blo 2271435 6471265 := bstep (se 2 (by rfl) ⟨2426724, by rfl⟩ : syracuseStep 6471265 = 4853449) B4853449
theorem B8628353 : Blo 2271435 8628353 := bstep (se 2 (by rfl) ⟨3235632, by rfl⟩ : syracuseStep 8628353 = 6471265) B6471265
theorem B5752235 : Blo 2271435 5752235 := bstep (se 1 (by rfl) ⟨4314176, by rfl⟩ : syracuseStep 5752235 = 8628353) B8628353
theorem B3834823 : Blo 2271435 3834823 := bstep (se 1 (by rfl) ⟨2876117, by rfl⟩ : syracuseStep 3834823 = 5752235) B5752235
theorem B5113097 : Blo 2271435 5113097 := bstep (se 2 (by rfl) ⟨1917411, by rfl⟩ : syracuseStep 5113097 = 3834823) B3834823
theorem B3408731 : Blo 2271435 3408731 := bstep (se 1 (by rfl) ⟨2556548, by rfl⟩ : syracuseStep 3408731 = 5113097) B5113097
theorem B2272487 : Blo 2271435 2272487 := bstep (se 1 (by rfl) ⟨1704365, by rfl⟩ : syracuseStep 2272487 = 3408731) B3408731
theorem B2556553 : Blo 2271435 2556553 := bbase (se 2 (by rfl) ⟨958707, by rfl⟩ : syracuseStep 2556553 = 1917415) (by norm_num)
theorem B3408737 : Blo 2271435 3408737 := bstep (se 2 (by rfl) ⟨1278276, by rfl⟩ : syracuseStep 3408737 = 2556553) B2556553
theorem B2272491 : Blo 2271435 2272491 := bstep (se 1 (by rfl) ⟨1704368, by rfl⟩ : syracuseStep 2272491 = 3408737) B3408737
theorem B2527421 : Blo 2271435 2527421 := bbase (se 3 (by rfl) ⟨473891, by rfl⟩ : syracuseStep 2527421 = 947783) (by norm_num)
theorem B6739789 : Blo 2271435 6739789 := bstep (se 3 (by rfl) ⟨1263710, by rfl⟩ : syracuseStep 6739789 = 2527421) B2527421
theorem B8986385 : Blo 2271435 8986385 := bstep (se 2 (by rfl) ⟨3369894, by rfl⟩ : syracuseStep 8986385 = 6739789) B6739789
theorem B5990923 : Blo 2271435 5990923 := bstep (se 1 (by rfl) ⟨4493192, by rfl⟩ : syracuseStep 5990923 = 8986385) B8986385
theorem B7987897 : Blo 2271435 7987897 := bstep (se 2 (by rfl) ⟨2995461, by rfl⟩ : syracuseStep 7987897 = 5990923) B5990923
theorem B10650529 : Blo 2271435 10650529 := bstep (se 2 (by rfl) ⟨3993948, by rfl⟩ : syracuseStep 10650529 = 7987897) B7987897
theorem B14200705 : Blo 2271435 14200705 := bstep (se 2 (by rfl) ⟨5325264, by rfl⟩ : syracuseStep 14200705 = 10650529) B10650529
theorem B18934273 : Blo 2271435 18934273 := bstep (se 2 (by rfl) ⟨7100352, by rfl⟩ : syracuseStep 18934273 = 14200705) B14200705
theorem B25245697 : Blo 2271435 25245697 := bstep (se 2 (by rfl) ⟨9467136, by rfl⟩ : syracuseStep 25245697 = 18934273) B18934273
theorem B33660929 : Blo 2271435 33660929 := bstep (se 2 (by rfl) ⟨12622848, by rfl⟩ : syracuseStep 33660929 = 25245697) B25245697
theorem B22440619 : Blo 2271435 22440619 := bstep (se 1 (by rfl) ⟨16830464, by rfl⟩ : syracuseStep 22440619 = 33660929) B33660929
theorem B29920825 : Blo 2271435 29920825 := bstep (se 2 (by rfl) ⟨11220309, by rfl⟩ : syracuseStep 29920825 = 22440619) B22440619
theorem B39894433 : Blo 2271435 39894433 := bstep (se 2 (by rfl) ⟨14960412, by rfl⟩ : syracuseStep 39894433 = 29920825) B29920825
theorem B212770309 : Blo 2271435 212770309 := bstep (se 4 (by rfl) ⟨19947216, by rfl⟩ : syracuseStep 212770309 = 39894433) B39894433
theorem B283693745 : Blo 2271435 283693745 := bstep (se 2 (by rfl) ⟨106385154, by rfl⟩ : syracuseStep 283693745 = 212770309) B212770309
theorem B189129163 : Blo 2271435 189129163 := bstep (se 1 (by rfl) ⟨141846872, by rfl⟩ : syracuseStep 189129163 = 283693745) B283693745
theorem B252172217 : Blo 2271435 252172217 := bstep (se 2 (by rfl) ⟨94564581, by rfl⟩ : syracuseStep 252172217 = 189129163) B189129163
theorem B168114811 : Blo 2271435 168114811 := bstep (se 1 (by rfl) ⟨126086108, by rfl⟩ : syracuseStep 168114811 = 252172217) B252172217
theorem B224153081 : Blo 2271435 224153081 := bstep (se 2 (by rfl) ⟨84057405, by rfl⟩ : syracuseStep 224153081 = 168114811) B168114811
theorem B149435387 : Blo 2271435 149435387 := bstep (se 1 (by rfl) ⟨112076540, by rfl⟩ : syracuseStep 149435387 = 224153081) B224153081
theorem B99623591 : Blo 2271435 99623591 := bstep (se 1 (by rfl) ⟨74717693, by rfl⟩ : syracuseStep 99623591 = 149435387) B149435387
theorem B66415727 : Blo 2271435 66415727 := bstep (se 1 (by rfl) ⟨49811795, by rfl⟩ : syracuseStep 66415727 = 99623591) B99623591
theorem B44277151 : Blo 2271435 44277151 := bstep (se 1 (by rfl) ⟨33207863, by rfl⟩ : syracuseStep 44277151 = 66415727) B66415727
theorem B59036201 : Blo 2271435 59036201 := bstep (se 2 (by rfl) ⟨22138575, by rfl⟩ : syracuseStep 59036201 = 44277151) B44277151
theorem B39357467 : Blo 2271435 39357467 := bstep (se 1 (by rfl) ⟨29518100, by rfl⟩ : syracuseStep 39357467 = 59036201) B59036201
theorem B26238311 : Blo 2271435 26238311 := bstep (se 1 (by rfl) ⟨19678733, by rfl⟩ : syracuseStep 26238311 = 39357467) B39357467
theorem B17492207 : Blo 2271435 17492207 := bstep (se 1 (by rfl) ⟨13119155, by rfl⟩ : syracuseStep 17492207 = 26238311) B26238311
theorem B46645885 : Blo 2271435 46645885 := bstep (se 3 (by rfl) ⟨8746103, by rfl⟩ : syracuseStep 46645885 = 17492207) B17492207
theorem B248778053 : Blo 2271435 248778053 := bstep (se 4 (by rfl) ⟨23322942, by rfl⟩ : syracuseStep 248778053 = 46645885) B46645885
theorem B165852035 : Blo 2271435 165852035 := bstep (se 1 (by rfl) ⟨124389026, by rfl⟩ : syracuseStep 165852035 = 248778053) B248778053
theorem B110568023 : Blo 2271435 110568023 := bstep (se 1 (by rfl) ⟨82926017, by rfl⟩ : syracuseStep 110568023 = 165852035) B165852035
theorem B73712015 : Blo 2271435 73712015 := bstep (se 1 (by rfl) ⟨55284011, by rfl⟩ : syracuseStep 73712015 = 110568023) B110568023
theorem B49141343 : Blo 2271435 49141343 := bstep (se 1 (by rfl) ⟨36856007, by rfl⟩ : syracuseStep 49141343 = 73712015) B73712015
theorem B32760895 : Blo 2271435 32760895 := bstep (se 1 (by rfl) ⟨24570671, by rfl⟩ : syracuseStep 32760895 = 49141343) B49141343
theorem B43681193 : Blo 2271435 43681193 := bstep (se 2 (by rfl) ⟨16380447, by rfl⟩ : syracuseStep 43681193 = 32760895) B32760895
theorem B29120795 : Blo 2271435 29120795 := bstep (se 1 (by rfl) ⟨21840596, by rfl⟩ : syracuseStep 29120795 = 43681193) B43681193
theorem B19413863 : Blo 2271435 19413863 := bstep (se 1 (by rfl) ⟨14560397, by rfl⟩ : syracuseStep 19413863 = 29120795) B29120795
theorem B12942575 : Blo 2271435 12942575 := bstep (se 1 (by rfl) ⟨9706931, by rfl⟩ : syracuseStep 12942575 = 19413863) B19413863
theorem B8628383 : Blo 2271435 8628383 := bstep (se 1 (by rfl) ⟨6471287, by rfl⟩ : syracuseStep 8628383 = 12942575) B12942575
theorem B5752255 : Blo 2271435 5752255 := bstep (se 1 (by rfl) ⟨4314191, by rfl⟩ : syracuseStep 5752255 = 8628383) B8628383
theorem B7669673 : Blo 2271435 7669673 := bstep (se 2 (by rfl) ⟨2876127, by rfl⟩ : syracuseStep 7669673 = 5752255) B5752255
theorem B5113115 : Blo 2271435 5113115 := bstep (se 1 (by rfl) ⟨3834836, by rfl⟩ : syracuseStep 5113115 = 7669673) B7669673
theorem B3408743 : Blo 2271435 3408743 := bstep (se 1 (by rfl) ⟨2556557, by rfl⟩ : syracuseStep 3408743 = 5113115) B5113115
theorem B2272495 : Blo 2271435 2272495 := bstep (se 1 (by rfl) ⟨1704371, by rfl⟩ : syracuseStep 2272495 = 3408743) B3408743
theorem B3408749 : Blo 2271435 3408749 := bbase (se 3 (by rfl) ⟨639140, by rfl⟩ : syracuseStep 3408749 = 1278281) (by norm_num)
theorem B2272499 : Blo 2271435 2272499 := bstep (se 1 (by rfl) ⟨1704374, by rfl⟩ : syracuseStep 2272499 = 3408749) B3408749
theorem B5113133 : Blo 2271435 5113133 := bbase (se 3 (by rfl) ⟨958712, by rfl⟩ : syracuseStep 5113133 = 1917425) (by norm_num)
theorem B3408755 : Blo 2271435 3408755 := bstep (se 1 (by rfl) ⟨2556566, by rfl⟩ : syracuseStep 3408755 = 5113133) B5113133
theorem B2272503 : Blo 2271435 2272503 := bstep (se 1 (by rfl) ⟨1704377, by rfl⟩ : syracuseStep 2272503 = 3408755) B3408755
theorem B4373077 : Blo 2271435 4373077 := bbase (se 8 (by rfl) ⟨25623, by rfl⟩ : syracuseStep 4373077 = 51247) (by norm_num)
theorem B5830769 : Blo 2271435 5830769 := bstep (se 2 (by rfl) ⟨2186538, by rfl⟩ : syracuseStep 5830769 = 4373077) B4373077
theorem B3887179 : Blo 2271435 3887179 := bstep (se 1 (by rfl) ⟨2915384, by rfl⟩ : syracuseStep 3887179 = 5830769) B5830769
theorem B20731621 : Blo 2271435 20731621 := bstep (se 4 (by rfl) ⟨1943589, by rfl⟩ : syracuseStep 20731621 = 3887179) B3887179
theorem B27642161 : Blo 2271435 27642161 := bstep (se 2 (by rfl) ⟨10365810, by rfl⟩ : syracuseStep 27642161 = 20731621) B20731621
theorem B18428107 : Blo 2271435 18428107 := bstep (se 1 (by rfl) ⟨13821080, by rfl⟩ : syracuseStep 18428107 = 27642161) B27642161
theorem B24570809 : Blo 2271435 24570809 := bstep (se 2 (by rfl) ⟨9214053, by rfl⟩ : syracuseStep 24570809 = 18428107) B18428107
theorem B16380539 : Blo 2271435 16380539 := bstep (se 1 (by rfl) ⟨12285404, by rfl⟩ : syracuseStep 16380539 = 24570809) B24570809
theorem B10920359 : Blo 2271435 10920359 := bstep (se 1 (by rfl) ⟨8190269, by rfl⟩ : syracuseStep 10920359 = 16380539) B16380539
theorem B7280239 : Blo 2271435 7280239 := bstep (se 1 (by rfl) ⟨5460179, by rfl⟩ : syracuseStep 7280239 = 10920359) B10920359
theorem B9706985 : Blo 2271435 9706985 := bstep (se 2 (by rfl) ⟨3640119, by rfl⟩ : syracuseStep 9706985 = 7280239) B7280239
theorem B6471323 : Blo 2271435 6471323 := bstep (se 1 (by rfl) ⟨4853492, by rfl⟩ : syracuseStep 6471323 = 9706985) B9706985
theorem B4314215 : Blo 2271435 4314215 := bstep (se 1 (by rfl) ⟨3235661, by rfl⟩ : syracuseStep 4314215 = 6471323) B6471323
theorem B2876143 : Blo 2271435 2876143 := bstep (se 1 (by rfl) ⟨2157107, by rfl⟩ : syracuseStep 2876143 = 4314215) B4314215
theorem B3834857 : Blo 2271435 3834857 := bstep (se 2 (by rfl) ⟨1438071, by rfl⟩ : syracuseStep 3834857 = 2876143) B2876143
theorem B2556571 : Blo 2271435 2556571 := bstep (se 1 (by rfl) ⟨1917428, by rfl⟩ : syracuseStep 2556571 = 3834857) B3834857
theorem B3408761 : Blo 2271435 3408761 := bstep (se 2 (by rfl) ⟨1278285, by rfl⟩ : syracuseStep 3408761 = 2556571) B2556571
theorem B2272507 : Blo 2271435 2272507 := bstep (se 1 (by rfl) ⟨1704380, by rfl⟩ : syracuseStep 2272507 = 3408761) B3408761
theorem B2915389 : Blo 2271435 2915389 := bbase (se 3 (by rfl) ⟨546635, by rfl⟩ : syracuseStep 2915389 = 1093271) (by norm_num)
theorem B3887185 : Blo 2271435 3887185 := bstep (se 2 (by rfl) ⟨1457694, by rfl⟩ : syracuseStep 3887185 = 2915389) B2915389
theorem B5182913 : Blo 2271435 5182913 := bstep (se 2 (by rfl) ⟨1943592, by rfl⟩ : syracuseStep 5182913 = 3887185) B3887185
theorem B13821101 : Blo 2271435 13821101 := bstep (se 3 (by rfl) ⟨2591456, by rfl⟩ : syracuseStep 13821101 = 5182913) B5182913
theorem B9214067 : Blo 2271435 9214067 := bstep (se 1 (by rfl) ⟨6910550, by rfl⟩ : syracuseStep 9214067 = 13821101) B13821101
theorem B6142711 : Blo 2271435 6142711 := bstep (se 1 (by rfl) ⟨4607033, by rfl⟩ : syracuseStep 6142711 = 9214067) B9214067
theorem B8190281 : Blo 2271435 8190281 := bstep (se 2 (by rfl) ⟨3071355, by rfl⟩ : syracuseStep 8190281 = 6142711) B6142711
theorem B21840749 : Blo 2271435 21840749 := bstep (se 3 (by rfl) ⟨4095140, by rfl⟩ : syracuseStep 21840749 = 8190281) B8190281
theorem B14560499 : Blo 2271435 14560499 := bstep (se 1 (by rfl) ⟨10920374, by rfl⟩ : syracuseStep 14560499 = 21840749) B21840749
theorem B38827997 : Blo 2271435 38827997 := bstep (se 3 (by rfl) ⟨7280249, by rfl⟩ : syracuseStep 38827997 = 14560499) B14560499
theorem B25885331 : Blo 2271435 25885331 := bstep (se 1 (by rfl) ⟨19413998, by rfl⟩ : syracuseStep 25885331 = 38827997) B38827997
theorem B17256887 : Blo 2271435 17256887 := bstep (se 1 (by rfl) ⟨12942665, by rfl⟩ : syracuseStep 17256887 = 25885331) B25885331
theorem B11504591 : Blo 2271435 11504591 := bstep (se 1 (by rfl) ⟨8628443, by rfl⟩ : syracuseStep 11504591 = 17256887) B17256887
theorem B7669727 : Blo 2271435 7669727 := bstep (se 1 (by rfl) ⟨5752295, by rfl⟩ : syracuseStep 7669727 = 11504591) B11504591
theorem B5113151 : Blo 2271435 5113151 := bstep (se 1 (by rfl) ⟨3834863, by rfl⟩ : syracuseStep 5113151 = 7669727) B7669727
theorem B3408767 : Blo 2271435 3408767 := bstep (se 1 (by rfl) ⟨2556575, by rfl⟩ : syracuseStep 3408767 = 5113151) B5113151
theorem B2272511 : Blo 2271435 2272511 := bstep (se 1 (by rfl) ⟨1704383, by rfl⟩ : syracuseStep 2272511 = 3408767) B3408767
theorem B3408773 : Blo 2271435 3408773 := bbase (se 4 (by rfl) ⟨319572, by rfl⟩ : syracuseStep 3408773 = 639145) (by norm_num)
theorem B2272515 : Blo 2271435 2272515 := bstep (se 1 (by rfl) ⟨1704386, by rfl⟩ : syracuseStep 2272515 = 3408773) B3408773
theorem B3834877 : Blo 2271435 3834877 := bbase (se 3 (by rfl) ⟨719039, by rfl⟩ : syracuseStep 3834877 = 1438079) (by norm_num)
theorem B5113169 : Blo 2271435 5113169 := bstep (se 2 (by rfl) ⟨1917438, by rfl⟩ : syracuseStep 5113169 = 3834877) B3834877
theorem B3408779 : Blo 2271435 3408779 := bstep (se 1 (by rfl) ⟨2556584, by rfl⟩ : syracuseStep 3408779 = 5113169) B5113169
theorem B2272519 : Blo 2271435 2272519 := bstep (se 1 (by rfl) ⟨1704389, by rfl⟩ : syracuseStep 2272519 = 3408779) B3408779
theorem B2556589 : Blo 2271435 2556589 := bbase (se 3 (by rfl) ⟨479360, by rfl⟩ : syracuseStep 2556589 = 958721) (by norm_num)
theorem B3408785 : Blo 2271435 3408785 := bstep (se 2 (by rfl) ⟨1278294, by rfl⟩ : syracuseStep 3408785 = 2556589) B2556589
theorem B2272523 : Blo 2271435 2272523 := bstep (se 1 (by rfl) ⟨1704392, by rfl⟩ : syracuseStep 2272523 = 3408785) B3408785
theorem B7669781 : Blo 2271435 7669781 := bbase (se 6 (by rfl) ⟨179760, by rfl⟩ : syracuseStep 7669781 = 359521) (by norm_num)
theorem B5113187 : Blo 2271435 5113187 := bstep (se 1 (by rfl) ⟨3834890, by rfl⟩ : syracuseStep 5113187 = 7669781) B7669781
theorem B3408791 : Blo 2271435 3408791 := bstep (se 1 (by rfl) ⟨2556593, by rfl⟩ : syracuseStep 3408791 = 5113187) B5113187
theorem B2272527 : Blo 2271435 2272527 := bstep (se 1 (by rfl) ⟨1704395, by rfl⟩ : syracuseStep 2272527 = 3408791) B3408791
theorem B3408797 : Blo 2271435 3408797 := bbase (se 3 (by rfl) ⟨639149, by rfl⟩ : syracuseStep 3408797 = 1278299) (by norm_num)
theorem B2272531 : Blo 2271435 2272531 := bstep (se 1 (by rfl) ⟨1704398, by rfl⟩ : syracuseStep 2272531 = 3408797) B3408797
theorem B5113205 : Blo 2271435 5113205 := bbase (se 5 (by rfl) ⟨239681, by rfl⟩ : syracuseStep 5113205 = 479363) (by norm_num)
theorem B3408803 : Blo 2271435 3408803 := bstep (se 1 (by rfl) ⟨2556602, by rfl⟩ : syracuseStep 3408803 = 5113205) B5113205
theorem B2272535 : Blo 2271435 2272535 := bstep (se 1 (by rfl) ⟨1704401, by rfl⟩ : syracuseStep 2272535 = 3408803) B3408803
theorem B2915425 : Blo 2271435 2915425 := bbase (se 2 (by rfl) ⟨1093284, by rfl⟩ : syracuseStep 2915425 = 2186569) (by norm_num)
theorem B3887233 : Blo 2271435 3887233 := bstep (se 2 (by rfl) ⟨1457712, by rfl⟩ : syracuseStep 3887233 = 2915425) B2915425
theorem B82927637 : Blo 2271435 82927637 := bstep (se 6 (by rfl) ⟨1943616, by rfl⟩ : syracuseStep 82927637 = 3887233) B3887233
theorem B55285091 : Blo 2271435 55285091 := bstep (se 1 (by rfl) ⟨41463818, by rfl⟩ : syracuseStep 55285091 = 82927637) B82927637
theorem B36856727 : Blo 2271435 36856727 := bstep (se 1 (by rfl) ⟨27642545, by rfl⟩ : syracuseStep 36856727 = 55285091) B55285091
theorem B24571151 : Blo 2271435 24571151 := bstep (se 1 (by rfl) ⟨18428363, by rfl⟩ : syracuseStep 24571151 = 36856727) B36856727
theorem B16380767 : Blo 2271435 16380767 := bstep (se 1 (by rfl) ⟨12285575, by rfl⟩ : syracuseStep 16380767 = 24571151) B24571151
theorem B10920511 : Blo 2271435 10920511 := bstep (se 1 (by rfl) ⟨8190383, by rfl⟩ : syracuseStep 10920511 = 16380767) B16380767
theorem B14560681 : Blo 2271435 14560681 := bstep (se 2 (by rfl) ⟨5460255, by rfl⟩ : syracuseStep 14560681 = 10920511) B10920511
theorem B19414241 : Blo 2271435 19414241 := bstep (se 2 (by rfl) ⟨7280340, by rfl⟩ : syracuseStep 19414241 = 14560681) B14560681
theorem B12942827 : Blo 2271435 12942827 := bstep (se 1 (by rfl) ⟨9707120, by rfl⟩ : syracuseStep 12942827 = 19414241) B19414241
theorem B8628551 : Blo 2271435 8628551 := bstep (se 1 (by rfl) ⟨6471413, by rfl⟩ : syracuseStep 8628551 = 12942827) B12942827
theorem B5752367 : Blo 2271435 5752367 := bstep (se 1 (by rfl) ⟨4314275, by rfl⟩ : syracuseStep 5752367 = 8628551) B8628551
theorem B3834911 : Blo 2271435 3834911 := bstep (se 1 (by rfl) ⟨2876183, by rfl⟩ : syracuseStep 3834911 = 5752367) B5752367
theorem B2556607 : Blo 2271435 2556607 := bstep (se 1 (by rfl) ⟨1917455, by rfl⟩ : syracuseStep 2556607 = 3834911) B3834911
theorem B3408809 : Blo 2271435 3408809 := bstep (se 2 (by rfl) ⟨1278303, by rfl⟩ : syracuseStep 3408809 = 2556607) B2556607
theorem B2272539 : Blo 2271435 2272539 := bstep (se 1 (by rfl) ⟨1704404, by rfl⟩ : syracuseStep 2272539 = 3408809) B3408809
theorem B8628565 : Blo 2271435 8628565 := bbase (se 10 (by rfl) ⟨12639, by rfl⟩ : syracuseStep 8628565 = 25279) (by norm_num)
theorem B11504753 : Blo 2271435 11504753 := bstep (se 2 (by rfl) ⟨4314282, by rfl⟩ : syracuseStep 11504753 = 8628565) B8628565
theorem B7669835 : Blo 2271435 7669835 := bstep (se 1 (by rfl) ⟨5752376, by rfl⟩ : syracuseStep 7669835 = 11504753) B11504753
theorem B5113223 : Blo 2271435 5113223 := bstep (se 1 (by rfl) ⟨3834917, by rfl⟩ : syracuseStep 5113223 = 7669835) B7669835
theorem B3408815 : Blo 2271435 3408815 := bstep (se 1 (by rfl) ⟨2556611, by rfl⟩ : syracuseStep 3408815 = 5113223) B5113223
theorem B2272543 : Blo 2271435 2272543 := bstep (se 1 (by rfl) ⟨1704407, by rfl⟩ : syracuseStep 2272543 = 3408815) B3408815
theorem B3408821 : Blo 2271435 3408821 := bbase (se 5 (by rfl) ⟨159788, by rfl⟩ : syracuseStep 3408821 = 319577) (by norm_num)
theorem B2272547 : Blo 2271435 2272547 := bstep (se 1 (by rfl) ⟨1704410, by rfl⟩ : syracuseStep 2272547 = 3408821) B3408821
theorem B5752397 : Blo 2271435 5752397 := bbase (se 3 (by rfl) ⟨1078574, by rfl⟩ : syracuseStep 5752397 = 2157149) (by norm_num)
theorem B3834931 : Blo 2271435 3834931 := bstep (se 1 (by rfl) ⟨2876198, by rfl⟩ : syracuseStep 3834931 = 5752397) B5752397
theorem B5113241 : Blo 2271435 5113241 := bstep (se 2 (by rfl) ⟨1917465, by rfl⟩ : syracuseStep 5113241 = 3834931) B3834931
theorem B3408827 : Blo 2271435 3408827 := bstep (se 1 (by rfl) ⟨2556620, by rfl⟩ : syracuseStep 3408827 = 5113241) B5113241
theorem B2272551 : Blo 2271435 2272551 := bstep (se 1 (by rfl) ⟨1704413, by rfl⟩ : syracuseStep 2272551 = 3408827) B3408827
theorem B2556625 : Blo 2271435 2556625 := bbase (se 2 (by rfl) ⟨958734, by rfl⟩ : syracuseStep 2556625 = 1917469) (by norm_num)
theorem B3408833 : Blo 2271435 3408833 := bstep (se 2 (by rfl) ⟨1278312, by rfl⟩ : syracuseStep 3408833 = 2556625) B2556625
theorem B2272555 : Blo 2271435 2272555 := bstep (se 1 (by rfl) ⟨1704416, by rfl⟩ : syracuseStep 2272555 = 3408833) B3408833
theorem B7280405 : Blo 2271435 7280405 := bbase (se 6 (by rfl) ⟨170634, by rfl⟩ : syracuseStep 7280405 = 341269) (by norm_num)
theorem B4853603 : Blo 2271435 4853603 := bstep (se 1 (by rfl) ⟨3640202, by rfl⟩ : syracuseStep 4853603 = 7280405) B7280405
theorem B3235735 : Blo 2271435 3235735 := bstep (se 1 (by rfl) ⟨2426801, by rfl⟩ : syracuseStep 3235735 = 4853603) B4853603
theorem B4314313 : Blo 2271435 4314313 := bstep (se 2 (by rfl) ⟨1617867, by rfl⟩ : syracuseStep 4314313 = 3235735) B3235735
theorem B5752417 : Blo 2271435 5752417 := bstep (se 2 (by rfl) ⟨2157156, by rfl⟩ : syracuseStep 5752417 = 4314313) B4314313
theorem B7669889 : Blo 2271435 7669889 := bstep (se 2 (by rfl) ⟨2876208, by rfl⟩ : syracuseStep 7669889 = 5752417) B5752417
theorem B5113259 : Blo 2271435 5113259 := bstep (se 1 (by rfl) ⟨3834944, by rfl⟩ : syracuseStep 5113259 = 7669889) B7669889
theorem B3408839 : Blo 2271435 3408839 := bstep (se 1 (by rfl) ⟨2556629, by rfl⟩ : syracuseStep 3408839 = 5113259) B5113259
theorem B2272559 : Blo 2271435 2272559 := bstep (se 1 (by rfl) ⟨1704419, by rfl⟩ : syracuseStep 2272559 = 3408839) B3408839
theorem B3408845 : Blo 2271435 3408845 := bbase (se 3 (by rfl) ⟨639158, by rfl⟩ : syracuseStep 3408845 = 1278317) (by norm_num)
theorem B2272563 : Blo 2271435 2272563 := bstep (se 1 (by rfl) ⟨1704422, by rfl⟩ : syracuseStep 2272563 = 3408845) B3408845
theorem B5113277 : Blo 2271435 5113277 := bbase (se 3 (by rfl) ⟨958739, by rfl⟩ : syracuseStep 5113277 = 1917479) (by norm_num)
theorem B3408851 : Blo 2271435 3408851 := bstep (se 1 (by rfl) ⟨2556638, by rfl⟩ : syracuseStep 3408851 = 5113277) B5113277
theorem B2272567 : Blo 2271435 2272567 := bstep (se 1 (by rfl) ⟨1704425, by rfl⟩ : syracuseStep 2272567 = 3408851) B3408851
theorem B3834965 : Blo 2271435 3834965 := bbase (se 8 (by rfl) ⟨22470, by rfl⟩ : syracuseStep 3834965 = 44941) (by norm_num)
theorem B2556643 : Blo 2271435 2556643 := bstep (se 1 (by rfl) ⟨1917482, by rfl⟩ : syracuseStep 2556643 = 3834965) B3834965
theorem B3408857 : Blo 2271435 3408857 := bstep (se 2 (by rfl) ⟨1278321, by rfl⟩ : syracuseStep 3408857 = 2556643) B2556643
theorem B2272571 : Blo 2271435 2272571 := bstep (se 1 (by rfl) ⟨1704428, by rfl⟩ : syracuseStep 2272571 = 3408857) B3408857
theorem B9839717 : Blo 2271435 9839717 := bbase (se 4 (by rfl) ⟨922473, by rfl⟩ : syracuseStep 9839717 = 1844947) (by norm_num)
theorem B6559811 : Blo 2271435 6559811 := bstep (se 1 (by rfl) ⟨4919858, by rfl⟩ : syracuseStep 6559811 = 9839717) B9839717
theorem B4373207 : Blo 2271435 4373207 := bstep (se 1 (by rfl) ⟨3279905, by rfl⟩ : syracuseStep 4373207 = 6559811) B6559811
theorem B2915471 : Blo 2271435 2915471 := bstep (se 1 (by rfl) ⟨2186603, by rfl⟩ : syracuseStep 2915471 = 4373207) B4373207
theorem B7774589 : Blo 2271435 7774589 := bstep (se 3 (by rfl) ⟨1457735, by rfl⟩ : syracuseStep 7774589 = 2915471) B2915471
theorem B20732237 : Blo 2271435 20732237 := bstep (se 3 (by rfl) ⟨3887294, by rfl⟩ : syracuseStep 20732237 = 7774589) B7774589
theorem B13821491 : Blo 2271435 13821491 := bstep (se 1 (by rfl) ⟨10366118, by rfl⟩ : syracuseStep 13821491 = 20732237) B20732237
theorem B9214327 : Blo 2271435 9214327 := bstep (se 1 (by rfl) ⟨6910745, by rfl⟩ : syracuseStep 9214327 = 13821491) B13821491
theorem B12285769 : Blo 2271435 12285769 := bstep (se 2 (by rfl) ⟨4607163, by rfl⟩ : syracuseStep 12285769 = 9214327) B9214327
theorem B16381025 : Blo 2271435 16381025 := bstep (se 2 (by rfl) ⟨6142884, by rfl⟩ : syracuseStep 16381025 = 12285769) B12285769
theorem B10920683 : Blo 2271435 10920683 := bstep (se 1 (by rfl) ⟨8190512, by rfl⟩ : syracuseStep 10920683 = 16381025) B16381025
theorem B7280455 : Blo 2271435 7280455 := bstep (se 1 (by rfl) ⟨5460341, by rfl⟩ : syracuseStep 7280455 = 10920683) B10920683
theorem B9707273 : Blo 2271435 9707273 := bstep (se 2 (by rfl) ⟨3640227, by rfl⟩ : syracuseStep 9707273 = 7280455) B7280455
theorem B6471515 : Blo 2271435 6471515 := bstep (se 1 (by rfl) ⟨4853636, by rfl⟩ : syracuseStep 6471515 = 9707273) B9707273
theorem B17257373 : Blo 2271435 17257373 := bstep (se 3 (by rfl) ⟨3235757, by rfl⟩ : syracuseStep 17257373 = 6471515) B6471515
theorem B11504915 : Blo 2271435 11504915 := bstep (se 1 (by rfl) ⟨8628686, by rfl⟩ : syracuseStep 11504915 = 17257373) B17257373
theorem B7669943 : Blo 2271435 7669943 := bstep (se 1 (by rfl) ⟨5752457, by rfl⟩ : syracuseStep 7669943 = 11504915) B11504915
theorem B5113295 : Blo 2271435 5113295 := bstep (se 1 (by rfl) ⟨3834971, by rfl⟩ : syracuseStep 5113295 = 7669943) B7669943
theorem B3408863 : Blo 2271435 3408863 := bstep (se 1 (by rfl) ⟨2556647, by rfl⟩ : syracuseStep 3408863 = 5113295) B5113295
theorem B2272575 : Blo 2271435 2272575 := bstep (se 1 (by rfl) ⟨1704431, by rfl⟩ : syracuseStep 2272575 = 3408863) B3408863
theorem B3408869 : Blo 2271435 3408869 := bbase (se 4 (by rfl) ⟨319581, by rfl⟩ : syracuseStep 3408869 = 639163) (by norm_num)
theorem B2272579 : Blo 2271435 2272579 := bstep (se 1 (by rfl) ⟨1704434, by rfl⟩ : syracuseStep 2272579 = 3408869) B3408869
theorem B2730181 : Blo 2271435 2730181 := bbase (se 4 (by rfl) ⟨255954, by rfl⟩ : syracuseStep 2730181 = 511909) (by norm_num)
theorem B3640241 : Blo 2271435 3640241 := bstep (se 2 (by rfl) ⟨1365090, by rfl⟩ : syracuseStep 3640241 = 2730181) B2730181
theorem B9707309 : Blo 2271435 9707309 := bstep (se 3 (by rfl) ⟨1820120, by rfl⟩ : syracuseStep 9707309 = 3640241) B3640241
theorem B6471539 : Blo 2271435 6471539 := bstep (se 1 (by rfl) ⟨4853654, by rfl⟩ : syracuseStep 6471539 = 9707309) B9707309
theorem B4314359 : Blo 2271435 4314359 := bstep (se 1 (by rfl) ⟨3235769, by rfl⟩ : syracuseStep 4314359 = 6471539) B6471539
theorem B2876239 : Blo 2271435 2876239 := bstep (se 1 (by rfl) ⟨2157179, by rfl⟩ : syracuseStep 2876239 = 4314359) B4314359
theorem B3834985 : Blo 2271435 3834985 := bstep (se 2 (by rfl) ⟨1438119, by rfl⟩ : syracuseStep 3834985 = 2876239) B2876239
theorem B5113313 : Blo 2271435 5113313 := bstep (se 2 (by rfl) ⟨1917492, by rfl⟩ : syracuseStep 5113313 = 3834985) B3834985
theorem B3408875 : Blo 2271435 3408875 := bstep (se 1 (by rfl) ⟨2556656, by rfl⟩ : syracuseStep 3408875 = 5113313) B5113313
theorem B2272583 : Blo 2271435 2272583 := bstep (se 1 (by rfl) ⟨1704437, by rfl⟩ : syracuseStep 2272583 = 3408875) B3408875
theorem B2556661 : Blo 2271435 2556661 := bbase (se 5 (by rfl) ⟨119843, by rfl⟩ : syracuseStep 2556661 = 239687) (by norm_num)
theorem B3408881 : Blo 2271435 3408881 := bstep (se 2 (by rfl) ⟨1278330, by rfl⟩ : syracuseStep 3408881 = 2556661) B2556661
theorem B2272587 : Blo 2271435 2272587 := bstep (se 1 (by rfl) ⟨1704440, by rfl⟩ : syracuseStep 2272587 = 3408881) B3408881
theorem B2876249 : Blo 2271435 2876249 := bbase (se 2 (by rfl) ⟨1078593, by rfl⟩ : syracuseStep 2876249 = 2157187) (by norm_num)
theorem B7669997 : Blo 2271435 7669997 := bstep (se 3 (by rfl) ⟨1438124, by rfl⟩ : syracuseStep 7669997 = 2876249) B2876249
theorem B5113331 : Blo 2271435 5113331 := bstep (se 1 (by rfl) ⟨3834998, by rfl⟩ : syracuseStep 5113331 = 7669997) B7669997
theorem B3408887 : Blo 2271435 3408887 := bstep (se 1 (by rfl) ⟨2556665, by rfl⟩ : syracuseStep 3408887 = 5113331) B5113331
theorem B2272591 : Blo 2271435 2272591 := bstep (se 1 (by rfl) ⟨1704443, by rfl⟩ : syracuseStep 2272591 = 3408887) B3408887
theorem B3408893 : Blo 2271435 3408893 := bbase (se 3 (by rfl) ⟨639167, by rfl⟩ : syracuseStep 3408893 = 1278335) (by norm_num)
theorem B2272595 : Blo 2271435 2272595 := bstep (se 1 (by rfl) ⟨1704446, by rfl⟩ : syracuseStep 2272595 = 3408893) B3408893
theorem B5113349 : Blo 2271435 5113349 := bbase (se 4 (by rfl) ⟨479376, by rfl⟩ : syracuseStep 5113349 = 958753) (by norm_num)
theorem B3408899 : Blo 2271435 3408899 := bstep (se 1 (by rfl) ⟨2556674, by rfl⟩ : syracuseStep 3408899 = 5113349) B5113349
theorem B2272599 : Blo 2271435 2272599 := bstep (se 1 (by rfl) ⟨1704449, by rfl⟩ : syracuseStep 2272599 = 3408899) B3408899
theorem B4314397 : Blo 2271435 4314397 := bbase (se 3 (by rfl) ⟨808949, by rfl⟩ : syracuseStep 4314397 = 1617899) (by norm_num)
theorem B5752529 : Blo 2271435 5752529 := bstep (se 2 (by rfl) ⟨2157198, by rfl⟩ : syracuseStep 5752529 = 4314397) B4314397
theorem B3835019 : Blo 2271435 3835019 := bstep (se 1 (by rfl) ⟨2876264, by rfl⟩ : syracuseStep 3835019 = 5752529) B5752529
theorem B2556679 : Blo 2271435 2556679 := bstep (se 1 (by rfl) ⟨1917509, by rfl⟩ : syracuseStep 2556679 = 3835019) B3835019
theorem B3408905 : Blo 2271435 3408905 := bstep (se 2 (by rfl) ⟨1278339, by rfl⟩ : syracuseStep 3408905 = 2556679) B2556679
theorem B2272603 : Blo 2271435 2272603 := bstep (se 1 (by rfl) ⟨1704452, by rfl⟩ : syracuseStep 2272603 = 3408905) B3408905
theorem B11505077 : Blo 2271435 11505077 := bbase (se 5 (by rfl) ⟨539300, by rfl⟩ : syracuseStep 11505077 = 1078601) (by norm_num)
theorem B7670051 : Blo 2271435 7670051 := bstep (se 1 (by rfl) ⟨5752538, by rfl⟩ : syracuseStep 7670051 = 11505077) B11505077
theorem B5113367 : Blo 2271435 5113367 := bstep (se 1 (by rfl) ⟨3835025, by rfl⟩ : syracuseStep 5113367 = 7670051) B7670051
theorem B3408911 : Blo 2271435 3408911 := bstep (se 1 (by rfl) ⟨2556683, by rfl⟩ : syracuseStep 3408911 = 5113367) B5113367
theorem B2272607 : Blo 2271435 2272607 := bstep (se 1 (by rfl) ⟨1704455, by rfl⟩ : syracuseStep 2272607 = 3408911) B3408911
theorem B3408917 : Blo 2271435 3408917 := bbase (se 6 (by rfl) ⟨79896, by rfl⟩ : syracuseStep 3408917 = 159793) (by norm_num)
theorem B2272611 : Blo 2271435 2272611 := bstep (se 1 (by rfl) ⟨1704458, by rfl⟩ : syracuseStep 2272611 = 3408917) B3408917
theorem B5831045 : Blo 2271435 5831045 := bbase (se 4 (by rfl) ⟨546660, by rfl⟩ : syracuseStep 5831045 = 1093321) (by norm_num)
theorem B3887363 : Blo 2271435 3887363 := bstep (se 1 (by rfl) ⟨2915522, by rfl⟩ : syracuseStep 3887363 = 5831045) B5831045
theorem B10366301 : Blo 2271435 10366301 := bstep (se 3 (by rfl) ⟨1943681, by rfl⟩ : syracuseStep 10366301 = 3887363) B3887363
theorem B6910867 : Blo 2271435 6910867 := bstep (se 1 (by rfl) ⟨5183150, by rfl⟩ : syracuseStep 6910867 = 10366301) B10366301
theorem B9214489 : Blo 2271435 9214489 := bstep (se 2 (by rfl) ⟨3455433, by rfl⟩ : syracuseStep 9214489 = 6910867) B6910867
theorem B49143941 : Blo 2271435 49143941 := bstep (se 4 (by rfl) ⟨4607244, by rfl⟩ : syracuseStep 49143941 = 9214489) B9214489
theorem B32762627 : Blo 2271435 32762627 := bstep (se 1 (by rfl) ⟨24571970, by rfl⟩ : syracuseStep 32762627 = 49143941) B49143941
theorem B21841751 : Blo 2271435 21841751 := bstep (se 1 (by rfl) ⟨16381313, by rfl⟩ : syracuseStep 21841751 = 32762627) B32762627
theorem B14561167 : Blo 2271435 14561167 := bstep (se 1 (by rfl) ⟨10920875, by rfl⟩ : syracuseStep 14561167 = 21841751) B21841751
theorem B19414889 : Blo 2271435 19414889 := bstep (se 2 (by rfl) ⟨7280583, by rfl⟩ : syracuseStep 19414889 = 14561167) B14561167
theorem B12943259 : Blo 2271435 12943259 := bstep (se 1 (by rfl) ⟨9707444, by rfl⟩ : syracuseStep 12943259 = 19414889) B19414889
theorem B8628839 : Blo 2271435 8628839 := bstep (se 1 (by rfl) ⟨6471629, by rfl⟩ : syracuseStep 8628839 = 12943259) B12943259
theorem B5752559 : Blo 2271435 5752559 := bstep (se 1 (by rfl) ⟨4314419, by rfl⟩ : syracuseStep 5752559 = 8628839) B8628839
theorem B3835039 : Blo 2271435 3835039 := bstep (se 1 (by rfl) ⟨2876279, by rfl⟩ : syracuseStep 3835039 = 5752559) B5752559
theorem B5113385 : Blo 2271435 5113385 := bstep (se 2 (by rfl) ⟨1917519, by rfl⟩ : syracuseStep 5113385 = 3835039) B3835039
theorem B3408923 : Blo 2271435 3408923 := bstep (se 1 (by rfl) ⟨2556692, by rfl⟩ : syracuseStep 3408923 = 5113385) B5113385
theorem B2272615 : Blo 2271435 2272615 := bstep (se 1 (by rfl) ⟨1704461, by rfl⟩ : syracuseStep 2272615 = 3408923) B3408923
theorem B2556697 : Blo 2271435 2556697 := bbase (se 2 (by rfl) ⟨958761, by rfl⟩ : syracuseStep 2556697 = 1917523) (by norm_num)
theorem B3408929 : Blo 2271435 3408929 := bstep (se 2 (by rfl) ⟨1278348, by rfl⟩ : syracuseStep 3408929 = 2556697) B2556697
theorem B2272619 : Blo 2271435 2272619 := bstep (se 1 (by rfl) ⟨1704464, by rfl⟩ : syracuseStep 2272619 = 3408929) B3408929
theorem B8628869 : Blo 2271435 8628869 := bbase (se 4 (by rfl) ⟨808956, by rfl⟩ : syracuseStep 8628869 = 1617913) (by norm_num)
theorem B5752579 : Blo 2271435 5752579 := bstep (se 1 (by rfl) ⟨4314434, by rfl⟩ : syracuseStep 5752579 = 8628869) B8628869
theorem B7670105 : Blo 2271435 7670105 := bstep (se 2 (by rfl) ⟨2876289, by rfl⟩ : syracuseStep 7670105 = 5752579) B5752579
theorem B5113403 : Blo 2271435 5113403 := bstep (se 1 (by rfl) ⟨3835052, by rfl⟩ : syracuseStep 5113403 = 7670105) B7670105
theorem B3408935 : Blo 2271435 3408935 := bstep (se 1 (by rfl) ⟨2556701, by rfl⟩ : syracuseStep 3408935 = 5113403) B5113403
theorem B2272623 : Blo 2271435 2272623 := bstep (se 1 (by rfl) ⟨1704467, by rfl⟩ : syracuseStep 2272623 = 3408935) B3408935
theorem B3408941 : Blo 2271435 3408941 := bbase (se 3 (by rfl) ⟨639176, by rfl⟩ : syracuseStep 3408941 = 1278353) (by norm_num)
theorem B2272627 : Blo 2271435 2272627 := bstep (se 1 (by rfl) ⟨1704470, by rfl⟩ : syracuseStep 2272627 = 3408941) B3408941
theorem B5113421 : Blo 2271435 5113421 := bbase (se 3 (by rfl) ⟨958766, by rfl⟩ : syracuseStep 5113421 = 1917533) (by norm_num)
theorem B3408947 : Blo 2271435 3408947 := bstep (se 1 (by rfl) ⟨2556710, by rfl⟩ : syracuseStep 3408947 = 5113421) B5113421
theorem B2272631 : Blo 2271435 2272631 := bstep (se 1 (by rfl) ⟨1704473, by rfl⟩ : syracuseStep 2272631 = 3408947) B3408947
theorem B2876305 : Blo 2271435 2876305 := bbase (se 2 (by rfl) ⟨1078614, by rfl⟩ : syracuseStep 2876305 = 2157229) (by norm_num)
theorem B3835073 : Blo 2271435 3835073 := bstep (se 2 (by rfl) ⟨1438152, by rfl⟩ : syracuseStep 3835073 = 2876305) B2876305
theorem B2556715 : Blo 2271435 2556715 := bstep (se 1 (by rfl) ⟨1917536, by rfl⟩ : syracuseStep 2556715 = 3835073) B3835073
theorem B3408953 : Blo 2271435 3408953 := bstep (se 2 (by rfl) ⟨1278357, by rfl⟩ : syracuseStep 3408953 = 2556715) B2556715
theorem B2272635 : Blo 2271435 2272635 := bstep (se 1 (by rfl) ⟨1704476, by rfl⟩ : syracuseStep 2272635 = 3408953) B3408953
theorem B4853773 : Blo 2271435 4853773 := bbase (se 3 (by rfl) ⟨910082, by rfl⟩ : syracuseStep 4853773 = 1820165) (by norm_num)
theorem B25886789 : Blo 2271435 25886789 := bstep (se 4 (by rfl) ⟨2426886, by rfl⟩ : syracuseStep 25886789 = 4853773) B4853773
theorem B17257859 : Blo 2271435 17257859 := bstep (se 1 (by rfl) ⟨12943394, by rfl⟩ : syracuseStep 17257859 = 25886789) B25886789
theorem B11505239 : Blo 2271435 11505239 := bstep (se 1 (by rfl) ⟨8628929, by rfl⟩ : syracuseStep 11505239 = 17257859) B17257859
theorem B7670159 : Blo 2271435 7670159 := bstep (se 1 (by rfl) ⟨5752619, by rfl⟩ : syracuseStep 7670159 = 11505239) B11505239
theorem B5113439 : Blo 2271435 5113439 := bstep (se 1 (by rfl) ⟨3835079, by rfl⟩ : syracuseStep 5113439 = 7670159) B7670159
theorem B3408959 : Blo 2271435 3408959 := bstep (se 1 (by rfl) ⟨2556719, by rfl⟩ : syracuseStep 3408959 = 5113439) B5113439
theorem B2272639 : Blo 2271435 2272639 := bstep (se 1 (by rfl) ⟨1704479, by rfl⟩ : syracuseStep 2272639 = 3408959) B3408959
theorem B3408965 : Blo 2271435 3408965 := bbase (se 4 (by rfl) ⟨319590, by rfl⟩ : syracuseStep 3408965 = 639181) (by norm_num)
theorem B2272643 : Blo 2271435 2272643 := bstep (se 1 (by rfl) ⟨1704482, by rfl⟩ : syracuseStep 2272643 = 3408965) B3408965
theorem B3835093 : Blo 2271435 3835093 := bbase (se 7 (by rfl) ⟨44942, by rfl⟩ : syracuseStep 3835093 = 89885) (by norm_num)
theorem B5113457 : Blo 2271435 5113457 := bstep (se 2 (by rfl) ⟨1917546, by rfl⟩ : syracuseStep 5113457 = 3835093) B3835093
theorem B3408971 : Blo 2271435 3408971 := bstep (se 1 (by rfl) ⟨2556728, by rfl⟩ : syracuseStep 3408971 = 5113457) B5113457
theorem B2272647 : Blo 2271435 2272647 := bstep (se 1 (by rfl) ⟨1704485, by rfl⟩ : syracuseStep 2272647 = 3408971) B3408971
theorem B2556733 : Blo 2271435 2556733 := bbase (se 3 (by rfl) ⟨479387, by rfl⟩ : syracuseStep 2556733 = 958775) (by norm_num)
theorem B3408977 : Blo 2271435 3408977 := bstep (se 2 (by rfl) ⟨1278366, by rfl⟩ : syracuseStep 3408977 = 2556733) B2556733
theorem B2272651 : Blo 2271435 2272651 := bstep (se 1 (by rfl) ⟨1704488, by rfl⟩ : syracuseStep 2272651 = 3408977) B3408977
theorem B7670213 : Blo 2271435 7670213 := bbase (se 4 (by rfl) ⟨719082, by rfl⟩ : syracuseStep 7670213 = 1438165) (by norm_num)
theorem B5113475 : Blo 2271435 5113475 := bstep (se 1 (by rfl) ⟨3835106, by rfl⟩ : syracuseStep 5113475 = 7670213) B7670213
theorem B3408983 : Blo 2271435 3408983 := bstep (se 1 (by rfl) ⟨2556737, by rfl⟩ : syracuseStep 3408983 = 5113475) B5113475
theorem B2272655 : Blo 2271435 2272655 := bstep (se 1 (by rfl) ⟨1704491, by rfl⟩ : syracuseStep 2272655 = 3408983) B3408983
theorem B3408989 : Blo 2271435 3408989 := bbase (se 3 (by rfl) ⟨639185, by rfl⟩ : syracuseStep 3408989 = 1278371) (by norm_num)
theorem B2272659 : Blo 2271435 2272659 := bstep (se 1 (by rfl) ⟨1704494, by rfl⟩ : syracuseStep 2272659 = 3408989) B3408989
theorem B5113493 : Blo 2271435 5113493 := bbase (se 6 (by rfl) ⟨119847, by rfl⟩ : syracuseStep 5113493 = 239695) (by norm_num)
theorem B3408995 : Blo 2271435 3408995 := bstep (se 1 (by rfl) ⟨2556746, by rfl⟩ : syracuseStep 3408995 = 5113493) B5113493
theorem B2272663 : Blo 2271435 2272663 := bstep (se 1 (by rfl) ⟨1704497, by rfl⟩ : syracuseStep 2272663 = 3408995) B3408995
theorem B2426917 : Blo 2271435 2426917 := bbase (se 4 (by rfl) ⟨227523, by rfl⟩ : syracuseStep 2426917 = 455047) (by norm_num)
theorem B3235889 : Blo 2271435 3235889 := bstep (se 2 (by rfl) ⟨1213458, by rfl⟩ : syracuseStep 3235889 = 2426917) B2426917
theorem B8629037 : Blo 2271435 8629037 := bstep (se 3 (by rfl) ⟨1617944, by rfl⟩ : syracuseStep 8629037 = 3235889) B3235889
theorem B5752691 : Blo 2271435 5752691 := bstep (se 1 (by rfl) ⟨4314518, by rfl⟩ : syracuseStep 5752691 = 8629037) B8629037
theorem B3835127 : Blo 2271435 3835127 := bstep (se 1 (by rfl) ⟨2876345, by rfl⟩ : syracuseStep 3835127 = 5752691) B5752691
theorem B2556751 : Blo 2271435 2556751 := bstep (se 1 (by rfl) ⟨1917563, by rfl⟩ : syracuseStep 2556751 = 3835127) B3835127
theorem B3409001 : Blo 2271435 3409001 := bstep (se 2 (by rfl) ⟨1278375, by rfl⟩ : syracuseStep 3409001 = 2556751) B2556751
theorem B2272667 : Blo 2271435 2272667 := bstep (se 1 (by rfl) ⟨1704500, by rfl⟩ : syracuseStep 2272667 = 3409001) B3409001
theorem B14561525 : Blo 2271435 14561525 := bbase (se 5 (by rfl) ⟨682571, by rfl⟩ : syracuseStep 14561525 = 1365143) (by norm_num)
theorem B9707683 : Blo 2271435 9707683 := bstep (se 1 (by rfl) ⟨7280762, by rfl⟩ : syracuseStep 9707683 = 14561525) B14561525
theorem B12943577 : Blo 2271435 12943577 := bstep (se 2 (by rfl) ⟨4853841, by rfl⟩ : syracuseStep 12943577 = 9707683) B9707683
theorem B8629051 : Blo 2271435 8629051 := bstep (se 1 (by rfl) ⟨6471788, by rfl⟩ : syracuseStep 8629051 = 12943577) B12943577
theorem B11505401 : Blo 2271435 11505401 := bstep (se 2 (by rfl) ⟨4314525, by rfl⟩ : syracuseStep 11505401 = 8629051) B8629051
theorem B7670267 : Blo 2271435 7670267 := bstep (se 1 (by rfl) ⟨5752700, by rfl⟩ : syracuseStep 7670267 = 11505401) B11505401
theorem B5113511 : Blo 2271435 5113511 := bstep (se 1 (by rfl) ⟨3835133, by rfl⟩ : syracuseStep 5113511 = 7670267) B7670267
theorem B3409007 : Blo 2271435 3409007 := bstep (se 1 (by rfl) ⟨2556755, by rfl⟩ : syracuseStep 3409007 = 5113511) B5113511
theorem B2272671 : Blo 2271435 2272671 := bstep (se 1 (by rfl) ⟨1704503, by rfl⟩ : syracuseStep 2272671 = 3409007) B3409007
theorem B3409013 : Blo 2271435 3409013 := bbase (se 5 (by rfl) ⟨159797, by rfl⟩ : syracuseStep 3409013 = 319595) (by norm_num)
theorem B2272675 : Blo 2271435 2272675 := bstep (se 1 (by rfl) ⟨1704506, by rfl⟩ : syracuseStep 2272675 = 3409013) B3409013
theorem B4314541 : Blo 2271435 4314541 := bbase (se 3 (by rfl) ⟨808976, by rfl⟩ : syracuseStep 4314541 = 1617953) (by norm_num)
theorem B5752721 : Blo 2271435 5752721 := bstep (se 2 (by rfl) ⟨2157270, by rfl⟩ : syracuseStep 5752721 = 4314541) B4314541
theorem B3835147 : Blo 2271435 3835147 := bstep (se 1 (by rfl) ⟨2876360, by rfl⟩ : syracuseStep 3835147 = 5752721) B5752721
theorem B5113529 : Blo 2271435 5113529 := bstep (se 2 (by rfl) ⟨1917573, by rfl⟩ : syracuseStep 5113529 = 3835147) B3835147
theorem B3409019 : Blo 2271435 3409019 := bstep (se 1 (by rfl) ⟨2556764, by rfl⟩ : syracuseStep 3409019 = 5113529) B5113529
theorem B2272679 : Blo 2271435 2272679 := bstep (se 1 (by rfl) ⟨1704509, by rfl⟩ : syracuseStep 2272679 = 3409019) B3409019
theorem B2556769 : Blo 2271435 2556769 := bbase (se 2 (by rfl) ⟨958788, by rfl⟩ : syracuseStep 2556769 = 1917577) (by norm_num)
theorem B3409025 : Blo 2271435 3409025 := bstep (se 2 (by rfl) ⟨1278384, by rfl⟩ : syracuseStep 3409025 = 2556769) B2556769
theorem B2272683 : Blo 2271435 2272683 := bstep (se 1 (by rfl) ⟨1704512, by rfl⟩ : syracuseStep 2272683 = 3409025) B3409025
theorem B5752741 : Blo 2271435 5752741 := bbase (se 4 (by rfl) ⟨539319, by rfl⟩ : syracuseStep 5752741 = 1078639) (by norm_num)
theorem B7670321 : Blo 2271435 7670321 := bstep (se 2 (by rfl) ⟨2876370, by rfl⟩ : syracuseStep 7670321 = 5752741) B5752741
theorem B5113547 : Blo 2271435 5113547 := bstep (se 1 (by rfl) ⟨3835160, by rfl⟩ : syracuseStep 5113547 = 7670321) B7670321
theorem B3409031 : Blo 2271435 3409031 := bstep (se 1 (by rfl) ⟨2556773, by rfl⟩ : syracuseStep 3409031 = 5113547) B5113547
theorem B2272687 : Blo 2271435 2272687 := bstep (se 1 (by rfl) ⟨1704515, by rfl⟩ : syracuseStep 2272687 = 3409031) B3409031
theorem B3409037 : Blo 2271435 3409037 := bbase (se 3 (by rfl) ⟨639194, by rfl⟩ : syracuseStep 3409037 = 1278389) (by norm_num)
theorem B2272691 : Blo 2271435 2272691 := bstep (se 1 (by rfl) ⟨1704518, by rfl⟩ : syracuseStep 2272691 = 3409037) B3409037
theorem B5113565 : Blo 2271435 5113565 := bbase (se 3 (by rfl) ⟨958793, by rfl⟩ : syracuseStep 5113565 = 1917587) (by norm_num)
theorem B3409043 : Blo 2271435 3409043 := bstep (se 1 (by rfl) ⟨2556782, by rfl⟩ : syracuseStep 3409043 = 5113565) B5113565
theorem B2272695 : Blo 2271435 2272695 := bstep (se 1 (by rfl) ⟨1704521, by rfl⟩ : syracuseStep 2272695 = 3409043) B3409043
theorem B3835181 : Blo 2271435 3835181 := bbase (se 3 (by rfl) ⟨719096, by rfl⟩ : syracuseStep 3835181 = 1438193) (by norm_num)
theorem B2556787 : Blo 2271435 2556787 := bstep (se 1 (by rfl) ⟨1917590, by rfl⟩ : syracuseStep 2556787 = 3835181) B3835181
theorem B3409049 : Blo 2271435 3409049 := bstep (se 2 (by rfl) ⟨1278393, by rfl⟩ : syracuseStep 3409049 = 2556787) B2556787
theorem B2272699 : Blo 2271435 2272699 := bstep (se 1 (by rfl) ⟨1704524, by rfl⟩ : syracuseStep 2272699 = 3409049) B3409049
theorem B3370205 : Blo 2271435 3370205 := bbase (se 3 (by rfl) ⟨631913, by rfl⟩ : syracuseStep 3370205 = 1263827) (by norm_num)
theorem B8987213 : Blo 2271435 8987213 := bstep (se 3 (by rfl) ⟨1685102, by rfl⟩ : syracuseStep 8987213 = 3370205) B3370205
theorem B5991475 : Blo 2271435 5991475 := bstep (se 1 (by rfl) ⟨4493606, by rfl⟩ : syracuseStep 5991475 = 8987213) B8987213
theorem B7988633 : Blo 2271435 7988633 := bstep (se 2 (by rfl) ⟨2995737, by rfl⟩ : syracuseStep 7988633 = 5991475) B5991475
theorem B5325755 : Blo 2271435 5325755 := bstep (se 1 (by rfl) ⟨3994316, by rfl⟩ : syracuseStep 5325755 = 7988633) B7988633
theorem B14202013 : Blo 2271435 14202013 := bstep (se 3 (by rfl) ⟨2662877, by rfl⟩ : syracuseStep 14202013 = 5325755) B5325755
theorem B18936017 : Blo 2271435 18936017 := bstep (se 2 (by rfl) ⟨7101006, by rfl⟩ : syracuseStep 18936017 = 14202013) B14202013
theorem B12624011 : Blo 2271435 12624011 := bstep (se 1 (by rfl) ⟨9468008, by rfl⟩ : syracuseStep 12624011 = 18936017) B18936017
theorem B8416007 : Blo 2271435 8416007 := bstep (se 1 (by rfl) ⟨6312005, by rfl⟩ : syracuseStep 8416007 = 12624011) B12624011
theorem B5610671 : Blo 2271435 5610671 := bstep (se 1 (by rfl) ⟨4208003, by rfl⟩ : syracuseStep 5610671 = 8416007) B8416007
theorem B3740447 : Blo 2271435 3740447 := bstep (se 1 (by rfl) ⟨2805335, by rfl⟩ : syracuseStep 3740447 = 5610671) B5610671
theorem B2493631 : Blo 2271435 2493631 := bstep (se 1 (by rfl) ⟨1870223, by rfl⟩ : syracuseStep 2493631 = 3740447) B3740447
theorem B13299365 : Blo 2271435 13299365 := bstep (se 4 (by rfl) ⟨1246815, by rfl⟩ : syracuseStep 13299365 = 2493631) B2493631
theorem B35464973 : Blo 2271435 35464973 := bstep (se 3 (by rfl) ⟨6649682, by rfl⟩ : syracuseStep 35464973 = 13299365) B13299365
theorem B94573261 : Blo 2271435 94573261 := bstep (se 3 (by rfl) ⟨17732486, by rfl⟩ : syracuseStep 94573261 = 35464973) B35464973
theorem B126097681 : Blo 2271435 126097681 := bstep (se 2 (by rfl) ⟨47286630, by rfl⟩ : syracuseStep 126097681 = 94573261) B94573261
theorem B168130241 : Blo 2271435 168130241 := bstep (se 2 (by rfl) ⟨63048840, by rfl⟩ : syracuseStep 168130241 = 126097681) B126097681
theorem B112086827 : Blo 2271435 112086827 := bstep (se 1 (by rfl) ⟨84065120, by rfl⟩ : syracuseStep 112086827 = 168130241) B168130241
theorem B74724551 : Blo 2271435 74724551 := bstep (se 1 (by rfl) ⟨56043413, by rfl⟩ : syracuseStep 74724551 = 112086827) B112086827
theorem B49816367 : Blo 2271435 49816367 := bstep (se 1 (by rfl) ⟨37362275, by rfl⟩ : syracuseStep 49816367 = 74724551) B74724551
theorem B33210911 : Blo 2271435 33210911 := bstep (se 1 (by rfl) ⟨24908183, by rfl⟩ : syracuseStep 33210911 = 49816367) B49816367
theorem B88562429 : Blo 2271435 88562429 := bstep (se 3 (by rfl) ⟨16605455, by rfl⟩ : syracuseStep 88562429 = 33210911) B33210911
theorem B59041619 : Blo 2271435 59041619 := bstep (se 1 (by rfl) ⟨44281214, by rfl⟩ : syracuseStep 59041619 = 88562429) B88562429
theorem B39361079 : Blo 2271435 39361079 := bstep (se 1 (by rfl) ⟨29520809, by rfl⟩ : syracuseStep 39361079 = 59041619) B59041619
theorem B26240719 : Blo 2271435 26240719 := bstep (se 1 (by rfl) ⟨19680539, by rfl⟩ : syracuseStep 26240719 = 39361079) B39361079
theorem B34987625 : Blo 2271435 34987625 := bstep (se 2 (by rfl) ⟨13120359, by rfl⟩ : syracuseStep 34987625 = 26240719) B26240719
theorem B23325083 : Blo 2271435 23325083 := bstep (se 1 (by rfl) ⟨17493812, by rfl⟩ : syracuseStep 23325083 = 34987625) B34987625
theorem B15550055 : Blo 2271435 15550055 := bstep (se 1 (by rfl) ⟨11662541, by rfl⟩ : syracuseStep 15550055 = 23325083) B23325083
theorem B10366703 : Blo 2271435 10366703 := bstep (se 1 (by rfl) ⟨7775027, by rfl⟩ : syracuseStep 10366703 = 15550055) B15550055
theorem B6911135 : Blo 2271435 6911135 := bstep (se 1 (by rfl) ⟨5183351, by rfl⟩ : syracuseStep 6911135 = 10366703) B10366703
theorem B4607423 : Blo 2271435 4607423 := bstep (se 1 (by rfl) ⟨3455567, by rfl⟩ : syracuseStep 4607423 = 6911135) B6911135
theorem B3071615 : Blo 2271435 3071615 := bstep (se 1 (by rfl) ⟨2303711, by rfl⟩ : syracuseStep 3071615 = 4607423) B4607423
theorem B8190973 : Blo 2271435 8190973 := bstep (se 3 (by rfl) ⟨1535807, by rfl⟩ : syracuseStep 8190973 = 3071615) B3071615
theorem B43685189 : Blo 2271435 43685189 := bstep (se 4 (by rfl) ⟨4095486, by rfl⟩ : syracuseStep 43685189 = 8190973) B8190973
theorem B29123459 : Blo 2271435 29123459 := bstep (se 1 (by rfl) ⟨21842594, by rfl⟩ : syracuseStep 29123459 = 43685189) B43685189
theorem B19415639 : Blo 2271435 19415639 := bstep (se 1 (by rfl) ⟨14561729, by rfl⟩ : syracuseStep 19415639 = 29123459) B29123459
theorem B12943759 : Blo 2271435 12943759 := bstep (se 1 (by rfl) ⟨9707819, by rfl⟩ : syracuseStep 12943759 = 19415639) B19415639
theorem B17258345 : Blo 2271435 17258345 := bstep (se 2 (by rfl) ⟨6471879, by rfl⟩ : syracuseStep 17258345 = 12943759) B12943759
theorem B11505563 : Blo 2271435 11505563 := bstep (se 1 (by rfl) ⟨8629172, by rfl⟩ : syracuseStep 11505563 = 17258345) B17258345
theorem B7670375 : Blo 2271435 7670375 := bstep (se 1 (by rfl) ⟨5752781, by rfl⟩ : syracuseStep 7670375 = 11505563) B11505563
theorem B5113583 : Blo 2271435 5113583 := bstep (se 1 (by rfl) ⟨3835187, by rfl⟩ : syracuseStep 5113583 = 7670375) B7670375
theorem B3409055 : Blo 2271435 3409055 := bstep (se 1 (by rfl) ⟨2556791, by rfl⟩ : syracuseStep 3409055 = 5113583) B5113583
theorem B2272703 : Blo 2271435 2272703 := bstep (se 1 (by rfl) ⟨1704527, by rfl⟩ : syracuseStep 2272703 = 3409055) B3409055
theorem B3409061 : Blo 2271435 3409061 := bbase (se 4 (by rfl) ⟨319599, by rfl⟩ : syracuseStep 3409061 = 639199) (by norm_num)
theorem B2272707 : Blo 2271435 2272707 := bstep (se 1 (by rfl) ⟨1704530, by rfl⟩ : syracuseStep 2272707 = 3409061) B3409061
theorem B2876401 : Blo 2271435 2876401 := bbase (se 2 (by rfl) ⟨1078650, by rfl⟩ : syracuseStep 2876401 = 2157301) (by norm_num)
theorem B3835201 : Blo 2271435 3835201 := bstep (se 2 (by rfl) ⟨1438200, by rfl⟩ : syracuseStep 3835201 = 2876401) B2876401
theorem B5113601 : Blo 2271435 5113601 := bstep (se 2 (by rfl) ⟨1917600, by rfl⟩ : syracuseStep 5113601 = 3835201) B3835201
theorem B3409067 : Blo 2271435 3409067 := bstep (se 1 (by rfl) ⟨2556800, by rfl⟩ : syracuseStep 3409067 = 5113601) B5113601
theorem B2272711 : Blo 2271435 2272711 := bstep (se 1 (by rfl) ⟨1704533, by rfl⟩ : syracuseStep 2272711 = 3409067) B3409067
theorem B2556805 : Blo 2271435 2556805 := bbase (se 4 (by rfl) ⟨239700, by rfl⟩ : syracuseStep 2556805 = 479401) (by norm_num)
theorem B3409073 : Blo 2271435 3409073 := bstep (se 2 (by rfl) ⟨1278402, by rfl⟩ : syracuseStep 3409073 = 2556805) B2556805
theorem B2272715 : Blo 2271435 2272715 := bstep (se 1 (by rfl) ⟨1704536, by rfl⟩ : syracuseStep 2272715 = 3409073) B3409073
theorem B4095517 : Blo 2271435 4095517 := bbase (se 3 (by rfl) ⟨767909, by rfl⟩ : syracuseStep 4095517 = 1535819) (by norm_num)
theorem B5460689 : Blo 2271435 5460689 := bstep (se 2 (by rfl) ⟨2047758, by rfl⟩ : syracuseStep 5460689 = 4095517) B4095517
theorem B3640459 : Blo 2271435 3640459 := bstep (se 1 (by rfl) ⟨2730344, by rfl⟩ : syracuseStep 3640459 = 5460689) B5460689
theorem B4853945 : Blo 2271435 4853945 := bstep (se 2 (by rfl) ⟨1820229, by rfl⟩ : syracuseStep 4853945 = 3640459) B3640459
theorem B3235963 : Blo 2271435 3235963 := bstep (se 1 (by rfl) ⟨2426972, by rfl⟩ : syracuseStep 3235963 = 4853945) B4853945
theorem B4314617 : Blo 2271435 4314617 := bstep (se 2 (by rfl) ⟨1617981, by rfl⟩ : syracuseStep 4314617 = 3235963) B3235963
theorem B2876411 : Blo 2271435 2876411 := bstep (se 1 (by rfl) ⟨2157308, by rfl⟩ : syracuseStep 2876411 = 4314617) B4314617
theorem B7670429 : Blo 2271435 7670429 := bstep (se 3 (by rfl) ⟨1438205, by rfl⟩ : syracuseStep 7670429 = 2876411) B2876411
theorem B5113619 : Blo 2271435 5113619 := bstep (se 1 (by rfl) ⟨3835214, by rfl⟩ : syracuseStep 5113619 = 7670429) B7670429
theorem B3409079 : Blo 2271435 3409079 := bstep (se 1 (by rfl) ⟨2556809, by rfl⟩ : syracuseStep 3409079 = 5113619) B5113619
theorem B2272719 : Blo 2271435 2272719 := bstep (se 1 (by rfl) ⟨1704539, by rfl⟩ : syracuseStep 2272719 = 3409079) B3409079
theorem B3409085 : Blo 2271435 3409085 := bbase (se 3 (by rfl) ⟨639203, by rfl⟩ : syracuseStep 3409085 = 1278407) (by norm_num)
theorem B2272723 : Blo 2271435 2272723 := bstep (se 1 (by rfl) ⟨1704542, by rfl⟩ : syracuseStep 2272723 = 3409085) B3409085
theorem B5113637 : Blo 2271435 5113637 := bbase (se 4 (by rfl) ⟨479403, by rfl⟩ : syracuseStep 5113637 = 958807) (by norm_num)
theorem B3409091 : Blo 2271435 3409091 := bstep (se 1 (by rfl) ⟨2556818, by rfl⟩ : syracuseStep 3409091 = 5113637) B5113637
theorem B2272727 : Blo 2271435 2272727 := bstep (se 1 (by rfl) ⟨1704545, by rfl⟩ : syracuseStep 2272727 = 3409091) B3409091
theorem B5752853 : Blo 2271435 5752853 := bbase (se 6 (by rfl) ⟨134832, by rfl⟩ : syracuseStep 5752853 = 269665) (by norm_num)
theorem B3835235 : Blo 2271435 3835235 := bstep (se 1 (by rfl) ⟨2876426, by rfl⟩ : syracuseStep 3835235 = 5752853) B5752853
theorem B2556823 : Blo 2271435 2556823 := bstep (se 1 (by rfl) ⟨1917617, by rfl⟩ : syracuseStep 2556823 = 3835235) B3835235
theorem B3409097 : Blo 2271435 3409097 := bstep (se 2 (by rfl) ⟨1278411, by rfl⟩ : syracuseStep 3409097 = 2556823) B2556823
theorem B2272731 : Blo 2271435 2272731 := bstep (se 1 (by rfl) ⟨1704548, by rfl⟩ : syracuseStep 2272731 = 3409097) B3409097
theorem B9707957 : Blo 2271435 9707957 := bbase (se 5 (by rfl) ⟨455060, by rfl⟩ : syracuseStep 9707957 = 910121) (by norm_num)
theorem B6471971 : Blo 2271435 6471971 := bstep (se 1 (by rfl) ⟨4853978, by rfl⟩ : syracuseStep 6471971 = 9707957) B9707957
theorem B4314647 : Blo 2271435 4314647 := bstep (se 1 (by rfl) ⟨3235985, by rfl⟩ : syracuseStep 4314647 = 6471971) B6471971
theorem B11505725 : Blo 2271435 11505725 := bstep (se 3 (by rfl) ⟨2157323, by rfl⟩ : syracuseStep 11505725 = 4314647) B4314647
theorem B7670483 : Blo 2271435 7670483 := bstep (se 1 (by rfl) ⟨5752862, by rfl⟩ : syracuseStep 7670483 = 11505725) B11505725
theorem B5113655 : Blo 2271435 5113655 := bstep (se 1 (by rfl) ⟨3835241, by rfl⟩ : syracuseStep 5113655 = 7670483) B7670483
theorem B3409103 : Blo 2271435 3409103 := bstep (se 1 (by rfl) ⟨2556827, by rfl⟩ : syracuseStep 3409103 = 5113655) B5113655
theorem B2272735 : Blo 2271435 2272735 := bstep (se 1 (by rfl) ⟨1704551, by rfl⟩ : syracuseStep 2272735 = 3409103) B3409103
theorem B3409109 : Blo 2271435 3409109 := bbase (se 7 (by rfl) ⟨39950, by rfl⟩ : syracuseStep 3409109 = 79901) (by norm_num)
theorem B2272739 : Blo 2271435 2272739 := bstep (se 1 (by rfl) ⟨1704554, by rfl⟩ : syracuseStep 2272739 = 3409109) B3409109
theorem B3235997 : Blo 2271435 3235997 := bbase (se 3 (by rfl) ⟨606749, by rfl⟩ : syracuseStep 3235997 = 1213499) (by norm_num)
theorem B8629325 : Blo 2271435 8629325 := bstep (se 3 (by rfl) ⟨1617998, by rfl⟩ : syracuseStep 8629325 = 3235997) B3235997
theorem B5752883 : Blo 2271435 5752883 := bstep (se 1 (by rfl) ⟨4314662, by rfl⟩ : syracuseStep 5752883 = 8629325) B8629325
theorem B3835255 : Blo 2271435 3835255 := bstep (se 1 (by rfl) ⟨2876441, by rfl⟩ : syracuseStep 3835255 = 5752883) B5752883
theorem B5113673 : Blo 2271435 5113673 := bstep (se 2 (by rfl) ⟨1917627, by rfl⟩ : syracuseStep 5113673 = 3835255) B3835255
theorem B3409115 : Blo 2271435 3409115 := bstep (se 1 (by rfl) ⟨2556836, by rfl⟩ : syracuseStep 3409115 = 5113673) B5113673
theorem B2272743 : Blo 2271435 2272743 := bstep (se 1 (by rfl) ⟨1704557, by rfl⟩ : syracuseStep 2272743 = 3409115) B3409115
theorem B2556841 : Blo 2271435 2556841 := bbase (se 2 (by rfl) ⟨958815, by rfl⟩ : syracuseStep 2556841 = 1917631) (by norm_num)
theorem B3409121 : Blo 2271435 3409121 := bstep (se 2 (by rfl) ⟨1278420, by rfl⟩ : syracuseStep 3409121 = 2556841) B2556841
theorem B2272747 : Blo 2271435 2272747 := bstep (se 1 (by rfl) ⟨1704560, by rfl⟩ : syracuseStep 2272747 = 3409121) B3409121
theorem B5183461 : Blo 2271435 5183461 := bbase (se 4 (by rfl) ⟨485949, by rfl⟩ : syracuseStep 5183461 = 971899) (by norm_num)
theorem B6911281 : Blo 2271435 6911281 := bstep (se 2 (by rfl) ⟨2591730, by rfl⟩ : syracuseStep 6911281 = 5183461) B5183461
theorem B9215041 : Blo 2271435 9215041 := bstep (se 2 (by rfl) ⟨3455640, by rfl⟩ : syracuseStep 9215041 = 6911281) B6911281
theorem B12286721 : Blo 2271435 12286721 := bstep (se 2 (by rfl) ⟨4607520, by rfl⟩ : syracuseStep 12286721 = 9215041) B9215041
theorem B8191147 : Blo 2271435 8191147 := bstep (se 1 (by rfl) ⟨6143360, by rfl⟩ : syracuseStep 8191147 = 12286721) B12286721
theorem B10921529 : Blo 2271435 10921529 := bstep (se 2 (by rfl) ⟨4095573, by rfl⟩ : syracuseStep 10921529 = 8191147) B8191147
theorem B7281019 : Blo 2271435 7281019 := bstep (se 1 (by rfl) ⟨5460764, by rfl⟩ : syracuseStep 7281019 = 10921529) B10921529
theorem B9708025 : Blo 2271435 9708025 := bstep (se 2 (by rfl) ⟨3640509, by rfl⟩ : syracuseStep 9708025 = 7281019) B7281019
theorem B12944033 : Blo 2271435 12944033 := bstep (se 2 (by rfl) ⟨4854012, by rfl⟩ : syracuseStep 12944033 = 9708025) B9708025
theorem B8629355 : Blo 2271435 8629355 := bstep (se 1 (by rfl) ⟨6472016, by rfl⟩ : syracuseStep 8629355 = 12944033) B12944033
theorem B5752903 : Blo 2271435 5752903 := bstep (se 1 (by rfl) ⟨4314677, by rfl⟩ : syracuseStep 5752903 = 8629355) B8629355
theorem B7670537 : Blo 2271435 7670537 := bstep (se 2 (by rfl) ⟨2876451, by rfl⟩ : syracuseStep 7670537 = 5752903) B5752903
theorem B5113691 : Blo 2271435 5113691 := bstep (se 1 (by rfl) ⟨3835268, by rfl⟩ : syracuseStep 5113691 = 7670537) B7670537
theorem B3409127 : Blo 2271435 3409127 := bstep (se 1 (by rfl) ⟨2556845, by rfl⟩ : syracuseStep 3409127 = 5113691) B5113691
theorem B2272751 : Blo 2271435 2272751 := bstep (se 1 (by rfl) ⟨1704563, by rfl⟩ : syracuseStep 2272751 = 3409127) B3409127
theorem B3409133 : Blo 2271435 3409133 := bbase (se 3 (by rfl) ⟨639212, by rfl⟩ : syracuseStep 3409133 = 1278425) (by norm_num)
theorem B2272755 : Blo 2271435 2272755 := bstep (se 1 (by rfl) ⟨1704566, by rfl⟩ : syracuseStep 2272755 = 3409133) B3409133
theorem B5113709 : Blo 2271435 5113709 := bbase (se 3 (by rfl) ⟨958820, by rfl⟩ : syracuseStep 5113709 = 1917641) (by norm_num)
theorem B3409139 : Blo 2271435 3409139 := bstep (se 1 (by rfl) ⟨2556854, by rfl⟩ : syracuseStep 3409139 = 5113709) B5113709
theorem B2272759 : Blo 2271435 2272759 := bstep (se 1 (by rfl) ⟨1704569, by rfl⟩ : syracuseStep 2272759 = 3409139) B3409139
theorem B4314701 : Blo 2271435 4314701 := bbase (se 3 (by rfl) ⟨809006, by rfl⟩ : syracuseStep 4314701 = 1618013) (by norm_num)
theorem B2876467 : Blo 2271435 2876467 := bstep (se 1 (by rfl) ⟨2157350, by rfl⟩ : syracuseStep 2876467 = 4314701) B4314701
theorem B3835289 : Blo 2271435 3835289 := bstep (se 2 (by rfl) ⟨1438233, by rfl⟩ : syracuseStep 3835289 = 2876467) B2876467
theorem B2556859 : Blo 2271435 2556859 := bstep (se 1 (by rfl) ⟨1917644, by rfl⟩ : syracuseStep 2556859 = 3835289) B3835289
theorem B3409145 : Blo 2271435 3409145 := bstep (se 2 (by rfl) ⟨1278429, by rfl⟩ : syracuseStep 3409145 = 2556859) B2556859
theorem B2272763 : Blo 2271435 2272763 := bstep (se 1 (by rfl) ⟨1704572, by rfl⟩ : syracuseStep 2272763 = 3409145) B3409145
theorem B6227221 : Blo 2271435 6227221 := bbase (se 6 (by rfl) ⟨145950, by rfl⟩ : syracuseStep 6227221 = 291901) (by norm_num)
theorem B8302961 : Blo 2271435 8302961 := bstep (se 2 (by rfl) ⟨3113610, by rfl⟩ : syracuseStep 8302961 = 6227221) B6227221
theorem B5535307 : Blo 2271435 5535307 := bstep (se 1 (by rfl) ⟨4151480, by rfl⟩ : syracuseStep 5535307 = 8302961) B8302961
theorem B7380409 : Blo 2271435 7380409 := bstep (se 2 (by rfl) ⟨2767653, by rfl⟩ : syracuseStep 7380409 = 5535307) B5535307
theorem B9840545 : Blo 2271435 9840545 := bstep (se 2 (by rfl) ⟨3690204, by rfl⟩ : syracuseStep 9840545 = 7380409) B7380409
theorem B6560363 : Blo 2271435 6560363 := bstep (se 1 (by rfl) ⟨4920272, by rfl⟩ : syracuseStep 6560363 = 9840545) B9840545
theorem B17494301 : Blo 2271435 17494301 := bstep (se 3 (by rfl) ⟨3280181, by rfl⟩ : syracuseStep 17494301 = 6560363) B6560363
theorem B11662867 : Blo 2271435 11662867 := bstep (se 1 (by rfl) ⟨8747150, by rfl⟩ : syracuseStep 11662867 = 17494301) B17494301
theorem B15550489 : Blo 2271435 15550489 := bstep (se 2 (by rfl) ⟨5831433, by rfl⟩ : syracuseStep 15550489 = 11662867) B11662867
theorem B20733985 : Blo 2271435 20733985 := bstep (se 2 (by rfl) ⟨7775244, by rfl⟩ : syracuseStep 20733985 = 15550489) B15550489
theorem B27645313 : Blo 2271435 27645313 := bstep (se 2 (by rfl) ⟨10366992, by rfl⟩ : syracuseStep 27645313 = 20733985) B20733985
theorem B36860417 : Blo 2271435 36860417 := bstep (se 2 (by rfl) ⟨13822656, by rfl⟩ : syracuseStep 36860417 = 27645313) B27645313
theorem B24573611 : Blo 2271435 24573611 := bstep (se 1 (by rfl) ⟨18430208, by rfl⟩ : syracuseStep 24573611 = 36860417) B36860417
theorem B16382407 : Blo 2271435 16382407 := bstep (se 1 (by rfl) ⟨12286805, by rfl⟩ : syracuseStep 16382407 = 24573611) B24573611
theorem B21843209 : Blo 2271435 21843209 := bstep (se 2 (by rfl) ⟨8191203, by rfl⟩ : syracuseStep 21843209 = 16382407) B16382407
theorem B58248557 : Blo 2271435 58248557 := bstep (se 3 (by rfl) ⟨10921604, by rfl⟩ : syracuseStep 58248557 = 21843209) B21843209
theorem B38832371 : Blo 2271435 38832371 := bstep (se 1 (by rfl) ⟨29124278, by rfl⟩ : syracuseStep 38832371 = 58248557) B58248557
theorem B25888247 : Blo 2271435 25888247 := bstep (se 1 (by rfl) ⟨19416185, by rfl⟩ : syracuseStep 25888247 = 38832371) B38832371
theorem B17258831 : Blo 2271435 17258831 := bstep (se 1 (by rfl) ⟨12944123, by rfl⟩ : syracuseStep 17258831 = 25888247) B25888247
theorem B11505887 : Blo 2271435 11505887 := bstep (se 1 (by rfl) ⟨8629415, by rfl⟩ : syracuseStep 11505887 = 17258831) B17258831
theorem B7670591 : Blo 2271435 7670591 := bstep (se 1 (by rfl) ⟨5752943, by rfl⟩ : syracuseStep 7670591 = 11505887) B11505887
theorem B5113727 : Blo 2271435 5113727 := bstep (se 1 (by rfl) ⟨3835295, by rfl⟩ : syracuseStep 5113727 = 7670591) B7670591
theorem B3409151 : Blo 2271435 3409151 := bstep (se 1 (by rfl) ⟨2556863, by rfl⟩ : syracuseStep 3409151 = 5113727) B5113727
theorem B2272767 : Blo 2271435 2272767 := bstep (se 1 (by rfl) ⟨1704575, by rfl⟩ : syracuseStep 2272767 = 3409151) B3409151
theorem B3409157 : Blo 2271435 3409157 := bbase (se 4 (by rfl) ⟨319608, by rfl⟩ : syracuseStep 3409157 = 639217) (by norm_num)
theorem B2272771 : Blo 2271435 2272771 := bstep (se 1 (by rfl) ⟨1704578, by rfl⟩ : syracuseStep 2272771 = 3409157) B3409157
theorem B3835309 : Blo 2271435 3835309 := bbase (se 3 (by rfl) ⟨719120, by rfl⟩ : syracuseStep 3835309 = 1438241) (by norm_num)
theorem B5113745 : Blo 2271435 5113745 := bstep (se 2 (by rfl) ⟨1917654, by rfl⟩ : syracuseStep 5113745 = 3835309) B3835309
theorem B3409163 : Blo 2271435 3409163 := bstep (se 1 (by rfl) ⟨2556872, by rfl⟩ : syracuseStep 3409163 = 5113745) B5113745
theorem B2272775 : Blo 2271435 2272775 := bstep (se 1 (by rfl) ⟨1704581, by rfl⟩ : syracuseStep 2272775 = 3409163) B3409163
theorem B2556877 : Blo 2271435 2556877 := bbase (se 3 (by rfl) ⟨479414, by rfl⟩ : syracuseStep 2556877 = 958829) (by norm_num)
theorem B3409169 : Blo 2271435 3409169 := bstep (se 2 (by rfl) ⟨1278438, by rfl⟩ : syracuseStep 3409169 = 2556877) B2556877
theorem B2272779 : Blo 2271435 2272779 := bstep (se 1 (by rfl) ⟨1704584, by rfl⟩ : syracuseStep 2272779 = 3409169) B3409169
theorem B7670645 : Blo 2271435 7670645 := bbase (se 5 (by rfl) ⟨359561, by rfl⟩ : syracuseStep 7670645 = 719123) (by norm_num)
theorem B5113763 : Blo 2271435 5113763 := bstep (se 1 (by rfl) ⟨3835322, by rfl⟩ : syracuseStep 5113763 = 7670645) B7670645
theorem B3409175 : Blo 2271435 3409175 := bstep (se 1 (by rfl) ⟨2556881, by rfl⟩ : syracuseStep 3409175 = 5113763) B5113763
theorem B2272783 : Blo 2271435 2272783 := bstep (se 1 (by rfl) ⟨1704587, by rfl⟩ : syracuseStep 2272783 = 3409175) B3409175
theorem B3409181 : Blo 2271435 3409181 := bbase (se 3 (by rfl) ⟨639221, by rfl⟩ : syracuseStep 3409181 = 1278443) (by norm_num)
theorem B2272787 : Blo 2271435 2272787 := bstep (se 1 (by rfl) ⟨1704590, by rfl⟩ : syracuseStep 2272787 = 3409181) B3409181
theorem B5113781 : Blo 2271435 5113781 := bbase (se 5 (by rfl) ⟨239708, by rfl⟩ : syracuseStep 5113781 = 479417) (by norm_num)
theorem B3409187 : Blo 2271435 3409187 := bstep (se 1 (by rfl) ⟨2556890, by rfl⟩ : syracuseStep 3409187 = 5113781) B5113781
theorem B2272791 : Blo 2271435 2272791 := bstep (se 1 (by rfl) ⟨1704593, by rfl⟩ : syracuseStep 2272791 = 3409187) B3409187
theorem B9215221 : Blo 2271435 9215221 := bbase (se 5 (by rfl) ⟨431963, by rfl⟩ : syracuseStep 9215221 = 863927) (by norm_num)
theorem B12286961 : Blo 2271435 12286961 := bstep (se 2 (by rfl) ⟨4607610, by rfl⟩ : syracuseStep 12286961 = 9215221) B9215221
theorem B8191307 : Blo 2271435 8191307 := bstep (se 1 (by rfl) ⟨6143480, by rfl⟩ : syracuseStep 8191307 = 12286961) B12286961
theorem B5460871 : Blo 2271435 5460871 := bstep (se 1 (by rfl) ⟨4095653, by rfl⟩ : syracuseStep 5460871 = 8191307) B8191307
theorem B7281161 : Blo 2271435 7281161 := bstep (se 2 (by rfl) ⟨2730435, by rfl⟩ : syracuseStep 7281161 = 5460871) B5460871
theorem B4854107 : Blo 2271435 4854107 := bstep (se 1 (by rfl) ⟨3640580, by rfl⟩ : syracuseStep 4854107 = 7281161) B7281161
theorem B12944285 : Blo 2271435 12944285 := bstep (se 3 (by rfl) ⟨2427053, by rfl⟩ : syracuseStep 12944285 = 4854107) B4854107
theorem B8629523 : Blo 2271435 8629523 := bstep (se 1 (by rfl) ⟨6472142, by rfl⟩ : syracuseStep 8629523 = 12944285) B12944285
theorem B5753015 : Blo 2271435 5753015 := bstep (se 1 (by rfl) ⟨4314761, by rfl⟩ : syracuseStep 5753015 = 8629523) B8629523
theorem B3835343 : Blo 2271435 3835343 := bstep (se 1 (by rfl) ⟨2876507, by rfl⟩ : syracuseStep 3835343 = 5753015) B5753015
theorem B2556895 : Blo 2271435 2556895 := bstep (se 1 (by rfl) ⟨1917671, by rfl⟩ : syracuseStep 2556895 = 3835343) B3835343
theorem B3409193 : Blo 2271435 3409193 := bstep (se 2 (by rfl) ⟨1278447, by rfl⟩ : syracuseStep 3409193 = 2556895) B2556895
theorem B2272795 : Blo 2271435 2272795 := bstep (se 1 (by rfl) ⟨1704596, by rfl⟩ : syracuseStep 2272795 = 3409193) B3409193
theorem B7281173 : Blo 2271435 7281173 := bbase (se 6 (by rfl) ⟨170652, by rfl⟩ : syracuseStep 7281173 = 341305) (by norm_num)
theorem B4854115 : Blo 2271435 4854115 := bstep (se 1 (by rfl) ⟨3640586, by rfl⟩ : syracuseStep 4854115 = 7281173) B7281173
theorem B6472153 : Blo 2271435 6472153 := bstep (se 2 (by rfl) ⟨2427057, by rfl⟩ : syracuseStep 6472153 = 4854115) B4854115
theorem B8629537 : Blo 2271435 8629537 := bstep (se 2 (by rfl) ⟨3236076, by rfl⟩ : syracuseStep 8629537 = 6472153) B6472153
theorem B11506049 : Blo 2271435 11506049 := bstep (se 2 (by rfl) ⟨4314768, by rfl⟩ : syracuseStep 11506049 = 8629537) B8629537
theorem B7670699 : Blo 2271435 7670699 := bstep (se 1 (by rfl) ⟨5753024, by rfl⟩ : syracuseStep 7670699 = 11506049) B11506049
theorem B5113799 : Blo 2271435 5113799 := bstep (se 1 (by rfl) ⟨3835349, by rfl⟩ : syracuseStep 5113799 = 7670699) B7670699
theorem B3409199 : Blo 2271435 3409199 := bstep (se 1 (by rfl) ⟨2556899, by rfl⟩ : syracuseStep 3409199 = 5113799) B5113799
theorem B2272799 : Blo 2271435 2272799 := bstep (se 1 (by rfl) ⟨1704599, by rfl⟩ : syracuseStep 2272799 = 3409199) B3409199
theorem B3409205 : Blo 2271435 3409205 := bbase (se 5 (by rfl) ⟨159806, by rfl⟩ : syracuseStep 3409205 = 319613) (by norm_num)
theorem B2272803 : Blo 2271435 2272803 := bstep (se 1 (by rfl) ⟨1704602, by rfl⟩ : syracuseStep 2272803 = 3409205) B3409205
theorem B5753045 : Blo 2271435 5753045 := bbase (se 7 (by rfl) ⟨67418, by rfl⟩ : syracuseStep 5753045 = 134837) (by norm_num)
theorem B3835363 : Blo 2271435 3835363 := bstep (se 1 (by rfl) ⟨2876522, by rfl⟩ : syracuseStep 3835363 = 5753045) B5753045
theorem B5113817 : Blo 2271435 5113817 := bstep (se 2 (by rfl) ⟨1917681, by rfl⟩ : syracuseStep 5113817 = 3835363) B3835363
theorem B3409211 : Blo 2271435 3409211 := bstep (se 1 (by rfl) ⟨2556908, by rfl⟩ : syracuseStep 3409211 = 5113817) B5113817
theorem B2272807 : Blo 2271435 2272807 := bstep (se 1 (by rfl) ⟨1704605, by rfl⟩ : syracuseStep 2272807 = 3409211) B3409211
theorem B2556913 : Blo 2271435 2556913 := bbase (se 2 (by rfl) ⟨958842, by rfl⟩ : syracuseStep 2556913 = 1917685) (by norm_num)
theorem B3409217 : Blo 2271435 3409217 := bstep (se 2 (by rfl) ⟨1278456, by rfl⟩ : syracuseStep 3409217 = 2556913) B2556913
theorem B2272811 : Blo 2271435 2272811 := bstep (se 1 (by rfl) ⟨1704608, by rfl⟩ : syracuseStep 2272811 = 3409217) B3409217
theorem B6911477 : Blo 2271435 6911477 := bbase (se 5 (by rfl) ⟨323975, by rfl⟩ : syracuseStep 6911477 = 647951) (by norm_num)
theorem B4607651 : Blo 2271435 4607651 := bstep (se 1 (by rfl) ⟨3455738, by rfl⟩ : syracuseStep 4607651 = 6911477) B6911477
theorem B3071767 : Blo 2271435 3071767 := bstep (se 1 (by rfl) ⟨2303825, by rfl⟩ : syracuseStep 3071767 = 4607651) B4607651
theorem B4095689 : Blo 2271435 4095689 := bstep (se 2 (by rfl) ⟨1535883, by rfl⟩ : syracuseStep 4095689 = 3071767) B3071767
theorem B10921837 : Blo 2271435 10921837 := bstep (se 3 (by rfl) ⟨2047844, by rfl⟩ : syracuseStep 10921837 = 4095689) B4095689
theorem B14562449 : Blo 2271435 14562449 := bstep (se 2 (by rfl) ⟨5460918, by rfl⟩ : syracuseStep 14562449 = 10921837) B10921837
theorem B9708299 : Blo 2271435 9708299 := bstep (se 1 (by rfl) ⟨7281224, by rfl⟩ : syracuseStep 9708299 = 14562449) B14562449
theorem B6472199 : Blo 2271435 6472199 := bstep (se 1 (by rfl) ⟨4854149, by rfl⟩ : syracuseStep 6472199 = 9708299) B9708299
theorem B4314799 : Blo 2271435 4314799 := bstep (se 1 (by rfl) ⟨3236099, by rfl⟩ : syracuseStep 4314799 = 6472199) B6472199
theorem B5753065 : Blo 2271435 5753065 := bstep (se 2 (by rfl) ⟨2157399, by rfl⟩ : syracuseStep 5753065 = 4314799) B4314799
theorem B7670753 : Blo 2271435 7670753 := bstep (se 2 (by rfl) ⟨2876532, by rfl⟩ : syracuseStep 7670753 = 5753065) B5753065
theorem B5113835 : Blo 2271435 5113835 := bstep (se 1 (by rfl) ⟨3835376, by rfl⟩ : syracuseStep 5113835 = 7670753) B7670753
theorem B3409223 : Blo 2271435 3409223 := bstep (se 1 (by rfl) ⟨2556917, by rfl⟩ : syracuseStep 3409223 = 5113835) B5113835
theorem B2272815 : Blo 2271435 2272815 := bstep (se 1 (by rfl) ⟨1704611, by rfl⟩ : syracuseStep 2272815 = 3409223) B3409223
theorem B3409229 : Blo 2271435 3409229 := bbase (se 3 (by rfl) ⟨639230, by rfl⟩ : syracuseStep 3409229 = 1278461) (by norm_num)
theorem B2272819 : Blo 2271435 2272819 := bstep (se 1 (by rfl) ⟨1704614, by rfl⟩ : syracuseStep 2272819 = 3409229) B3409229
theorem B5113853 : Blo 2271435 5113853 := bbase (se 3 (by rfl) ⟨958847, by rfl⟩ : syracuseStep 5113853 = 1917695) (by norm_num)
theorem B3409235 : Blo 2271435 3409235 := bstep (se 1 (by rfl) ⟨2556926, by rfl⟩ : syracuseStep 3409235 = 5113853) B5113853
theorem B2272823 : Blo 2271435 2272823 := bstep (se 1 (by rfl) ⟨1704617, by rfl⟩ : syracuseStep 2272823 = 3409235) B3409235
theorem B3835397 : Blo 2271435 3835397 := bbase (se 4 (by rfl) ⟨359568, by rfl⟩ : syracuseStep 3835397 = 719137) (by norm_num)
theorem B2556931 : Blo 2271435 2556931 := bstep (se 1 (by rfl) ⟨1917698, by rfl⟩ : syracuseStep 2556931 = 3835397) B3835397
theorem B3409241 : Blo 2271435 3409241 := bstep (se 2 (by rfl) ⟨1278465, by rfl⟩ : syracuseStep 3409241 = 2556931) B2556931
theorem B2272827 : Blo 2271435 2272827 := bstep (se 1 (by rfl) ⟨1704620, by rfl⟩ : syracuseStep 2272827 = 3409241) B3409241
theorem B17259317 : Blo 2271435 17259317 := bbase (se 5 (by rfl) ⟨809030, by rfl⟩ : syracuseStep 17259317 = 1618061) (by norm_num)
theorem B11506211 : Blo 2271435 11506211 := bstep (se 1 (by rfl) ⟨8629658, by rfl⟩ : syracuseStep 11506211 = 17259317) B17259317
theorem B7670807 : Blo 2271435 7670807 := bstep (se 1 (by rfl) ⟨5753105, by rfl⟩ : syracuseStep 7670807 = 11506211) B11506211
theorem B5113871 : Blo 2271435 5113871 := bstep (se 1 (by rfl) ⟨3835403, by rfl⟩ : syracuseStep 5113871 = 7670807) B7670807
theorem B3409247 : Blo 2271435 3409247 := bstep (se 1 (by rfl) ⟨2556935, by rfl⟩ : syracuseStep 3409247 = 5113871) B5113871
theorem B2272831 : Blo 2271435 2272831 := bstep (se 1 (by rfl) ⟨1704623, by rfl⟩ : syracuseStep 2272831 = 3409247) B3409247
theorem B3409253 : Blo 2271435 3409253 := bbase (se 4 (by rfl) ⟨319617, by rfl⟩ : syracuseStep 3409253 = 639235) (by norm_num)
theorem B2272835 : Blo 2271435 2272835 := bstep (se 1 (by rfl) ⟨1704626, by rfl⟩ : syracuseStep 2272835 = 3409253) B3409253
theorem B4314845 : Blo 2271435 4314845 := bbase (se 3 (by rfl) ⟨809033, by rfl⟩ : syracuseStep 4314845 = 1618067) (by norm_num)
theorem B2876563 : Blo 2271435 2876563 := bstep (se 1 (by rfl) ⟨2157422, by rfl⟩ : syracuseStep 2876563 = 4314845) B4314845
theorem B3835417 : Blo 2271435 3835417 := bstep (se 2 (by rfl) ⟨1438281, by rfl⟩ : syracuseStep 3835417 = 2876563) B2876563
theorem B5113889 : Blo 2271435 5113889 := bstep (se 2 (by rfl) ⟨1917708, by rfl⟩ : syracuseStep 5113889 = 3835417) B3835417
theorem B3409259 : Blo 2271435 3409259 := bstep (se 1 (by rfl) ⟨2556944, by rfl⟩ : syracuseStep 3409259 = 5113889) B5113889
theorem B2272839 : Blo 2271435 2272839 := bstep (se 1 (by rfl) ⟨1704629, by rfl⟩ : syracuseStep 2272839 = 3409259) B3409259
theorem B2556949 : Blo 2271435 2556949 := bbase (se 6 (by rfl) ⟨59928, by rfl⟩ : syracuseStep 2556949 = 119857) (by norm_num)
theorem B3409265 : Blo 2271435 3409265 := bstep (se 2 (by rfl) ⟨1278474, by rfl⟩ : syracuseStep 3409265 = 2556949) B2556949
theorem B2272843 : Blo 2271435 2272843 := bstep (se 1 (by rfl) ⟨1704632, by rfl⟩ : syracuseStep 2272843 = 3409265) B3409265
theorem B2876573 : Blo 2271435 2876573 := bbase (se 3 (by rfl) ⟨539357, by rfl⟩ : syracuseStep 2876573 = 1078715) (by norm_num)
theorem B7670861 : Blo 2271435 7670861 := bstep (se 3 (by rfl) ⟨1438286, by rfl⟩ : syracuseStep 7670861 = 2876573) B2876573
theorem B5113907 : Blo 2271435 5113907 := bstep (se 1 (by rfl) ⟨3835430, by rfl⟩ : syracuseStep 5113907 = 7670861) B7670861
theorem B3409271 : Blo 2271435 3409271 := bstep (se 1 (by rfl) ⟨2556953, by rfl⟩ : syracuseStep 3409271 = 5113907) B5113907
theorem B2272847 : Blo 2271435 2272847 := bstep (se 1 (by rfl) ⟨1704635, by rfl⟩ : syracuseStep 2272847 = 3409271) B3409271
theorem B3409277 : Blo 2271435 3409277 := bbase (se 3 (by rfl) ⟨639239, by rfl⟩ : syracuseStep 3409277 = 1278479) (by norm_num)
theorem B2272851 : Blo 2271435 2272851 := bstep (se 1 (by rfl) ⟨1704638, by rfl⟩ : syracuseStep 2272851 = 3409277) B3409277
theorem B5113925 : Blo 2271435 5113925 := bbase (se 4 (by rfl) ⟨479430, by rfl⟩ : syracuseStep 5113925 = 958861) (by norm_num)
theorem B3409283 : Blo 2271435 3409283 := bstep (se 1 (by rfl) ⟨2556962, by rfl⟩ : syracuseStep 3409283 = 5113925) B5113925
theorem B2272855 : Blo 2271435 2272855 := bstep (se 1 (by rfl) ⟨1704641, by rfl⟩ : syracuseStep 2272855 = 3409283) B3409283
theorem B6472325 : Blo 2271435 6472325 := bbase (se 4 (by rfl) ⟨606780, by rfl⟩ : syracuseStep 6472325 = 1213561) (by norm_num)
theorem B4314883 : Blo 2271435 4314883 := bstep (se 1 (by rfl) ⟨3236162, by rfl⟩ : syracuseStep 4314883 = 6472325) B6472325
theorem B5753177 : Blo 2271435 5753177 := bstep (se 2 (by rfl) ⟨2157441, by rfl⟩ : syracuseStep 5753177 = 4314883) B4314883
theorem B3835451 : Blo 2271435 3835451 := bstep (se 1 (by rfl) ⟨2876588, by rfl⟩ : syracuseStep 3835451 = 5753177) B5753177
theorem B2556967 : Blo 2271435 2556967 := bstep (se 1 (by rfl) ⟨1917725, by rfl⟩ : syracuseStep 2556967 = 3835451) B3835451
theorem B3409289 : Blo 2271435 3409289 := bstep (se 2 (by rfl) ⟨1278483, by rfl⟩ : syracuseStep 3409289 = 2556967) B2556967
theorem B2272859 : Blo 2271435 2272859 := bstep (se 1 (by rfl) ⟨1704644, by rfl⟩ : syracuseStep 2272859 = 3409289) B3409289
theorem B11506373 : Blo 2271435 11506373 := bbase (se 4 (by rfl) ⟨1078722, by rfl⟩ : syracuseStep 11506373 = 2157445) (by norm_num)
theorem B7670915 : Blo 2271435 7670915 := bstep (se 1 (by rfl) ⟨5753186, by rfl⟩ : syracuseStep 7670915 = 11506373) B11506373
theorem B5113943 : Blo 2271435 5113943 := bstep (se 1 (by rfl) ⟨3835457, by rfl⟩ : syracuseStep 5113943 = 7670915) B7670915
theorem B3409295 : Blo 2271435 3409295 := bstep (se 1 (by rfl) ⟨2556971, by rfl⟩ : syracuseStep 3409295 = 5113943) B5113943
theorem B2272863 : Blo 2271435 2272863 := bstep (se 1 (by rfl) ⟨1704647, by rfl⟩ : syracuseStep 2272863 = 3409295) B3409295
theorem B3409301 : Blo 2271435 3409301 := bbase (se 6 (by rfl) ⟨79905, by rfl⟩ : syracuseStep 3409301 = 159811) (by norm_num)
theorem B2272867 : Blo 2271435 2272867 := bstep (se 1 (by rfl) ⟨1704650, by rfl⟩ : syracuseStep 2272867 = 3409301) B3409301
theorem B4854269 : Blo 2271435 4854269 := bbase (se 3 (by rfl) ⟨910175, by rfl⟩ : syracuseStep 4854269 = 1820351) (by norm_num)
theorem B12944717 : Blo 2271435 12944717 := bstep (se 3 (by rfl) ⟨2427134, by rfl⟩ : syracuseStep 12944717 = 4854269) B4854269
theorem B8629811 : Blo 2271435 8629811 := bstep (se 1 (by rfl) ⟨6472358, by rfl⟩ : syracuseStep 8629811 = 12944717) B12944717
theorem B5753207 : Blo 2271435 5753207 := bstep (se 1 (by rfl) ⟨4314905, by rfl⟩ : syracuseStep 5753207 = 8629811) B8629811
theorem B3835471 : Blo 2271435 3835471 := bstep (se 1 (by rfl) ⟨2876603, by rfl⟩ : syracuseStep 3835471 = 5753207) B5753207
theorem B5113961 : Blo 2271435 5113961 := bstep (se 2 (by rfl) ⟨1917735, by rfl⟩ : syracuseStep 5113961 = 3835471) B3835471
theorem B3409307 : Blo 2271435 3409307 := bstep (se 1 (by rfl) ⟨2556980, by rfl⟩ : syracuseStep 3409307 = 5113961) B5113961
theorem B2272871 : Blo 2271435 2272871 := bstep (se 1 (by rfl) ⟨1704653, by rfl⟩ : syracuseStep 2272871 = 3409307) B3409307
theorem B2556985 : Blo 2271435 2556985 := bbase (se 2 (by rfl) ⟨958869, by rfl⟩ : syracuseStep 2556985 = 1917739) (by norm_num)
theorem B3409313 : Blo 2271435 3409313 := bstep (se 2 (by rfl) ⟨1278492, by rfl⟩ : syracuseStep 3409313 = 2556985) B2556985
theorem B2272875 : Blo 2271435 2272875 := bstep (se 1 (by rfl) ⟨1704656, by rfl⟩ : syracuseStep 2272875 = 3409313) B3409313
theorem B4095805 : Blo 2271435 4095805 := bbase (se 3 (by rfl) ⟨767963, by rfl⟩ : syracuseStep 4095805 = 1535927) (by norm_num)
theorem B5461073 : Blo 2271435 5461073 := bstep (se 2 (by rfl) ⟨2047902, by rfl⟩ : syracuseStep 5461073 = 4095805) B4095805
theorem B3640715 : Blo 2271435 3640715 := bstep (se 1 (by rfl) ⟨2730536, by rfl⟩ : syracuseStep 3640715 = 5461073) B5461073
theorem B2427143 : Blo 2271435 2427143 := bstep (se 1 (by rfl) ⟨1820357, by rfl⟩ : syracuseStep 2427143 = 3640715) B3640715
theorem B6472381 : Blo 2271435 6472381 := bstep (se 3 (by rfl) ⟨1213571, by rfl⟩ : syracuseStep 6472381 = 2427143) B2427143
theorem B8629841 : Blo 2271435 8629841 := bstep (se 2 (by rfl) ⟨3236190, by rfl⟩ : syracuseStep 8629841 = 6472381) B6472381
theorem B5753227 : Blo 2271435 5753227 := bstep (se 1 (by rfl) ⟨4314920, by rfl⟩ : syracuseStep 5753227 = 8629841) B8629841
theorem B7670969 : Blo 2271435 7670969 := bstep (se 2 (by rfl) ⟨2876613, by rfl⟩ : syracuseStep 7670969 = 5753227) B5753227
theorem B5113979 : Blo 2271435 5113979 := bstep (se 1 (by rfl) ⟨3835484, by rfl⟩ : syracuseStep 5113979 = 7670969) B7670969
theorem B3409319 : Blo 2271435 3409319 := bstep (se 1 (by rfl) ⟨2556989, by rfl⟩ : syracuseStep 3409319 = 5113979) B5113979
theorem B2272879 : Blo 2271435 2272879 := bstep (se 1 (by rfl) ⟨1704659, by rfl⟩ : syracuseStep 2272879 = 3409319) B3409319
theorem B3409325 : Blo 2271435 3409325 := bbase (se 3 (by rfl) ⟨639248, by rfl⟩ : syracuseStep 3409325 = 1278497) (by norm_num)
theorem B2272883 : Blo 2271435 2272883 := bstep (se 1 (by rfl) ⟨1704662, by rfl⟩ : syracuseStep 2272883 = 3409325) B3409325
theorem B5113997 : Blo 2271435 5113997 := bbase (se 3 (by rfl) ⟨958874, by rfl⟩ : syracuseStep 5113997 = 1917749) (by norm_num)
theorem B3409331 : Blo 2271435 3409331 := bstep (se 1 (by rfl) ⟨2556998, by rfl⟩ : syracuseStep 3409331 = 5113997) B5113997
theorem B2272887 : Blo 2271435 2272887 := bstep (se 1 (by rfl) ⟨1704665, by rfl⟩ : syracuseStep 2272887 = 3409331) B3409331
theorem B2876629 : Blo 2271435 2876629 := bbase (se 7 (by rfl) ⟨33710, by rfl⟩ : syracuseStep 2876629 = 67421) (by norm_num)
theorem B3835505 : Blo 2271435 3835505 := bstep (se 2 (by rfl) ⟨1438314, by rfl⟩ : syracuseStep 3835505 = 2876629) B2876629
theorem B2557003 : Blo 2271435 2557003 := bstep (se 1 (by rfl) ⟨1917752, by rfl⟩ : syracuseStep 2557003 = 3835505) B3835505
theorem B3409337 : Blo 2271435 3409337 := bstep (se 2 (by rfl) ⟨1278501, by rfl⟩ : syracuseStep 3409337 = 2557003) B2557003
theorem B2272891 : Blo 2271435 2272891 := bstep (se 1 (by rfl) ⟨1704668, by rfl⟩ : syracuseStep 2272891 = 3409337) B3409337
theorem B110587477 : Blo 2271435 110587477 := bbase (se 8 (by rfl) ⟨647973, by rfl⟩ : syracuseStep 110587477 = 1295947) (by norm_num)
theorem B147449969 : Blo 2271435 147449969 := bstep (se 2 (by rfl) ⟨55293738, by rfl⟩ : syracuseStep 147449969 = 110587477) B110587477
theorem B98299979 : Blo 2271435 98299979 := bstep (se 1 (by rfl) ⟨73724984, by rfl⟩ : syracuseStep 98299979 = 147449969) B147449969
theorem B65533319 : Blo 2271435 65533319 := bstep (se 1 (by rfl) ⟨49149989, by rfl⟩ : syracuseStep 65533319 = 98299979) B98299979
theorem B43688879 : Blo 2271435 43688879 := bstep (se 1 (by rfl) ⟨32766659, by rfl⟩ : syracuseStep 43688879 = 65533319) B65533319
theorem B29125919 : Blo 2271435 29125919 := bstep (se 1 (by rfl) ⟨21844439, by rfl⟩ : syracuseStep 29125919 = 43688879) B43688879
theorem B19417279 : Blo 2271435 19417279 := bstep (se 1 (by rfl) ⟨14562959, by rfl⟩ : syracuseStep 19417279 = 29125919) B29125919
theorem B25889705 : Blo 2271435 25889705 := bstep (se 2 (by rfl) ⟨9708639, by rfl⟩ : syracuseStep 25889705 = 19417279) B19417279
theorem B17259803 : Blo 2271435 17259803 := bstep (se 1 (by rfl) ⟨12944852, by rfl⟩ : syracuseStep 17259803 = 25889705) B25889705
theorem B11506535 : Blo 2271435 11506535 := bstep (se 1 (by rfl) ⟨8629901, by rfl⟩ : syracuseStep 11506535 = 17259803) B17259803
theorem B7671023 : Blo 2271435 7671023 := bstep (se 1 (by rfl) ⟨5753267, by rfl⟩ : syracuseStep 7671023 = 11506535) B11506535
theorem B5114015 : Blo 2271435 5114015 := bstep (se 1 (by rfl) ⟨3835511, by rfl⟩ : syracuseStep 5114015 = 7671023) B7671023
theorem B3409343 : Blo 2271435 3409343 := bstep (se 1 (by rfl) ⟨2557007, by rfl⟩ : syracuseStep 3409343 = 5114015) B5114015
theorem B2272895 : Blo 2271435 2272895 := bstep (se 1 (by rfl) ⟨1704671, by rfl⟩ : syracuseStep 2272895 = 3409343) B3409343
theorem B3409349 : Blo 2271435 3409349 := bbase (se 4 (by rfl) ⟨319626, by rfl⟩ : syracuseStep 3409349 = 639253) (by norm_num)
theorem B2272899 : Blo 2271435 2272899 := bstep (se 1 (by rfl) ⟨1704674, by rfl⟩ : syracuseStep 2272899 = 3409349) B3409349
theorem B3835525 : Blo 2271435 3835525 := bbase (se 4 (by rfl) ⟨359580, by rfl⟩ : syracuseStep 3835525 = 719161) (by norm_num)
theorem B5114033 : Blo 2271435 5114033 := bstep (se 2 (by rfl) ⟨1917762, by rfl⟩ : syracuseStep 5114033 = 3835525) B3835525
theorem B3409355 : Blo 2271435 3409355 := bstep (se 1 (by rfl) ⟨2557016, by rfl⟩ : syracuseStep 3409355 = 5114033) B5114033
theorem B2272903 : Blo 2271435 2272903 := bstep (se 1 (by rfl) ⟨1704677, by rfl⟩ : syracuseStep 2272903 = 3409355) B3409355
theorem B2557021 : Blo 2271435 2557021 := bbase (se 3 (by rfl) ⟨479441, by rfl⟩ : syracuseStep 2557021 = 958883) (by norm_num)
theorem B3409361 : Blo 2271435 3409361 := bstep (se 2 (by rfl) ⟨1278510, by rfl⟩ : syracuseStep 3409361 = 2557021) B2557021
theorem B2272907 : Blo 2271435 2272907 := bstep (se 1 (by rfl) ⟨1704680, by rfl⟩ : syracuseStep 2272907 = 3409361) B3409361
theorem B7671077 : Blo 2271435 7671077 := bbase (se 4 (by rfl) ⟨719163, by rfl⟩ : syracuseStep 7671077 = 1438327) (by norm_num)
theorem B5114051 : Blo 2271435 5114051 := bstep (se 1 (by rfl) ⟨3835538, by rfl⟩ : syracuseStep 5114051 = 7671077) B7671077
theorem B3409367 : Blo 2271435 3409367 := bstep (se 1 (by rfl) ⟨2557025, by rfl⟩ : syracuseStep 3409367 = 5114051) B5114051
theorem B2272911 : Blo 2271435 2272911 := bstep (se 1 (by rfl) ⟨1704683, by rfl⟩ : syracuseStep 2272911 = 3409367) B3409367
theorem B3409373 : Blo 2271435 3409373 := bbase (se 3 (by rfl) ⟨639257, by rfl⟩ : syracuseStep 3409373 = 1278515) (by norm_num)
theorem B2272915 : Blo 2271435 2272915 := bstep (se 1 (by rfl) ⟨1704686, by rfl⟩ : syracuseStep 2272915 = 3409373) B3409373
theorem B5114069 : Blo 2271435 5114069 := bbase (se 7 (by rfl) ⟨59930, by rfl⟩ : syracuseStep 5114069 = 119861) (by norm_num)
theorem B3409379 : Blo 2271435 3409379 := bstep (se 1 (by rfl) ⟨2557034, by rfl⟩ : syracuseStep 3409379 = 5114069) B5114069
theorem B2272919 : Blo 2271435 2272919 := bstep (se 1 (by rfl) ⟨1704689, by rfl⟩ : syracuseStep 2272919 = 3409379) B3409379
theorem B10922357 : Blo 2271435 10922357 := bbase (se 5 (by rfl) ⟨511985, by rfl⟩ : syracuseStep 10922357 = 1023971) (by norm_num)
theorem B7281571 : Blo 2271435 7281571 := bstep (se 1 (by rfl) ⟨5461178, by rfl⟩ : syracuseStep 7281571 = 10922357) B10922357
theorem B9708761 : Blo 2271435 9708761 := bstep (se 2 (by rfl) ⟨3640785, by rfl⟩ : syracuseStep 9708761 = 7281571) B7281571
theorem B6472507 : Blo 2271435 6472507 := bstep (se 1 (by rfl) ⟨4854380, by rfl⟩ : syracuseStep 6472507 = 9708761) B9708761
theorem B8630009 : Blo 2271435 8630009 := bstep (se 2 (by rfl) ⟨3236253, by rfl⟩ : syracuseStep 8630009 = 6472507) B6472507
theorem B5753339 : Blo 2271435 5753339 := bstep (se 1 (by rfl) ⟨4315004, by rfl⟩ : syracuseStep 5753339 = 8630009) B8630009
theorem B3835559 : Blo 2271435 3835559 := bstep (se 1 (by rfl) ⟨2876669, by rfl⟩ : syracuseStep 3835559 = 5753339) B5753339
theorem B2557039 : Blo 2271435 2557039 := bstep (se 1 (by rfl) ⟨1917779, by rfl⟩ : syracuseStep 2557039 = 3835559) B3835559
theorem B3409385 : Blo 2271435 3409385 := bstep (se 2 (by rfl) ⟨1278519, by rfl⟩ : syracuseStep 3409385 = 2557039) B2557039
theorem B2272923 : Blo 2271435 2272923 := bstep (se 1 (by rfl) ⟨1704692, by rfl⟩ : syracuseStep 2272923 = 3409385) B3409385
theorem B8191781 : Blo 2271435 8191781 := bbase (se 4 (by rfl) ⟨767979, by rfl⟩ : syracuseStep 8191781 = 1535959) (by norm_num)
theorem B5461187 : Blo 2271435 5461187 := bstep (se 1 (by rfl) ⟨4095890, by rfl⟩ : syracuseStep 5461187 = 8191781) B8191781
theorem B14563165 : Blo 2271435 14563165 := bstep (se 3 (by rfl) ⟨2730593, by rfl⟩ : syracuseStep 14563165 = 5461187) B5461187
theorem B19417553 : Blo 2271435 19417553 := bstep (se 2 (by rfl) ⟨7281582, by rfl⟩ : syracuseStep 19417553 = 14563165) B14563165
theorem B12945035 : Blo 2271435 12945035 := bstep (se 1 (by rfl) ⟨9708776, by rfl⟩ : syracuseStep 12945035 = 19417553) B19417553
theorem B8630023 : Blo 2271435 8630023 := bstep (se 1 (by rfl) ⟨6472517, by rfl⟩ : syracuseStep 8630023 = 12945035) B12945035
theorem B11506697 : Blo 2271435 11506697 := bstep (se 2 (by rfl) ⟨4315011, by rfl⟩ : syracuseStep 11506697 = 8630023) B8630023
theorem B7671131 : Blo 2271435 7671131 := bstep (se 1 (by rfl) ⟨5753348, by rfl⟩ : syracuseStep 7671131 = 11506697) B11506697
theorem B5114087 : Blo 2271435 5114087 := bstep (se 1 (by rfl) ⟨3835565, by rfl⟩ : syracuseStep 5114087 = 7671131) B7671131
theorem B3409391 : Blo 2271435 3409391 := bstep (se 1 (by rfl) ⟨2557043, by rfl⟩ : syracuseStep 3409391 = 5114087) B5114087
theorem B2272927 : Blo 2271435 2272927 := bstep (se 1 (by rfl) ⟨1704695, by rfl⟩ : syracuseStep 2272927 = 3409391) B3409391
theorem B3409397 : Blo 2271435 3409397 := bbase (se 5 (by rfl) ⟨159815, by rfl⟩ : syracuseStep 3409397 = 319631) (by norm_num)
theorem B2272931 : Blo 2271435 2272931 := bstep (se 1 (by rfl) ⟨1704698, by rfl⟩ : syracuseStep 2272931 = 3409397) B3409397
theorem B3640805 : Blo 2271435 3640805 := bbase (se 4 (by rfl) ⟨341325, by rfl⟩ : syracuseStep 3640805 = 682651) (by norm_num)
theorem B2427203 : Blo 2271435 2427203 := bstep (se 1 (by rfl) ⟨1820402, by rfl⟩ : syracuseStep 2427203 = 3640805) B3640805
theorem B6472541 : Blo 2271435 6472541 := bstep (se 3 (by rfl) ⟨1213601, by rfl⟩ : syracuseStep 6472541 = 2427203) B2427203
theorem B4315027 : Blo 2271435 4315027 := bstep (se 1 (by rfl) ⟨3236270, by rfl⟩ : syracuseStep 4315027 = 6472541) B6472541
theorem B5753369 : Blo 2271435 5753369 := bstep (se 2 (by rfl) ⟨2157513, by rfl⟩ : syracuseStep 5753369 = 4315027) B4315027
theorem B3835579 : Blo 2271435 3835579 := bstep (se 1 (by rfl) ⟨2876684, by rfl⟩ : syracuseStep 3835579 = 5753369) B5753369
theorem B5114105 : Blo 2271435 5114105 := bstep (se 2 (by rfl) ⟨1917789, by rfl⟩ : syracuseStep 5114105 = 3835579) B3835579
theorem B3409403 : Blo 2271435 3409403 := bstep (se 1 (by rfl) ⟨2557052, by rfl⟩ : syracuseStep 3409403 = 5114105) B5114105
theorem B2272935 : Blo 2271435 2272935 := bstep (se 1 (by rfl) ⟨1704701, by rfl⟩ : syracuseStep 2272935 = 3409403) B3409403
theorem B2557057 : Blo 2271435 2557057 := bbase (se 2 (by rfl) ⟨958896, by rfl⟩ : syracuseStep 2557057 = 1917793) (by norm_num)
theorem B3409409 : Blo 2271435 3409409 := bstep (se 2 (by rfl) ⟨1278528, by rfl⟩ : syracuseStep 3409409 = 2557057) B2557057
theorem B2272939 : Blo 2271435 2272939 := bstep (se 1 (by rfl) ⟨1704704, by rfl⟩ : syracuseStep 2272939 = 3409409) B3409409
theorem B5753389 : Blo 2271435 5753389 := bbase (se 3 (by rfl) ⟨1078760, by rfl⟩ : syracuseStep 5753389 = 2157521) (by norm_num)
theorem B7671185 : Blo 2271435 7671185 := bstep (se 2 (by rfl) ⟨2876694, by rfl⟩ : syracuseStep 7671185 = 5753389) B5753389
theorem B5114123 : Blo 2271435 5114123 := bstep (se 1 (by rfl) ⟨3835592, by rfl⟩ : syracuseStep 5114123 = 7671185) B7671185
theorem B3409415 : Blo 2271435 3409415 := bstep (se 1 (by rfl) ⟨2557061, by rfl⟩ : syracuseStep 3409415 = 5114123) B5114123
theorem B2272943 : Blo 2271435 2272943 := bstep (se 1 (by rfl) ⟨1704707, by rfl⟩ : syracuseStep 2272943 = 3409415) B3409415
theorem B3409421 : Blo 2271435 3409421 := bbase (se 3 (by rfl) ⟨639266, by rfl⟩ : syracuseStep 3409421 = 1278533) (by norm_num)
theorem B2272947 : Blo 2271435 2272947 := bstep (se 1 (by rfl) ⟨1704710, by rfl⟩ : syracuseStep 2272947 = 3409421) B3409421
theorem B5114141 : Blo 2271435 5114141 := bbase (se 3 (by rfl) ⟨958901, by rfl⟩ : syracuseStep 5114141 = 1917803) (by norm_num)
theorem B3409427 : Blo 2271435 3409427 := bstep (se 1 (by rfl) ⟨2557070, by rfl⟩ : syracuseStep 3409427 = 5114141) B5114141
theorem B2272951 : Blo 2271435 2272951 := bstep (se 1 (by rfl) ⟨1704713, by rfl⟩ : syracuseStep 2272951 = 3409427) B3409427
theorem B3835613 : Blo 2271435 3835613 := bbase (se 3 (by rfl) ⟨719177, by rfl⟩ : syracuseStep 3835613 = 1438355) (by norm_num)
theorem B2557075 : Blo 2271435 2557075 := bstep (se 1 (by rfl) ⟨1917806, by rfl⟩ : syracuseStep 2557075 = 3835613) B3835613
theorem B3409433 : Blo 2271435 3409433 := bstep (se 2 (by rfl) ⟨1278537, by rfl⟩ : syracuseStep 3409433 = 2557075) B2557075
theorem B2272955 : Blo 2271435 2272955 := bstep (se 1 (by rfl) ⟨1704716, by rfl⟩ : syracuseStep 2272955 = 3409433) B3409433
theorem B7281685 : Blo 2271435 7281685 := bbase (se 6 (by rfl) ⟨170664, by rfl⟩ : syracuseStep 7281685 = 341329) (by norm_num)
theorem B9708913 : Blo 2271435 9708913 := bstep (se 2 (by rfl) ⟨3640842, by rfl⟩ : syracuseStep 9708913 = 7281685) B7281685
theorem B12945217 : Blo 2271435 12945217 := bstep (se 2 (by rfl) ⟨4854456, by rfl⟩ : syracuseStep 12945217 = 9708913) B9708913
theorem B17260289 : Blo 2271435 17260289 := bstep (se 2 (by rfl) ⟨6472608, by rfl⟩ : syracuseStep 17260289 = 12945217) B12945217
theorem B11506859 : Blo 2271435 11506859 := bstep (se 1 (by rfl) ⟨8630144, by rfl⟩ : syracuseStep 11506859 = 17260289) B17260289
theorem B7671239 : Blo 2271435 7671239 := bstep (se 1 (by rfl) ⟨5753429, by rfl⟩ : syracuseStep 7671239 = 11506859) B11506859
theorem B5114159 : Blo 2271435 5114159 := bstep (se 1 (by rfl) ⟨3835619, by rfl⟩ : syracuseStep 5114159 = 7671239) B7671239
theorem B3409439 : Blo 2271435 3409439 := bstep (se 1 (by rfl) ⟨2557079, by rfl⟩ : syracuseStep 3409439 = 5114159) B5114159
theorem B2272959 : Blo 2271435 2272959 := bstep (se 1 (by rfl) ⟨1704719, by rfl⟩ : syracuseStep 2272959 = 3409439) B3409439
theorem B3409445 : Blo 2271435 3409445 := bbase (se 4 (by rfl) ⟨319635, by rfl⟩ : syracuseStep 3409445 = 639271) (by norm_num)
theorem B2272963 : Blo 2271435 2272963 := bstep (se 1 (by rfl) ⟨1704722, by rfl⟩ : syracuseStep 2272963 = 3409445) B3409445
theorem B2876725 : Blo 2271435 2876725 := bbase (se 5 (by rfl) ⟨134846, by rfl⟩ : syracuseStep 2876725 = 269693) (by norm_num)
theorem B3835633 : Blo 2271435 3835633 := bstep (se 2 (by rfl) ⟨1438362, by rfl⟩ : syracuseStep 3835633 = 2876725) B2876725
theorem B5114177 : Blo 2271435 5114177 := bstep (se 2 (by rfl) ⟨1917816, by rfl⟩ : syracuseStep 5114177 = 3835633) B3835633
theorem B3409451 : Blo 2271435 3409451 := bstep (se 1 (by rfl) ⟨2557088, by rfl⟩ : syracuseStep 3409451 = 5114177) B5114177
theorem B2272967 : Blo 2271435 2272967 := bstep (se 1 (by rfl) ⟨1704725, by rfl⟩ : syracuseStep 2272967 = 3409451) B3409451
theorem B2557093 : Blo 2271435 2557093 := bbase (se 4 (by rfl) ⟨239727, by rfl⟩ : syracuseStep 2557093 = 479455) (by norm_num)
theorem B3409457 : Blo 2271435 3409457 := bstep (se 2 (by rfl) ⟨1278546, by rfl⟩ : syracuseStep 3409457 = 2557093) B2557093
theorem B2272971 : Blo 2271435 2272971 := bstep (se 1 (by rfl) ⟨1704728, by rfl⟩ : syracuseStep 2272971 = 3409457) B3409457
theorem B4920725 : Blo 2271435 4920725 := bbase (se 6 (by rfl) ⟨115329, by rfl⟩ : syracuseStep 4920725 = 230659) (by norm_num)
theorem B3280483 : Blo 2271435 3280483 := bstep (se 1 (by rfl) ⟨2460362, by rfl⟩ : syracuseStep 3280483 = 4920725) B4920725
theorem B17495909 : Blo 2271435 17495909 := bstep (se 4 (by rfl) ⟨1640241, by rfl⟩ : syracuseStep 17495909 = 3280483) B3280483
theorem B11663939 : Blo 2271435 11663939 := bstep (se 1 (by rfl) ⟨8747954, by rfl⟩ : syracuseStep 11663939 = 17495909) B17495909
theorem B7775959 : Blo 2271435 7775959 := bstep (se 1 (by rfl) ⟨5831969, by rfl⟩ : syracuseStep 7775959 = 11663939) B11663939
theorem B10367945 : Blo 2271435 10367945 := bstep (se 2 (by rfl) ⟨3887979, by rfl⟩ : syracuseStep 10367945 = 7775959) B7775959
theorem B6911963 : Blo 2271435 6911963 := bstep (se 1 (by rfl) ⟨5183972, by rfl⟩ : syracuseStep 6911963 = 10367945) B10367945
theorem B4607975 : Blo 2271435 4607975 := bstep (se 1 (by rfl) ⟨3455981, by rfl⟩ : syracuseStep 4607975 = 6911963) B6911963
theorem B12287933 : Blo 2271435 12287933 := bstep (se 3 (by rfl) ⟨2303987, by rfl⟩ : syracuseStep 12287933 = 4607975) B4607975
theorem B8191955 : Blo 2271435 8191955 := bstep (se 1 (by rfl) ⟨6143966, by rfl⟩ : syracuseStep 8191955 = 12287933) B12287933
theorem B21845213 : Blo 2271435 21845213 := bstep (se 3 (by rfl) ⟨4095977, by rfl⟩ : syracuseStep 21845213 = 8191955) B8191955
theorem B14563475 : Blo 2271435 14563475 := bstep (se 1 (by rfl) ⟨10922606, by rfl⟩ : syracuseStep 14563475 = 21845213) B21845213
theorem B9708983 : Blo 2271435 9708983 := bstep (se 1 (by rfl) ⟨7281737, by rfl⟩ : syracuseStep 9708983 = 14563475) B14563475
theorem B6472655 : Blo 2271435 6472655 := bstep (se 1 (by rfl) ⟨4854491, by rfl⟩ : syracuseStep 6472655 = 9708983) B9708983
theorem B4315103 : Blo 2271435 4315103 := bstep (se 1 (by rfl) ⟨3236327, by rfl⟩ : syracuseStep 4315103 = 6472655) B6472655
theorem B2876735 : Blo 2271435 2876735 := bstep (se 1 (by rfl) ⟨2157551, by rfl⟩ : syracuseStep 2876735 = 4315103) B4315103
theorem B7671293 : Blo 2271435 7671293 := bstep (se 3 (by rfl) ⟨1438367, by rfl⟩ : syracuseStep 7671293 = 2876735) B2876735
theorem B5114195 : Blo 2271435 5114195 := bstep (se 1 (by rfl) ⟨3835646, by rfl⟩ : syracuseStep 5114195 = 7671293) B7671293
theorem B3409463 : Blo 2271435 3409463 := bstep (se 1 (by rfl) ⟨2557097, by rfl⟩ : syracuseStep 3409463 = 5114195) B5114195
theorem B2272975 : Blo 2271435 2272975 := bstep (se 1 (by rfl) ⟨1704731, by rfl⟩ : syracuseStep 2272975 = 3409463) B3409463
theorem B3409469 : Blo 2271435 3409469 := bbase (se 3 (by rfl) ⟨639275, by rfl⟩ : syracuseStep 3409469 = 1278551) (by norm_num)
theorem B2272979 : Blo 2271435 2272979 := bstep (se 1 (by rfl) ⟨1704734, by rfl⟩ : syracuseStep 2272979 = 3409469) B3409469
theorem B5114213 : Blo 2271435 5114213 := bbase (se 4 (by rfl) ⟨479457, by rfl⟩ : syracuseStep 5114213 = 958915) (by norm_num)
theorem B3409475 : Blo 2271435 3409475 := bstep (se 1 (by rfl) ⟨2557106, by rfl⟩ : syracuseStep 3409475 = 5114213) B5114213
theorem B2272983 : Blo 2271435 2272983 := bstep (se 1 (by rfl) ⟨1704737, by rfl⟩ : syracuseStep 2272983 = 3409475) B3409475
theorem B5753501 : Blo 2271435 5753501 := bbase (se 3 (by rfl) ⟨1078781, by rfl⟩ : syracuseStep 5753501 = 2157563) (by norm_num)
theorem B3835667 : Blo 2271435 3835667 := bstep (se 1 (by rfl) ⟨2876750, by rfl⟩ : syracuseStep 3835667 = 5753501) B5753501
theorem B2557111 : Blo 2271435 2557111 := bstep (se 1 (by rfl) ⟨1917833, by rfl⟩ : syracuseStep 2557111 = 3835667) B3835667
theorem B3409481 : Blo 2271435 3409481 := bstep (se 2 (by rfl) ⟨1278555, by rfl⟩ : syracuseStep 3409481 = 2557111) B2557111
theorem B2272987 : Blo 2271435 2272987 := bstep (se 1 (by rfl) ⟨1704740, by rfl⟩ : syracuseStep 2272987 = 3409481) B3409481
theorem B4315133 : Blo 2271435 4315133 := bbase (se 3 (by rfl) ⟨809087, by rfl⟩ : syracuseStep 4315133 = 1618175) (by norm_num)
theorem B11507021 : Blo 2271435 11507021 := bstep (se 3 (by rfl) ⟨2157566, by rfl⟩ : syracuseStep 11507021 = 4315133) B4315133
theorem B7671347 : Blo 2271435 7671347 := bstep (se 1 (by rfl) ⟨5753510, by rfl⟩ : syracuseStep 7671347 = 11507021) B11507021
theorem B5114231 : Blo 2271435 5114231 := bstep (se 1 (by rfl) ⟨3835673, by rfl⟩ : syracuseStep 5114231 = 7671347) B7671347
theorem B3409487 : Blo 2271435 3409487 := bstep (se 1 (by rfl) ⟨2557115, by rfl⟩ : syracuseStep 3409487 = 5114231) B5114231
theorem B2272991 : Blo 2271435 2272991 := bstep (se 1 (by rfl) ⟨1704743, by rfl⟩ : syracuseStep 2272991 = 3409487) B3409487
theorem B3409493 : Blo 2271435 3409493 := bbase (se 8 (by rfl) ⟨19977, by rfl⟩ : syracuseStep 3409493 = 39955) (by norm_num)
theorem B2272995 : Blo 2271435 2272995 := bstep (se 1 (by rfl) ⟨1704746, by rfl⟩ : syracuseStep 2272995 = 3409493) B3409493
theorem B4096021 : Blo 2271435 4096021 := bbase (se 6 (by rfl) ⟨96000, by rfl⟩ : syracuseStep 4096021 = 192001) (by norm_num)
theorem B5461361 : Blo 2271435 5461361 := bstep (se 2 (by rfl) ⟨2048010, by rfl⟩ : syracuseStep 5461361 = 4096021) B4096021
theorem B3640907 : Blo 2271435 3640907 := bstep (se 1 (by rfl) ⟨2730680, by rfl⟩ : syracuseStep 3640907 = 5461361) B5461361
theorem B9709085 : Blo 2271435 9709085 := bstep (se 3 (by rfl) ⟨1820453, by rfl⟩ : syracuseStep 9709085 = 3640907) B3640907
theorem B6472723 : Blo 2271435 6472723 := bstep (se 1 (by rfl) ⟨4854542, by rfl⟩ : syracuseStep 6472723 = 9709085) B9709085
theorem B8630297 : Blo 2271435 8630297 := bstep (se 2 (by rfl) ⟨3236361, by rfl⟩ : syracuseStep 8630297 = 6472723) B6472723
theorem B5753531 : Blo 2271435 5753531 := bstep (se 1 (by rfl) ⟨4315148, by rfl⟩ : syracuseStep 5753531 = 8630297) B8630297
theorem B3835687 : Blo 2271435 3835687 := bstep (se 1 (by rfl) ⟨2876765, by rfl⟩ : syracuseStep 3835687 = 5753531) B5753531
theorem B5114249 : Blo 2271435 5114249 := bstep (se 2 (by rfl) ⟨1917843, by rfl⟩ : syracuseStep 5114249 = 3835687) B3835687
theorem B3409499 : Blo 2271435 3409499 := bstep (se 1 (by rfl) ⟨2557124, by rfl⟩ : syracuseStep 3409499 = 5114249) B5114249
theorem B2272999 : Blo 2271435 2272999 := bstep (se 1 (by rfl) ⟨1704749, by rfl⟩ : syracuseStep 2272999 = 3409499) B3409499
theorem B2557129 : Blo 2271435 2557129 := bbase (se 2 (by rfl) ⟨958923, by rfl⟩ : syracuseStep 2557129 = 1917847) (by norm_num)
theorem B3409505 : Blo 2271435 3409505 := bstep (se 2 (by rfl) ⟨1278564, by rfl⟩ : syracuseStep 3409505 = 2557129) B2557129
theorem B2273003 : Blo 2271435 2273003 := bstep (se 1 (by rfl) ⟨1704752, by rfl⟩ : syracuseStep 2273003 = 3409505) B3409505
theorem B11664101 : Blo 2271435 11664101 := bbase (se 4 (by rfl) ⟨1093509, by rfl⟩ : syracuseStep 11664101 = 2187019) (by norm_num)
theorem B7776067 : Blo 2271435 7776067 := bstep (se 1 (by rfl) ⟨5832050, by rfl⟩ : syracuseStep 7776067 = 11664101) B11664101
theorem B10368089 : Blo 2271435 10368089 := bstep (se 2 (by rfl) ⟨3888033, by rfl⟩ : syracuseStep 10368089 = 7776067) B7776067
theorem B6912059 : Blo 2271435 6912059 := bstep (se 1 (by rfl) ⟨5184044, by rfl⟩ : syracuseStep 6912059 = 10368089) B10368089
theorem B18432157 : Blo 2271435 18432157 := bstep (se 3 (by rfl) ⟨3456029, by rfl⟩ : syracuseStep 18432157 = 6912059) B6912059
theorem B24576209 : Blo 2271435 24576209 := bstep (se 2 (by rfl) ⟨9216078, by rfl⟩ : syracuseStep 24576209 = 18432157) B18432157
theorem B16384139 : Blo 2271435 16384139 := bstep (se 1 (by rfl) ⟨12288104, by rfl⟩ : syracuseStep 16384139 = 24576209) B24576209
theorem B10922759 : Blo 2271435 10922759 := bstep (se 1 (by rfl) ⟨8192069, by rfl⟩ : syracuseStep 10922759 = 16384139) B16384139
theorem B7281839 : Blo 2271435 7281839 := bstep (se 1 (by rfl) ⟨5461379, by rfl⟩ : syracuseStep 7281839 = 10922759) B10922759
theorem B19418237 : Blo 2271435 19418237 := bstep (se 3 (by rfl) ⟨3640919, by rfl⟩ : syracuseStep 19418237 = 7281839) B7281839
theorem B12945491 : Blo 2271435 12945491 := bstep (se 1 (by rfl) ⟨9709118, by rfl⟩ : syracuseStep 12945491 = 19418237) B19418237
theorem B8630327 : Blo 2271435 8630327 := bstep (se 1 (by rfl) ⟨6472745, by rfl⟩ : syracuseStep 8630327 = 12945491) B12945491
theorem B5753551 : Blo 2271435 5753551 := bstep (se 1 (by rfl) ⟨4315163, by rfl⟩ : syracuseStep 5753551 = 8630327) B8630327
theorem B7671401 : Blo 2271435 7671401 := bstep (se 2 (by rfl) ⟨2876775, by rfl⟩ : syracuseStep 7671401 = 5753551) B5753551
theorem B5114267 : Blo 2271435 5114267 := bstep (se 1 (by rfl) ⟨3835700, by rfl⟩ : syracuseStep 5114267 = 7671401) B7671401
theorem B3409511 : Blo 2271435 3409511 := bstep (se 1 (by rfl) ⟨2557133, by rfl⟩ : syracuseStep 3409511 = 5114267) B5114267
theorem B2273007 : Blo 2271435 2273007 := bstep (se 1 (by rfl) ⟨1704755, by rfl⟩ : syracuseStep 2273007 = 3409511) B3409511
theorem B3409517 : Blo 2271435 3409517 := bbase (se 3 (by rfl) ⟨639284, by rfl⟩ : syracuseStep 3409517 = 1278569) (by norm_num)
theorem B2273011 : Blo 2271435 2273011 := bstep (se 1 (by rfl) ⟨1704758, by rfl⟩ : syracuseStep 2273011 = 3409517) B3409517
theorem B5114285 : Blo 2271435 5114285 := bbase (se 3 (by rfl) ⟨958928, by rfl⟩ : syracuseStep 5114285 = 1917857) (by norm_num)
theorem B3409523 : Blo 2271435 3409523 := bstep (se 1 (by rfl) ⟨2557142, by rfl⟩ : syracuseStep 3409523 = 5114285) B5114285
theorem B2273015 : Blo 2271435 2273015 := bstep (se 1 (by rfl) ⟨1704761, by rfl⟩ : syracuseStep 2273015 = 3409523) B3409523
theorem B2427293 : Blo 2271435 2427293 := bbase (se 3 (by rfl) ⟨455117, by rfl⟩ : syracuseStep 2427293 = 910235) (by norm_num)
theorem B6472781 : Blo 2271435 6472781 := bstep (se 3 (by rfl) ⟨1213646, by rfl⟩ : syracuseStep 6472781 = 2427293) B2427293
theorem B4315187 : Blo 2271435 4315187 := bstep (se 1 (by rfl) ⟨3236390, by rfl⟩ : syracuseStep 4315187 = 6472781) B6472781
theorem B2876791 : Blo 2271435 2876791 := bstep (se 1 (by rfl) ⟨2157593, by rfl⟩ : syracuseStep 2876791 = 4315187) B4315187
theorem B3835721 : Blo 2271435 3835721 := bstep (se 2 (by rfl) ⟨1438395, by rfl⟩ : syracuseStep 3835721 = 2876791) B2876791
theorem B2557147 : Blo 2271435 2557147 := bstep (se 1 (by rfl) ⟨1917860, by rfl⟩ : syracuseStep 2557147 = 3835721) B3835721
theorem B3409529 : Blo 2271435 3409529 := bstep (se 2 (by rfl) ⟨1278573, by rfl⟩ : syracuseStep 3409529 = 2557147) B2557147
theorem B2273019 : Blo 2271435 2273019 := bstep (se 1 (by rfl) ⟨1704764, by rfl⟩ : syracuseStep 2273019 = 3409529) B3409529
theorem B5194925 : Blo 2271435 5194925 := bbase (se 3 (by rfl) ⟨974048, by rfl⟩ : syracuseStep 5194925 = 1948097) (by norm_num)
theorem B3463283 : Blo 2271435 3463283 := bstep (se 1 (by rfl) ⟨2597462, by rfl⟩ : syracuseStep 3463283 = 5194925) B5194925
theorem B9235421 : Blo 2271435 9235421 := bstep (se 3 (by rfl) ⟨1731641, by rfl⟩ : syracuseStep 9235421 = 3463283) B3463283
theorem B6156947 : Blo 2271435 6156947 := bstep (se 1 (by rfl) ⟨4617710, by rfl⟩ : syracuseStep 6156947 = 9235421) B9235421
theorem B4104631 : Blo 2271435 4104631 := bstep (se 1 (by rfl) ⟨3078473, by rfl⟩ : syracuseStep 4104631 = 6156947) B6156947
theorem B5472841 : Blo 2271435 5472841 := bstep (se 2 (by rfl) ⟨2052315, by rfl⟩ : syracuseStep 5472841 = 4104631) B4104631
theorem B7297121 : Blo 2271435 7297121 := bstep (se 2 (by rfl) ⟨2736420, by rfl⟩ : syracuseStep 7297121 = 5472841) B5472841
theorem B4864747 : Blo 2271435 4864747 := bstep (se 1 (by rfl) ⟨3648560, by rfl⟩ : syracuseStep 4864747 = 7297121) B7297121
theorem B6486329 : Blo 2271435 6486329 := bstep (se 2 (by rfl) ⟨2432373, by rfl⟩ : syracuseStep 6486329 = 4864747) B4864747
theorem B17296877 : Blo 2271435 17296877 := bstep (se 3 (by rfl) ⟨3243164, by rfl⟩ : syracuseStep 17296877 = 6486329) B6486329
theorem B11531251 : Blo 2271435 11531251 := bstep (se 1 (by rfl) ⟨8648438, by rfl⟩ : syracuseStep 11531251 = 17296877) B17296877
theorem B61500005 : Blo 2271435 61500005 := bstep (se 4 (by rfl) ⟨5765625, by rfl⟩ : syracuseStep 61500005 = 11531251) B11531251
theorem B41000003 : Blo 2271435 41000003 := bstep (se 1 (by rfl) ⟨30750002, by rfl⟩ : syracuseStep 41000003 = 61500005) B61500005
theorem B27333335 : Blo 2271435 27333335 := bstep (se 1 (by rfl) ⟨20500001, by rfl⟩ : syracuseStep 27333335 = 41000003) B41000003
theorem B72888893 : Blo 2271435 72888893 := bstep (se 3 (by rfl) ⟨13666667, by rfl⟩ : syracuseStep 72888893 = 27333335) B27333335
theorem B48592595 : Blo 2271435 48592595 := bstep (se 1 (by rfl) ⟨36444446, by rfl⟩ : syracuseStep 48592595 = 72888893) B72888893
theorem B32395063 : Blo 2271435 32395063 := bstep (se 1 (by rfl) ⟨24296297, by rfl⟩ : syracuseStep 32395063 = 48592595) B48592595
theorem B43193417 : Blo 2271435 43193417 := bstep (se 2 (by rfl) ⟨16197531, by rfl⟩ : syracuseStep 43193417 = 32395063) B32395063
theorem B115182445 : Blo 2271435 115182445 := bstep (se 3 (by rfl) ⟨21596708, by rfl⟩ : syracuseStep 115182445 = 43193417) B43193417
theorem B153576593 : Blo 2271435 153576593 := bstep (se 2 (by rfl) ⟨57591222, by rfl⟩ : syracuseStep 153576593 = 115182445) B115182445
theorem B102384395 : Blo 2271435 102384395 := bstep (se 1 (by rfl) ⟨76788296, by rfl⟩ : syracuseStep 102384395 = 153576593) B153576593
theorem B68256263 : Blo 2271435 68256263 := bstep (se 1 (by rfl) ⟨51192197, by rfl⟩ : syracuseStep 68256263 = 102384395) B102384395
theorem B45504175 : Blo 2271435 45504175 := bstep (se 1 (by rfl) ⟨34128131, by rfl⟩ : syracuseStep 45504175 = 68256263) B68256263
theorem B60672233 : Blo 2271435 60672233 := bstep (se 2 (by rfl) ⟨22752087, by rfl⟩ : syracuseStep 60672233 = 45504175) B45504175
theorem B40448155 : Blo 2271435 40448155 := bstep (se 1 (by rfl) ⟨30336116, by rfl⟩ : syracuseStep 40448155 = 60672233) B60672233
theorem B53930873 : Blo 2271435 53930873 := bstep (se 2 (by rfl) ⟨20224077, by rfl⟩ : syracuseStep 53930873 = 40448155) B40448155
theorem B35953915 : Blo 2271435 35953915 := bstep (se 1 (by rfl) ⟨26965436, by rfl⟩ : syracuseStep 35953915 = 53930873) B53930873
theorem B47938553 : Blo 2271435 47938553 := bstep (se 2 (by rfl) ⟨17976957, by rfl⟩ : syracuseStep 47938553 = 35953915) B35953915
theorem B31959035 : Blo 2271435 31959035 := bstep (se 1 (by rfl) ⟨23969276, by rfl⟩ : syracuseStep 31959035 = 47938553) B47938553
theorem B21306023 : Blo 2271435 21306023 := bstep (se 1 (by rfl) ⟨15979517, by rfl⟩ : syracuseStep 21306023 = 31959035) B31959035
theorem B14204015 : Blo 2271435 14204015 := bstep (se 1 (by rfl) ⟨10653011, by rfl⟩ : syracuseStep 14204015 = 21306023) B21306023
theorem B9469343 : Blo 2271435 9469343 := bstep (se 1 (by rfl) ⟨7102007, by rfl⟩ : syracuseStep 9469343 = 14204015) B14204015
theorem B25251581 : Blo 2271435 25251581 := bstep (se 3 (by rfl) ⟨4734671, by rfl⟩ : syracuseStep 25251581 = 9469343) B9469343
theorem B16834387 : Blo 2271435 16834387 := bstep (se 1 (by rfl) ⟨12625790, by rfl⟩ : syracuseStep 16834387 = 25251581) B25251581
theorem B22445849 : Blo 2271435 22445849 := bstep (se 2 (by rfl) ⟨8417193, by rfl⟩ : syracuseStep 22445849 = 16834387) B16834387
theorem B14963899 : Blo 2271435 14963899 := bstep (se 1 (by rfl) ⟨11222924, by rfl⟩ : syracuseStep 14963899 = 22445849) B22445849
theorem B19951865 : Blo 2271435 19951865 := bstep (se 2 (by rfl) ⟨7481949, by rfl⟩ : syracuseStep 19951865 = 14963899) B14963899
theorem B13301243 : Blo 2271435 13301243 := bstep (se 1 (by rfl) ⟨9975932, by rfl⟩ : syracuseStep 13301243 = 19951865) B19951865
theorem B8867495 : Blo 2271435 8867495 := bstep (se 1 (by rfl) ⟨6650621, by rfl⟩ : syracuseStep 8867495 = 13301243) B13301243
theorem B5911663 : Blo 2271435 5911663 := bstep (se 1 (by rfl) ⟨4433747, by rfl⟩ : syracuseStep 5911663 = 8867495) B8867495
theorem B7882217 : Blo 2271435 7882217 := bstep (se 2 (by rfl) ⟨2955831, by rfl⟩ : syracuseStep 7882217 = 5911663) B5911663
theorem B5254811 : Blo 2271435 5254811 := bstep (se 1 (by rfl) ⟨3941108, by rfl⟩ : syracuseStep 5254811 = 7882217) B7882217
theorem B3503207 : Blo 2271435 3503207 := bstep (se 1 (by rfl) ⟨2627405, by rfl⟩ : syracuseStep 3503207 = 5254811) B5254811
theorem B9341885 : Blo 2271435 9341885 := bstep (se 3 (by rfl) ⟨1751603, by rfl⟩ : syracuseStep 9341885 = 3503207) B3503207
theorem B6227923 : Blo 2271435 6227923 := bstep (se 1 (by rfl) ⟨4670942, by rfl⟩ : syracuseStep 6227923 = 9341885) B9341885
theorem B8303897 : Blo 2271435 8303897 := bstep (se 2 (by rfl) ⟨3113961, by rfl⟩ : syracuseStep 8303897 = 6227923) B6227923
theorem B22143725 : Blo 2271435 22143725 := bstep (se 3 (by rfl) ⟨4151948, by rfl⟩ : syracuseStep 22143725 = 8303897) B8303897
theorem B14762483 : Blo 2271435 14762483 := bstep (se 1 (by rfl) ⟨11071862, by rfl⟩ : syracuseStep 14762483 = 22143725) B22143725
theorem B9841655 : Blo 2271435 9841655 := bstep (se 1 (by rfl) ⟨7381241, by rfl⟩ : syracuseStep 9841655 = 14762483) B14762483
theorem B6561103 : Blo 2271435 6561103 := bstep (se 1 (by rfl) ⟨4920827, by rfl⟩ : syracuseStep 6561103 = 9841655) B9841655
theorem B8748137 : Blo 2271435 8748137 := bstep (se 2 (by rfl) ⟨3280551, by rfl⟩ : syracuseStep 8748137 = 6561103) B6561103
theorem B5832091 : Blo 2271435 5832091 := bstep (se 1 (by rfl) ⟨4374068, by rfl⟩ : syracuseStep 5832091 = 8748137) B8748137
theorem B7776121 : Blo 2271435 7776121 := bstep (se 2 (by rfl) ⟨2916045, by rfl⟩ : syracuseStep 7776121 = 5832091) B5832091
theorem B10368161 : Blo 2271435 10368161 := bstep (se 2 (by rfl) ⟨3888060, by rfl⟩ : syracuseStep 10368161 = 7776121) B7776121
theorem B6912107 : Blo 2271435 6912107 := bstep (se 1 (by rfl) ⟨5184080, by rfl⟩ : syracuseStep 6912107 = 10368161) B10368161
theorem B4608071 : Blo 2271435 4608071 := bstep (se 1 (by rfl) ⟨3456053, by rfl⟩ : syracuseStep 4608071 = 6912107) B6912107
theorem B49152757 : Blo 2271435 49152757 := bstep (se 5 (by rfl) ⟨2304035, by rfl⟩ : syracuseStep 49152757 = 4608071) B4608071
theorem B65537009 : Blo 2271435 65537009 := bstep (se 2 (by rfl) ⟨24576378, by rfl⟩ : syracuseStep 65537009 = 49152757) B49152757
theorem B43691339 : Blo 2271435 43691339 := bstep (se 1 (by rfl) ⟨32768504, by rfl⟩ : syracuseStep 43691339 = 65537009) B65537009
theorem B29127559 : Blo 2271435 29127559 := bstep (se 1 (by rfl) ⟨21845669, by rfl⟩ : syracuseStep 29127559 = 43691339) B43691339
theorem B38836745 : Blo 2271435 38836745 := bstep (se 2 (by rfl) ⟨14563779, by rfl⟩ : syracuseStep 38836745 = 29127559) B29127559
theorem B25891163 : Blo 2271435 25891163 := bstep (se 1 (by rfl) ⟨19418372, by rfl⟩ : syracuseStep 25891163 = 38836745) B38836745
theorem B17260775 : Blo 2271435 17260775 := bstep (se 1 (by rfl) ⟨12945581, by rfl⟩ : syracuseStep 17260775 = 25891163) B25891163
theorem B11507183 : Blo 2271435 11507183 := bstep (se 1 (by rfl) ⟨8630387, by rfl⟩ : syracuseStep 11507183 = 17260775) B17260775
theorem B7671455 : Blo 2271435 7671455 := bstep (se 1 (by rfl) ⟨5753591, by rfl⟩ : syracuseStep 7671455 = 11507183) B11507183
theorem B5114303 : Blo 2271435 5114303 := bstep (se 1 (by rfl) ⟨3835727, by rfl⟩ : syracuseStep 5114303 = 7671455) B7671455
theorem B3409535 : Blo 2271435 3409535 := bstep (se 1 (by rfl) ⟨2557151, by rfl⟩ : syracuseStep 3409535 = 5114303) B5114303
theorem B2273023 : Blo 2271435 2273023 := bstep (se 1 (by rfl) ⟨1704767, by rfl⟩ : syracuseStep 2273023 = 3409535) B3409535
theorem B3409541 : Blo 2271435 3409541 := bbase (se 4 (by rfl) ⟨319644, by rfl⟩ : syracuseStep 3409541 = 639289) (by norm_num)
theorem B2273027 : Blo 2271435 2273027 := bstep (se 1 (by rfl) ⟨1704770, by rfl⟩ : syracuseStep 2273027 = 3409541) B3409541
theorem B3835741 : Blo 2271435 3835741 := bbase (se 3 (by rfl) ⟨719201, by rfl⟩ : syracuseStep 3835741 = 1438403) (by norm_num)
theorem B5114321 : Blo 2271435 5114321 := bstep (se 2 (by rfl) ⟨1917870, by rfl⟩ : syracuseStep 5114321 = 3835741) B3835741
theorem B3409547 : Blo 2271435 3409547 := bstep (se 1 (by rfl) ⟨2557160, by rfl⟩ : syracuseStep 3409547 = 5114321) B5114321
theorem B2273031 : Blo 2271435 2273031 := bstep (se 1 (by rfl) ⟨1704773, by rfl⟩ : syracuseStep 2273031 = 3409547) B3409547
theorem B2557165 : Blo 2271435 2557165 := bbase (se 3 (by rfl) ⟨479468, by rfl⟩ : syracuseStep 2557165 = 958937) (by norm_num)
theorem B3409553 : Blo 2271435 3409553 := bstep (se 2 (by rfl) ⟨1278582, by rfl⟩ : syracuseStep 3409553 = 2557165) B2557165
theorem B2273035 : Blo 2271435 2273035 := bstep (se 1 (by rfl) ⟨1704776, by rfl⟩ : syracuseStep 2273035 = 3409553) B3409553
theorem B7671509 : Blo 2271435 7671509 := bbase (se 7 (by rfl) ⟨89900, by rfl⟩ : syracuseStep 7671509 = 179801) (by norm_num)
theorem B5114339 : Blo 2271435 5114339 := bstep (se 1 (by rfl) ⟨3835754, by rfl⟩ : syracuseStep 5114339 = 7671509) B7671509
theorem B3409559 : Blo 2271435 3409559 := bstep (se 1 (by rfl) ⟨2557169, by rfl⟩ : syracuseStep 3409559 = 5114339) B5114339
theorem B2273039 : Blo 2271435 2273039 := bstep (se 1 (by rfl) ⟨1704779, by rfl⟩ : syracuseStep 2273039 = 3409559) B3409559
theorem B3409565 : Blo 2271435 3409565 := bbase (se 3 (by rfl) ⟨639293, by rfl⟩ : syracuseStep 3409565 = 1278587) (by norm_num)
theorem B2273043 : Blo 2271435 2273043 := bstep (se 1 (by rfl) ⟨1704782, by rfl⟩ : syracuseStep 2273043 = 3409565) B3409565
theorem B5114357 : Blo 2271435 5114357 := bbase (se 5 (by rfl) ⟨239735, by rfl⟩ : syracuseStep 5114357 = 479471) (by norm_num)
theorem B3409571 : Blo 2271435 3409571 := bstep (se 1 (by rfl) ⟨2557178, by rfl⟩ : syracuseStep 3409571 = 5114357) B5114357
theorem B2273047 : Blo 2271435 2273047 := bstep (se 1 (by rfl) ⟨1704785, by rfl⟩ : syracuseStep 2273047 = 3409571) B3409571
theorem B3888109 : Blo 2271435 3888109 := bbase (se 3 (by rfl) ⟨729020, by rfl⟩ : syracuseStep 3888109 = 1458041) (by norm_num)
theorem B5184145 : Blo 2271435 5184145 := bstep (se 2 (by rfl) ⟨1944054, by rfl⟩ : syracuseStep 5184145 = 3888109) B3888109
theorem B27648773 : Blo 2271435 27648773 := bstep (se 4 (by rfl) ⟨2592072, by rfl⟩ : syracuseStep 27648773 = 5184145) B5184145
theorem B18432515 : Blo 2271435 18432515 := bstep (se 1 (by rfl) ⟨13824386, by rfl⟩ : syracuseStep 18432515 = 27648773) B27648773
theorem B12288343 : Blo 2271435 12288343 := bstep (se 1 (by rfl) ⟨9216257, by rfl⟩ : syracuseStep 12288343 = 18432515) B18432515
theorem B16384457 : Blo 2271435 16384457 := bstep (se 2 (by rfl) ⟨6144171, by rfl⟩ : syracuseStep 16384457 = 12288343) B12288343
theorem B43691885 : Blo 2271435 43691885 := bstep (se 3 (by rfl) ⟨8192228, by rfl⟩ : syracuseStep 43691885 = 16384457) B16384457
theorem B29127923 : Blo 2271435 29127923 := bstep (se 1 (by rfl) ⟨21845942, by rfl⟩ : syracuseStep 29127923 = 43691885) B43691885
theorem B19418615 : Blo 2271435 19418615 := bstep (se 1 (by rfl) ⟨14563961, by rfl⟩ : syracuseStep 19418615 = 29127923) B29127923
theorem B12945743 : Blo 2271435 12945743 := bstep (se 1 (by rfl) ⟨9709307, by rfl⟩ : syracuseStep 12945743 = 19418615) B19418615
theorem B8630495 : Blo 2271435 8630495 := bstep (se 1 (by rfl) ⟨6472871, by rfl⟩ : syracuseStep 8630495 = 12945743) B12945743
theorem B5753663 : Blo 2271435 5753663 := bstep (se 1 (by rfl) ⟨4315247, by rfl⟩ : syracuseStep 5753663 = 8630495) B8630495
theorem B3835775 : Blo 2271435 3835775 := bstep (se 1 (by rfl) ⟨2876831, by rfl⟩ : syracuseStep 3835775 = 5753663) B5753663
theorem B2557183 : Blo 2271435 2557183 := bstep (se 1 (by rfl) ⟨1917887, by rfl⟩ : syracuseStep 2557183 = 3835775) B3835775
theorem B3409577 : Blo 2271435 3409577 := bstep (se 2 (by rfl) ⟨1278591, by rfl⟩ : syracuseStep 3409577 = 2557183) B2557183
theorem B2273051 : Blo 2271435 2273051 := bstep (se 1 (by rfl) ⟨1704788, by rfl⟩ : syracuseStep 2273051 = 3409577) B3409577
theorem B3640997 : Blo 2271435 3640997 := bbase (se 4 (by rfl) ⟨341343, by rfl⟩ : syracuseStep 3640997 = 682687) (by norm_num)
theorem B2427331 : Blo 2271435 2427331 := bstep (se 1 (by rfl) ⟨1820498, by rfl⟩ : syracuseStep 2427331 = 3640997) B3640997
theorem B3236441 : Blo 2271435 3236441 := bstep (se 2 (by rfl) ⟨1213665, by rfl⟩ : syracuseStep 3236441 = 2427331) B2427331
theorem B8630509 : Blo 2271435 8630509 := bstep (se 3 (by rfl) ⟨1618220, by rfl⟩ : syracuseStep 8630509 = 3236441) B3236441
theorem B11507345 : Blo 2271435 11507345 := bstep (se 2 (by rfl) ⟨4315254, by rfl⟩ : syracuseStep 11507345 = 8630509) B8630509
theorem B7671563 : Blo 2271435 7671563 := bstep (se 1 (by rfl) ⟨5753672, by rfl⟩ : syracuseStep 7671563 = 11507345) B11507345
theorem B5114375 : Blo 2271435 5114375 := bstep (se 1 (by rfl) ⟨3835781, by rfl⟩ : syracuseStep 5114375 = 7671563) B7671563
theorem B3409583 : Blo 2271435 3409583 := bstep (se 1 (by rfl) ⟨2557187, by rfl⟩ : syracuseStep 3409583 = 5114375) B5114375
theorem B2273055 : Blo 2271435 2273055 := bstep (se 1 (by rfl) ⟨1704791, by rfl⟩ : syracuseStep 2273055 = 3409583) B3409583
theorem B3409589 : Blo 2271435 3409589 := bbase (se 5 (by rfl) ⟨159824, by rfl⟩ : syracuseStep 3409589 = 319649) (by norm_num)
theorem B2273059 : Blo 2271435 2273059 := bstep (se 1 (by rfl) ⟨1704794, by rfl⟩ : syracuseStep 2273059 = 3409589) B3409589
theorem B5753693 : Blo 2271435 5753693 := bbase (se 3 (by rfl) ⟨1078817, by rfl⟩ : syracuseStep 5753693 = 2157635) (by norm_num)
theorem B3835795 : Blo 2271435 3835795 := bstep (se 1 (by rfl) ⟨2876846, by rfl⟩ : syracuseStep 3835795 = 5753693) B5753693
theorem B5114393 : Blo 2271435 5114393 := bstep (se 2 (by rfl) ⟨1917897, by rfl⟩ : syracuseStep 5114393 = 3835795) B3835795
theorem B3409595 : Blo 2271435 3409595 := bstep (se 1 (by rfl) ⟨2557196, by rfl⟩ : syracuseStep 3409595 = 5114393) B5114393
theorem B2273063 : Blo 2271435 2273063 := bstep (se 1 (by rfl) ⟨1704797, by rfl⟩ : syracuseStep 2273063 = 3409595) B3409595
theorem B2557201 : Blo 2271435 2557201 := bbase (se 2 (by rfl) ⟨958950, by rfl⟩ : syracuseStep 2557201 = 1917901) (by norm_num)
theorem B3409601 : Blo 2271435 3409601 := bstep (se 2 (by rfl) ⟨1278600, by rfl⟩ : syracuseStep 3409601 = 2557201) B2557201
theorem B2273067 : Blo 2271435 2273067 := bstep (se 1 (by rfl) ⟨1704800, by rfl⟩ : syracuseStep 2273067 = 3409601) B3409601
theorem B4315285 : Blo 2271435 4315285 := bbase (se 6 (by rfl) ⟨101139, by rfl⟩ : syracuseStep 4315285 = 202279) (by norm_num)
theorem B5753713 : Blo 2271435 5753713 := bstep (se 2 (by rfl) ⟨2157642, by rfl⟩ : syracuseStep 5753713 = 4315285) B4315285
theorem B7671617 : Blo 2271435 7671617 := bstep (se 2 (by rfl) ⟨2876856, by rfl⟩ : syracuseStep 7671617 = 5753713) B5753713
theorem B5114411 : Blo 2271435 5114411 := bstep (se 1 (by rfl) ⟨3835808, by rfl⟩ : syracuseStep 5114411 = 7671617) B7671617
theorem B3409607 : Blo 2271435 3409607 := bstep (se 1 (by rfl) ⟨2557205, by rfl⟩ : syracuseStep 3409607 = 5114411) B5114411
theorem B2273071 : Blo 2271435 2273071 := bstep (se 1 (by rfl) ⟨1704803, by rfl⟩ : syracuseStep 2273071 = 3409607) B3409607
theorem B3409613 : Blo 2271435 3409613 := bbase (se 3 (by rfl) ⟨639302, by rfl⟩ : syracuseStep 3409613 = 1278605) (by norm_num)
theorem B2273075 : Blo 2271435 2273075 := bstep (se 1 (by rfl) ⟨1704806, by rfl⟩ : syracuseStep 2273075 = 3409613) B3409613
theorem B5114429 : Blo 2271435 5114429 := bbase (se 3 (by rfl) ⟨958955, by rfl⟩ : syracuseStep 5114429 = 1917911) (by norm_num)
theorem B3409619 : Blo 2271435 3409619 := bstep (se 1 (by rfl) ⟨2557214, by rfl⟩ : syracuseStep 3409619 = 5114429) B5114429
theorem B2273079 : Blo 2271435 2273079 := bstep (se 1 (by rfl) ⟨1704809, by rfl⟩ : syracuseStep 2273079 = 3409619) B3409619
theorem B3835829 : Blo 2271435 3835829 := bbase (se 5 (by rfl) ⟨179804, by rfl⟩ : syracuseStep 3835829 = 359609) (by norm_num)
theorem B2557219 : Blo 2271435 2557219 := bstep (se 1 (by rfl) ⟨1917914, by rfl⟩ : syracuseStep 2557219 = 3835829) B3835829
theorem B3409625 : Blo 2271435 3409625 := bstep (se 2 (by rfl) ⟨1278609, by rfl⟩ : syracuseStep 3409625 = 2557219) B2557219
theorem B2273083 : Blo 2271435 2273083 := bstep (se 1 (by rfl) ⟨1704812, by rfl⟩ : syracuseStep 2273083 = 3409625) B3409625
theorem B2427365 : Blo 2271435 2427365 := bbase (se 4 (by rfl) ⟨227565, by rfl⟩ : syracuseStep 2427365 = 455131) (by norm_num)
theorem B6472973 : Blo 2271435 6472973 := bstep (se 3 (by rfl) ⟨1213682, by rfl⟩ : syracuseStep 6472973 = 2427365) B2427365
theorem B17261261 : Blo 2271435 17261261 := bstep (se 3 (by rfl) ⟨3236486, by rfl⟩ : syracuseStep 17261261 = 6472973) B6472973
theorem B11507507 : Blo 2271435 11507507 := bstep (se 1 (by rfl) ⟨8630630, by rfl⟩ : syracuseStep 11507507 = 17261261) B17261261
theorem B7671671 : Blo 2271435 7671671 := bstep (se 1 (by rfl) ⟨5753753, by rfl⟩ : syracuseStep 7671671 = 11507507) B11507507
theorem B5114447 : Blo 2271435 5114447 := bstep (se 1 (by rfl) ⟨3835835, by rfl⟩ : syracuseStep 5114447 = 7671671) B7671671
theorem B3409631 : Blo 2271435 3409631 := bstep (se 1 (by rfl) ⟨2557223, by rfl⟩ : syracuseStep 3409631 = 5114447) B5114447
theorem B2273087 : Blo 2271435 2273087 := bstep (se 1 (by rfl) ⟨1704815, by rfl⟩ : syracuseStep 2273087 = 3409631) B3409631
theorem B3409637 : Blo 2271435 3409637 := bbase (se 4 (by rfl) ⟨319653, by rfl⟩ : syracuseStep 3409637 = 639307) (by norm_num)
theorem B2273091 : Blo 2271435 2273091 := bstep (se 1 (by rfl) ⟨1704818, by rfl⟩ : syracuseStep 2273091 = 3409637) B3409637
theorem B6472997 : Blo 2271435 6472997 := bbase (se 4 (by rfl) ⟨606843, by rfl⟩ : syracuseStep 6472997 = 1213687) (by norm_num)
theorem B4315331 : Blo 2271435 4315331 := bstep (se 1 (by rfl) ⟨3236498, by rfl⟩ : syracuseStep 4315331 = 6472997) B6472997
theorem B2876887 : Blo 2271435 2876887 := bstep (se 1 (by rfl) ⟨2157665, by rfl⟩ : syracuseStep 2876887 = 4315331) B4315331
theorem B3835849 : Blo 2271435 3835849 := bstep (se 2 (by rfl) ⟨1438443, by rfl⟩ : syracuseStep 3835849 = 2876887) B2876887
theorem B5114465 : Blo 2271435 5114465 := bstep (se 2 (by rfl) ⟨1917924, by rfl⟩ : syracuseStep 5114465 = 3835849) B3835849
theorem B3409643 : Blo 2271435 3409643 := bstep (se 1 (by rfl) ⟨2557232, by rfl⟩ : syracuseStep 3409643 = 5114465) B5114465
theorem B2273095 : Blo 2271435 2273095 := bstep (se 1 (by rfl) ⟨1704821, by rfl⟩ : syracuseStep 2273095 = 3409643) B3409643
theorem B2557237 : Blo 2271435 2557237 := bbase (se 5 (by rfl) ⟨119870, by rfl⟩ : syracuseStep 2557237 = 239741) (by norm_num)
theorem B3409649 : Blo 2271435 3409649 := bstep (se 2 (by rfl) ⟨1278618, by rfl⟩ : syracuseStep 3409649 = 2557237) B2557237
theorem B2273099 : Blo 2271435 2273099 := bstep (se 1 (by rfl) ⟨1704824, by rfl⟩ : syracuseStep 2273099 = 3409649) B3409649
theorem B2876897 : Blo 2271435 2876897 := bbase (se 2 (by rfl) ⟨1078836, by rfl⟩ : syracuseStep 2876897 = 2157673) (by norm_num)
theorem B7671725 : Blo 2271435 7671725 := bstep (se 3 (by rfl) ⟨1438448, by rfl⟩ : syracuseStep 7671725 = 2876897) B2876897
theorem B5114483 : Blo 2271435 5114483 := bstep (se 1 (by rfl) ⟨3835862, by rfl⟩ : syracuseStep 5114483 = 7671725) B7671725
theorem B3409655 : Blo 2271435 3409655 := bstep (se 1 (by rfl) ⟨2557241, by rfl⟩ : syracuseStep 3409655 = 5114483) B5114483
theorem B2273103 : Blo 2271435 2273103 := bstep (se 1 (by rfl) ⟨1704827, by rfl⟩ : syracuseStep 2273103 = 3409655) B3409655
theorem B3409661 : Blo 2271435 3409661 := bbase (se 3 (by rfl) ⟨639311, by rfl⟩ : syracuseStep 3409661 = 1278623) (by norm_num)
theorem B2273107 : Blo 2271435 2273107 := bstep (se 1 (by rfl) ⟨1704830, by rfl⟩ : syracuseStep 2273107 = 3409661) B3409661
theorem B5114501 : Blo 2271435 5114501 := bbase (se 4 (by rfl) ⟨479484, by rfl⟩ : syracuseStep 5114501 = 958969) (by norm_num)
theorem B3409667 : Blo 2271435 3409667 := bstep (se 1 (by rfl) ⟨2557250, by rfl⟩ : syracuseStep 3409667 = 5114501) B5114501
theorem B2273111 : Blo 2271435 2273111 := bstep (se 1 (by rfl) ⟨1704833, by rfl⟩ : syracuseStep 2273111 = 3409667) B3409667
theorem B3072173 : Blo 2271435 3072173 := bbase (se 3 (by rfl) ⟨576032, by rfl⟩ : syracuseStep 3072173 = 1152065) (by norm_num)
theorem B8192461 : Blo 2271435 8192461 := bstep (se 3 (by rfl) ⟨1536086, by rfl⟩ : syracuseStep 8192461 = 3072173) B3072173
theorem B10923281 : Blo 2271435 10923281 := bstep (se 2 (by rfl) ⟨4096230, by rfl⟩ : syracuseStep 10923281 = 8192461) B8192461
theorem B7282187 : Blo 2271435 7282187 := bstep (se 1 (by rfl) ⟨5461640, by rfl⟩ : syracuseStep 7282187 = 10923281) B10923281
theorem B4854791 : Blo 2271435 4854791 := bstep (se 1 (by rfl) ⟨3641093, by rfl⟩ : syracuseStep 4854791 = 7282187) B7282187
theorem B3236527 : Blo 2271435 3236527 := bstep (se 1 (by rfl) ⟨2427395, by rfl⟩ : syracuseStep 3236527 = 4854791) B4854791
theorem B4315369 : Blo 2271435 4315369 := bstep (se 2 (by rfl) ⟨1618263, by rfl⟩ : syracuseStep 4315369 = 3236527) B3236527
theorem B5753825 : Blo 2271435 5753825 := bstep (se 2 (by rfl) ⟨2157684, by rfl⟩ : syracuseStep 5753825 = 4315369) B4315369
theorem B3835883 : Blo 2271435 3835883 := bstep (se 1 (by rfl) ⟨2876912, by rfl⟩ : syracuseStep 3835883 = 5753825) B5753825
theorem B2557255 : Blo 2271435 2557255 := bstep (se 1 (by rfl) ⟨1917941, by rfl⟩ : syracuseStep 2557255 = 3835883) B3835883
theorem B3409673 : Blo 2271435 3409673 := bstep (se 2 (by rfl) ⟨1278627, by rfl⟩ : syracuseStep 3409673 = 2557255) B2557255
theorem B2273115 : Blo 2271435 2273115 := bstep (se 1 (by rfl) ⟨1704836, by rfl⟩ : syracuseStep 2273115 = 3409673) B3409673
theorem B11507669 : Blo 2271435 11507669 := bbase (se 7 (by rfl) ⟨134855, by rfl⟩ : syracuseStep 11507669 = 269711) (by norm_num)
theorem B7671779 : Blo 2271435 7671779 := bstep (se 1 (by rfl) ⟨5753834, by rfl⟩ : syracuseStep 7671779 = 11507669) B11507669
theorem B5114519 : Blo 2271435 5114519 := bstep (se 1 (by rfl) ⟨3835889, by rfl⟩ : syracuseStep 5114519 = 7671779) B7671779
theorem B3409679 : Blo 2271435 3409679 := bstep (se 1 (by rfl) ⟨2557259, by rfl⟩ : syracuseStep 3409679 = 5114519) B5114519
theorem B2273119 : Blo 2271435 2273119 := bstep (se 1 (by rfl) ⟨1704839, by rfl⟩ : syracuseStep 2273119 = 3409679) B3409679
theorem B3409685 : Blo 2271435 3409685 := bbase (se 6 (by rfl) ⟨79914, by rfl⟩ : syracuseStep 3409685 = 159829) (by norm_num)
theorem B2273123 : Blo 2271435 2273123 := bstep (se 1 (by rfl) ⟨1704842, by rfl⟩ : syracuseStep 2273123 = 3409685) B3409685
theorem B13122805 : Blo 2271435 13122805 := bbase (se 5 (by rfl) ⟨615131, by rfl⟩ : syracuseStep 13122805 = 1230263) (by norm_num)
theorem B17497073 : Blo 2271435 17497073 := bstep (se 2 (by rfl) ⟨6561402, by rfl⟩ : syracuseStep 17497073 = 13122805) B13122805
theorem B11664715 : Blo 2271435 11664715 := bstep (se 1 (by rfl) ⟨8748536, by rfl⟩ : syracuseStep 11664715 = 17497073) B17497073
theorem B15552953 : Blo 2271435 15552953 := bstep (se 2 (by rfl) ⟨5832357, by rfl⟩ : syracuseStep 15552953 = 11664715) B11664715
theorem B165898165 : Blo 2271435 165898165 := bstep (se 5 (by rfl) ⟨7776476, by rfl⟩ : syracuseStep 165898165 = 15552953) B15552953
theorem B221197553 : Blo 2271435 221197553 := bstep (se 2 (by rfl) ⟨82949082, by rfl⟩ : syracuseStep 221197553 = 165898165) B165898165
theorem B147465035 : Blo 2271435 147465035 := bstep (se 1 (by rfl) ⟨110598776, by rfl⟩ : syracuseStep 147465035 = 221197553) B221197553
theorem B98310023 : Blo 2271435 98310023 := bstep (se 1 (by rfl) ⟨73732517, by rfl⟩ : syracuseStep 98310023 = 147465035) B147465035
theorem B65540015 : Blo 2271435 65540015 := bstep (se 1 (by rfl) ⟨49155011, by rfl⟩ : syracuseStep 65540015 = 98310023) B98310023
theorem B43693343 : Blo 2271435 43693343 := bstep (se 1 (by rfl) ⟨32770007, by rfl⟩ : syracuseStep 43693343 = 65540015) B65540015
theorem B29128895 : Blo 2271435 29128895 := bstep (se 1 (by rfl) ⟨21846671, by rfl⟩ : syracuseStep 29128895 = 43693343) B43693343
theorem B19419263 : Blo 2271435 19419263 := bstep (se 1 (by rfl) ⟨14564447, by rfl⟩ : syracuseStep 19419263 = 29128895) B29128895
theorem B12946175 : Blo 2271435 12946175 := bstep (se 1 (by rfl) ⟨9709631, by rfl⟩ : syracuseStep 12946175 = 19419263) B19419263
theorem B8630783 : Blo 2271435 8630783 := bstep (se 1 (by rfl) ⟨6473087, by rfl⟩ : syracuseStep 8630783 = 12946175) B12946175
theorem B5753855 : Blo 2271435 5753855 := bstep (se 1 (by rfl) ⟨4315391, by rfl⟩ : syracuseStep 5753855 = 8630783) B8630783
theorem B3835903 : Blo 2271435 3835903 := bstep (se 1 (by rfl) ⟨2876927, by rfl⟩ : syracuseStep 3835903 = 5753855) B5753855
theorem B5114537 : Blo 2271435 5114537 := bstep (se 2 (by rfl) ⟨1917951, by rfl⟩ : syracuseStep 5114537 = 3835903) B3835903
theorem B3409691 : Blo 2271435 3409691 := bstep (se 1 (by rfl) ⟨2557268, by rfl⟩ : syracuseStep 3409691 = 5114537) B5114537
theorem B2273127 : Blo 2271435 2273127 := bstep (se 1 (by rfl) ⟨1704845, by rfl⟩ : syracuseStep 2273127 = 3409691) B3409691
theorem B2557273 : Blo 2271435 2557273 := bbase (se 2 (by rfl) ⟨958977, by rfl⟩ : syracuseStep 2557273 = 1917955) (by norm_num)
theorem B3409697 : Blo 2271435 3409697 := bstep (se 2 (by rfl) ⟨1278636, by rfl⟩ : syracuseStep 3409697 = 2557273) B2557273
theorem B2273131 : Blo 2271435 2273131 := bstep (se 1 (by rfl) ⟨1704848, by rfl⟩ : syracuseStep 2273131 = 3409697) B3409697
theorem B3641125 : Blo 2271435 3641125 := bbase (se 4 (by rfl) ⟨341355, by rfl⟩ : syracuseStep 3641125 = 682711) (by norm_num)
theorem B4854833 : Blo 2271435 4854833 := bstep (se 2 (by rfl) ⟨1820562, by rfl⟩ : syracuseStep 4854833 = 3641125) B3641125
theorem B3236555 : Blo 2271435 3236555 := bstep (se 1 (by rfl) ⟨2427416, by rfl⟩ : syracuseStep 3236555 = 4854833) B4854833
theorem B8630813 : Blo 2271435 8630813 := bstep (se 3 (by rfl) ⟨1618277, by rfl⟩ : syracuseStep 8630813 = 3236555) B3236555
theorem B5753875 : Blo 2271435 5753875 := bstep (se 1 (by rfl) ⟨4315406, by rfl⟩ : syracuseStep 5753875 = 8630813) B8630813
theorem B7671833 : Blo 2271435 7671833 := bstep (se 2 (by rfl) ⟨2876937, by rfl⟩ : syracuseStep 7671833 = 5753875) B5753875
theorem B5114555 : Blo 2271435 5114555 := bstep (se 1 (by rfl) ⟨3835916, by rfl⟩ : syracuseStep 5114555 = 7671833) B7671833
theorem B3409703 : Blo 2271435 3409703 := bstep (se 1 (by rfl) ⟨2557277, by rfl⟩ : syracuseStep 3409703 = 5114555) B5114555
theorem B2273135 : Blo 2271435 2273135 := bstep (se 1 (by rfl) ⟨1704851, by rfl⟩ : syracuseStep 2273135 = 3409703) B3409703
theorem B3409709 : Blo 2271435 3409709 := bbase (se 3 (by rfl) ⟨639320, by rfl⟩ : syracuseStep 3409709 = 1278641) (by norm_num)
theorem B2273139 : Blo 2271435 2273139 := bstep (se 1 (by rfl) ⟨1704854, by rfl⟩ : syracuseStep 2273139 = 3409709) B3409709
theorem B5114573 : Blo 2271435 5114573 := bbase (se 3 (by rfl) ⟨958982, by rfl⟩ : syracuseStep 5114573 = 1917965) (by norm_num)
theorem B3409715 : Blo 2271435 3409715 := bstep (se 1 (by rfl) ⟨2557286, by rfl⟩ : syracuseStep 3409715 = 5114573) B5114573
theorem B2273143 : Blo 2271435 2273143 := bstep (se 1 (by rfl) ⟨1704857, by rfl⟩ : syracuseStep 2273143 = 3409715) B3409715
theorem B2876953 : Blo 2271435 2876953 := bbase (se 2 (by rfl) ⟨1078857, by rfl⟩ : syracuseStep 2876953 = 2157715) (by norm_num)
theorem B3835937 : Blo 2271435 3835937 := bstep (se 2 (by rfl) ⟨1438476, by rfl⟩ : syracuseStep 3835937 = 2876953) B2876953
theorem B2557291 : Blo 2271435 2557291 := bstep (se 1 (by rfl) ⟨1917968, by rfl⟩ : syracuseStep 2557291 = 3835937) B3835937
theorem B3409721 : Blo 2271435 3409721 := bstep (se 2 (by rfl) ⟨1278645, by rfl⟩ : syracuseStep 3409721 = 2557291) B2557291
theorem B2273147 : Blo 2271435 2273147 := bstep (se 1 (by rfl) ⟨1704860, by rfl⟩ : syracuseStep 2273147 = 3409721) B3409721
theorem B9709733 : Blo 2271435 9709733 := bbase (se 4 (by rfl) ⟨910287, by rfl⟩ : syracuseStep 9709733 = 1820575) (by norm_num)
theorem B25892621 : Blo 2271435 25892621 := bstep (se 3 (by rfl) ⟨4854866, by rfl⟩ : syracuseStep 25892621 = 9709733) B9709733
theorem B17261747 : Blo 2271435 17261747 := bstep (se 1 (by rfl) ⟨12946310, by rfl⟩ : syracuseStep 17261747 = 25892621) B25892621
theorem B11507831 : Blo 2271435 11507831 := bstep (se 1 (by rfl) ⟨8630873, by rfl⟩ : syracuseStep 11507831 = 17261747) B17261747
theorem B7671887 : Blo 2271435 7671887 := bstep (se 1 (by rfl) ⟨5753915, by rfl⟩ : syracuseStep 7671887 = 11507831) B11507831
theorem B5114591 : Blo 2271435 5114591 := bstep (se 1 (by rfl) ⟨3835943, by rfl⟩ : syracuseStep 5114591 = 7671887) B7671887
theorem B3409727 : Blo 2271435 3409727 := bstep (se 1 (by rfl) ⟨2557295, by rfl⟩ : syracuseStep 3409727 = 5114591) B5114591
theorem B2273151 : Blo 2271435 2273151 := bstep (se 1 (by rfl) ⟨1704863, by rfl⟩ : syracuseStep 2273151 = 3409727) B3409727
theorem B3409733 : Blo 2271435 3409733 := bbase (se 4 (by rfl) ⟨319662, by rfl⟩ : syracuseStep 3409733 = 639325) (by norm_num)
theorem B2273155 : Blo 2271435 2273155 := bstep (se 1 (by rfl) ⟨1704866, by rfl⟩ : syracuseStep 2273155 = 3409733) B3409733
theorem B3835957 : Blo 2271435 3835957 := bbase (se 5 (by rfl) ⟨179810, by rfl⟩ : syracuseStep 3835957 = 359621) (by norm_num)
theorem B5114609 : Blo 2271435 5114609 := bstep (se 2 (by rfl) ⟨1917978, by rfl⟩ : syracuseStep 5114609 = 3835957) B3835957
theorem B3409739 : Blo 2271435 3409739 := bstep (se 1 (by rfl) ⟨2557304, by rfl⟩ : syracuseStep 3409739 = 5114609) B5114609
theorem B2273159 : Blo 2271435 2273159 := bstep (se 1 (by rfl) ⟨1704869, by rfl⟩ : syracuseStep 2273159 = 3409739) B3409739
theorem B2557309 : Blo 2271435 2557309 := bbase (se 3 (by rfl) ⟨479495, by rfl⟩ : syracuseStep 2557309 = 958991) (by norm_num)
theorem B3409745 : Blo 2271435 3409745 := bstep (se 2 (by rfl) ⟨1278654, by rfl⟩ : syracuseStep 3409745 = 2557309) B2557309
theorem B2273163 : Blo 2271435 2273163 := bstep (se 1 (by rfl) ⟨1704872, by rfl⟩ : syracuseStep 2273163 = 3409745) B3409745
theorem B7671941 : Blo 2271435 7671941 := bbase (se 4 (by rfl) ⟨719244, by rfl⟩ : syracuseStep 7671941 = 1438489) (by norm_num)
theorem B5114627 : Blo 2271435 5114627 := bstep (se 1 (by rfl) ⟨3835970, by rfl⟩ : syracuseStep 5114627 = 7671941) B7671941
theorem B3409751 : Blo 2271435 3409751 := bstep (se 1 (by rfl) ⟨2557313, by rfl⟩ : syracuseStep 3409751 = 5114627) B5114627
theorem B2273167 : Blo 2271435 2273167 := bstep (se 1 (by rfl) ⟨1704875, by rfl⟩ : syracuseStep 2273167 = 3409751) B3409751
theorem B3409757 : Blo 2271435 3409757 := bbase (se 3 (by rfl) ⟨639329, by rfl⟩ : syracuseStep 3409757 = 1278659) (by norm_num)
theorem B2273171 : Blo 2271435 2273171 := bstep (se 1 (by rfl) ⟨1704878, by rfl⟩ : syracuseStep 2273171 = 3409757) B3409757
theorem B5114645 : Blo 2271435 5114645 := bbase (se 6 (by rfl) ⟨119874, by rfl⟩ : syracuseStep 5114645 = 239749) (by norm_num)
theorem B3409763 : Blo 2271435 3409763 := bstep (se 1 (by rfl) ⟨2557322, by rfl⟩ : syracuseStep 3409763 = 5114645) B5114645
theorem B2273175 : Blo 2271435 2273175 := bstep (se 1 (by rfl) ⟨1704881, by rfl⟩ : syracuseStep 2273175 = 3409763) B3409763
theorem B8630981 : Blo 2271435 8630981 := bbase (se 4 (by rfl) ⟨809154, by rfl⟩ : syracuseStep 8630981 = 1618309) (by norm_num)
theorem B5753987 : Blo 2271435 5753987 := bstep (se 1 (by rfl) ⟨4315490, by rfl⟩ : syracuseStep 5753987 = 8630981) B8630981
theorem B3835991 : Blo 2271435 3835991 := bstep (se 1 (by rfl) ⟨2876993, by rfl⟩ : syracuseStep 3835991 = 5753987) B5753987
theorem B2557327 : Blo 2271435 2557327 := bstep (se 1 (by rfl) ⟨1917995, by rfl⟩ : syracuseStep 2557327 = 3835991) B3835991
theorem B3409769 : Blo 2271435 3409769 := bstep (se 2 (by rfl) ⟨1278663, by rfl⟩ : syracuseStep 3409769 = 2557327) B2557327
theorem B2273179 : Blo 2271435 2273179 := bstep (se 1 (by rfl) ⟨1704884, by rfl⟩ : syracuseStep 2273179 = 3409769) B3409769
theorem B10923605 : Blo 2271435 10923605 := bbase (se 8 (by rfl) ⟨64005, by rfl⟩ : syracuseStep 10923605 = 128011) (by norm_num)
theorem B7282403 : Blo 2271435 7282403 := bstep (se 1 (by rfl) ⟨5461802, by rfl⟩ : syracuseStep 7282403 = 10923605) B10923605
theorem B4854935 : Blo 2271435 4854935 := bstep (se 1 (by rfl) ⟨3641201, by rfl⟩ : syracuseStep 4854935 = 7282403) B7282403
theorem B12946493 : Blo 2271435 12946493 := bstep (se 3 (by rfl) ⟨2427467, by rfl⟩ : syracuseStep 12946493 = 4854935) B4854935
theorem B8630995 : Blo 2271435 8630995 := bstep (se 1 (by rfl) ⟨6473246, by rfl⟩ : syracuseStep 8630995 = 12946493) B12946493
theorem B11507993 : Blo 2271435 11507993 := bstep (se 2 (by rfl) ⟨4315497, by rfl⟩ : syracuseStep 11507993 = 8630995) B8630995
theorem B7671995 : Blo 2271435 7671995 := bstep (se 1 (by rfl) ⟨5753996, by rfl⟩ : syracuseStep 7671995 = 11507993) B11507993
theorem B5114663 : Blo 2271435 5114663 := bstep (se 1 (by rfl) ⟨3835997, by rfl⟩ : syracuseStep 5114663 = 7671995) B7671995
theorem B3409775 : Blo 2271435 3409775 := bstep (se 1 (by rfl) ⟨2557331, by rfl⟩ : syracuseStep 3409775 = 5114663) B5114663
theorem B2273183 : Blo 2271435 2273183 := bstep (se 1 (by rfl) ⟨1704887, by rfl⟩ : syracuseStep 2273183 = 3409775) B3409775
theorem B3409781 : Blo 2271435 3409781 := bbase (se 5 (by rfl) ⟨159833, by rfl⟩ : syracuseStep 3409781 = 319667) (by norm_num)
theorem B2273187 : Blo 2271435 2273187 := bstep (se 1 (by rfl) ⟨1704890, by rfl⟩ : syracuseStep 2273187 = 3409781) B3409781
theorem B15553397 : Blo 2271435 15553397 := bbase (se 5 (by rfl) ⟨729065, by rfl⟩ : syracuseStep 15553397 = 1458131) (by norm_num)
theorem B41475725 : Blo 2271435 41475725 := bstep (se 3 (by rfl) ⟨7776698, by rfl⟩ : syracuseStep 41475725 = 15553397) B15553397
theorem B27650483 : Blo 2271435 27650483 := bstep (se 1 (by rfl) ⟨20737862, by rfl⟩ : syracuseStep 27650483 = 41475725) B41475725
theorem B18433655 : Blo 2271435 18433655 := bstep (se 1 (by rfl) ⟨13825241, by rfl⟩ : syracuseStep 18433655 = 27650483) B27650483
theorem B12289103 : Blo 2271435 12289103 := bstep (se 1 (by rfl) ⟨9216827, by rfl⟩ : syracuseStep 12289103 = 18433655) B18433655
theorem B8192735 : Blo 2271435 8192735 := bstep (se 1 (by rfl) ⟨6144551, by rfl⟩ : syracuseStep 8192735 = 12289103) B12289103
theorem B5461823 : Blo 2271435 5461823 := bstep (se 1 (by rfl) ⟨4096367, by rfl⟩ : syracuseStep 5461823 = 8192735) B8192735
theorem B3641215 : Blo 2271435 3641215 := bstep (se 1 (by rfl) ⟨2730911, by rfl⟩ : syracuseStep 3641215 = 5461823) B5461823
theorem B4854953 : Blo 2271435 4854953 := bstep (se 2 (by rfl) ⟨1820607, by rfl⟩ : syracuseStep 4854953 = 3641215) B3641215
theorem B3236635 : Blo 2271435 3236635 := bstep (se 1 (by rfl) ⟨2427476, by rfl⟩ : syracuseStep 3236635 = 4854953) B4854953
theorem B4315513 : Blo 2271435 4315513 := bstep (se 2 (by rfl) ⟨1618317, by rfl⟩ : syracuseStep 4315513 = 3236635) B3236635
theorem B5754017 : Blo 2271435 5754017 := bstep (se 2 (by rfl) ⟨2157756, by rfl⟩ : syracuseStep 5754017 = 4315513) B4315513
theorem B3836011 : Blo 2271435 3836011 := bstep (se 1 (by rfl) ⟨2877008, by rfl⟩ : syracuseStep 3836011 = 5754017) B5754017
theorem B5114681 : Blo 2271435 5114681 := bstep (se 2 (by rfl) ⟨1918005, by rfl⟩ : syracuseStep 5114681 = 3836011) B3836011
theorem B3409787 : Blo 2271435 3409787 := bstep (se 1 (by rfl) ⟨2557340, by rfl⟩ : syracuseStep 3409787 = 5114681) B5114681
theorem B2273191 : Blo 2271435 2273191 := bstep (se 1 (by rfl) ⟨1704893, by rfl⟩ : syracuseStep 2273191 = 3409787) B3409787
theorem B2557345 : Blo 2271435 2557345 := bbase (se 2 (by rfl) ⟨959004, by rfl⟩ : syracuseStep 2557345 = 1918009) (by norm_num)
theorem B3409793 : Blo 2271435 3409793 := bstep (se 2 (by rfl) ⟨1278672, by rfl⟩ : syracuseStep 3409793 = 2557345) B2557345
theorem B2273195 : Blo 2271435 2273195 := bstep (se 1 (by rfl) ⟨1704896, by rfl⟩ : syracuseStep 2273195 = 3409793) B3409793
theorem B5754037 : Blo 2271435 5754037 := bbase (se 5 (by rfl) ⟨269720, by rfl⟩ : syracuseStep 5754037 = 539441) (by norm_num)
theorem B7672049 : Blo 2271435 7672049 := bstep (se 2 (by rfl) ⟨2877018, by rfl⟩ : syracuseStep 7672049 = 5754037) B5754037
theorem B5114699 : Blo 2271435 5114699 := bstep (se 1 (by rfl) ⟨3836024, by rfl⟩ : syracuseStep 5114699 = 7672049) B7672049
theorem B3409799 : Blo 2271435 3409799 := bstep (se 1 (by rfl) ⟨2557349, by rfl⟩ : syracuseStep 3409799 = 5114699) B5114699
theorem B2273199 : Blo 2271435 2273199 := bstep (se 1 (by rfl) ⟨1704899, by rfl⟩ : syracuseStep 2273199 = 3409799) B3409799
theorem B3409805 : Blo 2271435 3409805 := bbase (se 3 (by rfl) ⟨639338, by rfl⟩ : syracuseStep 3409805 = 1278677) (by norm_num)
theorem B2273203 : Blo 2271435 2273203 := bstep (se 1 (by rfl) ⟨1704902, by rfl⟩ : syracuseStep 2273203 = 3409805) B3409805
theorem B5114717 : Blo 2271435 5114717 := bbase (se 3 (by rfl) ⟨959009, by rfl⟩ : syracuseStep 5114717 = 1918019) (by norm_num)
theorem B3409811 : Blo 2271435 3409811 := bstep (se 1 (by rfl) ⟨2557358, by rfl⟩ : syracuseStep 3409811 = 5114717) B5114717
theorem B2273207 : Blo 2271435 2273207 := bstep (se 1 (by rfl) ⟨1704905, by rfl⟩ : syracuseStep 2273207 = 3409811) B3409811
theorem B3836045 : Blo 2271435 3836045 := bbase (se 3 (by rfl) ⟨719258, by rfl⟩ : syracuseStep 3836045 = 1438517) (by norm_num)
theorem B2557363 : Blo 2271435 2557363 := bstep (se 1 (by rfl) ⟨1918022, by rfl⟩ : syracuseStep 2557363 = 3836045) B3836045
theorem B3409817 : Blo 2271435 3409817 := bstep (se 2 (by rfl) ⟨1278681, by rfl⟩ : syracuseStep 3409817 = 2557363) B2557363
theorem B2273211 : Blo 2271435 2273211 := bstep (se 1 (by rfl) ⟨1704908, by rfl⟩ : syracuseStep 2273211 = 3409817) B3409817
theorem B4608461 : Blo 2271435 4608461 := bbase (se 3 (by rfl) ⟨864086, by rfl⟩ : syracuseStep 4608461 = 1728173) (by norm_num)
theorem B12289229 : Blo 2271435 12289229 := bstep (se 3 (by rfl) ⟨2304230, by rfl⟩ : syracuseStep 12289229 = 4608461) B4608461
theorem B8192819 : Blo 2271435 8192819 := bstep (se 1 (by rfl) ⟨6144614, by rfl⟩ : syracuseStep 8192819 = 12289229) B12289229
theorem B5461879 : Blo 2271435 5461879 := bstep (se 1 (by rfl) ⟨4096409, by rfl⟩ : syracuseStep 5461879 = 8192819) B8192819
theorem B7282505 : Blo 2271435 7282505 := bstep (se 2 (by rfl) ⟨2730939, by rfl⟩ : syracuseStep 7282505 = 5461879) B5461879
theorem B19420013 : Blo 2271435 19420013 := bstep (se 3 (by rfl) ⟨3641252, by rfl⟩ : syracuseStep 19420013 = 7282505) B7282505
theorem B12946675 : Blo 2271435 12946675 := bstep (se 1 (by rfl) ⟨9710006, by rfl⟩ : syracuseStep 12946675 = 19420013) B19420013
theorem B17262233 : Blo 2271435 17262233 := bstep (se 2 (by rfl) ⟨6473337, by rfl⟩ : syracuseStep 17262233 = 12946675) B12946675
theorem B11508155 : Blo 2271435 11508155 := bstep (se 1 (by rfl) ⟨8631116, by rfl⟩ : syracuseStep 11508155 = 17262233) B17262233
theorem B7672103 : Blo 2271435 7672103 := bstep (se 1 (by rfl) ⟨5754077, by rfl⟩ : syracuseStep 7672103 = 11508155) B11508155
theorem B5114735 : Blo 2271435 5114735 := bstep (se 1 (by rfl) ⟨3836051, by rfl⟩ : syracuseStep 5114735 = 7672103) B7672103
theorem B3409823 : Blo 2271435 3409823 := bstep (se 1 (by rfl) ⟨2557367, by rfl⟩ : syracuseStep 3409823 = 5114735) B5114735
theorem B2273215 : Blo 2271435 2273215 := bstep (se 1 (by rfl) ⟨1704911, by rfl⟩ : syracuseStep 2273215 = 3409823) B3409823
theorem B3409829 : Blo 2271435 3409829 := bbase (se 4 (by rfl) ⟨319671, by rfl⟩ : syracuseStep 3409829 = 639343) (by norm_num)
theorem B2273219 : Blo 2271435 2273219 := bstep (se 1 (by rfl) ⟨1704914, by rfl⟩ : syracuseStep 2273219 = 3409829) B3409829
theorem B2877049 : Blo 2271435 2877049 := bbase (se 2 (by rfl) ⟨1078893, by rfl⟩ : syracuseStep 2877049 = 2157787) (by norm_num)
theorem B3836065 : Blo 2271435 3836065 := bstep (se 2 (by rfl) ⟨1438524, by rfl⟩ : syracuseStep 3836065 = 2877049) B2877049
theorem B5114753 : Blo 2271435 5114753 := bstep (se 2 (by rfl) ⟨1918032, by rfl⟩ : syracuseStep 5114753 = 3836065) B3836065
theorem B3409835 : Blo 2271435 3409835 := bstep (se 1 (by rfl) ⟨2557376, by rfl⟩ : syracuseStep 3409835 = 5114753) B5114753
theorem B2273223 : Blo 2271435 2273223 := bstep (se 1 (by rfl) ⟨1704917, by rfl⟩ : syracuseStep 2273223 = 3409835) B3409835
theorem B2557381 : Blo 2271435 2557381 := bbase (se 4 (by rfl) ⟨239754, by rfl⟩ : syracuseStep 2557381 = 479509) (by norm_num)
theorem B3409841 : Blo 2271435 3409841 := bstep (se 2 (by rfl) ⟨1278690, by rfl⟩ : syracuseStep 3409841 = 2557381) B2557381
theorem B2273227 : Blo 2271435 2273227 := bstep (se 1 (by rfl) ⟨1704920, by rfl⟩ : syracuseStep 2273227 = 3409841) B3409841
theorem B4315589 : Blo 2271435 4315589 := bbase (se 4 (by rfl) ⟨404586, by rfl⟩ : syracuseStep 4315589 = 809173) (by norm_num)
theorem B2877059 : Blo 2271435 2877059 := bstep (se 1 (by rfl) ⟨2157794, by rfl⟩ : syracuseStep 2877059 = 4315589) B4315589
theorem B7672157 : Blo 2271435 7672157 := bstep (se 3 (by rfl) ⟨1438529, by rfl⟩ : syracuseStep 7672157 = 2877059) B2877059
theorem B5114771 : Blo 2271435 5114771 := bstep (se 1 (by rfl) ⟨3836078, by rfl⟩ : syracuseStep 5114771 = 7672157) B7672157
theorem B3409847 : Blo 2271435 3409847 := bstep (se 1 (by rfl) ⟨2557385, by rfl⟩ : syracuseStep 3409847 = 5114771) B5114771
theorem B2273231 : Blo 2271435 2273231 := bstep (se 1 (by rfl) ⟨1704923, by rfl⟩ : syracuseStep 2273231 = 3409847) B3409847
theorem B3409853 : Blo 2271435 3409853 := bbase (se 3 (by rfl) ⟨639347, by rfl⟩ : syracuseStep 3409853 = 1278695) (by norm_num)
theorem B2273235 : Blo 2271435 2273235 := bstep (se 1 (by rfl) ⟨1704926, by rfl⟩ : syracuseStep 2273235 = 3409853) B3409853
theorem B5114789 : Blo 2271435 5114789 := bbase (se 4 (by rfl) ⟨479511, by rfl⟩ : syracuseStep 5114789 = 959023) (by norm_num)
theorem B3409859 : Blo 2271435 3409859 := bstep (se 1 (by rfl) ⟨2557394, by rfl⟩ : syracuseStep 3409859 = 5114789) B5114789
theorem B2273239 : Blo 2271435 2273239 := bstep (se 1 (by rfl) ⟨1704929, by rfl⟩ : syracuseStep 2273239 = 3409859) B3409859
theorem B5754149 : Blo 2271435 5754149 := bbase (se 4 (by rfl) ⟨539451, by rfl⟩ : syracuseStep 5754149 = 1078903) (by norm_num)
theorem B3836099 : Blo 2271435 3836099 := bstep (se 1 (by rfl) ⟨2877074, by rfl⟩ : syracuseStep 3836099 = 5754149) B5754149
theorem B2557399 : Blo 2271435 2557399 := bstep (se 1 (by rfl) ⟨1918049, by rfl⟩ : syracuseStep 2557399 = 3836099) B3836099
theorem B3409865 : Blo 2271435 3409865 := bstep (se 2 (by rfl) ⟨1278699, by rfl⟩ : syracuseStep 3409865 = 2557399) B2557399
theorem B2273243 : Blo 2271435 2273243 := bstep (se 1 (by rfl) ⟨1704932, by rfl⟩ : syracuseStep 2273243 = 3409865) B3409865
theorem B6473429 : Blo 2271435 6473429 := bbase (se 7 (by rfl) ⟨75860, by rfl⟩ : syracuseStep 6473429 = 151721) (by norm_num)
theorem B4315619 : Blo 2271435 4315619 := bstep (se 1 (by rfl) ⟨3236714, by rfl⟩ : syracuseStep 4315619 = 6473429) B6473429
theorem B11508317 : Blo 2271435 11508317 := bstep (se 3 (by rfl) ⟨2157809, by rfl⟩ : syracuseStep 11508317 = 4315619) B4315619
theorem B7672211 : Blo 2271435 7672211 := bstep (se 1 (by rfl) ⟨5754158, by rfl⟩ : syracuseStep 7672211 = 11508317) B11508317
theorem B5114807 : Blo 2271435 5114807 := bstep (se 1 (by rfl) ⟨3836105, by rfl⟩ : syracuseStep 5114807 = 7672211) B7672211
theorem B3409871 : Blo 2271435 3409871 := bstep (se 1 (by rfl) ⟨2557403, by rfl⟩ : syracuseStep 3409871 = 5114807) B5114807
theorem B2273247 : Blo 2271435 2273247 := bstep (se 1 (by rfl) ⟨1704935, by rfl⟩ : syracuseStep 2273247 = 3409871) B3409871
theorem B3409877 : Blo 2271435 3409877 := bbase (se 7 (by rfl) ⟨39959, by rfl⟩ : syracuseStep 3409877 = 79919) (by norm_num)
theorem B2273251 : Blo 2271435 2273251 := bstep (se 1 (by rfl) ⟨1704938, by rfl⟩ : syracuseStep 2273251 = 3409877) B3409877
theorem B8631269 : Blo 2271435 8631269 := bbase (se 4 (by rfl) ⟨809181, by rfl⟩ : syracuseStep 8631269 = 1618363) (by norm_num)
theorem B5754179 : Blo 2271435 5754179 := bstep (se 1 (by rfl) ⟨4315634, by rfl⟩ : syracuseStep 5754179 = 8631269) B8631269
theorem B3836119 : Blo 2271435 3836119 := bstep (se 1 (by rfl) ⟨2877089, by rfl⟩ : syracuseStep 3836119 = 5754179) B5754179
theorem B5114825 : Blo 2271435 5114825 := bstep (se 2 (by rfl) ⟨1918059, by rfl⟩ : syracuseStep 5114825 = 3836119) B3836119
theorem B3409883 : Blo 2271435 3409883 := bstep (se 1 (by rfl) ⟨2557412, by rfl⟩ : syracuseStep 3409883 = 5114825) B5114825
theorem B2273255 : Blo 2271435 2273255 := bstep (se 1 (by rfl) ⟨1704941, by rfl⟩ : syracuseStep 2273255 = 3409883) B3409883
theorem B2557417 : Blo 2271435 2557417 := bbase (se 2 (by rfl) ⟨959031, by rfl⟩ : syracuseStep 2557417 = 1918063) (by norm_num)
theorem B3409889 : Blo 2271435 3409889 := bstep (se 2 (by rfl) ⟨1278708, by rfl⟩ : syracuseStep 3409889 = 2557417) B2557417
theorem B2273259 : Blo 2271435 2273259 := bstep (se 1 (by rfl) ⟨1704944, by rfl⟩ : syracuseStep 2273259 = 3409889) B3409889
theorem B2427553 : Blo 2271435 2427553 := bbase (se 2 (by rfl) ⟨910332, by rfl⟩ : syracuseStep 2427553 = 1820665) (by norm_num)
theorem B12946949 : Blo 2271435 12946949 := bstep (se 4 (by rfl) ⟨1213776, by rfl⟩ : syracuseStep 12946949 = 2427553) B2427553
theorem B8631299 : Blo 2271435 8631299 := bstep (se 1 (by rfl) ⟨6473474, by rfl⟩ : syracuseStep 8631299 = 12946949) B12946949
theorem B5754199 : Blo 2271435 5754199 := bstep (se 1 (by rfl) ⟨4315649, by rfl⟩ : syracuseStep 5754199 = 8631299) B8631299
theorem B7672265 : Blo 2271435 7672265 := bstep (se 2 (by rfl) ⟨2877099, by rfl⟩ : syracuseStep 7672265 = 5754199) B5754199
theorem B5114843 : Blo 2271435 5114843 := bstep (se 1 (by rfl) ⟨3836132, by rfl⟩ : syracuseStep 5114843 = 7672265) B7672265
theorem B3409895 : Blo 2271435 3409895 := bstep (se 1 (by rfl) ⟨2557421, by rfl⟩ : syracuseStep 3409895 = 5114843) B5114843
theorem B2273263 : Blo 2271435 2273263 := bstep (se 1 (by rfl) ⟨1704947, by rfl⟩ : syracuseStep 2273263 = 3409895) B3409895
theorem B3409901 : Blo 2271435 3409901 := bbase (se 3 (by rfl) ⟨639356, by rfl⟩ : syracuseStep 3409901 = 1278713) (by norm_num)
theorem B2273267 : Blo 2271435 2273267 := bstep (se 1 (by rfl) ⟨1704950, by rfl⟩ : syracuseStep 2273267 = 3409901) B3409901
theorem B5114861 : Blo 2271435 5114861 := bbase (se 3 (by rfl) ⟨959036, by rfl⟩ : syracuseStep 5114861 = 1918073) (by norm_num)
theorem B3409907 : Blo 2271435 3409907 := bstep (se 1 (by rfl) ⟨2557430, by rfl⟩ : syracuseStep 3409907 = 5114861) B5114861
theorem B2273271 : Blo 2271435 2273271 := bstep (se 1 (by rfl) ⟨1704953, by rfl⟩ : syracuseStep 2273271 = 3409907) B3409907
theorem B4855133 : Blo 2271435 4855133 := bbase (se 3 (by rfl) ⟨910337, by rfl⟩ : syracuseStep 4855133 = 1820675) (by norm_num)
theorem B3236755 : Blo 2271435 3236755 := bstep (se 1 (by rfl) ⟨2427566, by rfl⟩ : syracuseStep 3236755 = 4855133) B4855133
theorem B4315673 : Blo 2271435 4315673 := bstep (se 2 (by rfl) ⟨1618377, by rfl⟩ : syracuseStep 4315673 = 3236755) B3236755
theorem B2877115 : Blo 2271435 2877115 := bstep (se 1 (by rfl) ⟨2157836, by rfl⟩ : syracuseStep 2877115 = 4315673) B4315673
theorem B3836153 : Blo 2271435 3836153 := bstep (se 2 (by rfl) ⟨1438557, by rfl⟩ : syracuseStep 3836153 = 2877115) B2877115
theorem B2557435 : Blo 2271435 2557435 := bstep (se 1 (by rfl) ⟨1918076, by rfl⟩ : syracuseStep 2557435 = 3836153) B3836153
theorem B3409913 : Blo 2271435 3409913 := bstep (se 2 (by rfl) ⟨1278717, by rfl⟩ : syracuseStep 3409913 = 2557435) B2557435
theorem B2273275 : Blo 2271435 2273275 := bstep (se 1 (by rfl) ⟨1704956, by rfl⟩ : syracuseStep 2273275 = 3409913) B3409913
theorem B5612093 : Blo 2271435 5612093 := bbase (se 3 (by rfl) ⟨1052267, by rfl⟩ : syracuseStep 5612093 = 2104535) (by norm_num)
theorem B3741395 : Blo 2271435 3741395 := bstep (se 1 (by rfl) ⟨2806046, by rfl⟩ : syracuseStep 3741395 = 5612093) B5612093
theorem B9977053 : Blo 2271435 9977053 := bstep (se 3 (by rfl) ⟨1870697, by rfl⟩ : syracuseStep 9977053 = 3741395) B3741395
theorem B13302737 : Blo 2271435 13302737 := bstep (se 2 (by rfl) ⟨4988526, by rfl⟩ : syracuseStep 13302737 = 9977053) B9977053
theorem B8868491 : Blo 2271435 8868491 := bstep (se 1 (by rfl) ⟨6651368, by rfl⟩ : syracuseStep 8868491 = 13302737) B13302737
theorem B5912327 : Blo 2271435 5912327 := bstep (se 1 (by rfl) ⟨4434245, by rfl⟩ : syracuseStep 5912327 = 8868491) B8868491
theorem B3941551 : Blo 2271435 3941551 := bstep (se 1 (by rfl) ⟨2956163, by rfl⟩ : syracuseStep 3941551 = 5912327) B5912327
theorem B5255401 : Blo 2271435 5255401 := bstep (se 2 (by rfl) ⟨1970775, by rfl⟩ : syracuseStep 5255401 = 3941551) B3941551
theorem B7007201 : Blo 2271435 7007201 := bstep (se 2 (by rfl) ⟨2627700, by rfl⟩ : syracuseStep 7007201 = 5255401) B5255401
theorem B4671467 : Blo 2271435 4671467 := bstep (se 1 (by rfl) ⟨3503600, by rfl⟩ : syracuseStep 4671467 = 7007201) B7007201
theorem B3114311 : Blo 2271435 3114311 := bstep (se 1 (by rfl) ⟨2335733, by rfl⟩ : syracuseStep 3114311 = 4671467) B4671467
theorem B8304829 : Blo 2271435 8304829 := bstep (se 3 (by rfl) ⟨1557155, by rfl⟩ : syracuseStep 8304829 = 3114311) B3114311
theorem B44292421 : Blo 2271435 44292421 := bstep (se 4 (by rfl) ⟨4152414, by rfl⟩ : syracuseStep 44292421 = 8304829) B8304829
theorem B59056561 : Blo 2271435 59056561 := bstep (se 2 (by rfl) ⟨22146210, by rfl⟩ : syracuseStep 59056561 = 44292421) B44292421
theorem B78742081 : Blo 2271435 78742081 := bstep (se 2 (by rfl) ⟨29528280, by rfl⟩ : syracuseStep 78742081 = 59056561) B59056561
theorem B104989441 : Blo 2271435 104989441 := bstep (se 2 (by rfl) ⟨39371040, by rfl⟩ : syracuseStep 104989441 = 78742081) B78742081
theorem B139985921 : Blo 2271435 139985921 := bstep (se 2 (by rfl) ⟨52494720, by rfl⟩ : syracuseStep 139985921 = 104989441) B104989441
theorem B93323947 : Blo 2271435 93323947 := bstep (se 1 (by rfl) ⟨69992960, by rfl⟩ : syracuseStep 93323947 = 139985921) B139985921
theorem B124431929 : Blo 2271435 124431929 := bstep (se 2 (by rfl) ⟨46661973, by rfl⟩ : syracuseStep 124431929 = 93323947) B93323947
theorem B82954619 : Blo 2271435 82954619 := bstep (se 1 (by rfl) ⟨62215964, by rfl⟩ : syracuseStep 82954619 = 124431929) B124431929
theorem B55303079 : Blo 2271435 55303079 := bstep (se 1 (by rfl) ⟨41477309, by rfl⟩ : syracuseStep 55303079 = 82954619) B82954619
theorem B147474877 : Blo 2271435 147474877 := bstep (se 3 (by rfl) ⟨27651539, by rfl⟩ : syracuseStep 147474877 = 55303079) B55303079
theorem B196633169 : Blo 2271435 196633169 := bstep (se 2 (by rfl) ⟨73737438, by rfl⟩ : syracuseStep 196633169 = 147474877) B147474877
theorem B131088779 : Blo 2271435 131088779 := bstep (se 1 (by rfl) ⟨98316584, by rfl⟩ : syracuseStep 131088779 = 196633169) B196633169
theorem B87392519 : Blo 2271435 87392519 := bstep (se 1 (by rfl) ⟨65544389, by rfl⟩ : syracuseStep 87392519 = 131088779) B131088779
theorem B58261679 : Blo 2271435 58261679 := bstep (se 1 (by rfl) ⟨43696259, by rfl⟩ : syracuseStep 58261679 = 87392519) B87392519
theorem B38841119 : Blo 2271435 38841119 := bstep (se 1 (by rfl) ⟨29130839, by rfl⟩ : syracuseStep 38841119 = 58261679) B58261679
theorem B25894079 : Blo 2271435 25894079 := bstep (se 1 (by rfl) ⟨19420559, by rfl⟩ : syracuseStep 25894079 = 38841119) B38841119
theorem B17262719 : Blo 2271435 17262719 := bstep (se 1 (by rfl) ⟨12947039, by rfl⟩ : syracuseStep 17262719 = 25894079) B25894079
theorem B11508479 : Blo 2271435 11508479 := bstep (se 1 (by rfl) ⟨8631359, by rfl⟩ : syracuseStep 11508479 = 17262719) B17262719
theorem B7672319 : Blo 2271435 7672319 := bstep (se 1 (by rfl) ⟨5754239, by rfl⟩ : syracuseStep 7672319 = 11508479) B11508479
theorem B5114879 : Blo 2271435 5114879 := bstep (se 1 (by rfl) ⟨3836159, by rfl⟩ : syracuseStep 5114879 = 7672319) B7672319
theorem B3409919 : Blo 2271435 3409919 := bstep (se 1 (by rfl) ⟨2557439, by rfl⟩ : syracuseStep 3409919 = 5114879) B5114879
theorem B2273279 : Blo 2271435 2273279 := bstep (se 1 (by rfl) ⟨1704959, by rfl⟩ : syracuseStep 2273279 = 3409919) B3409919
theorem B3409925 : Blo 2271435 3409925 := bbase (se 4 (by rfl) ⟨319680, by rfl⟩ : syracuseStep 3409925 = 639361) (by norm_num)
theorem B2273283 : Blo 2271435 2273283 := bstep (se 1 (by rfl) ⟨1704962, by rfl⟩ : syracuseStep 2273283 = 3409925) B3409925
theorem B3836173 : Blo 2271435 3836173 := bbase (se 3 (by rfl) ⟨719282, by rfl⟩ : syracuseStep 3836173 = 1438565) (by norm_num)
theorem B5114897 : Blo 2271435 5114897 := bstep (se 2 (by rfl) ⟨1918086, by rfl⟩ : syracuseStep 5114897 = 3836173) B3836173
theorem B3409931 : Blo 2271435 3409931 := bstep (se 1 (by rfl) ⟨2557448, by rfl⟩ : syracuseStep 3409931 = 5114897) B5114897
theorem B2273287 : Blo 2271435 2273287 := bstep (se 1 (by rfl) ⟨1704965, by rfl⟩ : syracuseStep 2273287 = 3409931) B3409931
theorem B2557453 : Blo 2271435 2557453 := bbase (se 3 (by rfl) ⟨479522, by rfl⟩ : syracuseStep 2557453 = 959045) (by norm_num)
theorem B3409937 : Blo 2271435 3409937 := bstep (se 2 (by rfl) ⟨1278726, by rfl⟩ : syracuseStep 3409937 = 2557453) B2557453
theorem B2273291 : Blo 2271435 2273291 := bstep (se 1 (by rfl) ⟨1704968, by rfl⟩ : syracuseStep 2273291 = 3409937) B3409937
theorem B7672373 : Blo 2271435 7672373 := bbase (se 5 (by rfl) ⟨359642, by rfl⟩ : syracuseStep 7672373 = 719285) (by norm_num)
theorem B5114915 : Blo 2271435 5114915 := bstep (se 1 (by rfl) ⟨3836186, by rfl⟩ : syracuseStep 5114915 = 7672373) B7672373
theorem B3409943 : Blo 2271435 3409943 := bstep (se 1 (by rfl) ⟨2557457, by rfl⟩ : syracuseStep 3409943 = 5114915) B5114915
theorem B2273295 : Blo 2271435 2273295 := bstep (se 1 (by rfl) ⟨1704971, by rfl⟩ : syracuseStep 2273295 = 3409943) B3409943
theorem B3409949 : Blo 2271435 3409949 := bbase (se 3 (by rfl) ⟨639365, by rfl⟩ : syracuseStep 3409949 = 1278731) (by norm_num)
theorem B2273299 : Blo 2271435 2273299 := bstep (se 1 (by rfl) ⟨1704974, by rfl⟩ : syracuseStep 2273299 = 3409949) B3409949
theorem B5114933 : Blo 2271435 5114933 := bbase (se 5 (by rfl) ⟨239762, by rfl⟩ : syracuseStep 5114933 = 479525) (by norm_num)
theorem B3409955 : Blo 2271435 3409955 := bstep (se 1 (by rfl) ⟨2557466, by rfl⟩ : syracuseStep 3409955 = 5114933) B5114933
theorem B2273303 : Blo 2271435 2273303 := bstep (se 1 (by rfl) ⟨1704977, by rfl⟩ : syracuseStep 2273303 = 3409955) B3409955
theorem B5462101 : Blo 2271435 5462101 := bbase (se 8 (by rfl) ⟨32004, by rfl⟩ : syracuseStep 5462101 = 64009) (by norm_num)
theorem B7282801 : Blo 2271435 7282801 := bstep (se 2 (by rfl) ⟨2731050, by rfl⟩ : syracuseStep 7282801 = 5462101) B5462101
theorem B9710401 : Blo 2271435 9710401 := bstep (se 2 (by rfl) ⟨3641400, by rfl⟩ : syracuseStep 9710401 = 7282801) B7282801
theorem B12947201 : Blo 2271435 12947201 := bstep (se 2 (by rfl) ⟨4855200, by rfl⟩ : syracuseStep 12947201 = 9710401) B9710401
theorem B8631467 : Blo 2271435 8631467 := bstep (se 1 (by rfl) ⟨6473600, by rfl⟩ : syracuseStep 8631467 = 12947201) B12947201
theorem B5754311 : Blo 2271435 5754311 := bstep (se 1 (by rfl) ⟨4315733, by rfl⟩ : syracuseStep 5754311 = 8631467) B8631467
theorem B3836207 : Blo 2271435 3836207 := bstep (se 1 (by rfl) ⟨2877155, by rfl⟩ : syracuseStep 3836207 = 5754311) B5754311
theorem B2557471 : Blo 2271435 2557471 := bstep (se 1 (by rfl) ⟨1918103, by rfl⟩ : syracuseStep 2557471 = 3836207) B3836207
theorem B3409961 : Blo 2271435 3409961 := bstep (se 2 (by rfl) ⟨1278735, by rfl⟩ : syracuseStep 3409961 = 2557471) B2557471
theorem B2273307 : Blo 2271435 2273307 := bstep (se 1 (by rfl) ⟨1704980, by rfl⟩ : syracuseStep 2273307 = 3409961) B3409961
theorem B7777109 : Blo 2271435 7777109 := bbase (se 9 (by rfl) ⟨22784, by rfl⟩ : syracuseStep 7777109 = 45569) (by norm_num)
theorem B5184739 : Blo 2271435 5184739 := bstep (se 1 (by rfl) ⟨3888554, by rfl⟩ : syracuseStep 5184739 = 7777109) B7777109
theorem B6912985 : Blo 2271435 6912985 := bstep (se 2 (by rfl) ⟨2592369, by rfl⟩ : syracuseStep 6912985 = 5184739) B5184739
theorem B9217313 : Blo 2271435 9217313 := bstep (se 2 (by rfl) ⟨3456492, by rfl⟩ : syracuseStep 9217313 = 6912985) B6912985
theorem B6144875 : Blo 2271435 6144875 := bstep (se 1 (by rfl) ⟨4608656, by rfl⟩ : syracuseStep 6144875 = 9217313) B9217313
theorem B4096583 : Blo 2271435 4096583 := bstep (se 1 (by rfl) ⟨3072437, by rfl⟩ : syracuseStep 4096583 = 6144875) B6144875
theorem B2731055 : Blo 2271435 2731055 := bstep (se 1 (by rfl) ⟨2048291, by rfl⟩ : syracuseStep 2731055 = 4096583) B4096583
theorem B7282813 : Blo 2271435 7282813 := bstep (se 3 (by rfl) ⟨1365527, by rfl⟩ : syracuseStep 7282813 = 2731055) B2731055
theorem B9710417 : Blo 2271435 9710417 := bstep (se 2 (by rfl) ⟨3641406, by rfl⟩ : syracuseStep 9710417 = 7282813) B7282813
theorem B6473611 : Blo 2271435 6473611 := bstep (se 1 (by rfl) ⟨4855208, by rfl⟩ : syracuseStep 6473611 = 9710417) B9710417
theorem B8631481 : Blo 2271435 8631481 := bstep (se 2 (by rfl) ⟨3236805, by rfl⟩ : syracuseStep 8631481 = 6473611) B6473611
theorem B11508641 : Blo 2271435 11508641 := bstep (se 2 (by rfl) ⟨4315740, by rfl⟩ : syracuseStep 11508641 = 8631481) B8631481
theorem B7672427 : Blo 2271435 7672427 := bstep (se 1 (by rfl) ⟨5754320, by rfl⟩ : syracuseStep 7672427 = 11508641) B11508641
theorem B5114951 : Blo 2271435 5114951 := bstep (se 1 (by rfl) ⟨3836213, by rfl⟩ : syracuseStep 5114951 = 7672427) B7672427
theorem B3409967 : Blo 2271435 3409967 := bstep (se 1 (by rfl) ⟨2557475, by rfl⟩ : syracuseStep 3409967 = 5114951) B5114951
theorem B2273311 : Blo 2271435 2273311 := bstep (se 1 (by rfl) ⟨1704983, by rfl⟩ : syracuseStep 2273311 = 3409967) B3409967
theorem B3409973 : Blo 2271435 3409973 := bbase (se 5 (by rfl) ⟨159842, by rfl⟩ : syracuseStep 3409973 = 319685) (by norm_num)
theorem B2273315 : Blo 2271435 2273315 := bstep (se 1 (by rfl) ⟨1704986, by rfl⟩ : syracuseStep 2273315 = 3409973) B3409973
theorem B5754341 : Blo 2271435 5754341 := bbase (se 4 (by rfl) ⟨539469, by rfl⟩ : syracuseStep 5754341 = 1078939) (by norm_num)
theorem B3836227 : Blo 2271435 3836227 := bstep (se 1 (by rfl) ⟨2877170, by rfl⟩ : syracuseStep 3836227 = 5754341) B5754341
theorem B5114969 : Blo 2271435 5114969 := bstep (se 2 (by rfl) ⟨1918113, by rfl⟩ : syracuseStep 5114969 = 3836227) B3836227
theorem B3409979 : Blo 2271435 3409979 := bstep (se 1 (by rfl) ⟨2557484, by rfl⟩ : syracuseStep 3409979 = 5114969) B5114969
theorem B2273319 : Blo 2271435 2273319 := bstep (se 1 (by rfl) ⟨1704989, by rfl⟩ : syracuseStep 2273319 = 3409979) B3409979
theorem B2557489 : Blo 2271435 2557489 := bbase (se 2 (by rfl) ⟨959058, by rfl⟩ : syracuseStep 2557489 = 1918117) (by norm_num)
theorem B3409985 : Blo 2271435 3409985 := bstep (se 2 (by rfl) ⟨1278744, by rfl⟩ : syracuseStep 3409985 = 2557489) B2557489
theorem B2273323 : Blo 2271435 2273323 := bstep (se 1 (by rfl) ⟨1704992, by rfl⟩ : syracuseStep 2273323 = 3409985) B3409985
theorem B5462149 : Blo 2271435 5462149 := bbase (se 4 (by rfl) ⟨512076, by rfl⟩ : syracuseStep 5462149 = 1024153) (by norm_num)
theorem B7282865 : Blo 2271435 7282865 := bstep (se 2 (by rfl) ⟨2731074, by rfl⟩ : syracuseStep 7282865 = 5462149) B5462149
theorem B4855243 : Blo 2271435 4855243 := bstep (se 1 (by rfl) ⟨3641432, by rfl⟩ : syracuseStep 4855243 = 7282865) B7282865
theorem B6473657 : Blo 2271435 6473657 := bstep (se 2 (by rfl) ⟨2427621, by rfl⟩ : syracuseStep 6473657 = 4855243) B4855243
theorem B4315771 : Blo 2271435 4315771 := bstep (se 1 (by rfl) ⟨3236828, by rfl⟩ : syracuseStep 4315771 = 6473657) B6473657
theorem B5754361 : Blo 2271435 5754361 := bstep (se 2 (by rfl) ⟨2157885, by rfl⟩ : syracuseStep 5754361 = 4315771) B4315771
theorem B7672481 : Blo 2271435 7672481 := bstep (se 2 (by rfl) ⟨2877180, by rfl⟩ : syracuseStep 7672481 = 5754361) B5754361
theorem B5114987 : Blo 2271435 5114987 := bstep (se 1 (by rfl) ⟨3836240, by rfl⟩ : syracuseStep 5114987 = 7672481) B7672481
theorem B3409991 : Blo 2271435 3409991 := bstep (se 1 (by rfl) ⟨2557493, by rfl⟩ : syracuseStep 3409991 = 5114987) B5114987
theorem B2273327 : Blo 2271435 2273327 := bstep (se 1 (by rfl) ⟨1704995, by rfl⟩ : syracuseStep 2273327 = 3409991) B3409991
theorem B3409997 : Blo 2271435 3409997 := bbase (se 3 (by rfl) ⟨639374, by rfl⟩ : syracuseStep 3409997 = 1278749) (by norm_num)
theorem B2273331 : Blo 2271435 2273331 := bstep (se 1 (by rfl) ⟨1704998, by rfl⟩ : syracuseStep 2273331 = 3409997) B3409997
theorem B5115005 : Blo 2271435 5115005 := bbase (se 3 (by rfl) ⟨959063, by rfl⟩ : syracuseStep 5115005 = 1918127) (by norm_num)
theorem B3410003 : Blo 2271435 3410003 := bstep (se 1 (by rfl) ⟨2557502, by rfl⟩ : syracuseStep 3410003 = 5115005) B5115005
theorem B2273335 : Blo 2271435 2273335 := bstep (se 1 (by rfl) ⟨1705001, by rfl⟩ : syracuseStep 2273335 = 3410003) B3410003
theorem B3836261 : Blo 2271435 3836261 := bbase (se 4 (by rfl) ⟨359649, by rfl⟩ : syracuseStep 3836261 = 719299) (by norm_num)
theorem B2557507 : Blo 2271435 2557507 := bstep (se 1 (by rfl) ⟨1918130, by rfl⟩ : syracuseStep 2557507 = 3836261) B3836261
theorem B3410009 : Blo 2271435 3410009 := bstep (se 2 (by rfl) ⟨1278753, by rfl⟩ : syracuseStep 3410009 = 2557507) B2557507
theorem B2273339 : Blo 2271435 2273339 := bstep (se 1 (by rfl) ⟨1705004, by rfl⟩ : syracuseStep 2273339 = 3410009) B3410009
theorem B4855277 : Blo 2271435 4855277 := bbase (se 3 (by rfl) ⟨910364, by rfl⟩ : syracuseStep 4855277 = 1820729) (by norm_num)
theorem B3236851 : Blo 2271435 3236851 := bstep (se 1 (by rfl) ⟨2427638, by rfl⟩ : syracuseStep 3236851 = 4855277) B4855277
theorem B17263205 : Blo 2271435 17263205 := bstep (se 4 (by rfl) ⟨1618425, by rfl⟩ : syracuseStep 17263205 = 3236851) B3236851
theorem B11508803 : Blo 2271435 11508803 := bstep (se 1 (by rfl) ⟨8631602, by rfl⟩ : syracuseStep 11508803 = 17263205) B17263205
theorem B7672535 : Blo 2271435 7672535 := bstep (se 1 (by rfl) ⟨5754401, by rfl⟩ : syracuseStep 7672535 = 11508803) B11508803
theorem B5115023 : Blo 2271435 5115023 := bstep (se 1 (by rfl) ⟨3836267, by rfl⟩ : syracuseStep 5115023 = 7672535) B7672535
theorem B3410015 : Blo 2271435 3410015 := bstep (se 1 (by rfl) ⟨2557511, by rfl⟩ : syracuseStep 3410015 = 5115023) B5115023
theorem B2273343 : Blo 2271435 2273343 := bstep (se 1 (by rfl) ⟨1705007, by rfl⟩ : syracuseStep 2273343 = 3410015) B3410015
theorem B3410021 : Blo 2271435 3410021 := bbase (se 4 (by rfl) ⟨319689, by rfl⟩ : syracuseStep 3410021 = 639379) (by norm_num)
theorem B2273347 : Blo 2271435 2273347 := bstep (se 1 (by rfl) ⟨1705010, by rfl⟩ : syracuseStep 2273347 = 3410021) B3410021
theorem B4374701 : Blo 2271435 4374701 := bbase (se 3 (by rfl) ⟨820256, by rfl⟩ : syracuseStep 4374701 = 1640513) (by norm_num)
theorem B2916467 : Blo 2271435 2916467 := bstep (se 1 (by rfl) ⟨2187350, by rfl⟩ : syracuseStep 2916467 = 4374701) B4374701
theorem B124435925 : Blo 2271435 124435925 := bstep (se 7 (by rfl) ⟨1458233, by rfl⟩ : syracuseStep 124435925 = 2916467) B2916467
theorem B82957283 : Blo 2271435 82957283 := bstep (se 1 (by rfl) ⟨62217962, by rfl⟩ : syracuseStep 82957283 = 124435925) B124435925
theorem B55304855 : Blo 2271435 55304855 := bstep (se 1 (by rfl) ⟨41478641, by rfl⟩ : syracuseStep 55304855 = 82957283) B82957283
theorem B36869903 : Blo 2271435 36869903 := bstep (se 1 (by rfl) ⟨27652427, by rfl⟩ : syracuseStep 36869903 = 55304855) B55304855
theorem B24579935 : Blo 2271435 24579935 := bstep (se 1 (by rfl) ⟨18434951, by rfl⟩ : syracuseStep 24579935 = 36869903) B36869903
theorem B16386623 : Blo 2271435 16386623 := bstep (se 1 (by rfl) ⟨12289967, by rfl⟩ : syracuseStep 16386623 = 24579935) B24579935
theorem B10924415 : Blo 2271435 10924415 := bstep (se 1 (by rfl) ⟨8193311, by rfl⟩ : syracuseStep 10924415 = 16386623) B16386623
theorem B7282943 : Blo 2271435 7282943 := bstep (se 1 (by rfl) ⟨5462207, by rfl⟩ : syracuseStep 7282943 = 10924415) B10924415
theorem B4855295 : Blo 2271435 4855295 := bstep (se 1 (by rfl) ⟨3641471, by rfl⟩ : syracuseStep 4855295 = 7282943) B7282943
theorem B3236863 : Blo 2271435 3236863 := bstep (se 1 (by rfl) ⟨2427647, by rfl⟩ : syracuseStep 3236863 = 4855295) B4855295
theorem B4315817 : Blo 2271435 4315817 := bstep (se 2 (by rfl) ⟨1618431, by rfl⟩ : syracuseStep 4315817 = 3236863) B3236863
theorem B2877211 : Blo 2271435 2877211 := bstep (se 1 (by rfl) ⟨2157908, by rfl⟩ : syracuseStep 2877211 = 4315817) B4315817
theorem B3836281 : Blo 2271435 3836281 := bstep (se 2 (by rfl) ⟨1438605, by rfl⟩ : syracuseStep 3836281 = 2877211) B2877211
theorem B5115041 : Blo 2271435 5115041 := bstep (se 2 (by rfl) ⟨1918140, by rfl⟩ : syracuseStep 5115041 = 3836281) B3836281
theorem B3410027 : Blo 2271435 3410027 := bstep (se 1 (by rfl) ⟨2557520, by rfl⟩ : syracuseStep 3410027 = 5115041) B5115041
theorem B2273351 : Blo 2271435 2273351 := bstep (se 1 (by rfl) ⟨1705013, by rfl⟩ : syracuseStep 2273351 = 3410027) B3410027
theorem B2557525 : Blo 2271435 2557525 := bbase (se 8 (by rfl) ⟨14985, by rfl⟩ : syracuseStep 2557525 = 29971) (by norm_num)
theorem B3410033 : Blo 2271435 3410033 := bstep (se 2 (by rfl) ⟨1278762, by rfl⟩ : syracuseStep 3410033 = 2557525) B2557525
theorem B2273355 : Blo 2271435 2273355 := bstep (se 1 (by rfl) ⟨1705016, by rfl⟩ : syracuseStep 2273355 = 3410033) B3410033
theorem B2877221 : Blo 2271435 2877221 := bbase (se 4 (by rfl) ⟨269739, by rfl⟩ : syracuseStep 2877221 = 539479) (by norm_num)
theorem B7672589 : Blo 2271435 7672589 := bstep (se 3 (by rfl) ⟨1438610, by rfl⟩ : syracuseStep 7672589 = 2877221) B2877221
theorem B5115059 : Blo 2271435 5115059 := bstep (se 1 (by rfl) ⟨3836294, by rfl⟩ : syracuseStep 5115059 = 7672589) B7672589
theorem B3410039 : Blo 2271435 3410039 := bstep (se 1 (by rfl) ⟨2557529, by rfl⟩ : syracuseStep 3410039 = 5115059) B5115059
theorem B2273359 : Blo 2271435 2273359 := bstep (se 1 (by rfl) ⟨1705019, by rfl⟩ : syracuseStep 2273359 = 3410039) B3410039
theorem B3410045 : Blo 2271435 3410045 := bbase (se 3 (by rfl) ⟨639383, by rfl⟩ : syracuseStep 3410045 = 1278767) (by norm_num)
theorem B2273363 : Blo 2271435 2273363 := bstep (se 1 (by rfl) ⟨1705022, by rfl⟩ : syracuseStep 2273363 = 3410045) B3410045
theorem B5115077 : Blo 2271435 5115077 := bbase (se 4 (by rfl) ⟨479538, by rfl⟩ : syracuseStep 5115077 = 959077) (by norm_num)
theorem B3410051 : Blo 2271435 3410051 := bstep (se 1 (by rfl) ⟨2557538, by rfl⟩ : syracuseStep 3410051 = 5115077) B5115077
theorem B2273367 : Blo 2271435 2273367 := bstep (se 1 (by rfl) ⟨1705025, by rfl⟩ : syracuseStep 2273367 = 3410051) B3410051
theorem B2335829 : Blo 2271435 2335829 := bbase (se 8 (by rfl) ⟨13686, by rfl⟩ : syracuseStep 2335829 = 27373) (by norm_num)
theorem B24915509 : Blo 2271435 24915509 := bstep (se 5 (by rfl) ⟨1167914, by rfl⟩ : syracuseStep 24915509 = 2335829) B2335829
theorem B16610339 : Blo 2271435 16610339 := bstep (se 1 (by rfl) ⟨12457754, by rfl⟩ : syracuseStep 16610339 = 24915509) B24915509
theorem B11073559 : Blo 2271435 11073559 := bstep (se 1 (by rfl) ⟨8305169, by rfl⟩ : syracuseStep 11073559 = 16610339) B16610339
theorem B14764745 : Blo 2271435 14764745 := bstep (se 2 (by rfl) ⟨5536779, by rfl⟩ : syracuseStep 14764745 = 11073559) B11073559
theorem B9843163 : Blo 2271435 9843163 := bstep (se 1 (by rfl) ⟨7382372, by rfl⟩ : syracuseStep 9843163 = 14764745) B14764745
theorem B52496869 : Blo 2271435 52496869 := bstep (se 4 (by rfl) ⟨4921581, by rfl⟩ : syracuseStep 52496869 = 9843163) B9843163
theorem B69995825 : Blo 2271435 69995825 := bstep (se 2 (by rfl) ⟨26248434, by rfl⟩ : syracuseStep 69995825 = 52496869) B52496869
theorem B46663883 : Blo 2271435 46663883 := bstep (se 1 (by rfl) ⟨34997912, by rfl⟩ : syracuseStep 46663883 = 69995825) B69995825
theorem B31109255 : Blo 2271435 31109255 := bstep (se 1 (by rfl) ⟨23331941, by rfl⟩ : syracuseStep 31109255 = 46663883) B46663883
theorem B20739503 : Blo 2271435 20739503 := bstep (se 1 (by rfl) ⟨15554627, by rfl⟩ : syracuseStep 20739503 = 31109255) B31109255
theorem B13826335 : Blo 2271435 13826335 := bstep (se 1 (by rfl) ⟨10369751, by rfl⟩ : syracuseStep 13826335 = 20739503) B20739503
theorem B18435113 : Blo 2271435 18435113 := bstep (se 2 (by rfl) ⟨6913167, by rfl⟩ : syracuseStep 18435113 = 13826335) B13826335
theorem B12290075 : Blo 2271435 12290075 := bstep (se 1 (by rfl) ⟨9217556, by rfl⟩ : syracuseStep 12290075 = 18435113) B18435113
theorem B8193383 : Blo 2271435 8193383 := bstep (se 1 (by rfl) ⟨6145037, by rfl⟩ : syracuseStep 8193383 = 12290075) B12290075
theorem B5462255 : Blo 2271435 5462255 := bstep (se 1 (by rfl) ⟨4096691, by rfl⟩ : syracuseStep 5462255 = 8193383) B8193383
theorem B14566013 : Blo 2271435 14566013 := bstep (se 3 (by rfl) ⟨2731127, by rfl⟩ : syracuseStep 14566013 = 5462255) B5462255
theorem B9710675 : Blo 2271435 9710675 := bstep (se 1 (by rfl) ⟨7283006, by rfl⟩ : syracuseStep 9710675 = 14566013) B14566013
theorem B6473783 : Blo 2271435 6473783 := bstep (se 1 (by rfl) ⟨4855337, by rfl⟩ : syracuseStep 6473783 = 9710675) B9710675
theorem B4315855 : Blo 2271435 4315855 := bstep (se 1 (by rfl) ⟨3236891, by rfl⟩ : syracuseStep 4315855 = 6473783) B6473783
theorem B5754473 : Blo 2271435 5754473 := bstep (se 2 (by rfl) ⟨2157927, by rfl⟩ : syracuseStep 5754473 = 4315855) B4315855
theorem B3836315 : Blo 2271435 3836315 := bstep (se 1 (by rfl) ⟨2877236, by rfl⟩ : syracuseStep 3836315 = 5754473) B5754473
theorem B2557543 : Blo 2271435 2557543 := bstep (se 1 (by rfl) ⟨1918157, by rfl⟩ : syracuseStep 2557543 = 3836315) B3836315
theorem B3410057 : Blo 2271435 3410057 := bstep (se 2 (by rfl) ⟨1278771, by rfl⟩ : syracuseStep 3410057 = 2557543) B2557543
theorem B2273371 : Blo 2271435 2273371 := bstep (se 1 (by rfl) ⟨1705028, by rfl⟩ : syracuseStep 2273371 = 3410057) B3410057
theorem B11508965 : Blo 2271435 11508965 := bbase (se 4 (by rfl) ⟨1078965, by rfl⟩ : syracuseStep 11508965 = 2157931) (by norm_num)
theorem B7672643 : Blo 2271435 7672643 := bstep (se 1 (by rfl) ⟨5754482, by rfl⟩ : syracuseStep 7672643 = 11508965) B11508965
theorem B5115095 : Blo 2271435 5115095 := bstep (se 1 (by rfl) ⟨3836321, by rfl⟩ : syracuseStep 5115095 = 7672643) B7672643
theorem B3410063 : Blo 2271435 3410063 := bstep (se 1 (by rfl) ⟨2557547, by rfl⟩ : syracuseStep 3410063 = 5115095) B5115095
theorem B2273375 : Blo 2271435 2273375 := bstep (se 1 (by rfl) ⟨1705031, by rfl⟩ : syracuseStep 2273375 = 3410063) B3410063
theorem B3410069 : Blo 2271435 3410069 := bbase (se 6 (by rfl) ⟨79923, by rfl⟩ : syracuseStep 3410069 = 159847) (by norm_num)
theorem B2273379 : Blo 2271435 2273379 := bstep (se 1 (by rfl) ⟨1705034, by rfl⟩ : syracuseStep 2273379 = 3410069) B3410069
theorem B9710725 : Blo 2271435 9710725 := bbase (se 4 (by rfl) ⟨910380, by rfl⟩ : syracuseStep 9710725 = 1820761) (by norm_num)
theorem B12947633 : Blo 2271435 12947633 := bstep (se 2 (by rfl) ⟨4855362, by rfl⟩ : syracuseStep 12947633 = 9710725) B9710725
theorem B8631755 : Blo 2271435 8631755 := bstep (se 1 (by rfl) ⟨6473816, by rfl⟩ : syracuseStep 8631755 = 12947633) B12947633
theorem B5754503 : Blo 2271435 5754503 := bstep (se 1 (by rfl) ⟨4315877, by rfl⟩ : syracuseStep 5754503 = 8631755) B8631755
theorem B3836335 : Blo 2271435 3836335 := bstep (se 1 (by rfl) ⟨2877251, by rfl⟩ : syracuseStep 3836335 = 5754503) B5754503
theorem B5115113 : Blo 2271435 5115113 := bstep (se 2 (by rfl) ⟨1918167, by rfl⟩ : syracuseStep 5115113 = 3836335) B3836335
theorem B3410075 : Blo 2271435 3410075 := bstep (se 1 (by rfl) ⟨2557556, by rfl⟩ : syracuseStep 3410075 = 5115113) B5115113
theorem B2273383 : Blo 2271435 2273383 := bstep (se 1 (by rfl) ⟨1705037, by rfl⟩ : syracuseStep 2273383 = 3410075) B3410075
theorem B2557561 : Blo 2271435 2557561 := bbase (se 2 (by rfl) ⟨959085, by rfl⟩ : syracuseStep 2557561 = 1918171) (by norm_num)
theorem B3410081 : Blo 2271435 3410081 := bstep (se 2 (by rfl) ⟨1278780, by rfl⟩ : syracuseStep 3410081 = 2557561) B2557561
theorem B2273387 : Blo 2271435 2273387 := bstep (se 1 (by rfl) ⟨1705040, by rfl⟩ : syracuseStep 2273387 = 3410081) B3410081
theorem B6562165 : Blo 2271435 6562165 := bbase (se 5 (by rfl) ⟨307601, by rfl⟩ : syracuseStep 6562165 = 615203) (by norm_num)
theorem B8749553 : Blo 2271435 8749553 := bstep (se 2 (by rfl) ⟨3281082, by rfl⟩ : syracuseStep 8749553 = 6562165) B6562165
theorem B23332141 : Blo 2271435 23332141 := bstep (se 3 (by rfl) ⟨4374776, by rfl⟩ : syracuseStep 23332141 = 8749553) B8749553
theorem B31109521 : Blo 2271435 31109521 := bstep (se 2 (by rfl) ⟨11666070, by rfl⟩ : syracuseStep 31109521 = 23332141) B23332141
theorem B41479361 : Blo 2271435 41479361 := bstep (se 2 (by rfl) ⟨15554760, by rfl⟩ : syracuseStep 41479361 = 31109521) B31109521
theorem B27652907 : Blo 2271435 27652907 := bstep (se 1 (by rfl) ⟨20739680, by rfl⟩ : syracuseStep 27652907 = 41479361) B41479361
theorem B18435271 : Blo 2271435 18435271 := bstep (se 1 (by rfl) ⟨13826453, by rfl⟩ : syracuseStep 18435271 = 27652907) B27652907
theorem B24580361 : Blo 2271435 24580361 := bstep (se 2 (by rfl) ⟨9217635, by rfl⟩ : syracuseStep 24580361 = 18435271) B18435271
theorem B16386907 : Blo 2271435 16386907 := bstep (se 1 (by rfl) ⟨12290180, by rfl⟩ : syracuseStep 16386907 = 24580361) B24580361
theorem B21849209 : Blo 2271435 21849209 := bstep (se 2 (by rfl) ⟨8193453, by rfl⟩ : syracuseStep 21849209 = 16386907) B16386907
theorem B14566139 : Blo 2271435 14566139 := bstep (se 1 (by rfl) ⟨10924604, by rfl⟩ : syracuseStep 14566139 = 21849209) B21849209
theorem B9710759 : Blo 2271435 9710759 := bstep (se 1 (by rfl) ⟨7283069, by rfl⟩ : syracuseStep 9710759 = 14566139) B14566139
theorem B6473839 : Blo 2271435 6473839 := bstep (se 1 (by rfl) ⟨4855379, by rfl⟩ : syracuseStep 6473839 = 9710759) B9710759
theorem B8631785 : Blo 2271435 8631785 := bstep (se 2 (by rfl) ⟨3236919, by rfl⟩ : syracuseStep 8631785 = 6473839) B6473839
theorem B5754523 : Blo 2271435 5754523 := bstep (se 1 (by rfl) ⟨4315892, by rfl⟩ : syracuseStep 5754523 = 8631785) B8631785
theorem B7672697 : Blo 2271435 7672697 := bstep (se 2 (by rfl) ⟨2877261, by rfl⟩ : syracuseStep 7672697 = 5754523) B5754523
theorem B5115131 : Blo 2271435 5115131 := bstep (se 1 (by rfl) ⟨3836348, by rfl⟩ : syracuseStep 5115131 = 7672697) B7672697
theorem B3410087 : Blo 2271435 3410087 := bstep (se 1 (by rfl) ⟨2557565, by rfl⟩ : syracuseStep 3410087 = 5115131) B5115131
theorem B2273391 : Blo 2271435 2273391 := bstep (se 1 (by rfl) ⟨1705043, by rfl⟩ : syracuseStep 2273391 = 3410087) B3410087
theorem B3410093 : Blo 2271435 3410093 := bbase (se 3 (by rfl) ⟨639392, by rfl⟩ : syracuseStep 3410093 = 1278785) (by norm_num)
theorem B2273395 : Blo 2271435 2273395 := bstep (se 1 (by rfl) ⟨1705046, by rfl⟩ : syracuseStep 2273395 = 3410093) B3410093
theorem B5115149 : Blo 2271435 5115149 := bbase (se 3 (by rfl) ⟨959090, by rfl⟩ : syracuseStep 5115149 = 1918181) (by norm_num)
theorem B3410099 : Blo 2271435 3410099 := bstep (se 1 (by rfl) ⟨2557574, by rfl⟩ : syracuseStep 3410099 = 5115149) B5115149
theorem B2273399 : Blo 2271435 2273399 := bstep (se 1 (by rfl) ⟨1705049, by rfl⟩ : syracuseStep 2273399 = 3410099) B3410099
theorem B2877277 : Blo 2271435 2877277 := bbase (se 3 (by rfl) ⟨539489, by rfl⟩ : syracuseStep 2877277 = 1078979) (by norm_num)
theorem B3836369 : Blo 2271435 3836369 := bstep (se 2 (by rfl) ⟨1438638, by rfl⟩ : syracuseStep 3836369 = 2877277) B2877277
theorem B2557579 : Blo 2271435 2557579 := bstep (se 1 (by rfl) ⟨1918184, by rfl⟩ : syracuseStep 2557579 = 3836369) B3836369
theorem B3410105 : Blo 2271435 3410105 := bstep (se 2 (by rfl) ⟨1278789, by rfl⟩ : syracuseStep 3410105 = 2557579) B2557579
theorem B2273403 : Blo 2271435 2273403 := bstep (se 1 (by rfl) ⟨1705052, by rfl⟩ : syracuseStep 2273403 = 3410105) B3410105
theorem B19421653 : Blo 2271435 19421653 := bbase (se 7 (by rfl) ⟨227597, by rfl⟩ : syracuseStep 19421653 = 455195) (by norm_num)
theorem B25895537 : Blo 2271435 25895537 := bstep (se 2 (by rfl) ⟨9710826, by rfl⟩ : syracuseStep 25895537 = 19421653) B19421653
theorem B17263691 : Blo 2271435 17263691 := bstep (se 1 (by rfl) ⟨12947768, by rfl⟩ : syracuseStep 17263691 = 25895537) B25895537
theorem B11509127 : Blo 2271435 11509127 := bstep (se 1 (by rfl) ⟨8631845, by rfl⟩ : syracuseStep 11509127 = 17263691) B17263691
theorem B7672751 : Blo 2271435 7672751 := bstep (se 1 (by rfl) ⟨5754563, by rfl⟩ : syracuseStep 7672751 = 11509127) B11509127
theorem B5115167 : Blo 2271435 5115167 := bstep (se 1 (by rfl) ⟨3836375, by rfl⟩ : syracuseStep 5115167 = 7672751) B7672751
theorem B3410111 : Blo 2271435 3410111 := bstep (se 1 (by rfl) ⟨2557583, by rfl⟩ : syracuseStep 3410111 = 5115167) B5115167
theorem B2273407 : Blo 2271435 2273407 := bstep (se 1 (by rfl) ⟨1705055, by rfl⟩ : syracuseStep 2273407 = 3410111) B3410111
theorem B3410117 : Blo 2271435 3410117 := bbase (se 4 (by rfl) ⟨319698, by rfl⟩ : syracuseStep 3410117 = 639397) (by norm_num)
theorem B2273411 : Blo 2271435 2273411 := bstep (se 1 (by rfl) ⟨1705058, by rfl⟩ : syracuseStep 2273411 = 3410117) B3410117
theorem B3836389 : Blo 2271435 3836389 := bbase (se 4 (by rfl) ⟨359661, by rfl⟩ : syracuseStep 3836389 = 719323) (by norm_num)
theorem B5115185 : Blo 2271435 5115185 := bstep (se 2 (by rfl) ⟨1918194, by rfl⟩ : syracuseStep 5115185 = 3836389) B3836389
theorem B3410123 : Blo 2271435 3410123 := bstep (se 1 (by rfl) ⟨2557592, by rfl⟩ : syracuseStep 3410123 = 5115185) B5115185
theorem B2273415 : Blo 2271435 2273415 := bstep (se 1 (by rfl) ⟨1705061, by rfl⟩ : syracuseStep 2273415 = 3410123) B3410123
theorem B2557597 : Blo 2271435 2557597 := bbase (se 3 (by rfl) ⟨479549, by rfl⟩ : syracuseStep 2557597 = 959099) (by norm_num)
theorem B3410129 : Blo 2271435 3410129 := bstep (se 2 (by rfl) ⟨1278798, by rfl⟩ : syracuseStep 3410129 = 2557597) B2557597
theorem B2273419 : Blo 2271435 2273419 := bstep (se 1 (by rfl) ⟨1705064, by rfl⟩ : syracuseStep 2273419 = 3410129) B3410129
theorem B7672805 : Blo 2271435 7672805 := bbase (se 4 (by rfl) ⟨719325, by rfl⟩ : syracuseStep 7672805 = 1438651) (by norm_num)
theorem B5115203 : Blo 2271435 5115203 := bstep (se 1 (by rfl) ⟨3836402, by rfl⟩ : syracuseStep 5115203 = 7672805) B7672805
theorem B3410135 : Blo 2271435 3410135 := bstep (se 1 (by rfl) ⟨2557601, by rfl⟩ : syracuseStep 3410135 = 5115203) B5115203
theorem B2273423 : Blo 2271435 2273423 := bstep (se 1 (by rfl) ⟨1705067, by rfl⟩ : syracuseStep 2273423 = 3410135) B3410135
theorem B3410141 : Blo 2271435 3410141 := bbase (se 3 (by rfl) ⟨639401, by rfl⟩ : syracuseStep 3410141 = 1278803) (by norm_num)
theorem B2273427 : Blo 2271435 2273427 := bstep (se 1 (by rfl) ⟨1705070, by rfl⟩ : syracuseStep 2273427 = 3410141) B3410141
theorem B5115221 : Blo 2271435 5115221 := bbase (se 11 (by rfl) ⟨3746, by rfl⟩ : syracuseStep 5115221 = 7493) (by norm_num)
theorem B3410147 : Blo 2271435 3410147 := bstep (se 1 (by rfl) ⟨2557610, by rfl⟩ : syracuseStep 3410147 = 5115221) B5115221
theorem B2273431 : Blo 2271435 2273431 := bstep (se 1 (by rfl) ⟨1705073, by rfl⟩ : syracuseStep 2273431 = 3410147) B3410147
theorem B2427737 : Blo 2271435 2427737 := bbase (se 2 (by rfl) ⟨910401, by rfl⟩ : syracuseStep 2427737 = 1820803) (by norm_num)
theorem B6473965 : Blo 2271435 6473965 := bstep (se 3 (by rfl) ⟨1213868, by rfl⟩ : syracuseStep 6473965 = 2427737) B2427737
theorem B8631953 : Blo 2271435 8631953 := bstep (se 2 (by rfl) ⟨3236982, by rfl⟩ : syracuseStep 8631953 = 6473965) B6473965
theorem B5754635 : Blo 2271435 5754635 := bstep (se 1 (by rfl) ⟨4315976, by rfl⟩ : syracuseStep 5754635 = 8631953) B8631953
theorem B3836423 : Blo 2271435 3836423 := bstep (se 1 (by rfl) ⟨2877317, by rfl⟩ : syracuseStep 3836423 = 5754635) B5754635
theorem B2557615 : Blo 2271435 2557615 := bstep (se 1 (by rfl) ⟨1918211, by rfl⟩ : syracuseStep 2557615 = 3836423) B3836423
theorem B3410153 : Blo 2271435 3410153 := bstep (se 2 (by rfl) ⟨1278807, by rfl⟩ : syracuseStep 3410153 = 2557615) B2557615
theorem B2273435 : Blo 2271435 2273435 := bstep (se 1 (by rfl) ⟨1705076, by rfl⟩ : syracuseStep 2273435 = 3410153) B3410153
theorem C0 (j : ℕ) (h1 : 567858 ≤ j) (h2 : j ≤ 568358) : Blo 2271435 (4 * j + 3) := by
  interval_cases j
  · exact B2271435
  · exact B2271439
  · exact B2271443
  · exact B2271447
  · exact B2271451
  · exact B2271455
  · exact B2271459
  · exact B2271463
  · exact B2271467
  · exact B2271471
  · exact B2271475
  · exact B2271479
  · exact B2271483
  · exact B2271487
  · exact B2271491
  · exact B2271495
  · exact B2271499
  · exact B2271503
  · exact B2271507
  · exact B2271511
  · exact B2271515
  · exact B2271519
  · exact B2271523
  · exact B2271527
  · exact B2271531
  · exact B2271535
  · exact B2271539
  · exact B2271543
  · exact B2271547
  · exact B2271551
  · exact B2271555
  · exact B2271559
  · exact B2271563
  · exact B2271567
  · exact B2271571
  · exact B2271575
  · exact B2271579
  · exact B2271583
  · exact B2271587
  · exact B2271591
  · exact B2271595
  · exact B2271599
  · exact B2271603
  · exact B2271607
  · exact B2271611
  · exact B2271615
  · exact B2271619
  · exact B2271623
  · exact B2271627
  · exact B2271631
  · exact B2271635
  · exact B2271639
  · exact B2271643
  · exact B2271647
  · exact B2271651
  · exact B2271655
  · exact B2271659
  · exact B2271663
  · exact B2271667
  · exact B2271671
  · exact B2271675
  · exact B2271679
  · exact B2271683
  · exact B2271687
  · exact B2271691
  · exact B2271695
  · exact B2271699
  · exact B2271703
  · exact B2271707
  · exact B2271711
  · exact B2271715
  · exact B2271719
  · exact B2271723
  · exact B2271727
  · exact B2271731
  · exact B2271735
  · exact B2271739
  · exact B2271743
  · exact B2271747
  · exact B2271751
  · exact B2271755
  · exact B2271759
  · exact B2271763
  · exact B2271767
  · exact B2271771
  · exact B2271775
  · exact B2271779
  · exact B2271783
  · exact B2271787
  · exact B2271791
  · exact B2271795
  · exact B2271799
  · exact B2271803
  · exact B2271807
  · exact B2271811
  · exact B2271815
  · exact B2271819
  · exact B2271823
  · exact B2271827
  · exact B2271831
  · exact B2271835
  · exact B2271839
  · exact B2271843
  · exact B2271847
  · exact B2271851
  · exact B2271855
  · exact B2271859
  · exact B2271863
  · exact B2271867
  · exact B2271871
  · exact B2271875
  · exact B2271879
  · exact B2271883
  · exact B2271887
  · exact B2271891
  · exact B2271895
  · exact B2271899
  · exact B2271903
  · exact B2271907
  · exact B2271911
  · exact B2271915
  · exact B2271919
  · exact B2271923
  · exact B2271927
  · exact B2271931
  · exact B2271935
  · exact B2271939
  · exact B2271943
  · exact B2271947
  · exact B2271951
  · exact B2271955
  · exact B2271959
  · exact B2271963
  · exact B2271967
  · exact B2271971
  · exact B2271975
  · exact B2271979
  · exact B2271983
  · exact B2271987
  · exact B2271991
  · exact B2271995
  · exact B2271999
  · exact B2272003
  · exact B2272007
  · exact B2272011
  · exact B2272015
  · exact B2272019
  · exact B2272023
  · exact B2272027
  · exact B2272031
  · exact B2272035
  · exact B2272039
  · exact B2272043
  · exact B2272047
  · exact B2272051
  · exact B2272055
  · exact B2272059
  · exact B2272063
  · exact B2272067
  · exact B2272071
  · exact B2272075
  · exact B2272079
  · exact B2272083
  · exact B2272087
  · exact B2272091
  · exact B2272095
  · exact B2272099
  · exact B2272103
  · exact B2272107
  · exact B2272111
  · exact B2272115
  · exact B2272119
  · exact B2272123
  · exact B2272127
  · exact B2272131
  · exact B2272135
  · exact B2272139
  · exact B2272143
  · exact B2272147
  · exact B2272151
  · exact B2272155
  · exact B2272159
  · exact B2272163
  · exact B2272167
  · exact B2272171
  · exact B2272175
  · exact B2272179
  · exact B2272183
  · exact B2272187
  · exact B2272191
  · exact B2272195
  · exact B2272199
  · exact B2272203
  · exact B2272207
  · exact B2272211
  · exact B2272215
  · exact B2272219
  · exact B2272223
  · exact B2272227
  · exact B2272231
  · exact B2272235
  · exact B2272239
  · exact B2272243
  · exact B2272247
  · exact B2272251
  · exact B2272255
  · exact B2272259
  · exact B2272263
  · exact B2272267
  · exact B2272271
  · exact B2272275
  · exact B2272279
  · exact B2272283
  · exact B2272287
  · exact B2272291
  · exact B2272295
  · exact B2272299
  · exact B2272303
  · exact B2272307
  · exact B2272311
  · exact B2272315
  · exact B2272319
  · exact B2272323
  · exact B2272327
  · exact B2272331
  · exact B2272335
  · exact B2272339
  · exact B2272343
  · exact B2272347
  · exact B2272351
  · exact B2272355
  · exact B2272359
  · exact B2272363
  · exact B2272367
  · exact B2272371
  · exact B2272375
  · exact B2272379
  · exact B2272383
  · exact B2272387
  · exact B2272391
  · exact B2272395
  · exact B2272399
  · exact B2272403
  · exact B2272407
  · exact B2272411
  · exact B2272415
  · exact B2272419
  · exact B2272423
  · exact B2272427
  · exact B2272431
  · exact B2272435
  · exact B2272439
  · exact B2272443
  · exact B2272447
  · exact B2272451
  · exact B2272455
  · exact B2272459
  · exact B2272463
  · exact B2272467
  · exact B2272471
  · exact B2272475
  · exact B2272479
  · exact B2272483
  · exact B2272487
  · exact B2272491
  · exact B2272495
  · exact B2272499
  · exact B2272503
  · exact B2272507
  · exact B2272511
  · exact B2272515
  · exact B2272519
  · exact B2272523
  · exact B2272527
  · exact B2272531
  · exact B2272535
  · exact B2272539
  · exact B2272543
  · exact B2272547
  · exact B2272551
  · exact B2272555
  · exact B2272559
  · exact B2272563
  · exact B2272567
  · exact B2272571
  · exact B2272575
  · exact B2272579
  · exact B2272583
  · exact B2272587
  · exact B2272591
  · exact B2272595
  · exact B2272599
  · exact B2272603
  · exact B2272607
  · exact B2272611
  · exact B2272615
  · exact B2272619
  · exact B2272623
  · exact B2272627
  · exact B2272631
  · exact B2272635
  · exact B2272639
  · exact B2272643
  · exact B2272647
  · exact B2272651
  · exact B2272655
  · exact B2272659
  · exact B2272663
  · exact B2272667
  · exact B2272671
  · exact B2272675
  · exact B2272679
  · exact B2272683
  · exact B2272687
  · exact B2272691
  · exact B2272695
  · exact B2272699
  · exact B2272703
  · exact B2272707
  · exact B2272711
  · exact B2272715
  · exact B2272719
  · exact B2272723
  · exact B2272727
  · exact B2272731
  · exact B2272735
  · exact B2272739
  · exact B2272743
  · exact B2272747
  · exact B2272751
  · exact B2272755
  · exact B2272759
  · exact B2272763
  · exact B2272767
  · exact B2272771
  · exact B2272775
  · exact B2272779
  · exact B2272783
  · exact B2272787
  · exact B2272791
  · exact B2272795
  · exact B2272799
  · exact B2272803
  · exact B2272807
  · exact B2272811
  · exact B2272815
  · exact B2272819
  · exact B2272823
  · exact B2272827
  · exact B2272831
  · exact B2272835
  · exact B2272839
  · exact B2272843
  · exact B2272847
  · exact B2272851
  · exact B2272855
  · exact B2272859
  · exact B2272863
  · exact B2272867
  · exact B2272871
  · exact B2272875
  · exact B2272879
  · exact B2272883
  · exact B2272887
  · exact B2272891
  · exact B2272895
  · exact B2272899
  · exact B2272903
  · exact B2272907
  · exact B2272911
  · exact B2272915
  · exact B2272919
  · exact B2272923
  · exact B2272927
  · exact B2272931
  · exact B2272935
  · exact B2272939
  · exact B2272943
  · exact B2272947
  · exact B2272951
  · exact B2272955
  · exact B2272959
  · exact B2272963
  · exact B2272967
  · exact B2272971
  · exact B2272975
  · exact B2272979
  · exact B2272983
  · exact B2272987
  · exact B2272991
  · exact B2272995
  · exact B2272999
  · exact B2273003
  · exact B2273007
  · exact B2273011
  · exact B2273015
  · exact B2273019
  · exact B2273023
  · exact B2273027
  · exact B2273031
  · exact B2273035
  · exact B2273039
  · exact B2273043
  · exact B2273047
  · exact B2273051
  · exact B2273055
  · exact B2273059
  · exact B2273063
  · exact B2273067
  · exact B2273071
  · exact B2273075
  · exact B2273079
  · exact B2273083
  · exact B2273087
  · exact B2273091
  · exact B2273095
  · exact B2273099
  · exact B2273103
  · exact B2273107
  · exact B2273111
  · exact B2273115
  · exact B2273119
  · exact B2273123
  · exact B2273127
  · exact B2273131
  · exact B2273135
  · exact B2273139
  · exact B2273143
  · exact B2273147
  · exact B2273151
  · exact B2273155
  · exact B2273159
  · exact B2273163
  · exact B2273167
  · exact B2273171
  · exact B2273175
  · exact B2273179
  · exact B2273183
  · exact B2273187
  · exact B2273191
  · exact B2273195
  · exact B2273199
  · exact B2273203
  · exact B2273207
  · exact B2273211
  · exact B2273215
  · exact B2273219
  · exact B2273223
  · exact B2273227
  · exact B2273231
  · exact B2273235
  · exact B2273239
  · exact B2273243
  · exact B2273247
  · exact B2273251
  · exact B2273255
  · exact B2273259
  · exact B2273263
  · exact B2273267
  · exact B2273271
  · exact B2273275
  · exact B2273279
  · exact B2273283
  · exact B2273287
  · exact B2273291
  · exact B2273295
  · exact B2273299
  · exact B2273303
  · exact B2273307
  · exact B2273311
  · exact B2273315
  · exact B2273319
  · exact B2273323
  · exact B2273327
  · exact B2273331
  · exact B2273335
  · exact B2273339
  · exact B2273343
  · exact B2273347
  · exact B2273351
  · exact B2273355
  · exact B2273359
  · exact B2273363
  · exact B2273367
  · exact B2273371
  · exact B2273375
  · exact B2273379
  · exact B2273383
  · exact B2273387
  · exact B2273391
  · exact B2273395
  · exact B2273399
  · exact B2273403
  · exact B2273407
  · exact B2273411
  · exact B2273415
  · exact B2273419
  · exact B2273423
  · exact B2273427
  · exact B2273431
  · exact B2273435
theorem solution (m : ℕ) (hlo : 2271435 ≤ m) (hhi : m ≤ 2273435) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 567858 ≤ j := by omega
    have hj2 : j ≤ 568358 := by omega
    have hb : Blo 2271435 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
