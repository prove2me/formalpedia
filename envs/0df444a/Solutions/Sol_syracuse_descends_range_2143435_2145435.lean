-- Prove2me | solution 1 for syracuse_descends_range_2143435_2145435
-- status  : ACCEPTED   (prove)
-- author  : @chstdu
-- created : 2026-09-23T17:17:19.045901+00:00
-- url     : https://prove2.me/submissions/7eef6d3f-9514-4276-acb8-c44e1954b55e

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

theorem B2411365 : Blo 2143435 2411365 := bbase (se 4 (by rfl) ⟨226065, by rfl⟩ : syracuseStep 2411365 = 452131) (by norm_num)
theorem B3215153 : Blo 2143435 3215153 := bstep (se 2 (by rfl) ⟨1205682, by rfl⟩ : syracuseStep 3215153 = 2411365) B2411365
theorem B2143435 : Blo 2143435 2143435 := bstep (se 1 (by rfl) ⟨1607576, by rfl⟩ : syracuseStep 2143435 = 3215153) B3215153
theorem B6103781 : Blo 2143435 6103781 := bbase (se 4 (by rfl) ⟨572229, by rfl⟩ : syracuseStep 6103781 = 1144459) (by norm_num)
theorem B4069187 : Blo 2143435 4069187 := bstep (se 1 (by rfl) ⟨3051890, by rfl⟩ : syracuseStep 4069187 = 6103781) B6103781
theorem B2712791 : Blo 2143435 2712791 := bstep (se 1 (by rfl) ⟨2034593, by rfl⟩ : syracuseStep 2712791 = 4069187) B4069187
theorem B7234109 : Blo 2143435 7234109 := bstep (se 3 (by rfl) ⟨1356395, by rfl⟩ : syracuseStep 7234109 = 2712791) B2712791
theorem B4822739 : Blo 2143435 4822739 := bstep (se 1 (by rfl) ⟨3617054, by rfl⟩ : syracuseStep 4822739 = 7234109) B7234109
theorem B3215159 : Blo 2143435 3215159 := bstep (se 1 (by rfl) ⟨2411369, by rfl⟩ : syracuseStep 3215159 = 4822739) B4822739
theorem B2143439 : Blo 2143435 2143439 := bstep (se 1 (by rfl) ⟨1607579, by rfl⟩ : syracuseStep 2143439 = 3215159) B3215159
theorem B3215165 : Blo 2143435 3215165 := bbase (se 3 (by rfl) ⟨602843, by rfl⟩ : syracuseStep 3215165 = 1205687) (by norm_num)
theorem B2143443 : Blo 2143435 2143443 := bstep (se 1 (by rfl) ⟨1607582, by rfl⟩ : syracuseStep 2143443 = 3215165) B3215165
theorem B4822757 : Blo 2143435 4822757 := bbase (se 4 (by rfl) ⟨452133, by rfl⟩ : syracuseStep 4822757 = 904267) (by norm_num)
theorem B3215171 : Blo 2143435 3215171 := bstep (se 1 (by rfl) ⟨2411378, by rfl⟩ : syracuseStep 3215171 = 4822757) B4822757
theorem B2143447 : Blo 2143435 2143447 := bstep (se 1 (by rfl) ⟨1607585, by rfl⟩ : syracuseStep 2143447 = 3215171) B3215171
theorem B5425613 : Blo 2143435 5425613 := bbase (se 3 (by rfl) ⟨1017302, by rfl⟩ : syracuseStep 5425613 = 2034605) (by norm_num)
theorem B3617075 : Blo 2143435 3617075 := bstep (se 1 (by rfl) ⟨2712806, by rfl⟩ : syracuseStep 3617075 = 5425613) B5425613
theorem B2411383 : Blo 2143435 2411383 := bstep (se 1 (by rfl) ⟨1808537, by rfl⟩ : syracuseStep 2411383 = 3617075) B3617075
theorem B3215177 : Blo 2143435 3215177 := bstep (se 2 (by rfl) ⟨1205691, by rfl⟩ : syracuseStep 3215177 = 2411383) B2411383
theorem B2143451 : Blo 2143435 2143451 := bstep (se 1 (by rfl) ⟨1607588, by rfl⟩ : syracuseStep 2143451 = 3215177) B3215177
theorem B2172701 : Blo 2143435 2172701 := bbase (se 3 (by rfl) ⟨407381, by rfl⟩ : syracuseStep 2172701 = 814763) (by norm_num)
theorem B5793869 : Blo 2143435 5793869 := bstep (se 3 (by rfl) ⟨1086350, by rfl⟩ : syracuseStep 5793869 = 2172701) B2172701
theorem B3862579 : Blo 2143435 3862579 := bstep (se 1 (by rfl) ⟨2896934, by rfl⟩ : syracuseStep 3862579 = 5793869) B5793869
theorem B5150105 : Blo 2143435 5150105 := bstep (se 2 (by rfl) ⟨1931289, by rfl⟩ : syracuseStep 5150105 = 3862579) B3862579
theorem B3433403 : Blo 2143435 3433403 := bstep (se 1 (by rfl) ⟨2575052, by rfl⟩ : syracuseStep 3433403 = 5150105) B5150105
theorem B2288935 : Blo 2143435 2288935 := bstep (se 1 (by rfl) ⟨1716701, by rfl⟩ : syracuseStep 2288935 = 3433403) B3433403
theorem B3051913 : Blo 2143435 3051913 := bstep (se 2 (by rfl) ⟨1144467, by rfl⟩ : syracuseStep 3051913 = 2288935) B2288935
theorem B4069217 : Blo 2143435 4069217 := bstep (se 2 (by rfl) ⟨1525956, by rfl⟩ : syracuseStep 4069217 = 3051913) B3051913
theorem B10851245 : Blo 2143435 10851245 := bstep (se 3 (by rfl) ⟨2034608, by rfl⟩ : syracuseStep 10851245 = 4069217) B4069217
theorem B7234163 : Blo 2143435 7234163 := bstep (se 1 (by rfl) ⟨5425622, by rfl⟩ : syracuseStep 7234163 = 10851245) B10851245
theorem B4822775 : Blo 2143435 4822775 := bstep (se 1 (by rfl) ⟨3617081, by rfl⟩ : syracuseStep 4822775 = 7234163) B7234163
theorem B3215183 : Blo 2143435 3215183 := bstep (se 1 (by rfl) ⟨2411387, by rfl⟩ : syracuseStep 3215183 = 4822775) B4822775
theorem B2143455 : Blo 2143435 2143455 := bstep (se 1 (by rfl) ⟨1607591, by rfl⟩ : syracuseStep 2143455 = 3215183) B3215183
theorem B3215189 : Blo 2143435 3215189 := bbase (se 9 (by rfl) ⟨9419, by rfl⟩ : syracuseStep 3215189 = 18839) (by norm_num)
theorem B2143459 : Blo 2143435 2143459 := bstep (se 1 (by rfl) ⟨1607594, by rfl⟩ : syracuseStep 2143459 = 3215189) B3215189
theorem B3093565 : Blo 2143435 3093565 := bbase (se 3 (by rfl) ⟨580043, by rfl⟩ : syracuseStep 3093565 = 1160087) (by norm_num)
theorem B4124753 : Blo 2143435 4124753 := bstep (se 2 (by rfl) ⟨1546782, by rfl⟩ : syracuseStep 4124753 = 3093565) B3093565
theorem B2749835 : Blo 2143435 2749835 := bstep (se 1 (by rfl) ⟨2062376, by rfl⟩ : syracuseStep 2749835 = 4124753) B4124753
theorem B7332893 : Blo 2143435 7332893 := bstep (se 3 (by rfl) ⟨1374917, by rfl⟩ : syracuseStep 7332893 = 2749835) B2749835
theorem B4888595 : Blo 2143435 4888595 := bstep (se 1 (by rfl) ⟨3666446, by rfl⟩ : syracuseStep 4888595 = 7332893) B7332893
theorem B3259063 : Blo 2143435 3259063 := bstep (se 1 (by rfl) ⟨2444297, by rfl⟩ : syracuseStep 3259063 = 4888595) B4888595
theorem B4345417 : Blo 2143435 4345417 := bstep (se 2 (by rfl) ⟨1629531, by rfl⟩ : syracuseStep 4345417 = 3259063) B3259063
theorem B23175557 : Blo 2143435 23175557 := bstep (se 4 (by rfl) ⟨2172708, by rfl⟩ : syracuseStep 23175557 = 4345417) B4345417
theorem B15450371 : Blo 2143435 15450371 := bstep (se 1 (by rfl) ⟨11587778, by rfl⟩ : syracuseStep 15450371 = 23175557) B23175557
theorem B10300247 : Blo 2143435 10300247 := bstep (se 1 (by rfl) ⟨7725185, by rfl⟩ : syracuseStep 10300247 = 15450371) B15450371
theorem B6866831 : Blo 2143435 6866831 := bstep (se 1 (by rfl) ⟨5150123, by rfl⟩ : syracuseStep 6866831 = 10300247) B10300247
theorem B4577887 : Blo 2143435 4577887 := bstep (se 1 (by rfl) ⟨3433415, by rfl⟩ : syracuseStep 4577887 = 6866831) B6866831
theorem B6103849 : Blo 2143435 6103849 := bstep (se 2 (by rfl) ⟨2288943, by rfl⟩ : syracuseStep 6103849 = 4577887) B4577887
theorem B8138465 : Blo 2143435 8138465 := bstep (se 2 (by rfl) ⟨3051924, by rfl⟩ : syracuseStep 8138465 = 6103849) B6103849
theorem B5425643 : Blo 2143435 5425643 := bstep (se 1 (by rfl) ⟨4069232, by rfl⟩ : syracuseStep 5425643 = 8138465) B8138465
theorem B3617095 : Blo 2143435 3617095 := bstep (se 1 (by rfl) ⟨2712821, by rfl⟩ : syracuseStep 3617095 = 5425643) B5425643
theorem B4822793 : Blo 2143435 4822793 := bstep (se 2 (by rfl) ⟨1808547, by rfl⟩ : syracuseStep 4822793 = 3617095) B3617095
theorem B3215195 : Blo 2143435 3215195 := bstep (se 1 (by rfl) ⟨2411396, by rfl⟩ : syracuseStep 3215195 = 4822793) B4822793
theorem B2143463 : Blo 2143435 2143463 := bstep (se 1 (by rfl) ⟨1607597, by rfl⟩ : syracuseStep 2143463 = 3215195) B3215195
theorem B2411401 : Blo 2143435 2411401 := bbase (se 2 (by rfl) ⟨904275, by rfl⟩ : syracuseStep 2411401 = 1808551) (by norm_num)
theorem B3215201 : Blo 2143435 3215201 := bstep (se 2 (by rfl) ⟨1205700, by rfl⟩ : syracuseStep 3215201 = 2411401) B2411401
theorem B2143467 : Blo 2143435 2143467 := bstep (se 1 (by rfl) ⟨1607600, by rfl⟩ : syracuseStep 2143467 = 3215201) B3215201
theorem B2787361 : Blo 2143435 2787361 := bbase (se 2 (by rfl) ⟨1045260, by rfl⟩ : syracuseStep 2787361 = 2090521) (by norm_num)
theorem B14865925 : Blo 2143435 14865925 := bstep (se 4 (by rfl) ⟨1393680, by rfl⟩ : syracuseStep 14865925 = 2787361) B2787361
theorem B19821233 : Blo 2143435 19821233 := bstep (se 2 (by rfl) ⟨7432962, by rfl⟩ : syracuseStep 19821233 = 14865925) B14865925
theorem B52856621 : Blo 2143435 52856621 := bstep (se 3 (by rfl) ⟨9910616, by rfl⟩ : syracuseStep 52856621 = 19821233) B19821233
theorem B35237747 : Blo 2143435 35237747 := bstep (se 1 (by rfl) ⟨26428310, by rfl⟩ : syracuseStep 35237747 = 52856621) B52856621
theorem B23491831 : Blo 2143435 23491831 := bstep (se 1 (by rfl) ⟨17618873, by rfl⟩ : syracuseStep 23491831 = 35237747) B35237747
theorem B31322441 : Blo 2143435 31322441 := bstep (se 2 (by rfl) ⟨11745915, by rfl⟩ : syracuseStep 31322441 = 23491831) B23491831
theorem B83526509 : Blo 2143435 83526509 := bstep (se 3 (by rfl) ⟨15661220, by rfl⟩ : syracuseStep 83526509 = 31322441) B31322441
theorem B222737357 : Blo 2143435 222737357 := bstep (se 3 (by rfl) ⟨41763254, by rfl⟩ : syracuseStep 222737357 = 83526509) B83526509
theorem B148491571 : Blo 2143435 148491571 := bstep (se 1 (by rfl) ⟨111368678, by rfl⟩ : syracuseStep 148491571 = 222737357) B222737357
theorem B197988761 : Blo 2143435 197988761 := bstep (se 2 (by rfl) ⟨74245785, by rfl⟩ : syracuseStep 197988761 = 148491571) B148491571
theorem B131992507 : Blo 2143435 131992507 := bstep (se 1 (by rfl) ⟨98994380, by rfl⟩ : syracuseStep 131992507 = 197988761) B197988761
theorem B175990009 : Blo 2143435 175990009 := bstep (se 2 (by rfl) ⟨65996253, by rfl⟩ : syracuseStep 175990009 = 131992507) B131992507
theorem B234653345 : Blo 2143435 234653345 := bstep (se 2 (by rfl) ⟨87995004, by rfl⟩ : syracuseStep 234653345 = 175990009) B175990009
theorem B156435563 : Blo 2143435 156435563 := bstep (se 1 (by rfl) ⟨117326672, by rfl⟩ : syracuseStep 156435563 = 234653345) B234653345
theorem B104290375 : Blo 2143435 104290375 := bstep (se 1 (by rfl) ⟨78217781, by rfl⟩ : syracuseStep 104290375 = 156435563) B156435563
theorem B139053833 : Blo 2143435 139053833 := bstep (se 2 (by rfl) ⟨52145187, by rfl⟩ : syracuseStep 139053833 = 104290375) B104290375
theorem B92702555 : Blo 2143435 92702555 := bstep (se 1 (by rfl) ⟨69526916, by rfl⟩ : syracuseStep 92702555 = 139053833) B139053833
theorem B61801703 : Blo 2143435 61801703 := bstep (se 1 (by rfl) ⟨46351277, by rfl⟩ : syracuseStep 61801703 = 92702555) B92702555
theorem B41201135 : Blo 2143435 41201135 := bstep (se 1 (by rfl) ⟨30900851, by rfl⟩ : syracuseStep 41201135 = 61801703) B61801703
theorem B27467423 : Blo 2143435 27467423 := bstep (se 1 (by rfl) ⟨20600567, by rfl⟩ : syracuseStep 27467423 = 41201135) B41201135
theorem B18311615 : Blo 2143435 18311615 := bstep (se 1 (by rfl) ⟨13733711, by rfl⟩ : syracuseStep 18311615 = 27467423) B27467423
theorem B12207743 : Blo 2143435 12207743 := bstep (se 1 (by rfl) ⟨9155807, by rfl⟩ : syracuseStep 12207743 = 18311615) B18311615
theorem B8138495 : Blo 2143435 8138495 := bstep (se 1 (by rfl) ⟨6103871, by rfl⟩ : syracuseStep 8138495 = 12207743) B12207743
theorem B5425663 : Blo 2143435 5425663 := bstep (se 1 (by rfl) ⟨4069247, by rfl⟩ : syracuseStep 5425663 = 8138495) B8138495
theorem B7234217 : Blo 2143435 7234217 := bstep (se 2 (by rfl) ⟨2712831, by rfl⟩ : syracuseStep 7234217 = 5425663) B5425663
theorem B4822811 : Blo 2143435 4822811 := bstep (se 1 (by rfl) ⟨3617108, by rfl⟩ : syracuseStep 4822811 = 7234217) B7234217
theorem B3215207 : Blo 2143435 3215207 := bstep (se 1 (by rfl) ⟨2411405, by rfl⟩ : syracuseStep 3215207 = 4822811) B4822811
theorem B2143471 : Blo 2143435 2143471 := bstep (se 1 (by rfl) ⟨1607603, by rfl⟩ : syracuseStep 2143471 = 3215207) B3215207
theorem B3215213 : Blo 2143435 3215213 := bbase (se 3 (by rfl) ⟨602852, by rfl⟩ : syracuseStep 3215213 = 1205705) (by norm_num)
theorem B2143475 : Blo 2143435 2143475 := bstep (se 1 (by rfl) ⟨1607606, by rfl⟩ : syracuseStep 2143475 = 3215213) B3215213
theorem B4822829 : Blo 2143435 4822829 := bbase (se 3 (by rfl) ⟨904280, by rfl⟩ : syracuseStep 4822829 = 1808561) (by norm_num)
theorem B3215219 : Blo 2143435 3215219 := bstep (se 1 (by rfl) ⟨2411414, by rfl⟩ : syracuseStep 3215219 = 4822829) B4822829
theorem B2143479 : Blo 2143435 2143479 := bstep (se 1 (by rfl) ⟨1607609, by rfl⟩ : syracuseStep 2143479 = 3215219) B3215219
theorem B9155861 : Blo 2143435 9155861 := bbase (se 6 (by rfl) ⟨214590, by rfl⟩ : syracuseStep 9155861 = 429181) (by norm_num)
theorem B6103907 : Blo 2143435 6103907 := bstep (se 1 (by rfl) ⟨4577930, by rfl⟩ : syracuseStep 6103907 = 9155861) B9155861
theorem B4069271 : Blo 2143435 4069271 := bstep (se 1 (by rfl) ⟨3051953, by rfl⟩ : syracuseStep 4069271 = 6103907) B6103907
theorem B2712847 : Blo 2143435 2712847 := bstep (se 1 (by rfl) ⟨2034635, by rfl⟩ : syracuseStep 2712847 = 4069271) B4069271
theorem B3617129 : Blo 2143435 3617129 := bstep (se 2 (by rfl) ⟨1356423, by rfl⟩ : syracuseStep 3617129 = 2712847) B2712847
theorem B2411419 : Blo 2143435 2411419 := bstep (se 1 (by rfl) ⟨1808564, by rfl⟩ : syracuseStep 2411419 = 3617129) B3617129
theorem B3215225 : Blo 2143435 3215225 := bstep (se 2 (by rfl) ⟨1205709, by rfl⟩ : syracuseStep 3215225 = 2411419) B2411419
theorem B2143483 : Blo 2143435 2143483 := bstep (se 1 (by rfl) ⟨1607612, by rfl⟩ : syracuseStep 2143483 = 3215225) B3215225
theorem B13733813 : Blo 2143435 13733813 := bbase (se 5 (by rfl) ⟨643772, by rfl⟩ : syracuseStep 13733813 = 1287545) (by norm_num)
theorem B36623501 : Blo 2143435 36623501 := bstep (se 3 (by rfl) ⟨6866906, by rfl⟩ : syracuseStep 36623501 = 13733813) B13733813
theorem B24415667 : Blo 2143435 24415667 := bstep (se 1 (by rfl) ⟨18311750, by rfl⟩ : syracuseStep 24415667 = 36623501) B36623501
theorem B16277111 : Blo 2143435 16277111 := bstep (se 1 (by rfl) ⟨12207833, by rfl⟩ : syracuseStep 16277111 = 24415667) B24415667
theorem B10851407 : Blo 2143435 10851407 := bstep (se 1 (by rfl) ⟨8138555, by rfl⟩ : syracuseStep 10851407 = 16277111) B16277111
theorem B7234271 : Blo 2143435 7234271 := bstep (se 1 (by rfl) ⟨5425703, by rfl⟩ : syracuseStep 7234271 = 10851407) B10851407
theorem B4822847 : Blo 2143435 4822847 := bstep (se 1 (by rfl) ⟨3617135, by rfl⟩ : syracuseStep 4822847 = 7234271) B7234271
theorem B3215231 : Blo 2143435 3215231 := bstep (se 1 (by rfl) ⟨2411423, by rfl⟩ : syracuseStep 3215231 = 4822847) B4822847
theorem B2143487 : Blo 2143435 2143487 := bstep (se 1 (by rfl) ⟨1607615, by rfl⟩ : syracuseStep 2143487 = 3215231) B3215231
theorem B3215237 : Blo 2143435 3215237 := bbase (se 4 (by rfl) ⟨301428, by rfl⟩ : syracuseStep 3215237 = 602857) (by norm_num)
theorem B2143491 : Blo 2143435 2143491 := bstep (se 1 (by rfl) ⟨1607618, by rfl⟩ : syracuseStep 2143491 = 3215237) B3215237
theorem B3617149 : Blo 2143435 3617149 := bbase (se 3 (by rfl) ⟨678215, by rfl⟩ : syracuseStep 3617149 = 1356431) (by norm_num)
theorem B4822865 : Blo 2143435 4822865 := bstep (se 2 (by rfl) ⟨1808574, by rfl⟩ : syracuseStep 4822865 = 3617149) B3617149
theorem B3215243 : Blo 2143435 3215243 := bstep (se 1 (by rfl) ⟨2411432, by rfl⟩ : syracuseStep 3215243 = 4822865) B4822865
theorem B2143495 : Blo 2143435 2143495 := bstep (se 1 (by rfl) ⟨1607621, by rfl⟩ : syracuseStep 2143495 = 3215243) B3215243
theorem B2411437 : Blo 2143435 2411437 := bbase (se 3 (by rfl) ⟨452144, by rfl⟩ : syracuseStep 2411437 = 904289) (by norm_num)
theorem B3215249 : Blo 2143435 3215249 := bstep (se 2 (by rfl) ⟨1205718, by rfl⟩ : syracuseStep 3215249 = 2411437) B2411437
theorem B2143499 : Blo 2143435 2143499 := bstep (se 1 (by rfl) ⟨1607624, by rfl⟩ : syracuseStep 2143499 = 3215249) B3215249
theorem B7234325 : Blo 2143435 7234325 := bbase (se 6 (by rfl) ⟨169554, by rfl⟩ : syracuseStep 7234325 = 339109) (by norm_num)
theorem B4822883 : Blo 2143435 4822883 := bstep (se 1 (by rfl) ⟨3617162, by rfl⟩ : syracuseStep 4822883 = 7234325) B7234325
theorem B3215255 : Blo 2143435 3215255 := bstep (se 1 (by rfl) ⟨2411441, by rfl⟩ : syracuseStep 3215255 = 4822883) B4822883
theorem B2143503 : Blo 2143435 2143503 := bstep (se 1 (by rfl) ⟨1607627, by rfl⟩ : syracuseStep 2143503 = 3215255) B3215255
theorem B3215261 : Blo 2143435 3215261 := bbase (se 3 (by rfl) ⟨602861, by rfl⟩ : syracuseStep 3215261 = 1205723) (by norm_num)
theorem B2143507 : Blo 2143435 2143507 := bstep (se 1 (by rfl) ⟨1607630, by rfl⟩ : syracuseStep 2143507 = 3215261) B3215261
theorem B4822901 : Blo 2143435 4822901 := bbase (se 5 (by rfl) ⟨226073, by rfl⟩ : syracuseStep 4822901 = 452147) (by norm_num)
theorem B3215267 : Blo 2143435 3215267 := bstep (se 1 (by rfl) ⟨2411450, by rfl⟩ : syracuseStep 3215267 = 4822901) B4822901
theorem B2143511 : Blo 2143435 2143511 := bstep (se 1 (by rfl) ⟨1607633, by rfl⟩ : syracuseStep 2143511 = 3215267) B3215267
theorem B2749901 : Blo 2143435 2749901 := bbase (se 3 (by rfl) ⟨515606, by rfl⟩ : syracuseStep 2749901 = 1031213) (by norm_num)
theorem B29332277 : Blo 2143435 29332277 := bstep (se 5 (by rfl) ⟨1374950, by rfl⟩ : syracuseStep 29332277 = 2749901) B2749901
theorem B19554851 : Blo 2143435 19554851 := bstep (se 1 (by rfl) ⟨14666138, by rfl⟩ : syracuseStep 19554851 = 29332277) B29332277
theorem B13036567 : Blo 2143435 13036567 := bstep (se 1 (by rfl) ⟨9777425, by rfl⟩ : syracuseStep 13036567 = 19554851) B19554851
theorem B17382089 : Blo 2143435 17382089 := bstep (se 2 (by rfl) ⟨6518283, by rfl⟩ : syracuseStep 17382089 = 13036567) B13036567
theorem B11588059 : Blo 2143435 11588059 := bstep (se 1 (by rfl) ⟨8691044, by rfl⟩ : syracuseStep 11588059 = 17382089) B17382089
theorem B15450745 : Blo 2143435 15450745 := bstep (se 2 (by rfl) ⟨5794029, by rfl⟩ : syracuseStep 15450745 = 11588059) B11588059
theorem B20600993 : Blo 2143435 20600993 := bstep (se 2 (by rfl) ⟨7725372, by rfl⟩ : syracuseStep 20600993 = 15450745) B15450745
theorem B13733995 : Blo 2143435 13733995 := bstep (se 1 (by rfl) ⟨10300496, by rfl⟩ : syracuseStep 13733995 = 20600993) B20600993
theorem B18311993 : Blo 2143435 18311993 := bstep (se 2 (by rfl) ⟨6866997, by rfl⟩ : syracuseStep 18311993 = 13733995) B13733995
theorem B12207995 : Blo 2143435 12207995 := bstep (se 1 (by rfl) ⟨9155996, by rfl⟩ : syracuseStep 12207995 = 18311993) B18311993
theorem B8138663 : Blo 2143435 8138663 := bstep (se 1 (by rfl) ⟨6103997, by rfl⟩ : syracuseStep 8138663 = 12207995) B12207995
theorem B5425775 : Blo 2143435 5425775 := bstep (se 1 (by rfl) ⟨4069331, by rfl⟩ : syracuseStep 5425775 = 8138663) B8138663
theorem B3617183 : Blo 2143435 3617183 := bstep (se 1 (by rfl) ⟨2712887, by rfl⟩ : syracuseStep 3617183 = 5425775) B5425775
theorem B2411455 : Blo 2143435 2411455 := bstep (se 1 (by rfl) ⟨1808591, by rfl⟩ : syracuseStep 2411455 = 3617183) B3617183
theorem B3215273 : Blo 2143435 3215273 := bstep (se 2 (by rfl) ⟨1205727, by rfl⟩ : syracuseStep 3215273 = 2411455) B2411455
theorem B2143515 : Blo 2143435 2143515 := bstep (se 1 (by rfl) ⟨1607636, by rfl⟩ : syracuseStep 2143515 = 3215273) B3215273
theorem B8138677 : Blo 2143435 8138677 := bbase (se 5 (by rfl) ⟨381500, by rfl⟩ : syracuseStep 8138677 = 763001) (by norm_num)
theorem B10851569 : Blo 2143435 10851569 := bstep (se 2 (by rfl) ⟨4069338, by rfl⟩ : syracuseStep 10851569 = 8138677) B8138677
theorem B7234379 : Blo 2143435 7234379 := bstep (se 1 (by rfl) ⟨5425784, by rfl⟩ : syracuseStep 7234379 = 10851569) B10851569
theorem B4822919 : Blo 2143435 4822919 := bstep (se 1 (by rfl) ⟨3617189, by rfl⟩ : syracuseStep 4822919 = 7234379) B7234379
theorem B3215279 : Blo 2143435 3215279 := bstep (se 1 (by rfl) ⟨2411459, by rfl⟩ : syracuseStep 3215279 = 4822919) B4822919
theorem B2143519 : Blo 2143435 2143519 := bstep (se 1 (by rfl) ⟨1607639, by rfl⟩ : syracuseStep 2143519 = 3215279) B3215279
theorem B3215285 : Blo 2143435 3215285 := bbase (se 5 (by rfl) ⟨150716, by rfl⟩ : syracuseStep 3215285 = 301433) (by norm_num)
theorem B2143523 : Blo 2143435 2143523 := bstep (se 1 (by rfl) ⟨1607642, by rfl⟩ : syracuseStep 2143523 = 3215285) B3215285
theorem B5425805 : Blo 2143435 5425805 := bbase (se 3 (by rfl) ⟨1017338, by rfl⟩ : syracuseStep 5425805 = 2034677) (by norm_num)
theorem B3617203 : Blo 2143435 3617203 := bstep (se 1 (by rfl) ⟨2712902, by rfl⟩ : syracuseStep 3617203 = 5425805) B5425805
theorem B4822937 : Blo 2143435 4822937 := bstep (se 2 (by rfl) ⟨1808601, by rfl⟩ : syracuseStep 4822937 = 3617203) B3617203
theorem B3215291 : Blo 2143435 3215291 := bstep (se 1 (by rfl) ⟨2411468, by rfl⟩ : syracuseStep 3215291 = 4822937) B4822937
theorem B2143527 : Blo 2143435 2143527 := bstep (se 1 (by rfl) ⟨1607645, by rfl⟩ : syracuseStep 2143527 = 3215291) B3215291
theorem B2411473 : Blo 2143435 2411473 := bbase (se 2 (by rfl) ⟨904302, by rfl⟩ : syracuseStep 2411473 = 1808605) (by norm_num)
theorem B3215297 : Blo 2143435 3215297 := bstep (se 2 (by rfl) ⟨1205736, by rfl⟩ : syracuseStep 3215297 = 2411473) B2411473
theorem B2143531 : Blo 2143435 2143531 := bstep (se 1 (by rfl) ⟨1607648, by rfl⟩ : syracuseStep 2143531 = 3215297) B3215297
theorem B5794085 : Blo 2143435 5794085 := bbase (se 4 (by rfl) ⟨543195, by rfl⟩ : syracuseStep 5794085 = 1086391) (by norm_num)
theorem B3862723 : Blo 2143435 3862723 := bstep (se 1 (by rfl) ⟨2897042, by rfl⟩ : syracuseStep 3862723 = 5794085) B5794085
theorem B5150297 : Blo 2143435 5150297 := bstep (se 2 (by rfl) ⟨1931361, by rfl⟩ : syracuseStep 5150297 = 3862723) B3862723
theorem B3433531 : Blo 2143435 3433531 := bstep (se 1 (by rfl) ⟨2575148, by rfl⟩ : syracuseStep 3433531 = 5150297) B5150297
theorem B4578041 : Blo 2143435 4578041 := bstep (se 2 (by rfl) ⟨1716765, by rfl⟩ : syracuseStep 4578041 = 3433531) B3433531
theorem B3052027 : Blo 2143435 3052027 := bstep (se 1 (by rfl) ⟨2289020, by rfl⟩ : syracuseStep 3052027 = 4578041) B4578041
theorem B4069369 : Blo 2143435 4069369 := bstep (se 2 (by rfl) ⟨1526013, by rfl⟩ : syracuseStep 4069369 = 3052027) B3052027
theorem B5425825 : Blo 2143435 5425825 := bstep (se 2 (by rfl) ⟨2034684, by rfl⟩ : syracuseStep 5425825 = 4069369) B4069369
theorem B7234433 : Blo 2143435 7234433 := bstep (se 2 (by rfl) ⟨2712912, by rfl⟩ : syracuseStep 7234433 = 5425825) B5425825
theorem B4822955 : Blo 2143435 4822955 := bstep (se 1 (by rfl) ⟨3617216, by rfl⟩ : syracuseStep 4822955 = 7234433) B7234433
theorem B3215303 : Blo 2143435 3215303 := bstep (se 1 (by rfl) ⟨2411477, by rfl⟩ : syracuseStep 3215303 = 4822955) B4822955
theorem B2143535 : Blo 2143435 2143535 := bstep (se 1 (by rfl) ⟨1607651, by rfl⟩ : syracuseStep 2143535 = 3215303) B3215303
theorem B3215309 : Blo 2143435 3215309 := bbase (se 3 (by rfl) ⟨602870, by rfl⟩ : syracuseStep 3215309 = 1205741) (by norm_num)
theorem B2143539 : Blo 2143435 2143539 := bstep (se 1 (by rfl) ⟨1607654, by rfl⟩ : syracuseStep 2143539 = 3215309) B3215309
theorem B4822973 : Blo 2143435 4822973 := bbase (se 3 (by rfl) ⟨904307, by rfl⟩ : syracuseStep 4822973 = 1808615) (by norm_num)
theorem B3215315 : Blo 2143435 3215315 := bstep (se 1 (by rfl) ⟨2411486, by rfl⟩ : syracuseStep 3215315 = 4822973) B4822973
theorem B2143543 : Blo 2143435 2143543 := bstep (se 1 (by rfl) ⟨1607657, by rfl⟩ : syracuseStep 2143543 = 3215315) B3215315
theorem B3617237 : Blo 2143435 3617237 := bbase (se 7 (by rfl) ⟨42389, by rfl⟩ : syracuseStep 3617237 = 84779) (by norm_num)
theorem B2411491 : Blo 2143435 2411491 := bstep (se 1 (by rfl) ⟨1808618, by rfl⟩ : syracuseStep 2411491 = 3617237) B3617237
theorem B3215321 : Blo 2143435 3215321 := bstep (se 2 (by rfl) ⟨1205745, by rfl⟩ : syracuseStep 3215321 = 2411491) B2411491
theorem B2143547 : Blo 2143435 2143547 := bstep (se 1 (by rfl) ⟨1607660, by rfl⟩ : syracuseStep 2143547 = 3215321) B3215321
theorem B9156149 : Blo 2143435 9156149 := bbase (se 5 (by rfl) ⟨429194, by rfl⟩ : syracuseStep 9156149 = 858389) (by norm_num)
theorem B6104099 : Blo 2143435 6104099 := bstep (se 1 (by rfl) ⟨4578074, by rfl⟩ : syracuseStep 6104099 = 9156149) B9156149
theorem B16277597 : Blo 2143435 16277597 := bstep (se 3 (by rfl) ⟨3052049, by rfl⟩ : syracuseStep 16277597 = 6104099) B6104099
theorem B10851731 : Blo 2143435 10851731 := bstep (se 1 (by rfl) ⟨8138798, by rfl⟩ : syracuseStep 10851731 = 16277597) B16277597
theorem B7234487 : Blo 2143435 7234487 := bstep (se 1 (by rfl) ⟨5425865, by rfl⟩ : syracuseStep 7234487 = 10851731) B10851731
theorem B4822991 : Blo 2143435 4822991 := bstep (se 1 (by rfl) ⟨3617243, by rfl⟩ : syracuseStep 4822991 = 7234487) B7234487
theorem B3215327 : Blo 2143435 3215327 := bstep (se 1 (by rfl) ⟨2411495, by rfl⟩ : syracuseStep 3215327 = 4822991) B4822991
theorem B2143551 : Blo 2143435 2143551 := bstep (se 1 (by rfl) ⟨1607663, by rfl⟩ : syracuseStep 2143551 = 3215327) B3215327
theorem B3215333 : Blo 2143435 3215333 := bbase (se 4 (by rfl) ⟨301437, by rfl⟩ : syracuseStep 3215333 = 602875) (by norm_num)
theorem B2143555 : Blo 2143435 2143555 := bstep (se 1 (by rfl) ⟨1607666, by rfl⟩ : syracuseStep 2143555 = 3215333) B3215333
theorem B10300709 : Blo 2143435 10300709 := bbase (se 4 (by rfl) ⟨965691, by rfl⟩ : syracuseStep 10300709 = 1931383) (by norm_num)
theorem B6867139 : Blo 2143435 6867139 := bstep (se 1 (by rfl) ⟨5150354, by rfl⟩ : syracuseStep 6867139 = 10300709) B10300709
theorem B9156185 : Blo 2143435 9156185 := bstep (se 2 (by rfl) ⟨3433569, by rfl⟩ : syracuseStep 9156185 = 6867139) B6867139
theorem B6104123 : Blo 2143435 6104123 := bstep (se 1 (by rfl) ⟨4578092, by rfl⟩ : syracuseStep 6104123 = 9156185) B9156185
theorem B4069415 : Blo 2143435 4069415 := bstep (se 1 (by rfl) ⟨3052061, by rfl⟩ : syracuseStep 4069415 = 6104123) B6104123
theorem B2712943 : Blo 2143435 2712943 := bstep (se 1 (by rfl) ⟨2034707, by rfl⟩ : syracuseStep 2712943 = 4069415) B4069415
theorem B3617257 : Blo 2143435 3617257 := bstep (se 2 (by rfl) ⟨1356471, by rfl⟩ : syracuseStep 3617257 = 2712943) B2712943
theorem B4823009 : Blo 2143435 4823009 := bstep (se 2 (by rfl) ⟨1808628, by rfl⟩ : syracuseStep 4823009 = 3617257) B3617257
theorem B3215339 : Blo 2143435 3215339 := bstep (se 1 (by rfl) ⟨2411504, by rfl⟩ : syracuseStep 3215339 = 4823009) B4823009
theorem B2143559 : Blo 2143435 2143559 := bstep (se 1 (by rfl) ⟨1607669, by rfl⟩ : syracuseStep 2143559 = 3215339) B3215339
theorem B2411509 : Blo 2143435 2411509 := bbase (se 5 (by rfl) ⟨113039, by rfl⟩ : syracuseStep 2411509 = 226079) (by norm_num)
theorem B3215345 : Blo 2143435 3215345 := bstep (se 2 (by rfl) ⟨1205754, by rfl⟩ : syracuseStep 3215345 = 2411509) B2411509
theorem B2143563 : Blo 2143435 2143563 := bstep (se 1 (by rfl) ⟨1607672, by rfl⟩ : syracuseStep 2143563 = 3215345) B3215345
theorem B2712953 : Blo 2143435 2712953 := bbase (se 2 (by rfl) ⟨1017357, by rfl⟩ : syracuseStep 2712953 = 2034715) (by norm_num)
theorem B7234541 : Blo 2143435 7234541 := bstep (se 3 (by rfl) ⟨1356476, by rfl⟩ : syracuseStep 7234541 = 2712953) B2712953
theorem B4823027 : Blo 2143435 4823027 := bstep (se 1 (by rfl) ⟨3617270, by rfl⟩ : syracuseStep 4823027 = 7234541) B7234541
theorem B3215351 : Blo 2143435 3215351 := bstep (se 1 (by rfl) ⟨2411513, by rfl⟩ : syracuseStep 3215351 = 4823027) B4823027
theorem B2143567 : Blo 2143435 2143567 := bstep (se 1 (by rfl) ⟨1607675, by rfl⟩ : syracuseStep 2143567 = 3215351) B3215351
theorem B3215357 : Blo 2143435 3215357 := bbase (se 3 (by rfl) ⟨602879, by rfl⟩ : syracuseStep 3215357 = 1205759) (by norm_num)
theorem B2143571 : Blo 2143435 2143571 := bstep (se 1 (by rfl) ⟨1607678, by rfl⟩ : syracuseStep 2143571 = 3215357) B3215357
theorem B4823045 : Blo 2143435 4823045 := bbase (se 4 (by rfl) ⟨452160, by rfl⟩ : syracuseStep 4823045 = 904321) (by norm_num)
theorem B3215363 : Blo 2143435 3215363 := bstep (se 1 (by rfl) ⟨2411522, by rfl⟩ : syracuseStep 3215363 = 4823045) B4823045
theorem B2143575 : Blo 2143435 2143575 := bstep (se 1 (by rfl) ⟨1607681, by rfl⟩ : syracuseStep 2143575 = 3215363) B3215363
theorem B4069453 : Blo 2143435 4069453 := bbase (se 3 (by rfl) ⟨763022, by rfl⟩ : syracuseStep 4069453 = 1526045) (by norm_num)
theorem B5425937 : Blo 2143435 5425937 := bstep (se 2 (by rfl) ⟨2034726, by rfl⟩ : syracuseStep 5425937 = 4069453) B4069453
theorem B3617291 : Blo 2143435 3617291 := bstep (se 1 (by rfl) ⟨2712968, by rfl⟩ : syracuseStep 3617291 = 5425937) B5425937
theorem B2411527 : Blo 2143435 2411527 := bstep (se 1 (by rfl) ⟨1808645, by rfl⟩ : syracuseStep 2411527 = 3617291) B3617291
theorem B3215369 : Blo 2143435 3215369 := bstep (se 2 (by rfl) ⟨1205763, by rfl⟩ : syracuseStep 3215369 = 2411527) B2411527
theorem B2143579 : Blo 2143435 2143579 := bstep (se 1 (by rfl) ⟨1607684, by rfl⟩ : syracuseStep 2143579 = 3215369) B3215369
theorem B10851893 : Blo 2143435 10851893 := bbase (se 5 (by rfl) ⟨508682, by rfl⟩ : syracuseStep 10851893 = 1017365) (by norm_num)
theorem B7234595 : Blo 2143435 7234595 := bstep (se 1 (by rfl) ⟨5425946, by rfl⟩ : syracuseStep 7234595 = 10851893) B10851893
theorem B4823063 : Blo 2143435 4823063 := bstep (se 1 (by rfl) ⟨3617297, by rfl⟩ : syracuseStep 4823063 = 7234595) B7234595
theorem B3215375 : Blo 2143435 3215375 := bstep (se 1 (by rfl) ⟨2411531, by rfl⟩ : syracuseStep 3215375 = 4823063) B4823063
theorem B2143583 : Blo 2143435 2143583 := bstep (se 1 (by rfl) ⟨1607687, by rfl⟩ : syracuseStep 2143583 = 3215375) B3215375
theorem B3215381 : Blo 2143435 3215381 := bbase (se 6 (by rfl) ⟨75360, by rfl⟩ : syracuseStep 3215381 = 150721) (by norm_num)
theorem B2143587 : Blo 2143435 2143587 := bstep (se 1 (by rfl) ⟨1607690, by rfl⟩ : syracuseStep 2143587 = 3215381) B3215381
theorem B3716693 : Blo 2143435 3716693 := bbase (se 8 (by rfl) ⟨21777, by rfl⟩ : syracuseStep 3716693 = 43555) (by norm_num)
theorem B2477795 : Blo 2143435 2477795 := bstep (se 1 (by rfl) ⟨1858346, by rfl⟩ : syracuseStep 2477795 = 3716693) B3716693
theorem B26429813 : Blo 2143435 26429813 := bstep (se 5 (by rfl) ⟨1238897, by rfl⟩ : syracuseStep 26429813 = 2477795) B2477795
theorem B17619875 : Blo 2143435 17619875 := bstep (se 1 (by rfl) ⟨13214906, by rfl⟩ : syracuseStep 17619875 = 26429813) B26429813
theorem B11746583 : Blo 2143435 11746583 := bstep (se 1 (by rfl) ⟨8809937, by rfl⟩ : syracuseStep 11746583 = 17619875) B17619875
theorem B7831055 : Blo 2143435 7831055 := bstep (se 1 (by rfl) ⟨5873291, by rfl⟩ : syracuseStep 7831055 = 11746583) B11746583
theorem B5220703 : Blo 2143435 5220703 := bstep (se 1 (by rfl) ⟨3915527, by rfl⟩ : syracuseStep 5220703 = 7831055) B7831055
theorem B6960937 : Blo 2143435 6960937 := bstep (se 2 (by rfl) ⟨2610351, by rfl⟩ : syracuseStep 6960937 = 5220703) B5220703
theorem B9281249 : Blo 2143435 9281249 := bstep (se 2 (by rfl) ⟨3480468, by rfl⟩ : syracuseStep 9281249 = 6960937) B6960937
theorem B6187499 : Blo 2143435 6187499 := bstep (se 1 (by rfl) ⟨4640624, by rfl⟩ : syracuseStep 6187499 = 9281249) B9281249
theorem B4124999 : Blo 2143435 4124999 := bstep (se 1 (by rfl) ⟨3093749, by rfl⟩ : syracuseStep 4124999 = 6187499) B6187499
theorem B2749999 : Blo 2143435 2749999 := bstep (se 1 (by rfl) ⟨2062499, by rfl⟩ : syracuseStep 2749999 = 4124999) B4124999
theorem B3666665 : Blo 2143435 3666665 := bstep (se 2 (by rfl) ⟨1374999, by rfl⟩ : syracuseStep 3666665 = 2749999) B2749999
theorem B9777773 : Blo 2143435 9777773 := bstep (se 3 (by rfl) ⟨1833332, by rfl⟩ : syracuseStep 9777773 = 3666665) B3666665
theorem B6518515 : Blo 2143435 6518515 := bstep (se 1 (by rfl) ⟨4888886, by rfl⟩ : syracuseStep 6518515 = 9777773) B9777773
theorem B8691353 : Blo 2143435 8691353 := bstep (se 2 (by rfl) ⟨3259257, by rfl⟩ : syracuseStep 8691353 = 6518515) B6518515
theorem B5794235 : Blo 2143435 5794235 := bstep (se 1 (by rfl) ⟨4345676, by rfl⟩ : syracuseStep 5794235 = 8691353) B8691353
theorem B3862823 : Blo 2143435 3862823 := bstep (se 1 (by rfl) ⟨2897117, by rfl⟩ : syracuseStep 3862823 = 5794235) B5794235
theorem B10300861 : Blo 2143435 10300861 := bstep (se 3 (by rfl) ⟨1931411, by rfl⟩ : syracuseStep 10300861 = 3862823) B3862823
theorem B13734481 : Blo 2143435 13734481 := bstep (se 2 (by rfl) ⟨5150430, by rfl⟩ : syracuseStep 13734481 = 10300861) B10300861
theorem B18312641 : Blo 2143435 18312641 := bstep (se 2 (by rfl) ⟨6867240, by rfl⟩ : syracuseStep 18312641 = 13734481) B13734481
theorem B12208427 : Blo 2143435 12208427 := bstep (se 1 (by rfl) ⟨9156320, by rfl⟩ : syracuseStep 12208427 = 18312641) B18312641
theorem B8138951 : Blo 2143435 8138951 := bstep (se 1 (by rfl) ⟨6104213, by rfl⟩ : syracuseStep 8138951 = 12208427) B12208427
theorem B5425967 : Blo 2143435 5425967 := bstep (se 1 (by rfl) ⟨4069475, by rfl⟩ : syracuseStep 5425967 = 8138951) B8138951
theorem B3617311 : Blo 2143435 3617311 := bstep (se 1 (by rfl) ⟨2712983, by rfl⟩ : syracuseStep 3617311 = 5425967) B5425967
theorem B4823081 : Blo 2143435 4823081 := bstep (se 2 (by rfl) ⟨1808655, by rfl⟩ : syracuseStep 4823081 = 3617311) B3617311
theorem B3215387 : Blo 2143435 3215387 := bstep (se 1 (by rfl) ⟨2411540, by rfl⟩ : syracuseStep 3215387 = 4823081) B4823081
theorem B2143591 : Blo 2143435 2143591 := bstep (se 1 (by rfl) ⟨1607693, by rfl⟩ : syracuseStep 2143591 = 3215387) B3215387
theorem B2411545 : Blo 2143435 2411545 := bbase (se 2 (by rfl) ⟨904329, by rfl⟩ : syracuseStep 2411545 = 1808659) (by norm_num)
theorem B3215393 : Blo 2143435 3215393 := bstep (se 2 (by rfl) ⟨1205772, by rfl⟩ : syracuseStep 3215393 = 2411545) B2411545
theorem B2143595 : Blo 2143435 2143595 := bstep (se 1 (by rfl) ⟨1607696, by rfl⟩ : syracuseStep 2143595 = 3215393) B3215393
theorem B8138981 : Blo 2143435 8138981 := bbase (se 4 (by rfl) ⟨763029, by rfl⟩ : syracuseStep 8138981 = 1526059) (by norm_num)
theorem B5425987 : Blo 2143435 5425987 := bstep (se 1 (by rfl) ⟨4069490, by rfl⟩ : syracuseStep 5425987 = 8138981) B8138981
theorem B7234649 : Blo 2143435 7234649 := bstep (se 2 (by rfl) ⟨2712993, by rfl⟩ : syracuseStep 7234649 = 5425987) B5425987
theorem B4823099 : Blo 2143435 4823099 := bstep (se 1 (by rfl) ⟨3617324, by rfl⟩ : syracuseStep 4823099 = 7234649) B7234649
theorem B3215399 : Blo 2143435 3215399 := bstep (se 1 (by rfl) ⟨2411549, by rfl⟩ : syracuseStep 3215399 = 4823099) B4823099
theorem B2143599 : Blo 2143435 2143599 := bstep (se 1 (by rfl) ⟨1607699, by rfl⟩ : syracuseStep 2143599 = 3215399) B3215399
theorem B3215405 : Blo 2143435 3215405 := bbase (se 3 (by rfl) ⟨602888, by rfl⟩ : syracuseStep 3215405 = 1205777) (by norm_num)
theorem B2143603 : Blo 2143435 2143603 := bstep (se 1 (by rfl) ⟨1607702, by rfl⟩ : syracuseStep 2143603 = 3215405) B3215405
theorem B4823117 : Blo 2143435 4823117 := bbase (se 3 (by rfl) ⟨904334, by rfl⟩ : syracuseStep 4823117 = 1808669) (by norm_num)
theorem B3215411 : Blo 2143435 3215411 := bstep (se 1 (by rfl) ⟨2411558, by rfl⟩ : syracuseStep 3215411 = 4823117) B4823117
theorem B2143607 : Blo 2143435 2143607 := bstep (se 1 (by rfl) ⟨1607705, by rfl⟩ : syracuseStep 2143607 = 3215411) B3215411
theorem B2713009 : Blo 2143435 2713009 := bbase (se 2 (by rfl) ⟨1017378, by rfl⟩ : syracuseStep 2713009 = 2034757) (by norm_num)
theorem B3617345 : Blo 2143435 3617345 := bstep (se 2 (by rfl) ⟨1356504, by rfl⟩ : syracuseStep 3617345 = 2713009) B2713009
theorem B2411563 : Blo 2143435 2411563 := bstep (se 1 (by rfl) ⟨1808672, by rfl⟩ : syracuseStep 2411563 = 3617345) B3617345
theorem B3215417 : Blo 2143435 3215417 := bstep (se 2 (by rfl) ⟨1205781, by rfl⟩ : syracuseStep 3215417 = 2411563) B2411563
theorem B2143611 : Blo 2143435 2143611 := bstep (se 1 (by rfl) ⟨1607708, by rfl⟩ : syracuseStep 2143611 = 3215417) B3215417
theorem B6867317 : Blo 2143435 6867317 := bbase (se 5 (by rfl) ⟨321905, by rfl⟩ : syracuseStep 6867317 = 643811) (by norm_num)
theorem B4578211 : Blo 2143435 4578211 := bstep (se 1 (by rfl) ⟨3433658, by rfl⟩ : syracuseStep 4578211 = 6867317) B6867317
theorem B24417125 : Blo 2143435 24417125 := bstep (se 4 (by rfl) ⟨2289105, by rfl⟩ : syracuseStep 24417125 = 4578211) B4578211
theorem B16278083 : Blo 2143435 16278083 := bstep (se 1 (by rfl) ⟨12208562, by rfl⟩ : syracuseStep 16278083 = 24417125) B24417125
theorem B10852055 : Blo 2143435 10852055 := bstep (se 1 (by rfl) ⟨8139041, by rfl⟩ : syracuseStep 10852055 = 16278083) B16278083
theorem B7234703 : Blo 2143435 7234703 := bstep (se 1 (by rfl) ⟨5426027, by rfl⟩ : syracuseStep 7234703 = 10852055) B10852055
theorem B4823135 : Blo 2143435 4823135 := bstep (se 1 (by rfl) ⟨3617351, by rfl⟩ : syracuseStep 4823135 = 7234703) B7234703
theorem B3215423 : Blo 2143435 3215423 := bstep (se 1 (by rfl) ⟨2411567, by rfl⟩ : syracuseStep 3215423 = 4823135) B4823135
theorem B2143615 : Blo 2143435 2143615 := bstep (se 1 (by rfl) ⟨1607711, by rfl⟩ : syracuseStep 2143615 = 3215423) B3215423
theorem B3215429 : Blo 2143435 3215429 := bbase (se 4 (by rfl) ⟨301446, by rfl⟩ : syracuseStep 3215429 = 602893) (by norm_num)
theorem B2143619 : Blo 2143435 2143619 := bstep (se 1 (by rfl) ⟨1607714, by rfl⟩ : syracuseStep 2143619 = 3215429) B3215429
theorem B3617365 : Blo 2143435 3617365 := bbase (se 8 (by rfl) ⟨21195, by rfl⟩ : syracuseStep 3617365 = 42391) (by norm_num)
theorem B4823153 : Blo 2143435 4823153 := bstep (se 2 (by rfl) ⟨1808682, by rfl⟩ : syracuseStep 4823153 = 3617365) B3617365
theorem B3215435 : Blo 2143435 3215435 := bstep (se 1 (by rfl) ⟨2411576, by rfl⟩ : syracuseStep 3215435 = 4823153) B4823153
theorem B2143623 : Blo 2143435 2143623 := bstep (se 1 (by rfl) ⟨1607717, by rfl⟩ : syracuseStep 2143623 = 3215435) B3215435
theorem B2411581 : Blo 2143435 2411581 := bbase (se 3 (by rfl) ⟨452171, by rfl⟩ : syracuseStep 2411581 = 904343) (by norm_num)
theorem B3215441 : Blo 2143435 3215441 := bstep (se 2 (by rfl) ⟨1205790, by rfl⟩ : syracuseStep 3215441 = 2411581) B2411581
theorem B2143627 : Blo 2143435 2143627 := bstep (se 1 (by rfl) ⟨1607720, by rfl⟩ : syracuseStep 2143627 = 3215441) B3215441
theorem B7234757 : Blo 2143435 7234757 := bbase (se 4 (by rfl) ⟨678258, by rfl⟩ : syracuseStep 7234757 = 1356517) (by norm_num)
theorem B4823171 : Blo 2143435 4823171 := bstep (se 1 (by rfl) ⟨3617378, by rfl⟩ : syracuseStep 4823171 = 7234757) B7234757
theorem B3215447 : Blo 2143435 3215447 := bstep (se 1 (by rfl) ⟨2411585, by rfl⟩ : syracuseStep 3215447 = 4823171) B4823171
theorem B2143631 : Blo 2143435 2143631 := bstep (se 1 (by rfl) ⟨1607723, by rfl⟩ : syracuseStep 2143631 = 3215447) B3215447
theorem B3215453 : Blo 2143435 3215453 := bbase (se 3 (by rfl) ⟨602897, by rfl⟩ : syracuseStep 3215453 = 1205795) (by norm_num)
theorem B2143635 : Blo 2143435 2143635 := bstep (se 1 (by rfl) ⟨1607726, by rfl⟩ : syracuseStep 2143635 = 3215453) B3215453
theorem B4823189 : Blo 2143435 4823189 := bbase (se 6 (by rfl) ⟨113043, by rfl⟩ : syracuseStep 4823189 = 226087) (by norm_num)
theorem B3215459 : Blo 2143435 3215459 := bstep (se 1 (by rfl) ⟨2411594, by rfl⟩ : syracuseStep 3215459 = 4823189) B4823189
theorem B2143639 : Blo 2143435 2143639 := bstep (se 1 (by rfl) ⟨1607729, by rfl⟩ : syracuseStep 2143639 = 3215459) B3215459
theorem B3052181 : Blo 2143435 3052181 := bbase (se 6 (by rfl) ⟨71535, by rfl⟩ : syracuseStep 3052181 = 143071) (by norm_num)
theorem B8139149 : Blo 2143435 8139149 := bstep (se 3 (by rfl) ⟨1526090, by rfl⟩ : syracuseStep 8139149 = 3052181) B3052181
theorem B5426099 : Blo 2143435 5426099 := bstep (se 1 (by rfl) ⟨4069574, by rfl⟩ : syracuseStep 5426099 = 8139149) B8139149
theorem B3617399 : Blo 2143435 3617399 := bstep (se 1 (by rfl) ⟨2713049, by rfl⟩ : syracuseStep 3617399 = 5426099) B5426099
theorem B2411599 : Blo 2143435 2411599 := bstep (se 1 (by rfl) ⟨1808699, by rfl⟩ : syracuseStep 2411599 = 3617399) B3617399
theorem B3215465 : Blo 2143435 3215465 := bstep (se 2 (by rfl) ⟨1205799, by rfl⟩ : syracuseStep 3215465 = 2411599) B2411599
theorem B2143643 : Blo 2143435 2143643 := bstep (se 1 (by rfl) ⟨1607732, by rfl⟩ : syracuseStep 2143643 = 3215465) B3215465
theorem B17383157 : Blo 2143435 17383157 := bbase (se 5 (by rfl) ⟨814835, by rfl⟩ : syracuseStep 17383157 = 1629671) (by norm_num)
theorem B11588771 : Blo 2143435 11588771 := bstep (se 1 (by rfl) ⟨8691578, by rfl⟩ : syracuseStep 11588771 = 17383157) B17383157
theorem B30903389 : Blo 2143435 30903389 := bstep (se 3 (by rfl) ⟨5794385, by rfl⟩ : syracuseStep 30903389 = 11588771) B11588771
theorem B20602259 : Blo 2143435 20602259 := bstep (se 1 (by rfl) ⟨15451694, by rfl⟩ : syracuseStep 20602259 = 30903389) B30903389
theorem B13734839 : Blo 2143435 13734839 := bstep (se 1 (by rfl) ⟨10301129, by rfl⟩ : syracuseStep 13734839 = 20602259) B20602259
theorem B9156559 : Blo 2143435 9156559 := bstep (se 1 (by rfl) ⟨6867419, by rfl⟩ : syracuseStep 9156559 = 13734839) B13734839
theorem B12208745 : Blo 2143435 12208745 := bstep (se 2 (by rfl) ⟨4578279, by rfl⟩ : syracuseStep 12208745 = 9156559) B9156559
theorem B8139163 : Blo 2143435 8139163 := bstep (se 1 (by rfl) ⟨6104372, by rfl⟩ : syracuseStep 8139163 = 12208745) B12208745
theorem B10852217 : Blo 2143435 10852217 := bstep (se 2 (by rfl) ⟨4069581, by rfl⟩ : syracuseStep 10852217 = 8139163) B8139163
theorem B7234811 : Blo 2143435 7234811 := bstep (se 1 (by rfl) ⟨5426108, by rfl⟩ : syracuseStep 7234811 = 10852217) B10852217
theorem B4823207 : Blo 2143435 4823207 := bstep (se 1 (by rfl) ⟨3617405, by rfl⟩ : syracuseStep 4823207 = 7234811) B7234811
theorem B3215471 : Blo 2143435 3215471 := bstep (se 1 (by rfl) ⟨2411603, by rfl⟩ : syracuseStep 3215471 = 4823207) B4823207
theorem B2143647 : Blo 2143435 2143647 := bstep (se 1 (by rfl) ⟨1607735, by rfl⟩ : syracuseStep 2143647 = 3215471) B3215471
theorem B3215477 : Blo 2143435 3215477 := bbase (se 5 (by rfl) ⟨150725, by rfl⟩ : syracuseStep 3215477 = 301451) (by norm_num)
theorem B2143651 : Blo 2143435 2143651 := bstep (se 1 (by rfl) ⟨1607738, by rfl⟩ : syracuseStep 2143651 = 3215477) B3215477
theorem B4069597 : Blo 2143435 4069597 := bbase (se 3 (by rfl) ⟨763049, by rfl⟩ : syracuseStep 4069597 = 1526099) (by norm_num)
theorem B5426129 : Blo 2143435 5426129 := bstep (se 2 (by rfl) ⟨2034798, by rfl⟩ : syracuseStep 5426129 = 4069597) B4069597
theorem B3617419 : Blo 2143435 3617419 := bstep (se 1 (by rfl) ⟨2713064, by rfl⟩ : syracuseStep 3617419 = 5426129) B5426129
theorem B4823225 : Blo 2143435 4823225 := bstep (se 2 (by rfl) ⟨1808709, by rfl⟩ : syracuseStep 4823225 = 3617419) B3617419
theorem B3215483 : Blo 2143435 3215483 := bstep (se 1 (by rfl) ⟨2411612, by rfl⟩ : syracuseStep 3215483 = 4823225) B4823225
theorem B2143655 : Blo 2143435 2143655 := bstep (se 1 (by rfl) ⟨1607741, by rfl⟩ : syracuseStep 2143655 = 3215483) B3215483
theorem B2411617 : Blo 2143435 2411617 := bbase (se 2 (by rfl) ⟨904356, by rfl⟩ : syracuseStep 2411617 = 1808713) (by norm_num)
theorem B3215489 : Blo 2143435 3215489 := bstep (se 2 (by rfl) ⟨1205808, by rfl⟩ : syracuseStep 3215489 = 2411617) B2411617
theorem B2143659 : Blo 2143435 2143659 := bstep (se 1 (by rfl) ⟨1607744, by rfl⟩ : syracuseStep 2143659 = 3215489) B3215489
theorem B5426149 : Blo 2143435 5426149 := bbase (se 4 (by rfl) ⟨508701, by rfl⟩ : syracuseStep 5426149 = 1017403) (by norm_num)
theorem B7234865 : Blo 2143435 7234865 := bstep (se 2 (by rfl) ⟨2713074, by rfl⟩ : syracuseStep 7234865 = 5426149) B5426149
theorem B4823243 : Blo 2143435 4823243 := bstep (se 1 (by rfl) ⟨3617432, by rfl⟩ : syracuseStep 4823243 = 7234865) B7234865
theorem B3215495 : Blo 2143435 3215495 := bstep (se 1 (by rfl) ⟨2411621, by rfl⟩ : syracuseStep 3215495 = 4823243) B4823243
theorem B2143663 : Blo 2143435 2143663 := bstep (se 1 (by rfl) ⟨1607747, by rfl⟩ : syracuseStep 2143663 = 3215495) B3215495
theorem B3215501 : Blo 2143435 3215501 := bbase (se 3 (by rfl) ⟨602906, by rfl⟩ : syracuseStep 3215501 = 1205813) (by norm_num)
theorem B2143667 : Blo 2143435 2143667 := bstep (se 1 (by rfl) ⟨1607750, by rfl⟩ : syracuseStep 2143667 = 3215501) B3215501
theorem B4823261 : Blo 2143435 4823261 := bbase (se 3 (by rfl) ⟨904361, by rfl⟩ : syracuseStep 4823261 = 1808723) (by norm_num)
theorem B3215507 : Blo 2143435 3215507 := bstep (se 1 (by rfl) ⟨2411630, by rfl⟩ : syracuseStep 3215507 = 4823261) B4823261
theorem B2143671 : Blo 2143435 2143671 := bstep (se 1 (by rfl) ⟨1607753, by rfl⟩ : syracuseStep 2143671 = 3215507) B3215507
theorem B3617453 : Blo 2143435 3617453 := bbase (se 3 (by rfl) ⟨678272, by rfl⟩ : syracuseStep 3617453 = 1356545) (by norm_num)
theorem B2411635 : Blo 2143435 2411635 := bstep (se 1 (by rfl) ⟨1808726, by rfl⟩ : syracuseStep 2411635 = 3617453) B3617453
theorem B3215513 : Blo 2143435 3215513 := bstep (se 2 (by rfl) ⟨1205817, by rfl⟩ : syracuseStep 3215513 = 2411635) B2411635
theorem B2143675 : Blo 2143435 2143675 := bstep (se 1 (by rfl) ⟨1607756, by rfl⟩ : syracuseStep 2143675 = 3215513) B3215513
theorem B2610457 : Blo 2143435 2610457 := bbase (se 2 (by rfl) ⟨978921, by rfl⟩ : syracuseStep 2610457 = 1957843) (by norm_num)
theorem B13922437 : Blo 2143435 13922437 := bstep (se 4 (by rfl) ⟨1305228, by rfl⟩ : syracuseStep 13922437 = 2610457) B2610457
theorem B18563249 : Blo 2143435 18563249 := bstep (se 2 (by rfl) ⟨6961218, by rfl⟩ : syracuseStep 18563249 = 13922437) B13922437
theorem B12375499 : Blo 2143435 12375499 := bstep (se 1 (by rfl) ⟨9281624, by rfl⟩ : syracuseStep 12375499 = 18563249) B18563249
theorem B16500665 : Blo 2143435 16500665 := bstep (se 2 (by rfl) ⟨6187749, by rfl⟩ : syracuseStep 16500665 = 12375499) B12375499
theorem B11000443 : Blo 2143435 11000443 := bstep (se 1 (by rfl) ⟨8250332, by rfl⟩ : syracuseStep 11000443 = 16500665) B16500665
theorem B14667257 : Blo 2143435 14667257 := bstep (se 2 (by rfl) ⟨5500221, by rfl⟩ : syracuseStep 14667257 = 11000443) B11000443
theorem B39112685 : Blo 2143435 39112685 := bstep (se 3 (by rfl) ⟨7333628, by rfl⟩ : syracuseStep 39112685 = 14667257) B14667257
theorem B26075123 : Blo 2143435 26075123 := bstep (se 1 (by rfl) ⟨19556342, by rfl⟩ : syracuseStep 26075123 = 39112685) B39112685
theorem B17383415 : Blo 2143435 17383415 := bstep (se 1 (by rfl) ⟨13037561, by rfl⟩ : syracuseStep 17383415 = 26075123) B26075123
theorem B46355773 : Blo 2143435 46355773 := bstep (se 3 (by rfl) ⟨8691707, by rfl⟩ : syracuseStep 46355773 = 17383415) B17383415
theorem B61807697 : Blo 2143435 61807697 := bstep (se 2 (by rfl) ⟨23177886, by rfl⟩ : syracuseStep 61807697 = 46355773) B46355773
theorem B41205131 : Blo 2143435 41205131 := bstep (se 1 (by rfl) ⟨30903848, by rfl⟩ : syracuseStep 41205131 = 61807697) B61807697
theorem B27470087 : Blo 2143435 27470087 := bstep (se 1 (by rfl) ⟨20602565, by rfl⟩ : syracuseStep 27470087 = 41205131) B41205131
theorem B18313391 : Blo 2143435 18313391 := bstep (se 1 (by rfl) ⟨13735043, by rfl⟩ : syracuseStep 18313391 = 27470087) B27470087
theorem B12208927 : Blo 2143435 12208927 := bstep (se 1 (by rfl) ⟨9156695, by rfl⟩ : syracuseStep 12208927 = 18313391) B18313391
theorem B16278569 : Blo 2143435 16278569 := bstep (se 2 (by rfl) ⟨6104463, by rfl⟩ : syracuseStep 16278569 = 12208927) B12208927
theorem B10852379 : Blo 2143435 10852379 := bstep (se 1 (by rfl) ⟨8139284, by rfl⟩ : syracuseStep 10852379 = 16278569) B16278569
theorem B7234919 : Blo 2143435 7234919 := bstep (se 1 (by rfl) ⟨5426189, by rfl⟩ : syracuseStep 7234919 = 10852379) B10852379
theorem B4823279 : Blo 2143435 4823279 := bstep (se 1 (by rfl) ⟨3617459, by rfl⟩ : syracuseStep 4823279 = 7234919) B7234919
theorem B3215519 : Blo 2143435 3215519 := bstep (se 1 (by rfl) ⟨2411639, by rfl⟩ : syracuseStep 3215519 = 4823279) B4823279
theorem B2143679 : Blo 2143435 2143679 := bstep (se 1 (by rfl) ⟨1607759, by rfl⟩ : syracuseStep 2143679 = 3215519) B3215519
theorem B3215525 : Blo 2143435 3215525 := bbase (se 4 (by rfl) ⟨301455, by rfl⟩ : syracuseStep 3215525 = 602911) (by norm_num)
theorem B2143683 : Blo 2143435 2143683 := bstep (se 1 (by rfl) ⟨1607762, by rfl⟩ : syracuseStep 2143683 = 3215525) B3215525
theorem B2713105 : Blo 2143435 2713105 := bbase (se 2 (by rfl) ⟨1017414, by rfl⟩ : syracuseStep 2713105 = 2034829) (by norm_num)
theorem B3617473 : Blo 2143435 3617473 := bstep (se 2 (by rfl) ⟨1356552, by rfl⟩ : syracuseStep 3617473 = 2713105) B2713105
theorem B4823297 : Blo 2143435 4823297 := bstep (se 2 (by rfl) ⟨1808736, by rfl⟩ : syracuseStep 4823297 = 3617473) B3617473
theorem B3215531 : Blo 2143435 3215531 := bstep (se 1 (by rfl) ⟨2411648, by rfl⟩ : syracuseStep 3215531 = 4823297) B4823297
theorem B2143687 : Blo 2143435 2143687 := bstep (se 1 (by rfl) ⟨1607765, by rfl⟩ : syracuseStep 2143687 = 3215531) B3215531
theorem B2411653 : Blo 2143435 2411653 := bbase (se 4 (by rfl) ⟨226092, by rfl⟩ : syracuseStep 2411653 = 452185) (by norm_num)
theorem B3215537 : Blo 2143435 3215537 := bstep (se 2 (by rfl) ⟨1205826, by rfl⟩ : syracuseStep 3215537 = 2411653) B2411653
theorem B2143691 : Blo 2143435 2143691 := bstep (se 1 (by rfl) ⟨1607768, by rfl⟩ : syracuseStep 2143691 = 3215537) B3215537
theorem B5794517 : Blo 2143435 5794517 := bbase (se 7 (by rfl) ⟨67904, by rfl⟩ : syracuseStep 5794517 = 135809) (by norm_num)
theorem B15452045 : Blo 2143435 15452045 := bstep (se 3 (by rfl) ⟨2897258, by rfl⟩ : syracuseStep 15452045 = 5794517) B5794517
theorem B10301363 : Blo 2143435 10301363 := bstep (se 1 (by rfl) ⟨7726022, by rfl⟩ : syracuseStep 10301363 = 15452045) B15452045
theorem B6867575 : Blo 2143435 6867575 := bstep (se 1 (by rfl) ⟨5150681, by rfl⟩ : syracuseStep 6867575 = 10301363) B10301363
theorem B4578383 : Blo 2143435 4578383 := bstep (se 1 (by rfl) ⟨3433787, by rfl⟩ : syracuseStep 4578383 = 6867575) B6867575
theorem B3052255 : Blo 2143435 3052255 := bstep (se 1 (by rfl) ⟨2289191, by rfl⟩ : syracuseStep 3052255 = 4578383) B4578383
theorem B4069673 : Blo 2143435 4069673 := bstep (se 2 (by rfl) ⟨1526127, by rfl⟩ : syracuseStep 4069673 = 3052255) B3052255
theorem B2713115 : Blo 2143435 2713115 := bstep (se 1 (by rfl) ⟨2034836, by rfl⟩ : syracuseStep 2713115 = 4069673) B4069673
theorem B7234973 : Blo 2143435 7234973 := bstep (se 3 (by rfl) ⟨1356557, by rfl⟩ : syracuseStep 7234973 = 2713115) B2713115
theorem B4823315 : Blo 2143435 4823315 := bstep (se 1 (by rfl) ⟨3617486, by rfl⟩ : syracuseStep 4823315 = 7234973) B7234973
theorem B3215543 : Blo 2143435 3215543 := bstep (se 1 (by rfl) ⟨2411657, by rfl⟩ : syracuseStep 3215543 = 4823315) B4823315
theorem B2143695 : Blo 2143435 2143695 := bstep (se 1 (by rfl) ⟨1607771, by rfl⟩ : syracuseStep 2143695 = 3215543) B3215543
theorem B3215549 : Blo 2143435 3215549 := bbase (se 3 (by rfl) ⟨602915, by rfl⟩ : syracuseStep 3215549 = 1205831) (by norm_num)
theorem B2143699 : Blo 2143435 2143699 := bstep (se 1 (by rfl) ⟨1607774, by rfl⟩ : syracuseStep 2143699 = 3215549) B3215549
theorem B4823333 : Blo 2143435 4823333 := bbase (se 4 (by rfl) ⟨452187, by rfl⟩ : syracuseStep 4823333 = 904375) (by norm_num)
theorem B3215555 : Blo 2143435 3215555 := bstep (se 1 (by rfl) ⟨2411666, by rfl⟩ : syracuseStep 3215555 = 4823333) B4823333
theorem B2143703 : Blo 2143435 2143703 := bstep (se 1 (by rfl) ⟨1607777, by rfl⟩ : syracuseStep 2143703 = 3215555) B3215555
theorem B5426261 : Blo 2143435 5426261 := bbase (se 8 (by rfl) ⟨31794, by rfl⟩ : syracuseStep 5426261 = 63589) (by norm_num)
theorem B3617507 : Blo 2143435 3617507 := bstep (se 1 (by rfl) ⟨2713130, by rfl⟩ : syracuseStep 3617507 = 5426261) B5426261
theorem B2411671 : Blo 2143435 2411671 := bstep (se 1 (by rfl) ⟨1808753, by rfl⟩ : syracuseStep 2411671 = 3617507) B3617507
theorem B3215561 : Blo 2143435 3215561 := bstep (se 2 (by rfl) ⟨1205835, by rfl⟩ : syracuseStep 3215561 = 2411671) B2411671
theorem B2143707 : Blo 2143435 2143707 := bstep (se 1 (by rfl) ⟨1607780, by rfl⟩ : syracuseStep 2143707 = 3215561) B3215561
theorem B4405213 : Blo 2143435 4405213 := bbase (se 3 (by rfl) ⟨825977, by rfl⟩ : syracuseStep 4405213 = 1651955) (by norm_num)
theorem B5873617 : Blo 2143435 5873617 := bstep (se 2 (by rfl) ⟨2202606, by rfl⟩ : syracuseStep 5873617 = 4405213) B4405213
theorem B31325957 : Blo 2143435 31325957 := bstep (se 4 (by rfl) ⟨2936808, by rfl⟩ : syracuseStep 31325957 = 5873617) B5873617
theorem B20883971 : Blo 2143435 20883971 := bstep (se 1 (by rfl) ⟨15662978, by rfl⟩ : syracuseStep 20883971 = 31325957) B31325957
theorem B13922647 : Blo 2143435 13922647 := bstep (se 1 (by rfl) ⟨10441985, by rfl⟩ : syracuseStep 13922647 = 20883971) B20883971
theorem B297016469 : Blo 2143435 297016469 := bstep (se 6 (by rfl) ⟨6961323, by rfl⟩ : syracuseStep 297016469 = 13922647) B13922647
theorem B198010979 : Blo 2143435 198010979 := bstep (se 1 (by rfl) ⟨148508234, by rfl⟩ : syracuseStep 198010979 = 297016469) B297016469
theorem B132007319 : Blo 2143435 132007319 := bstep (se 1 (by rfl) ⟨99005489, by rfl⟩ : syracuseStep 132007319 = 198010979) B198010979
theorem B88004879 : Blo 2143435 88004879 := bstep (se 1 (by rfl) ⟨66003659, by rfl⟩ : syracuseStep 88004879 = 132007319) B132007319
theorem B58669919 : Blo 2143435 58669919 := bstep (se 1 (by rfl) ⟨44002439, by rfl⟩ : syracuseStep 58669919 = 88004879) B88004879
theorem B39113279 : Blo 2143435 39113279 := bstep (se 1 (by rfl) ⟨29334959, by rfl⟩ : syracuseStep 39113279 = 58669919) B58669919
theorem B26075519 : Blo 2143435 26075519 := bstep (se 1 (by rfl) ⟨19556639, by rfl⟩ : syracuseStep 26075519 = 39113279) B39113279
theorem B17383679 : Blo 2143435 17383679 := bstep (se 1 (by rfl) ⟨13037759, by rfl⟩ : syracuseStep 17383679 = 26075519) B26075519
theorem B11589119 : Blo 2143435 11589119 := bstep (se 1 (by rfl) ⟨8691839, by rfl⟩ : syracuseStep 11589119 = 17383679) B17383679
theorem B7726079 : Blo 2143435 7726079 := bstep (se 1 (by rfl) ⟨5794559, by rfl⟩ : syracuseStep 7726079 = 11589119) B11589119
theorem B5150719 : Blo 2143435 5150719 := bstep (se 1 (by rfl) ⟨3863039, by rfl⟩ : syracuseStep 5150719 = 7726079) B7726079
theorem B6867625 : Blo 2143435 6867625 := bstep (se 2 (by rfl) ⟨2575359, by rfl⟩ : syracuseStep 6867625 = 5150719) B5150719
theorem B9156833 : Blo 2143435 9156833 := bstep (se 2 (by rfl) ⟨3433812, by rfl⟩ : syracuseStep 9156833 = 6867625) B6867625
theorem B6104555 : Blo 2143435 6104555 := bstep (se 1 (by rfl) ⟨4578416, by rfl⟩ : syracuseStep 6104555 = 9156833) B9156833
theorem B4069703 : Blo 2143435 4069703 := bstep (se 1 (by rfl) ⟨3052277, by rfl⟩ : syracuseStep 4069703 = 6104555) B6104555
theorem B10852541 : Blo 2143435 10852541 := bstep (se 3 (by rfl) ⟨2034851, by rfl⟩ : syracuseStep 10852541 = 4069703) B4069703
theorem B7235027 : Blo 2143435 7235027 := bstep (se 1 (by rfl) ⟨5426270, by rfl⟩ : syracuseStep 7235027 = 10852541) B10852541
theorem B4823351 : Blo 2143435 4823351 := bstep (se 1 (by rfl) ⟨3617513, by rfl⟩ : syracuseStep 4823351 = 7235027) B7235027
theorem B3215567 : Blo 2143435 3215567 := bstep (se 1 (by rfl) ⟨2411675, by rfl⟩ : syracuseStep 3215567 = 4823351) B4823351
theorem B2143711 : Blo 2143435 2143711 := bstep (se 1 (by rfl) ⟨1607783, by rfl⟩ : syracuseStep 2143711 = 3215567) B3215567
theorem B3215573 : Blo 2143435 3215573 := bbase (se 7 (by rfl) ⟨37682, by rfl⟩ : syracuseStep 3215573 = 75365) (by norm_num)
theorem B2143715 : Blo 2143435 2143715 := bstep (se 1 (by rfl) ⟨1607786, by rfl⟩ : syracuseStep 2143715 = 3215573) B3215573
theorem B2289217 : Blo 2143435 2289217 := bbase (se 2 (by rfl) ⟨858456, by rfl⟩ : syracuseStep 2289217 = 1716913) (by norm_num)
theorem B3052289 : Blo 2143435 3052289 := bstep (se 2 (by rfl) ⟨1144608, by rfl⟩ : syracuseStep 3052289 = 2289217) B2289217
theorem B8139437 : Blo 2143435 8139437 := bstep (se 3 (by rfl) ⟨1526144, by rfl⟩ : syracuseStep 8139437 = 3052289) B3052289
theorem B5426291 : Blo 2143435 5426291 := bstep (se 1 (by rfl) ⟨4069718, by rfl⟩ : syracuseStep 5426291 = 8139437) B8139437
theorem B3617527 : Blo 2143435 3617527 := bstep (se 1 (by rfl) ⟨2713145, by rfl⟩ : syracuseStep 3617527 = 5426291) B5426291
theorem B4823369 : Blo 2143435 4823369 := bstep (se 2 (by rfl) ⟨1808763, by rfl⟩ : syracuseStep 4823369 = 3617527) B3617527
theorem B3215579 : Blo 2143435 3215579 := bstep (se 1 (by rfl) ⟨2411684, by rfl⟩ : syracuseStep 3215579 = 4823369) B4823369
theorem B2143719 : Blo 2143435 2143719 := bstep (se 1 (by rfl) ⟨1607789, by rfl⟩ : syracuseStep 2143719 = 3215579) B3215579
theorem B2411689 : Blo 2143435 2411689 := bbase (se 2 (by rfl) ⟨904383, by rfl⟩ : syracuseStep 2411689 = 1808767) (by norm_num)
theorem B3215585 : Blo 2143435 3215585 := bstep (se 2 (by rfl) ⟨1205844, by rfl⟩ : syracuseStep 3215585 = 2411689) B2411689
theorem B2143723 : Blo 2143435 2143723 := bstep (se 1 (by rfl) ⟨1607792, by rfl⟩ : syracuseStep 2143723 = 3215585) B3215585
theorem B9156901 : Blo 2143435 9156901 := bbase (se 4 (by rfl) ⟨858459, by rfl⟩ : syracuseStep 9156901 = 1716919) (by norm_num)
theorem B12209201 : Blo 2143435 12209201 := bstep (se 2 (by rfl) ⟨4578450, by rfl⟩ : syracuseStep 12209201 = 9156901) B9156901
theorem B8139467 : Blo 2143435 8139467 := bstep (se 1 (by rfl) ⟨6104600, by rfl⟩ : syracuseStep 8139467 = 12209201) B12209201
theorem B5426311 : Blo 2143435 5426311 := bstep (se 1 (by rfl) ⟨4069733, by rfl⟩ : syracuseStep 5426311 = 8139467) B8139467
theorem B7235081 : Blo 2143435 7235081 := bstep (se 2 (by rfl) ⟨2713155, by rfl⟩ : syracuseStep 7235081 = 5426311) B5426311
theorem B4823387 : Blo 2143435 4823387 := bstep (se 1 (by rfl) ⟨3617540, by rfl⟩ : syracuseStep 4823387 = 7235081) B7235081
theorem B3215591 : Blo 2143435 3215591 := bstep (se 1 (by rfl) ⟨2411693, by rfl⟩ : syracuseStep 3215591 = 4823387) B4823387
theorem B2143727 : Blo 2143435 2143727 := bstep (se 1 (by rfl) ⟨1607795, by rfl⟩ : syracuseStep 2143727 = 3215591) B3215591
theorem B3215597 : Blo 2143435 3215597 := bbase (se 3 (by rfl) ⟨602924, by rfl⟩ : syracuseStep 3215597 = 1205849) (by norm_num)
theorem B2143731 : Blo 2143435 2143731 := bstep (se 1 (by rfl) ⟨1607798, by rfl⟩ : syracuseStep 2143731 = 3215597) B3215597
theorem B4823405 : Blo 2143435 4823405 := bbase (se 3 (by rfl) ⟨904388, by rfl⟩ : syracuseStep 4823405 = 1808777) (by norm_num)
theorem B3215603 : Blo 2143435 3215603 := bstep (se 1 (by rfl) ⟨2411702, by rfl⟩ : syracuseStep 3215603 = 4823405) B4823405
theorem B2143735 : Blo 2143435 2143735 := bstep (se 1 (by rfl) ⟨1607801, by rfl⟩ : syracuseStep 2143735 = 3215603) B3215603
theorem B4069757 : Blo 2143435 4069757 := bbase (se 3 (by rfl) ⟨763079, by rfl⟩ : syracuseStep 4069757 = 1526159) (by norm_num)
theorem B2713171 : Blo 2143435 2713171 := bstep (se 1 (by rfl) ⟨2034878, by rfl⟩ : syracuseStep 2713171 = 4069757) B4069757
theorem B3617561 : Blo 2143435 3617561 := bstep (se 2 (by rfl) ⟨1356585, by rfl⟩ : syracuseStep 3617561 = 2713171) B2713171
theorem B2411707 : Blo 2143435 2411707 := bstep (se 1 (by rfl) ⟨1808780, by rfl⟩ : syracuseStep 2411707 = 3617561) B3617561
theorem B3215609 : Blo 2143435 3215609 := bstep (se 2 (by rfl) ⟨1205853, by rfl⟩ : syracuseStep 3215609 = 2411707) B2411707
theorem B2143739 : Blo 2143435 2143739 := bstep (se 1 (by rfl) ⟨1607804, by rfl⟩ : syracuseStep 2143739 = 3215609) B3215609
theorem B5794645 : Blo 2143435 5794645 := bbase (se 9 (by rfl) ⟨16976, by rfl⟩ : syracuseStep 5794645 = 33953) (by norm_num)
theorem B7726193 : Blo 2143435 7726193 := bstep (se 2 (by rfl) ⟨2897322, by rfl⟩ : syracuseStep 7726193 = 5794645) B5794645
theorem B5150795 : Blo 2143435 5150795 := bstep (se 1 (by rfl) ⟨3863096, by rfl⟩ : syracuseStep 5150795 = 7726193) B7726193
theorem B54941813 : Blo 2143435 54941813 := bstep (se 5 (by rfl) ⟨2575397, by rfl⟩ : syracuseStep 54941813 = 5150795) B5150795
theorem B36627875 : Blo 2143435 36627875 := bstep (se 1 (by rfl) ⟨27470906, by rfl⟩ : syracuseStep 36627875 = 54941813) B54941813
theorem B24418583 : Blo 2143435 24418583 := bstep (se 1 (by rfl) ⟨18313937, by rfl⟩ : syracuseStep 24418583 = 36627875) B36627875
theorem B16279055 : Blo 2143435 16279055 := bstep (se 1 (by rfl) ⟨12209291, by rfl⟩ : syracuseStep 16279055 = 24418583) B24418583
theorem B10852703 : Blo 2143435 10852703 := bstep (se 1 (by rfl) ⟨8139527, by rfl⟩ : syracuseStep 10852703 = 16279055) B16279055
theorem B7235135 : Blo 2143435 7235135 := bstep (se 1 (by rfl) ⟨5426351, by rfl⟩ : syracuseStep 7235135 = 10852703) B10852703
theorem B4823423 : Blo 2143435 4823423 := bstep (se 1 (by rfl) ⟨3617567, by rfl⟩ : syracuseStep 4823423 = 7235135) B7235135
theorem B3215615 : Blo 2143435 3215615 := bstep (se 1 (by rfl) ⟨2411711, by rfl⟩ : syracuseStep 3215615 = 4823423) B4823423
theorem B2143743 : Blo 2143435 2143743 := bstep (se 1 (by rfl) ⟨1607807, by rfl⟩ : syracuseStep 2143743 = 3215615) B3215615
theorem B3215621 : Blo 2143435 3215621 := bbase (se 4 (by rfl) ⟨301464, by rfl⟩ : syracuseStep 3215621 = 602929) (by norm_num)
theorem B2143747 : Blo 2143435 2143747 := bstep (se 1 (by rfl) ⟨1607810, by rfl⟩ : syracuseStep 2143747 = 3215621) B3215621
theorem B3617581 : Blo 2143435 3617581 := bbase (se 3 (by rfl) ⟨678296, by rfl⟩ : syracuseStep 3617581 = 1356593) (by norm_num)
theorem B4823441 : Blo 2143435 4823441 := bstep (se 2 (by rfl) ⟨1808790, by rfl⟩ : syracuseStep 4823441 = 3617581) B3617581
theorem B3215627 : Blo 2143435 3215627 := bstep (se 1 (by rfl) ⟨2411720, by rfl⟩ : syracuseStep 3215627 = 4823441) B4823441
theorem B2143751 : Blo 2143435 2143751 := bstep (se 1 (by rfl) ⟨1607813, by rfl⟩ : syracuseStep 2143751 = 3215627) B3215627
theorem B2411725 : Blo 2143435 2411725 := bbase (se 3 (by rfl) ⟨452198, by rfl⟩ : syracuseStep 2411725 = 904397) (by norm_num)
theorem B3215633 : Blo 2143435 3215633 := bstep (se 2 (by rfl) ⟨1205862, by rfl⟩ : syracuseStep 3215633 = 2411725) B2411725
theorem B2143755 : Blo 2143435 2143755 := bstep (se 1 (by rfl) ⟨1607816, by rfl⟩ : syracuseStep 2143755 = 3215633) B3215633
theorem B7235189 : Blo 2143435 7235189 := bbase (se 5 (by rfl) ⟨339149, by rfl⟩ : syracuseStep 7235189 = 678299) (by norm_num)
theorem B4823459 : Blo 2143435 4823459 := bstep (se 1 (by rfl) ⟨3617594, by rfl⟩ : syracuseStep 4823459 = 7235189) B7235189
theorem B3215639 : Blo 2143435 3215639 := bstep (se 1 (by rfl) ⟨2411729, by rfl⟩ : syracuseStep 3215639 = 4823459) B4823459
theorem B2143759 : Blo 2143435 2143759 := bstep (se 1 (by rfl) ⟨1607819, by rfl⟩ : syracuseStep 2143759 = 3215639) B3215639
theorem B3215645 : Blo 2143435 3215645 := bbase (se 3 (by rfl) ⟨602933, by rfl⟩ : syracuseStep 3215645 = 1205867) (by norm_num)
theorem B2143763 : Blo 2143435 2143763 := bstep (se 1 (by rfl) ⟨1607822, by rfl⟩ : syracuseStep 2143763 = 3215645) B3215645
theorem B4823477 : Blo 2143435 4823477 := bbase (se 5 (by rfl) ⟨226100, by rfl⟩ : syracuseStep 4823477 = 452201) (by norm_num)
theorem B3215651 : Blo 2143435 3215651 := bstep (se 1 (by rfl) ⟨2411738, by rfl⟩ : syracuseStep 3215651 = 4823477) B4823477
theorem B2143767 : Blo 2143435 2143767 := bstep (se 1 (by rfl) ⟨1607825, by rfl⟩ : syracuseStep 2143767 = 3215651) B3215651
theorem B3433909 : Blo 2143435 3433909 := bbase (se 5 (by rfl) ⟨160964, by rfl⟩ : syracuseStep 3433909 = 321929) (by norm_num)
theorem B4578545 : Blo 2143435 4578545 := bstep (se 2 (by rfl) ⟨1716954, by rfl⟩ : syracuseStep 4578545 = 3433909) B3433909
theorem B12209453 : Blo 2143435 12209453 := bstep (se 3 (by rfl) ⟨2289272, by rfl⟩ : syracuseStep 12209453 = 4578545) B4578545
theorem B8139635 : Blo 2143435 8139635 := bstep (se 1 (by rfl) ⟨6104726, by rfl⟩ : syracuseStep 8139635 = 12209453) B12209453
theorem B5426423 : Blo 2143435 5426423 := bstep (se 1 (by rfl) ⟨4069817, by rfl⟩ : syracuseStep 5426423 = 8139635) B8139635
theorem B3617615 : Blo 2143435 3617615 := bstep (se 1 (by rfl) ⟨2713211, by rfl⟩ : syracuseStep 3617615 = 5426423) B5426423
theorem B2411743 : Blo 2143435 2411743 := bstep (se 1 (by rfl) ⟨1808807, by rfl⟩ : syracuseStep 2411743 = 3617615) B3617615
theorem B3215657 : Blo 2143435 3215657 := bstep (se 2 (by rfl) ⟨1205871, by rfl⟩ : syracuseStep 3215657 = 2411743) B2411743
theorem B2143771 : Blo 2143435 2143771 := bstep (se 1 (by rfl) ⟨1607828, by rfl⟩ : syracuseStep 2143771 = 3215657) B3215657
theorem B2173025 : Blo 2143435 2173025 := bbase (se 2 (by rfl) ⟨814884, by rfl⟩ : syracuseStep 2173025 = 1629769) (by norm_num)
theorem B5794733 : Blo 2143435 5794733 := bstep (se 3 (by rfl) ⟨1086512, by rfl⟩ : syracuseStep 5794733 = 2173025) B2173025
theorem B3863155 : Blo 2143435 3863155 := bstep (se 1 (by rfl) ⟨2897366, by rfl⟩ : syracuseStep 3863155 = 5794733) B5794733
theorem B5150873 : Blo 2143435 5150873 := bstep (se 2 (by rfl) ⟨1931577, by rfl⟩ : syracuseStep 5150873 = 3863155) B3863155
theorem B3433915 : Blo 2143435 3433915 := bstep (se 1 (by rfl) ⟨2575436, by rfl⟩ : syracuseStep 3433915 = 5150873) B5150873
theorem B4578553 : Blo 2143435 4578553 := bstep (se 2 (by rfl) ⟨1716957, by rfl⟩ : syracuseStep 4578553 = 3433915) B3433915
theorem B6104737 : Blo 2143435 6104737 := bstep (se 2 (by rfl) ⟨2289276, by rfl⟩ : syracuseStep 6104737 = 4578553) B4578553
theorem B8139649 : Blo 2143435 8139649 := bstep (se 2 (by rfl) ⟨3052368, by rfl⟩ : syracuseStep 8139649 = 6104737) B6104737
theorem B10852865 : Blo 2143435 10852865 := bstep (se 2 (by rfl) ⟨4069824, by rfl⟩ : syracuseStep 10852865 = 8139649) B8139649
theorem B7235243 : Blo 2143435 7235243 := bstep (se 1 (by rfl) ⟨5426432, by rfl⟩ : syracuseStep 7235243 = 10852865) B10852865
theorem B4823495 : Blo 2143435 4823495 := bstep (se 1 (by rfl) ⟨3617621, by rfl⟩ : syracuseStep 4823495 = 7235243) B7235243
theorem B3215663 : Blo 2143435 3215663 := bstep (se 1 (by rfl) ⟨2411747, by rfl⟩ : syracuseStep 3215663 = 4823495) B4823495
theorem B2143775 : Blo 2143435 2143775 := bstep (se 1 (by rfl) ⟨1607831, by rfl⟩ : syracuseStep 2143775 = 3215663) B3215663
theorem B3215669 : Blo 2143435 3215669 := bbase (se 5 (by rfl) ⟨150734, by rfl⟩ : syracuseStep 3215669 = 301469) (by norm_num)
theorem B2143779 : Blo 2143435 2143779 := bstep (se 1 (by rfl) ⟨1607834, by rfl⟩ : syracuseStep 2143779 = 3215669) B3215669
theorem B5426453 : Blo 2143435 5426453 := bbase (se 6 (by rfl) ⟨127182, by rfl⟩ : syracuseStep 5426453 = 254365) (by norm_num)
theorem B3617635 : Blo 2143435 3617635 := bstep (se 1 (by rfl) ⟨2713226, by rfl⟩ : syracuseStep 3617635 = 5426453) B5426453
theorem B4823513 : Blo 2143435 4823513 := bstep (se 2 (by rfl) ⟨1808817, by rfl⟩ : syracuseStep 4823513 = 3617635) B3617635
theorem B3215675 : Blo 2143435 3215675 := bstep (se 1 (by rfl) ⟨2411756, by rfl⟩ : syracuseStep 3215675 = 4823513) B4823513
theorem B2143783 : Blo 2143435 2143783 := bstep (se 1 (by rfl) ⟨1607837, by rfl⟩ : syracuseStep 2143783 = 3215675) B3215675
theorem B2411761 : Blo 2143435 2411761 := bbase (se 2 (by rfl) ⟨904410, by rfl⟩ : syracuseStep 2411761 = 1808821) (by norm_num)
theorem B3215681 : Blo 2143435 3215681 := bstep (se 2 (by rfl) ⟨1205880, by rfl⟩ : syracuseStep 3215681 = 2411761) B2411761
theorem B2143787 : Blo 2143435 2143787 := bstep (se 1 (by rfl) ⟨1607840, by rfl⟩ : syracuseStep 2143787 = 3215681) B3215681
theorem B5221189 : Blo 2143435 5221189 := bbase (se 4 (by rfl) ⟨489486, by rfl⟩ : syracuseStep 5221189 = 978973) (by norm_num)
theorem B6961585 : Blo 2143435 6961585 := bstep (se 2 (by rfl) ⟨2610594, by rfl⟩ : syracuseStep 6961585 = 5221189) B5221189
theorem B9282113 : Blo 2143435 9282113 := bstep (se 2 (by rfl) ⟨3480792, by rfl⟩ : syracuseStep 9282113 = 6961585) B6961585
theorem B6188075 : Blo 2143435 6188075 := bstep (se 1 (by rfl) ⟨4641056, by rfl⟩ : syracuseStep 6188075 = 9282113) B9282113
theorem B4125383 : Blo 2143435 4125383 := bstep (se 1 (by rfl) ⟨3094037, by rfl⟩ : syracuseStep 4125383 = 6188075) B6188075
theorem B2750255 : Blo 2143435 2750255 := bstep (se 1 (by rfl) ⟨2062691, by rfl⟩ : syracuseStep 2750255 = 4125383) B4125383
theorem B29336053 : Blo 2143435 29336053 := bstep (se 5 (by rfl) ⟨1375127, by rfl⟩ : syracuseStep 29336053 = 2750255) B2750255
theorem B39114737 : Blo 2143435 39114737 := bstep (se 2 (by rfl) ⟨14668026, by rfl⟩ : syracuseStep 39114737 = 29336053) B29336053
theorem B26076491 : Blo 2143435 26076491 := bstep (se 1 (by rfl) ⟨19557368, by rfl⟩ : syracuseStep 26076491 = 39114737) B39114737
theorem B17384327 : Blo 2143435 17384327 := bstep (se 1 (by rfl) ⟨13038245, by rfl⟩ : syracuseStep 17384327 = 26076491) B26076491
theorem B11589551 : Blo 2143435 11589551 := bstep (se 1 (by rfl) ⟨8692163, by rfl⟩ : syracuseStep 11589551 = 17384327) B17384327
theorem B7726367 : Blo 2143435 7726367 := bstep (se 1 (by rfl) ⟨5794775, by rfl⟩ : syracuseStep 7726367 = 11589551) B11589551
theorem B20603645 : Blo 2143435 20603645 := bstep (se 3 (by rfl) ⟨3863183, by rfl⟩ : syracuseStep 20603645 = 7726367) B7726367
theorem B13735763 : Blo 2143435 13735763 := bstep (se 1 (by rfl) ⟨10301822, by rfl⟩ : syracuseStep 13735763 = 20603645) B20603645
theorem B9157175 : Blo 2143435 9157175 := bstep (se 1 (by rfl) ⟨6867881, by rfl⟩ : syracuseStep 9157175 = 13735763) B13735763
theorem B6104783 : Blo 2143435 6104783 := bstep (se 1 (by rfl) ⟨4578587, by rfl⟩ : syracuseStep 6104783 = 9157175) B9157175
theorem B4069855 : Blo 2143435 4069855 := bstep (se 1 (by rfl) ⟨3052391, by rfl⟩ : syracuseStep 4069855 = 6104783) B6104783
theorem B5426473 : Blo 2143435 5426473 := bstep (se 2 (by rfl) ⟨2034927, by rfl⟩ : syracuseStep 5426473 = 4069855) B4069855
theorem B7235297 : Blo 2143435 7235297 := bstep (se 2 (by rfl) ⟨2713236, by rfl⟩ : syracuseStep 7235297 = 5426473) B5426473
theorem B4823531 : Blo 2143435 4823531 := bstep (se 1 (by rfl) ⟨3617648, by rfl⟩ : syracuseStep 4823531 = 7235297) B7235297
theorem B3215687 : Blo 2143435 3215687 := bstep (se 1 (by rfl) ⟨2411765, by rfl⟩ : syracuseStep 3215687 = 4823531) B4823531
theorem B2143791 : Blo 2143435 2143791 := bstep (se 1 (by rfl) ⟨1607843, by rfl⟩ : syracuseStep 2143791 = 3215687) B3215687
theorem B3215693 : Blo 2143435 3215693 := bbase (se 3 (by rfl) ⟨602942, by rfl⟩ : syracuseStep 3215693 = 1205885) (by norm_num)
theorem B2143795 : Blo 2143435 2143795 := bstep (se 1 (by rfl) ⟨1607846, by rfl⟩ : syracuseStep 2143795 = 3215693) B3215693
theorem B4823549 : Blo 2143435 4823549 := bbase (se 3 (by rfl) ⟨904415, by rfl⟩ : syracuseStep 4823549 = 1808831) (by norm_num)
theorem B3215699 : Blo 2143435 3215699 := bstep (se 1 (by rfl) ⟨2411774, by rfl⟩ : syracuseStep 3215699 = 4823549) B4823549
theorem B2143799 : Blo 2143435 2143799 := bstep (se 1 (by rfl) ⟨1607849, by rfl⟩ : syracuseStep 2143799 = 3215699) B3215699
theorem B3617669 : Blo 2143435 3617669 := bbase (se 4 (by rfl) ⟨339156, by rfl⟩ : syracuseStep 3617669 = 678313) (by norm_num)
theorem B2411779 : Blo 2143435 2411779 := bstep (se 1 (by rfl) ⟨1808834, by rfl⟩ : syracuseStep 2411779 = 3617669) B3617669
theorem B3215705 : Blo 2143435 3215705 := bstep (se 2 (by rfl) ⟨1205889, by rfl⟩ : syracuseStep 3215705 = 2411779) B2411779
theorem B2143803 : Blo 2143435 2143803 := bstep (se 1 (by rfl) ⟨1607852, by rfl⟩ : syracuseStep 2143803 = 3215705) B3215705
theorem B16279541 : Blo 2143435 16279541 := bbase (se 5 (by rfl) ⟨763103, by rfl⟩ : syracuseStep 16279541 = 1526207) (by norm_num)
theorem B10853027 : Blo 2143435 10853027 := bstep (se 1 (by rfl) ⟨8139770, by rfl⟩ : syracuseStep 10853027 = 16279541) B16279541
theorem B7235351 : Blo 2143435 7235351 := bstep (se 1 (by rfl) ⟨5426513, by rfl⟩ : syracuseStep 7235351 = 10853027) B10853027
theorem B4823567 : Blo 2143435 4823567 := bstep (se 1 (by rfl) ⟨3617675, by rfl⟩ : syracuseStep 4823567 = 7235351) B7235351
theorem B3215711 : Blo 2143435 3215711 := bstep (se 1 (by rfl) ⟨2411783, by rfl⟩ : syracuseStep 3215711 = 4823567) B4823567
theorem B2143807 : Blo 2143435 2143807 := bstep (se 1 (by rfl) ⟨1607855, by rfl⟩ : syracuseStep 2143807 = 3215711) B3215711
theorem B3215717 : Blo 2143435 3215717 := bbase (se 4 (by rfl) ⟨301473, by rfl⟩ : syracuseStep 3215717 = 602947) (by norm_num)
theorem B2143811 : Blo 2143435 2143811 := bstep (se 1 (by rfl) ⟨1607858, by rfl⟩ : syracuseStep 2143811 = 3215717) B3215717
theorem B4069901 : Blo 2143435 4069901 := bbase (se 3 (by rfl) ⟨763106, by rfl⟩ : syracuseStep 4069901 = 1526213) (by norm_num)
theorem B2713267 : Blo 2143435 2713267 := bstep (se 1 (by rfl) ⟨2034950, by rfl⟩ : syracuseStep 2713267 = 4069901) B4069901
theorem B3617689 : Blo 2143435 3617689 := bstep (se 2 (by rfl) ⟨1356633, by rfl⟩ : syracuseStep 3617689 = 2713267) B2713267
theorem B4823585 : Blo 2143435 4823585 := bstep (se 2 (by rfl) ⟨1808844, by rfl⟩ : syracuseStep 4823585 = 3617689) B3617689
theorem B3215723 : Blo 2143435 3215723 := bstep (se 1 (by rfl) ⟨2411792, by rfl⟩ : syracuseStep 3215723 = 4823585) B4823585
theorem B2143815 : Blo 2143435 2143815 := bstep (se 1 (by rfl) ⟨1607861, by rfl⟩ : syracuseStep 2143815 = 3215723) B3215723
theorem B2411797 : Blo 2143435 2411797 := bbase (se 6 (by rfl) ⟨56526, by rfl⟩ : syracuseStep 2411797 = 113053) (by norm_num)
theorem B3215729 : Blo 2143435 3215729 := bstep (se 2 (by rfl) ⟨1205898, by rfl⟩ : syracuseStep 3215729 = 2411797) B2411797
theorem B2143819 : Blo 2143435 2143819 := bstep (se 1 (by rfl) ⟨1607864, by rfl⟩ : syracuseStep 2143819 = 3215729) B3215729
theorem B2713277 : Blo 2143435 2713277 := bbase (se 3 (by rfl) ⟨508739, by rfl⟩ : syracuseStep 2713277 = 1017479) (by norm_num)
theorem B7235405 : Blo 2143435 7235405 := bstep (se 3 (by rfl) ⟨1356638, by rfl⟩ : syracuseStep 7235405 = 2713277) B2713277
theorem B4823603 : Blo 2143435 4823603 := bstep (se 1 (by rfl) ⟨3617702, by rfl⟩ : syracuseStep 4823603 = 7235405) B7235405
theorem B3215735 : Blo 2143435 3215735 := bstep (se 1 (by rfl) ⟨2411801, by rfl⟩ : syracuseStep 3215735 = 4823603) B4823603
theorem B2143823 : Blo 2143435 2143823 := bstep (se 1 (by rfl) ⟨1607867, by rfl⟩ : syracuseStep 2143823 = 3215735) B3215735
theorem B3215741 : Blo 2143435 3215741 := bbase (se 3 (by rfl) ⟨602951, by rfl⟩ : syracuseStep 3215741 = 1205903) (by norm_num)
theorem B2143827 : Blo 2143435 2143827 := bstep (se 1 (by rfl) ⟨1607870, by rfl⟩ : syracuseStep 2143827 = 3215741) B3215741
theorem B4823621 : Blo 2143435 4823621 := bbase (se 4 (by rfl) ⟨452214, by rfl⟩ : syracuseStep 4823621 = 904429) (by norm_num)
theorem B3215747 : Blo 2143435 3215747 := bstep (se 1 (by rfl) ⟨2411810, by rfl⟩ : syracuseStep 3215747 = 4823621) B4823621
theorem B2143831 : Blo 2143435 2143831 := bstep (se 1 (by rfl) ⟨1607873, by rfl⟩ : syracuseStep 2143831 = 3215747) B3215747
theorem B2289341 : Blo 2143435 2289341 := bbase (se 3 (by rfl) ⟨429251, by rfl⟩ : syracuseStep 2289341 = 858503) (by norm_num)
theorem B6104909 : Blo 2143435 6104909 := bstep (se 3 (by rfl) ⟨1144670, by rfl⟩ : syracuseStep 6104909 = 2289341) B2289341
theorem B4069939 : Blo 2143435 4069939 := bstep (se 1 (by rfl) ⟨3052454, by rfl⟩ : syracuseStep 4069939 = 6104909) B6104909
theorem B5426585 : Blo 2143435 5426585 := bstep (se 2 (by rfl) ⟨2034969, by rfl⟩ : syracuseStep 5426585 = 4069939) B4069939
theorem B3617723 : Blo 2143435 3617723 := bstep (se 1 (by rfl) ⟨2713292, by rfl⟩ : syracuseStep 3617723 = 5426585) B5426585
theorem B2411815 : Blo 2143435 2411815 := bstep (se 1 (by rfl) ⟨1808861, by rfl⟩ : syracuseStep 2411815 = 3617723) B3617723
theorem B3215753 : Blo 2143435 3215753 := bstep (se 2 (by rfl) ⟨1205907, by rfl⟩ : syracuseStep 3215753 = 2411815) B2411815
theorem B2143835 : Blo 2143435 2143835 := bstep (se 1 (by rfl) ⟨1607876, by rfl⟩ : syracuseStep 2143835 = 3215753) B3215753
theorem B10853189 : Blo 2143435 10853189 := bbase (se 4 (by rfl) ⟨1017486, by rfl⟩ : syracuseStep 10853189 = 2034973) (by norm_num)
theorem B7235459 : Blo 2143435 7235459 := bstep (se 1 (by rfl) ⟨5426594, by rfl⟩ : syracuseStep 7235459 = 10853189) B10853189
theorem B4823639 : Blo 2143435 4823639 := bstep (se 1 (by rfl) ⟨3617729, by rfl⟩ : syracuseStep 4823639 = 7235459) B7235459
theorem B3215759 : Blo 2143435 3215759 := bstep (se 1 (by rfl) ⟨2411819, by rfl⟩ : syracuseStep 3215759 = 4823639) B4823639
theorem B2143839 : Blo 2143435 2143839 := bstep (se 1 (by rfl) ⟨1607879, by rfl⟩ : syracuseStep 2143839 = 3215759) B3215759
theorem B3215765 : Blo 2143435 3215765 := bbase (se 6 (by rfl) ⟨75369, by rfl⟩ : syracuseStep 3215765 = 150739) (by norm_num)
theorem B2143843 : Blo 2143435 2143843 := bstep (se 1 (by rfl) ⟨1607882, by rfl⟩ : syracuseStep 2143843 = 3215765) B3215765
theorem B3863285 : Blo 2143435 3863285 := bbase (se 5 (by rfl) ⟨181091, by rfl⟩ : syracuseStep 3863285 = 362183) (by norm_num)
theorem B2575523 : Blo 2143435 2575523 := bstep (se 1 (by rfl) ⟨1931642, by rfl⟩ : syracuseStep 2575523 = 3863285) B3863285
theorem B6868061 : Blo 2143435 6868061 := bstep (se 3 (by rfl) ⟨1287761, by rfl⟩ : syracuseStep 6868061 = 2575523) B2575523
theorem B4578707 : Blo 2143435 4578707 := bstep (se 1 (by rfl) ⟨3434030, by rfl⟩ : syracuseStep 4578707 = 6868061) B6868061
theorem B12209885 : Blo 2143435 12209885 := bstep (se 3 (by rfl) ⟨2289353, by rfl⟩ : syracuseStep 12209885 = 4578707) B4578707
theorem B8139923 : Blo 2143435 8139923 := bstep (se 1 (by rfl) ⟨6104942, by rfl⟩ : syracuseStep 8139923 = 12209885) B12209885
theorem B5426615 : Blo 2143435 5426615 := bstep (se 1 (by rfl) ⟨4069961, by rfl⟩ : syracuseStep 5426615 = 8139923) B8139923
theorem B3617743 : Blo 2143435 3617743 := bstep (se 1 (by rfl) ⟨2713307, by rfl⟩ : syracuseStep 3617743 = 5426615) B5426615
theorem B4823657 : Blo 2143435 4823657 := bstep (se 2 (by rfl) ⟨1808871, by rfl⟩ : syracuseStep 4823657 = 3617743) B3617743
theorem B3215771 : Blo 2143435 3215771 := bstep (se 1 (by rfl) ⟨2411828, by rfl⟩ : syracuseStep 3215771 = 4823657) B4823657
theorem B2143847 : Blo 2143435 2143847 := bstep (se 1 (by rfl) ⟨1607885, by rfl⟩ : syracuseStep 2143847 = 3215771) B3215771
theorem B2411833 : Blo 2143435 2411833 := bbase (se 2 (by rfl) ⟨904437, by rfl⟩ : syracuseStep 2411833 = 1808875) (by norm_num)
theorem B3215777 : Blo 2143435 3215777 := bstep (se 2 (by rfl) ⟨1205916, by rfl⟩ : syracuseStep 3215777 = 2411833) B2411833
theorem B2143851 : Blo 2143435 2143851 := bstep (se 1 (by rfl) ⟨1607888, by rfl⟩ : syracuseStep 2143851 = 3215777) B3215777
theorem B6104965 : Blo 2143435 6104965 := bbase (se 4 (by rfl) ⟨572340, by rfl⟩ : syracuseStep 6104965 = 1144681) (by norm_num)
theorem B8139953 : Blo 2143435 8139953 := bstep (se 2 (by rfl) ⟨3052482, by rfl⟩ : syracuseStep 8139953 = 6104965) B6104965
theorem B5426635 : Blo 2143435 5426635 := bstep (se 1 (by rfl) ⟨4069976, by rfl⟩ : syracuseStep 5426635 = 8139953) B8139953
theorem B7235513 : Blo 2143435 7235513 := bstep (se 2 (by rfl) ⟨2713317, by rfl⟩ : syracuseStep 7235513 = 5426635) B5426635
theorem B4823675 : Blo 2143435 4823675 := bstep (se 1 (by rfl) ⟨3617756, by rfl⟩ : syracuseStep 4823675 = 7235513) B7235513
theorem B3215783 : Blo 2143435 3215783 := bstep (se 1 (by rfl) ⟨2411837, by rfl⟩ : syracuseStep 3215783 = 4823675) B4823675
theorem B2143855 : Blo 2143435 2143855 := bstep (se 1 (by rfl) ⟨1607891, by rfl⟩ : syracuseStep 2143855 = 3215783) B3215783
theorem B3215789 : Blo 2143435 3215789 := bbase (se 3 (by rfl) ⟨602960, by rfl⟩ : syracuseStep 3215789 = 1205921) (by norm_num)
theorem B2143859 : Blo 2143435 2143859 := bstep (se 1 (by rfl) ⟨1607894, by rfl⟩ : syracuseStep 2143859 = 3215789) B3215789
theorem B4823693 : Blo 2143435 4823693 := bbase (se 3 (by rfl) ⟨904442, by rfl⟩ : syracuseStep 4823693 = 1808885) (by norm_num)
theorem B3215795 : Blo 2143435 3215795 := bstep (se 1 (by rfl) ⟨2411846, by rfl⟩ : syracuseStep 3215795 = 4823693) B4823693
theorem B2143863 : Blo 2143435 2143863 := bstep (se 1 (by rfl) ⟨1607897, by rfl⟩ : syracuseStep 2143863 = 3215795) B3215795
theorem B2713333 : Blo 2143435 2713333 := bbase (se 5 (by rfl) ⟨127187, by rfl⟩ : syracuseStep 2713333 = 254375) (by norm_num)
theorem B3617777 : Blo 2143435 3617777 := bstep (se 2 (by rfl) ⟨1356666, by rfl⟩ : syracuseStep 3617777 = 2713333) B2713333
theorem B2411851 : Blo 2143435 2411851 := bstep (se 1 (by rfl) ⟨1808888, by rfl⟩ : syracuseStep 2411851 = 3617777) B3617777
theorem B3215801 : Blo 2143435 3215801 := bstep (se 2 (by rfl) ⟨1205925, by rfl⟩ : syracuseStep 3215801 = 2411851) B2411851
theorem B2143867 : Blo 2143435 2143867 := bstep (se 1 (by rfl) ⟨1607900, by rfl⟩ : syracuseStep 2143867 = 3215801) B3215801
theorem B4641229 : Blo 2143435 4641229 := bbase (se 3 (by rfl) ⟨870230, by rfl⟩ : syracuseStep 4641229 = 1740461) (by norm_num)
theorem B6188305 : Blo 2143435 6188305 := bstep (se 2 (by rfl) ⟨2320614, by rfl⟩ : syracuseStep 6188305 = 4641229) B4641229
theorem B8251073 : Blo 2143435 8251073 := bstep (se 2 (by rfl) ⟨3094152, by rfl⟩ : syracuseStep 8251073 = 6188305) B6188305
theorem B5500715 : Blo 2143435 5500715 := bstep (se 1 (by rfl) ⟨4125536, by rfl⟩ : syracuseStep 5500715 = 8251073) B8251073
theorem B14668573 : Blo 2143435 14668573 := bstep (se 3 (by rfl) ⟨2750357, by rfl⟩ : syracuseStep 14668573 = 5500715) B5500715
theorem B19558097 : Blo 2143435 19558097 := bstep (se 2 (by rfl) ⟨7334286, by rfl⟩ : syracuseStep 19558097 = 14668573) B14668573
theorem B13038731 : Blo 2143435 13038731 := bstep (se 1 (by rfl) ⟨9779048, by rfl⟩ : syracuseStep 13038731 = 19558097) B19558097
theorem B8692487 : Blo 2143435 8692487 := bstep (se 1 (by rfl) ⟨6519365, by rfl⟩ : syracuseStep 8692487 = 13038731) B13038731
theorem B5794991 : Blo 2143435 5794991 := bstep (se 1 (by rfl) ⟨4346243, by rfl⟩ : syracuseStep 5794991 = 8692487) B8692487
theorem B3863327 : Blo 2143435 3863327 := bstep (se 1 (by rfl) ⟨2897495, by rfl⟩ : syracuseStep 3863327 = 5794991) B5794991
theorem B41208821 : Blo 2143435 41208821 := bstep (se 5 (by rfl) ⟨1931663, by rfl⟩ : syracuseStep 41208821 = 3863327) B3863327
theorem B27472547 : Blo 2143435 27472547 := bstep (se 1 (by rfl) ⟨20604410, by rfl⟩ : syracuseStep 27472547 = 41208821) B41208821
theorem B18315031 : Blo 2143435 18315031 := bstep (se 1 (by rfl) ⟨13736273, by rfl⟩ : syracuseStep 18315031 = 27472547) B27472547
theorem B24420041 : Blo 2143435 24420041 := bstep (se 2 (by rfl) ⟨9157515, by rfl⟩ : syracuseStep 24420041 = 18315031) B18315031
theorem B16280027 : Blo 2143435 16280027 := bstep (se 1 (by rfl) ⟨12210020, by rfl⟩ : syracuseStep 16280027 = 24420041) B24420041
theorem B10853351 : Blo 2143435 10853351 := bstep (se 1 (by rfl) ⟨8140013, by rfl⟩ : syracuseStep 10853351 = 16280027) B16280027
theorem B7235567 : Blo 2143435 7235567 := bstep (se 1 (by rfl) ⟨5426675, by rfl⟩ : syracuseStep 7235567 = 10853351) B10853351
theorem B4823711 : Blo 2143435 4823711 := bstep (se 1 (by rfl) ⟨3617783, by rfl⟩ : syracuseStep 4823711 = 7235567) B7235567
theorem B3215807 : Blo 2143435 3215807 := bstep (se 1 (by rfl) ⟨2411855, by rfl⟩ : syracuseStep 3215807 = 4823711) B4823711
theorem B2143871 : Blo 2143435 2143871 := bstep (se 1 (by rfl) ⟨1607903, by rfl⟩ : syracuseStep 2143871 = 3215807) B3215807
theorem B3215813 : Blo 2143435 3215813 := bbase (se 4 (by rfl) ⟨301482, by rfl⟩ : syracuseStep 3215813 = 602965) (by norm_num)
theorem B2143875 : Blo 2143435 2143875 := bstep (se 1 (by rfl) ⟨1607906, by rfl⟩ : syracuseStep 2143875 = 3215813) B3215813
theorem B3617797 : Blo 2143435 3617797 := bbase (se 4 (by rfl) ⟨339168, by rfl⟩ : syracuseStep 3617797 = 678337) (by norm_num)
theorem B4823729 : Blo 2143435 4823729 := bstep (se 2 (by rfl) ⟨1808898, by rfl⟩ : syracuseStep 4823729 = 3617797) B3617797
theorem B3215819 : Blo 2143435 3215819 := bstep (se 1 (by rfl) ⟨2411864, by rfl⟩ : syracuseStep 3215819 = 4823729) B4823729
theorem B2143879 : Blo 2143435 2143879 := bstep (se 1 (by rfl) ⟨1607909, by rfl⟩ : syracuseStep 2143879 = 3215819) B3215819
theorem B2411869 : Blo 2143435 2411869 := bbase (se 3 (by rfl) ⟨452225, by rfl⟩ : syracuseStep 2411869 = 904451) (by norm_num)
theorem B3215825 : Blo 2143435 3215825 := bstep (se 2 (by rfl) ⟨1205934, by rfl⟩ : syracuseStep 3215825 = 2411869) B2411869
theorem B2143883 : Blo 2143435 2143883 := bstep (se 1 (by rfl) ⟨1607912, by rfl⟩ : syracuseStep 2143883 = 3215825) B3215825
theorem B7235621 : Blo 2143435 7235621 := bbase (se 4 (by rfl) ⟨678339, by rfl⟩ : syracuseStep 7235621 = 1356679) (by norm_num)
theorem B4823747 : Blo 2143435 4823747 := bstep (se 1 (by rfl) ⟨3617810, by rfl⟩ : syracuseStep 4823747 = 7235621) B7235621
theorem B3215831 : Blo 2143435 3215831 := bstep (se 1 (by rfl) ⟨2411873, by rfl⟩ : syracuseStep 3215831 = 4823747) B4823747
theorem B2143887 : Blo 2143435 2143887 := bstep (se 1 (by rfl) ⟨1607915, by rfl⟩ : syracuseStep 2143887 = 3215831) B3215831
theorem B3215837 : Blo 2143435 3215837 := bbase (se 3 (by rfl) ⟨602969, by rfl⟩ : syracuseStep 3215837 = 1205939) (by norm_num)
theorem B2143891 : Blo 2143435 2143891 := bstep (se 1 (by rfl) ⟨1607918, by rfl⟩ : syracuseStep 2143891 = 3215837) B3215837
theorem B4823765 : Blo 2143435 4823765 := bbase (se 7 (by rfl) ⟨56528, by rfl⟩ : syracuseStep 4823765 = 113057) (by norm_num)
theorem B3215843 : Blo 2143435 3215843 := bstep (se 1 (by rfl) ⟨2411882, by rfl⟩ : syracuseStep 3215843 = 4823765) B4823765
theorem B2143895 : Blo 2143435 2143895 := bstep (se 1 (by rfl) ⟨1607921, by rfl⟩ : syracuseStep 2143895 = 3215843) B3215843
theorem B9157637 : Blo 2143435 9157637 := bbase (se 4 (by rfl) ⟨858528, by rfl⟩ : syracuseStep 9157637 = 1717057) (by norm_num)
theorem B6105091 : Blo 2143435 6105091 := bstep (se 1 (by rfl) ⟨4578818, by rfl⟩ : syracuseStep 6105091 = 9157637) B9157637
theorem B8140121 : Blo 2143435 8140121 := bstep (se 2 (by rfl) ⟨3052545, by rfl⟩ : syracuseStep 8140121 = 6105091) B6105091
theorem B5426747 : Blo 2143435 5426747 := bstep (se 1 (by rfl) ⟨4070060, by rfl⟩ : syracuseStep 5426747 = 8140121) B8140121
theorem B3617831 : Blo 2143435 3617831 := bstep (se 1 (by rfl) ⟨2713373, by rfl⟩ : syracuseStep 3617831 = 5426747) B5426747
theorem B2411887 : Blo 2143435 2411887 := bstep (se 1 (by rfl) ⟨1808915, by rfl⟩ : syracuseStep 2411887 = 3617831) B3617831
theorem B3215849 : Blo 2143435 3215849 := bstep (se 2 (by rfl) ⟨1205943, by rfl⟩ : syracuseStep 3215849 = 2411887) B2411887
theorem B2143899 : Blo 2143435 2143899 := bstep (se 1 (by rfl) ⟨1607924, by rfl⟩ : syracuseStep 2143899 = 3215849) B3215849
theorem B13923893 : Blo 2143435 13923893 := bbase (se 5 (by rfl) ⟨652682, by rfl⟩ : syracuseStep 13923893 = 1305365) (by norm_num)
theorem B9282595 : Blo 2143435 9282595 := bstep (se 1 (by rfl) ⟨6961946, by rfl⟩ : syracuseStep 9282595 = 13923893) B13923893
theorem B12376793 : Blo 2143435 12376793 := bstep (se 2 (by rfl) ⟨4641297, by rfl⟩ : syracuseStep 12376793 = 9282595) B9282595
theorem B8251195 : Blo 2143435 8251195 := bstep (se 1 (by rfl) ⟨6188396, by rfl⟩ : syracuseStep 8251195 = 12376793) B12376793
theorem B11001593 : Blo 2143435 11001593 := bstep (se 2 (by rfl) ⟨4125597, by rfl⟩ : syracuseStep 11001593 = 8251195) B8251195
theorem B7334395 : Blo 2143435 7334395 := bstep (se 1 (by rfl) ⟨5500796, by rfl⟩ : syracuseStep 7334395 = 11001593) B11001593
theorem B39116773 : Blo 2143435 39116773 := bstep (se 4 (by rfl) ⟨3667197, by rfl⟩ : syracuseStep 39116773 = 7334395) B7334395
theorem B52155697 : Blo 2143435 52155697 := bstep (se 2 (by rfl) ⟨19558386, by rfl⟩ : syracuseStep 52155697 = 39116773) B39116773
theorem B69540929 : Blo 2143435 69540929 := bstep (se 2 (by rfl) ⟨26077848, by rfl⟩ : syracuseStep 69540929 = 52155697) B52155697
theorem B46360619 : Blo 2143435 46360619 := bstep (se 1 (by rfl) ⟨34770464, by rfl⟩ : syracuseStep 46360619 = 69540929) B69540929
theorem B30907079 : Blo 2143435 30907079 := bstep (se 1 (by rfl) ⟨23180309, by rfl⟩ : syracuseStep 30907079 = 46360619) B46360619
theorem B20604719 : Blo 2143435 20604719 := bstep (se 1 (by rfl) ⟨15453539, by rfl⟩ : syracuseStep 20604719 = 30907079) B30907079
theorem B13736479 : Blo 2143435 13736479 := bstep (se 1 (by rfl) ⟨10302359, by rfl⟩ : syracuseStep 13736479 = 20604719) B20604719
theorem B18315305 : Blo 2143435 18315305 := bstep (se 2 (by rfl) ⟨6868239, by rfl⟩ : syracuseStep 18315305 = 13736479) B13736479
theorem B12210203 : Blo 2143435 12210203 := bstep (se 1 (by rfl) ⟨9157652, by rfl⟩ : syracuseStep 12210203 = 18315305) B18315305
theorem B8140135 : Blo 2143435 8140135 := bstep (se 1 (by rfl) ⟨6105101, by rfl⟩ : syracuseStep 8140135 = 12210203) B12210203
theorem B10853513 : Blo 2143435 10853513 := bstep (se 2 (by rfl) ⟨4070067, by rfl⟩ : syracuseStep 10853513 = 8140135) B8140135
theorem B7235675 : Blo 2143435 7235675 := bstep (se 1 (by rfl) ⟨5426756, by rfl⟩ : syracuseStep 7235675 = 10853513) B10853513
theorem B4823783 : Blo 2143435 4823783 := bstep (se 1 (by rfl) ⟨3617837, by rfl⟩ : syracuseStep 4823783 = 7235675) B7235675
theorem B3215855 : Blo 2143435 3215855 := bstep (se 1 (by rfl) ⟨2411891, by rfl⟩ : syracuseStep 3215855 = 4823783) B4823783
theorem B2143903 : Blo 2143435 2143903 := bstep (se 1 (by rfl) ⟨1607927, by rfl⟩ : syracuseStep 2143903 = 3215855) B3215855
theorem B3215861 : Blo 2143435 3215861 := bbase (se 5 (by rfl) ⟨150743, by rfl⟩ : syracuseStep 3215861 = 301487) (by norm_num)
theorem B2143907 : Blo 2143435 2143907 := bstep (se 1 (by rfl) ⟨1607930, by rfl⟩ : syracuseStep 2143907 = 3215861) B3215861
theorem B6105125 : Blo 2143435 6105125 := bbase (se 4 (by rfl) ⟨572355, by rfl⟩ : syracuseStep 6105125 = 1144711) (by norm_num)
theorem B4070083 : Blo 2143435 4070083 := bstep (se 1 (by rfl) ⟨3052562, by rfl⟩ : syracuseStep 4070083 = 6105125) B6105125
theorem B5426777 : Blo 2143435 5426777 := bstep (se 2 (by rfl) ⟨2035041, by rfl⟩ : syracuseStep 5426777 = 4070083) B4070083
theorem B3617851 : Blo 2143435 3617851 := bstep (se 1 (by rfl) ⟨2713388, by rfl⟩ : syracuseStep 3617851 = 5426777) B5426777
theorem B4823801 : Blo 2143435 4823801 := bstep (se 2 (by rfl) ⟨1808925, by rfl⟩ : syracuseStep 4823801 = 3617851) B3617851
theorem B3215867 : Blo 2143435 3215867 := bstep (se 1 (by rfl) ⟨2411900, by rfl⟩ : syracuseStep 3215867 = 4823801) B4823801
theorem B2143911 : Blo 2143435 2143911 := bstep (se 1 (by rfl) ⟨1607933, by rfl⟩ : syracuseStep 2143911 = 3215867) B3215867
theorem B2411905 : Blo 2143435 2411905 := bbase (se 2 (by rfl) ⟨904464, by rfl⟩ : syracuseStep 2411905 = 1808929) (by norm_num)
theorem B3215873 : Blo 2143435 3215873 := bstep (se 2 (by rfl) ⟨1205952, by rfl⟩ : syracuseStep 3215873 = 2411905) B2411905
theorem B2143915 : Blo 2143435 2143915 := bstep (se 1 (by rfl) ⟨1607936, by rfl⟩ : syracuseStep 2143915 = 3215873) B3215873
theorem B5426797 : Blo 2143435 5426797 := bbase (se 3 (by rfl) ⟨1017524, by rfl⟩ : syracuseStep 5426797 = 2035049) (by norm_num)
theorem B7235729 : Blo 2143435 7235729 := bstep (se 2 (by rfl) ⟨2713398, by rfl⟩ : syracuseStep 7235729 = 5426797) B5426797
theorem B4823819 : Blo 2143435 4823819 := bstep (se 1 (by rfl) ⟨3617864, by rfl⟩ : syracuseStep 4823819 = 7235729) B7235729
theorem B3215879 : Blo 2143435 3215879 := bstep (se 1 (by rfl) ⟨2411909, by rfl⟩ : syracuseStep 3215879 = 4823819) B4823819
theorem B2143919 : Blo 2143435 2143919 := bstep (se 1 (by rfl) ⟨1607939, by rfl⟩ : syracuseStep 2143919 = 3215879) B3215879
theorem B3215885 : Blo 2143435 3215885 := bbase (se 3 (by rfl) ⟨602978, by rfl⟩ : syracuseStep 3215885 = 1205957) (by norm_num)
theorem B2143923 : Blo 2143435 2143923 := bstep (se 1 (by rfl) ⟨1607942, by rfl⟩ : syracuseStep 2143923 = 3215885) B3215885
theorem B4823837 : Blo 2143435 4823837 := bbase (se 3 (by rfl) ⟨904469, by rfl⟩ : syracuseStep 4823837 = 1808939) (by norm_num)
theorem B3215891 : Blo 2143435 3215891 := bstep (se 1 (by rfl) ⟨2411918, by rfl⟩ : syracuseStep 3215891 = 4823837) B4823837
theorem B2143927 : Blo 2143435 2143927 := bstep (se 1 (by rfl) ⟨1607945, by rfl⟩ : syracuseStep 2143927 = 3215891) B3215891
theorem B3617885 : Blo 2143435 3617885 := bbase (se 3 (by rfl) ⟨678353, by rfl⟩ : syracuseStep 3617885 = 1356707) (by norm_num)
theorem B2411923 : Blo 2143435 2411923 := bstep (se 1 (by rfl) ⟨1808942, by rfl⟩ : syracuseStep 2411923 = 3617885) B3617885
theorem B3215897 : Blo 2143435 3215897 := bstep (se 2 (by rfl) ⟨1205961, by rfl⟩ : syracuseStep 3215897 = 2411923) B2411923
theorem B2143931 : Blo 2143435 2143931 := bstep (se 1 (by rfl) ⟨1607948, by rfl⟩ : syracuseStep 2143931 = 3215897) B3215897
theorem B3259781 : Blo 2143435 3259781 := bbase (se 4 (by rfl) ⟨305604, by rfl⟩ : syracuseStep 3259781 = 611209) (by norm_num)
theorem B2173187 : Blo 2143435 2173187 := bstep (se 1 (by rfl) ⟨1629890, by rfl⟩ : syracuseStep 2173187 = 3259781) B3259781
theorem B5795165 : Blo 2143435 5795165 := bstep (se 3 (by rfl) ⟨1086593, by rfl⟩ : syracuseStep 5795165 = 2173187) B2173187
theorem B3863443 : Blo 2143435 3863443 := bstep (se 1 (by rfl) ⟨2897582, by rfl⟩ : syracuseStep 3863443 = 5795165) B5795165
theorem B5151257 : Blo 2143435 5151257 := bstep (se 2 (by rfl) ⟨1931721, by rfl⟩ : syracuseStep 5151257 = 3863443) B3863443
theorem B3434171 : Blo 2143435 3434171 := bstep (se 1 (by rfl) ⟨2575628, by rfl⟩ : syracuseStep 3434171 = 5151257) B5151257
theorem B9157789 : Blo 2143435 9157789 := bstep (se 3 (by rfl) ⟨1717085, by rfl⟩ : syracuseStep 9157789 = 3434171) B3434171
theorem B12210385 : Blo 2143435 12210385 := bstep (se 2 (by rfl) ⟨4578894, by rfl⟩ : syracuseStep 12210385 = 9157789) B9157789
theorem B16280513 : Blo 2143435 16280513 := bstep (se 2 (by rfl) ⟨6105192, by rfl⟩ : syracuseStep 16280513 = 12210385) B12210385
theorem B10853675 : Blo 2143435 10853675 := bstep (se 1 (by rfl) ⟨8140256, by rfl⟩ : syracuseStep 10853675 = 16280513) B16280513
theorem B7235783 : Blo 2143435 7235783 := bstep (se 1 (by rfl) ⟨5426837, by rfl⟩ : syracuseStep 7235783 = 10853675) B10853675
theorem B4823855 : Blo 2143435 4823855 := bstep (se 1 (by rfl) ⟨3617891, by rfl⟩ : syracuseStep 4823855 = 7235783) B7235783
theorem B3215903 : Blo 2143435 3215903 := bstep (se 1 (by rfl) ⟨2411927, by rfl⟩ : syracuseStep 3215903 = 4823855) B4823855
theorem B2143935 : Blo 2143435 2143935 := bstep (se 1 (by rfl) ⟨1607951, by rfl⟩ : syracuseStep 2143935 = 3215903) B3215903
theorem B3215909 : Blo 2143435 3215909 := bbase (se 4 (by rfl) ⟨301491, by rfl⟩ : syracuseStep 3215909 = 602983) (by norm_num)
theorem B2143939 : Blo 2143435 2143939 := bstep (se 1 (by rfl) ⟨1607954, by rfl⟩ : syracuseStep 2143939 = 3215909) B3215909
theorem B2713429 : Blo 2143435 2713429 := bbase (se 9 (by rfl) ⟨7949, by rfl⟩ : syracuseStep 2713429 = 15899) (by norm_num)
theorem B3617905 : Blo 2143435 3617905 := bstep (se 2 (by rfl) ⟨1356714, by rfl⟩ : syracuseStep 3617905 = 2713429) B2713429
theorem B4823873 : Blo 2143435 4823873 := bstep (se 2 (by rfl) ⟨1808952, by rfl⟩ : syracuseStep 4823873 = 3617905) B3617905
theorem B3215915 : Blo 2143435 3215915 := bstep (se 1 (by rfl) ⟨2411936, by rfl⟩ : syracuseStep 3215915 = 4823873) B4823873
theorem B2143943 : Blo 2143435 2143943 := bstep (se 1 (by rfl) ⟨1607957, by rfl⟩ : syracuseStep 2143943 = 3215915) B3215915
theorem B2411941 : Blo 2143435 2411941 := bbase (se 4 (by rfl) ⟨226119, by rfl⟩ : syracuseStep 2411941 = 452239) (by norm_num)
theorem B3215921 : Blo 2143435 3215921 := bstep (se 2 (by rfl) ⟨1205970, by rfl⟩ : syracuseStep 3215921 = 2411941) B2411941
theorem B2143947 : Blo 2143435 2143947 := bstep (se 1 (by rfl) ⟨1607960, by rfl⟩ : syracuseStep 2143947 = 3215921) B3215921
theorem B13736789 : Blo 2143435 13736789 := bbase (se 9 (by rfl) ⟨40244, by rfl⟩ : syracuseStep 13736789 = 80489) (by norm_num)
theorem B9157859 : Blo 2143435 9157859 := bstep (se 1 (by rfl) ⟨6868394, by rfl⟩ : syracuseStep 9157859 = 13736789) B13736789
theorem B6105239 : Blo 2143435 6105239 := bstep (se 1 (by rfl) ⟨4578929, by rfl⟩ : syracuseStep 6105239 = 9157859) B9157859
theorem B4070159 : Blo 2143435 4070159 := bstep (se 1 (by rfl) ⟨3052619, by rfl⟩ : syracuseStep 4070159 = 6105239) B6105239
theorem B2713439 : Blo 2143435 2713439 := bstep (se 1 (by rfl) ⟨2035079, by rfl⟩ : syracuseStep 2713439 = 4070159) B4070159
theorem B7235837 : Blo 2143435 7235837 := bstep (se 3 (by rfl) ⟨1356719, by rfl⟩ : syracuseStep 7235837 = 2713439) B2713439
theorem B4823891 : Blo 2143435 4823891 := bstep (se 1 (by rfl) ⟨3617918, by rfl⟩ : syracuseStep 4823891 = 7235837) B7235837
theorem B3215927 : Blo 2143435 3215927 := bstep (se 1 (by rfl) ⟨2411945, by rfl⟩ : syracuseStep 3215927 = 4823891) B4823891
theorem B2143951 : Blo 2143435 2143951 := bstep (se 1 (by rfl) ⟨1607963, by rfl⟩ : syracuseStep 2143951 = 3215927) B3215927
theorem B3215933 : Blo 2143435 3215933 := bbase (se 3 (by rfl) ⟨602987, by rfl⟩ : syracuseStep 3215933 = 1205975) (by norm_num)
theorem B2143955 : Blo 2143435 2143955 := bstep (se 1 (by rfl) ⟨1607966, by rfl⟩ : syracuseStep 2143955 = 3215933) B3215933
theorem B4823909 : Blo 2143435 4823909 := bbase (se 4 (by rfl) ⟨452241, by rfl⟩ : syracuseStep 4823909 = 904483) (by norm_num)
theorem B3215939 : Blo 2143435 3215939 := bstep (se 1 (by rfl) ⟨2411954, by rfl⟩ : syracuseStep 3215939 = 4823909) B4823909
theorem B2143959 : Blo 2143435 2143959 := bstep (se 1 (by rfl) ⟨1607969, by rfl⟩ : syracuseStep 2143959 = 3215939) B3215939
theorem B5426909 : Blo 2143435 5426909 := bbase (se 3 (by rfl) ⟨1017545, by rfl⟩ : syracuseStep 5426909 = 2035091) (by norm_num)
theorem B3617939 : Blo 2143435 3617939 := bstep (se 1 (by rfl) ⟨2713454, by rfl⟩ : syracuseStep 3617939 = 5426909) B5426909
theorem B2411959 : Blo 2143435 2411959 := bstep (se 1 (by rfl) ⟨1808969, by rfl⟩ : syracuseStep 2411959 = 3617939) B3617939
theorem B3215945 : Blo 2143435 3215945 := bstep (se 2 (by rfl) ⟨1205979, by rfl⟩ : syracuseStep 3215945 = 2411959) B2411959
theorem B2143963 : Blo 2143435 2143963 := bstep (se 1 (by rfl) ⟨1607972, by rfl⟩ : syracuseStep 2143963 = 3215945) B3215945
theorem B4070189 : Blo 2143435 4070189 := bbase (se 3 (by rfl) ⟨763160, by rfl⟩ : syracuseStep 4070189 = 1526321) (by norm_num)
theorem B10853837 : Blo 2143435 10853837 := bstep (se 3 (by rfl) ⟨2035094, by rfl⟩ : syracuseStep 10853837 = 4070189) B4070189
theorem B7235891 : Blo 2143435 7235891 := bstep (se 1 (by rfl) ⟨5426918, by rfl⟩ : syracuseStep 7235891 = 10853837) B10853837
theorem B4823927 : Blo 2143435 4823927 := bstep (se 1 (by rfl) ⟨3617945, by rfl⟩ : syracuseStep 4823927 = 7235891) B7235891
theorem B3215951 : Blo 2143435 3215951 := bstep (se 1 (by rfl) ⟨2411963, by rfl⟩ : syracuseStep 3215951 = 4823927) B4823927
theorem B2143967 : Blo 2143435 2143967 := bstep (se 1 (by rfl) ⟨1607975, by rfl⟩ : syracuseStep 2143967 = 3215951) B3215951
theorem B3215957 : Blo 2143435 3215957 := bbase (se 8 (by rfl) ⟨18843, by rfl⟩ : syracuseStep 3215957 = 37687) (by norm_num)
theorem B2143971 : Blo 2143435 2143971 := bstep (se 1 (by rfl) ⟨1607978, by rfl⟩ : syracuseStep 2143971 = 3215957) B3215957
theorem B9779525 : Blo 2143435 9779525 := bbase (se 4 (by rfl) ⟨916830, by rfl⟩ : syracuseStep 9779525 = 1833661) (by norm_num)
theorem B6519683 : Blo 2143435 6519683 := bstep (se 1 (by rfl) ⟨4889762, by rfl⟩ : syracuseStep 6519683 = 9779525) B9779525
theorem B4346455 : Blo 2143435 4346455 := bstep (se 1 (by rfl) ⟨3259841, by rfl⟩ : syracuseStep 4346455 = 6519683) B6519683
theorem B5795273 : Blo 2143435 5795273 := bstep (se 2 (by rfl) ⟨2173227, by rfl⟩ : syracuseStep 5795273 = 4346455) B4346455
theorem B15454061 : Blo 2143435 15454061 := bstep (se 3 (by rfl) ⟨2897636, by rfl⟩ : syracuseStep 15454061 = 5795273) B5795273
theorem B10302707 : Blo 2143435 10302707 := bstep (se 1 (by rfl) ⟨7727030, by rfl⟩ : syracuseStep 10302707 = 15454061) B15454061
theorem B6868471 : Blo 2143435 6868471 := bstep (se 1 (by rfl) ⟨5151353, by rfl⟩ : syracuseStep 6868471 = 10302707) B10302707
theorem B9157961 : Blo 2143435 9157961 := bstep (se 2 (by rfl) ⟨3434235, by rfl⟩ : syracuseStep 9157961 = 6868471) B6868471
theorem B6105307 : Blo 2143435 6105307 := bstep (se 1 (by rfl) ⟨4578980, by rfl⟩ : syracuseStep 6105307 = 9157961) B9157961
theorem B8140409 : Blo 2143435 8140409 := bstep (se 2 (by rfl) ⟨3052653, by rfl⟩ : syracuseStep 8140409 = 6105307) B6105307
theorem B5426939 : Blo 2143435 5426939 := bstep (se 1 (by rfl) ⟨4070204, by rfl⟩ : syracuseStep 5426939 = 8140409) B8140409
theorem B3617959 : Blo 2143435 3617959 := bstep (se 1 (by rfl) ⟨2713469, by rfl⟩ : syracuseStep 3617959 = 5426939) B5426939
theorem B4823945 : Blo 2143435 4823945 := bstep (se 2 (by rfl) ⟨1808979, by rfl⟩ : syracuseStep 4823945 = 3617959) B3617959
theorem B3215963 : Blo 2143435 3215963 := bstep (se 1 (by rfl) ⟨2411972, by rfl⟩ : syracuseStep 3215963 = 4823945) B4823945
theorem B2143975 : Blo 2143435 2143975 := bstep (se 1 (by rfl) ⟨1607981, by rfl⟩ : syracuseStep 2143975 = 3215963) B3215963
theorem B2411977 : Blo 2143435 2411977 := bbase (se 2 (by rfl) ⟨904491, by rfl⟩ : syracuseStep 2411977 = 1808983) (by norm_num)
theorem B3215969 : Blo 2143435 3215969 := bstep (se 2 (by rfl) ⟨1205988, by rfl⟩ : syracuseStep 3215969 = 2411977) B2411977
theorem B2143979 : Blo 2143435 2143979 := bstep (se 1 (by rfl) ⟨1607984, by rfl⟩ : syracuseStep 2143979 = 3215969) B3215969
theorem B18315989 : Blo 2143435 18315989 := bbase (se 7 (by rfl) ⟨214640, by rfl⟩ : syracuseStep 18315989 = 429281) (by norm_num)
theorem B12210659 : Blo 2143435 12210659 := bstep (se 1 (by rfl) ⟨9157994, by rfl⟩ : syracuseStep 12210659 = 18315989) B18315989
theorem B8140439 : Blo 2143435 8140439 := bstep (se 1 (by rfl) ⟨6105329, by rfl⟩ : syracuseStep 8140439 = 12210659) B12210659
theorem B5426959 : Blo 2143435 5426959 := bstep (se 1 (by rfl) ⟨4070219, by rfl⟩ : syracuseStep 5426959 = 8140439) B8140439
theorem B7235945 : Blo 2143435 7235945 := bstep (se 2 (by rfl) ⟨2713479, by rfl⟩ : syracuseStep 7235945 = 5426959) B5426959
theorem B4823963 : Blo 2143435 4823963 := bstep (se 1 (by rfl) ⟨3617972, by rfl⟩ : syracuseStep 4823963 = 7235945) B7235945
theorem B3215975 : Blo 2143435 3215975 := bstep (se 1 (by rfl) ⟨2411981, by rfl⟩ : syracuseStep 3215975 = 4823963) B4823963
theorem B2143983 : Blo 2143435 2143983 := bstep (se 1 (by rfl) ⟨1607987, by rfl⟩ : syracuseStep 2143983 = 3215975) B3215975
theorem B3215981 : Blo 2143435 3215981 := bbase (se 3 (by rfl) ⟨602996, by rfl⟩ : syracuseStep 3215981 = 1205993) (by norm_num)
theorem B2143987 : Blo 2143435 2143987 := bstep (se 1 (by rfl) ⟨1607990, by rfl⟩ : syracuseStep 2143987 = 3215981) B3215981
theorem B4823981 : Blo 2143435 4823981 := bbase (se 3 (by rfl) ⟨904496, by rfl⟩ : syracuseStep 4823981 = 1808993) (by norm_num)
theorem B3215987 : Blo 2143435 3215987 := bstep (se 1 (by rfl) ⟨2411990, by rfl⟩ : syracuseStep 3215987 = 4823981) B4823981
theorem B2143991 : Blo 2143435 2143991 := bstep (se 1 (by rfl) ⟨1607993, by rfl⟩ : syracuseStep 2143991 = 3215987) B3215987
theorem B6105365 : Blo 2143435 6105365 := bbase (se 6 (by rfl) ⟨143094, by rfl⟩ : syracuseStep 6105365 = 286189) (by norm_num)
theorem B4070243 : Blo 2143435 4070243 := bstep (se 1 (by rfl) ⟨3052682, by rfl⟩ : syracuseStep 4070243 = 6105365) B6105365
theorem B2713495 : Blo 2143435 2713495 := bstep (se 1 (by rfl) ⟨2035121, by rfl⟩ : syracuseStep 2713495 = 4070243) B4070243
theorem B3617993 : Blo 2143435 3617993 := bstep (se 2 (by rfl) ⟨1356747, by rfl⟩ : syracuseStep 3617993 = 2713495) B2713495
theorem B2411995 : Blo 2143435 2411995 := bstep (se 1 (by rfl) ⟨1808996, by rfl⟩ : syracuseStep 2411995 = 3617993) B3617993
theorem B3215993 : Blo 2143435 3215993 := bstep (se 2 (by rfl) ⟨1205997, by rfl⟩ : syracuseStep 3215993 = 2411995) B2411995
theorem B2143995 : Blo 2143435 2143995 := bstep (se 1 (by rfl) ⟨1607996, by rfl⟩ : syracuseStep 2143995 = 3215993) B3215993
theorem B3259877 : Blo 2143435 3259877 := bbase (se 4 (by rfl) ⟨305613, by rfl⟩ : syracuseStep 3259877 = 611227) (by norm_num)
theorem B8693005 : Blo 2143435 8693005 := bstep (se 3 (by rfl) ⟨1629938, by rfl⟩ : syracuseStep 8693005 = 3259877) B3259877
theorem B11590673 : Blo 2143435 11590673 := bstep (se 2 (by rfl) ⟨4346502, by rfl⟩ : syracuseStep 11590673 = 8693005) B8693005
theorem B30908461 : Blo 2143435 30908461 := bstep (se 3 (by rfl) ⟨5795336, by rfl⟩ : syracuseStep 30908461 = 11590673) B11590673
theorem B41211281 : Blo 2143435 41211281 := bstep (se 2 (by rfl) ⟨15454230, by rfl⟩ : syracuseStep 41211281 = 30908461) B30908461
theorem B27474187 : Blo 2143435 27474187 := bstep (se 1 (by rfl) ⟨20605640, by rfl⟩ : syracuseStep 27474187 = 41211281) B41211281
theorem B36632249 : Blo 2143435 36632249 := bstep (se 2 (by rfl) ⟨13737093, by rfl⟩ : syracuseStep 36632249 = 27474187) B27474187
theorem B24421499 : Blo 2143435 24421499 := bstep (se 1 (by rfl) ⟨18316124, by rfl⟩ : syracuseStep 24421499 = 36632249) B36632249
theorem B16280999 : Blo 2143435 16280999 := bstep (se 1 (by rfl) ⟨12210749, by rfl⟩ : syracuseStep 16280999 = 24421499) B24421499
theorem B10853999 : Blo 2143435 10853999 := bstep (se 1 (by rfl) ⟨8140499, by rfl⟩ : syracuseStep 10853999 = 16280999) B16280999
theorem B7235999 : Blo 2143435 7235999 := bstep (se 1 (by rfl) ⟨5426999, by rfl⟩ : syracuseStep 7235999 = 10853999) B10853999
theorem B4823999 : Blo 2143435 4823999 := bstep (se 1 (by rfl) ⟨3617999, by rfl⟩ : syracuseStep 4823999 = 7235999) B7235999
theorem B3215999 : Blo 2143435 3215999 := bstep (se 1 (by rfl) ⟨2411999, by rfl⟩ : syracuseStep 3215999 = 4823999) B4823999
theorem B2143999 : Blo 2143435 2143999 := bstep (se 1 (by rfl) ⟨1607999, by rfl⟩ : syracuseStep 2143999 = 3215999) B3215999
theorem B3216005 : Blo 2143435 3216005 := bbase (se 4 (by rfl) ⟨301500, by rfl⟩ : syracuseStep 3216005 = 603001) (by norm_num)
theorem B2144003 : Blo 2143435 2144003 := bstep (se 1 (by rfl) ⟨1608002, by rfl⟩ : syracuseStep 2144003 = 3216005) B3216005
theorem B3618013 : Blo 2143435 3618013 := bbase (se 3 (by rfl) ⟨678377, by rfl⟩ : syracuseStep 3618013 = 1356755) (by norm_num)
theorem B4824017 : Blo 2143435 4824017 := bstep (se 2 (by rfl) ⟨1809006, by rfl⟩ : syracuseStep 4824017 = 3618013) B3618013
theorem B3216011 : Blo 2143435 3216011 := bstep (se 1 (by rfl) ⟨2412008, by rfl⟩ : syracuseStep 3216011 = 4824017) B4824017
theorem B2144007 : Blo 2143435 2144007 := bstep (se 1 (by rfl) ⟨1608005, by rfl⟩ : syracuseStep 2144007 = 3216011) B3216011
theorem B2412013 : Blo 2143435 2412013 := bbase (se 3 (by rfl) ⟨452252, by rfl⟩ : syracuseStep 2412013 = 904505) (by norm_num)
theorem B3216017 : Blo 2143435 3216017 := bstep (se 2 (by rfl) ⟨1206006, by rfl⟩ : syracuseStep 3216017 = 2412013) B2412013
theorem B2144011 : Blo 2143435 2144011 := bstep (se 1 (by rfl) ⟨1608008, by rfl⟩ : syracuseStep 2144011 = 3216017) B3216017
theorem B7236053 : Blo 2143435 7236053 := bbase (se 7 (by rfl) ⟨84797, by rfl⟩ : syracuseStep 7236053 = 169595) (by norm_num)
theorem B4824035 : Blo 2143435 4824035 := bstep (se 1 (by rfl) ⟨3618026, by rfl⟩ : syracuseStep 4824035 = 7236053) B7236053
theorem B3216023 : Blo 2143435 3216023 := bstep (se 1 (by rfl) ⟨2412017, by rfl⟩ : syracuseStep 3216023 = 4824035) B4824035
theorem B2144015 : Blo 2143435 2144015 := bstep (se 1 (by rfl) ⟨1608011, by rfl⟩ : syracuseStep 2144015 = 3216023) B3216023
theorem B3216029 : Blo 2143435 3216029 := bbase (se 3 (by rfl) ⟨603005, by rfl⟩ : syracuseStep 3216029 = 1206011) (by norm_num)
theorem B2144019 : Blo 2143435 2144019 := bstep (se 1 (by rfl) ⟨1608014, by rfl⟩ : syracuseStep 2144019 = 3216029) B3216029
theorem B4824053 : Blo 2143435 4824053 := bbase (se 5 (by rfl) ⟨226127, by rfl⟩ : syracuseStep 4824053 = 452255) (by norm_num)
theorem B3216035 : Blo 2143435 3216035 := bstep (se 1 (by rfl) ⟨2412026, by rfl⟩ : syracuseStep 3216035 = 4824053) B4824053
theorem B2144023 : Blo 2143435 2144023 := bstep (se 1 (by rfl) ⟨1608017, by rfl⟩ : syracuseStep 2144023 = 3216035) B3216035
theorem B23181653 : Blo 2143435 23181653 := bbase (se 10 (by rfl) ⟨33957, by rfl⟩ : syracuseStep 23181653 = 67915) (by norm_num)
theorem B61817741 : Blo 2143435 61817741 := bstep (se 3 (by rfl) ⟨11590826, by rfl⟩ : syracuseStep 61817741 = 23181653) B23181653
theorem B41211827 : Blo 2143435 41211827 := bstep (se 1 (by rfl) ⟨30908870, by rfl⟩ : syracuseStep 41211827 = 61817741) B61817741
theorem B27474551 : Blo 2143435 27474551 := bstep (se 1 (by rfl) ⟨20605913, by rfl⟩ : syracuseStep 27474551 = 41211827) B41211827
theorem B18316367 : Blo 2143435 18316367 := bstep (se 1 (by rfl) ⟨13737275, by rfl⟩ : syracuseStep 18316367 = 27474551) B27474551
theorem B12210911 : Blo 2143435 12210911 := bstep (se 1 (by rfl) ⟨9158183, by rfl⟩ : syracuseStep 12210911 = 18316367) B18316367
theorem B8140607 : Blo 2143435 8140607 := bstep (se 1 (by rfl) ⟨6105455, by rfl⟩ : syracuseStep 8140607 = 12210911) B12210911
theorem B5427071 : Blo 2143435 5427071 := bstep (se 1 (by rfl) ⟨4070303, by rfl⟩ : syracuseStep 5427071 = 8140607) B8140607
theorem B3618047 : Blo 2143435 3618047 := bstep (se 1 (by rfl) ⟨2713535, by rfl⟩ : syracuseStep 3618047 = 5427071) B5427071
theorem B2412031 : Blo 2143435 2412031 := bstep (se 1 (by rfl) ⟨1809023, by rfl⟩ : syracuseStep 2412031 = 3618047) B3618047
theorem B3216041 : Blo 2143435 3216041 := bstep (se 2 (by rfl) ⟨1206015, by rfl⟩ : syracuseStep 3216041 = 2412031) B2412031
theorem B2144027 : Blo 2143435 2144027 := bstep (se 1 (by rfl) ⟨1608020, by rfl⟩ : syracuseStep 2144027 = 3216041) B3216041
theorem B3052733 : Blo 2143435 3052733 := bbase (se 3 (by rfl) ⟨572387, by rfl⟩ : syracuseStep 3052733 = 1144775) (by norm_num)
theorem B8140621 : Blo 2143435 8140621 := bstep (se 3 (by rfl) ⟨1526366, by rfl⟩ : syracuseStep 8140621 = 3052733) B3052733
theorem B10854161 : Blo 2143435 10854161 := bstep (se 2 (by rfl) ⟨4070310, by rfl⟩ : syracuseStep 10854161 = 8140621) B8140621
theorem B7236107 : Blo 2143435 7236107 := bstep (se 1 (by rfl) ⟨5427080, by rfl⟩ : syracuseStep 7236107 = 10854161) B10854161
theorem B4824071 : Blo 2143435 4824071 := bstep (se 1 (by rfl) ⟨3618053, by rfl⟩ : syracuseStep 4824071 = 7236107) B7236107
theorem B3216047 : Blo 2143435 3216047 := bstep (se 1 (by rfl) ⟨2412035, by rfl⟩ : syracuseStep 3216047 = 4824071) B4824071
theorem B2144031 : Blo 2143435 2144031 := bstep (se 1 (by rfl) ⟨1608023, by rfl⟩ : syracuseStep 2144031 = 3216047) B3216047
theorem B3216053 : Blo 2143435 3216053 := bbase (se 5 (by rfl) ⟨150752, by rfl⟩ : syracuseStep 3216053 = 301505) (by norm_num)
theorem B2144035 : Blo 2143435 2144035 := bstep (se 1 (by rfl) ⟨1608026, by rfl⟩ : syracuseStep 2144035 = 3216053) B3216053
theorem B5427101 : Blo 2143435 5427101 := bbase (se 3 (by rfl) ⟨1017581, by rfl⟩ : syracuseStep 5427101 = 2035163) (by norm_num)
theorem B3618067 : Blo 2143435 3618067 := bstep (se 1 (by rfl) ⟨2713550, by rfl⟩ : syracuseStep 3618067 = 5427101) B5427101
theorem B4824089 : Blo 2143435 4824089 := bstep (se 2 (by rfl) ⟨1809033, by rfl⟩ : syracuseStep 4824089 = 3618067) B3618067
theorem B3216059 : Blo 2143435 3216059 := bstep (se 1 (by rfl) ⟨2412044, by rfl⟩ : syracuseStep 3216059 = 4824089) B4824089
theorem B2144039 : Blo 2143435 2144039 := bstep (se 1 (by rfl) ⟨1608029, by rfl⟩ : syracuseStep 2144039 = 3216059) B3216059
theorem B2412049 : Blo 2143435 2412049 := bbase (se 2 (by rfl) ⟨904518, by rfl⟩ : syracuseStep 2412049 = 1809037) (by norm_num)
theorem B3216065 : Blo 2143435 3216065 := bstep (se 2 (by rfl) ⟨1206024, by rfl⟩ : syracuseStep 3216065 = 2412049) B2412049
theorem B2144043 : Blo 2143435 2144043 := bstep (se 1 (by rfl) ⟨1608032, by rfl⟩ : syracuseStep 2144043 = 3216065) B3216065
theorem B4070341 : Blo 2143435 4070341 := bbase (se 4 (by rfl) ⟨381594, by rfl⟩ : syracuseStep 4070341 = 763189) (by norm_num)
theorem B5427121 : Blo 2143435 5427121 := bstep (se 2 (by rfl) ⟨2035170, by rfl⟩ : syracuseStep 5427121 = 4070341) B4070341
theorem B7236161 : Blo 2143435 7236161 := bstep (se 2 (by rfl) ⟨2713560, by rfl⟩ : syracuseStep 7236161 = 5427121) B5427121
theorem B4824107 : Blo 2143435 4824107 := bstep (se 1 (by rfl) ⟨3618080, by rfl⟩ : syracuseStep 4824107 = 7236161) B7236161
theorem B3216071 : Blo 2143435 3216071 := bstep (se 1 (by rfl) ⟨2412053, by rfl⟩ : syracuseStep 3216071 = 4824107) B4824107
theorem B2144047 : Blo 2143435 2144047 := bstep (se 1 (by rfl) ⟨1608035, by rfl⟩ : syracuseStep 2144047 = 3216071) B3216071
theorem B3216077 : Blo 2143435 3216077 := bbase (se 3 (by rfl) ⟨603014, by rfl⟩ : syracuseStep 3216077 = 1206029) (by norm_num)
theorem B2144051 : Blo 2143435 2144051 := bstep (se 1 (by rfl) ⟨1608038, by rfl⟩ : syracuseStep 2144051 = 3216077) B3216077
theorem B4824125 : Blo 2143435 4824125 := bbase (se 3 (by rfl) ⟨904523, by rfl⟩ : syracuseStep 4824125 = 1809047) (by norm_num)
theorem B3216083 : Blo 2143435 3216083 := bstep (se 1 (by rfl) ⟨2412062, by rfl⟩ : syracuseStep 3216083 = 4824125) B4824125
theorem B2144055 : Blo 2143435 2144055 := bstep (se 1 (by rfl) ⟨1608041, by rfl⟩ : syracuseStep 2144055 = 3216083) B3216083
theorem B3618101 : Blo 2143435 3618101 := bbase (se 5 (by rfl) ⟨169598, by rfl⟩ : syracuseStep 3618101 = 339197) (by norm_num)
theorem B2412067 : Blo 2143435 2412067 := bstep (se 1 (by rfl) ⟨1809050, by rfl⟩ : syracuseStep 2412067 = 3618101) B3618101
theorem B3216089 : Blo 2143435 3216089 := bstep (se 2 (by rfl) ⟨1206033, by rfl⟩ : syracuseStep 3216089 = 2412067) B2412067
theorem B2144059 : Blo 2143435 2144059 := bstep (se 1 (by rfl) ⟨1608044, by rfl⟩ : syracuseStep 2144059 = 3216089) B3216089
theorem B6105557 : Blo 2143435 6105557 := bbase (se 7 (by rfl) ⟨71549, by rfl⟩ : syracuseStep 6105557 = 143099) (by norm_num)
theorem B16281485 : Blo 2143435 16281485 := bstep (se 3 (by rfl) ⟨3052778, by rfl⟩ : syracuseStep 16281485 = 6105557) B6105557
theorem B10854323 : Blo 2143435 10854323 := bstep (se 1 (by rfl) ⟨8140742, by rfl⟩ : syracuseStep 10854323 = 16281485) B16281485
theorem B7236215 : Blo 2143435 7236215 := bstep (se 1 (by rfl) ⟨5427161, by rfl⟩ : syracuseStep 7236215 = 10854323) B10854323
theorem B4824143 : Blo 2143435 4824143 := bstep (se 1 (by rfl) ⟨3618107, by rfl⟩ : syracuseStep 4824143 = 7236215) B7236215
theorem B3216095 : Blo 2143435 3216095 := bstep (se 1 (by rfl) ⟨2412071, by rfl⟩ : syracuseStep 3216095 = 4824143) B4824143
theorem B2144063 : Blo 2143435 2144063 := bstep (se 1 (by rfl) ⟨1608047, by rfl⟩ : syracuseStep 2144063 = 3216095) B3216095
theorem B3216101 : Blo 2143435 3216101 := bbase (se 4 (by rfl) ⟨301509, by rfl⟩ : syracuseStep 3216101 = 603019) (by norm_num)
theorem B2144067 : Blo 2143435 2144067 := bstep (se 1 (by rfl) ⟨1608050, by rfl⟩ : syracuseStep 2144067 = 3216101) B3216101
theorem B2289593 : Blo 2143435 2289593 := bbase (se 2 (by rfl) ⟨858597, by rfl⟩ : syracuseStep 2289593 = 1717195) (by norm_num)
theorem B6105581 : Blo 2143435 6105581 := bstep (se 3 (by rfl) ⟨1144796, by rfl⟩ : syracuseStep 6105581 = 2289593) B2289593
theorem B4070387 : Blo 2143435 4070387 := bstep (se 1 (by rfl) ⟨3052790, by rfl⟩ : syracuseStep 4070387 = 6105581) B6105581
theorem B2713591 : Blo 2143435 2713591 := bstep (se 1 (by rfl) ⟨2035193, by rfl⟩ : syracuseStep 2713591 = 4070387) B4070387
theorem B3618121 : Blo 2143435 3618121 := bstep (se 2 (by rfl) ⟨1356795, by rfl⟩ : syracuseStep 3618121 = 2713591) B2713591
theorem B4824161 : Blo 2143435 4824161 := bstep (se 2 (by rfl) ⟨1809060, by rfl⟩ : syracuseStep 4824161 = 3618121) B3618121
theorem B3216107 : Blo 2143435 3216107 := bstep (se 1 (by rfl) ⟨2412080, by rfl⟩ : syracuseStep 3216107 = 4824161) B4824161
theorem B2144071 : Blo 2143435 2144071 := bstep (se 1 (by rfl) ⟨1608053, by rfl⟩ : syracuseStep 2144071 = 3216107) B3216107
theorem B2412085 : Blo 2143435 2412085 := bbase (se 5 (by rfl) ⟨113066, by rfl⟩ : syracuseStep 2412085 = 226133) (by norm_num)
theorem B3216113 : Blo 2143435 3216113 := bstep (se 2 (by rfl) ⟨1206042, by rfl⟩ : syracuseStep 3216113 = 2412085) B2412085
theorem B2144075 : Blo 2143435 2144075 := bstep (se 1 (by rfl) ⟨1608056, by rfl⟩ : syracuseStep 2144075 = 3216113) B3216113
theorem B2713601 : Blo 2143435 2713601 := bbase (se 2 (by rfl) ⟨1017600, by rfl⟩ : syracuseStep 2713601 = 2035201) (by norm_num)
theorem B7236269 : Blo 2143435 7236269 := bstep (se 3 (by rfl) ⟨1356800, by rfl⟩ : syracuseStep 7236269 = 2713601) B2713601
theorem B4824179 : Blo 2143435 4824179 := bstep (se 1 (by rfl) ⟨3618134, by rfl⟩ : syracuseStep 4824179 = 7236269) B7236269
theorem B3216119 : Blo 2143435 3216119 := bstep (se 1 (by rfl) ⟨2412089, by rfl⟩ : syracuseStep 3216119 = 4824179) B4824179
theorem B2144079 : Blo 2143435 2144079 := bstep (se 1 (by rfl) ⟨1608059, by rfl⟩ : syracuseStep 2144079 = 3216119) B3216119
theorem B3216125 : Blo 2143435 3216125 := bbase (se 3 (by rfl) ⟨603023, by rfl⟩ : syracuseStep 3216125 = 1206047) (by norm_num)
theorem B2144083 : Blo 2143435 2144083 := bstep (se 1 (by rfl) ⟨1608062, by rfl⟩ : syracuseStep 2144083 = 3216125) B3216125
theorem B4824197 : Blo 2143435 4824197 := bbase (se 4 (by rfl) ⟨452268, by rfl⟩ : syracuseStep 4824197 = 904537) (by norm_num)
theorem B3216131 : Blo 2143435 3216131 := bstep (se 1 (by rfl) ⟨2412098, by rfl⟩ : syracuseStep 3216131 = 4824197) B4824197
theorem B2144087 : Blo 2143435 2144087 := bstep (se 1 (by rfl) ⟨1608065, by rfl⟩ : syracuseStep 2144087 = 3216131) B3216131
theorem B4579229 : Blo 2143435 4579229 := bbase (se 3 (by rfl) ⟨858605, by rfl⟩ : syracuseStep 4579229 = 1717211) (by norm_num)
theorem B3052819 : Blo 2143435 3052819 := bstep (se 1 (by rfl) ⟨2289614, by rfl⟩ : syracuseStep 3052819 = 4579229) B4579229
theorem B4070425 : Blo 2143435 4070425 := bstep (se 2 (by rfl) ⟨1526409, by rfl⟩ : syracuseStep 4070425 = 3052819) B3052819
theorem B5427233 : Blo 2143435 5427233 := bstep (se 2 (by rfl) ⟨2035212, by rfl⟩ : syracuseStep 5427233 = 4070425) B4070425
theorem B3618155 : Blo 2143435 3618155 := bstep (se 1 (by rfl) ⟨2713616, by rfl⟩ : syracuseStep 3618155 = 5427233) B5427233
theorem B2412103 : Blo 2143435 2412103 := bstep (se 1 (by rfl) ⟨1809077, by rfl⟩ : syracuseStep 2412103 = 3618155) B3618155
theorem B3216137 : Blo 2143435 3216137 := bstep (se 2 (by rfl) ⟨1206051, by rfl⟩ : syracuseStep 3216137 = 2412103) B2412103
theorem B2144091 : Blo 2143435 2144091 := bstep (se 1 (by rfl) ⟨1608068, by rfl⟩ : syracuseStep 2144091 = 3216137) B3216137
theorem B10854485 : Blo 2143435 10854485 := bbase (se 8 (by rfl) ⟨63600, by rfl⟩ : syracuseStep 10854485 = 127201) (by norm_num)
theorem B7236323 : Blo 2143435 7236323 := bstep (se 1 (by rfl) ⟨5427242, by rfl⟩ : syracuseStep 7236323 = 10854485) B10854485
theorem B4824215 : Blo 2143435 4824215 := bstep (se 1 (by rfl) ⟨3618161, by rfl⟩ : syracuseStep 4824215 = 7236323) B7236323
theorem B3216143 : Blo 2143435 3216143 := bstep (se 1 (by rfl) ⟨2412107, by rfl⟩ : syracuseStep 3216143 = 4824215) B4824215
theorem B2144095 : Blo 2143435 2144095 := bstep (se 1 (by rfl) ⟨1608071, by rfl⟩ : syracuseStep 2144095 = 3216143) B3216143
theorem B3216149 : Blo 2143435 3216149 := bbase (se 6 (by rfl) ⟨75378, by rfl⟩ : syracuseStep 3216149 = 150757) (by norm_num)
theorem B2144099 : Blo 2143435 2144099 := bstep (se 1 (by rfl) ⟨1608074, by rfl⟩ : syracuseStep 2144099 = 3216149) B3216149
theorem B2173357 : Blo 2143435 2173357 := bbase (se 3 (by rfl) ⟨407504, by rfl⟩ : syracuseStep 2173357 = 815009) (by norm_num)
theorem B11591237 : Blo 2143435 11591237 := bstep (se 4 (by rfl) ⟨1086678, by rfl⟩ : syracuseStep 11591237 = 2173357) B2173357
theorem B7727491 : Blo 2143435 7727491 := bstep (se 1 (by rfl) ⟨5795618, by rfl⟩ : syracuseStep 7727491 = 11591237) B11591237
theorem B41213285 : Blo 2143435 41213285 := bstep (se 4 (by rfl) ⟨3863745, by rfl⟩ : syracuseStep 41213285 = 7727491) B7727491
theorem B27475523 : Blo 2143435 27475523 := bstep (se 1 (by rfl) ⟨20606642, by rfl⟩ : syracuseStep 27475523 = 41213285) B41213285
theorem B18317015 : Blo 2143435 18317015 := bstep (se 1 (by rfl) ⟨13737761, by rfl⟩ : syracuseStep 18317015 = 27475523) B27475523
theorem B12211343 : Blo 2143435 12211343 := bstep (se 1 (by rfl) ⟨9158507, by rfl⟩ : syracuseStep 12211343 = 18317015) B18317015
theorem B8140895 : Blo 2143435 8140895 := bstep (se 1 (by rfl) ⟨6105671, by rfl⟩ : syracuseStep 8140895 = 12211343) B12211343
theorem B5427263 : Blo 2143435 5427263 := bstep (se 1 (by rfl) ⟨4070447, by rfl⟩ : syracuseStep 5427263 = 8140895) B8140895
theorem B3618175 : Blo 2143435 3618175 := bstep (se 1 (by rfl) ⟨2713631, by rfl⟩ : syracuseStep 3618175 = 5427263) B5427263
theorem B4824233 : Blo 2143435 4824233 := bstep (se 2 (by rfl) ⟨1809087, by rfl⟩ : syracuseStep 4824233 = 3618175) B3618175
theorem B3216155 : Blo 2143435 3216155 := bstep (se 1 (by rfl) ⟨2412116, by rfl⟩ : syracuseStep 3216155 = 4824233) B4824233
theorem B2144103 : Blo 2143435 2144103 := bstep (se 1 (by rfl) ⟨1608077, by rfl⟩ : syracuseStep 2144103 = 3216155) B3216155
theorem B2412121 : Blo 2143435 2412121 := bbase (se 2 (by rfl) ⟨904545, by rfl⟩ : syracuseStep 2412121 = 1809091) (by norm_num)
theorem B3216161 : Blo 2143435 3216161 := bstep (se 2 (by rfl) ⟨1206060, by rfl⟩ : syracuseStep 3216161 = 2412121) B2412121
theorem B2144107 : Blo 2143435 2144107 := bstep (se 1 (by rfl) ⟨1608080, by rfl⟩ : syracuseStep 2144107 = 3216161) B3216161
theorem B5501333 : Blo 2143435 5501333 := bbase (se 6 (by rfl) ⟨128937, by rfl⟩ : syracuseStep 5501333 = 257875) (by norm_num)
theorem B3667555 : Blo 2143435 3667555 := bstep (se 1 (by rfl) ⟨2750666, by rfl⟩ : syracuseStep 3667555 = 5501333) B5501333
theorem B4890073 : Blo 2143435 4890073 := bstep (se 2 (by rfl) ⟨1833777, by rfl⟩ : syracuseStep 4890073 = 3667555) B3667555
theorem B6520097 : Blo 2143435 6520097 := bstep (se 2 (by rfl) ⟨2445036, by rfl⟩ : syracuseStep 6520097 = 4890073) B4890073
theorem B4346731 : Blo 2143435 4346731 := bstep (se 1 (by rfl) ⟨3260048, by rfl⟩ : syracuseStep 4346731 = 6520097) B6520097
theorem B5795641 : Blo 2143435 5795641 := bstep (se 2 (by rfl) ⟨2173365, by rfl⟩ : syracuseStep 5795641 = 4346731) B4346731
theorem B7727521 : Blo 2143435 7727521 := bstep (se 2 (by rfl) ⟨2897820, by rfl⟩ : syracuseStep 7727521 = 5795641) B5795641
theorem B10303361 : Blo 2143435 10303361 := bstep (se 2 (by rfl) ⟨3863760, by rfl⟩ : syracuseStep 10303361 = 7727521) B7727521
theorem B6868907 : Blo 2143435 6868907 := bstep (se 1 (by rfl) ⟨5151680, by rfl⟩ : syracuseStep 6868907 = 10303361) B10303361
theorem B4579271 : Blo 2143435 4579271 := bstep (se 1 (by rfl) ⟨3434453, by rfl⟩ : syracuseStep 4579271 = 6868907) B6868907
theorem B3052847 : Blo 2143435 3052847 := bstep (se 1 (by rfl) ⟨2289635, by rfl⟩ : syracuseStep 3052847 = 4579271) B4579271
theorem B8140925 : Blo 2143435 8140925 := bstep (se 3 (by rfl) ⟨1526423, by rfl⟩ : syracuseStep 8140925 = 3052847) B3052847
theorem B5427283 : Blo 2143435 5427283 := bstep (se 1 (by rfl) ⟨4070462, by rfl⟩ : syracuseStep 5427283 = 8140925) B8140925
theorem B7236377 : Blo 2143435 7236377 := bstep (se 2 (by rfl) ⟨2713641, by rfl⟩ : syracuseStep 7236377 = 5427283) B5427283
theorem B4824251 : Blo 2143435 4824251 := bstep (se 1 (by rfl) ⟨3618188, by rfl⟩ : syracuseStep 4824251 = 7236377) B7236377
theorem B3216167 : Blo 2143435 3216167 := bstep (se 1 (by rfl) ⟨2412125, by rfl⟩ : syracuseStep 3216167 = 4824251) B4824251
theorem B2144111 : Blo 2143435 2144111 := bstep (se 1 (by rfl) ⟨1608083, by rfl⟩ : syracuseStep 2144111 = 3216167) B3216167
theorem B3216173 : Blo 2143435 3216173 := bbase (se 3 (by rfl) ⟨603032, by rfl⟩ : syracuseStep 3216173 = 1206065) (by norm_num)
theorem B2144115 : Blo 2143435 2144115 := bstep (se 1 (by rfl) ⟨1608086, by rfl⟩ : syracuseStep 2144115 = 3216173) B3216173
theorem B4824269 : Blo 2143435 4824269 := bbase (se 3 (by rfl) ⟨904550, by rfl⟩ : syracuseStep 4824269 = 1809101) (by norm_num)
theorem B3216179 : Blo 2143435 3216179 := bstep (se 1 (by rfl) ⟨2412134, by rfl⟩ : syracuseStep 3216179 = 4824269) B4824269
theorem B2144119 : Blo 2143435 2144119 := bstep (se 1 (by rfl) ⟨1608089, by rfl⟩ : syracuseStep 2144119 = 3216179) B3216179
theorem B2713657 : Blo 2143435 2713657 := bbase (se 2 (by rfl) ⟨1017621, by rfl⟩ : syracuseStep 2713657 = 2035243) (by norm_num)
theorem B3618209 : Blo 2143435 3618209 := bstep (se 2 (by rfl) ⟨1356828, by rfl⟩ : syracuseStep 3618209 = 2713657) B2713657
theorem B2412139 : Blo 2143435 2412139 := bstep (se 1 (by rfl) ⟨1809104, by rfl⟩ : syracuseStep 2412139 = 3618209) B3618209
theorem B3216185 : Blo 2143435 3216185 := bstep (se 2 (by rfl) ⟨1206069, by rfl⟩ : syracuseStep 3216185 = 2412139) B2412139
theorem B2144123 : Blo 2143435 2144123 := bstep (se 1 (by rfl) ⟨1608092, by rfl⟩ : syracuseStep 2144123 = 3216185) B3216185
theorem B3863789 : Blo 2143435 3863789 := bbase (se 3 (by rfl) ⟨724460, by rfl⟩ : syracuseStep 3863789 = 1448921) (by norm_num)
theorem B2575859 : Blo 2143435 2575859 := bstep (se 1 (by rfl) ⟨1931894, by rfl⟩ : syracuseStep 2575859 = 3863789) B3863789
theorem B6868957 : Blo 2143435 6868957 := bstep (se 3 (by rfl) ⟨1287929, by rfl⟩ : syracuseStep 6868957 = 2575859) B2575859
theorem B9158609 : Blo 2143435 9158609 := bstep (se 2 (by rfl) ⟨3434478, by rfl⟩ : syracuseStep 9158609 = 6868957) B6868957
theorem B24422957 : Blo 2143435 24422957 := bstep (se 3 (by rfl) ⟨4579304, by rfl⟩ : syracuseStep 24422957 = 9158609) B9158609
theorem B16281971 : Blo 2143435 16281971 := bstep (se 1 (by rfl) ⟨12211478, by rfl⟩ : syracuseStep 16281971 = 24422957) B24422957
theorem B10854647 : Blo 2143435 10854647 := bstep (se 1 (by rfl) ⟨8140985, by rfl⟩ : syracuseStep 10854647 = 16281971) B16281971
theorem B7236431 : Blo 2143435 7236431 := bstep (se 1 (by rfl) ⟨5427323, by rfl⟩ : syracuseStep 7236431 = 10854647) B10854647
theorem B4824287 : Blo 2143435 4824287 := bstep (se 1 (by rfl) ⟨3618215, by rfl⟩ : syracuseStep 4824287 = 7236431) B7236431
theorem B3216191 : Blo 2143435 3216191 := bstep (se 1 (by rfl) ⟨2412143, by rfl⟩ : syracuseStep 3216191 = 4824287) B4824287
theorem B2144127 : Blo 2143435 2144127 := bstep (se 1 (by rfl) ⟨1608095, by rfl⟩ : syracuseStep 2144127 = 3216191) B3216191
theorem B3216197 : Blo 2143435 3216197 := bbase (se 4 (by rfl) ⟨301518, by rfl⟩ : syracuseStep 3216197 = 603037) (by norm_num)
theorem B2144131 : Blo 2143435 2144131 := bstep (se 1 (by rfl) ⟨1608098, by rfl⟩ : syracuseStep 2144131 = 3216197) B3216197
theorem B3618229 : Blo 2143435 3618229 := bbase (se 5 (by rfl) ⟨169604, by rfl⟩ : syracuseStep 3618229 = 339209) (by norm_num)
theorem B4824305 : Blo 2143435 4824305 := bstep (se 2 (by rfl) ⟨1809114, by rfl⟩ : syracuseStep 4824305 = 3618229) B3618229
theorem B3216203 : Blo 2143435 3216203 := bstep (se 1 (by rfl) ⟨2412152, by rfl⟩ : syracuseStep 3216203 = 4824305) B4824305
theorem B2144135 : Blo 2143435 2144135 := bstep (se 1 (by rfl) ⟨1608101, by rfl⟩ : syracuseStep 2144135 = 3216203) B3216203
theorem B2412157 : Blo 2143435 2412157 := bbase (se 3 (by rfl) ⟨452279, by rfl⟩ : syracuseStep 2412157 = 904559) (by norm_num)
theorem B3216209 : Blo 2143435 3216209 := bstep (se 2 (by rfl) ⟨1206078, by rfl⟩ : syracuseStep 3216209 = 2412157) B2412157
theorem B2144139 : Blo 2143435 2144139 := bstep (se 1 (by rfl) ⟨1608104, by rfl⟩ : syracuseStep 2144139 = 3216209) B3216209
theorem B7236485 : Blo 2143435 7236485 := bbase (se 4 (by rfl) ⟨678420, by rfl⟩ : syracuseStep 7236485 = 1356841) (by norm_num)
theorem B4824323 : Blo 2143435 4824323 := bstep (se 1 (by rfl) ⟨3618242, by rfl⟩ : syracuseStep 4824323 = 7236485) B7236485
theorem B3216215 : Blo 2143435 3216215 := bstep (se 1 (by rfl) ⟨2412161, by rfl⟩ : syracuseStep 3216215 = 4824323) B4824323
theorem B2144143 : Blo 2143435 2144143 := bstep (se 1 (by rfl) ⟨1608107, by rfl⟩ : syracuseStep 2144143 = 3216215) B3216215
theorem B3216221 : Blo 2143435 3216221 := bbase (se 3 (by rfl) ⟨603041, by rfl⟩ : syracuseStep 3216221 = 1206083) (by norm_num)
theorem B2144147 : Blo 2143435 2144147 := bstep (se 1 (by rfl) ⟨1608110, by rfl⟩ : syracuseStep 2144147 = 3216221) B3216221
theorem B4824341 : Blo 2143435 4824341 := bbase (se 6 (by rfl) ⟨113070, by rfl⟩ : syracuseStep 4824341 = 226141) (by norm_num)
theorem B3216227 : Blo 2143435 3216227 := bstep (se 1 (by rfl) ⟨2412170, by rfl⟩ : syracuseStep 3216227 = 4824341) B4824341
theorem B2144151 : Blo 2143435 2144151 := bstep (se 1 (by rfl) ⟨1608113, by rfl⟩ : syracuseStep 2144151 = 3216227) B3216227
theorem B8141093 : Blo 2143435 8141093 := bbase (se 4 (by rfl) ⟨763227, by rfl⟩ : syracuseStep 8141093 = 1526455) (by norm_num)
theorem B5427395 : Blo 2143435 5427395 := bstep (se 1 (by rfl) ⟨4070546, by rfl⟩ : syracuseStep 5427395 = 8141093) B8141093
theorem B3618263 : Blo 2143435 3618263 := bstep (se 1 (by rfl) ⟨2713697, by rfl⟩ : syracuseStep 3618263 = 5427395) B5427395
theorem B2412175 : Blo 2143435 2412175 := bstep (se 1 (by rfl) ⟨1809131, by rfl⟩ : syracuseStep 2412175 = 3618263) B3618263
theorem B3216233 : Blo 2143435 3216233 := bstep (se 2 (by rfl) ⟨1206087, by rfl⟩ : syracuseStep 3216233 = 2412175) B2412175
theorem B2144155 : Blo 2143435 2144155 := bstep (se 1 (by rfl) ⟨1608116, by rfl⟩ : syracuseStep 2144155 = 3216233) B3216233
theorem B4579373 : Blo 2143435 4579373 := bbase (se 3 (by rfl) ⟨858632, by rfl⟩ : syracuseStep 4579373 = 1717265) (by norm_num)
theorem B12211661 : Blo 2143435 12211661 := bstep (se 3 (by rfl) ⟨2289686, by rfl⟩ : syracuseStep 12211661 = 4579373) B4579373
theorem B8141107 : Blo 2143435 8141107 := bstep (se 1 (by rfl) ⟨6105830, by rfl⟩ : syracuseStep 8141107 = 12211661) B12211661
theorem B10854809 : Blo 2143435 10854809 := bstep (se 2 (by rfl) ⟨4070553, by rfl⟩ : syracuseStep 10854809 = 8141107) B8141107
theorem B7236539 : Blo 2143435 7236539 := bstep (se 1 (by rfl) ⟨5427404, by rfl⟩ : syracuseStep 7236539 = 10854809) B10854809
theorem B4824359 : Blo 2143435 4824359 := bstep (se 1 (by rfl) ⟨3618269, by rfl⟩ : syracuseStep 4824359 = 7236539) B7236539
theorem B3216239 : Blo 2143435 3216239 := bstep (se 1 (by rfl) ⟨2412179, by rfl⟩ : syracuseStep 3216239 = 4824359) B4824359
theorem B2144159 : Blo 2143435 2144159 := bstep (se 1 (by rfl) ⟨1608119, by rfl⟩ : syracuseStep 2144159 = 3216239) B3216239
theorem B3216245 : Blo 2143435 3216245 := bbase (se 5 (by rfl) ⟨150761, by rfl⟩ : syracuseStep 3216245 = 301523) (by norm_num)
theorem B2144163 : Blo 2143435 2144163 := bstep (se 1 (by rfl) ⟨1608122, by rfl⟩ : syracuseStep 2144163 = 3216245) B3216245
theorem B7335301 : Blo 2143435 7335301 := bbase (se 4 (by rfl) ⟨687684, by rfl⟩ : syracuseStep 7335301 = 1375369) (by norm_num)
theorem B9780401 : Blo 2143435 9780401 := bstep (se 2 (by rfl) ⟨3667650, by rfl⟩ : syracuseStep 9780401 = 7335301) B7335301
theorem B6520267 : Blo 2143435 6520267 := bstep (se 1 (by rfl) ⟨4890200, by rfl⟩ : syracuseStep 6520267 = 9780401) B9780401
theorem B34774757 : Blo 2143435 34774757 := bstep (se 4 (by rfl) ⟨3260133, by rfl⟩ : syracuseStep 34774757 = 6520267) B6520267
theorem B23183171 : Blo 2143435 23183171 := bstep (se 1 (by rfl) ⟨17387378, by rfl⟩ : syracuseStep 23183171 = 34774757) B34774757
theorem B15455447 : Blo 2143435 15455447 := bstep (se 1 (by rfl) ⟨11591585, by rfl⟩ : syracuseStep 15455447 = 23183171) B23183171
theorem B10303631 : Blo 2143435 10303631 := bstep (se 1 (by rfl) ⟨7727723, by rfl⟩ : syracuseStep 10303631 = 15455447) B15455447
theorem B6869087 : Blo 2143435 6869087 := bstep (se 1 (by rfl) ⟨5151815, by rfl⟩ : syracuseStep 6869087 = 10303631) B10303631
theorem B4579391 : Blo 2143435 4579391 := bstep (se 1 (by rfl) ⟨3434543, by rfl⟩ : syracuseStep 4579391 = 6869087) B6869087
theorem B3052927 : Blo 2143435 3052927 := bstep (se 1 (by rfl) ⟨2289695, by rfl⟩ : syracuseStep 3052927 = 4579391) B4579391
theorem B4070569 : Blo 2143435 4070569 := bstep (se 2 (by rfl) ⟨1526463, by rfl⟩ : syracuseStep 4070569 = 3052927) B3052927
theorem B5427425 : Blo 2143435 5427425 := bstep (se 2 (by rfl) ⟨2035284, by rfl⟩ : syracuseStep 5427425 = 4070569) B4070569
theorem B3618283 : Blo 2143435 3618283 := bstep (se 1 (by rfl) ⟨2713712, by rfl⟩ : syracuseStep 3618283 = 5427425) B5427425
theorem B4824377 : Blo 2143435 4824377 := bstep (se 2 (by rfl) ⟨1809141, by rfl⟩ : syracuseStep 4824377 = 3618283) B3618283
theorem B3216251 : Blo 2143435 3216251 := bstep (se 1 (by rfl) ⟨2412188, by rfl⟩ : syracuseStep 3216251 = 4824377) B4824377
theorem B2144167 : Blo 2143435 2144167 := bstep (se 1 (by rfl) ⟨1608125, by rfl⟩ : syracuseStep 2144167 = 3216251) B3216251
theorem B2412193 : Blo 2143435 2412193 := bbase (se 2 (by rfl) ⟨904572, by rfl⟩ : syracuseStep 2412193 = 1809145) (by norm_num)
theorem B3216257 : Blo 2143435 3216257 := bstep (se 2 (by rfl) ⟨1206096, by rfl⟩ : syracuseStep 3216257 = 2412193) B2412193
theorem B2144171 : Blo 2143435 2144171 := bstep (se 1 (by rfl) ⟨1608128, by rfl⟩ : syracuseStep 2144171 = 3216257) B3216257
theorem B5427445 : Blo 2143435 5427445 := bbase (se 5 (by rfl) ⟨254411, by rfl⟩ : syracuseStep 5427445 = 508823) (by norm_num)
theorem B7236593 : Blo 2143435 7236593 := bstep (se 2 (by rfl) ⟨2713722, by rfl⟩ : syracuseStep 7236593 = 5427445) B5427445
theorem B4824395 : Blo 2143435 4824395 := bstep (se 1 (by rfl) ⟨3618296, by rfl⟩ : syracuseStep 4824395 = 7236593) B7236593
theorem B3216263 : Blo 2143435 3216263 := bstep (se 1 (by rfl) ⟨2412197, by rfl⟩ : syracuseStep 3216263 = 4824395) B4824395
theorem B2144175 : Blo 2143435 2144175 := bstep (se 1 (by rfl) ⟨1608131, by rfl⟩ : syracuseStep 2144175 = 3216263) B3216263
theorem B3216269 : Blo 2143435 3216269 := bbase (se 3 (by rfl) ⟨603050, by rfl⟩ : syracuseStep 3216269 = 1206101) (by norm_num)
theorem B2144179 : Blo 2143435 2144179 := bstep (se 1 (by rfl) ⟨1608134, by rfl⟩ : syracuseStep 2144179 = 3216269) B3216269
theorem B4824413 : Blo 2143435 4824413 := bbase (se 3 (by rfl) ⟨904577, by rfl⟩ : syracuseStep 4824413 = 1809155) (by norm_num)
theorem B3216275 : Blo 2143435 3216275 := bstep (se 1 (by rfl) ⟨2412206, by rfl⟩ : syracuseStep 3216275 = 4824413) B4824413
theorem B2144183 : Blo 2143435 2144183 := bstep (se 1 (by rfl) ⟨1608137, by rfl⟩ : syracuseStep 2144183 = 3216275) B3216275
theorem B3618317 : Blo 2143435 3618317 := bbase (se 3 (by rfl) ⟨678434, by rfl⟩ : syracuseStep 3618317 = 1356869) (by norm_num)
theorem B2412211 : Blo 2143435 2412211 := bstep (se 1 (by rfl) ⟨1809158, by rfl⟩ : syracuseStep 2412211 = 3618317) B3618317
theorem B3216281 : Blo 2143435 3216281 := bstep (se 2 (by rfl) ⟨1206105, by rfl⟩ : syracuseStep 3216281 = 2412211) B2412211
theorem B2144187 : Blo 2143435 2144187 := bstep (se 1 (by rfl) ⟨1608140, by rfl⟩ : syracuseStep 2144187 = 3216281) B3216281
theorem B3434581 : Blo 2143435 3434581 := bbase (se 8 (by rfl) ⟨20124, by rfl⟩ : syracuseStep 3434581 = 40249) (by norm_num)
theorem B18317765 : Blo 2143435 18317765 := bstep (se 4 (by rfl) ⟨1717290, by rfl⟩ : syracuseStep 18317765 = 3434581) B3434581
theorem B12211843 : Blo 2143435 12211843 := bstep (se 1 (by rfl) ⟨9158882, by rfl⟩ : syracuseStep 12211843 = 18317765) B18317765
theorem B16282457 : Blo 2143435 16282457 := bstep (se 2 (by rfl) ⟨6105921, by rfl⟩ : syracuseStep 16282457 = 12211843) B12211843
theorem B10854971 : Blo 2143435 10854971 := bstep (se 1 (by rfl) ⟨8141228, by rfl⟩ : syracuseStep 10854971 = 16282457) B16282457
theorem B7236647 : Blo 2143435 7236647 := bstep (se 1 (by rfl) ⟨5427485, by rfl⟩ : syracuseStep 7236647 = 10854971) B10854971
theorem B4824431 : Blo 2143435 4824431 := bstep (se 1 (by rfl) ⟨3618323, by rfl⟩ : syracuseStep 4824431 = 7236647) B7236647
theorem B3216287 : Blo 2143435 3216287 := bstep (se 1 (by rfl) ⟨2412215, by rfl⟩ : syracuseStep 3216287 = 4824431) B4824431
theorem B2144191 : Blo 2143435 2144191 := bstep (se 1 (by rfl) ⟨1608143, by rfl⟩ : syracuseStep 2144191 = 3216287) B3216287
theorem B3216293 : Blo 2143435 3216293 := bbase (se 4 (by rfl) ⟨301527, by rfl⟩ : syracuseStep 3216293 = 603055) (by norm_num)
theorem B2144195 : Blo 2143435 2144195 := bstep (se 1 (by rfl) ⟨1608146, by rfl⟩ : syracuseStep 2144195 = 3216293) B3216293
theorem B2713753 : Blo 2143435 2713753 := bbase (se 2 (by rfl) ⟨1017657, by rfl⟩ : syracuseStep 2713753 = 2035315) (by norm_num)
theorem B3618337 : Blo 2143435 3618337 := bstep (se 2 (by rfl) ⟨1356876, by rfl⟩ : syracuseStep 3618337 = 2713753) B2713753
theorem B4824449 : Blo 2143435 4824449 := bstep (se 2 (by rfl) ⟨1809168, by rfl⟩ : syracuseStep 4824449 = 3618337) B3618337
theorem B3216299 : Blo 2143435 3216299 := bstep (se 1 (by rfl) ⟨2412224, by rfl⟩ : syracuseStep 3216299 = 4824449) B4824449
theorem B2144199 : Blo 2143435 2144199 := bstep (se 1 (by rfl) ⟨1608149, by rfl⟩ : syracuseStep 2144199 = 3216299) B3216299
theorem B2412229 : Blo 2143435 2412229 := bbase (se 4 (by rfl) ⟨226146, by rfl⟩ : syracuseStep 2412229 = 452293) (by norm_num)
theorem B3216305 : Blo 2143435 3216305 := bstep (se 2 (by rfl) ⟨1206114, by rfl⟩ : syracuseStep 3216305 = 2412229) B2412229
theorem B2144203 : Blo 2143435 2144203 := bstep (se 1 (by rfl) ⟨1608152, by rfl⟩ : syracuseStep 2144203 = 3216305) B3216305
theorem B4070645 : Blo 2143435 4070645 := bbase (se 5 (by rfl) ⟨190811, by rfl⟩ : syracuseStep 4070645 = 381623) (by norm_num)
theorem B2713763 : Blo 2143435 2713763 := bstep (se 1 (by rfl) ⟨2035322, by rfl⟩ : syracuseStep 2713763 = 4070645) B4070645
theorem B7236701 : Blo 2143435 7236701 := bstep (se 3 (by rfl) ⟨1356881, by rfl⟩ : syracuseStep 7236701 = 2713763) B2713763
theorem B4824467 : Blo 2143435 4824467 := bstep (se 1 (by rfl) ⟨3618350, by rfl⟩ : syracuseStep 4824467 = 7236701) B7236701
theorem B3216311 : Blo 2143435 3216311 := bstep (se 1 (by rfl) ⟨2412233, by rfl⟩ : syracuseStep 3216311 = 4824467) B4824467
theorem B2144207 : Blo 2143435 2144207 := bstep (se 1 (by rfl) ⟨1608155, by rfl⟩ : syracuseStep 2144207 = 3216311) B3216311
theorem B3216317 : Blo 2143435 3216317 := bbase (se 3 (by rfl) ⟨603059, by rfl⟩ : syracuseStep 3216317 = 1206119) (by norm_num)
theorem B2144211 : Blo 2143435 2144211 := bstep (se 1 (by rfl) ⟨1608158, by rfl⟩ : syracuseStep 2144211 = 3216317) B3216317
theorem B4824485 : Blo 2143435 4824485 := bbase (se 4 (by rfl) ⟨452295, by rfl⟩ : syracuseStep 4824485 = 904591) (by norm_num)
theorem B3216323 : Blo 2143435 3216323 := bstep (se 1 (by rfl) ⟨2412242, by rfl⟩ : syracuseStep 3216323 = 4824485) B4824485
theorem B2144215 : Blo 2143435 2144215 := bstep (se 1 (by rfl) ⟨1608161, by rfl⟩ : syracuseStep 2144215 = 3216323) B3216323
theorem B5427557 : Blo 2143435 5427557 := bbase (se 4 (by rfl) ⟨508833, by rfl⟩ : syracuseStep 5427557 = 1017667) (by norm_num)
theorem B3618371 : Blo 2143435 3618371 := bstep (se 1 (by rfl) ⟨2713778, by rfl⟩ : syracuseStep 3618371 = 5427557) B5427557
theorem B2412247 : Blo 2143435 2412247 := bstep (se 1 (by rfl) ⟨1809185, by rfl⟩ : syracuseStep 2412247 = 3618371) B3618371
theorem B3216329 : Blo 2143435 3216329 := bstep (se 2 (by rfl) ⟨1206123, by rfl⟩ : syracuseStep 3216329 = 2412247) B2412247
theorem B2144219 : Blo 2143435 2144219 := bstep (se 1 (by rfl) ⟨1608164, by rfl⟩ : syracuseStep 2144219 = 3216329) B3216329
theorem B5501621 : Blo 2143435 5501621 := bbase (se 5 (by rfl) ⟨257888, by rfl⟩ : syracuseStep 5501621 = 515777) (by norm_num)
theorem B14670989 : Blo 2143435 14670989 := bstep (se 3 (by rfl) ⟨2750810, by rfl⟩ : syracuseStep 14670989 = 5501621) B5501621
theorem B9780659 : Blo 2143435 9780659 := bstep (se 1 (by rfl) ⟨7335494, by rfl⟩ : syracuseStep 9780659 = 14670989) B14670989
theorem B6520439 : Blo 2143435 6520439 := bstep (se 1 (by rfl) ⟨4890329, by rfl⟩ : syracuseStep 6520439 = 9780659) B9780659
theorem B4346959 : Blo 2143435 4346959 := bstep (se 1 (by rfl) ⟨3260219, by rfl⟩ : syracuseStep 4346959 = 6520439) B6520439
theorem B5795945 : Blo 2143435 5795945 := bstep (se 2 (by rfl) ⟨2173479, by rfl⟩ : syracuseStep 5795945 = 4346959) B4346959
theorem B3863963 : Blo 2143435 3863963 := bstep (se 1 (by rfl) ⟨2897972, by rfl⟩ : syracuseStep 3863963 = 5795945) B5795945
theorem B2575975 : Blo 2143435 2575975 := bstep (se 1 (by rfl) ⟨1931981, by rfl⟩ : syracuseStep 2575975 = 3863963) B3863963
theorem B3434633 : Blo 2143435 3434633 := bstep (se 2 (by rfl) ⟨1287987, by rfl⟩ : syracuseStep 3434633 = 2575975) B2575975
theorem B2289755 : Blo 2143435 2289755 := bstep (se 1 (by rfl) ⟨1717316, by rfl⟩ : syracuseStep 2289755 = 3434633) B3434633
theorem B6106013 : Blo 2143435 6106013 := bstep (se 3 (by rfl) ⟨1144877, by rfl⟩ : syracuseStep 6106013 = 2289755) B2289755
theorem B4070675 : Blo 2143435 4070675 := bstep (se 1 (by rfl) ⟨3053006, by rfl⟩ : syracuseStep 4070675 = 6106013) B6106013
theorem B10855133 : Blo 2143435 10855133 := bstep (se 3 (by rfl) ⟨2035337, by rfl⟩ : syracuseStep 10855133 = 4070675) B4070675
theorem B7236755 : Blo 2143435 7236755 := bstep (se 1 (by rfl) ⟨5427566, by rfl⟩ : syracuseStep 7236755 = 10855133) B10855133
theorem B4824503 : Blo 2143435 4824503 := bstep (se 1 (by rfl) ⟨3618377, by rfl⟩ : syracuseStep 4824503 = 7236755) B7236755
theorem B3216335 : Blo 2143435 3216335 := bstep (se 1 (by rfl) ⟨2412251, by rfl⟩ : syracuseStep 3216335 = 4824503) B4824503
theorem B2144223 : Blo 2143435 2144223 := bstep (se 1 (by rfl) ⟨1608167, by rfl⟩ : syracuseStep 2144223 = 3216335) B3216335
theorem B3216341 : Blo 2143435 3216341 := bbase (se 7 (by rfl) ⟨37691, by rfl⟩ : syracuseStep 3216341 = 75383) (by norm_num)
theorem B2144227 : Blo 2143435 2144227 := bstep (se 1 (by rfl) ⟨1608170, by rfl⟩ : syracuseStep 2144227 = 3216341) B3216341
theorem B8141381 : Blo 2143435 8141381 := bbase (se 4 (by rfl) ⟨763254, by rfl⟩ : syracuseStep 8141381 = 1526509) (by norm_num)
theorem B5427587 : Blo 2143435 5427587 := bstep (se 1 (by rfl) ⟨4070690, by rfl⟩ : syracuseStep 5427587 = 8141381) B8141381
theorem B3618391 : Blo 2143435 3618391 := bstep (se 1 (by rfl) ⟨2713793, by rfl⟩ : syracuseStep 3618391 = 5427587) B5427587
theorem B4824521 : Blo 2143435 4824521 := bstep (se 2 (by rfl) ⟨1809195, by rfl⟩ : syracuseStep 4824521 = 3618391) B3618391
theorem B3216347 : Blo 2143435 3216347 := bstep (se 1 (by rfl) ⟨2412260, by rfl⟩ : syracuseStep 3216347 = 4824521) B4824521
theorem B2144231 : Blo 2143435 2144231 := bstep (se 1 (by rfl) ⟨1608173, by rfl⟩ : syracuseStep 2144231 = 3216347) B3216347
theorem B2412265 : Blo 2143435 2412265 := bbase (se 2 (by rfl) ⟨904599, by rfl⟩ : syracuseStep 2412265 = 1809199) (by norm_num)
theorem B3216353 : Blo 2143435 3216353 := bstep (se 2 (by rfl) ⟨1206132, by rfl⟩ : syracuseStep 3216353 = 2412265) B2412265
theorem B2144235 : Blo 2143435 2144235 := bstep (se 1 (by rfl) ⟨1608176, by rfl⟩ : syracuseStep 2144235 = 3216353) B3216353
theorem B12212117 : Blo 2143435 12212117 := bbase (se 6 (by rfl) ⟨286221, by rfl⟩ : syracuseStep 12212117 = 572443) (by norm_num)
theorem B8141411 : Blo 2143435 8141411 := bstep (se 1 (by rfl) ⟨6106058, by rfl⟩ : syracuseStep 8141411 = 12212117) B12212117
theorem B5427607 : Blo 2143435 5427607 := bstep (se 1 (by rfl) ⟨4070705, by rfl⟩ : syracuseStep 5427607 = 8141411) B8141411
theorem B7236809 : Blo 2143435 7236809 := bstep (se 2 (by rfl) ⟨2713803, by rfl⟩ : syracuseStep 7236809 = 5427607) B5427607
theorem B4824539 : Blo 2143435 4824539 := bstep (se 1 (by rfl) ⟨3618404, by rfl⟩ : syracuseStep 4824539 = 7236809) B7236809
theorem B3216359 : Blo 2143435 3216359 := bstep (se 1 (by rfl) ⟨2412269, by rfl⟩ : syracuseStep 3216359 = 4824539) B4824539
theorem B2144239 : Blo 2143435 2144239 := bstep (se 1 (by rfl) ⟨1608179, by rfl⟩ : syracuseStep 2144239 = 3216359) B3216359
theorem B3216365 : Blo 2143435 3216365 := bbase (se 3 (by rfl) ⟨603068, by rfl⟩ : syracuseStep 3216365 = 1206137) (by norm_num)
theorem B2144243 : Blo 2143435 2144243 := bstep (se 1 (by rfl) ⟨1608182, by rfl⟩ : syracuseStep 2144243 = 3216365) B3216365
theorem B4824557 : Blo 2143435 4824557 := bbase (se 3 (by rfl) ⟨904604, by rfl⟩ : syracuseStep 4824557 = 1809209) (by norm_num)
theorem B3216371 : Blo 2143435 3216371 := bstep (se 1 (by rfl) ⟨2412278, by rfl⟩ : syracuseStep 3216371 = 4824557) B4824557
theorem B2144247 : Blo 2143435 2144247 := bstep (se 1 (by rfl) ⟨1608185, by rfl⟩ : syracuseStep 2144247 = 3216371) B3216371
theorem B2576009 : Blo 2143435 2576009 := bbase (se 2 (by rfl) ⟨966003, by rfl⟩ : syracuseStep 2576009 = 1932007) (by norm_num)
theorem B6869357 : Blo 2143435 6869357 := bstep (se 3 (by rfl) ⟨1288004, by rfl⟩ : syracuseStep 6869357 = 2576009) B2576009
theorem B4579571 : Blo 2143435 4579571 := bstep (se 1 (by rfl) ⟨3434678, by rfl⟩ : syracuseStep 4579571 = 6869357) B6869357
theorem B3053047 : Blo 2143435 3053047 := bstep (se 1 (by rfl) ⟨2289785, by rfl⟩ : syracuseStep 3053047 = 4579571) B4579571
theorem B4070729 : Blo 2143435 4070729 := bstep (se 2 (by rfl) ⟨1526523, by rfl⟩ : syracuseStep 4070729 = 3053047) B3053047
theorem B2713819 : Blo 2143435 2713819 := bstep (se 1 (by rfl) ⟨2035364, by rfl⟩ : syracuseStep 2713819 = 4070729) B4070729
theorem B3618425 : Blo 2143435 3618425 := bstep (se 2 (by rfl) ⟨1356909, by rfl⟩ : syracuseStep 3618425 = 2713819) B2713819
theorem B2412283 : Blo 2143435 2412283 := bstep (se 1 (by rfl) ⟨1809212, by rfl⟩ : syracuseStep 2412283 = 3618425) B3618425
theorem B3216377 : Blo 2143435 3216377 := bstep (se 2 (by rfl) ⟨1206141, by rfl⟩ : syracuseStep 3216377 = 2412283) B2412283
theorem B2144251 : Blo 2143435 2144251 := bstep (se 1 (by rfl) ⟨1608188, by rfl⟩ : syracuseStep 2144251 = 3216377) B3216377
theorem B69552341 : Blo 2143435 69552341 := bbase (se 7 (by rfl) ⟨815066, by rfl⟩ : syracuseStep 69552341 = 1630133) (by norm_num)
theorem B46368227 : Blo 2143435 46368227 := bstep (se 1 (by rfl) ⟨34776170, by rfl⟩ : syracuseStep 46368227 = 69552341) B69552341
theorem B123648605 : Blo 2143435 123648605 := bstep (se 3 (by rfl) ⟨23184113, by rfl⟩ : syracuseStep 123648605 = 46368227) B46368227
theorem B82432403 : Blo 2143435 82432403 := bstep (se 1 (by rfl) ⟨61824302, by rfl⟩ : syracuseStep 82432403 = 123648605) B123648605
theorem B54954935 : Blo 2143435 54954935 := bstep (se 1 (by rfl) ⟨41216201, by rfl⟩ : syracuseStep 54954935 = 82432403) B82432403
theorem B36636623 : Blo 2143435 36636623 := bstep (se 1 (by rfl) ⟨27477467, by rfl⟩ : syracuseStep 36636623 = 54954935) B54954935
theorem B24424415 : Blo 2143435 24424415 := bstep (se 1 (by rfl) ⟨18318311, by rfl⟩ : syracuseStep 24424415 = 36636623) B36636623
theorem B16282943 : Blo 2143435 16282943 := bstep (se 1 (by rfl) ⟨12212207, by rfl⟩ : syracuseStep 16282943 = 24424415) B24424415
theorem B10855295 : Blo 2143435 10855295 := bstep (se 1 (by rfl) ⟨8141471, by rfl⟩ : syracuseStep 10855295 = 16282943) B16282943
theorem B7236863 : Blo 2143435 7236863 := bstep (se 1 (by rfl) ⟨5427647, by rfl⟩ : syracuseStep 7236863 = 10855295) B10855295
theorem B4824575 : Blo 2143435 4824575 := bstep (se 1 (by rfl) ⟨3618431, by rfl⟩ : syracuseStep 4824575 = 7236863) B7236863
theorem B3216383 : Blo 2143435 3216383 := bstep (se 1 (by rfl) ⟨2412287, by rfl⟩ : syracuseStep 3216383 = 4824575) B4824575
theorem B2144255 : Blo 2143435 2144255 := bstep (se 1 (by rfl) ⟨1608191, by rfl⟩ : syracuseStep 2144255 = 3216383) B3216383
theorem B3216389 : Blo 2143435 3216389 := bbase (se 4 (by rfl) ⟨301536, by rfl⟩ : syracuseStep 3216389 = 603073) (by norm_num)
theorem B2144259 : Blo 2143435 2144259 := bstep (se 1 (by rfl) ⟨1608194, by rfl⟩ : syracuseStep 2144259 = 3216389) B3216389
theorem B3618445 : Blo 2143435 3618445 := bbase (se 3 (by rfl) ⟨678458, by rfl⟩ : syracuseStep 3618445 = 1356917) (by norm_num)
theorem B4824593 : Blo 2143435 4824593 := bstep (se 2 (by rfl) ⟨1809222, by rfl⟩ : syracuseStep 4824593 = 3618445) B3618445
theorem B3216395 : Blo 2143435 3216395 := bstep (se 1 (by rfl) ⟨2412296, by rfl⟩ : syracuseStep 3216395 = 4824593) B4824593
theorem B2144263 : Blo 2143435 2144263 := bstep (se 1 (by rfl) ⟨1608197, by rfl⟩ : syracuseStep 2144263 = 3216395) B3216395
theorem B2412301 : Blo 2143435 2412301 := bbase (se 3 (by rfl) ⟨452306, by rfl⟩ : syracuseStep 2412301 = 904613) (by norm_num)
theorem B3216401 : Blo 2143435 3216401 := bstep (se 2 (by rfl) ⟨1206150, by rfl⟩ : syracuseStep 3216401 = 2412301) B2412301
theorem B2144267 : Blo 2143435 2144267 := bstep (se 1 (by rfl) ⟨1608200, by rfl⟩ : syracuseStep 2144267 = 3216401) B3216401
theorem B7236917 : Blo 2143435 7236917 := bbase (se 5 (by rfl) ⟨339230, by rfl⟩ : syracuseStep 7236917 = 678461) (by norm_num)
theorem B4824611 : Blo 2143435 4824611 := bstep (se 1 (by rfl) ⟨3618458, by rfl⟩ : syracuseStep 4824611 = 7236917) B7236917
theorem B3216407 : Blo 2143435 3216407 := bstep (se 1 (by rfl) ⟨2412305, by rfl⟩ : syracuseStep 3216407 = 4824611) B4824611
theorem B2144271 : Blo 2143435 2144271 := bstep (se 1 (by rfl) ⟨1608203, by rfl⟩ : syracuseStep 2144271 = 3216407) B3216407
theorem B3216413 : Blo 2143435 3216413 := bbase (se 3 (by rfl) ⟨603077, by rfl⟩ : syracuseStep 3216413 = 1206155) (by norm_num)
theorem B2144275 : Blo 2143435 2144275 := bstep (se 1 (by rfl) ⟨1608206, by rfl⟩ : syracuseStep 2144275 = 3216413) B3216413
theorem B4824629 : Blo 2143435 4824629 := bbase (se 5 (by rfl) ⟨226154, by rfl⟩ : syracuseStep 4824629 = 452309) (by norm_num)
theorem B3216419 : Blo 2143435 3216419 := bstep (se 1 (by rfl) ⟨2412314, by rfl⟩ : syracuseStep 3216419 = 4824629) B4824629
theorem B2144279 : Blo 2143435 2144279 := bstep (se 1 (by rfl) ⟨1608209, by rfl⟩ : syracuseStep 2144279 = 3216419) B3216419
theorem B2445233 : Blo 2143435 2445233 := bbase (se 2 (by rfl) ⟨916962, by rfl⟩ : syracuseStep 2445233 = 1833925) (by norm_num)
theorem B6520621 : Blo 2143435 6520621 := bstep (se 3 (by rfl) ⟨1222616, by rfl⟩ : syracuseStep 6520621 = 2445233) B2445233
theorem B8694161 : Blo 2143435 8694161 := bstep (se 2 (by rfl) ⟨3260310, by rfl⟩ : syracuseStep 8694161 = 6520621) B6520621
theorem B5796107 : Blo 2143435 5796107 := bstep (se 1 (by rfl) ⟨4347080, by rfl⟩ : syracuseStep 5796107 = 8694161) B8694161
theorem B3864071 : Blo 2143435 3864071 := bstep (se 1 (by rfl) ⟨2898053, by rfl⟩ : syracuseStep 3864071 = 5796107) B5796107
theorem B2576047 : Blo 2143435 2576047 := bstep (se 1 (by rfl) ⟨1932035, by rfl⟩ : syracuseStep 2576047 = 3864071) B3864071
theorem B3434729 : Blo 2143435 3434729 := bstep (se 2 (by rfl) ⟨1288023, by rfl⟩ : syracuseStep 3434729 = 2576047) B2576047
theorem B9159277 : Blo 2143435 9159277 := bstep (se 3 (by rfl) ⟨1717364, by rfl⟩ : syracuseStep 9159277 = 3434729) B3434729
theorem B12212369 : Blo 2143435 12212369 := bstep (se 2 (by rfl) ⟨4579638, by rfl⟩ : syracuseStep 12212369 = 9159277) B9159277
theorem B8141579 : Blo 2143435 8141579 := bstep (se 1 (by rfl) ⟨6106184, by rfl⟩ : syracuseStep 8141579 = 12212369) B12212369
theorem B5427719 : Blo 2143435 5427719 := bstep (se 1 (by rfl) ⟨4070789, by rfl⟩ : syracuseStep 5427719 = 8141579) B8141579
theorem B3618479 : Blo 2143435 3618479 := bstep (se 1 (by rfl) ⟨2713859, by rfl⟩ : syracuseStep 3618479 = 5427719) B5427719
theorem B2412319 : Blo 2143435 2412319 := bstep (se 1 (by rfl) ⟨1809239, by rfl⟩ : syracuseStep 2412319 = 3618479) B3618479
theorem B3216425 : Blo 2143435 3216425 := bstep (se 2 (by rfl) ⟨1206159, by rfl⟩ : syracuseStep 3216425 = 2412319) B2412319
theorem B2144283 : Blo 2143435 2144283 := bstep (se 1 (by rfl) ⟨1608212, by rfl⟩ : syracuseStep 2144283 = 3216425) B3216425
theorem B13926389 : Blo 2143435 13926389 := bbase (se 5 (by rfl) ⟨652799, by rfl⟩ : syracuseStep 13926389 = 1305599) (by norm_num)
theorem B37137037 : Blo 2143435 37137037 := bstep (se 3 (by rfl) ⟨6963194, by rfl⟩ : syracuseStep 37137037 = 13926389) B13926389
theorem B49516049 : Blo 2143435 49516049 := bstep (se 2 (by rfl) ⟨18568518, by rfl⟩ : syracuseStep 49516049 = 37137037) B37137037
theorem B33010699 : Blo 2143435 33010699 := bstep (se 1 (by rfl) ⟨24758024, by rfl⟩ : syracuseStep 33010699 = 49516049) B49516049
theorem B44014265 : Blo 2143435 44014265 := bstep (se 2 (by rfl) ⟨16505349, by rfl⟩ : syracuseStep 44014265 = 33010699) B33010699
theorem B29342843 : Blo 2143435 29342843 := bstep (se 1 (by rfl) ⟨22007132, by rfl⟩ : syracuseStep 29342843 = 44014265) B44014265
theorem B19561895 : Blo 2143435 19561895 := bstep (se 1 (by rfl) ⟨14671421, by rfl⟩ : syracuseStep 19561895 = 29342843) B29342843
theorem B13041263 : Blo 2143435 13041263 := bstep (se 1 (by rfl) ⟨9780947, by rfl⟩ : syracuseStep 13041263 = 19561895) B19561895
theorem B8694175 : Blo 2143435 8694175 := bstep (se 1 (by rfl) ⟨6520631, by rfl⟩ : syracuseStep 8694175 = 13041263) B13041263
theorem B11592233 : Blo 2143435 11592233 := bstep (se 2 (by rfl) ⟨4347087, by rfl⟩ : syracuseStep 11592233 = 8694175) B8694175
theorem B7728155 : Blo 2143435 7728155 := bstep (se 1 (by rfl) ⟨5796116, by rfl⟩ : syracuseStep 7728155 = 11592233) B11592233
theorem B5152103 : Blo 2143435 5152103 := bstep (se 1 (by rfl) ⟨3864077, by rfl⟩ : syracuseStep 5152103 = 7728155) B7728155
theorem B3434735 : Blo 2143435 3434735 := bstep (se 1 (by rfl) ⟨2576051, by rfl⟩ : syracuseStep 3434735 = 5152103) B5152103
theorem B9159293 : Blo 2143435 9159293 := bstep (se 3 (by rfl) ⟨1717367, by rfl⟩ : syracuseStep 9159293 = 3434735) B3434735
theorem B6106195 : Blo 2143435 6106195 := bstep (se 1 (by rfl) ⟨4579646, by rfl⟩ : syracuseStep 6106195 = 9159293) B9159293
theorem B8141593 : Blo 2143435 8141593 := bstep (se 2 (by rfl) ⟨3053097, by rfl⟩ : syracuseStep 8141593 = 6106195) B6106195
theorem B10855457 : Blo 2143435 10855457 := bstep (se 2 (by rfl) ⟨4070796, by rfl⟩ : syracuseStep 10855457 = 8141593) B8141593
theorem B7236971 : Blo 2143435 7236971 := bstep (se 1 (by rfl) ⟨5427728, by rfl⟩ : syracuseStep 7236971 = 10855457) B10855457
theorem B4824647 : Blo 2143435 4824647 := bstep (se 1 (by rfl) ⟨3618485, by rfl⟩ : syracuseStep 4824647 = 7236971) B7236971
theorem B3216431 : Blo 2143435 3216431 := bstep (se 1 (by rfl) ⟨2412323, by rfl⟩ : syracuseStep 3216431 = 4824647) B4824647
theorem B2144287 : Blo 2143435 2144287 := bstep (se 1 (by rfl) ⟨1608215, by rfl⟩ : syracuseStep 2144287 = 3216431) B3216431
theorem B3216437 : Blo 2143435 3216437 := bbase (se 5 (by rfl) ⟨150770, by rfl⟩ : syracuseStep 3216437 = 301541) (by norm_num)
theorem B2144291 : Blo 2143435 2144291 := bstep (se 1 (by rfl) ⟨1608218, by rfl⟩ : syracuseStep 2144291 = 3216437) B3216437
theorem B5427749 : Blo 2143435 5427749 := bbase (se 4 (by rfl) ⟨508851, by rfl⟩ : syracuseStep 5427749 = 1017703) (by norm_num)
theorem B3618499 : Blo 2143435 3618499 := bstep (se 1 (by rfl) ⟨2713874, by rfl⟩ : syracuseStep 3618499 = 5427749) B5427749
theorem B4824665 : Blo 2143435 4824665 := bstep (se 2 (by rfl) ⟨1809249, by rfl⟩ : syracuseStep 4824665 = 3618499) B3618499
theorem B3216443 : Blo 2143435 3216443 := bstep (se 1 (by rfl) ⟨2412332, by rfl⟩ : syracuseStep 3216443 = 4824665) B4824665
theorem B2144295 : Blo 2143435 2144295 := bstep (se 1 (by rfl) ⟨1608221, by rfl⟩ : syracuseStep 2144295 = 3216443) B3216443
theorem B2412337 : Blo 2143435 2412337 := bbase (se 2 (by rfl) ⟨904626, by rfl⟩ : syracuseStep 2412337 = 1809253) (by norm_num)
theorem B3216449 : Blo 2143435 3216449 := bstep (se 2 (by rfl) ⟨1206168, by rfl⟩ : syracuseStep 3216449 = 2412337) B2412337
theorem B2144299 : Blo 2143435 2144299 := bstep (se 1 (by rfl) ⟨1608224, by rfl⟩ : syracuseStep 2144299 = 3216449) B3216449
theorem B3260341 : Blo 2143435 3260341 := bbase (se 5 (by rfl) ⟨152828, by rfl⟩ : syracuseStep 3260341 = 305657) (by norm_num)
theorem B4347121 : Blo 2143435 4347121 := bstep (se 2 (by rfl) ⟨1630170, by rfl⟩ : syracuseStep 4347121 = 3260341) B3260341
theorem B5796161 : Blo 2143435 5796161 := bstep (se 2 (by rfl) ⟨2173560, by rfl⟩ : syracuseStep 5796161 = 4347121) B4347121
theorem B3864107 : Blo 2143435 3864107 := bstep (se 1 (by rfl) ⟨2898080, by rfl⟩ : syracuseStep 3864107 = 5796161) B5796161
theorem B2576071 : Blo 2143435 2576071 := bstep (se 1 (by rfl) ⟨1932053, by rfl⟩ : syracuseStep 2576071 = 3864107) B3864107
theorem B3434761 : Blo 2143435 3434761 := bstep (se 2 (by rfl) ⟨1288035, by rfl⟩ : syracuseStep 3434761 = 2576071) B2576071
theorem B4579681 : Blo 2143435 4579681 := bstep (se 2 (by rfl) ⟨1717380, by rfl⟩ : syracuseStep 4579681 = 3434761) B3434761
theorem B6106241 : Blo 2143435 6106241 := bstep (se 2 (by rfl) ⟨2289840, by rfl⟩ : syracuseStep 6106241 = 4579681) B4579681
theorem B4070827 : Blo 2143435 4070827 := bstep (se 1 (by rfl) ⟨3053120, by rfl⟩ : syracuseStep 4070827 = 6106241) B6106241
theorem B5427769 : Blo 2143435 5427769 := bstep (se 2 (by rfl) ⟨2035413, by rfl⟩ : syracuseStep 5427769 = 4070827) B4070827
theorem B7237025 : Blo 2143435 7237025 := bstep (se 2 (by rfl) ⟨2713884, by rfl⟩ : syracuseStep 7237025 = 5427769) B5427769
theorem B4824683 : Blo 2143435 4824683 := bstep (se 1 (by rfl) ⟨3618512, by rfl⟩ : syracuseStep 4824683 = 7237025) B7237025
theorem B3216455 : Blo 2143435 3216455 := bstep (se 1 (by rfl) ⟨2412341, by rfl⟩ : syracuseStep 3216455 = 4824683) B4824683
theorem B2144303 : Blo 2143435 2144303 := bstep (se 1 (by rfl) ⟨1608227, by rfl⟩ : syracuseStep 2144303 = 3216455) B3216455
theorem B3216461 : Blo 2143435 3216461 := bbase (se 3 (by rfl) ⟨603086, by rfl⟩ : syracuseStep 3216461 = 1206173) (by norm_num)
theorem B2144307 : Blo 2143435 2144307 := bstep (se 1 (by rfl) ⟨1608230, by rfl⟩ : syracuseStep 2144307 = 3216461) B3216461
theorem B4824701 : Blo 2143435 4824701 := bbase (se 3 (by rfl) ⟨904631, by rfl⟩ : syracuseStep 4824701 = 1809263) (by norm_num)
theorem B3216467 : Blo 2143435 3216467 := bstep (se 1 (by rfl) ⟨2412350, by rfl⟩ : syracuseStep 3216467 = 4824701) B4824701
theorem B2144311 : Blo 2143435 2144311 := bstep (se 1 (by rfl) ⟨1608233, by rfl⟩ : syracuseStep 2144311 = 3216467) B3216467
theorem B3618533 : Blo 2143435 3618533 := bbase (se 4 (by rfl) ⟨339237, by rfl⟩ : syracuseStep 3618533 = 678475) (by norm_num)
theorem B2412355 : Blo 2143435 2412355 := bstep (se 1 (by rfl) ⟨1809266, by rfl⟩ : syracuseStep 2412355 = 3618533) B3618533
theorem B3216473 : Blo 2143435 3216473 := bstep (se 2 (by rfl) ⟨1206177, by rfl⟩ : syracuseStep 3216473 = 2412355) B2412355
theorem B2144315 : Blo 2143435 2144315 := bstep (se 1 (by rfl) ⟨1608236, by rfl⟩ : syracuseStep 2144315 = 3216473) B3216473
theorem B6869573 : Blo 2143435 6869573 := bbase (se 4 (by rfl) ⟨644022, by rfl⟩ : syracuseStep 6869573 = 1288045) (by norm_num)
theorem B4579715 : Blo 2143435 4579715 := bstep (se 1 (by rfl) ⟨3434786, by rfl⟩ : syracuseStep 4579715 = 6869573) B6869573
theorem B3053143 : Blo 2143435 3053143 := bstep (se 1 (by rfl) ⟨2289857, by rfl⟩ : syracuseStep 3053143 = 4579715) B4579715
theorem B16283429 : Blo 2143435 16283429 := bstep (se 4 (by rfl) ⟨1526571, by rfl⟩ : syracuseStep 16283429 = 3053143) B3053143
theorem B10855619 : Blo 2143435 10855619 := bstep (se 1 (by rfl) ⟨8141714, by rfl⟩ : syracuseStep 10855619 = 16283429) B16283429
theorem B7237079 : Blo 2143435 7237079 := bstep (se 1 (by rfl) ⟨5427809, by rfl⟩ : syracuseStep 7237079 = 10855619) B10855619
theorem B4824719 : Blo 2143435 4824719 := bstep (se 1 (by rfl) ⟨3618539, by rfl⟩ : syracuseStep 4824719 = 7237079) B7237079
theorem B3216479 : Blo 2143435 3216479 := bstep (se 1 (by rfl) ⟨2412359, by rfl⟩ : syracuseStep 3216479 = 4824719) B4824719
theorem B2144319 : Blo 2143435 2144319 := bstep (se 1 (by rfl) ⟨1608239, by rfl⟩ : syracuseStep 2144319 = 3216479) B3216479
theorem B3216485 : Blo 2143435 3216485 := bbase (se 4 (by rfl) ⟨301545, by rfl⟩ : syracuseStep 3216485 = 603091) (by norm_num)
theorem B2144323 : Blo 2143435 2144323 := bstep (se 1 (by rfl) ⟨1608242, by rfl⟩ : syracuseStep 2144323 = 3216485) B3216485
theorem B4579733 : Blo 2143435 4579733 := bbase (se 6 (by rfl) ⟨107337, by rfl⟩ : syracuseStep 4579733 = 214675) (by norm_num)
theorem B3053155 : Blo 2143435 3053155 := bstep (se 1 (by rfl) ⟨2289866, by rfl⟩ : syracuseStep 3053155 = 4579733) B4579733
theorem B4070873 : Blo 2143435 4070873 := bstep (se 2 (by rfl) ⟨1526577, by rfl⟩ : syracuseStep 4070873 = 3053155) B3053155
theorem B2713915 : Blo 2143435 2713915 := bstep (se 1 (by rfl) ⟨2035436, by rfl⟩ : syracuseStep 2713915 = 4070873) B4070873
theorem B3618553 : Blo 2143435 3618553 := bstep (se 2 (by rfl) ⟨1356957, by rfl⟩ : syracuseStep 3618553 = 2713915) B2713915
theorem B4824737 : Blo 2143435 4824737 := bstep (se 2 (by rfl) ⟨1809276, by rfl⟩ : syracuseStep 4824737 = 3618553) B3618553
theorem B3216491 : Blo 2143435 3216491 := bstep (se 1 (by rfl) ⟨2412368, by rfl⟩ : syracuseStep 3216491 = 4824737) B4824737
theorem B2144327 : Blo 2143435 2144327 := bstep (se 1 (by rfl) ⟨1608245, by rfl⟩ : syracuseStep 2144327 = 3216491) B3216491
theorem B2412373 : Blo 2143435 2412373 := bbase (se 9 (by rfl) ⟨7067, by rfl⟩ : syracuseStep 2412373 = 14135) (by norm_num)
theorem B3216497 : Blo 2143435 3216497 := bstep (se 2 (by rfl) ⟨1206186, by rfl⟩ : syracuseStep 3216497 = 2412373) B2412373
theorem B2144331 : Blo 2143435 2144331 := bstep (se 1 (by rfl) ⟨1608248, by rfl⟩ : syracuseStep 2144331 = 3216497) B3216497
theorem B2713925 : Blo 2143435 2713925 := bbase (se 4 (by rfl) ⟨254430, by rfl⟩ : syracuseStep 2713925 = 508861) (by norm_num)
theorem B7237133 : Blo 2143435 7237133 := bstep (se 3 (by rfl) ⟨1356962, by rfl⟩ : syracuseStep 7237133 = 2713925) B2713925
theorem B4824755 : Blo 2143435 4824755 := bstep (se 1 (by rfl) ⟨3618566, by rfl⟩ : syracuseStep 4824755 = 7237133) B7237133
theorem B3216503 : Blo 2143435 3216503 := bstep (se 1 (by rfl) ⟨2412377, by rfl⟩ : syracuseStep 3216503 = 4824755) B4824755
theorem B2144335 : Blo 2143435 2144335 := bstep (se 1 (by rfl) ⟨1608251, by rfl⟩ : syracuseStep 2144335 = 3216503) B3216503
theorem B3216509 : Blo 2143435 3216509 := bbase (se 3 (by rfl) ⟨603095, by rfl⟩ : syracuseStep 3216509 = 1206191) (by norm_num)
theorem B2144339 : Blo 2143435 2144339 := bstep (se 1 (by rfl) ⟨1608254, by rfl⟩ : syracuseStep 2144339 = 3216509) B3216509
theorem B4824773 : Blo 2143435 4824773 := bbase (se 4 (by rfl) ⟨452322, by rfl⟩ : syracuseStep 4824773 = 904645) (by norm_num)
theorem B3216515 : Blo 2143435 3216515 := bstep (se 1 (by rfl) ⟨2412386, by rfl⟩ : syracuseStep 3216515 = 4824773) B4824773
theorem B2144343 : Blo 2143435 2144343 := bstep (se 1 (by rfl) ⟨1608257, by rfl⟩ : syracuseStep 2144343 = 3216515) B3216515
theorem B14116789 : Blo 2143435 14116789 := bbase (se 5 (by rfl) ⟨661724, by rfl⟩ : syracuseStep 14116789 = 1323449) (by norm_num)
theorem B18822385 : Blo 2143435 18822385 := bstep (se 2 (by rfl) ⟨7058394, by rfl⟩ : syracuseStep 18822385 = 14116789) B14116789
theorem B25096513 : Blo 2143435 25096513 := bstep (se 2 (by rfl) ⟨9411192, by rfl⟩ : syracuseStep 25096513 = 18822385) B18822385
theorem B33462017 : Blo 2143435 33462017 := bstep (se 2 (by rfl) ⟨12548256, by rfl⟩ : syracuseStep 33462017 = 25096513) B25096513
theorem B22308011 : Blo 2143435 22308011 := bstep (se 1 (by rfl) ⟨16731008, by rfl⟩ : syracuseStep 22308011 = 33462017) B33462017
theorem B14872007 : Blo 2143435 14872007 := bstep (se 1 (by rfl) ⟨11154005, by rfl⟩ : syracuseStep 14872007 = 22308011) B22308011
theorem B9914671 : Blo 2143435 9914671 := bstep (se 1 (by rfl) ⟨7436003, by rfl⟩ : syracuseStep 9914671 = 14872007) B14872007
theorem B13219561 : Blo 2143435 13219561 := bstep (se 2 (by rfl) ⟨4957335, by rfl⟩ : syracuseStep 13219561 = 9914671) B9914671
theorem B17626081 : Blo 2143435 17626081 := bstep (se 2 (by rfl) ⟨6609780, by rfl⟩ : syracuseStep 17626081 = 13219561) B13219561
theorem B23501441 : Blo 2143435 23501441 := bstep (se 2 (by rfl) ⟨8813040, by rfl⟩ : syracuseStep 23501441 = 17626081) B17626081
theorem B15667627 : Blo 2143435 15667627 := bstep (se 1 (by rfl) ⟨11750720, by rfl⟩ : syracuseStep 15667627 = 23501441) B23501441
theorem B20890169 : Blo 2143435 20890169 := bstep (se 2 (by rfl) ⟨7833813, by rfl⟩ : syracuseStep 20890169 = 15667627) B15667627
theorem B13926779 : Blo 2143435 13926779 := bstep (se 1 (by rfl) ⟨10445084, by rfl⟩ : syracuseStep 13926779 = 20890169) B20890169
theorem B9284519 : Blo 2143435 9284519 := bstep (se 1 (by rfl) ⟨6963389, by rfl⟩ : syracuseStep 9284519 = 13926779) B13926779
theorem B6189679 : Blo 2143435 6189679 := bstep (se 1 (by rfl) ⟨4642259, by rfl⟩ : syracuseStep 6189679 = 9284519) B9284519
theorem B33011621 : Blo 2143435 33011621 := bstep (se 4 (by rfl) ⟨3094839, by rfl⟩ : syracuseStep 33011621 = 6189679) B6189679
theorem B22007747 : Blo 2143435 22007747 := bstep (se 1 (by rfl) ⟨16505810, by rfl⟩ : syracuseStep 22007747 = 33011621) B33011621
theorem B58687325 : Blo 2143435 58687325 := bstep (se 3 (by rfl) ⟨11003873, by rfl⟩ : syracuseStep 58687325 = 22007747) B22007747
theorem B39124883 : Blo 2143435 39124883 := bstep (se 1 (by rfl) ⟨29343662, by rfl⟩ : syracuseStep 39124883 = 58687325) B58687325
theorem B104333021 : Blo 2143435 104333021 := bstep (se 3 (by rfl) ⟨19562441, by rfl⟩ : syracuseStep 104333021 = 39124883) B39124883
theorem B69555347 : Blo 2143435 69555347 := bstep (se 1 (by rfl) ⟨52166510, by rfl⟩ : syracuseStep 69555347 = 104333021) B104333021
theorem B46370231 : Blo 2143435 46370231 := bstep (se 1 (by rfl) ⟨34777673, by rfl⟩ : syracuseStep 46370231 = 69555347) B69555347
theorem B30913487 : Blo 2143435 30913487 := bstep (se 1 (by rfl) ⟨23185115, by rfl⟩ : syracuseStep 30913487 = 46370231) B46370231
theorem B20608991 : Blo 2143435 20608991 := bstep (se 1 (by rfl) ⟨15456743, by rfl⟩ : syracuseStep 20608991 = 30913487) B30913487
theorem B13739327 : Blo 2143435 13739327 := bstep (se 1 (by rfl) ⟨10304495, by rfl⟩ : syracuseStep 13739327 = 20608991) B20608991
theorem B9159551 : Blo 2143435 9159551 := bstep (se 1 (by rfl) ⟨6869663, by rfl⟩ : syracuseStep 9159551 = 13739327) B13739327
theorem B6106367 : Blo 2143435 6106367 := bstep (se 1 (by rfl) ⟨4579775, by rfl⟩ : syracuseStep 6106367 = 9159551) B9159551
theorem B4070911 : Blo 2143435 4070911 := bstep (se 1 (by rfl) ⟨3053183, by rfl⟩ : syracuseStep 4070911 = 6106367) B6106367
theorem B5427881 : Blo 2143435 5427881 := bstep (se 2 (by rfl) ⟨2035455, by rfl⟩ : syracuseStep 5427881 = 4070911) B4070911
theorem B3618587 : Blo 2143435 3618587 := bstep (se 1 (by rfl) ⟨2713940, by rfl⟩ : syracuseStep 3618587 = 5427881) B5427881
theorem B2412391 : Blo 2143435 2412391 := bstep (se 1 (by rfl) ⟨1809293, by rfl⟩ : syracuseStep 2412391 = 3618587) B3618587
theorem B3216521 : Blo 2143435 3216521 := bstep (se 2 (by rfl) ⟨1206195, by rfl⟩ : syracuseStep 3216521 = 2412391) B2412391
theorem B2144347 : Blo 2143435 2144347 := bstep (se 1 (by rfl) ⟨1608260, by rfl⟩ : syracuseStep 2144347 = 3216521) B3216521
theorem B10855781 : Blo 2143435 10855781 := bbase (se 4 (by rfl) ⟨1017729, by rfl⟩ : syracuseStep 10855781 = 2035459) (by norm_num)
theorem B7237187 : Blo 2143435 7237187 := bstep (se 1 (by rfl) ⟨5427890, by rfl⟩ : syracuseStep 7237187 = 10855781) B10855781
theorem B4824791 : Blo 2143435 4824791 := bstep (se 1 (by rfl) ⟨3618593, by rfl⟩ : syracuseStep 4824791 = 7237187) B7237187
theorem B3216527 : Blo 2143435 3216527 := bstep (se 1 (by rfl) ⟨2412395, by rfl⟩ : syracuseStep 3216527 = 4824791) B4824791
theorem B2144351 : Blo 2143435 2144351 := bstep (se 1 (by rfl) ⟨1608263, by rfl⟩ : syracuseStep 2144351 = 3216527) B3216527
theorem B3216533 : Blo 2143435 3216533 := bbase (se 6 (by rfl) ⟨75387, by rfl⟩ : syracuseStep 3216533 = 150775) (by norm_num)
theorem B2144355 : Blo 2143435 2144355 := bstep (se 1 (by rfl) ⟨1608266, by rfl⟩ : syracuseStep 2144355 = 3216533) B3216533
theorem B6869701 : Blo 2143435 6869701 := bbase (se 4 (by rfl) ⟨644034, by rfl⟩ : syracuseStep 6869701 = 1288069) (by norm_num)
theorem B9159601 : Blo 2143435 9159601 := bstep (se 2 (by rfl) ⟨3434850, by rfl⟩ : syracuseStep 9159601 = 6869701) B6869701
theorem B12212801 : Blo 2143435 12212801 := bstep (se 2 (by rfl) ⟨4579800, by rfl⟩ : syracuseStep 12212801 = 9159601) B9159601
theorem B8141867 : Blo 2143435 8141867 := bstep (se 1 (by rfl) ⟨6106400, by rfl⟩ : syracuseStep 8141867 = 12212801) B12212801
theorem B5427911 : Blo 2143435 5427911 := bstep (se 1 (by rfl) ⟨4070933, by rfl⟩ : syracuseStep 5427911 = 8141867) B8141867
theorem B3618607 : Blo 2143435 3618607 := bstep (se 1 (by rfl) ⟨2713955, by rfl⟩ : syracuseStep 3618607 = 5427911) B5427911
theorem B4824809 : Blo 2143435 4824809 := bstep (se 2 (by rfl) ⟨1809303, by rfl⟩ : syracuseStep 4824809 = 3618607) B3618607
theorem B3216539 : Blo 2143435 3216539 := bstep (se 1 (by rfl) ⟨2412404, by rfl⟩ : syracuseStep 3216539 = 4824809) B4824809
theorem B2144359 : Blo 2143435 2144359 := bstep (se 1 (by rfl) ⟨1608269, by rfl⟩ : syracuseStep 2144359 = 3216539) B3216539
theorem B2412409 : Blo 2143435 2412409 := bbase (se 2 (by rfl) ⟨904653, by rfl⟩ : syracuseStep 2412409 = 1809307) (by norm_num)
theorem B3216545 : Blo 2143435 3216545 := bstep (se 2 (by rfl) ⟨1206204, by rfl⟩ : syracuseStep 3216545 = 2412409) B2412409
theorem B2144363 : Blo 2143435 2144363 := bstep (se 1 (by rfl) ⟨1608272, by rfl⟩ : syracuseStep 2144363 = 3216545) B3216545
theorem B13041749 : Blo 2143435 13041749 := bbase (se 8 (by rfl) ⟨76416, by rfl⟩ : syracuseStep 13041749 = 152833) (by norm_num)
theorem B8694499 : Blo 2143435 8694499 := bstep (se 1 (by rfl) ⟨6520874, by rfl⟩ : syracuseStep 8694499 = 13041749) B13041749
theorem B11592665 : Blo 2143435 11592665 := bstep (se 2 (by rfl) ⟨4347249, by rfl⟩ : syracuseStep 11592665 = 8694499) B8694499
theorem B7728443 : Blo 2143435 7728443 := bstep (se 1 (by rfl) ⟨5796332, by rfl⟩ : syracuseStep 7728443 = 11592665) B11592665
theorem B5152295 : Blo 2143435 5152295 := bstep (se 1 (by rfl) ⟨3864221, by rfl⟩ : syracuseStep 5152295 = 7728443) B7728443
theorem B13739453 : Blo 2143435 13739453 := bstep (se 3 (by rfl) ⟨2576147, by rfl⟩ : syracuseStep 13739453 = 5152295) B5152295
theorem B9159635 : Blo 2143435 9159635 := bstep (se 1 (by rfl) ⟨6869726, by rfl⟩ : syracuseStep 9159635 = 13739453) B13739453
theorem B6106423 : Blo 2143435 6106423 := bstep (se 1 (by rfl) ⟨4579817, by rfl⟩ : syracuseStep 6106423 = 9159635) B9159635
theorem B8141897 : Blo 2143435 8141897 := bstep (se 2 (by rfl) ⟨3053211, by rfl⟩ : syracuseStep 8141897 = 6106423) B6106423
theorem B5427931 : Blo 2143435 5427931 := bstep (se 1 (by rfl) ⟨4070948, by rfl⟩ : syracuseStep 5427931 = 8141897) B8141897
theorem B7237241 : Blo 2143435 7237241 := bstep (se 2 (by rfl) ⟨2713965, by rfl⟩ : syracuseStep 7237241 = 5427931) B5427931
theorem B4824827 : Blo 2143435 4824827 := bstep (se 1 (by rfl) ⟨3618620, by rfl⟩ : syracuseStep 4824827 = 7237241) B7237241
theorem B3216551 : Blo 2143435 3216551 := bstep (se 1 (by rfl) ⟨2412413, by rfl⟩ : syracuseStep 3216551 = 4824827) B4824827
theorem B2144367 : Blo 2143435 2144367 := bstep (se 1 (by rfl) ⟨1608275, by rfl⟩ : syracuseStep 2144367 = 3216551) B3216551
theorem B3216557 : Blo 2143435 3216557 := bbase (se 3 (by rfl) ⟨603104, by rfl⟩ : syracuseStep 3216557 = 1206209) (by norm_num)
theorem B2144371 : Blo 2143435 2144371 := bstep (se 1 (by rfl) ⟨1608278, by rfl⟩ : syracuseStep 2144371 = 3216557) B3216557
theorem B4824845 : Blo 2143435 4824845 := bbase (se 3 (by rfl) ⟨904658, by rfl⟩ : syracuseStep 4824845 = 1809317) (by norm_num)
theorem B3216563 : Blo 2143435 3216563 := bstep (se 1 (by rfl) ⟨2412422, by rfl⟩ : syracuseStep 3216563 = 4824845) B4824845
theorem B2144375 : Blo 2143435 2144375 := bstep (se 1 (by rfl) ⟨1608281, by rfl⟩ : syracuseStep 2144375 = 3216563) B3216563
theorem B2713981 : Blo 2143435 2713981 := bbase (se 3 (by rfl) ⟨508871, by rfl⟩ : syracuseStep 2713981 = 1017743) (by norm_num)
theorem B3618641 : Blo 2143435 3618641 := bstep (se 2 (by rfl) ⟨1356990, by rfl⟩ : syracuseStep 3618641 = 2713981) B2713981
theorem B2412427 : Blo 2143435 2412427 := bstep (se 1 (by rfl) ⟨1809320, by rfl⟩ : syracuseStep 2412427 = 3618641) B3618641
theorem B3216569 : Blo 2143435 3216569 := bstep (se 2 (by rfl) ⟨1206213, by rfl⟩ : syracuseStep 3216569 = 2412427) B2412427
theorem B2144379 : Blo 2143435 2144379 := bstep (se 1 (by rfl) ⟨1608284, by rfl⟩ : syracuseStep 2144379 = 3216569) B3216569
theorem B5152333 : Blo 2143435 5152333 := bbase (se 3 (by rfl) ⟨966062, by rfl⟩ : syracuseStep 5152333 = 1932125) (by norm_num)
theorem B6869777 : Blo 2143435 6869777 := bstep (se 2 (by rfl) ⟨2576166, by rfl⟩ : syracuseStep 6869777 = 5152333) B5152333
theorem B18319405 : Blo 2143435 18319405 := bstep (se 3 (by rfl) ⟨3434888, by rfl⟩ : syracuseStep 18319405 = 6869777) B6869777
theorem B24425873 : Blo 2143435 24425873 := bstep (se 2 (by rfl) ⟨9159702, by rfl⟩ : syracuseStep 24425873 = 18319405) B18319405
theorem B16283915 : Blo 2143435 16283915 := bstep (se 1 (by rfl) ⟨12212936, by rfl⟩ : syracuseStep 16283915 = 24425873) B24425873
theorem B10855943 : Blo 2143435 10855943 := bstep (se 1 (by rfl) ⟨8141957, by rfl⟩ : syracuseStep 10855943 = 16283915) B16283915
theorem B7237295 : Blo 2143435 7237295 := bstep (se 1 (by rfl) ⟨5427971, by rfl⟩ : syracuseStep 7237295 = 10855943) B10855943
theorem B4824863 : Blo 2143435 4824863 := bstep (se 1 (by rfl) ⟨3618647, by rfl⟩ : syracuseStep 4824863 = 7237295) B7237295
theorem B3216575 : Blo 2143435 3216575 := bstep (se 1 (by rfl) ⟨2412431, by rfl⟩ : syracuseStep 3216575 = 4824863) B4824863
theorem B2144383 : Blo 2143435 2144383 := bstep (se 1 (by rfl) ⟨1608287, by rfl⟩ : syracuseStep 2144383 = 3216575) B3216575
theorem B3216581 : Blo 2143435 3216581 := bbase (se 4 (by rfl) ⟨301554, by rfl⟩ : syracuseStep 3216581 = 603109) (by norm_num)
theorem B2144387 : Blo 2143435 2144387 := bstep (se 1 (by rfl) ⟨1608290, by rfl⟩ : syracuseStep 2144387 = 3216581) B3216581
theorem B3618661 : Blo 2143435 3618661 := bbase (se 4 (by rfl) ⟨339249, by rfl⟩ : syracuseStep 3618661 = 678499) (by norm_num)
theorem B4824881 : Blo 2143435 4824881 := bstep (se 2 (by rfl) ⟨1809330, by rfl⟩ : syracuseStep 4824881 = 3618661) B3618661
theorem B3216587 : Blo 2143435 3216587 := bstep (se 1 (by rfl) ⟨2412440, by rfl⟩ : syracuseStep 3216587 = 4824881) B4824881
theorem B2144391 : Blo 2143435 2144391 := bstep (se 1 (by rfl) ⟨1608293, by rfl⟩ : syracuseStep 2144391 = 3216587) B3216587
theorem B2412445 : Blo 2143435 2412445 := bbase (se 3 (by rfl) ⟨452333, by rfl⟩ : syracuseStep 2412445 = 904667) (by norm_num)
theorem B3216593 : Blo 2143435 3216593 := bstep (se 2 (by rfl) ⟨1206222, by rfl⟩ : syracuseStep 3216593 = 2412445) B2412445
theorem B2144395 : Blo 2143435 2144395 := bstep (se 1 (by rfl) ⟨1608296, by rfl⟩ : syracuseStep 2144395 = 3216593) B3216593
theorem B7237349 : Blo 2143435 7237349 := bbase (se 4 (by rfl) ⟨678501, by rfl⟩ : syracuseStep 7237349 = 1357003) (by norm_num)
theorem B4824899 : Blo 2143435 4824899 := bstep (se 1 (by rfl) ⟨3618674, by rfl⟩ : syracuseStep 4824899 = 7237349) B7237349
theorem B3216599 : Blo 2143435 3216599 := bstep (se 1 (by rfl) ⟨2412449, by rfl⟩ : syracuseStep 3216599 = 4824899) B4824899
theorem B2144399 : Blo 2143435 2144399 := bstep (se 1 (by rfl) ⟨1608299, by rfl⟩ : syracuseStep 2144399 = 3216599) B3216599
theorem B3216605 : Blo 2143435 3216605 := bbase (se 3 (by rfl) ⟨603113, by rfl⟩ : syracuseStep 3216605 = 1206227) (by norm_num)
theorem B2144403 : Blo 2143435 2144403 := bstep (se 1 (by rfl) ⟨1608302, by rfl⟩ : syracuseStep 2144403 = 3216605) B3216605
theorem B4824917 : Blo 2143435 4824917 := bbase (se 9 (by rfl) ⟨14135, by rfl⟩ : syracuseStep 4824917 = 28271) (by norm_num)
theorem B3216611 : Blo 2143435 3216611 := bstep (se 1 (by rfl) ⟨2412458, by rfl⟩ : syracuseStep 3216611 = 4824917) B4824917
theorem B2144407 : Blo 2143435 2144407 := bstep (se 1 (by rfl) ⟨1608305, by rfl⟩ : syracuseStep 2144407 = 3216611) B3216611
theorem B6106549 : Blo 2143435 6106549 := bbase (se 5 (by rfl) ⟨286244, by rfl⟩ : syracuseStep 6106549 = 572489) (by norm_num)
theorem B8142065 : Blo 2143435 8142065 := bstep (se 2 (by rfl) ⟨3053274, by rfl⟩ : syracuseStep 8142065 = 6106549) B6106549
theorem B5428043 : Blo 2143435 5428043 := bstep (se 1 (by rfl) ⟨4071032, by rfl⟩ : syracuseStep 5428043 = 8142065) B8142065
theorem B3618695 : Blo 2143435 3618695 := bstep (se 1 (by rfl) ⟨2714021, by rfl⟩ : syracuseStep 3618695 = 5428043) B5428043
theorem B2412463 : Blo 2143435 2412463 := bstep (se 1 (by rfl) ⟨1809347, by rfl⟩ : syracuseStep 2412463 = 3618695) B3618695
theorem B3216617 : Blo 2143435 3216617 := bstep (se 2 (by rfl) ⟨1206231, by rfl⟩ : syracuseStep 3216617 = 2412463) B2412463
theorem B2144411 : Blo 2143435 2144411 := bstep (se 1 (by rfl) ⟨1608308, by rfl⟩ : syracuseStep 2144411 = 3216617) B3216617
theorem B18569621 : Blo 2143435 18569621 := bbase (se 6 (by rfl) ⟨435225, by rfl⟩ : syracuseStep 18569621 = 870451) (by norm_num)
theorem B49518989 : Blo 2143435 49518989 := bstep (se 3 (by rfl) ⟨9284810, by rfl⟩ : syracuseStep 49518989 = 18569621) B18569621
theorem B33012659 : Blo 2143435 33012659 := bstep (se 1 (by rfl) ⟨24759494, by rfl⟩ : syracuseStep 33012659 = 49518989) B49518989
theorem B22008439 : Blo 2143435 22008439 := bstep (se 1 (by rfl) ⟨16506329, by rfl⟩ : syracuseStep 22008439 = 33012659) B33012659
theorem B117378341 : Blo 2143435 117378341 := bstep (se 4 (by rfl) ⟨11004219, by rfl⟩ : syracuseStep 117378341 = 22008439) B22008439
theorem B78252227 : Blo 2143435 78252227 := bstep (se 1 (by rfl) ⟨58689170, by rfl⟩ : syracuseStep 78252227 = 117378341) B117378341
theorem B52168151 : Blo 2143435 52168151 := bstep (se 1 (by rfl) ⟨39126113, by rfl⟩ : syracuseStep 52168151 = 78252227) B78252227
theorem B139115069 : Blo 2143435 139115069 := bstep (se 3 (by rfl) ⟨26084075, by rfl⟩ : syracuseStep 139115069 = 52168151) B52168151
theorem B92743379 : Blo 2143435 92743379 := bstep (se 1 (by rfl) ⟨69557534, by rfl⟩ : syracuseStep 92743379 = 139115069) B139115069
theorem B61828919 : Blo 2143435 61828919 := bstep (se 1 (by rfl) ⟨46371689, by rfl⟩ : syracuseStep 61828919 = 92743379) B92743379
theorem B41219279 : Blo 2143435 41219279 := bstep (se 1 (by rfl) ⟨30914459, by rfl⟩ : syracuseStep 41219279 = 61828919) B61828919
theorem B27479519 : Blo 2143435 27479519 := bstep (se 1 (by rfl) ⟨20609639, by rfl⟩ : syracuseStep 27479519 = 41219279) B41219279
theorem B18319679 : Blo 2143435 18319679 := bstep (se 1 (by rfl) ⟨13739759, by rfl⟩ : syracuseStep 18319679 = 27479519) B27479519
theorem B12213119 : Blo 2143435 12213119 := bstep (se 1 (by rfl) ⟨9159839, by rfl⟩ : syracuseStep 12213119 = 18319679) B18319679
theorem B8142079 : Blo 2143435 8142079 := bstep (se 1 (by rfl) ⟨6106559, by rfl⟩ : syracuseStep 8142079 = 12213119) B12213119
theorem B10856105 : Blo 2143435 10856105 := bstep (se 2 (by rfl) ⟨4071039, by rfl⟩ : syracuseStep 10856105 = 8142079) B8142079
theorem B7237403 : Blo 2143435 7237403 := bstep (se 1 (by rfl) ⟨5428052, by rfl⟩ : syracuseStep 7237403 = 10856105) B10856105
theorem B4824935 : Blo 2143435 4824935 := bstep (se 1 (by rfl) ⟨3618701, by rfl⟩ : syracuseStep 4824935 = 7237403) B7237403
theorem B3216623 : Blo 2143435 3216623 := bstep (se 1 (by rfl) ⟨2412467, by rfl⟩ : syracuseStep 3216623 = 4824935) B4824935
theorem B2144415 : Blo 2143435 2144415 := bstep (se 1 (by rfl) ⟨1608311, by rfl⟩ : syracuseStep 2144415 = 3216623) B3216623
theorem B3216629 : Blo 2143435 3216629 := bbase (se 5 (by rfl) ⟨150779, by rfl⟩ : syracuseStep 3216629 = 301559) (by norm_num)
theorem B2144419 : Blo 2143435 2144419 := bstep (se 1 (by rfl) ⟨1608314, by rfl⟩ : syracuseStep 2144419 = 3216629) B3216629
theorem B5796485 : Blo 2143435 5796485 := bbase (se 4 (by rfl) ⟨543420, by rfl⟩ : syracuseStep 5796485 = 1086841) (by norm_num)
theorem B3864323 : Blo 2143435 3864323 := bstep (se 1 (by rfl) ⟨2898242, by rfl⟩ : syracuseStep 3864323 = 5796485) B5796485
theorem B2576215 : Blo 2143435 2576215 := bstep (se 1 (by rfl) ⟨1932161, by rfl⟩ : syracuseStep 2576215 = 3864323) B3864323
theorem B13739813 : Blo 2143435 13739813 := bstep (se 4 (by rfl) ⟨1288107, by rfl⟩ : syracuseStep 13739813 = 2576215) B2576215
theorem B9159875 : Blo 2143435 9159875 := bstep (se 1 (by rfl) ⟨6869906, by rfl⟩ : syracuseStep 9159875 = 13739813) B13739813
theorem B6106583 : Blo 2143435 6106583 := bstep (se 1 (by rfl) ⟨4579937, by rfl⟩ : syracuseStep 6106583 = 9159875) B9159875
theorem B4071055 : Blo 2143435 4071055 := bstep (se 1 (by rfl) ⟨3053291, by rfl⟩ : syracuseStep 4071055 = 6106583) B6106583
theorem B5428073 : Blo 2143435 5428073 := bstep (se 2 (by rfl) ⟨2035527, by rfl⟩ : syracuseStep 5428073 = 4071055) B4071055
theorem B3618715 : Blo 2143435 3618715 := bstep (se 1 (by rfl) ⟨2714036, by rfl⟩ : syracuseStep 3618715 = 5428073) B5428073
theorem B4824953 : Blo 2143435 4824953 := bstep (se 2 (by rfl) ⟨1809357, by rfl⟩ : syracuseStep 4824953 = 3618715) B3618715
theorem B3216635 : Blo 2143435 3216635 := bstep (se 1 (by rfl) ⟨2412476, by rfl⟩ : syracuseStep 3216635 = 4824953) B4824953
theorem B2144423 : Blo 2143435 2144423 := bstep (se 1 (by rfl) ⟨1608317, by rfl⟩ : syracuseStep 2144423 = 3216635) B3216635
theorem B2412481 : Blo 2143435 2412481 := bbase (se 2 (by rfl) ⟨904680, by rfl⟩ : syracuseStep 2412481 = 1809361) (by norm_num)
theorem B3216641 : Blo 2143435 3216641 := bstep (se 2 (by rfl) ⟨1206240, by rfl⟩ : syracuseStep 3216641 = 2412481) B2412481
theorem B2144427 : Blo 2143435 2144427 := bstep (se 1 (by rfl) ⟨1608320, by rfl⟩ : syracuseStep 2144427 = 3216641) B3216641
theorem B5428093 : Blo 2143435 5428093 := bbase (se 3 (by rfl) ⟨1017767, by rfl⟩ : syracuseStep 5428093 = 2035535) (by norm_num)
theorem B7237457 : Blo 2143435 7237457 := bstep (se 2 (by rfl) ⟨2714046, by rfl⟩ : syracuseStep 7237457 = 5428093) B5428093
theorem B4824971 : Blo 2143435 4824971 := bstep (se 1 (by rfl) ⟨3618728, by rfl⟩ : syracuseStep 4824971 = 7237457) B7237457
theorem B3216647 : Blo 2143435 3216647 := bstep (se 1 (by rfl) ⟨2412485, by rfl⟩ : syracuseStep 3216647 = 4824971) B4824971
theorem B2144431 : Blo 2143435 2144431 := bstep (se 1 (by rfl) ⟨1608323, by rfl⟩ : syracuseStep 2144431 = 3216647) B3216647
theorem B3216653 : Blo 2143435 3216653 := bbase (se 3 (by rfl) ⟨603122, by rfl⟩ : syracuseStep 3216653 = 1206245) (by norm_num)
theorem B2144435 : Blo 2143435 2144435 := bstep (se 1 (by rfl) ⟨1608326, by rfl⟩ : syracuseStep 2144435 = 3216653) B3216653
theorem B4824989 : Blo 2143435 4824989 := bbase (se 3 (by rfl) ⟨904685, by rfl⟩ : syracuseStep 4824989 = 1809371) (by norm_num)
theorem B3216659 : Blo 2143435 3216659 := bstep (se 1 (by rfl) ⟨2412494, by rfl⟩ : syracuseStep 3216659 = 4824989) B4824989
theorem B2144439 : Blo 2143435 2144439 := bstep (se 1 (by rfl) ⟨1608329, by rfl⟩ : syracuseStep 2144439 = 3216659) B3216659
theorem B3618749 : Blo 2143435 3618749 := bbase (se 3 (by rfl) ⟨678515, by rfl⟩ : syracuseStep 3618749 = 1357031) (by norm_num)
theorem B2412499 : Blo 2143435 2412499 := bstep (se 1 (by rfl) ⟨1809374, by rfl⟩ : syracuseStep 2412499 = 3618749) B3618749
theorem B3216665 : Blo 2143435 3216665 := bstep (se 2 (by rfl) ⟨1206249, by rfl⟩ : syracuseStep 3216665 = 2412499) B2412499
theorem B2144443 : Blo 2143435 2144443 := bstep (se 1 (by rfl) ⟨1608332, by rfl⟩ : syracuseStep 2144443 = 3216665) B3216665
theorem B12213301 : Blo 2143435 12213301 := bbase (se 5 (by rfl) ⟨572498, by rfl⟩ : syracuseStep 12213301 = 1144997) (by norm_num)
theorem B16284401 : Blo 2143435 16284401 := bstep (se 2 (by rfl) ⟨6106650, by rfl⟩ : syracuseStep 16284401 = 12213301) B12213301
theorem B10856267 : Blo 2143435 10856267 := bstep (se 1 (by rfl) ⟨8142200, by rfl⟩ : syracuseStep 10856267 = 16284401) B16284401
theorem B7237511 : Blo 2143435 7237511 := bstep (se 1 (by rfl) ⟨5428133, by rfl⟩ : syracuseStep 7237511 = 10856267) B10856267
theorem B4825007 : Blo 2143435 4825007 := bstep (se 1 (by rfl) ⟨3618755, by rfl⟩ : syracuseStep 4825007 = 7237511) B7237511
theorem B3216671 : Blo 2143435 3216671 := bstep (se 1 (by rfl) ⟨2412503, by rfl⟩ : syracuseStep 3216671 = 4825007) B4825007
theorem B2144447 : Blo 2143435 2144447 := bstep (se 1 (by rfl) ⟨1608335, by rfl⟩ : syracuseStep 2144447 = 3216671) B3216671
theorem B3216677 : Blo 2143435 3216677 := bbase (se 4 (by rfl) ⟨301563, by rfl⟩ : syracuseStep 3216677 = 603127) (by norm_num)
theorem B2144451 : Blo 2143435 2144451 := bstep (se 1 (by rfl) ⟨1608338, by rfl⟩ : syracuseStep 2144451 = 3216677) B3216677
theorem B2714077 : Blo 2143435 2714077 := bbase (se 3 (by rfl) ⟨508889, by rfl⟩ : syracuseStep 2714077 = 1017779) (by norm_num)
theorem B3618769 : Blo 2143435 3618769 := bstep (se 2 (by rfl) ⟨1357038, by rfl⟩ : syracuseStep 3618769 = 2714077) B2714077
theorem B4825025 : Blo 2143435 4825025 := bstep (se 2 (by rfl) ⟨1809384, by rfl⟩ : syracuseStep 4825025 = 3618769) B3618769
theorem B3216683 : Blo 2143435 3216683 := bstep (se 1 (by rfl) ⟨2412512, by rfl⟩ : syracuseStep 3216683 = 4825025) B4825025
theorem B2144455 : Blo 2143435 2144455 := bstep (se 1 (by rfl) ⟨1608341, by rfl⟩ : syracuseStep 2144455 = 3216683) B3216683
theorem B2412517 : Blo 2143435 2412517 := bbase (se 4 (by rfl) ⟨226173, by rfl⟩ : syracuseStep 2412517 = 452347) (by norm_num)
theorem B3216689 : Blo 2143435 3216689 := bstep (se 2 (by rfl) ⟨1206258, by rfl⟩ : syracuseStep 3216689 = 2412517) B2412517
theorem B2144459 : Blo 2143435 2144459 := bstep (se 1 (by rfl) ⟨1608344, by rfl⟩ : syracuseStep 2144459 = 3216689) B3216689
theorem B4347445 : Blo 2143435 4347445 := bbase (se 5 (by rfl) ⟨203786, by rfl⟩ : syracuseStep 4347445 = 407573) (by norm_num)
theorem B5796593 : Blo 2143435 5796593 := bstep (se 2 (by rfl) ⟨2173722, by rfl⟩ : syracuseStep 5796593 = 4347445) B4347445
theorem B3864395 : Blo 2143435 3864395 := bstep (se 1 (by rfl) ⟨2898296, by rfl⟩ : syracuseStep 3864395 = 5796593) B5796593
theorem B10305053 : Blo 2143435 10305053 := bstep (se 3 (by rfl) ⟨1932197, by rfl⟩ : syracuseStep 10305053 = 3864395) B3864395
theorem B6870035 : Blo 2143435 6870035 := bstep (se 1 (by rfl) ⟨5152526, by rfl⟩ : syracuseStep 6870035 = 10305053) B10305053
theorem B4580023 : Blo 2143435 4580023 := bstep (se 1 (by rfl) ⟨3435017, by rfl⟩ : syracuseStep 4580023 = 6870035) B6870035
theorem B6106697 : Blo 2143435 6106697 := bstep (se 2 (by rfl) ⟨2290011, by rfl⟩ : syracuseStep 6106697 = 4580023) B4580023
theorem B4071131 : Blo 2143435 4071131 := bstep (se 1 (by rfl) ⟨3053348, by rfl⟩ : syracuseStep 4071131 = 6106697) B6106697
theorem B2714087 : Blo 2143435 2714087 := bstep (se 1 (by rfl) ⟨2035565, by rfl⟩ : syracuseStep 2714087 = 4071131) B4071131
theorem B7237565 : Blo 2143435 7237565 := bstep (se 3 (by rfl) ⟨1357043, by rfl⟩ : syracuseStep 7237565 = 2714087) B2714087
theorem B4825043 : Blo 2143435 4825043 := bstep (se 1 (by rfl) ⟨3618782, by rfl⟩ : syracuseStep 4825043 = 7237565) B7237565
theorem B3216695 : Blo 2143435 3216695 := bstep (se 1 (by rfl) ⟨2412521, by rfl⟩ : syracuseStep 3216695 = 4825043) B4825043
theorem B2144463 : Blo 2143435 2144463 := bstep (se 1 (by rfl) ⟨1608347, by rfl⟩ : syracuseStep 2144463 = 3216695) B3216695
theorem B3216701 : Blo 2143435 3216701 := bbase (se 3 (by rfl) ⟨603131, by rfl⟩ : syracuseStep 3216701 = 1206263) (by norm_num)
theorem B2144467 : Blo 2143435 2144467 := bstep (se 1 (by rfl) ⟨1608350, by rfl⟩ : syracuseStep 2144467 = 3216701) B3216701
theorem B4825061 : Blo 2143435 4825061 := bbase (se 4 (by rfl) ⟨452349, by rfl⟩ : syracuseStep 4825061 = 904699) (by norm_num)
theorem B3216707 : Blo 2143435 3216707 := bstep (se 1 (by rfl) ⟨2412530, by rfl⟩ : syracuseStep 3216707 = 4825061) B4825061
theorem B2144471 : Blo 2143435 2144471 := bstep (se 1 (by rfl) ⟨1608353, by rfl⟩ : syracuseStep 2144471 = 3216707) B3216707
theorem B5428205 : Blo 2143435 5428205 := bbase (se 3 (by rfl) ⟨1017788, by rfl⟩ : syracuseStep 5428205 = 2035577) (by norm_num)
theorem B3618803 : Blo 2143435 3618803 := bstep (se 1 (by rfl) ⟨2714102, by rfl⟩ : syracuseStep 3618803 = 5428205) B5428205
theorem B2412535 : Blo 2143435 2412535 := bstep (se 1 (by rfl) ⟨1809401, by rfl⟩ : syracuseStep 2412535 = 3618803) B3618803
theorem B3216713 : Blo 2143435 3216713 := bstep (se 2 (by rfl) ⟨1206267, by rfl⟩ : syracuseStep 3216713 = 2412535) B2412535
theorem B2144475 : Blo 2143435 2144475 := bstep (se 1 (by rfl) ⟨1608356, by rfl⟩ : syracuseStep 2144475 = 3216713) B3216713
theorem B5152565 : Blo 2143435 5152565 := bbase (se 5 (by rfl) ⟨241526, by rfl⟩ : syracuseStep 5152565 = 483053) (by norm_num)
theorem B3435043 : Blo 2143435 3435043 := bstep (se 1 (by rfl) ⟨2576282, by rfl⟩ : syracuseStep 3435043 = 5152565) B5152565
theorem B4580057 : Blo 2143435 4580057 := bstep (se 2 (by rfl) ⟨1717521, by rfl⟩ : syracuseStep 4580057 = 3435043) B3435043
theorem B3053371 : Blo 2143435 3053371 := bstep (se 1 (by rfl) ⟨2290028, by rfl⟩ : syracuseStep 3053371 = 4580057) B4580057
theorem B4071161 : Blo 2143435 4071161 := bstep (se 2 (by rfl) ⟨1526685, by rfl⟩ : syracuseStep 4071161 = 3053371) B3053371
theorem B10856429 : Blo 2143435 10856429 := bstep (se 3 (by rfl) ⟨2035580, by rfl⟩ : syracuseStep 10856429 = 4071161) B4071161
theorem B7237619 : Blo 2143435 7237619 := bstep (se 1 (by rfl) ⟨5428214, by rfl⟩ : syracuseStep 7237619 = 10856429) B10856429
theorem B4825079 : Blo 2143435 4825079 := bstep (se 1 (by rfl) ⟨3618809, by rfl⟩ : syracuseStep 4825079 = 7237619) B7237619
theorem B3216719 : Blo 2143435 3216719 := bstep (se 1 (by rfl) ⟨2412539, by rfl⟩ : syracuseStep 3216719 = 4825079) B4825079
theorem B2144479 : Blo 2143435 2144479 := bstep (se 1 (by rfl) ⟨1608359, by rfl⟩ : syracuseStep 2144479 = 3216719) B3216719
theorem B3216725 : Blo 2143435 3216725 := bbase (se 14 (by rfl) ⟨294, by rfl⟩ : syracuseStep 3216725 = 589) (by norm_num)
theorem B2144483 : Blo 2143435 2144483 := bstep (se 1 (by rfl) ⟨1608362, by rfl⟩ : syracuseStep 2144483 = 3216725) B3216725
theorem B2290037 : Blo 2143435 2290037 := bbase (se 5 (by rfl) ⟨107345, by rfl⟩ : syracuseStep 2290037 = 214691) (by norm_num)
theorem B6106765 : Blo 2143435 6106765 := bstep (se 3 (by rfl) ⟨1145018, by rfl⟩ : syracuseStep 6106765 = 2290037) B2290037
theorem B8142353 : Blo 2143435 8142353 := bstep (se 2 (by rfl) ⟨3053382, by rfl⟩ : syracuseStep 8142353 = 6106765) B6106765
theorem B5428235 : Blo 2143435 5428235 := bstep (se 1 (by rfl) ⟨4071176, by rfl⟩ : syracuseStep 5428235 = 8142353) B8142353
theorem B3618823 : Blo 2143435 3618823 := bstep (se 1 (by rfl) ⟨2714117, by rfl⟩ : syracuseStep 3618823 = 5428235) B5428235
theorem B4825097 : Blo 2143435 4825097 := bstep (se 2 (by rfl) ⟨1809411, by rfl⟩ : syracuseStep 4825097 = 3618823) B3618823
theorem B3216731 : Blo 2143435 3216731 := bstep (se 1 (by rfl) ⟨2412548, by rfl⟩ : syracuseStep 3216731 = 4825097) B4825097
theorem B2144487 : Blo 2143435 2144487 := bstep (se 1 (by rfl) ⟨1608365, by rfl⟩ : syracuseStep 2144487 = 3216731) B3216731
theorem B2412553 : Blo 2143435 2412553 := bbase (se 2 (by rfl) ⟨904707, by rfl⟩ : syracuseStep 2412553 = 1809415) (by norm_num)
theorem B3216737 : Blo 2143435 3216737 := bstep (se 2 (by rfl) ⟨1206276, by rfl⟩ : syracuseStep 3216737 = 2412553) B2412553
theorem B2144491 : Blo 2143435 2144491 := bstep (se 1 (by rfl) ⟨1608368, by rfl⟩ : syracuseStep 2144491 = 3216737) B3216737
theorem B7336421 : Blo 2143435 7336421 := bbase (se 4 (by rfl) ⟨687789, by rfl⟩ : syracuseStep 7336421 = 1375579) (by norm_num)
theorem B4890947 : Blo 2143435 4890947 := bstep (se 1 (by rfl) ⟨3668210, by rfl⟩ : syracuseStep 4890947 = 7336421) B7336421
theorem B52170101 : Blo 2143435 52170101 := bstep (se 5 (by rfl) ⟨2445473, by rfl⟩ : syracuseStep 52170101 = 4890947) B4890947
theorem B34780067 : Blo 2143435 34780067 := bstep (se 1 (by rfl) ⟨26085050, by rfl⟩ : syracuseStep 34780067 = 52170101) B52170101
theorem B23186711 : Blo 2143435 23186711 := bstep (se 1 (by rfl) ⟨17390033, by rfl⟩ : syracuseStep 23186711 = 34780067) B34780067
theorem B15457807 : Blo 2143435 15457807 := bstep (se 1 (by rfl) ⟨11593355, by rfl⟩ : syracuseStep 15457807 = 23186711) B23186711
theorem B20610409 : Blo 2143435 20610409 := bstep (se 2 (by rfl) ⟨7728903, by rfl⟩ : syracuseStep 20610409 = 15457807) B15457807
theorem B27480545 : Blo 2143435 27480545 := bstep (se 2 (by rfl) ⟨10305204, by rfl⟩ : syracuseStep 27480545 = 20610409) B20610409
theorem B18320363 : Blo 2143435 18320363 := bstep (se 1 (by rfl) ⟨13740272, by rfl⟩ : syracuseStep 18320363 = 27480545) B27480545
theorem B12213575 : Blo 2143435 12213575 := bstep (se 1 (by rfl) ⟨9160181, by rfl⟩ : syracuseStep 12213575 = 18320363) B18320363
theorem B8142383 : Blo 2143435 8142383 := bstep (se 1 (by rfl) ⟨6106787, by rfl⟩ : syracuseStep 8142383 = 12213575) B12213575
theorem B5428255 : Blo 2143435 5428255 := bstep (se 1 (by rfl) ⟨4071191, by rfl⟩ : syracuseStep 5428255 = 8142383) B8142383
theorem B7237673 : Blo 2143435 7237673 := bstep (se 2 (by rfl) ⟨2714127, by rfl⟩ : syracuseStep 7237673 = 5428255) B5428255
theorem B4825115 : Blo 2143435 4825115 := bstep (se 1 (by rfl) ⟨3618836, by rfl⟩ : syracuseStep 4825115 = 7237673) B7237673
theorem B3216743 : Blo 2143435 3216743 := bstep (se 1 (by rfl) ⟨2412557, by rfl⟩ : syracuseStep 3216743 = 4825115) B4825115
theorem B2144495 : Blo 2143435 2144495 := bstep (se 1 (by rfl) ⟨1608371, by rfl⟩ : syracuseStep 2144495 = 3216743) B3216743
theorem B3216749 : Blo 2143435 3216749 := bbase (se 3 (by rfl) ⟨603140, by rfl⟩ : syracuseStep 3216749 = 1206281) (by norm_num)
theorem B2144499 : Blo 2143435 2144499 := bstep (se 1 (by rfl) ⟨1608374, by rfl⟩ : syracuseStep 2144499 = 3216749) B3216749
theorem B4825133 : Blo 2143435 4825133 := bbase (se 3 (by rfl) ⟨904712, by rfl⟩ : syracuseStep 4825133 = 1809425) (by norm_num)
theorem B3216755 : Blo 2143435 3216755 := bstep (se 1 (by rfl) ⟨2412566, by rfl⟩ : syracuseStep 3216755 = 4825133) B4825133
theorem B2144503 : Blo 2143435 2144503 := bstep (se 1 (by rfl) ⟨1608377, by rfl⟩ : syracuseStep 2144503 = 3216755) B3216755
theorem B7728949 : Blo 2143435 7728949 := bbase (se 5 (by rfl) ⟨362294, by rfl⟩ : syracuseStep 7728949 = 724589) (by norm_num)
theorem B10305265 : Blo 2143435 10305265 := bstep (se 2 (by rfl) ⟨3864474, by rfl⟩ : syracuseStep 10305265 = 7728949) B7728949
theorem B13740353 : Blo 2143435 13740353 := bstep (se 2 (by rfl) ⟨5152632, by rfl⟩ : syracuseStep 13740353 = 10305265) B10305265
theorem B9160235 : Blo 2143435 9160235 := bstep (se 1 (by rfl) ⟨6870176, by rfl⟩ : syracuseStep 9160235 = 13740353) B13740353
theorem B6106823 : Blo 2143435 6106823 := bstep (se 1 (by rfl) ⟨4580117, by rfl⟩ : syracuseStep 6106823 = 9160235) B9160235
theorem B4071215 : Blo 2143435 4071215 := bstep (se 1 (by rfl) ⟨3053411, by rfl⟩ : syracuseStep 4071215 = 6106823) B6106823
theorem B2714143 : Blo 2143435 2714143 := bstep (se 1 (by rfl) ⟨2035607, by rfl⟩ : syracuseStep 2714143 = 4071215) B4071215
theorem B3618857 : Blo 2143435 3618857 := bstep (se 2 (by rfl) ⟨1357071, by rfl⟩ : syracuseStep 3618857 = 2714143) B2714143
theorem B2412571 : Blo 2143435 2412571 := bstep (se 1 (by rfl) ⟨1809428, by rfl⟩ : syracuseStep 2412571 = 3618857) B3618857
theorem B3216761 : Blo 2143435 3216761 := bstep (se 2 (by rfl) ⟨1206285, by rfl⟩ : syracuseStep 3216761 = 2412571) B2412571
theorem B2144507 : Blo 2143435 2144507 := bstep (se 1 (by rfl) ⟨1608380, by rfl⟩ : syracuseStep 2144507 = 3216761) B3216761
theorem B4347541 : Blo 2143435 4347541 := bbase (se 6 (by rfl) ⟨101895, by rfl⟩ : syracuseStep 4347541 = 203791) (by norm_num)
theorem B5796721 : Blo 2143435 5796721 := bstep (se 2 (by rfl) ⟨2173770, by rfl⟩ : syracuseStep 5796721 = 4347541) B4347541
theorem B7728961 : Blo 2143435 7728961 := bstep (se 2 (by rfl) ⟨2898360, by rfl⟩ : syracuseStep 7728961 = 5796721) B5796721
theorem B10305281 : Blo 2143435 10305281 := bstep (se 2 (by rfl) ⟨3864480, by rfl⟩ : syracuseStep 10305281 = 7728961) B7728961
theorem B6870187 : Blo 2143435 6870187 := bstep (se 1 (by rfl) ⟨5152640, by rfl⟩ : syracuseStep 6870187 = 10305281) B10305281
theorem B36640997 : Blo 2143435 36640997 := bstep (se 4 (by rfl) ⟨3435093, by rfl⟩ : syracuseStep 36640997 = 6870187) B6870187
theorem B24427331 : Blo 2143435 24427331 := bstep (se 1 (by rfl) ⟨18320498, by rfl⟩ : syracuseStep 24427331 = 36640997) B36640997
theorem B16284887 : Blo 2143435 16284887 := bstep (se 1 (by rfl) ⟨12213665, by rfl⟩ : syracuseStep 16284887 = 24427331) B24427331
theorem B10856591 : Blo 2143435 10856591 := bstep (se 1 (by rfl) ⟨8142443, by rfl⟩ : syracuseStep 10856591 = 16284887) B16284887
theorem B7237727 : Blo 2143435 7237727 := bstep (se 1 (by rfl) ⟨5428295, by rfl⟩ : syracuseStep 7237727 = 10856591) B10856591
theorem B4825151 : Blo 2143435 4825151 := bstep (se 1 (by rfl) ⟨3618863, by rfl⟩ : syracuseStep 4825151 = 7237727) B7237727
theorem B3216767 : Blo 2143435 3216767 := bstep (se 1 (by rfl) ⟨2412575, by rfl⟩ : syracuseStep 3216767 = 4825151) B4825151
theorem B2144511 : Blo 2143435 2144511 := bstep (se 1 (by rfl) ⟨1608383, by rfl⟩ : syracuseStep 2144511 = 3216767) B3216767
theorem B3216773 : Blo 2143435 3216773 := bbase (se 4 (by rfl) ⟨301572, by rfl⟩ : syracuseStep 3216773 = 603145) (by norm_num)
theorem B2144515 : Blo 2143435 2144515 := bstep (se 1 (by rfl) ⟨1608386, by rfl⟩ : syracuseStep 2144515 = 3216773) B3216773
theorem B3618877 : Blo 2143435 3618877 := bbase (se 3 (by rfl) ⟨678539, by rfl⟩ : syracuseStep 3618877 = 1357079) (by norm_num)
theorem B4825169 : Blo 2143435 4825169 := bstep (se 2 (by rfl) ⟨1809438, by rfl⟩ : syracuseStep 4825169 = 3618877) B3618877
theorem B3216779 : Blo 2143435 3216779 := bstep (se 1 (by rfl) ⟨2412584, by rfl⟩ : syracuseStep 3216779 = 4825169) B4825169
theorem B2144519 : Blo 2143435 2144519 := bstep (se 1 (by rfl) ⟨1608389, by rfl⟩ : syracuseStep 2144519 = 3216779) B3216779
theorem B2412589 : Blo 2143435 2412589 := bbase (se 3 (by rfl) ⟨452360, by rfl⟩ : syracuseStep 2412589 = 904721) (by norm_num)
theorem B3216785 : Blo 2143435 3216785 := bstep (se 2 (by rfl) ⟨1206294, by rfl⟩ : syracuseStep 3216785 = 2412589) B2412589
theorem B2144523 : Blo 2143435 2144523 := bstep (se 1 (by rfl) ⟨1608392, by rfl⟩ : syracuseStep 2144523 = 3216785) B3216785
theorem B7237781 : Blo 2143435 7237781 := bbase (se 6 (by rfl) ⟨169635, by rfl⟩ : syracuseStep 7237781 = 339271) (by norm_num)
theorem B4825187 : Blo 2143435 4825187 := bstep (se 1 (by rfl) ⟨3618890, by rfl⟩ : syracuseStep 4825187 = 7237781) B7237781
theorem B3216791 : Blo 2143435 3216791 := bstep (se 1 (by rfl) ⟨2412593, by rfl⟩ : syracuseStep 3216791 = 4825187) B4825187
theorem B2144527 : Blo 2143435 2144527 := bstep (se 1 (by rfl) ⟨1608395, by rfl⟩ : syracuseStep 2144527 = 3216791) B3216791
theorem B3216797 : Blo 2143435 3216797 := bbase (se 3 (by rfl) ⟨603149, by rfl⟩ : syracuseStep 3216797 = 1206299) (by norm_num)
theorem B2144531 : Blo 2143435 2144531 := bstep (se 1 (by rfl) ⟨1608398, by rfl⟩ : syracuseStep 2144531 = 3216797) B3216797
theorem B4825205 : Blo 2143435 4825205 := bbase (se 5 (by rfl) ⟨226181, by rfl⟩ : syracuseStep 4825205 = 452363) (by norm_num)
theorem B3216803 : Blo 2143435 3216803 := bstep (se 1 (by rfl) ⟨2412602, by rfl⟩ : syracuseStep 3216803 = 4825205) B4825205
theorem B2144535 : Blo 2143435 2144535 := bstep (se 1 (by rfl) ⟨1608401, by rfl⟩ : syracuseStep 2144535 = 3216803) B3216803
theorem B5152709 : Blo 2143435 5152709 := bbase (se 4 (by rfl) ⟨483066, by rfl⟩ : syracuseStep 5152709 = 966133) (by norm_num)
theorem B3435139 : Blo 2143435 3435139 := bstep (se 1 (by rfl) ⟨2576354, by rfl⟩ : syracuseStep 3435139 = 5152709) B5152709
theorem B18320741 : Blo 2143435 18320741 := bstep (se 4 (by rfl) ⟨1717569, by rfl⟩ : syracuseStep 18320741 = 3435139) B3435139
theorem B12213827 : Blo 2143435 12213827 := bstep (se 1 (by rfl) ⟨9160370, by rfl⟩ : syracuseStep 12213827 = 18320741) B18320741
theorem B8142551 : Blo 2143435 8142551 := bstep (se 1 (by rfl) ⟨6106913, by rfl⟩ : syracuseStep 8142551 = 12213827) B12213827
theorem B5428367 : Blo 2143435 5428367 := bstep (se 1 (by rfl) ⟨4071275, by rfl⟩ : syracuseStep 5428367 = 8142551) B8142551
theorem B3618911 : Blo 2143435 3618911 := bstep (se 1 (by rfl) ⟨2714183, by rfl⟩ : syracuseStep 3618911 = 5428367) B5428367
theorem B2412607 : Blo 2143435 2412607 := bstep (se 1 (by rfl) ⟨1809455, by rfl⟩ : syracuseStep 2412607 = 3618911) B3618911
theorem B3216809 : Blo 2143435 3216809 := bstep (se 2 (by rfl) ⟨1206303, by rfl⟩ : syracuseStep 3216809 = 2412607) B2412607
theorem B2144539 : Blo 2143435 2144539 := bstep (se 1 (by rfl) ⟨1608404, by rfl⟩ : syracuseStep 2144539 = 3216809) B3216809
theorem B8142565 : Blo 2143435 8142565 := bbase (se 4 (by rfl) ⟨763365, by rfl⟩ : syracuseStep 8142565 = 1526731) (by norm_num)
theorem B10856753 : Blo 2143435 10856753 := bstep (se 2 (by rfl) ⟨4071282, by rfl⟩ : syracuseStep 10856753 = 8142565) B8142565
theorem B7237835 : Blo 2143435 7237835 := bstep (se 1 (by rfl) ⟨5428376, by rfl⟩ : syracuseStep 7237835 = 10856753) B10856753
theorem B4825223 : Blo 2143435 4825223 := bstep (se 1 (by rfl) ⟨3618917, by rfl⟩ : syracuseStep 4825223 = 7237835) B7237835
theorem B3216815 : Blo 2143435 3216815 := bstep (se 1 (by rfl) ⟨2412611, by rfl⟩ : syracuseStep 3216815 = 4825223) B4825223
theorem B2144543 : Blo 2143435 2144543 := bstep (se 1 (by rfl) ⟨1608407, by rfl⟩ : syracuseStep 2144543 = 3216815) B3216815
theorem B3216821 : Blo 2143435 3216821 := bbase (se 5 (by rfl) ⟨150788, by rfl⟩ : syracuseStep 3216821 = 301577) (by norm_num)
theorem B2144547 : Blo 2143435 2144547 := bstep (se 1 (by rfl) ⟨1608410, by rfl⟩ : syracuseStep 2144547 = 3216821) B3216821
theorem B5428397 : Blo 2143435 5428397 := bbase (se 3 (by rfl) ⟨1017824, by rfl⟩ : syracuseStep 5428397 = 2035649) (by norm_num)
theorem B3618931 : Blo 2143435 3618931 := bstep (se 1 (by rfl) ⟨2714198, by rfl⟩ : syracuseStep 3618931 = 5428397) B5428397
theorem B4825241 : Blo 2143435 4825241 := bstep (se 2 (by rfl) ⟨1809465, by rfl⟩ : syracuseStep 4825241 = 3618931) B3618931
theorem B3216827 : Blo 2143435 3216827 := bstep (se 1 (by rfl) ⟨2412620, by rfl⟩ : syracuseStep 3216827 = 4825241) B4825241
theorem B2144551 : Blo 2143435 2144551 := bstep (se 1 (by rfl) ⟨1608413, by rfl⟩ : syracuseStep 2144551 = 3216827) B3216827
theorem B2412625 : Blo 2143435 2412625 := bbase (se 2 (by rfl) ⟨904734, by rfl⟩ : syracuseStep 2412625 = 1809469) (by norm_num)
theorem B3216833 : Blo 2143435 3216833 := bstep (se 2 (by rfl) ⟨1206312, by rfl⟩ : syracuseStep 3216833 = 2412625) B2412625
theorem B2144555 : Blo 2143435 2144555 := bstep (se 1 (by rfl) ⟨1608416, by rfl⟩ : syracuseStep 2144555 = 3216833) B3216833
theorem B3053485 : Blo 2143435 3053485 := bbase (se 3 (by rfl) ⟨572528, by rfl⟩ : syracuseStep 3053485 = 1145057) (by norm_num)
theorem B4071313 : Blo 2143435 4071313 := bstep (se 2 (by rfl) ⟨1526742, by rfl⟩ : syracuseStep 4071313 = 3053485) B3053485
theorem B5428417 : Blo 2143435 5428417 := bstep (se 2 (by rfl) ⟨2035656, by rfl⟩ : syracuseStep 5428417 = 4071313) B4071313
theorem B7237889 : Blo 2143435 7237889 := bstep (se 2 (by rfl) ⟨2714208, by rfl⟩ : syracuseStep 7237889 = 5428417) B5428417
theorem B4825259 : Blo 2143435 4825259 := bstep (se 1 (by rfl) ⟨3618944, by rfl⟩ : syracuseStep 4825259 = 7237889) B7237889
theorem B3216839 : Blo 2143435 3216839 := bstep (se 1 (by rfl) ⟨2412629, by rfl⟩ : syracuseStep 3216839 = 4825259) B4825259
theorem B2144559 : Blo 2143435 2144559 := bstep (se 1 (by rfl) ⟨1608419, by rfl⟩ : syracuseStep 2144559 = 3216839) B3216839
theorem B3216845 : Blo 2143435 3216845 := bbase (se 3 (by rfl) ⟨603158, by rfl⟩ : syracuseStep 3216845 = 1206317) (by norm_num)
theorem B2144563 : Blo 2143435 2144563 := bstep (se 1 (by rfl) ⟨1608422, by rfl⟩ : syracuseStep 2144563 = 3216845) B3216845
theorem B4825277 : Blo 2143435 4825277 := bbase (se 3 (by rfl) ⟨904739, by rfl⟩ : syracuseStep 4825277 = 1809479) (by norm_num)
theorem B3216851 : Blo 2143435 3216851 := bstep (se 1 (by rfl) ⟨2412638, by rfl⟩ : syracuseStep 3216851 = 4825277) B4825277
theorem B2144567 : Blo 2143435 2144567 := bstep (se 1 (by rfl) ⟨1608425, by rfl⟩ : syracuseStep 2144567 = 3216851) B3216851
theorem B3618965 : Blo 2143435 3618965 := bbase (se 6 (by rfl) ⟨84819, by rfl⟩ : syracuseStep 3618965 = 169639) (by norm_num)
theorem B2412643 : Blo 2143435 2412643 := bstep (se 1 (by rfl) ⟨1809482, by rfl⟩ : syracuseStep 2412643 = 3618965) B3618965
theorem B3216857 : Blo 2143435 3216857 := bstep (se 2 (by rfl) ⟨1206321, by rfl⟩ : syracuseStep 3216857 = 2412643) B2412643
theorem B2144571 : Blo 2143435 2144571 := bstep (se 1 (by rfl) ⟨1608428, by rfl⟩ : syracuseStep 2144571 = 3216857) B3216857
theorem B10305589 : Blo 2143435 10305589 := bbase (se 5 (by rfl) ⟨483074, by rfl⟩ : syracuseStep 10305589 = 966149) (by norm_num)
theorem B13740785 : Blo 2143435 13740785 := bstep (se 2 (by rfl) ⟨5152794, by rfl⟩ : syracuseStep 13740785 = 10305589) B10305589
theorem B9160523 : Blo 2143435 9160523 := bstep (se 1 (by rfl) ⟨6870392, by rfl⟩ : syracuseStep 9160523 = 13740785) B13740785
theorem B6107015 : Blo 2143435 6107015 := bstep (se 1 (by rfl) ⟨4580261, by rfl⟩ : syracuseStep 6107015 = 9160523) B9160523
theorem B16285373 : Blo 2143435 16285373 := bstep (se 3 (by rfl) ⟨3053507, by rfl⟩ : syracuseStep 16285373 = 6107015) B6107015
theorem B10856915 : Blo 2143435 10856915 := bstep (se 1 (by rfl) ⟨8142686, by rfl⟩ : syracuseStep 10856915 = 16285373) B16285373
theorem B7237943 : Blo 2143435 7237943 := bstep (se 1 (by rfl) ⟨5428457, by rfl⟩ : syracuseStep 7237943 = 10856915) B10856915
theorem B4825295 : Blo 2143435 4825295 := bstep (se 1 (by rfl) ⟨3618971, by rfl⟩ : syracuseStep 4825295 = 7237943) B7237943
theorem B3216863 : Blo 2143435 3216863 := bstep (se 1 (by rfl) ⟨2412647, by rfl⟩ : syracuseStep 3216863 = 4825295) B4825295
theorem B2144575 : Blo 2143435 2144575 := bstep (se 1 (by rfl) ⟨1608431, by rfl⟩ : syracuseStep 2144575 = 3216863) B3216863
theorem B3216869 : Blo 2143435 3216869 := bbase (se 4 (by rfl) ⟨301581, by rfl⟩ : syracuseStep 3216869 = 603163) (by norm_num)
theorem B2144579 : Blo 2143435 2144579 := bstep (se 1 (by rfl) ⟨1608434, by rfl⟩ : syracuseStep 2144579 = 3216869) B3216869
theorem B4706117 : Blo 2143435 4706117 := bbase (se 4 (by rfl) ⟨441198, by rfl⟩ : syracuseStep 4706117 = 882397) (by norm_num)
theorem B3137411 : Blo 2143435 3137411 := bstep (se 1 (by rfl) ⟨2353058, by rfl⟩ : syracuseStep 3137411 = 4706117) B4706117
theorem B8366429 : Blo 2143435 8366429 := bstep (se 3 (by rfl) ⟨1568705, by rfl⟩ : syracuseStep 8366429 = 3137411) B3137411
theorem B22310477 : Blo 2143435 22310477 := bstep (se 3 (by rfl) ⟨4183214, by rfl⟩ : syracuseStep 22310477 = 8366429) B8366429
theorem B14873651 : Blo 2143435 14873651 := bstep (se 1 (by rfl) ⟨11155238, by rfl⟩ : syracuseStep 14873651 = 22310477) B22310477
theorem B9915767 : Blo 2143435 9915767 := bstep (se 1 (by rfl) ⟨7436825, by rfl⟩ : syracuseStep 9915767 = 14873651) B14873651
theorem B6610511 : Blo 2143435 6610511 := bstep (se 1 (by rfl) ⟨4957883, by rfl⟩ : syracuseStep 6610511 = 9915767) B9915767
theorem B4407007 : Blo 2143435 4407007 := bstep (se 1 (by rfl) ⟨3305255, by rfl⟩ : syracuseStep 4407007 = 6610511) B6610511
theorem B5876009 : Blo 2143435 5876009 := bstep (se 2 (by rfl) ⟨2203503, by rfl⟩ : syracuseStep 5876009 = 4407007) B4407007
theorem B3917339 : Blo 2143435 3917339 := bstep (se 1 (by rfl) ⟨2938004, by rfl⟩ : syracuseStep 3917339 = 5876009) B5876009
theorem B2611559 : Blo 2143435 2611559 := bstep (se 1 (by rfl) ⟨1958669, by rfl⟩ : syracuseStep 2611559 = 3917339) B3917339
theorem B6964157 : Blo 2143435 6964157 := bstep (se 3 (by rfl) ⟨1305779, by rfl⟩ : syracuseStep 6964157 = 2611559) B2611559
theorem B4642771 : Blo 2143435 4642771 := bstep (se 1 (by rfl) ⟨3482078, by rfl⟩ : syracuseStep 4642771 = 6964157) B6964157
theorem B6190361 : Blo 2143435 6190361 := bstep (se 2 (by rfl) ⟨2321385, by rfl⟩ : syracuseStep 6190361 = 4642771) B4642771
theorem B4126907 : Blo 2143435 4126907 := bstep (se 1 (by rfl) ⟨3095180, by rfl⟩ : syracuseStep 4126907 = 6190361) B6190361
theorem B11005085 : Blo 2143435 11005085 := bstep (se 3 (by rfl) ⟨2063453, by rfl⟩ : syracuseStep 11005085 = 4126907) B4126907
theorem B29346893 : Blo 2143435 29346893 := bstep (se 3 (by rfl) ⟨5502542, by rfl⟩ : syracuseStep 29346893 = 11005085) B11005085
theorem B19564595 : Blo 2143435 19564595 := bstep (se 1 (by rfl) ⟨14673446, by rfl⟩ : syracuseStep 19564595 = 29346893) B29346893
theorem B13043063 : Blo 2143435 13043063 := bstep (se 1 (by rfl) ⟨9782297, by rfl⟩ : syracuseStep 13043063 = 19564595) B19564595
theorem B34781501 : Blo 2143435 34781501 := bstep (se 3 (by rfl) ⟨6521531, by rfl⟩ : syracuseStep 34781501 = 13043063) B13043063
theorem B23187667 : Blo 2143435 23187667 := bstep (se 1 (by rfl) ⟨17390750, by rfl⟩ : syracuseStep 23187667 = 34781501) B34781501
theorem B30916889 : Blo 2143435 30916889 := bstep (se 2 (by rfl) ⟨11593833, by rfl⟩ : syracuseStep 30916889 = 23187667) B23187667
theorem B20611259 : Blo 2143435 20611259 := bstep (se 1 (by rfl) ⟨15458444, by rfl⟩ : syracuseStep 20611259 = 30916889) B30916889
theorem B13740839 : Blo 2143435 13740839 := bstep (se 1 (by rfl) ⟨10305629, by rfl⟩ : syracuseStep 13740839 = 20611259) B20611259
theorem B9160559 : Blo 2143435 9160559 := bstep (se 1 (by rfl) ⟨6870419, by rfl⟩ : syracuseStep 9160559 = 13740839) B13740839
theorem B6107039 : Blo 2143435 6107039 := bstep (se 1 (by rfl) ⟨4580279, by rfl⟩ : syracuseStep 6107039 = 9160559) B9160559
theorem B4071359 : Blo 2143435 4071359 := bstep (se 1 (by rfl) ⟨3053519, by rfl⟩ : syracuseStep 4071359 = 6107039) B6107039
theorem B2714239 : Blo 2143435 2714239 := bstep (se 1 (by rfl) ⟨2035679, by rfl⟩ : syracuseStep 2714239 = 4071359) B4071359
theorem B3618985 : Blo 2143435 3618985 := bstep (se 2 (by rfl) ⟨1357119, by rfl⟩ : syracuseStep 3618985 = 2714239) B2714239
theorem B4825313 : Blo 2143435 4825313 := bstep (se 2 (by rfl) ⟨1809492, by rfl⟩ : syracuseStep 4825313 = 3618985) B3618985
theorem B3216875 : Blo 2143435 3216875 := bstep (se 1 (by rfl) ⟨2412656, by rfl⟩ : syracuseStep 3216875 = 4825313) B4825313
theorem B2144583 : Blo 2143435 2144583 := bstep (se 1 (by rfl) ⟨1608437, by rfl⟩ : syracuseStep 2144583 = 3216875) B3216875
theorem B2412661 : Blo 2143435 2412661 := bbase (se 5 (by rfl) ⟨113093, by rfl⟩ : syracuseStep 2412661 = 226187) (by norm_num)
theorem B3216881 : Blo 2143435 3216881 := bstep (se 2 (by rfl) ⟨1206330, by rfl⟩ : syracuseStep 3216881 = 2412661) B2412661
theorem B2144587 : Blo 2143435 2144587 := bstep (se 1 (by rfl) ⟨1608440, by rfl⟩ : syracuseStep 2144587 = 3216881) B3216881
theorem B2714249 : Blo 2143435 2714249 := bbase (se 2 (by rfl) ⟨1017843, by rfl⟩ : syracuseStep 2714249 = 2035687) (by norm_num)
theorem B7237997 : Blo 2143435 7237997 := bstep (se 3 (by rfl) ⟨1357124, by rfl⟩ : syracuseStep 7237997 = 2714249) B2714249
theorem B4825331 : Blo 2143435 4825331 := bstep (se 1 (by rfl) ⟨3618998, by rfl⟩ : syracuseStep 4825331 = 7237997) B7237997
theorem B3216887 : Blo 2143435 3216887 := bstep (se 1 (by rfl) ⟨2412665, by rfl⟩ : syracuseStep 3216887 = 4825331) B4825331
theorem B2144591 : Blo 2143435 2144591 := bstep (se 1 (by rfl) ⟨1608443, by rfl⟩ : syracuseStep 2144591 = 3216887) B3216887
theorem B3216893 : Blo 2143435 3216893 := bbase (se 3 (by rfl) ⟨603167, by rfl⟩ : syracuseStep 3216893 = 1206335) (by norm_num)
theorem B2144595 : Blo 2143435 2144595 := bstep (se 1 (by rfl) ⟨1608446, by rfl⟩ : syracuseStep 2144595 = 3216893) B3216893
theorem B4825349 : Blo 2143435 4825349 := bbase (se 4 (by rfl) ⟨452376, by rfl⟩ : syracuseStep 4825349 = 904753) (by norm_num)
theorem B3216899 : Blo 2143435 3216899 := bstep (se 1 (by rfl) ⟨2412674, by rfl⟩ : syracuseStep 3216899 = 4825349) B4825349
theorem B2144599 : Blo 2143435 2144599 := bstep (se 1 (by rfl) ⟨1608449, by rfl⟩ : syracuseStep 2144599 = 3216899) B3216899
theorem B4071397 : Blo 2143435 4071397 := bbase (se 4 (by rfl) ⟨381693, by rfl⟩ : syracuseStep 4071397 = 763387) (by norm_num)
theorem B5428529 : Blo 2143435 5428529 := bstep (se 2 (by rfl) ⟨2035698, by rfl⟩ : syracuseStep 5428529 = 4071397) B4071397
theorem B3619019 : Blo 2143435 3619019 := bstep (se 1 (by rfl) ⟨2714264, by rfl⟩ : syracuseStep 3619019 = 5428529) B5428529
theorem B2412679 : Blo 2143435 2412679 := bstep (se 1 (by rfl) ⟨1809509, by rfl⟩ : syracuseStep 2412679 = 3619019) B3619019
theorem B3216905 : Blo 2143435 3216905 := bstep (se 2 (by rfl) ⟨1206339, by rfl⟩ : syracuseStep 3216905 = 2412679) B2412679
theorem B2144603 : Blo 2143435 2144603 := bstep (se 1 (by rfl) ⟨1608452, by rfl⟩ : syracuseStep 2144603 = 3216905) B3216905
theorem B10857077 : Blo 2143435 10857077 := bbase (se 5 (by rfl) ⟨508925, by rfl⟩ : syracuseStep 10857077 = 1017851) (by norm_num)
theorem B7238051 : Blo 2143435 7238051 := bstep (se 1 (by rfl) ⟨5428538, by rfl⟩ : syracuseStep 7238051 = 10857077) B10857077
theorem B4825367 : Blo 2143435 4825367 := bstep (se 1 (by rfl) ⟨3619025, by rfl⟩ : syracuseStep 4825367 = 7238051) B7238051
theorem B3216911 : Blo 2143435 3216911 := bstep (se 1 (by rfl) ⟨2412683, by rfl⟩ : syracuseStep 3216911 = 4825367) B4825367
theorem B2144607 : Blo 2143435 2144607 := bstep (se 1 (by rfl) ⟨1608455, by rfl⟩ : syracuseStep 2144607 = 3216911) B3216911
theorem B3216917 : Blo 2143435 3216917 := bbase (se 6 (by rfl) ⟨75396, by rfl⟩ : syracuseStep 3216917 = 150793) (by norm_num)
theorem B2144611 : Blo 2143435 2144611 := bstep (se 1 (by rfl) ⟨1608458, by rfl⟩ : syracuseStep 2144611 = 3216917) B3216917
theorem B2751313 : Blo 2143435 2751313 := bbase (se 2 (by rfl) ⟨1031742, by rfl⟩ : syracuseStep 2751313 = 2063485) (by norm_num)
theorem B3668417 : Blo 2143435 3668417 := bstep (se 2 (by rfl) ⟨1375656, by rfl⟩ : syracuseStep 3668417 = 2751313) B2751313
theorem B2445611 : Blo 2143435 2445611 := bstep (se 1 (by rfl) ⟨1834208, by rfl⟩ : syracuseStep 2445611 = 3668417) B3668417
theorem B6521629 : Blo 2143435 6521629 := bstep (se 3 (by rfl) ⟨1222805, by rfl⟩ : syracuseStep 6521629 = 2445611) B2445611
theorem B8695505 : Blo 2143435 8695505 := bstep (se 2 (by rfl) ⟨3260814, by rfl⟩ : syracuseStep 8695505 = 6521629) B6521629
theorem B5797003 : Blo 2143435 5797003 := bstep (se 1 (by rfl) ⟨4347752, by rfl⟩ : syracuseStep 5797003 = 8695505) B8695505
theorem B7729337 : Blo 2143435 7729337 := bstep (se 2 (by rfl) ⟨2898501, by rfl⟩ : syracuseStep 7729337 = 5797003) B5797003
theorem B5152891 : Blo 2143435 5152891 := bstep (se 1 (by rfl) ⟨3864668, by rfl⟩ : syracuseStep 5152891 = 7729337) B7729337
theorem B6870521 : Blo 2143435 6870521 := bstep (se 2 (by rfl) ⟨2576445, by rfl⟩ : syracuseStep 6870521 = 5152891) B5152891
theorem B18321389 : Blo 2143435 18321389 := bstep (se 3 (by rfl) ⟨3435260, by rfl⟩ : syracuseStep 18321389 = 6870521) B6870521
theorem B12214259 : Blo 2143435 12214259 := bstep (se 1 (by rfl) ⟨9160694, by rfl⟩ : syracuseStep 12214259 = 18321389) B18321389
theorem B8142839 : Blo 2143435 8142839 := bstep (se 1 (by rfl) ⟨6107129, by rfl⟩ : syracuseStep 8142839 = 12214259) B12214259
theorem B5428559 : Blo 2143435 5428559 := bstep (se 1 (by rfl) ⟨4071419, by rfl⟩ : syracuseStep 5428559 = 8142839) B8142839
theorem B3619039 : Blo 2143435 3619039 := bstep (se 1 (by rfl) ⟨2714279, by rfl⟩ : syracuseStep 3619039 = 5428559) B5428559
theorem B4825385 : Blo 2143435 4825385 := bstep (se 2 (by rfl) ⟨1809519, by rfl⟩ : syracuseStep 4825385 = 3619039) B3619039
theorem B3216923 : Blo 2143435 3216923 := bstep (se 1 (by rfl) ⟨2412692, by rfl⟩ : syracuseStep 3216923 = 4825385) B4825385
theorem B2144615 : Blo 2143435 2144615 := bstep (se 1 (by rfl) ⟨1608461, by rfl⟩ : syracuseStep 2144615 = 3216923) B3216923
theorem B2412697 : Blo 2143435 2412697 := bbase (se 2 (by rfl) ⟨904761, by rfl⟩ : syracuseStep 2412697 = 1809523) (by norm_num)
theorem B3216929 : Blo 2143435 3216929 := bstep (se 2 (by rfl) ⟨1206348, by rfl⟩ : syracuseStep 3216929 = 2412697) B2412697
theorem B2144619 : Blo 2143435 2144619 := bstep (se 1 (by rfl) ⟨1608464, by rfl⟩ : syracuseStep 2144619 = 3216929) B3216929
theorem B8142869 : Blo 2143435 8142869 := bbase (se 6 (by rfl) ⟨190848, by rfl⟩ : syracuseStep 8142869 = 381697) (by norm_num)
theorem B5428579 : Blo 2143435 5428579 := bstep (se 1 (by rfl) ⟨4071434, by rfl⟩ : syracuseStep 5428579 = 8142869) B8142869
theorem B7238105 : Blo 2143435 7238105 := bstep (se 2 (by rfl) ⟨2714289, by rfl⟩ : syracuseStep 7238105 = 5428579) B5428579
theorem B4825403 : Blo 2143435 4825403 := bstep (se 1 (by rfl) ⟨3619052, by rfl⟩ : syracuseStep 4825403 = 7238105) B7238105
theorem B3216935 : Blo 2143435 3216935 := bstep (se 1 (by rfl) ⟨2412701, by rfl⟩ : syracuseStep 3216935 = 4825403) B4825403
theorem B2144623 : Blo 2143435 2144623 := bstep (se 1 (by rfl) ⟨1608467, by rfl⟩ : syracuseStep 2144623 = 3216935) B3216935
theorem B3216941 : Blo 2143435 3216941 := bbase (se 3 (by rfl) ⟨603176, by rfl⟩ : syracuseStep 3216941 = 1206353) (by norm_num)
theorem B2144627 : Blo 2143435 2144627 := bstep (se 1 (by rfl) ⟨1608470, by rfl⟩ : syracuseStep 2144627 = 3216941) B3216941
theorem B4825421 : Blo 2143435 4825421 := bbase (se 3 (by rfl) ⟨904766, by rfl⟩ : syracuseStep 4825421 = 1809533) (by norm_num)
theorem B3216947 : Blo 2143435 3216947 := bstep (se 1 (by rfl) ⟨2412710, by rfl⟩ : syracuseStep 3216947 = 4825421) B4825421
theorem B2144631 : Blo 2143435 2144631 := bstep (se 1 (by rfl) ⟨1608473, by rfl⟩ : syracuseStep 2144631 = 3216947) B3216947
theorem B2714305 : Blo 2143435 2714305 := bbase (se 2 (by rfl) ⟨1017864, by rfl⟩ : syracuseStep 2714305 = 2035729) (by norm_num)
theorem B3619073 : Blo 2143435 3619073 := bstep (se 2 (by rfl) ⟨1357152, by rfl⟩ : syracuseStep 3619073 = 2714305) B2714305
theorem B2412715 : Blo 2143435 2412715 := bstep (se 1 (by rfl) ⟨1809536, by rfl⟩ : syracuseStep 2412715 = 3619073) B3619073
theorem B3216953 : Blo 2143435 3216953 := bstep (se 2 (by rfl) ⟨1206357, by rfl⟩ : syracuseStep 3216953 = 2412715) B2412715
theorem B2144635 : Blo 2143435 2144635 := bstep (se 1 (by rfl) ⟨1608476, by rfl⟩ : syracuseStep 2144635 = 3216953) B3216953
theorem B5152949 : Blo 2143435 5152949 := bbase (se 5 (by rfl) ⟨241544, by rfl⟩ : syracuseStep 5152949 = 483089) (by norm_num)
theorem B3435299 : Blo 2143435 3435299 := bstep (se 1 (by rfl) ⟨2576474, by rfl⟩ : syracuseStep 3435299 = 5152949) B5152949
theorem B2290199 : Blo 2143435 2290199 := bstep (se 1 (by rfl) ⟨1717649, by rfl⟩ : syracuseStep 2290199 = 3435299) B3435299
theorem B24428789 : Blo 2143435 24428789 := bstep (se 5 (by rfl) ⟨1145099, by rfl⟩ : syracuseStep 24428789 = 2290199) B2290199
theorem B16285859 : Blo 2143435 16285859 := bstep (se 1 (by rfl) ⟨12214394, by rfl⟩ : syracuseStep 16285859 = 24428789) B24428789
theorem B10857239 : Blo 2143435 10857239 := bstep (se 1 (by rfl) ⟨8142929, by rfl⟩ : syracuseStep 10857239 = 16285859) B16285859
theorem B7238159 : Blo 2143435 7238159 := bstep (se 1 (by rfl) ⟨5428619, by rfl⟩ : syracuseStep 7238159 = 10857239) B10857239
theorem B4825439 : Blo 2143435 4825439 := bstep (se 1 (by rfl) ⟨3619079, by rfl⟩ : syracuseStep 4825439 = 7238159) B7238159
theorem B3216959 : Blo 2143435 3216959 := bstep (se 1 (by rfl) ⟨2412719, by rfl⟩ : syracuseStep 3216959 = 4825439) B4825439
theorem B2144639 : Blo 2143435 2144639 := bstep (se 1 (by rfl) ⟨1608479, by rfl⟩ : syracuseStep 2144639 = 3216959) B3216959
theorem B3216965 : Blo 2143435 3216965 := bbase (se 4 (by rfl) ⟨301590, by rfl⟩ : syracuseStep 3216965 = 603181) (by norm_num)
theorem B2144643 : Blo 2143435 2144643 := bstep (se 1 (by rfl) ⟨1608482, by rfl⟩ : syracuseStep 2144643 = 3216965) B3216965
theorem B3619093 : Blo 2143435 3619093 := bbase (se 6 (by rfl) ⟨84822, by rfl⟩ : syracuseStep 3619093 = 169645) (by norm_num)
theorem B4825457 : Blo 2143435 4825457 := bstep (se 2 (by rfl) ⟨1809546, by rfl⟩ : syracuseStep 4825457 = 3619093) B3619093
theorem B3216971 : Blo 2143435 3216971 := bstep (se 1 (by rfl) ⟨2412728, by rfl⟩ : syracuseStep 3216971 = 4825457) B4825457
theorem B2144647 : Blo 2143435 2144647 := bstep (se 1 (by rfl) ⟨1608485, by rfl⟩ : syracuseStep 2144647 = 3216971) B3216971
theorem B2412733 : Blo 2143435 2412733 := bbase (se 3 (by rfl) ⟨452387, by rfl⟩ : syracuseStep 2412733 = 904775) (by norm_num)
theorem B3216977 : Blo 2143435 3216977 := bstep (se 2 (by rfl) ⟨1206366, by rfl⟩ : syracuseStep 3216977 = 2412733) B2412733
theorem B2144651 : Blo 2143435 2144651 := bstep (se 1 (by rfl) ⟨1608488, by rfl⟩ : syracuseStep 2144651 = 3216977) B3216977
theorem B7238213 : Blo 2143435 7238213 := bbase (se 4 (by rfl) ⟨678582, by rfl⟩ : syracuseStep 7238213 = 1357165) (by norm_num)
theorem B4825475 : Blo 2143435 4825475 := bstep (se 1 (by rfl) ⟨3619106, by rfl⟩ : syracuseStep 4825475 = 7238213) B7238213
theorem B3216983 : Blo 2143435 3216983 := bstep (se 1 (by rfl) ⟨2412737, by rfl⟩ : syracuseStep 3216983 = 4825475) B4825475
theorem B2144655 : Blo 2143435 2144655 := bstep (se 1 (by rfl) ⟨1608491, by rfl⟩ : syracuseStep 2144655 = 3216983) B3216983
theorem B3216989 : Blo 2143435 3216989 := bbase (se 3 (by rfl) ⟨603185, by rfl⟩ : syracuseStep 3216989 = 1206371) (by norm_num)
theorem B2144659 : Blo 2143435 2144659 := bstep (se 1 (by rfl) ⟨1608494, by rfl⟩ : syracuseStep 2144659 = 3216989) B3216989
theorem B4825493 : Blo 2143435 4825493 := bbase (se 6 (by rfl) ⟨113097, by rfl⟩ : syracuseStep 4825493 = 226195) (by norm_num)
theorem B3216995 : Blo 2143435 3216995 := bstep (se 1 (by rfl) ⟨2412746, by rfl⟩ : syracuseStep 3216995 = 4825493) B4825493
theorem B2144663 : Blo 2143435 2144663 := bstep (se 1 (by rfl) ⟨1608497, by rfl⟩ : syracuseStep 2144663 = 3216995) B3216995
theorem B20893301 : Blo 2143435 20893301 := bbase (se 5 (by rfl) ⟨979373, by rfl⟩ : syracuseStep 20893301 = 1958747) (by norm_num)
theorem B13928867 : Blo 2143435 13928867 := bstep (se 1 (by rfl) ⟨10446650, by rfl⟩ : syracuseStep 13928867 = 20893301) B20893301
theorem B9285911 : Blo 2143435 9285911 := bstep (se 1 (by rfl) ⟨6964433, by rfl⟩ : syracuseStep 9285911 = 13928867) B13928867
theorem B6190607 : Blo 2143435 6190607 := bstep (se 1 (by rfl) ⟨4642955, by rfl⟩ : syracuseStep 6190607 = 9285911) B9285911
theorem B4127071 : Blo 2143435 4127071 := bstep (se 1 (by rfl) ⟨3095303, by rfl⟩ : syracuseStep 4127071 = 6190607) B6190607
theorem B5502761 : Blo 2143435 5502761 := bstep (se 2 (by rfl) ⟨2063535, by rfl⟩ : syracuseStep 5502761 = 4127071) B4127071
theorem B3668507 : Blo 2143435 3668507 := bstep (se 1 (by rfl) ⟨2751380, by rfl⟩ : syracuseStep 3668507 = 5502761) B5502761
theorem B2445671 : Blo 2143435 2445671 := bstep (se 1 (by rfl) ⟨1834253, by rfl⟩ : syracuseStep 2445671 = 3668507) B3668507
theorem B6521789 : Blo 2143435 6521789 := bstep (se 3 (by rfl) ⟨1222835, by rfl⟩ : syracuseStep 6521789 = 2445671) B2445671
theorem B4347859 : Blo 2143435 4347859 := bstep (se 1 (by rfl) ⟨3260894, by rfl⟩ : syracuseStep 4347859 = 6521789) B6521789
theorem B5797145 : Blo 2143435 5797145 := bstep (se 2 (by rfl) ⟨2173929, by rfl⟩ : syracuseStep 5797145 = 4347859) B4347859
theorem B3864763 : Blo 2143435 3864763 := bstep (se 1 (by rfl) ⟨2898572, by rfl⟩ : syracuseStep 3864763 = 5797145) B5797145
theorem B5153017 : Blo 2143435 5153017 := bstep (se 2 (by rfl) ⟨1932381, by rfl⟩ : syracuseStep 5153017 = 3864763) B3864763
theorem B6870689 : Blo 2143435 6870689 := bstep (se 2 (by rfl) ⟨2576508, by rfl⟩ : syracuseStep 6870689 = 5153017) B5153017
theorem B4580459 : Blo 2143435 4580459 := bstep (se 1 (by rfl) ⟨3435344, by rfl⟩ : syracuseStep 4580459 = 6870689) B6870689
theorem B3053639 : Blo 2143435 3053639 := bstep (se 1 (by rfl) ⟨2290229, by rfl⟩ : syracuseStep 3053639 = 4580459) B4580459
theorem B8143037 : Blo 2143435 8143037 := bstep (se 3 (by rfl) ⟨1526819, by rfl⟩ : syracuseStep 8143037 = 3053639) B3053639
theorem B5428691 : Blo 2143435 5428691 := bstep (se 1 (by rfl) ⟨4071518, by rfl⟩ : syracuseStep 5428691 = 8143037) B8143037
theorem B3619127 : Blo 2143435 3619127 := bstep (se 1 (by rfl) ⟨2714345, by rfl⟩ : syracuseStep 3619127 = 5428691) B5428691
theorem B2412751 : Blo 2143435 2412751 := bstep (se 1 (by rfl) ⟨1809563, by rfl⟩ : syracuseStep 2412751 = 3619127) B3619127
theorem B3217001 : Blo 2143435 3217001 := bstep (se 2 (by rfl) ⟨1206375, by rfl⟩ : syracuseStep 3217001 = 2412751) B2412751
theorem B2144667 : Blo 2143435 2144667 := bstep (se 1 (by rfl) ⟨1608500, by rfl⟩ : syracuseStep 2144667 = 3217001) B3217001
theorem B9160933 : Blo 2143435 9160933 := bbase (se 4 (by rfl) ⟨858837, by rfl⟩ : syracuseStep 9160933 = 1717675) (by norm_num)
theorem B12214577 : Blo 2143435 12214577 := bstep (se 2 (by rfl) ⟨4580466, by rfl⟩ : syracuseStep 12214577 = 9160933) B9160933
theorem B8143051 : Blo 2143435 8143051 := bstep (se 1 (by rfl) ⟨6107288, by rfl⟩ : syracuseStep 8143051 = 12214577) B12214577
theorem B10857401 : Blo 2143435 10857401 := bstep (se 2 (by rfl) ⟨4071525, by rfl⟩ : syracuseStep 10857401 = 8143051) B8143051
theorem B7238267 : Blo 2143435 7238267 := bstep (se 1 (by rfl) ⟨5428700, by rfl⟩ : syracuseStep 7238267 = 10857401) B10857401
theorem B4825511 : Blo 2143435 4825511 := bstep (se 1 (by rfl) ⟨3619133, by rfl⟩ : syracuseStep 4825511 = 7238267) B7238267
theorem B3217007 : Blo 2143435 3217007 := bstep (se 1 (by rfl) ⟨2412755, by rfl⟩ : syracuseStep 3217007 = 4825511) B4825511
theorem B2144671 : Blo 2143435 2144671 := bstep (se 1 (by rfl) ⟨1608503, by rfl⟩ : syracuseStep 2144671 = 3217007) B3217007
theorem B3217013 : Blo 2143435 3217013 := bbase (se 5 (by rfl) ⟨150797, by rfl⟩ : syracuseStep 3217013 = 301595) (by norm_num)
theorem B2144675 : Blo 2143435 2144675 := bstep (se 1 (by rfl) ⟨1608506, by rfl⟩ : syracuseStep 2144675 = 3217013) B3217013
theorem B4071541 : Blo 2143435 4071541 := bbase (se 5 (by rfl) ⟨190853, by rfl⟩ : syracuseStep 4071541 = 381707) (by norm_num)
theorem B5428721 : Blo 2143435 5428721 := bstep (se 2 (by rfl) ⟨2035770, by rfl⟩ : syracuseStep 5428721 = 4071541) B4071541
theorem B3619147 : Blo 2143435 3619147 := bstep (se 1 (by rfl) ⟨2714360, by rfl⟩ : syracuseStep 3619147 = 5428721) B5428721
theorem B4825529 : Blo 2143435 4825529 := bstep (se 2 (by rfl) ⟨1809573, by rfl⟩ : syracuseStep 4825529 = 3619147) B3619147
theorem B3217019 : Blo 2143435 3217019 := bstep (se 1 (by rfl) ⟨2412764, by rfl⟩ : syracuseStep 3217019 = 4825529) B4825529
theorem B2144679 : Blo 2143435 2144679 := bstep (se 1 (by rfl) ⟨1608509, by rfl⟩ : syracuseStep 2144679 = 3217019) B3217019
theorem B2412769 : Blo 2143435 2412769 := bbase (se 2 (by rfl) ⟨904788, by rfl⟩ : syracuseStep 2412769 = 1809577) (by norm_num)
theorem B3217025 : Blo 2143435 3217025 := bstep (se 2 (by rfl) ⟨1206384, by rfl⟩ : syracuseStep 3217025 = 2412769) B2412769
theorem B2144683 : Blo 2143435 2144683 := bstep (se 1 (by rfl) ⟨1608512, by rfl⟩ : syracuseStep 2144683 = 3217025) B3217025
theorem B5428741 : Blo 2143435 5428741 := bbase (se 4 (by rfl) ⟨508944, by rfl⟩ : syracuseStep 5428741 = 1017889) (by norm_num)
theorem B7238321 : Blo 2143435 7238321 := bstep (se 2 (by rfl) ⟨2714370, by rfl⟩ : syracuseStep 7238321 = 5428741) B5428741
theorem B4825547 : Blo 2143435 4825547 := bstep (se 1 (by rfl) ⟨3619160, by rfl⟩ : syracuseStep 4825547 = 7238321) B7238321
theorem B3217031 : Blo 2143435 3217031 := bstep (se 1 (by rfl) ⟨2412773, by rfl⟩ : syracuseStep 3217031 = 4825547) B4825547
theorem B2144687 : Blo 2143435 2144687 := bstep (se 1 (by rfl) ⟨1608515, by rfl⟩ : syracuseStep 2144687 = 3217031) B3217031
theorem B3217037 : Blo 2143435 3217037 := bbase (se 3 (by rfl) ⟨603194, by rfl⟩ : syracuseStep 3217037 = 1206389) (by norm_num)
theorem B2144691 : Blo 2143435 2144691 := bstep (se 1 (by rfl) ⟨1608518, by rfl⟩ : syracuseStep 2144691 = 3217037) B3217037
theorem B4825565 : Blo 2143435 4825565 := bbase (se 3 (by rfl) ⟨904793, by rfl⟩ : syracuseStep 4825565 = 1809587) (by norm_num)
theorem B3217043 : Blo 2143435 3217043 := bstep (se 1 (by rfl) ⟨2412782, by rfl⟩ : syracuseStep 3217043 = 4825565) B4825565
theorem B2144695 : Blo 2143435 2144695 := bstep (se 1 (by rfl) ⟨1608521, by rfl⟩ : syracuseStep 2144695 = 3217043) B3217043
theorem B3619181 : Blo 2143435 3619181 := bbase (se 3 (by rfl) ⟨678596, by rfl⟩ : syracuseStep 3619181 = 1357193) (by norm_num)
theorem B2412787 : Blo 2143435 2412787 := bstep (se 1 (by rfl) ⟨1809590, by rfl⟩ : syracuseStep 2412787 = 3619181) B3619181
theorem B3217049 : Blo 2143435 3217049 := bstep (se 2 (by rfl) ⟨1206393, by rfl⟩ : syracuseStep 3217049 = 2412787) B2412787
theorem B2144699 : Blo 2143435 2144699 := bstep (se 1 (by rfl) ⟨1608524, by rfl⟩ : syracuseStep 2144699 = 3217049) B3217049
theorem B4183445 : Blo 2143435 4183445 := bbase (se 6 (by rfl) ⟨98049, by rfl⟩ : syracuseStep 4183445 = 196099) (by norm_num)
theorem B11155853 : Blo 2143435 11155853 := bstep (se 3 (by rfl) ⟨2091722, by rfl⟩ : syracuseStep 11155853 = 4183445) B4183445
theorem B29748941 : Blo 2143435 29748941 := bstep (se 3 (by rfl) ⟨5577926, by rfl⟩ : syracuseStep 29748941 = 11155853) B11155853
theorem B19832627 : Blo 2143435 19832627 := bstep (se 1 (by rfl) ⟨14874470, by rfl⟩ : syracuseStep 19832627 = 29748941) B29748941
theorem B52887005 : Blo 2143435 52887005 := bstep (se 3 (by rfl) ⟨9916313, by rfl⟩ : syracuseStep 52887005 = 19832627) B19832627
theorem B35258003 : Blo 2143435 35258003 := bstep (se 1 (by rfl) ⟨26443502, by rfl⟩ : syracuseStep 35258003 = 52887005) B52887005
theorem B23505335 : Blo 2143435 23505335 := bstep (se 1 (by rfl) ⟨17629001, by rfl⟩ : syracuseStep 23505335 = 35258003) B35258003
theorem B15670223 : Blo 2143435 15670223 := bstep (se 1 (by rfl) ⟨11752667, by rfl⟩ : syracuseStep 15670223 = 23505335) B23505335
theorem B10446815 : Blo 2143435 10446815 := bstep (se 1 (by rfl) ⟨7835111, by rfl⟩ : syracuseStep 10446815 = 15670223) B15670223
theorem B27858173 : Blo 2143435 27858173 := bstep (se 3 (by rfl) ⟨5223407, by rfl⟩ : syracuseStep 27858173 = 10446815) B10446815
theorem B74288461 : Blo 2143435 74288461 := bstep (se 3 (by rfl) ⟨13929086, by rfl⟩ : syracuseStep 74288461 = 27858173) B27858173
theorem B99051281 : Blo 2143435 99051281 := bstep (se 2 (by rfl) ⟨37144230, by rfl⟩ : syracuseStep 99051281 = 74288461) B74288461
theorem B66034187 : Blo 2143435 66034187 := bstep (se 1 (by rfl) ⟨49525640, by rfl⟩ : syracuseStep 66034187 = 99051281) B99051281
theorem B44022791 : Blo 2143435 44022791 := bstep (se 1 (by rfl) ⟨33017093, by rfl⟩ : syracuseStep 44022791 = 66034187) B66034187
theorem B29348527 : Blo 2143435 29348527 := bstep (se 1 (by rfl) ⟨22011395, by rfl⟩ : syracuseStep 29348527 = 44022791) B44022791
theorem B39131369 : Blo 2143435 39131369 := bstep (se 2 (by rfl) ⟨14674263, by rfl⟩ : syracuseStep 39131369 = 29348527) B29348527
theorem B26087579 : Blo 2143435 26087579 := bstep (se 1 (by rfl) ⟨19565684, by rfl⟩ : syracuseStep 26087579 = 39131369) B39131369
theorem B17391719 : Blo 2143435 17391719 := bstep (se 1 (by rfl) ⟨13043789, by rfl⟩ : syracuseStep 17391719 = 26087579) B26087579
theorem B46377917 : Blo 2143435 46377917 := bstep (se 3 (by rfl) ⟨8695859, by rfl⟩ : syracuseStep 46377917 = 17391719) B17391719
theorem B30918611 : Blo 2143435 30918611 := bstep (se 1 (by rfl) ⟨23188958, by rfl⟩ : syracuseStep 30918611 = 46377917) B46377917
theorem B20612407 : Blo 2143435 20612407 := bstep (se 1 (by rfl) ⟨15459305, by rfl⟩ : syracuseStep 20612407 = 30918611) B30918611
theorem B27483209 : Blo 2143435 27483209 := bstep (se 2 (by rfl) ⟨10306203, by rfl⟩ : syracuseStep 27483209 = 20612407) B20612407
theorem B18322139 : Blo 2143435 18322139 := bstep (se 1 (by rfl) ⟨13741604, by rfl⟩ : syracuseStep 18322139 = 27483209) B27483209
theorem B12214759 : Blo 2143435 12214759 := bstep (se 1 (by rfl) ⟨9161069, by rfl⟩ : syracuseStep 12214759 = 18322139) B18322139
theorem B16286345 : Blo 2143435 16286345 := bstep (se 2 (by rfl) ⟨6107379, by rfl⟩ : syracuseStep 16286345 = 12214759) B12214759
theorem B10857563 : Blo 2143435 10857563 := bstep (se 1 (by rfl) ⟨8143172, by rfl⟩ : syracuseStep 10857563 = 16286345) B16286345
theorem B7238375 : Blo 2143435 7238375 := bstep (se 1 (by rfl) ⟨5428781, by rfl⟩ : syracuseStep 7238375 = 10857563) B10857563
theorem B4825583 : Blo 2143435 4825583 := bstep (se 1 (by rfl) ⟨3619187, by rfl⟩ : syracuseStep 4825583 = 7238375) B7238375
theorem B3217055 : Blo 2143435 3217055 := bstep (se 1 (by rfl) ⟨2412791, by rfl⟩ : syracuseStep 3217055 = 4825583) B4825583
theorem B2144703 : Blo 2143435 2144703 := bstep (se 1 (by rfl) ⟨1608527, by rfl⟩ : syracuseStep 2144703 = 3217055) B3217055
theorem B3217061 : Blo 2143435 3217061 := bbase (se 4 (by rfl) ⟨301599, by rfl⟩ : syracuseStep 3217061 = 603199) (by norm_num)
theorem B2144707 : Blo 2143435 2144707 := bstep (se 1 (by rfl) ⟨1608530, by rfl⟩ : syracuseStep 2144707 = 3217061) B3217061
theorem B2714401 : Blo 2143435 2714401 := bbase (se 2 (by rfl) ⟨1017900, by rfl⟩ : syracuseStep 2714401 = 2035801) (by norm_num)
theorem B3619201 : Blo 2143435 3619201 := bstep (se 2 (by rfl) ⟨1357200, by rfl⟩ : syracuseStep 3619201 = 2714401) B2714401
theorem B4825601 : Blo 2143435 4825601 := bstep (se 2 (by rfl) ⟨1809600, by rfl⟩ : syracuseStep 4825601 = 3619201) B3619201
theorem B3217067 : Blo 2143435 3217067 := bstep (se 1 (by rfl) ⟨2412800, by rfl⟩ : syracuseStep 3217067 = 4825601) B4825601
theorem B2144711 : Blo 2143435 2144711 := bstep (se 1 (by rfl) ⟨1608533, by rfl⟩ : syracuseStep 2144711 = 3217067) B3217067
theorem B2412805 : Blo 2143435 2412805 := bbase (se 4 (by rfl) ⟨226200, by rfl⟩ : syracuseStep 2412805 = 452401) (by norm_num)
theorem B3217073 : Blo 2143435 3217073 := bstep (se 2 (by rfl) ⟨1206402, by rfl⟩ : syracuseStep 3217073 = 2412805) B2412805
theorem B2144715 : Blo 2143435 2144715 := bstep (se 1 (by rfl) ⟨1608536, by rfl⟩ : syracuseStep 2144715 = 3217073) B3217073
theorem B2290285 : Blo 2143435 2290285 := bbase (se 3 (by rfl) ⟨429428, by rfl⟩ : syracuseStep 2290285 = 858857) (by norm_num)
theorem B3053713 : Blo 2143435 3053713 := bstep (se 2 (by rfl) ⟨1145142, by rfl⟩ : syracuseStep 3053713 = 2290285) B2290285
theorem B4071617 : Blo 2143435 4071617 := bstep (se 2 (by rfl) ⟨1526856, by rfl⟩ : syracuseStep 4071617 = 3053713) B3053713
theorem B2714411 : Blo 2143435 2714411 := bstep (se 1 (by rfl) ⟨2035808, by rfl⟩ : syracuseStep 2714411 = 4071617) B4071617
theorem B7238429 : Blo 2143435 7238429 := bstep (se 3 (by rfl) ⟨1357205, by rfl⟩ : syracuseStep 7238429 = 2714411) B2714411
theorem B4825619 : Blo 2143435 4825619 := bstep (se 1 (by rfl) ⟨3619214, by rfl⟩ : syracuseStep 4825619 = 7238429) B7238429
theorem B3217079 : Blo 2143435 3217079 := bstep (se 1 (by rfl) ⟨2412809, by rfl⟩ : syracuseStep 3217079 = 4825619) B4825619
theorem B2144719 : Blo 2143435 2144719 := bstep (se 1 (by rfl) ⟨1608539, by rfl⟩ : syracuseStep 2144719 = 3217079) B3217079
theorem B3217085 : Blo 2143435 3217085 := bbase (se 3 (by rfl) ⟨603203, by rfl⟩ : syracuseStep 3217085 = 1206407) (by norm_num)
theorem B2144723 : Blo 2143435 2144723 := bstep (se 1 (by rfl) ⟨1608542, by rfl⟩ : syracuseStep 2144723 = 3217085) B3217085
theorem B4825637 : Blo 2143435 4825637 := bbase (se 4 (by rfl) ⟨452403, by rfl⟩ : syracuseStep 4825637 = 904807) (by norm_num)
theorem B3217091 : Blo 2143435 3217091 := bstep (se 1 (by rfl) ⟨2412818, by rfl⟩ : syracuseStep 3217091 = 4825637) B4825637
theorem B2144727 : Blo 2143435 2144727 := bstep (se 1 (by rfl) ⟨1608545, by rfl⟩ : syracuseStep 2144727 = 3217091) B3217091
theorem B5428853 : Blo 2143435 5428853 := bbase (se 5 (by rfl) ⟨254477, by rfl⟩ : syracuseStep 5428853 = 508955) (by norm_num)
theorem B3619235 : Blo 2143435 3619235 := bstep (se 1 (by rfl) ⟨2714426, by rfl⟩ : syracuseStep 3619235 = 5428853) B5428853
theorem B2412823 : Blo 2143435 2412823 := bstep (se 1 (by rfl) ⟨1809617, by rfl⟩ : syracuseStep 2412823 = 3619235) B3619235
theorem B3217097 : Blo 2143435 3217097 := bstep (se 2 (by rfl) ⟨1206411, by rfl⟩ : syracuseStep 3217097 = 2412823) B2412823
theorem B2144731 : Blo 2143435 2144731 := bstep (se 1 (by rfl) ⟨1608548, by rfl⟩ : syracuseStep 2144731 = 3217097) B3217097
theorem B6701173 : Blo 2143435 6701173 := bbase (se 5 (by rfl) ⟨314117, by rfl⟩ : syracuseStep 6701173 = 628235) (by norm_num)
theorem B35739589 : Blo 2143435 35739589 := bstep (se 4 (by rfl) ⟨3350586, by rfl⟩ : syracuseStep 35739589 = 6701173) B6701173
theorem B47652785 : Blo 2143435 47652785 := bstep (se 2 (by rfl) ⟨17869794, by rfl⟩ : syracuseStep 47652785 = 35739589) B35739589
theorem B31768523 : Blo 2143435 31768523 := bstep (se 1 (by rfl) ⟨23826392, by rfl⟩ : syracuseStep 31768523 = 47652785) B47652785
theorem B21179015 : Blo 2143435 21179015 := bstep (se 1 (by rfl) ⟨15884261, by rfl⟩ : syracuseStep 21179015 = 31768523) B31768523
theorem B14119343 : Blo 2143435 14119343 := bstep (se 1 (by rfl) ⟨10589507, by rfl⟩ : syracuseStep 14119343 = 21179015) B21179015
theorem B9412895 : Blo 2143435 9412895 := bstep (se 1 (by rfl) ⟨7059671, by rfl⟩ : syracuseStep 9412895 = 14119343) B14119343
theorem B25101053 : Blo 2143435 25101053 := bstep (se 3 (by rfl) ⟨4706447, by rfl⟩ : syracuseStep 25101053 = 9412895) B9412895
theorem B16734035 : Blo 2143435 16734035 := bstep (se 1 (by rfl) ⟨12550526, by rfl⟩ : syracuseStep 16734035 = 25101053) B25101053
theorem B11156023 : Blo 2143435 11156023 := bstep (se 1 (by rfl) ⟨8367017, by rfl⟩ : syracuseStep 11156023 = 16734035) B16734035
theorem B14874697 : Blo 2143435 14874697 := bstep (se 2 (by rfl) ⟨5578011, by rfl⟩ : syracuseStep 14874697 = 11156023) B11156023
theorem B79331717 : Blo 2143435 79331717 := bstep (se 4 (by rfl) ⟨7437348, by rfl⟩ : syracuseStep 79331717 = 14874697) B14874697
theorem B52887811 : Blo 2143435 52887811 := bstep (se 1 (by rfl) ⟨39665858, by rfl⟩ : syracuseStep 52887811 = 79331717) B79331717
theorem B70517081 : Blo 2143435 70517081 := bstep (se 2 (by rfl) ⟨26443905, by rfl⟩ : syracuseStep 70517081 = 52887811) B52887811
theorem B47011387 : Blo 2143435 47011387 := bstep (se 1 (by rfl) ⟨35258540, by rfl⟩ : syracuseStep 47011387 = 70517081) B70517081
theorem B62681849 : Blo 2143435 62681849 := bstep (se 2 (by rfl) ⟨23505693, by rfl⟩ : syracuseStep 62681849 = 47011387) B47011387
theorem B41787899 : Blo 2143435 41787899 := bstep (se 1 (by rfl) ⟨31340924, by rfl⟩ : syracuseStep 41787899 = 62681849) B62681849
theorem B27858599 : Blo 2143435 27858599 := bstep (se 1 (by rfl) ⟨20893949, by rfl⟩ : syracuseStep 27858599 = 41787899) B41787899
theorem B18572399 : Blo 2143435 18572399 := bstep (se 1 (by rfl) ⟨13929299, by rfl⟩ : syracuseStep 18572399 = 27858599) B27858599
theorem B12381599 : Blo 2143435 12381599 := bstep (se 1 (by rfl) ⟨9286199, by rfl⟩ : syracuseStep 12381599 = 18572399) B18572399
theorem B8254399 : Blo 2143435 8254399 := bstep (se 1 (by rfl) ⟨6190799, by rfl⟩ : syracuseStep 8254399 = 12381599) B12381599
theorem B11005865 : Blo 2143435 11005865 := bstep (se 2 (by rfl) ⟨4127199, by rfl⟩ : syracuseStep 11005865 = 8254399) B8254399
theorem B7337243 : Blo 2143435 7337243 := bstep (se 1 (by rfl) ⟨5502932, by rfl⟩ : syracuseStep 7337243 = 11005865) B11005865
theorem B19565981 : Blo 2143435 19565981 := bstep (se 3 (by rfl) ⟨3668621, by rfl⟩ : syracuseStep 19565981 = 7337243) B7337243
theorem B13043987 : Blo 2143435 13043987 := bstep (se 1 (by rfl) ⟨9782990, by rfl⟩ : syracuseStep 13043987 = 19565981) B19565981
theorem B8695991 : Blo 2143435 8695991 := bstep (se 1 (by rfl) ⟨6521993, by rfl⟩ : syracuseStep 8695991 = 13043987) B13043987
theorem B5797327 : Blo 2143435 5797327 := bstep (se 1 (by rfl) ⟨4347995, by rfl⟩ : syracuseStep 5797327 = 8695991) B8695991
theorem B7729769 : Blo 2143435 7729769 := bstep (se 2 (by rfl) ⟨2898663, by rfl⟩ : syracuseStep 7729769 = 5797327) B5797327
theorem B20612717 : Blo 2143435 20612717 := bstep (se 3 (by rfl) ⟨3864884, by rfl⟩ : syracuseStep 20612717 = 7729769) B7729769
theorem B13741811 : Blo 2143435 13741811 := bstep (se 1 (by rfl) ⟨10306358, by rfl⟩ : syracuseStep 13741811 = 20612717) B20612717
theorem B9161207 : Blo 2143435 9161207 := bstep (se 1 (by rfl) ⟨6870905, by rfl⟩ : syracuseStep 9161207 = 13741811) B13741811
theorem B6107471 : Blo 2143435 6107471 := bstep (se 1 (by rfl) ⟨4580603, by rfl⟩ : syracuseStep 6107471 = 9161207) B9161207
theorem B4071647 : Blo 2143435 4071647 := bstep (se 1 (by rfl) ⟨3053735, by rfl⟩ : syracuseStep 4071647 = 6107471) B6107471
theorem B10857725 : Blo 2143435 10857725 := bstep (se 3 (by rfl) ⟨2035823, by rfl⟩ : syracuseStep 10857725 = 4071647) B4071647
theorem B7238483 : Blo 2143435 7238483 := bstep (se 1 (by rfl) ⟨5428862, by rfl⟩ : syracuseStep 7238483 = 10857725) B10857725
theorem B4825655 : Blo 2143435 4825655 := bstep (se 1 (by rfl) ⟨3619241, by rfl⟩ : syracuseStep 4825655 = 7238483) B7238483
theorem B3217103 : Blo 2143435 3217103 := bstep (se 1 (by rfl) ⟨2412827, by rfl⟩ : syracuseStep 3217103 = 4825655) B4825655
theorem B2144735 : Blo 2143435 2144735 := bstep (se 1 (by rfl) ⟨1608551, by rfl⟩ : syracuseStep 2144735 = 3217103) B3217103
theorem B3217109 : Blo 2143435 3217109 := bbase (se 7 (by rfl) ⟨37700, by rfl⟩ : syracuseStep 3217109 = 75401) (by norm_num)
theorem B2144739 : Blo 2143435 2144739 := bstep (se 1 (by rfl) ⟨1608554, by rfl⟩ : syracuseStep 2144739 = 3217109) B3217109
theorem B4580621 : Blo 2143435 4580621 := bbase (se 3 (by rfl) ⟨858866, by rfl⟩ : syracuseStep 4580621 = 1717733) (by norm_num)
theorem B3053747 : Blo 2143435 3053747 := bstep (se 1 (by rfl) ⟨2290310, by rfl⟩ : syracuseStep 3053747 = 4580621) B4580621
theorem B8143325 : Blo 2143435 8143325 := bstep (se 3 (by rfl) ⟨1526873, by rfl⟩ : syracuseStep 8143325 = 3053747) B3053747
theorem B5428883 : Blo 2143435 5428883 := bstep (se 1 (by rfl) ⟨4071662, by rfl⟩ : syracuseStep 5428883 = 8143325) B8143325
theorem B3619255 : Blo 2143435 3619255 := bstep (se 1 (by rfl) ⟨2714441, by rfl⟩ : syracuseStep 3619255 = 5428883) B5428883
theorem B4825673 : Blo 2143435 4825673 := bstep (se 2 (by rfl) ⟨1809627, by rfl⟩ : syracuseStep 4825673 = 3619255) B3619255
theorem B3217115 : Blo 2143435 3217115 := bstep (se 1 (by rfl) ⟨2412836, by rfl⟩ : syracuseStep 3217115 = 4825673) B4825673
theorem B2144743 : Blo 2143435 2144743 := bstep (se 1 (by rfl) ⟨1608557, by rfl⟩ : syracuseStep 2144743 = 3217115) B3217115
theorem B2412841 : Blo 2143435 2412841 := bbase (se 2 (by rfl) ⟨904815, by rfl⟩ : syracuseStep 2412841 = 1809631) (by norm_num)
theorem B3217121 : Blo 2143435 3217121 := bstep (se 2 (by rfl) ⟨1206420, by rfl⟩ : syracuseStep 3217121 = 2412841) B2412841
theorem B2144747 : Blo 2143435 2144747 := bstep (se 1 (by rfl) ⟨1608560, by rfl⟩ : syracuseStep 2144747 = 3217121) B3217121
theorem B2898685 : Blo 2143435 2898685 := bbase (se 3 (by rfl) ⟨543503, by rfl⟩ : syracuseStep 2898685 = 1087007) (by norm_num)
theorem B15459653 : Blo 2143435 15459653 := bstep (se 4 (by rfl) ⟨1449342, by rfl⟩ : syracuseStep 15459653 = 2898685) B2898685
theorem B10306435 : Blo 2143435 10306435 := bstep (se 1 (by rfl) ⟨7729826, by rfl⟩ : syracuseStep 10306435 = 15459653) B15459653
theorem B13741913 : Blo 2143435 13741913 := bstep (se 2 (by rfl) ⟨5153217, by rfl⟩ : syracuseStep 13741913 = 10306435) B10306435
theorem B9161275 : Blo 2143435 9161275 := bstep (se 1 (by rfl) ⟨6870956, by rfl⟩ : syracuseStep 9161275 = 13741913) B13741913
theorem B12215033 : Blo 2143435 12215033 := bstep (se 2 (by rfl) ⟨4580637, by rfl⟩ : syracuseStep 12215033 = 9161275) B9161275
theorem B8143355 : Blo 2143435 8143355 := bstep (se 1 (by rfl) ⟨6107516, by rfl⟩ : syracuseStep 8143355 = 12215033) B12215033
theorem B5428903 : Blo 2143435 5428903 := bstep (se 1 (by rfl) ⟨4071677, by rfl⟩ : syracuseStep 5428903 = 8143355) B8143355
theorem B7238537 : Blo 2143435 7238537 := bstep (se 2 (by rfl) ⟨2714451, by rfl⟩ : syracuseStep 7238537 = 5428903) B5428903
theorem B4825691 : Blo 2143435 4825691 := bstep (se 1 (by rfl) ⟨3619268, by rfl⟩ : syracuseStep 4825691 = 7238537) B7238537
theorem B3217127 : Blo 2143435 3217127 := bstep (se 1 (by rfl) ⟨2412845, by rfl⟩ : syracuseStep 3217127 = 4825691) B4825691
theorem B2144751 : Blo 2143435 2144751 := bstep (se 1 (by rfl) ⟨1608563, by rfl⟩ : syracuseStep 2144751 = 3217127) B3217127
theorem B3217133 : Blo 2143435 3217133 := bbase (se 3 (by rfl) ⟨603212, by rfl⟩ : syracuseStep 3217133 = 1206425) (by norm_num)
theorem B2144755 : Blo 2143435 2144755 := bstep (se 1 (by rfl) ⟨1608566, by rfl⟩ : syracuseStep 2144755 = 3217133) B3217133
theorem B4825709 : Blo 2143435 4825709 := bbase (se 3 (by rfl) ⟨904820, by rfl⟩ : syracuseStep 4825709 = 1809641) (by norm_num)
theorem B3217139 : Blo 2143435 3217139 := bstep (se 1 (by rfl) ⟨2412854, by rfl⟩ : syracuseStep 3217139 = 4825709) B4825709
theorem B2144759 : Blo 2143435 2144759 := bstep (se 1 (by rfl) ⟨1608569, by rfl⟩ : syracuseStep 2144759 = 3217139) B3217139
theorem B4071701 : Blo 2143435 4071701 := bbase (se 6 (by rfl) ⟨95430, by rfl⟩ : syracuseStep 4071701 = 190861) (by norm_num)
theorem B2714467 : Blo 2143435 2714467 := bstep (se 1 (by rfl) ⟨2035850, by rfl⟩ : syracuseStep 2714467 = 4071701) B4071701
theorem B3619289 : Blo 2143435 3619289 := bstep (se 2 (by rfl) ⟨1357233, by rfl⟩ : syracuseStep 3619289 = 2714467) B2714467
theorem B2412859 : Blo 2143435 2412859 := bstep (se 1 (by rfl) ⟨1809644, by rfl⟩ : syracuseStep 2412859 = 3619289) B3619289
theorem B3217145 : Blo 2143435 3217145 := bstep (se 2 (by rfl) ⟨1206429, by rfl⟩ : syracuseStep 3217145 = 2412859) B2412859
theorem B2144763 : Blo 2143435 2144763 := bstep (se 1 (by rfl) ⟨1608572, by rfl⟩ : syracuseStep 2144763 = 3217145) B3217145
theorem B12381781 : Blo 2143435 12381781 := bbase (se 8 (by rfl) ⟨72549, by rfl⟩ : syracuseStep 12381781 = 145099) (by norm_num)
theorem B16509041 : Blo 2143435 16509041 := bstep (se 2 (by rfl) ⟨6190890, by rfl⟩ : syracuseStep 16509041 = 12381781) B12381781
theorem B11006027 : Blo 2143435 11006027 := bstep (se 1 (by rfl) ⟨8254520, by rfl⟩ : syracuseStep 11006027 = 16509041) B16509041
theorem B7337351 : Blo 2143435 7337351 := bstep (se 1 (by rfl) ⟨5503013, by rfl⟩ : syracuseStep 7337351 = 11006027) B11006027
theorem B4891567 : Blo 2143435 4891567 := bstep (se 1 (by rfl) ⟨3668675, by rfl⟩ : syracuseStep 4891567 = 7337351) B7337351
theorem B6522089 : Blo 2143435 6522089 := bstep (se 2 (by rfl) ⟨2445783, by rfl⟩ : syracuseStep 6522089 = 4891567) B4891567
theorem B69568949 : Blo 2143435 69568949 := bstep (se 5 (by rfl) ⟨3261044, by rfl⟩ : syracuseStep 69568949 = 6522089) B6522089
theorem B46379299 : Blo 2143435 46379299 := bstep (se 1 (by rfl) ⟨34784474, by rfl⟩ : syracuseStep 46379299 = 69568949) B69568949
theorem B61839065 : Blo 2143435 61839065 := bstep (se 2 (by rfl) ⟨23189649, by rfl⟩ : syracuseStep 61839065 = 46379299) B46379299
theorem B41226043 : Blo 2143435 41226043 := bstep (se 1 (by rfl) ⟨30919532, by rfl⟩ : syracuseStep 41226043 = 61839065) B61839065
theorem B54968057 : Blo 2143435 54968057 := bstep (se 2 (by rfl) ⟨20613021, by rfl⟩ : syracuseStep 54968057 = 41226043) B41226043
theorem B36645371 : Blo 2143435 36645371 := bstep (se 1 (by rfl) ⟨27484028, by rfl⟩ : syracuseStep 36645371 = 54968057) B54968057
theorem B24430247 : Blo 2143435 24430247 := bstep (se 1 (by rfl) ⟨18322685, by rfl⟩ : syracuseStep 24430247 = 36645371) B36645371
theorem B16286831 : Blo 2143435 16286831 := bstep (se 1 (by rfl) ⟨12215123, by rfl⟩ : syracuseStep 16286831 = 24430247) B24430247
theorem B10857887 : Blo 2143435 10857887 := bstep (se 1 (by rfl) ⟨8143415, by rfl⟩ : syracuseStep 10857887 = 16286831) B16286831
theorem B7238591 : Blo 2143435 7238591 := bstep (se 1 (by rfl) ⟨5428943, by rfl⟩ : syracuseStep 7238591 = 10857887) B10857887
theorem B4825727 : Blo 2143435 4825727 := bstep (se 1 (by rfl) ⟨3619295, by rfl⟩ : syracuseStep 4825727 = 7238591) B7238591
theorem B3217151 : Blo 2143435 3217151 := bstep (se 1 (by rfl) ⟨2412863, by rfl⟩ : syracuseStep 3217151 = 4825727) B4825727
theorem B2144767 : Blo 2143435 2144767 := bstep (se 1 (by rfl) ⟨1608575, by rfl⟩ : syracuseStep 2144767 = 3217151) B3217151
theorem B3217157 : Blo 2143435 3217157 := bbase (se 4 (by rfl) ⟨301608, by rfl⟩ : syracuseStep 3217157 = 603217) (by norm_num)
theorem B2144771 : Blo 2143435 2144771 := bstep (se 1 (by rfl) ⟨1608578, by rfl⟩ : syracuseStep 2144771 = 3217157) B3217157
theorem B3619309 : Blo 2143435 3619309 := bbase (se 3 (by rfl) ⟨678620, by rfl⟩ : syracuseStep 3619309 = 1357241) (by norm_num)
theorem B4825745 : Blo 2143435 4825745 := bstep (se 2 (by rfl) ⟨1809654, by rfl⟩ : syracuseStep 4825745 = 3619309) B3619309
theorem B3217163 : Blo 2143435 3217163 := bstep (se 1 (by rfl) ⟨2412872, by rfl⟩ : syracuseStep 3217163 = 4825745) B4825745
theorem B2144775 : Blo 2143435 2144775 := bstep (se 1 (by rfl) ⟨1608581, by rfl⟩ : syracuseStep 2144775 = 3217163) B3217163
theorem B2412877 : Blo 2143435 2412877 := bbase (se 3 (by rfl) ⟨452414, by rfl⟩ : syracuseStep 2412877 = 904829) (by norm_num)
theorem B3217169 : Blo 2143435 3217169 := bstep (se 2 (by rfl) ⟨1206438, by rfl⟩ : syracuseStep 3217169 = 2412877) B2412877
theorem B2144779 : Blo 2143435 2144779 := bstep (se 1 (by rfl) ⟨1608584, by rfl⟩ : syracuseStep 2144779 = 3217169) B3217169
theorem B7238645 : Blo 2143435 7238645 := bbase (se 5 (by rfl) ⟨339311, by rfl⟩ : syracuseStep 7238645 = 678623) (by norm_num)
theorem B4825763 : Blo 2143435 4825763 := bstep (se 1 (by rfl) ⟨3619322, by rfl⟩ : syracuseStep 4825763 = 7238645) B7238645
theorem B3217175 : Blo 2143435 3217175 := bstep (se 1 (by rfl) ⟨2412881, by rfl⟩ : syracuseStep 3217175 = 4825763) B4825763
theorem B2144783 : Blo 2143435 2144783 := bstep (se 1 (by rfl) ⟨1608587, by rfl⟩ : syracuseStep 2144783 = 3217175) B3217175
theorem B3217181 : Blo 2143435 3217181 := bbase (se 3 (by rfl) ⟨603221, by rfl⟩ : syracuseStep 3217181 = 1206443) (by norm_num)
theorem B2144787 : Blo 2143435 2144787 := bstep (se 1 (by rfl) ⟨1608590, by rfl⟩ : syracuseStep 2144787 = 3217181) B3217181
theorem B4825781 : Blo 2143435 4825781 := bbase (se 5 (by rfl) ⟨226208, by rfl⟩ : syracuseStep 4825781 = 452417) (by norm_num)
theorem B3217187 : Blo 2143435 3217187 := bstep (se 1 (by rfl) ⟨2412890, by rfl⟩ : syracuseStep 3217187 = 4825781) B4825781
theorem B2144791 : Blo 2143435 2144791 := bstep (se 1 (by rfl) ⟨1608593, by rfl⟩ : syracuseStep 2144791 = 3217187) B3217187
theorem B12215285 : Blo 2143435 12215285 := bbase (se 5 (by rfl) ⟨572591, by rfl⟩ : syracuseStep 12215285 = 1145183) (by norm_num)
theorem B8143523 : Blo 2143435 8143523 := bstep (se 1 (by rfl) ⟨6107642, by rfl⟩ : syracuseStep 8143523 = 12215285) B12215285
theorem B5429015 : Blo 2143435 5429015 := bstep (se 1 (by rfl) ⟨4071761, by rfl⟩ : syracuseStep 5429015 = 8143523) B8143523
theorem B3619343 : Blo 2143435 3619343 := bstep (se 1 (by rfl) ⟨2714507, by rfl⟩ : syracuseStep 3619343 = 5429015) B5429015
theorem B2412895 : Blo 2143435 2412895 := bstep (se 1 (by rfl) ⟨1809671, by rfl⟩ : syracuseStep 2412895 = 3619343) B3619343
theorem B3217193 : Blo 2143435 3217193 := bstep (se 2 (by rfl) ⟨1206447, by rfl⟩ : syracuseStep 3217193 = 2412895) B2412895
theorem B2144795 : Blo 2143435 2144795 := bstep (se 1 (by rfl) ⟨1608596, by rfl⟩ : syracuseStep 2144795 = 3217193) B3217193
theorem B6107653 : Blo 2143435 6107653 := bbase (se 4 (by rfl) ⟨572592, by rfl⟩ : syracuseStep 6107653 = 1145185) (by norm_num)
theorem B8143537 : Blo 2143435 8143537 := bstep (se 2 (by rfl) ⟨3053826, by rfl⟩ : syracuseStep 8143537 = 6107653) B6107653
theorem B10858049 : Blo 2143435 10858049 := bstep (se 2 (by rfl) ⟨4071768, by rfl⟩ : syracuseStep 10858049 = 8143537) B8143537
theorem B7238699 : Blo 2143435 7238699 := bstep (se 1 (by rfl) ⟨5429024, by rfl⟩ : syracuseStep 7238699 = 10858049) B10858049
theorem B4825799 : Blo 2143435 4825799 := bstep (se 1 (by rfl) ⟨3619349, by rfl⟩ : syracuseStep 4825799 = 7238699) B7238699
theorem B3217199 : Blo 2143435 3217199 := bstep (se 1 (by rfl) ⟨2412899, by rfl⟩ : syracuseStep 3217199 = 4825799) B4825799
theorem B2144799 : Blo 2143435 2144799 := bstep (se 1 (by rfl) ⟨1608599, by rfl⟩ : syracuseStep 2144799 = 3217199) B3217199
theorem B3217205 : Blo 2143435 3217205 := bbase (se 5 (by rfl) ⟨150806, by rfl⟩ : syracuseStep 3217205 = 301613) (by norm_num)
theorem B2144803 : Blo 2143435 2144803 := bstep (se 1 (by rfl) ⟨1608602, by rfl⟩ : syracuseStep 2144803 = 3217205) B3217205
theorem B5429045 : Blo 2143435 5429045 := bbase (se 5 (by rfl) ⟨254486, by rfl⟩ : syracuseStep 5429045 = 508973) (by norm_num)
theorem B3619363 : Blo 2143435 3619363 := bstep (se 1 (by rfl) ⟨2714522, by rfl⟩ : syracuseStep 3619363 = 5429045) B5429045
theorem B4825817 : Blo 2143435 4825817 := bstep (se 2 (by rfl) ⟨1809681, by rfl⟩ : syracuseStep 4825817 = 3619363) B3619363
theorem B3217211 : Blo 2143435 3217211 := bstep (se 1 (by rfl) ⟨2412908, by rfl⟩ : syracuseStep 3217211 = 4825817) B4825817
theorem B2144807 : Blo 2143435 2144807 := bstep (se 1 (by rfl) ⟨1608605, by rfl⟩ : syracuseStep 2144807 = 3217211) B3217211
theorem B2412913 : Blo 2143435 2412913 := bbase (se 2 (by rfl) ⟨904842, by rfl⟩ : syracuseStep 2412913 = 1809685) (by norm_num)
theorem B3217217 : Blo 2143435 3217217 := bstep (se 2 (by rfl) ⟨1206456, by rfl⟩ : syracuseStep 3217217 = 2412913) B2412913
theorem B2144811 : Blo 2143435 2144811 := bstep (se 1 (by rfl) ⟨1608608, by rfl⟩ : syracuseStep 2144811 = 3217217) B3217217
theorem B3435581 : Blo 2143435 3435581 := bbase (se 3 (by rfl) ⟨644171, by rfl⟩ : syracuseStep 3435581 = 1288343) (by norm_num)
theorem B9161549 : Blo 2143435 9161549 := bstep (se 3 (by rfl) ⟨1717790, by rfl⟩ : syracuseStep 9161549 = 3435581) B3435581
theorem B6107699 : Blo 2143435 6107699 := bstep (se 1 (by rfl) ⟨4580774, by rfl⟩ : syracuseStep 6107699 = 9161549) B9161549
theorem B4071799 : Blo 2143435 4071799 := bstep (se 1 (by rfl) ⟨3053849, by rfl⟩ : syracuseStep 4071799 = 6107699) B6107699
theorem B5429065 : Blo 2143435 5429065 := bstep (se 2 (by rfl) ⟨2035899, by rfl⟩ : syracuseStep 5429065 = 4071799) B4071799
theorem B7238753 : Blo 2143435 7238753 := bstep (se 2 (by rfl) ⟨2714532, by rfl⟩ : syracuseStep 7238753 = 5429065) B5429065
theorem B4825835 : Blo 2143435 4825835 := bstep (se 1 (by rfl) ⟨3619376, by rfl⟩ : syracuseStep 4825835 = 7238753) B7238753
theorem B3217223 : Blo 2143435 3217223 := bstep (se 1 (by rfl) ⟨2412917, by rfl⟩ : syracuseStep 3217223 = 4825835) B4825835
theorem B2144815 : Blo 2143435 2144815 := bstep (se 1 (by rfl) ⟨1608611, by rfl⟩ : syracuseStep 2144815 = 3217223) B3217223
theorem B3217229 : Blo 2143435 3217229 := bbase (se 3 (by rfl) ⟨603230, by rfl⟩ : syracuseStep 3217229 = 1206461) (by norm_num)
theorem B2144819 : Blo 2143435 2144819 := bstep (se 1 (by rfl) ⟨1608614, by rfl⟩ : syracuseStep 2144819 = 3217229) B3217229
theorem B4825853 : Blo 2143435 4825853 := bbase (se 3 (by rfl) ⟨904847, by rfl⟩ : syracuseStep 4825853 = 1809695) (by norm_num)
theorem B3217235 : Blo 2143435 3217235 := bstep (se 1 (by rfl) ⟨2412926, by rfl⟩ : syracuseStep 3217235 = 4825853) B4825853
theorem B2144823 : Blo 2143435 2144823 := bstep (se 1 (by rfl) ⟨1608617, by rfl⟩ : syracuseStep 2144823 = 3217235) B3217235
theorem B3619397 : Blo 2143435 3619397 := bbase (se 4 (by rfl) ⟨339318, by rfl⟩ : syracuseStep 3619397 = 678637) (by norm_num)
theorem B2412931 : Blo 2143435 2412931 := bstep (se 1 (by rfl) ⟨1809698, by rfl⟩ : syracuseStep 2412931 = 3619397) B3619397
theorem B3217241 : Blo 2143435 3217241 := bstep (se 2 (by rfl) ⟨1206465, by rfl⟩ : syracuseStep 3217241 = 2412931) B2412931
theorem B2144827 : Blo 2143435 2144827 := bstep (se 1 (by rfl) ⟨1608620, by rfl⟩ : syracuseStep 2144827 = 3217241) B3217241
theorem B16287317 : Blo 2143435 16287317 := bbase (se 8 (by rfl) ⟨95433, by rfl⟩ : syracuseStep 16287317 = 190867) (by norm_num)
theorem B10858211 : Blo 2143435 10858211 := bstep (se 1 (by rfl) ⟨8143658, by rfl⟩ : syracuseStep 10858211 = 16287317) B16287317
theorem B7238807 : Blo 2143435 7238807 := bstep (se 1 (by rfl) ⟨5429105, by rfl⟩ : syracuseStep 7238807 = 10858211) B10858211
theorem B4825871 : Blo 2143435 4825871 := bstep (se 1 (by rfl) ⟨3619403, by rfl⟩ : syracuseStep 4825871 = 7238807) B7238807
theorem B3217247 : Blo 2143435 3217247 := bstep (se 1 (by rfl) ⟨2412935, by rfl⟩ : syracuseStep 3217247 = 4825871) B4825871
theorem B2144831 : Blo 2143435 2144831 := bstep (se 1 (by rfl) ⟨1608623, by rfl⟩ : syracuseStep 2144831 = 3217247) B3217247
theorem B3217253 : Blo 2143435 3217253 := bbase (se 4 (by rfl) ⟨301617, by rfl⟩ : syracuseStep 3217253 = 603235) (by norm_num)
theorem B2144835 : Blo 2143435 2144835 := bstep (se 1 (by rfl) ⟨1608626, by rfl⟩ : syracuseStep 2144835 = 3217253) B3217253
theorem B4071845 : Blo 2143435 4071845 := bbase (se 4 (by rfl) ⟨381735, by rfl⟩ : syracuseStep 4071845 = 763471) (by norm_num)
theorem B2714563 : Blo 2143435 2714563 := bstep (se 1 (by rfl) ⟨2035922, by rfl⟩ : syracuseStep 2714563 = 4071845) B4071845
theorem B3619417 : Blo 2143435 3619417 := bstep (se 2 (by rfl) ⟨1357281, by rfl⟩ : syracuseStep 3619417 = 2714563) B2714563
theorem B4825889 : Blo 2143435 4825889 := bstep (se 2 (by rfl) ⟨1809708, by rfl⟩ : syracuseStep 4825889 = 3619417) B3619417
theorem B3217259 : Blo 2143435 3217259 := bstep (se 1 (by rfl) ⟨2412944, by rfl⟩ : syracuseStep 3217259 = 4825889) B4825889
theorem B2144839 : Blo 2143435 2144839 := bstep (se 1 (by rfl) ⟨1608629, by rfl⟩ : syracuseStep 2144839 = 3217259) B3217259
theorem B2412949 : Blo 2143435 2412949 := bbase (se 6 (by rfl) ⟨56553, by rfl⟩ : syracuseStep 2412949 = 113107) (by norm_num)
theorem B3217265 : Blo 2143435 3217265 := bstep (se 2 (by rfl) ⟨1206474, by rfl⟩ : syracuseStep 3217265 = 2412949) B2412949
theorem B2144843 : Blo 2143435 2144843 := bstep (se 1 (by rfl) ⟨1608632, by rfl⟩ : syracuseStep 2144843 = 3217265) B3217265
theorem B2714573 : Blo 2143435 2714573 := bbase (se 3 (by rfl) ⟨508982, by rfl⟩ : syracuseStep 2714573 = 1017965) (by norm_num)
theorem B7238861 : Blo 2143435 7238861 := bstep (se 3 (by rfl) ⟨1357286, by rfl⟩ : syracuseStep 7238861 = 2714573) B2714573
theorem B4825907 : Blo 2143435 4825907 := bstep (se 1 (by rfl) ⟨3619430, by rfl⟩ : syracuseStep 4825907 = 7238861) B7238861
theorem B3217271 : Blo 2143435 3217271 := bstep (se 1 (by rfl) ⟨2412953, by rfl⟩ : syracuseStep 3217271 = 4825907) B4825907
theorem B2144847 : Blo 2143435 2144847 := bstep (se 1 (by rfl) ⟨1608635, by rfl⟩ : syracuseStep 2144847 = 3217271) B3217271
theorem B3217277 : Blo 2143435 3217277 := bbase (se 3 (by rfl) ⟨603239, by rfl⟩ : syracuseStep 3217277 = 1206479) (by norm_num)
theorem B2144851 : Blo 2143435 2144851 := bstep (se 1 (by rfl) ⟨1608638, by rfl⟩ : syracuseStep 2144851 = 3217277) B3217277
theorem B4825925 : Blo 2143435 4825925 := bbase (se 4 (by rfl) ⟨452430, by rfl⟩ : syracuseStep 4825925 = 904861) (by norm_num)
theorem B3217283 : Blo 2143435 3217283 := bstep (se 1 (by rfl) ⟨2412962, by rfl⟩ : syracuseStep 3217283 = 4825925) B4825925
theorem B2144855 : Blo 2143435 2144855 := bstep (se 1 (by rfl) ⟨1608641, by rfl⟩ : syracuseStep 2144855 = 3217283) B3217283
theorem B4580869 : Blo 2143435 4580869 := bbase (se 4 (by rfl) ⟨429456, by rfl⟩ : syracuseStep 4580869 = 858913) (by norm_num)
theorem B6107825 : Blo 2143435 6107825 := bstep (se 2 (by rfl) ⟨2290434, by rfl⟩ : syracuseStep 6107825 = 4580869) B4580869
theorem B4071883 : Blo 2143435 4071883 := bstep (se 1 (by rfl) ⟨3053912, by rfl⟩ : syracuseStep 4071883 = 6107825) B6107825
theorem B5429177 : Blo 2143435 5429177 := bstep (se 2 (by rfl) ⟨2035941, by rfl⟩ : syracuseStep 5429177 = 4071883) B4071883
theorem B3619451 : Blo 2143435 3619451 := bstep (se 1 (by rfl) ⟨2714588, by rfl⟩ : syracuseStep 3619451 = 5429177) B5429177
theorem B2412967 : Blo 2143435 2412967 := bstep (se 1 (by rfl) ⟨1809725, by rfl⟩ : syracuseStep 2412967 = 3619451) B3619451
theorem B3217289 : Blo 2143435 3217289 := bstep (se 2 (by rfl) ⟨1206483, by rfl⟩ : syracuseStep 3217289 = 2412967) B2412967
theorem B2144859 : Blo 2143435 2144859 := bstep (se 1 (by rfl) ⟨1608644, by rfl⟩ : syracuseStep 2144859 = 3217289) B3217289
theorem B10858373 : Blo 2143435 10858373 := bbase (se 4 (by rfl) ⟨1017972, by rfl⟩ : syracuseStep 10858373 = 2035945) (by norm_num)
theorem B7238915 : Blo 2143435 7238915 := bstep (se 1 (by rfl) ⟨5429186, by rfl⟩ : syracuseStep 7238915 = 10858373) B10858373
theorem B4825943 : Blo 2143435 4825943 := bstep (se 1 (by rfl) ⟨3619457, by rfl⟩ : syracuseStep 4825943 = 7238915) B7238915
theorem B3217295 : Blo 2143435 3217295 := bstep (se 1 (by rfl) ⟨2412971, by rfl⟩ : syracuseStep 3217295 = 4825943) B4825943
theorem B2144863 : Blo 2143435 2144863 := bstep (se 1 (by rfl) ⟨1608647, by rfl⟩ : syracuseStep 2144863 = 3217295) B3217295
theorem B3217301 : Blo 2143435 3217301 := bbase (se 6 (by rfl) ⟨75405, by rfl⟩ : syracuseStep 3217301 = 150811) (by norm_num)
theorem B2144867 : Blo 2143435 2144867 := bstep (se 1 (by rfl) ⟨1608650, by rfl⟩ : syracuseStep 2144867 = 3217301) B3217301
theorem B7730261 : Blo 2143435 7730261 := bbase (se 8 (by rfl) ⟨45294, by rfl⟩ : syracuseStep 7730261 = 90589) (by norm_num)
theorem B5153507 : Blo 2143435 5153507 := bstep (se 1 (by rfl) ⟨3865130, by rfl⟩ : syracuseStep 5153507 = 7730261) B7730261
theorem B3435671 : Blo 2143435 3435671 := bstep (se 1 (by rfl) ⟨2576753, by rfl⟩ : syracuseStep 3435671 = 5153507) B5153507
theorem B2290447 : Blo 2143435 2290447 := bstep (se 1 (by rfl) ⟨1717835, by rfl⟩ : syracuseStep 2290447 = 3435671) B3435671
theorem B12215717 : Blo 2143435 12215717 := bstep (se 4 (by rfl) ⟨1145223, by rfl⟩ : syracuseStep 12215717 = 2290447) B2290447
theorem B8143811 : Blo 2143435 8143811 := bstep (se 1 (by rfl) ⟨6107858, by rfl⟩ : syracuseStep 8143811 = 12215717) B12215717
theorem B5429207 : Blo 2143435 5429207 := bstep (se 1 (by rfl) ⟨4071905, by rfl⟩ : syracuseStep 5429207 = 8143811) B8143811
theorem B3619471 : Blo 2143435 3619471 := bstep (se 1 (by rfl) ⟨2714603, by rfl⟩ : syracuseStep 3619471 = 5429207) B5429207
theorem B4825961 : Blo 2143435 4825961 := bstep (se 2 (by rfl) ⟨1809735, by rfl⟩ : syracuseStep 4825961 = 3619471) B3619471
theorem B3217307 : Blo 2143435 3217307 := bstep (se 1 (by rfl) ⟨2412980, by rfl⟩ : syracuseStep 3217307 = 4825961) B4825961
theorem B2144871 : Blo 2143435 2144871 := bstep (se 1 (by rfl) ⟨1608653, by rfl⟩ : syracuseStep 2144871 = 3217307) B3217307
theorem B2412985 : Blo 2143435 2412985 := bbase (se 2 (by rfl) ⟨904869, by rfl⟩ : syracuseStep 2412985 = 1809739) (by norm_num)
theorem B3217313 : Blo 2143435 3217313 := bstep (se 2 (by rfl) ⟨1206492, by rfl⟩ : syracuseStep 3217313 = 2412985) B2412985
theorem B2144875 : Blo 2143435 2144875 := bstep (se 1 (by rfl) ⟨1608656, by rfl⟩ : syracuseStep 2144875 = 3217313) B3217313
theorem B2617381 : Blo 2143435 2617381 := bbase (se 4 (by rfl) ⟨245379, by rfl⟩ : syracuseStep 2617381 = 490759) (by norm_num)
theorem B3489841 : Blo 2143435 3489841 := bstep (se 2 (by rfl) ⟨1308690, by rfl⟩ : syracuseStep 3489841 = 2617381) B2617381
theorem B4653121 : Blo 2143435 4653121 := bstep (se 2 (by rfl) ⟨1744920, by rfl⟩ : syracuseStep 4653121 = 3489841) B3489841
theorem B6204161 : Blo 2143435 6204161 := bstep (se 2 (by rfl) ⟨2326560, by rfl⟩ : syracuseStep 6204161 = 4653121) B4653121
theorem B4136107 : Blo 2143435 4136107 := bstep (se 1 (by rfl) ⟨3102080, by rfl⟩ : syracuseStep 4136107 = 6204161) B6204161
theorem B5514809 : Blo 2143435 5514809 := bstep (se 2 (by rfl) ⟨2068053, by rfl⟩ : syracuseStep 5514809 = 4136107) B4136107
theorem B58824629 : Blo 2143435 58824629 := bstep (se 5 (by rfl) ⟨2757404, by rfl⟩ : syracuseStep 58824629 = 5514809) B5514809
theorem B39216419 : Blo 2143435 39216419 := bstep (se 1 (by rfl) ⟨29412314, by rfl⟩ : syracuseStep 39216419 = 58824629) B58824629
theorem B26144279 : Blo 2143435 26144279 := bstep (se 1 (by rfl) ⟨19608209, by rfl⟩ : syracuseStep 26144279 = 39216419) B39216419
theorem B17429519 : Blo 2143435 17429519 := bstep (se 1 (by rfl) ⟨13072139, by rfl⟩ : syracuseStep 17429519 = 26144279) B26144279
theorem B46478717 : Blo 2143435 46478717 := bstep (se 3 (by rfl) ⟨8714759, by rfl⟩ : syracuseStep 46478717 = 17429519) B17429519
theorem B30985811 : Blo 2143435 30985811 := bstep (se 1 (by rfl) ⟨23239358, by rfl⟩ : syracuseStep 30985811 = 46478717) B46478717
theorem B20657207 : Blo 2143435 20657207 := bstep (se 1 (by rfl) ⟨15492905, by rfl⟩ : syracuseStep 20657207 = 30985811) B30985811
theorem B13771471 : Blo 2143435 13771471 := bstep (se 1 (by rfl) ⟨10328603, by rfl⟩ : syracuseStep 13771471 = 20657207) B20657207
theorem B18361961 : Blo 2143435 18361961 := bstep (se 2 (by rfl) ⟨6885735, by rfl⟩ : syracuseStep 18361961 = 13771471) B13771471
theorem B12241307 : Blo 2143435 12241307 := bstep (se 1 (by rfl) ⟨9180980, by rfl⟩ : syracuseStep 12241307 = 18361961) B18361961
theorem B8160871 : Blo 2143435 8160871 := bstep (se 1 (by rfl) ⟨6120653, by rfl⟩ : syracuseStep 8160871 = 12241307) B12241307
theorem B10881161 : Blo 2143435 10881161 := bstep (se 2 (by rfl) ⟨4080435, by rfl⟩ : syracuseStep 10881161 = 8160871) B8160871
theorem B7254107 : Blo 2143435 7254107 := bstep (se 1 (by rfl) ⟨5440580, by rfl⟩ : syracuseStep 7254107 = 10881161) B10881161
theorem B4836071 : Blo 2143435 4836071 := bstep (se 1 (by rfl) ⟨3627053, by rfl⟩ : syracuseStep 4836071 = 7254107) B7254107
theorem B12896189 : Blo 2143435 12896189 := bstep (se 3 (by rfl) ⟨2418035, by rfl⟩ : syracuseStep 12896189 = 4836071) B4836071
theorem B8597459 : Blo 2143435 8597459 := bstep (se 1 (by rfl) ⟨6448094, by rfl⟩ : syracuseStep 8597459 = 12896189) B12896189
theorem B22926557 : Blo 2143435 22926557 := bstep (se 3 (by rfl) ⟨4298729, by rfl⟩ : syracuseStep 22926557 = 8597459) B8597459
theorem B15284371 : Blo 2143435 15284371 := bstep (se 1 (by rfl) ⟨11463278, by rfl⟩ : syracuseStep 15284371 = 22926557) B22926557
theorem B20379161 : Blo 2143435 20379161 := bstep (se 2 (by rfl) ⟨7642185, by rfl⟩ : syracuseStep 20379161 = 15284371) B15284371
theorem B54344429 : Blo 2143435 54344429 := bstep (se 3 (by rfl) ⟨10189580, by rfl⟩ : syracuseStep 54344429 = 20379161) B20379161
theorem B36229619 : Blo 2143435 36229619 := bstep (se 1 (by rfl) ⟨27172214, by rfl⟩ : syracuseStep 36229619 = 54344429) B54344429
theorem B24153079 : Blo 2143435 24153079 := bstep (se 1 (by rfl) ⟨18114809, by rfl⟩ : syracuseStep 24153079 = 36229619) B36229619
theorem B32204105 : Blo 2143435 32204105 := bstep (se 2 (by rfl) ⟨12076539, by rfl⟩ : syracuseStep 32204105 = 24153079) B24153079
theorem B21469403 : Blo 2143435 21469403 := bstep (se 1 (by rfl) ⟨16102052, by rfl⟩ : syracuseStep 21469403 = 32204105) B32204105
theorem B14312935 : Blo 2143435 14312935 := bstep (se 1 (by rfl) ⟨10734701, by rfl⟩ : syracuseStep 14312935 = 21469403) B21469403
theorem B76335653 : Blo 2143435 76335653 := bstep (se 4 (by rfl) ⟨7156467, by rfl⟩ : syracuseStep 76335653 = 14312935) B14312935
theorem B203561741 : Blo 2143435 203561741 := bstep (se 3 (by rfl) ⟨38167826, by rfl⟩ : syracuseStep 203561741 = 76335653) B76335653
theorem B135707827 : Blo 2143435 135707827 := bstep (se 1 (by rfl) ⟨101780870, by rfl⟩ : syracuseStep 135707827 = 203561741) B203561741
theorem B180943769 : Blo 2143435 180943769 := bstep (se 2 (by rfl) ⟨67853913, by rfl⟩ : syracuseStep 180943769 = 135707827) B135707827
theorem B120629179 : Blo 2143435 120629179 := bstep (se 1 (by rfl) ⟨90471884, by rfl⟩ : syracuseStep 120629179 = 180943769) B180943769
theorem B643355621 : Blo 2143435 643355621 := bstep (se 4 (by rfl) ⟨60314589, by rfl⟩ : syracuseStep 643355621 = 120629179) B120629179
theorem B428903747 : Blo 2143435 428903747 := bstep (se 1 (by rfl) ⟨321677810, by rfl⟩ : syracuseStep 428903747 = 643355621) B643355621
theorem B285935831 : Blo 2143435 285935831 := bstep (se 1 (by rfl) ⟨214451873, by rfl⟩ : syracuseStep 285935831 = 428903747) B428903747
theorem B190623887 : Blo 2143435 190623887 := bstep (se 1 (by rfl) ⟨142967915, by rfl⟩ : syracuseStep 190623887 = 285935831) B285935831
theorem B127082591 : Blo 2143435 127082591 := bstep (se 1 (by rfl) ⟨95311943, by rfl⟩ : syracuseStep 127082591 = 190623887) B190623887
theorem B84721727 : Blo 2143435 84721727 := bstep (se 1 (by rfl) ⟨63541295, by rfl⟩ : syracuseStep 84721727 = 127082591) B127082591
theorem B56481151 : Blo 2143435 56481151 := bstep (se 1 (by rfl) ⟨42360863, by rfl⟩ : syracuseStep 56481151 = 84721727) B84721727
theorem B75308201 : Blo 2143435 75308201 := bstep (se 2 (by rfl) ⟨28240575, by rfl⟩ : syracuseStep 75308201 = 56481151) B56481151
theorem B50205467 : Blo 2143435 50205467 := bstep (se 1 (by rfl) ⟨37654100, by rfl⟩ : syracuseStep 50205467 = 75308201) B75308201
theorem B133881245 : Blo 2143435 133881245 := bstep (se 3 (by rfl) ⟨25102733, by rfl⟩ : syracuseStep 133881245 = 50205467) B50205467
theorem B89254163 : Blo 2143435 89254163 := bstep (se 1 (by rfl) ⟨66940622, by rfl⟩ : syracuseStep 89254163 = 133881245) B133881245
theorem B59502775 : Blo 2143435 59502775 := bstep (se 1 (by rfl) ⟨44627081, by rfl⟩ : syracuseStep 59502775 = 89254163) B89254163
theorem B79337033 : Blo 2143435 79337033 := bstep (se 2 (by rfl) ⟨29751387, by rfl⟩ : syracuseStep 79337033 = 59502775) B59502775
theorem B52891355 : Blo 2143435 52891355 := bstep (se 1 (by rfl) ⟨39668516, by rfl⟩ : syracuseStep 52891355 = 79337033) B79337033
theorem B35260903 : Blo 2143435 35260903 := bstep (se 1 (by rfl) ⟨26445677, by rfl⟩ : syracuseStep 35260903 = 52891355) B52891355
theorem B188058149 : Blo 2143435 188058149 := bstep (se 4 (by rfl) ⟨17630451, by rfl⟩ : syracuseStep 188058149 = 35260903) B35260903
theorem B125372099 : Blo 2143435 125372099 := bstep (se 1 (by rfl) ⟨94029074, by rfl⟩ : syracuseStep 125372099 = 188058149) B188058149
theorem B83581399 : Blo 2143435 83581399 := bstep (se 1 (by rfl) ⟨62686049, by rfl⟩ : syracuseStep 83581399 = 125372099) B125372099
theorem B111441865 : Blo 2143435 111441865 := bstep (se 2 (by rfl) ⟨41790699, by rfl⟩ : syracuseStep 111441865 = 83581399) B83581399
theorem B148589153 : Blo 2143435 148589153 := bstep (se 2 (by rfl) ⟨55720932, by rfl⟩ : syracuseStep 148589153 = 111441865) B111441865
theorem B99059435 : Blo 2143435 99059435 := bstep (se 1 (by rfl) ⟨74294576, by rfl⟩ : syracuseStep 99059435 = 148589153) B148589153
theorem B66039623 : Blo 2143435 66039623 := bstep (se 1 (by rfl) ⟨49529717, by rfl⟩ : syracuseStep 66039623 = 99059435) B99059435
theorem B44026415 : Blo 2143435 44026415 := bstep (se 1 (by rfl) ⟨33019811, by rfl⟩ : syracuseStep 44026415 = 66039623) B66039623
theorem B29350943 : Blo 2143435 29350943 := bstep (se 1 (by rfl) ⟨22013207, by rfl⟩ : syracuseStep 29350943 = 44026415) B44026415
theorem B19567295 : Blo 2143435 19567295 := bstep (se 1 (by rfl) ⟨14675471, by rfl⟩ : syracuseStep 19567295 = 29350943) B29350943
theorem B13044863 : Blo 2143435 13044863 := bstep (se 1 (by rfl) ⟨9783647, by rfl⟩ : syracuseStep 13044863 = 19567295) B19567295
theorem B8696575 : Blo 2143435 8696575 := bstep (se 1 (by rfl) ⟨6522431, by rfl⟩ : syracuseStep 8696575 = 13044863) B13044863
theorem B11595433 : Blo 2143435 11595433 := bstep (se 2 (by rfl) ⟨4348287, by rfl⟩ : syracuseStep 11595433 = 8696575) B8696575
theorem B15460577 : Blo 2143435 15460577 := bstep (se 2 (by rfl) ⟨5797716, by rfl⟩ : syracuseStep 15460577 = 11595433) B11595433
theorem B10307051 : Blo 2143435 10307051 := bstep (se 1 (by rfl) ⟨7730288, by rfl⟩ : syracuseStep 10307051 = 15460577) B15460577
theorem B6871367 : Blo 2143435 6871367 := bstep (se 1 (by rfl) ⟨5153525, by rfl⟩ : syracuseStep 6871367 = 10307051) B10307051
theorem B4580911 : Blo 2143435 4580911 := bstep (se 1 (by rfl) ⟨3435683, by rfl⟩ : syracuseStep 4580911 = 6871367) B6871367
theorem B6107881 : Blo 2143435 6107881 := bstep (se 2 (by rfl) ⟨2290455, by rfl⟩ : syracuseStep 6107881 = 4580911) B4580911
theorem B8143841 : Blo 2143435 8143841 := bstep (se 2 (by rfl) ⟨3053940, by rfl⟩ : syracuseStep 8143841 = 6107881) B6107881
theorem B5429227 : Blo 2143435 5429227 := bstep (se 1 (by rfl) ⟨4071920, by rfl⟩ : syracuseStep 5429227 = 8143841) B8143841
theorem B7238969 : Blo 2143435 7238969 := bstep (se 2 (by rfl) ⟨2714613, by rfl⟩ : syracuseStep 7238969 = 5429227) B5429227
theorem B4825979 : Blo 2143435 4825979 := bstep (se 1 (by rfl) ⟨3619484, by rfl⟩ : syracuseStep 4825979 = 7238969) B7238969
theorem B3217319 : Blo 2143435 3217319 := bstep (se 1 (by rfl) ⟨2412989, by rfl⟩ : syracuseStep 3217319 = 4825979) B4825979
theorem B2144879 : Blo 2143435 2144879 := bstep (se 1 (by rfl) ⟨1608659, by rfl⟩ : syracuseStep 2144879 = 3217319) B3217319
theorem B3217325 : Blo 2143435 3217325 := bbase (se 3 (by rfl) ⟨603248, by rfl⟩ : syracuseStep 3217325 = 1206497) (by norm_num)
theorem B2144883 : Blo 2143435 2144883 := bstep (se 1 (by rfl) ⟨1608662, by rfl⟩ : syracuseStep 2144883 = 3217325) B3217325
theorem B4825997 : Blo 2143435 4825997 := bbase (se 3 (by rfl) ⟨904874, by rfl⟩ : syracuseStep 4825997 = 1809749) (by norm_num)
theorem B3217331 : Blo 2143435 3217331 := bstep (se 1 (by rfl) ⟨2412998, by rfl⟩ : syracuseStep 3217331 = 4825997) B4825997
theorem B2144887 : Blo 2143435 2144887 := bstep (se 1 (by rfl) ⟨1608665, by rfl⟩ : syracuseStep 2144887 = 3217331) B3217331
theorem B2714629 : Blo 2143435 2714629 := bbase (se 4 (by rfl) ⟨254496, by rfl⟩ : syracuseStep 2714629 = 508993) (by norm_num)
theorem B3619505 : Blo 2143435 3619505 := bstep (se 2 (by rfl) ⟨1357314, by rfl⟩ : syracuseStep 3619505 = 2714629) B2714629
theorem B2413003 : Blo 2143435 2413003 := bstep (se 1 (by rfl) ⟨1809752, by rfl⟩ : syracuseStep 2413003 = 3619505) B3619505
theorem B3217337 : Blo 2143435 3217337 := bstep (se 2 (by rfl) ⟨1206501, by rfl⟩ : syracuseStep 3217337 = 2413003) B2413003
theorem B2144891 : Blo 2143435 2144891 := bstep (se 1 (by rfl) ⟨1608668, by rfl⟩ : syracuseStep 2144891 = 3217337) B3217337
theorem B18573781 : Blo 2143435 18573781 := bbase (se 7 (by rfl) ⟨217661, by rfl⟩ : syracuseStep 18573781 = 435323) (by norm_num)
theorem B24765041 : Blo 2143435 24765041 := bstep (se 2 (by rfl) ⟨9286890, by rfl⟩ : syracuseStep 24765041 = 18573781) B18573781
theorem B66040109 : Blo 2143435 66040109 := bstep (se 3 (by rfl) ⟨12382520, by rfl⟩ : syracuseStep 66040109 = 24765041) B24765041
theorem B44026739 : Blo 2143435 44026739 := bstep (se 1 (by rfl) ⟨33020054, by rfl⟩ : syracuseStep 44026739 = 66040109) B66040109
theorem B29351159 : Blo 2143435 29351159 := bstep (se 1 (by rfl) ⟨22013369, by rfl⟩ : syracuseStep 29351159 = 44026739) B44026739
theorem B19567439 : Blo 2143435 19567439 := bstep (se 1 (by rfl) ⟨14675579, by rfl⟩ : syracuseStep 19567439 = 29351159) B29351159
theorem B13044959 : Blo 2143435 13044959 := bstep (se 1 (by rfl) ⟨9783719, by rfl⟩ : syracuseStep 13044959 = 19567439) B19567439
theorem B8696639 : Blo 2143435 8696639 := bstep (se 1 (by rfl) ⟨6522479, by rfl⟩ : syracuseStep 8696639 = 13044959) B13044959
theorem B5797759 : Blo 2143435 5797759 := bstep (se 1 (by rfl) ⟨4348319, by rfl⟩ : syracuseStep 5797759 = 8696639) B8696639
theorem B7730345 : Blo 2143435 7730345 := bstep (se 2 (by rfl) ⟨2898879, by rfl⟩ : syracuseStep 7730345 = 5797759) B5797759
theorem B5153563 : Blo 2143435 5153563 := bstep (se 1 (by rfl) ⟨3865172, by rfl⟩ : syracuseStep 5153563 = 7730345) B7730345
theorem B27485669 : Blo 2143435 27485669 := bstep (se 4 (by rfl) ⟨2576781, by rfl⟩ : syracuseStep 27485669 = 5153563) B5153563
theorem B18323779 : Blo 2143435 18323779 := bstep (se 1 (by rfl) ⟨13742834, by rfl⟩ : syracuseStep 18323779 = 27485669) B27485669
theorem B24431705 : Blo 2143435 24431705 := bstep (se 2 (by rfl) ⟨9161889, by rfl⟩ : syracuseStep 24431705 = 18323779) B18323779
theorem B16287803 : Blo 2143435 16287803 := bstep (se 1 (by rfl) ⟨12215852, by rfl⟩ : syracuseStep 16287803 = 24431705) B24431705
theorem B10858535 : Blo 2143435 10858535 := bstep (se 1 (by rfl) ⟨8143901, by rfl⟩ : syracuseStep 10858535 = 16287803) B16287803
theorem B7239023 : Blo 2143435 7239023 := bstep (se 1 (by rfl) ⟨5429267, by rfl⟩ : syracuseStep 7239023 = 10858535) B10858535
theorem B4826015 : Blo 2143435 4826015 := bstep (se 1 (by rfl) ⟨3619511, by rfl⟩ : syracuseStep 4826015 = 7239023) B7239023
theorem B3217343 : Blo 2143435 3217343 := bstep (se 1 (by rfl) ⟨2413007, by rfl⟩ : syracuseStep 3217343 = 4826015) B4826015
theorem B2144895 : Blo 2143435 2144895 := bstep (se 1 (by rfl) ⟨1608671, by rfl⟩ : syracuseStep 2144895 = 3217343) B3217343
theorem B3217349 : Blo 2143435 3217349 := bbase (se 4 (by rfl) ⟨301626, by rfl⟩ : syracuseStep 3217349 = 603253) (by norm_num)
theorem B2144899 : Blo 2143435 2144899 := bstep (se 1 (by rfl) ⟨1608674, by rfl⟩ : syracuseStep 2144899 = 3217349) B3217349
theorem B3619525 : Blo 2143435 3619525 := bbase (se 4 (by rfl) ⟨339330, by rfl⟩ : syracuseStep 3619525 = 678661) (by norm_num)
theorem B4826033 : Blo 2143435 4826033 := bstep (se 2 (by rfl) ⟨1809762, by rfl⟩ : syracuseStep 4826033 = 3619525) B3619525
theorem B3217355 : Blo 2143435 3217355 := bstep (se 1 (by rfl) ⟨2413016, by rfl⟩ : syracuseStep 3217355 = 4826033) B4826033
theorem B2144903 : Blo 2143435 2144903 := bstep (se 1 (by rfl) ⟨1608677, by rfl⟩ : syracuseStep 2144903 = 3217355) B3217355
theorem B2413021 : Blo 2143435 2413021 := bbase (se 3 (by rfl) ⟨452441, by rfl⟩ : syracuseStep 2413021 = 904883) (by norm_num)
theorem B3217361 : Blo 2143435 3217361 := bstep (se 2 (by rfl) ⟨1206510, by rfl⟩ : syracuseStep 3217361 = 2413021) B2413021
theorem B2144907 : Blo 2143435 2144907 := bstep (se 1 (by rfl) ⟨1608680, by rfl⟩ : syracuseStep 2144907 = 3217361) B3217361
theorem B7239077 : Blo 2143435 7239077 := bbase (se 4 (by rfl) ⟨678663, by rfl⟩ : syracuseStep 7239077 = 1357327) (by norm_num)
theorem B4826051 : Blo 2143435 4826051 := bstep (se 1 (by rfl) ⟨3619538, by rfl⟩ : syracuseStep 4826051 = 7239077) B7239077
theorem B3217367 : Blo 2143435 3217367 := bstep (se 1 (by rfl) ⟨2413025, by rfl⟩ : syracuseStep 3217367 = 4826051) B4826051
theorem B2144911 : Blo 2143435 2144911 := bstep (se 1 (by rfl) ⟨1608683, by rfl⟩ : syracuseStep 2144911 = 3217367) B3217367
theorem B3217373 : Blo 2143435 3217373 := bbase (se 3 (by rfl) ⟨603257, by rfl⟩ : syracuseStep 3217373 = 1206515) (by norm_num)
theorem B2144915 : Blo 2143435 2144915 := bstep (se 1 (by rfl) ⟨1608686, by rfl⟩ : syracuseStep 2144915 = 3217373) B3217373
theorem B4826069 : Blo 2143435 4826069 := bbase (se 7 (by rfl) ⟨56555, by rfl⟩ : syracuseStep 4826069 = 113111) (by norm_num)
theorem B3217379 : Blo 2143435 3217379 := bstep (se 1 (by rfl) ⟨2413034, by rfl⟩ : syracuseStep 3217379 = 4826069) B4826069
theorem B2144919 : Blo 2143435 2144919 := bstep (se 1 (by rfl) ⟨1608689, by rfl⟩ : syracuseStep 2144919 = 3217379) B3217379
theorem B2611973 : Blo 2143435 2611973 := bbase (se 4 (by rfl) ⟨244872, by rfl⟩ : syracuseStep 2611973 = 489745) (by norm_num)
theorem B6965261 : Blo 2143435 6965261 := bstep (se 3 (by rfl) ⟨1305986, by rfl⟩ : syracuseStep 6965261 = 2611973) B2611973
theorem B4643507 : Blo 2143435 4643507 := bstep (se 1 (by rfl) ⟨3482630, by rfl⟩ : syracuseStep 4643507 = 6965261) B6965261
theorem B3095671 : Blo 2143435 3095671 := bstep (se 1 (by rfl) ⟨2321753, by rfl⟩ : syracuseStep 3095671 = 4643507) B4643507
theorem B4127561 : Blo 2143435 4127561 := bstep (se 2 (by rfl) ⟨1547835, by rfl⟩ : syracuseStep 4127561 = 3095671) B3095671
theorem B44027317 : Blo 2143435 44027317 := bstep (se 5 (by rfl) ⟨2063780, by rfl⟩ : syracuseStep 44027317 = 4127561) B4127561
theorem B58703089 : Blo 2143435 58703089 := bstep (se 2 (by rfl) ⟨22013658, by rfl⟩ : syracuseStep 58703089 = 44027317) B44027317
theorem B78270785 : Blo 2143435 78270785 := bstep (se 2 (by rfl) ⟨29351544, by rfl⟩ : syracuseStep 78270785 = 58703089) B58703089
theorem B52180523 : Blo 2143435 52180523 := bstep (se 1 (by rfl) ⟨39135392, by rfl⟩ : syracuseStep 52180523 = 78270785) B78270785
theorem B34787015 : Blo 2143435 34787015 := bstep (se 1 (by rfl) ⟨26090261, by rfl⟩ : syracuseStep 34787015 = 52180523) B52180523
theorem B23191343 : Blo 2143435 23191343 := bstep (se 1 (by rfl) ⟨17393507, by rfl⟩ : syracuseStep 23191343 = 34787015) B34787015
theorem B15460895 : Blo 2143435 15460895 := bstep (se 1 (by rfl) ⟨11595671, by rfl⟩ : syracuseStep 15460895 = 23191343) B23191343
theorem B10307263 : Blo 2143435 10307263 := bstep (se 1 (by rfl) ⟨7730447, by rfl⟩ : syracuseStep 10307263 = 15460895) B15460895
theorem B13743017 : Blo 2143435 13743017 := bstep (se 2 (by rfl) ⟨5153631, by rfl⟩ : syracuseStep 13743017 = 10307263) B10307263
theorem B9162011 : Blo 2143435 9162011 := bstep (se 1 (by rfl) ⟨6871508, by rfl⟩ : syracuseStep 9162011 = 13743017) B13743017
theorem B6108007 : Blo 2143435 6108007 := bstep (se 1 (by rfl) ⟨4581005, by rfl⟩ : syracuseStep 6108007 = 9162011) B9162011
theorem B8144009 : Blo 2143435 8144009 := bstep (se 2 (by rfl) ⟨3054003, by rfl⟩ : syracuseStep 8144009 = 6108007) B6108007
theorem B5429339 : Blo 2143435 5429339 := bstep (se 1 (by rfl) ⟨4072004, by rfl⟩ : syracuseStep 5429339 = 8144009) B8144009
theorem B3619559 : Blo 2143435 3619559 := bstep (se 1 (by rfl) ⟨2714669, by rfl⟩ : syracuseStep 3619559 = 5429339) B5429339
theorem B2413039 : Blo 2143435 2413039 := bstep (se 1 (by rfl) ⟨1809779, by rfl⟩ : syracuseStep 2413039 = 3619559) B3619559
theorem B3217385 : Blo 2143435 3217385 := bstep (se 2 (by rfl) ⟨1206519, by rfl⟩ : syracuseStep 3217385 = 2413039) B2413039
theorem B2144923 : Blo 2143435 2144923 := bstep (se 1 (by rfl) ⟨1608692, by rfl⟩ : syracuseStep 2144923 = 3217385) B3217385
theorem B18324053 : Blo 2143435 18324053 := bbase (se 8 (by rfl) ⟨107367, by rfl⟩ : syracuseStep 18324053 = 214735) (by norm_num)
theorem B12216035 : Blo 2143435 12216035 := bstep (se 1 (by rfl) ⟨9162026, by rfl⟩ : syracuseStep 12216035 = 18324053) B18324053
theorem B8144023 : Blo 2143435 8144023 := bstep (se 1 (by rfl) ⟨6108017, by rfl⟩ : syracuseStep 8144023 = 12216035) B12216035
theorem B10858697 : Blo 2143435 10858697 := bstep (se 2 (by rfl) ⟨4072011, by rfl⟩ : syracuseStep 10858697 = 8144023) B8144023
theorem B7239131 : Blo 2143435 7239131 := bstep (se 1 (by rfl) ⟨5429348, by rfl⟩ : syracuseStep 7239131 = 10858697) B10858697
theorem B4826087 : Blo 2143435 4826087 := bstep (se 1 (by rfl) ⟨3619565, by rfl⟩ : syracuseStep 4826087 = 7239131) B7239131
theorem B3217391 : Blo 2143435 3217391 := bstep (se 1 (by rfl) ⟨2413043, by rfl⟩ : syracuseStep 3217391 = 4826087) B4826087
theorem B2144927 : Blo 2143435 2144927 := bstep (se 1 (by rfl) ⟨1608695, by rfl⟩ : syracuseStep 2144927 = 3217391) B3217391
theorem B3217397 : Blo 2143435 3217397 := bbase (se 5 (by rfl) ⟨150815, by rfl⟩ : syracuseStep 3217397 = 301631) (by norm_num)
theorem B2144931 : Blo 2143435 2144931 := bstep (se 1 (by rfl) ⟨1608698, by rfl⟩ : syracuseStep 2144931 = 3217397) B3217397
theorem B13045205 : Blo 2143435 13045205 := bbase (se 7 (by rfl) ⟨152873, by rfl⟩ : syracuseStep 13045205 = 305747) (by norm_num)
theorem B8696803 : Blo 2143435 8696803 := bstep (se 1 (by rfl) ⟨6522602, by rfl⟩ : syracuseStep 8696803 = 13045205) B13045205
theorem B11595737 : Blo 2143435 11595737 := bstep (se 2 (by rfl) ⟨4348401, by rfl⟩ : syracuseStep 11595737 = 8696803) B8696803
theorem B7730491 : Blo 2143435 7730491 := bstep (se 1 (by rfl) ⟨5797868, by rfl⟩ : syracuseStep 7730491 = 11595737) B11595737
theorem B10307321 : Blo 2143435 10307321 := bstep (se 2 (by rfl) ⟨3865245, by rfl⟩ : syracuseStep 10307321 = 7730491) B7730491
theorem B6871547 : Blo 2143435 6871547 := bstep (se 1 (by rfl) ⟨5153660, by rfl⟩ : syracuseStep 6871547 = 10307321) B10307321
theorem B4581031 : Blo 2143435 4581031 := bstep (se 1 (by rfl) ⟨3435773, by rfl⟩ : syracuseStep 4581031 = 6871547) B6871547
theorem B6108041 : Blo 2143435 6108041 := bstep (se 2 (by rfl) ⟨2290515, by rfl⟩ : syracuseStep 6108041 = 4581031) B4581031
theorem B4072027 : Blo 2143435 4072027 := bstep (se 1 (by rfl) ⟨3054020, by rfl⟩ : syracuseStep 4072027 = 6108041) B6108041
theorem B5429369 : Blo 2143435 5429369 := bstep (se 2 (by rfl) ⟨2036013, by rfl⟩ : syracuseStep 5429369 = 4072027) B4072027
theorem B3619579 : Blo 2143435 3619579 := bstep (se 1 (by rfl) ⟨2714684, by rfl⟩ : syracuseStep 3619579 = 5429369) B5429369
theorem B4826105 : Blo 2143435 4826105 := bstep (se 2 (by rfl) ⟨1809789, by rfl⟩ : syracuseStep 4826105 = 3619579) B3619579
theorem B3217403 : Blo 2143435 3217403 := bstep (se 1 (by rfl) ⟨2413052, by rfl⟩ : syracuseStep 3217403 = 4826105) B4826105
theorem B2144935 : Blo 2143435 2144935 := bstep (se 1 (by rfl) ⟨1608701, by rfl⟩ : syracuseStep 2144935 = 3217403) B3217403
theorem B2413057 : Blo 2143435 2413057 := bbase (se 2 (by rfl) ⟨904896, by rfl⟩ : syracuseStep 2413057 = 1809793) (by norm_num)
theorem B3217409 : Blo 2143435 3217409 := bstep (se 2 (by rfl) ⟨1206528, by rfl⟩ : syracuseStep 3217409 = 2413057) B2413057
theorem B2144939 : Blo 2143435 2144939 := bstep (se 1 (by rfl) ⟨1608704, by rfl⟩ : syracuseStep 2144939 = 3217409) B3217409
theorem B5429389 : Blo 2143435 5429389 := bbase (se 3 (by rfl) ⟨1018010, by rfl⟩ : syracuseStep 5429389 = 2036021) (by norm_num)
theorem B7239185 : Blo 2143435 7239185 := bstep (se 2 (by rfl) ⟨2714694, by rfl⟩ : syracuseStep 7239185 = 5429389) B5429389
theorem B4826123 : Blo 2143435 4826123 := bstep (se 1 (by rfl) ⟨3619592, by rfl⟩ : syracuseStep 4826123 = 7239185) B7239185
theorem B3217415 : Blo 2143435 3217415 := bstep (se 1 (by rfl) ⟨2413061, by rfl⟩ : syracuseStep 3217415 = 4826123) B4826123
theorem B2144943 : Blo 2143435 2144943 := bstep (se 1 (by rfl) ⟨1608707, by rfl⟩ : syracuseStep 2144943 = 3217415) B3217415
theorem B3217421 : Blo 2143435 3217421 := bbase (se 3 (by rfl) ⟨603266, by rfl⟩ : syracuseStep 3217421 = 1206533) (by norm_num)
theorem B2144947 : Blo 2143435 2144947 := bstep (se 1 (by rfl) ⟨1608710, by rfl⟩ : syracuseStep 2144947 = 3217421) B3217421
theorem B4826141 : Blo 2143435 4826141 := bbase (se 3 (by rfl) ⟨904901, by rfl⟩ : syracuseStep 4826141 = 1809803) (by norm_num)
theorem B3217427 : Blo 2143435 3217427 := bstep (se 1 (by rfl) ⟨2413070, by rfl⟩ : syracuseStep 3217427 = 4826141) B4826141
theorem B2144951 : Blo 2143435 2144951 := bstep (se 1 (by rfl) ⟨1608713, by rfl⟩ : syracuseStep 2144951 = 3217427) B3217427
theorem B3619613 : Blo 2143435 3619613 := bbase (se 3 (by rfl) ⟨678677, by rfl⟩ : syracuseStep 3619613 = 1357355) (by norm_num)
theorem B2413075 : Blo 2143435 2413075 := bstep (se 1 (by rfl) ⟨1809806, by rfl⟩ : syracuseStep 2413075 = 3619613) B3619613
theorem B3217433 : Blo 2143435 3217433 := bstep (se 2 (by rfl) ⟨1206537, by rfl⟩ : syracuseStep 3217433 = 2413075) B2413075
theorem B2144955 : Blo 2143435 2144955 := bstep (se 1 (by rfl) ⟨1608716, by rfl⟩ : syracuseStep 2144955 = 3217433) B3217433
theorem B5153717 : Blo 2143435 5153717 := bbase (se 5 (by rfl) ⟨241580, by rfl⟩ : syracuseStep 5153717 = 483161) (by norm_num)
theorem B13743245 : Blo 2143435 13743245 := bstep (se 3 (by rfl) ⟨2576858, by rfl⟩ : syracuseStep 13743245 = 5153717) B5153717
theorem B9162163 : Blo 2143435 9162163 := bstep (se 1 (by rfl) ⟨6871622, by rfl⟩ : syracuseStep 9162163 = 13743245) B13743245
theorem B12216217 : Blo 2143435 12216217 := bstep (se 2 (by rfl) ⟨4581081, by rfl⟩ : syracuseStep 12216217 = 9162163) B9162163
theorem B16288289 : Blo 2143435 16288289 := bstep (se 2 (by rfl) ⟨6108108, by rfl⟩ : syracuseStep 16288289 = 12216217) B12216217
theorem B10858859 : Blo 2143435 10858859 := bstep (se 1 (by rfl) ⟨8144144, by rfl⟩ : syracuseStep 10858859 = 16288289) B16288289
theorem B7239239 : Blo 2143435 7239239 := bstep (se 1 (by rfl) ⟨5429429, by rfl⟩ : syracuseStep 7239239 = 10858859) B10858859
theorem B4826159 : Blo 2143435 4826159 := bstep (se 1 (by rfl) ⟨3619619, by rfl⟩ : syracuseStep 4826159 = 7239239) B7239239
theorem B3217439 : Blo 2143435 3217439 := bstep (se 1 (by rfl) ⟨2413079, by rfl⟩ : syracuseStep 3217439 = 4826159) B4826159
theorem B2144959 : Blo 2143435 2144959 := bstep (se 1 (by rfl) ⟨1608719, by rfl⟩ : syracuseStep 2144959 = 3217439) B3217439
theorem B3217445 : Blo 2143435 3217445 := bbase (se 4 (by rfl) ⟨301635, by rfl⟩ : syracuseStep 3217445 = 603271) (by norm_num)
theorem B2144963 : Blo 2143435 2144963 := bstep (se 1 (by rfl) ⟨1608722, by rfl⟩ : syracuseStep 2144963 = 3217445) B3217445
theorem B2714725 : Blo 2143435 2714725 := bbase (se 4 (by rfl) ⟨254505, by rfl⟩ : syracuseStep 2714725 = 509011) (by norm_num)
theorem B3619633 : Blo 2143435 3619633 := bstep (se 2 (by rfl) ⟨1357362, by rfl⟩ : syracuseStep 3619633 = 2714725) B2714725
theorem B4826177 : Blo 2143435 4826177 := bstep (se 2 (by rfl) ⟨1809816, by rfl⟩ : syracuseStep 4826177 = 3619633) B3619633
theorem B3217451 : Blo 2143435 3217451 := bstep (se 1 (by rfl) ⟨2413088, by rfl⟩ : syracuseStep 3217451 = 4826177) B4826177
theorem B2144967 : Blo 2143435 2144967 := bstep (se 1 (by rfl) ⟨1608725, by rfl⟩ : syracuseStep 2144967 = 3217451) B3217451
theorem B2413093 : Blo 2143435 2413093 := bbase (se 4 (by rfl) ⟨226227, by rfl⟩ : syracuseStep 2413093 = 452455) (by norm_num)
theorem B3217457 : Blo 2143435 3217457 := bstep (se 2 (by rfl) ⟨1206546, by rfl⟩ : syracuseStep 3217457 = 2413093) B2413093
theorem B2144971 : Blo 2143435 2144971 := bstep (se 1 (by rfl) ⟨1608728, by rfl⟩ : syracuseStep 2144971 = 3217457) B3217457
theorem B8696965 : Blo 2143435 8696965 := bbase (se 4 (by rfl) ⟨815340, by rfl⟩ : syracuseStep 8696965 = 1630681) (by norm_num)
theorem B11595953 : Blo 2143435 11595953 := bstep (se 2 (by rfl) ⟨4348482, by rfl⟩ : syracuseStep 11595953 = 8696965) B8696965
theorem B7730635 : Blo 2143435 7730635 := bstep (se 1 (by rfl) ⟨5797976, by rfl⟩ : syracuseStep 7730635 = 11595953) B11595953
theorem B10307513 : Blo 2143435 10307513 := bstep (se 2 (by rfl) ⟨3865317, by rfl⟩ : syracuseStep 10307513 = 7730635) B7730635
theorem B6871675 : Blo 2143435 6871675 := bstep (se 1 (by rfl) ⟨5153756, by rfl⟩ : syracuseStep 6871675 = 10307513) B10307513
theorem B9162233 : Blo 2143435 9162233 := bstep (se 2 (by rfl) ⟨3435837, by rfl⟩ : syracuseStep 9162233 = 6871675) B6871675
theorem B6108155 : Blo 2143435 6108155 := bstep (se 1 (by rfl) ⟨4581116, by rfl⟩ : syracuseStep 6108155 = 9162233) B9162233
theorem B4072103 : Blo 2143435 4072103 := bstep (se 1 (by rfl) ⟨3054077, by rfl⟩ : syracuseStep 4072103 = 6108155) B6108155
theorem B2714735 : Blo 2143435 2714735 := bstep (se 1 (by rfl) ⟨2036051, by rfl⟩ : syracuseStep 2714735 = 4072103) B4072103
theorem B7239293 : Blo 2143435 7239293 := bstep (se 3 (by rfl) ⟨1357367, by rfl⟩ : syracuseStep 7239293 = 2714735) B2714735
theorem B4826195 : Blo 2143435 4826195 := bstep (se 1 (by rfl) ⟨3619646, by rfl⟩ : syracuseStep 4826195 = 7239293) B7239293
theorem B3217463 : Blo 2143435 3217463 := bstep (se 1 (by rfl) ⟨2413097, by rfl⟩ : syracuseStep 3217463 = 4826195) B4826195
theorem B2144975 : Blo 2143435 2144975 := bstep (se 1 (by rfl) ⟨1608731, by rfl⟩ : syracuseStep 2144975 = 3217463) B3217463
theorem B3217469 : Blo 2143435 3217469 := bbase (se 3 (by rfl) ⟨603275, by rfl⟩ : syracuseStep 3217469 = 1206551) (by norm_num)
theorem B2144979 : Blo 2143435 2144979 := bstep (se 1 (by rfl) ⟨1608734, by rfl⟩ : syracuseStep 2144979 = 3217469) B3217469
theorem B4826213 : Blo 2143435 4826213 := bbase (se 4 (by rfl) ⟨452457, by rfl⟩ : syracuseStep 4826213 = 904915) (by norm_num)
theorem B3217475 : Blo 2143435 3217475 := bstep (se 1 (by rfl) ⟨2413106, by rfl⟩ : syracuseStep 3217475 = 4826213) B4826213
theorem B2144983 : Blo 2143435 2144983 := bstep (se 1 (by rfl) ⟨1608737, by rfl⟩ : syracuseStep 2144983 = 3217475) B3217475
theorem B5429501 : Blo 2143435 5429501 := bbase (se 3 (by rfl) ⟨1018031, by rfl⟩ : syracuseStep 5429501 = 2036063) (by norm_num)
theorem B3619667 : Blo 2143435 3619667 := bstep (se 1 (by rfl) ⟨2714750, by rfl⟩ : syracuseStep 3619667 = 5429501) B5429501
theorem B2413111 : Blo 2143435 2413111 := bstep (se 1 (by rfl) ⟨1809833, by rfl⟩ : syracuseStep 2413111 = 3619667) B3619667
theorem B3217481 : Blo 2143435 3217481 := bstep (se 2 (by rfl) ⟨1206555, by rfl⟩ : syracuseStep 3217481 = 2413111) B2413111
theorem B2144987 : Blo 2143435 2144987 := bstep (se 1 (by rfl) ⟨1608740, by rfl⟩ : syracuseStep 2144987 = 3217481) B3217481
theorem B4072133 : Blo 2143435 4072133 := bbase (se 4 (by rfl) ⟨381762, by rfl⟩ : syracuseStep 4072133 = 763525) (by norm_num)
theorem B10859021 : Blo 2143435 10859021 := bstep (se 3 (by rfl) ⟨2036066, by rfl⟩ : syracuseStep 10859021 = 4072133) B4072133
theorem B7239347 : Blo 2143435 7239347 := bstep (se 1 (by rfl) ⟨5429510, by rfl⟩ : syracuseStep 7239347 = 10859021) B10859021
theorem B4826231 : Blo 2143435 4826231 := bstep (se 1 (by rfl) ⟨3619673, by rfl⟩ : syracuseStep 4826231 = 7239347) B7239347
theorem B3217487 : Blo 2143435 3217487 := bstep (se 1 (by rfl) ⟨2413115, by rfl⟩ : syracuseStep 3217487 = 4826231) B4826231
theorem B2144991 : Blo 2143435 2144991 := bstep (se 1 (by rfl) ⟨1608743, by rfl⟩ : syracuseStep 2144991 = 3217487) B3217487
theorem B3217493 : Blo 2143435 3217493 := bbase (se 8 (by rfl) ⟨18852, by rfl⟩ : syracuseStep 3217493 = 37705) (by norm_num)
theorem B2144995 : Blo 2143435 2144995 := bstep (se 1 (by rfl) ⟨1608746, by rfl⟩ : syracuseStep 2144995 = 3217493) B3217493
theorem B8697061 : Blo 2143435 8697061 := bbase (se 4 (by rfl) ⟨815349, by rfl⟩ : syracuseStep 8697061 = 1630699) (by norm_num)
theorem B46384325 : Blo 2143435 46384325 := bstep (se 4 (by rfl) ⟨4348530, by rfl⟩ : syracuseStep 46384325 = 8697061) B8697061
theorem B30922883 : Blo 2143435 30922883 := bstep (se 1 (by rfl) ⟨23192162, by rfl⟩ : syracuseStep 30922883 = 46384325) B46384325
theorem B20615255 : Blo 2143435 20615255 := bstep (se 1 (by rfl) ⟨15461441, by rfl⟩ : syracuseStep 20615255 = 30922883) B30922883
theorem B13743503 : Blo 2143435 13743503 := bstep (se 1 (by rfl) ⟨10307627, by rfl⟩ : syracuseStep 13743503 = 20615255) B20615255
theorem B9162335 : Blo 2143435 9162335 := bstep (se 1 (by rfl) ⟨6871751, by rfl⟩ : syracuseStep 9162335 = 13743503) B13743503
theorem B6108223 : Blo 2143435 6108223 := bstep (se 1 (by rfl) ⟨4581167, by rfl⟩ : syracuseStep 6108223 = 9162335) B9162335
theorem B8144297 : Blo 2143435 8144297 := bstep (se 2 (by rfl) ⟨3054111, by rfl⟩ : syracuseStep 8144297 = 6108223) B6108223
theorem B5429531 : Blo 2143435 5429531 := bstep (se 1 (by rfl) ⟨4072148, by rfl⟩ : syracuseStep 5429531 = 8144297) B8144297
theorem B3619687 : Blo 2143435 3619687 := bstep (se 1 (by rfl) ⟨2714765, by rfl⟩ : syracuseStep 3619687 = 5429531) B5429531
theorem B4826249 : Blo 2143435 4826249 := bstep (se 2 (by rfl) ⟨1809843, by rfl⟩ : syracuseStep 4826249 = 3619687) B3619687
theorem B3217499 : Blo 2143435 3217499 := bstep (se 1 (by rfl) ⟨2413124, by rfl⟩ : syracuseStep 3217499 = 4826249) B4826249
theorem B2144999 : Blo 2143435 2144999 := bstep (se 1 (by rfl) ⟨1608749, by rfl⟩ : syracuseStep 2144999 = 3217499) B3217499
theorem B2413129 : Blo 2143435 2413129 := bbase (se 2 (by rfl) ⟨904923, by rfl⟩ : syracuseStep 2413129 = 1809847) (by norm_num)
theorem B3217505 : Blo 2143435 3217505 := bstep (se 2 (by rfl) ⟨1206564, by rfl⟩ : syracuseStep 3217505 = 2413129) B2413129
theorem B2145003 : Blo 2143435 2145003 := bstep (se 1 (by rfl) ⟨1608752, by rfl⟩ : syracuseStep 2145003 = 3217505) B3217505
theorem B6522821 : Blo 2143435 6522821 := bbase (se 4 (by rfl) ⟨611514, by rfl⟩ : syracuseStep 6522821 = 1223029) (by norm_num)
theorem B4348547 : Blo 2143435 4348547 := bstep (se 1 (by rfl) ⟨3261410, by rfl⟩ : syracuseStep 4348547 = 6522821) B6522821
theorem B2899031 : Blo 2143435 2899031 := bstep (se 1 (by rfl) ⟨2174273, by rfl⟩ : syracuseStep 2899031 = 4348547) B4348547
theorem B7730749 : Blo 2143435 7730749 := bstep (se 3 (by rfl) ⟨1449515, by rfl⟩ : syracuseStep 7730749 = 2899031) B2899031
theorem B10307665 : Blo 2143435 10307665 := bstep (se 2 (by rfl) ⟨3865374, by rfl⟩ : syracuseStep 10307665 = 7730749) B7730749
theorem B13743553 : Blo 2143435 13743553 := bstep (se 2 (by rfl) ⟨5153832, by rfl⟩ : syracuseStep 13743553 = 10307665) B10307665
theorem B18324737 : Blo 2143435 18324737 := bstep (se 2 (by rfl) ⟨6871776, by rfl⟩ : syracuseStep 18324737 = 13743553) B13743553
theorem B12216491 : Blo 2143435 12216491 := bstep (se 1 (by rfl) ⟨9162368, by rfl⟩ : syracuseStep 12216491 = 18324737) B18324737
theorem B8144327 : Blo 2143435 8144327 := bstep (se 1 (by rfl) ⟨6108245, by rfl⟩ : syracuseStep 8144327 = 12216491) B12216491
theorem B5429551 : Blo 2143435 5429551 := bstep (se 1 (by rfl) ⟨4072163, by rfl⟩ : syracuseStep 5429551 = 8144327) B8144327
theorem B7239401 : Blo 2143435 7239401 := bstep (se 2 (by rfl) ⟨2714775, by rfl⟩ : syracuseStep 7239401 = 5429551) B5429551
theorem B4826267 : Blo 2143435 4826267 := bstep (se 1 (by rfl) ⟨3619700, by rfl⟩ : syracuseStep 4826267 = 7239401) B7239401
theorem B3217511 : Blo 2143435 3217511 := bstep (se 1 (by rfl) ⟨2413133, by rfl⟩ : syracuseStep 3217511 = 4826267) B4826267
theorem B2145007 : Blo 2143435 2145007 := bstep (se 1 (by rfl) ⟨1608755, by rfl⟩ : syracuseStep 2145007 = 3217511) B3217511
theorem B3217517 : Blo 2143435 3217517 := bbase (se 3 (by rfl) ⟨603284, by rfl⟩ : syracuseStep 3217517 = 1206569) (by norm_num)
theorem B2145011 : Blo 2143435 2145011 := bstep (se 1 (by rfl) ⟨1608758, by rfl⟩ : syracuseStep 2145011 = 3217517) B3217517
theorem B4826285 : Blo 2143435 4826285 := bbase (se 3 (by rfl) ⟨904928, by rfl⟩ : syracuseStep 4826285 = 1809857) (by norm_num)
theorem B3217523 : Blo 2143435 3217523 := bstep (se 1 (by rfl) ⟨2413142, by rfl⟩ : syracuseStep 3217523 = 4826285) B4826285
theorem B2145015 : Blo 2143435 2145015 := bstep (se 1 (by rfl) ⟨1608761, by rfl⟩ : syracuseStep 2145015 = 3217523) B3217523
theorem B5224181 : Blo 2143435 5224181 := bbase (se 5 (by rfl) ⟨244883, by rfl⟩ : syracuseStep 5224181 = 489767) (by norm_num)
theorem B13931149 : Blo 2143435 13931149 := bstep (se 3 (by rfl) ⟨2612090, by rfl⟩ : syracuseStep 13931149 = 5224181) B5224181
theorem B18574865 : Blo 2143435 18574865 := bstep (se 2 (by rfl) ⟨6965574, by rfl⟩ : syracuseStep 18574865 = 13931149) B13931149
theorem B12383243 : Blo 2143435 12383243 := bstep (se 1 (by rfl) ⟨9287432, by rfl⟩ : syracuseStep 12383243 = 18574865) B18574865
theorem B8255495 : Blo 2143435 8255495 := bstep (se 1 (by rfl) ⟨6191621, by rfl⟩ : syracuseStep 8255495 = 12383243) B12383243
theorem B5503663 : Blo 2143435 5503663 := bstep (se 1 (by rfl) ⟨4127747, by rfl⟩ : syracuseStep 5503663 = 8255495) B8255495
theorem B7338217 : Blo 2143435 7338217 := bstep (se 2 (by rfl) ⟨2751831, by rfl⟩ : syracuseStep 7338217 = 5503663) B5503663
theorem B9784289 : Blo 2143435 9784289 := bstep (se 2 (by rfl) ⟨3669108, by rfl⟩ : syracuseStep 9784289 = 7338217) B7338217
theorem B6522859 : Blo 2143435 6522859 := bstep (se 1 (by rfl) ⟨4892144, by rfl⟩ : syracuseStep 6522859 = 9784289) B9784289
theorem B8697145 : Blo 2143435 8697145 := bstep (se 2 (by rfl) ⟨3261429, by rfl⟩ : syracuseStep 8697145 = 6522859) B6522859
theorem B11596193 : Blo 2143435 11596193 := bstep (se 2 (by rfl) ⟨4348572, by rfl⟩ : syracuseStep 11596193 = 8697145) B8697145
theorem B7730795 : Blo 2143435 7730795 := bstep (se 1 (by rfl) ⟨5798096, by rfl⟩ : syracuseStep 7730795 = 11596193) B11596193
theorem B5153863 : Blo 2143435 5153863 := bstep (se 1 (by rfl) ⟨3865397, by rfl⟩ : syracuseStep 5153863 = 7730795) B7730795
theorem B6871817 : Blo 2143435 6871817 := bstep (se 2 (by rfl) ⟨2576931, by rfl⟩ : syracuseStep 6871817 = 5153863) B5153863
theorem B4581211 : Blo 2143435 4581211 := bstep (se 1 (by rfl) ⟨3435908, by rfl⟩ : syracuseStep 4581211 = 6871817) B6871817
theorem B6108281 : Blo 2143435 6108281 := bstep (se 2 (by rfl) ⟨2290605, by rfl⟩ : syracuseStep 6108281 = 4581211) B4581211
theorem B4072187 : Blo 2143435 4072187 := bstep (se 1 (by rfl) ⟨3054140, by rfl⟩ : syracuseStep 4072187 = 6108281) B6108281
theorem B2714791 : Blo 2143435 2714791 := bstep (se 1 (by rfl) ⟨2036093, by rfl⟩ : syracuseStep 2714791 = 4072187) B4072187
theorem B3619721 : Blo 2143435 3619721 := bstep (se 2 (by rfl) ⟨1357395, by rfl⟩ : syracuseStep 3619721 = 2714791) B2714791
theorem B2413147 : Blo 2143435 2413147 := bstep (se 1 (by rfl) ⟨1809860, by rfl⟩ : syracuseStep 2413147 = 3619721) B3619721
theorem B3217529 : Blo 2143435 3217529 := bstep (se 2 (by rfl) ⟨1206573, by rfl⟩ : syracuseStep 3217529 = 2413147) B2413147
theorem B2145019 : Blo 2143435 2145019 := bstep (se 1 (by rfl) ⟨1608764, by rfl⟩ : syracuseStep 2145019 = 3217529) B3217529
theorem B6522869 : Blo 2143435 6522869 := bbase (se 5 (by rfl) ⟨305759, by rfl⟩ : syracuseStep 6522869 = 611519) (by norm_num)
theorem B4348579 : Blo 2143435 4348579 := bstep (se 1 (by rfl) ⟨3261434, by rfl⟩ : syracuseStep 4348579 = 6522869) B6522869
theorem B5798105 : Blo 2143435 5798105 := bstep (se 2 (by rfl) ⟨2174289, by rfl⟩ : syracuseStep 5798105 = 4348579) B4348579
theorem B3865403 : Blo 2143435 3865403 := bstep (se 1 (by rfl) ⟨2899052, by rfl⟩ : syracuseStep 3865403 = 5798105) B5798105
theorem B10307741 : Blo 2143435 10307741 := bstep (se 3 (by rfl) ⟨1932701, by rfl⟩ : syracuseStep 10307741 = 3865403) B3865403
theorem B27487309 : Blo 2143435 27487309 := bstep (se 3 (by rfl) ⟨5153870, by rfl⟩ : syracuseStep 27487309 = 10307741) B10307741
theorem B36649745 : Blo 2143435 36649745 := bstep (se 2 (by rfl) ⟨13743654, by rfl⟩ : syracuseStep 36649745 = 27487309) B27487309
theorem B24433163 : Blo 2143435 24433163 := bstep (se 1 (by rfl) ⟨18324872, by rfl⟩ : syracuseStep 24433163 = 36649745) B36649745
theorem B16288775 : Blo 2143435 16288775 := bstep (se 1 (by rfl) ⟨12216581, by rfl⟩ : syracuseStep 16288775 = 24433163) B24433163
theorem B10859183 : Blo 2143435 10859183 := bstep (se 1 (by rfl) ⟨8144387, by rfl⟩ : syracuseStep 10859183 = 16288775) B16288775
theorem B7239455 : Blo 2143435 7239455 := bstep (se 1 (by rfl) ⟨5429591, by rfl⟩ : syracuseStep 7239455 = 10859183) B10859183
theorem B4826303 : Blo 2143435 4826303 := bstep (se 1 (by rfl) ⟨3619727, by rfl⟩ : syracuseStep 4826303 = 7239455) B7239455
theorem B3217535 : Blo 2143435 3217535 := bstep (se 1 (by rfl) ⟨2413151, by rfl⟩ : syracuseStep 3217535 = 4826303) B4826303
theorem B2145023 : Blo 2143435 2145023 := bstep (se 1 (by rfl) ⟨1608767, by rfl⟩ : syracuseStep 2145023 = 3217535) B3217535
theorem B3217541 : Blo 2143435 3217541 := bbase (se 4 (by rfl) ⟨301644, by rfl⟩ : syracuseStep 3217541 = 603289) (by norm_num)
theorem B2145027 : Blo 2143435 2145027 := bstep (se 1 (by rfl) ⟨1608770, by rfl⟩ : syracuseStep 2145027 = 3217541) B3217541
theorem B3619741 : Blo 2143435 3619741 := bbase (se 3 (by rfl) ⟨678701, by rfl⟩ : syracuseStep 3619741 = 1357403) (by norm_num)
theorem B4826321 : Blo 2143435 4826321 := bstep (se 2 (by rfl) ⟨1809870, by rfl⟩ : syracuseStep 4826321 = 3619741) B3619741
theorem B3217547 : Blo 2143435 3217547 := bstep (se 1 (by rfl) ⟨2413160, by rfl⟩ : syracuseStep 3217547 = 4826321) B4826321
theorem B2145031 : Blo 2143435 2145031 := bstep (se 1 (by rfl) ⟨1608773, by rfl⟩ : syracuseStep 2145031 = 3217547) B3217547
theorem B2413165 : Blo 2143435 2413165 := bbase (se 3 (by rfl) ⟨452468, by rfl⟩ : syracuseStep 2413165 = 904937) (by norm_num)
theorem B3217553 : Blo 2143435 3217553 := bstep (se 2 (by rfl) ⟨1206582, by rfl⟩ : syracuseStep 3217553 = 2413165) B2413165
theorem B2145035 : Blo 2143435 2145035 := bstep (se 1 (by rfl) ⟨1608776, by rfl⟩ : syracuseStep 2145035 = 3217553) B3217553
theorem B7239509 : Blo 2143435 7239509 := bbase (se 9 (by rfl) ⟨21209, by rfl⟩ : syracuseStep 7239509 = 42419) (by norm_num)
theorem B4826339 : Blo 2143435 4826339 := bstep (se 1 (by rfl) ⟨3619754, by rfl⟩ : syracuseStep 4826339 = 7239509) B7239509
theorem B3217559 : Blo 2143435 3217559 := bstep (se 1 (by rfl) ⟨2413169, by rfl⟩ : syracuseStep 3217559 = 4826339) B4826339
theorem B2145039 : Blo 2143435 2145039 := bstep (se 1 (by rfl) ⟨1608779, by rfl⟩ : syracuseStep 2145039 = 3217559) B3217559
theorem B3217565 : Blo 2143435 3217565 := bbase (se 3 (by rfl) ⟨603293, by rfl⟩ : syracuseStep 3217565 = 1206587) (by norm_num)
theorem B2145043 : Blo 2143435 2145043 := bstep (se 1 (by rfl) ⟨1608782, by rfl⟩ : syracuseStep 2145043 = 3217565) B3217565
theorem B4826357 : Blo 2143435 4826357 := bbase (se 5 (by rfl) ⟨226235, by rfl⟩ : syracuseStep 4826357 = 452471) (by norm_num)
theorem B3217571 : Blo 2143435 3217571 := bstep (se 1 (by rfl) ⟨2413178, by rfl⟩ : syracuseStep 3217571 = 4826357) B4826357
theorem B2145047 : Blo 2143435 2145047 := bstep (se 1 (by rfl) ⟨1608785, by rfl⟩ : syracuseStep 2145047 = 3217571) B3217571
theorem B23192725 : Blo 2143435 23192725 := bbase (se 6 (by rfl) ⟨543579, by rfl⟩ : syracuseStep 23192725 = 1087159) (by norm_num)
theorem B30923633 : Blo 2143435 30923633 := bstep (se 2 (by rfl) ⟨11596362, by rfl⟩ : syracuseStep 30923633 = 23192725) B23192725
theorem B20615755 : Blo 2143435 20615755 := bstep (se 1 (by rfl) ⟨15461816, by rfl⟩ : syracuseStep 20615755 = 30923633) B30923633
theorem B27487673 : Blo 2143435 27487673 := bstep (se 2 (by rfl) ⟨10307877, by rfl⟩ : syracuseStep 27487673 = 20615755) B20615755
theorem B18325115 : Blo 2143435 18325115 := bstep (se 1 (by rfl) ⟨13743836, by rfl⟩ : syracuseStep 18325115 = 27487673) B27487673
theorem B12216743 : Blo 2143435 12216743 := bstep (se 1 (by rfl) ⟨9162557, by rfl⟩ : syracuseStep 12216743 = 18325115) B18325115
theorem B8144495 : Blo 2143435 8144495 := bstep (se 1 (by rfl) ⟨6108371, by rfl⟩ : syracuseStep 8144495 = 12216743) B12216743
theorem B5429663 : Blo 2143435 5429663 := bstep (se 1 (by rfl) ⟨4072247, by rfl⟩ : syracuseStep 5429663 = 8144495) B8144495
theorem B3619775 : Blo 2143435 3619775 := bstep (se 1 (by rfl) ⟨2714831, by rfl⟩ : syracuseStep 3619775 = 5429663) B5429663
theorem B2413183 : Blo 2143435 2413183 := bstep (se 1 (by rfl) ⟨1809887, by rfl⟩ : syracuseStep 2413183 = 3619775) B3619775
theorem B3217577 : Blo 2143435 3217577 := bstep (se 2 (by rfl) ⟨1206591, by rfl⟩ : syracuseStep 3217577 = 2413183) B2413183
theorem B2145051 : Blo 2143435 2145051 := bstep (se 1 (by rfl) ⟨1608788, by rfl⟩ : syracuseStep 2145051 = 3217577) B3217577
theorem B2751877 : Blo 2143435 2751877 := bbase (se 4 (by rfl) ⟨257988, by rfl⟩ : syracuseStep 2751877 = 515977) (by norm_num)
theorem B14676677 : Blo 2143435 14676677 := bstep (se 4 (by rfl) ⟨1375938, by rfl⟩ : syracuseStep 14676677 = 2751877) B2751877
theorem B9784451 : Blo 2143435 9784451 := bstep (se 1 (by rfl) ⟨7338338, by rfl⟩ : syracuseStep 9784451 = 14676677) B14676677
theorem B6522967 : Blo 2143435 6522967 := bstep (se 1 (by rfl) ⟨4892225, by rfl⟩ : syracuseStep 6522967 = 9784451) B9784451
theorem B8697289 : Blo 2143435 8697289 := bstep (se 2 (by rfl) ⟨3261483, by rfl⟩ : syracuseStep 8697289 = 6522967) B6522967
theorem B11596385 : Blo 2143435 11596385 := bstep (se 2 (by rfl) ⟨4348644, by rfl⟩ : syracuseStep 11596385 = 8697289) B8697289
theorem B7730923 : Blo 2143435 7730923 := bstep (se 1 (by rfl) ⟨5798192, by rfl⟩ : syracuseStep 7730923 = 11596385) B11596385
theorem B10307897 : Blo 2143435 10307897 := bstep (se 2 (by rfl) ⟨3865461, by rfl⟩ : syracuseStep 10307897 = 7730923) B7730923
theorem B6871931 : Blo 2143435 6871931 := bstep (se 1 (by rfl) ⟨5153948, by rfl⟩ : syracuseStep 6871931 = 10307897) B10307897
theorem B4581287 : Blo 2143435 4581287 := bstep (se 1 (by rfl) ⟨3435965, by rfl⟩ : syracuseStep 4581287 = 6871931) B6871931
theorem B3054191 : Blo 2143435 3054191 := bstep (se 1 (by rfl) ⟨2290643, by rfl⟩ : syracuseStep 3054191 = 4581287) B4581287
theorem B8144509 : Blo 2143435 8144509 := bstep (se 3 (by rfl) ⟨1527095, by rfl⟩ : syracuseStep 8144509 = 3054191) B3054191
theorem B10859345 : Blo 2143435 10859345 := bstep (se 2 (by rfl) ⟨4072254, by rfl⟩ : syracuseStep 10859345 = 8144509) B8144509
theorem B7239563 : Blo 2143435 7239563 := bstep (se 1 (by rfl) ⟨5429672, by rfl⟩ : syracuseStep 7239563 = 10859345) B10859345
theorem B4826375 : Blo 2143435 4826375 := bstep (se 1 (by rfl) ⟨3619781, by rfl⟩ : syracuseStep 4826375 = 7239563) B7239563
theorem B3217583 : Blo 2143435 3217583 := bstep (se 1 (by rfl) ⟨2413187, by rfl⟩ : syracuseStep 3217583 = 4826375) B4826375
theorem B2145055 : Blo 2143435 2145055 := bstep (se 1 (by rfl) ⟨1608791, by rfl⟩ : syracuseStep 2145055 = 3217583) B3217583
theorem B3217589 : Blo 2143435 3217589 := bbase (se 5 (by rfl) ⟨150824, by rfl⟩ : syracuseStep 3217589 = 301649) (by norm_num)
theorem B2145059 : Blo 2143435 2145059 := bstep (se 1 (by rfl) ⟨1608794, by rfl⟩ : syracuseStep 2145059 = 3217589) B3217589
theorem B5429693 : Blo 2143435 5429693 := bbase (se 3 (by rfl) ⟨1018067, by rfl⟩ : syracuseStep 5429693 = 2036135) (by norm_num)
theorem B3619795 : Blo 2143435 3619795 := bstep (se 1 (by rfl) ⟨2714846, by rfl⟩ : syracuseStep 3619795 = 5429693) B5429693
theorem B4826393 : Blo 2143435 4826393 := bstep (se 2 (by rfl) ⟨1809897, by rfl⟩ : syracuseStep 4826393 = 3619795) B3619795
theorem B3217595 : Blo 2143435 3217595 := bstep (se 1 (by rfl) ⟨2413196, by rfl⟩ : syracuseStep 3217595 = 4826393) B4826393
theorem B2145063 : Blo 2143435 2145063 := bstep (se 1 (by rfl) ⟨1608797, by rfl⟩ : syracuseStep 2145063 = 3217595) B3217595
theorem B2413201 : Blo 2143435 2413201 := bbase (se 2 (by rfl) ⟨904950, by rfl⟩ : syracuseStep 2413201 = 1809901) (by norm_num)
theorem B3217601 : Blo 2143435 3217601 := bstep (se 2 (by rfl) ⟨1206600, by rfl⟩ : syracuseStep 3217601 = 2413201) B2413201
theorem B2145067 : Blo 2143435 2145067 := bstep (se 1 (by rfl) ⟨1608800, by rfl⟩ : syracuseStep 2145067 = 3217601) B3217601
theorem B4072285 : Blo 2143435 4072285 := bbase (se 3 (by rfl) ⟨763553, by rfl⟩ : syracuseStep 4072285 = 1527107) (by norm_num)
theorem B5429713 : Blo 2143435 5429713 := bstep (se 2 (by rfl) ⟨2036142, by rfl⟩ : syracuseStep 5429713 = 4072285) B4072285
theorem B7239617 : Blo 2143435 7239617 := bstep (se 2 (by rfl) ⟨2714856, by rfl⟩ : syracuseStep 7239617 = 5429713) B5429713
theorem B4826411 : Blo 2143435 4826411 := bstep (se 1 (by rfl) ⟨3619808, by rfl⟩ : syracuseStep 4826411 = 7239617) B7239617
theorem B3217607 : Blo 2143435 3217607 := bstep (se 1 (by rfl) ⟨2413205, by rfl⟩ : syracuseStep 3217607 = 4826411) B4826411
theorem B2145071 : Blo 2143435 2145071 := bstep (se 1 (by rfl) ⟨1608803, by rfl⟩ : syracuseStep 2145071 = 3217607) B3217607
theorem B3217613 : Blo 2143435 3217613 := bbase (se 3 (by rfl) ⟨603302, by rfl⟩ : syracuseStep 3217613 = 1206605) (by norm_num)
theorem B2145075 : Blo 2143435 2145075 := bstep (se 1 (by rfl) ⟨1608806, by rfl⟩ : syracuseStep 2145075 = 3217613) B3217613
theorem B4826429 : Blo 2143435 4826429 := bbase (se 3 (by rfl) ⟨904955, by rfl⟩ : syracuseStep 4826429 = 1809911) (by norm_num)
theorem B3217619 : Blo 2143435 3217619 := bstep (se 1 (by rfl) ⟨2413214, by rfl⟩ : syracuseStep 3217619 = 4826429) B4826429
theorem B2145079 : Blo 2143435 2145079 := bstep (se 1 (by rfl) ⟨1608809, by rfl⟩ : syracuseStep 2145079 = 3217619) B3217619
theorem B3619829 : Blo 2143435 3619829 := bbase (se 5 (by rfl) ⟨169679, by rfl⟩ : syracuseStep 3619829 = 339359) (by norm_num)
theorem B2413219 : Blo 2143435 2413219 := bstep (se 1 (by rfl) ⟨1809914, by rfl⟩ : syracuseStep 2413219 = 3619829) B3619829
theorem B3217625 : Blo 2143435 3217625 := bstep (se 2 (by rfl) ⟨1206609, by rfl⟩ : syracuseStep 3217625 = 2413219) B2413219
theorem B2145083 : Blo 2143435 2145083 := bstep (se 1 (by rfl) ⟨1608812, by rfl⟩ : syracuseStep 2145083 = 3217625) B3217625
theorem B9784597 : Blo 2143435 9784597 := bbase (se 6 (by rfl) ⟨229326, by rfl⟩ : syracuseStep 9784597 = 458653) (by norm_num)
theorem B13046129 : Blo 2143435 13046129 := bstep (se 2 (by rfl) ⟨4892298, by rfl⟩ : syracuseStep 13046129 = 9784597) B9784597
theorem B8697419 : Blo 2143435 8697419 := bstep (se 1 (by rfl) ⟨6523064, by rfl⟩ : syracuseStep 8697419 = 13046129) B13046129
theorem B5798279 : Blo 2143435 5798279 := bstep (se 1 (by rfl) ⟨4348709, by rfl⟩ : syracuseStep 5798279 = 8697419) B8697419
theorem B3865519 : Blo 2143435 3865519 := bstep (se 1 (by rfl) ⟨2899139, by rfl⟩ : syracuseStep 3865519 = 5798279) B5798279
theorem B5154025 : Blo 2143435 5154025 := bstep (se 2 (by rfl) ⟨1932759, by rfl⟩ : syracuseStep 5154025 = 3865519) B3865519
theorem B6872033 : Blo 2143435 6872033 := bstep (se 2 (by rfl) ⟨2577012, by rfl⟩ : syracuseStep 6872033 = 5154025) B5154025
theorem B4581355 : Blo 2143435 4581355 := bstep (se 1 (by rfl) ⟨3436016, by rfl⟩ : syracuseStep 4581355 = 6872033) B6872033
theorem B6108473 : Blo 2143435 6108473 := bstep (se 2 (by rfl) ⟨2290677, by rfl⟩ : syracuseStep 6108473 = 4581355) B4581355
theorem B16289261 : Blo 2143435 16289261 := bstep (se 3 (by rfl) ⟨3054236, by rfl⟩ : syracuseStep 16289261 = 6108473) B6108473
theorem B10859507 : Blo 2143435 10859507 := bstep (se 1 (by rfl) ⟨8144630, by rfl⟩ : syracuseStep 10859507 = 16289261) B16289261
theorem B7239671 : Blo 2143435 7239671 := bstep (se 1 (by rfl) ⟨5429753, by rfl⟩ : syracuseStep 7239671 = 10859507) B10859507
theorem B4826447 : Blo 2143435 4826447 := bstep (se 1 (by rfl) ⟨3619835, by rfl⟩ : syracuseStep 4826447 = 7239671) B7239671
theorem B3217631 : Blo 2143435 3217631 := bstep (se 1 (by rfl) ⟨2413223, by rfl⟩ : syracuseStep 3217631 = 4826447) B4826447
theorem B2145087 : Blo 2143435 2145087 := bstep (se 1 (by rfl) ⟨1608815, by rfl⟩ : syracuseStep 2145087 = 3217631) B3217631
theorem B3217637 : Blo 2143435 3217637 := bbase (se 4 (by rfl) ⟨301653, by rfl⟩ : syracuseStep 3217637 = 603307) (by norm_num)
theorem B2145091 : Blo 2143435 2145091 := bstep (se 1 (by rfl) ⟨1608818, by rfl⟩ : syracuseStep 2145091 = 3217637) B3217637
theorem B4581373 : Blo 2143435 4581373 := bbase (se 3 (by rfl) ⟨859007, by rfl⟩ : syracuseStep 4581373 = 1718015) (by norm_num)
theorem B6108497 : Blo 2143435 6108497 := bstep (se 2 (by rfl) ⟨2290686, by rfl⟩ : syracuseStep 6108497 = 4581373) B4581373
theorem B4072331 : Blo 2143435 4072331 := bstep (se 1 (by rfl) ⟨3054248, by rfl⟩ : syracuseStep 4072331 = 6108497) B6108497
theorem B2714887 : Blo 2143435 2714887 := bstep (se 1 (by rfl) ⟨2036165, by rfl⟩ : syracuseStep 2714887 = 4072331) B4072331
theorem B3619849 : Blo 2143435 3619849 := bstep (se 2 (by rfl) ⟨1357443, by rfl⟩ : syracuseStep 3619849 = 2714887) B2714887
theorem B4826465 : Blo 2143435 4826465 := bstep (se 2 (by rfl) ⟨1809924, by rfl⟩ : syracuseStep 4826465 = 3619849) B3619849
theorem B3217643 : Blo 2143435 3217643 := bstep (se 1 (by rfl) ⟨2413232, by rfl⟩ : syracuseStep 3217643 = 4826465) B4826465
theorem B2145095 : Blo 2143435 2145095 := bstep (se 1 (by rfl) ⟨1608821, by rfl⟩ : syracuseStep 2145095 = 3217643) B3217643
theorem B2413237 : Blo 2143435 2413237 := bbase (se 5 (by rfl) ⟨113120, by rfl⟩ : syracuseStep 2413237 = 226241) (by norm_num)
theorem B3217649 : Blo 2143435 3217649 := bstep (se 2 (by rfl) ⟨1206618, by rfl⟩ : syracuseStep 3217649 = 2413237) B2413237
theorem B2145099 : Blo 2143435 2145099 := bstep (se 1 (by rfl) ⟨1608824, by rfl⟩ : syracuseStep 2145099 = 3217649) B3217649
theorem B2714897 : Blo 2143435 2714897 := bbase (se 2 (by rfl) ⟨1018086, by rfl⟩ : syracuseStep 2714897 = 2036173) (by norm_num)
theorem B7239725 : Blo 2143435 7239725 := bstep (se 3 (by rfl) ⟨1357448, by rfl⟩ : syracuseStep 7239725 = 2714897) B2714897
theorem B4826483 : Blo 2143435 4826483 := bstep (se 1 (by rfl) ⟨3619862, by rfl⟩ : syracuseStep 4826483 = 7239725) B7239725
theorem B3217655 : Blo 2143435 3217655 := bstep (se 1 (by rfl) ⟨2413241, by rfl⟩ : syracuseStep 3217655 = 4826483) B4826483
theorem B2145103 : Blo 2143435 2145103 := bstep (se 1 (by rfl) ⟨1608827, by rfl⟩ : syracuseStep 2145103 = 3217655) B3217655
theorem B3217661 : Blo 2143435 3217661 := bbase (se 3 (by rfl) ⟨603311, by rfl⟩ : syracuseStep 3217661 = 1206623) (by norm_num)
theorem B2145107 : Blo 2143435 2145107 := bstep (se 1 (by rfl) ⟨1608830, by rfl⟩ : syracuseStep 2145107 = 3217661) B3217661
theorem B4826501 : Blo 2143435 4826501 := bbase (se 4 (by rfl) ⟨452484, by rfl⟩ : syracuseStep 4826501 = 904969) (by norm_num)
theorem B3217667 : Blo 2143435 3217667 := bstep (se 1 (by rfl) ⟨2413250, by rfl⟩ : syracuseStep 3217667 = 4826501) B4826501
theorem B2145111 : Blo 2143435 2145111 := bstep (se 1 (by rfl) ⟨1608833, by rfl⟩ : syracuseStep 2145111 = 3217667) B3217667
theorem B3054277 : Blo 2143435 3054277 := bbase (se 4 (by rfl) ⟨286338, by rfl⟩ : syracuseStep 3054277 = 572677) (by norm_num)
theorem B4072369 : Blo 2143435 4072369 := bstep (se 2 (by rfl) ⟨1527138, by rfl⟩ : syracuseStep 4072369 = 3054277) B3054277
theorem B5429825 : Blo 2143435 5429825 := bstep (se 2 (by rfl) ⟨2036184, by rfl⟩ : syracuseStep 5429825 = 4072369) B4072369
theorem B3619883 : Blo 2143435 3619883 := bstep (se 1 (by rfl) ⟨2714912, by rfl⟩ : syracuseStep 3619883 = 5429825) B5429825
theorem B2413255 : Blo 2143435 2413255 := bstep (se 1 (by rfl) ⟨1809941, by rfl⟩ : syracuseStep 2413255 = 3619883) B3619883
theorem B3217673 : Blo 2143435 3217673 := bstep (se 2 (by rfl) ⟨1206627, by rfl⟩ : syracuseStep 3217673 = 2413255) B2413255
theorem B2145115 : Blo 2143435 2145115 := bstep (se 1 (by rfl) ⟨1608836, by rfl⟩ : syracuseStep 2145115 = 3217673) B3217673
theorem B10859669 : Blo 2143435 10859669 := bbase (se 6 (by rfl) ⟨254523, by rfl⟩ : syracuseStep 10859669 = 509047) (by norm_num)
theorem B7239779 : Blo 2143435 7239779 := bstep (se 1 (by rfl) ⟨5429834, by rfl⟩ : syracuseStep 7239779 = 10859669) B10859669
theorem B4826519 : Blo 2143435 4826519 := bstep (se 1 (by rfl) ⟨3619889, by rfl⟩ : syracuseStep 4826519 = 7239779) B7239779
theorem B3217679 : Blo 2143435 3217679 := bstep (se 1 (by rfl) ⟨2413259, by rfl⟩ : syracuseStep 3217679 = 4826519) B4826519
theorem B2145119 : Blo 2143435 2145119 := bstep (se 1 (by rfl) ⟨1608839, by rfl⟩ : syracuseStep 2145119 = 3217679) B3217679
theorem B3217685 : Blo 2143435 3217685 := bbase (se 6 (by rfl) ⟨75414, by rfl⟩ : syracuseStep 3217685 = 150829) (by norm_num)
theorem B2145123 : Blo 2143435 2145123 := bstep (se 1 (by rfl) ⟨1608842, by rfl⟩ : syracuseStep 2145123 = 3217685) B3217685
theorem B3669293 : Blo 2143435 3669293 := bbase (se 3 (by rfl) ⟨687992, by rfl⟩ : syracuseStep 3669293 = 1375985) (by norm_num)
theorem B2446195 : Blo 2143435 2446195 := bstep (se 1 (by rfl) ⟨1834646, by rfl⟩ : syracuseStep 2446195 = 3669293) B3669293
theorem B3261593 : Blo 2143435 3261593 := bstep (se 2 (by rfl) ⟨1223097, by rfl⟩ : syracuseStep 3261593 = 2446195) B2446195
theorem B8697581 : Blo 2143435 8697581 := bstep (se 3 (by rfl) ⟨1630796, by rfl⟩ : syracuseStep 8697581 = 3261593) B3261593
theorem B5798387 : Blo 2143435 5798387 := bstep (se 1 (by rfl) ⟨4348790, by rfl⟩ : syracuseStep 5798387 = 8697581) B8697581
theorem B3865591 : Blo 2143435 3865591 := bstep (se 1 (by rfl) ⟨2899193, by rfl⟩ : syracuseStep 3865591 = 5798387) B5798387
theorem B5154121 : Blo 2143435 5154121 := bstep (se 2 (by rfl) ⟨1932795, by rfl⟩ : syracuseStep 5154121 = 3865591) B3865591
theorem B27488645 : Blo 2143435 27488645 := bstep (se 4 (by rfl) ⟨2577060, by rfl⟩ : syracuseStep 27488645 = 5154121) B5154121
theorem B18325763 : Blo 2143435 18325763 := bstep (se 1 (by rfl) ⟨13744322, by rfl⟩ : syracuseStep 18325763 = 27488645) B27488645
theorem B12217175 : Blo 2143435 12217175 := bstep (se 1 (by rfl) ⟨9162881, by rfl⟩ : syracuseStep 12217175 = 18325763) B18325763
theorem B8144783 : Blo 2143435 8144783 := bstep (se 1 (by rfl) ⟨6108587, by rfl⟩ : syracuseStep 8144783 = 12217175) B12217175
theorem B5429855 : Blo 2143435 5429855 := bstep (se 1 (by rfl) ⟨4072391, by rfl⟩ : syracuseStep 5429855 = 8144783) B8144783
theorem B3619903 : Blo 2143435 3619903 := bstep (se 1 (by rfl) ⟨2714927, by rfl⟩ : syracuseStep 3619903 = 5429855) B5429855
theorem B4826537 : Blo 2143435 4826537 := bstep (se 2 (by rfl) ⟨1809951, by rfl⟩ : syracuseStep 4826537 = 3619903) B3619903
theorem B3217691 : Blo 2143435 3217691 := bstep (se 1 (by rfl) ⟨2413268, by rfl⟩ : syracuseStep 3217691 = 4826537) B4826537
theorem B2145127 : Blo 2143435 2145127 := bstep (se 1 (by rfl) ⟨1608845, by rfl⟩ : syracuseStep 2145127 = 3217691) B3217691
theorem B2413273 : Blo 2143435 2413273 := bbase (se 2 (by rfl) ⟨904977, by rfl⟩ : syracuseStep 2413273 = 1809955) (by norm_num)
theorem B3217697 : Blo 2143435 3217697 := bstep (se 2 (by rfl) ⟨1206636, by rfl⟩ : syracuseStep 3217697 = 2413273) B2413273
theorem B2145131 : Blo 2143435 2145131 := bstep (se 1 (by rfl) ⟨1608848, by rfl⟩ : syracuseStep 2145131 = 3217697) B3217697
theorem B2290729 : Blo 2143435 2290729 := bbase (se 2 (by rfl) ⟨859023, by rfl⟩ : syracuseStep 2290729 = 1718047) (by norm_num)
theorem B3054305 : Blo 2143435 3054305 := bstep (se 2 (by rfl) ⟨1145364, by rfl⟩ : syracuseStep 3054305 = 2290729) B2290729
theorem B8144813 : Blo 2143435 8144813 := bstep (se 3 (by rfl) ⟨1527152, by rfl⟩ : syracuseStep 8144813 = 3054305) B3054305
theorem B5429875 : Blo 2143435 5429875 := bstep (se 1 (by rfl) ⟨4072406, by rfl⟩ : syracuseStep 5429875 = 8144813) B8144813
theorem B7239833 : Blo 2143435 7239833 := bstep (se 2 (by rfl) ⟨2714937, by rfl⟩ : syracuseStep 7239833 = 5429875) B5429875
theorem B4826555 : Blo 2143435 4826555 := bstep (se 1 (by rfl) ⟨3619916, by rfl⟩ : syracuseStep 4826555 = 7239833) B7239833
theorem B3217703 : Blo 2143435 3217703 := bstep (se 1 (by rfl) ⟨2413277, by rfl⟩ : syracuseStep 3217703 = 4826555) B4826555
theorem B2145135 : Blo 2143435 2145135 := bstep (se 1 (by rfl) ⟨1608851, by rfl⟩ : syracuseStep 2145135 = 3217703) B3217703
theorem B3217709 : Blo 2143435 3217709 := bbase (se 3 (by rfl) ⟨603320, by rfl⟩ : syracuseStep 3217709 = 1206641) (by norm_num)
theorem B2145139 : Blo 2143435 2145139 := bstep (se 1 (by rfl) ⟨1608854, by rfl⟩ : syracuseStep 2145139 = 3217709) B3217709
theorem B4826573 : Blo 2143435 4826573 := bbase (se 3 (by rfl) ⟨904982, by rfl⟩ : syracuseStep 4826573 = 1809965) (by norm_num)
theorem B3217715 : Blo 2143435 3217715 := bstep (se 1 (by rfl) ⟨2413286, by rfl⟩ : syracuseStep 3217715 = 4826573) B4826573
theorem B2145143 : Blo 2143435 2145143 := bstep (se 1 (by rfl) ⟨1608857, by rfl⟩ : syracuseStep 2145143 = 3217715) B3217715
theorem B2714953 : Blo 2143435 2714953 := bbase (se 2 (by rfl) ⟨1018107, by rfl⟩ : syracuseStep 2714953 = 2036215) (by norm_num)
theorem B3619937 : Blo 2143435 3619937 := bstep (se 2 (by rfl) ⟨1357476, by rfl⟩ : syracuseStep 3619937 = 2714953) B2714953
theorem B2413291 : Blo 2143435 2413291 := bstep (se 1 (by rfl) ⟨1809968, by rfl⟩ : syracuseStep 2413291 = 3619937) B3619937
theorem B3217721 : Blo 2143435 3217721 := bstep (se 2 (by rfl) ⟨1206645, by rfl⟩ : syracuseStep 3217721 = 2413291) B2413291
theorem B2145147 : Blo 2143435 2145147 := bstep (se 1 (by rfl) ⟨1608860, by rfl⟩ : syracuseStep 2145147 = 3217721) B3217721
theorem B5590757 : Blo 2143435 5590757 := bbase (se 4 (by rfl) ⟨524133, by rfl⟩ : syracuseStep 5590757 = 1048267) (by norm_num)
theorem B3727171 : Blo 2143435 3727171 := bstep (se 1 (by rfl) ⟨2795378, by rfl⟩ : syracuseStep 3727171 = 5590757) B5590757
theorem B4969561 : Blo 2143435 4969561 := bstep (se 2 (by rfl) ⟨1863585, by rfl⟩ : syracuseStep 4969561 = 3727171) B3727171
theorem B6626081 : Blo 2143435 6626081 := bstep (se 2 (by rfl) ⟨2484780, by rfl⟩ : syracuseStep 6626081 = 4969561) B4969561
theorem B17669549 : Blo 2143435 17669549 := bstep (se 3 (by rfl) ⟨3313040, by rfl⟩ : syracuseStep 17669549 = 6626081) B6626081
theorem B47118797 : Blo 2143435 47118797 := bstep (se 3 (by rfl) ⟨8834774, by rfl⟩ : syracuseStep 47118797 = 17669549) B17669549
theorem B31412531 : Blo 2143435 31412531 := bstep (se 1 (by rfl) ⟨23559398, by rfl⟩ : syracuseStep 31412531 = 47118797) B47118797
theorem B20941687 : Blo 2143435 20941687 := bstep (se 1 (by rfl) ⟨15706265, by rfl⟩ : syracuseStep 20941687 = 31412531) B31412531
theorem B27922249 : Blo 2143435 27922249 := bstep (se 2 (by rfl) ⟨10470843, by rfl⟩ : syracuseStep 27922249 = 20941687) B20941687
theorem B37229665 : Blo 2143435 37229665 := bstep (se 2 (by rfl) ⟨13961124, by rfl⟩ : syracuseStep 37229665 = 27922249) B27922249
theorem B49639553 : Blo 2143435 49639553 := bstep (se 2 (by rfl) ⟨18614832, by rfl⟩ : syracuseStep 49639553 = 37229665) B37229665
theorem B33093035 : Blo 2143435 33093035 := bstep (se 1 (by rfl) ⟨24819776, by rfl⟩ : syracuseStep 33093035 = 49639553) B49639553
theorem B22062023 : Blo 2143435 22062023 := bstep (se 1 (by rfl) ⟨16546517, by rfl⟩ : syracuseStep 22062023 = 33093035) B33093035
theorem B14708015 : Blo 2143435 14708015 := bstep (se 1 (by rfl) ⟨11031011, by rfl⟩ : syracuseStep 14708015 = 22062023) B22062023
theorem B156885493 : Blo 2143435 156885493 := bstep (se 5 (by rfl) ⟨7354007, by rfl⟩ : syracuseStep 156885493 = 14708015) B14708015
theorem B209180657 : Blo 2143435 209180657 := bstep (se 2 (by rfl) ⟨78442746, by rfl⟩ : syracuseStep 209180657 = 156885493) B156885493
theorem B139453771 : Blo 2143435 139453771 := bstep (se 1 (by rfl) ⟨104590328, by rfl⟩ : syracuseStep 139453771 = 209180657) B209180657
theorem B185938361 : Blo 2143435 185938361 := bstep (se 2 (by rfl) ⟨69726885, by rfl⟩ : syracuseStep 185938361 = 139453771) B139453771
theorem B123958907 : Blo 2143435 123958907 := bstep (se 1 (by rfl) ⟨92969180, by rfl⟩ : syracuseStep 123958907 = 185938361) B185938361
theorem B82639271 : Blo 2143435 82639271 := bstep (se 1 (by rfl) ⟨61979453, by rfl⟩ : syracuseStep 82639271 = 123958907) B123958907
theorem B55092847 : Blo 2143435 55092847 := bstep (se 1 (by rfl) ⟨41319635, by rfl⟩ : syracuseStep 55092847 = 82639271) B82639271
theorem B73457129 : Blo 2143435 73457129 := bstep (se 2 (by rfl) ⟨27546423, by rfl⟩ : syracuseStep 73457129 = 55092847) B55092847
theorem B3134170837 : Blo 2143435 3134170837 := bstep (se 7 (by rfl) ⟨36728564, by rfl⟩ : syracuseStep 3134170837 = 73457129) B73457129
theorem B4178894449 : Blo 2143435 4178894449 := bstep (se 2 (by rfl) ⟨1567085418, by rfl⟩ : syracuseStep 4178894449 = 3134170837) B3134170837
theorem B5571859265 : Blo 2143435 5571859265 := bstep (se 2 (by rfl) ⟨2089447224, by rfl⟩ : syracuseStep 5571859265 = 4178894449) B4178894449
theorem B3714572843 : Blo 2143435 3714572843 := bstep (se 1 (by rfl) ⟨2785929632, by rfl⟩ : syracuseStep 3714572843 = 5571859265) B5571859265
theorem B2476381895 : Blo 2143435 2476381895 := bstep (se 1 (by rfl) ⟨1857286421, by rfl⟩ : syracuseStep 2476381895 = 3714572843) B3714572843
theorem B1650921263 : Blo 2143435 1650921263 := bstep (se 1 (by rfl) ⟨1238190947, by rfl⟩ : syracuseStep 1650921263 = 2476381895) B2476381895
theorem B1100614175 : Blo 2143435 1100614175 := bstep (se 1 (by rfl) ⟨825460631, by rfl⟩ : syracuseStep 1100614175 = 1650921263) B1650921263
theorem B733742783 : Blo 2143435 733742783 := bstep (se 1 (by rfl) ⟨550307087, by rfl⟩ : syracuseStep 733742783 = 1100614175) B1100614175
theorem B489161855 : Blo 2143435 489161855 := bstep (se 1 (by rfl) ⟨366871391, by rfl⟩ : syracuseStep 489161855 = 733742783) B733742783
theorem B326107903 : Blo 2143435 326107903 := bstep (se 1 (by rfl) ⟨244580927, by rfl⟩ : syracuseStep 326107903 = 489161855) B489161855
theorem B434810537 : Blo 2143435 434810537 := bstep (se 2 (by rfl) ⟨163053951, by rfl⟩ : syracuseStep 434810537 = 326107903) B326107903
theorem B289873691 : Blo 2143435 289873691 := bstep (se 1 (by rfl) ⟨217405268, by rfl⟩ : syracuseStep 289873691 = 434810537) B434810537
theorem B193249127 : Blo 2143435 193249127 := bstep (se 1 (by rfl) ⟨144936845, by rfl⟩ : syracuseStep 193249127 = 289873691) B289873691
theorem B128832751 : Blo 2143435 128832751 := bstep (se 1 (by rfl) ⟨96624563, by rfl⟩ : syracuseStep 128832751 = 193249127) B193249127
theorem B687108005 : Blo 2143435 687108005 := bstep (se 4 (by rfl) ⟨64416375, by rfl⟩ : syracuseStep 687108005 = 128832751) B128832751
theorem B458072003 : Blo 2143435 458072003 := bstep (se 1 (by rfl) ⟨343554002, by rfl⟩ : syracuseStep 458072003 = 687108005) B687108005
theorem B305381335 : Blo 2143435 305381335 := bstep (se 1 (by rfl) ⟨229036001, by rfl⟩ : syracuseStep 305381335 = 458072003) B458072003
theorem B407175113 : Blo 2143435 407175113 := bstep (se 2 (by rfl) ⟨152690667, by rfl⟩ : syracuseStep 407175113 = 305381335) B305381335
theorem B271450075 : Blo 2143435 271450075 := bstep (se 1 (by rfl) ⟨203587556, by rfl⟩ : syracuseStep 271450075 = 407175113) B407175113
theorem B361933433 : Blo 2143435 361933433 := bstep (se 2 (by rfl) ⟨135725037, by rfl⟩ : syracuseStep 361933433 = 271450075) B271450075
theorem B241288955 : Blo 2143435 241288955 := bstep (se 1 (by rfl) ⟨180966716, by rfl⟩ : syracuseStep 241288955 = 361933433) B361933433
theorem B160859303 : Blo 2143435 160859303 := bstep (se 1 (by rfl) ⟨120644477, by rfl⟩ : syracuseStep 160859303 = 241288955) B241288955
theorem B107239535 : Blo 2143435 107239535 := bstep (se 1 (by rfl) ⟨80429651, by rfl⟩ : syracuseStep 107239535 = 160859303) B160859303
theorem B71493023 : Blo 2143435 71493023 := bstep (se 1 (by rfl) ⟨53619767, by rfl⟩ : syracuseStep 71493023 = 107239535) B107239535
theorem B47662015 : Blo 2143435 47662015 := bstep (se 1 (by rfl) ⟨35746511, by rfl⟩ : syracuseStep 47662015 = 71493023) B71493023
theorem B63549353 : Blo 2143435 63549353 := bstep (se 2 (by rfl) ⟨23831007, by rfl⟩ : syracuseStep 63549353 = 47662015) B47662015
theorem B42366235 : Blo 2143435 42366235 := bstep (se 1 (by rfl) ⟨31774676, by rfl⟩ : syracuseStep 42366235 = 63549353) B63549353
theorem B56488313 : Blo 2143435 56488313 := bstep (se 2 (by rfl) ⟨21183117, by rfl⟩ : syracuseStep 56488313 = 42366235) B42366235
theorem B37658875 : Blo 2143435 37658875 := bstep (se 1 (by rfl) ⟨28244156, by rfl⟩ : syracuseStep 37658875 = 56488313) B56488313
theorem B50211833 : Blo 2143435 50211833 := bstep (se 2 (by rfl) ⟨18829437, by rfl⟩ : syracuseStep 50211833 = 37658875) B37658875
theorem B133898221 : Blo 2143435 133898221 := bstep (se 3 (by rfl) ⟨25105916, by rfl⟩ : syracuseStep 133898221 = 50211833) B50211833
theorem B178530961 : Blo 2143435 178530961 := bstep (se 2 (by rfl) ⟨66949110, by rfl⟩ : syracuseStep 178530961 = 133898221) B133898221
theorem B238041281 : Blo 2143435 238041281 := bstep (se 2 (by rfl) ⟨89265480, by rfl⟩ : syracuseStep 238041281 = 178530961) B178530961
theorem B158694187 : Blo 2143435 158694187 := bstep (se 1 (by rfl) ⟨119020640, by rfl⟩ : syracuseStep 158694187 = 238041281) B238041281
theorem B211592249 : Blo 2143435 211592249 := bstep (se 2 (by rfl) ⟨79347093, by rfl⟩ : syracuseStep 211592249 = 158694187) B158694187
theorem B141061499 : Blo 2143435 141061499 := bstep (se 1 (by rfl) ⟨105796124, by rfl⟩ : syracuseStep 141061499 = 211592249) B211592249
theorem B94040999 : Blo 2143435 94040999 := bstep (se 1 (by rfl) ⟨70530749, by rfl⟩ : syracuseStep 94040999 = 141061499) B141061499
theorem B62693999 : Blo 2143435 62693999 := bstep (se 1 (by rfl) ⟨47020499, by rfl⟩ : syracuseStep 62693999 = 94040999) B94040999
theorem B41795999 : Blo 2143435 41795999 := bstep (se 1 (by rfl) ⟨31346999, by rfl⟩ : syracuseStep 41795999 = 62693999) B62693999
theorem B27863999 : Blo 2143435 27863999 := bstep (se 1 (by rfl) ⟨20897999, by rfl⟩ : syracuseStep 27863999 = 41795999) B41795999
theorem B18575999 : Blo 2143435 18575999 := bstep (se 1 (by rfl) ⟨13931999, by rfl⟩ : syracuseStep 18575999 = 27863999) B27863999
theorem B12383999 : Blo 2143435 12383999 := bstep (se 1 (by rfl) ⟨9287999, by rfl⟩ : syracuseStep 12383999 = 18575999) B18575999
theorem B8255999 : Blo 2143435 8255999 := bstep (se 1 (by rfl) ⟨6191999, by rfl⟩ : syracuseStep 8255999 = 12383999) B12383999
theorem B5503999 : Blo 2143435 5503999 := bstep (se 1 (by rfl) ⟨4127999, by rfl⟩ : syracuseStep 5503999 = 8255999) B8255999
theorem B7338665 : Blo 2143435 7338665 := bstep (se 2 (by rfl) ⟨2751999, by rfl⟩ : syracuseStep 7338665 = 5503999) B5503999
theorem B4892443 : Blo 2143435 4892443 := bstep (se 1 (by rfl) ⟨3669332, by rfl⟩ : syracuseStep 4892443 = 7338665) B7338665
theorem B26093029 : Blo 2143435 26093029 := bstep (se 4 (by rfl) ⟨2446221, by rfl⟩ : syracuseStep 26093029 = 4892443) B4892443
theorem B34790705 : Blo 2143435 34790705 := bstep (se 2 (by rfl) ⟨13046514, by rfl⟩ : syracuseStep 34790705 = 26093029) B26093029
theorem B23193803 : Blo 2143435 23193803 := bstep (se 1 (by rfl) ⟨17395352, by rfl⟩ : syracuseStep 23193803 = 34790705) B34790705
theorem B15462535 : Blo 2143435 15462535 := bstep (se 1 (by rfl) ⟨11596901, by rfl⟩ : syracuseStep 15462535 = 23193803) B23193803
theorem B20616713 : Blo 2143435 20616713 := bstep (se 2 (by rfl) ⟨7731267, by rfl⟩ : syracuseStep 20616713 = 15462535) B15462535
theorem B13744475 : Blo 2143435 13744475 := bstep (se 1 (by rfl) ⟨10308356, by rfl⟩ : syracuseStep 13744475 = 20616713) B20616713
theorem B9162983 : Blo 2143435 9162983 := bstep (se 1 (by rfl) ⟨6872237, by rfl⟩ : syracuseStep 9162983 = 13744475) B13744475
theorem B24434621 : Blo 2143435 24434621 := bstep (se 3 (by rfl) ⟨4581491, by rfl⟩ : syracuseStep 24434621 = 9162983) B9162983
theorem B16289747 : Blo 2143435 16289747 := bstep (se 1 (by rfl) ⟨12217310, by rfl⟩ : syracuseStep 16289747 = 24434621) B24434621
theorem B10859831 : Blo 2143435 10859831 := bstep (se 1 (by rfl) ⟨8144873, by rfl⟩ : syracuseStep 10859831 = 16289747) B16289747
theorem B7239887 : Blo 2143435 7239887 := bstep (se 1 (by rfl) ⟨5429915, by rfl⟩ : syracuseStep 7239887 = 10859831) B10859831
theorem B4826591 : Blo 2143435 4826591 := bstep (se 1 (by rfl) ⟨3619943, by rfl⟩ : syracuseStep 4826591 = 7239887) B7239887
theorem B3217727 : Blo 2143435 3217727 := bstep (se 1 (by rfl) ⟨2413295, by rfl⟩ : syracuseStep 3217727 = 4826591) B4826591
theorem B2145151 : Blo 2143435 2145151 := bstep (se 1 (by rfl) ⟨1608863, by rfl⟩ : syracuseStep 2145151 = 3217727) B3217727
theorem B3217733 : Blo 2143435 3217733 := bbase (se 4 (by rfl) ⟨301662, by rfl⟩ : syracuseStep 3217733 = 603325) (by norm_num)
theorem B2145155 : Blo 2143435 2145155 := bstep (se 1 (by rfl) ⟨1608866, by rfl⟩ : syracuseStep 2145155 = 3217733) B3217733
theorem B3619957 : Blo 2143435 3619957 := bbase (se 5 (by rfl) ⟨169685, by rfl⟩ : syracuseStep 3619957 = 339371) (by norm_num)
theorem B4826609 : Blo 2143435 4826609 := bstep (se 2 (by rfl) ⟨1809978, by rfl⟩ : syracuseStep 4826609 = 3619957) B3619957
theorem B3217739 : Blo 2143435 3217739 := bstep (se 1 (by rfl) ⟨2413304, by rfl⟩ : syracuseStep 3217739 = 4826609) B4826609
theorem B2145159 : Blo 2143435 2145159 := bstep (se 1 (by rfl) ⟨1608869, by rfl⟩ : syracuseStep 2145159 = 3217739) B3217739
theorem B2413309 : Blo 2143435 2413309 := bbase (se 3 (by rfl) ⟨452495, by rfl⟩ : syracuseStep 2413309 = 904991) (by norm_num)
theorem B3217745 : Blo 2143435 3217745 := bstep (se 2 (by rfl) ⟨1206654, by rfl⟩ : syracuseStep 3217745 = 2413309) B2413309
theorem B2145163 : Blo 2143435 2145163 := bstep (se 1 (by rfl) ⟨1608872, by rfl⟩ : syracuseStep 2145163 = 3217745) B3217745
theorem B7239941 : Blo 2143435 7239941 := bbase (se 4 (by rfl) ⟨678744, by rfl⟩ : syracuseStep 7239941 = 1357489) (by norm_num)
theorem B4826627 : Blo 2143435 4826627 := bstep (se 1 (by rfl) ⟨3619970, by rfl⟩ : syracuseStep 4826627 = 7239941) B7239941
theorem B3217751 : Blo 2143435 3217751 := bstep (se 1 (by rfl) ⟨2413313, by rfl⟩ : syracuseStep 3217751 = 4826627) B4826627
theorem B2145167 : Blo 2143435 2145167 := bstep (se 1 (by rfl) ⟨1608875, by rfl⟩ : syracuseStep 2145167 = 3217751) B3217751
theorem B3217757 : Blo 2143435 3217757 := bbase (se 3 (by rfl) ⟨603329, by rfl⟩ : syracuseStep 3217757 = 1206659) (by norm_num)
theorem B2145171 : Blo 2143435 2145171 := bstep (se 1 (by rfl) ⟨1608878, by rfl⟩ : syracuseStep 2145171 = 3217757) B3217757
theorem B4826645 : Blo 2143435 4826645 := bbase (se 6 (by rfl) ⟨113124, by rfl⟩ : syracuseStep 4826645 = 226249) (by norm_num)
theorem B3217763 : Blo 2143435 3217763 := bstep (se 1 (by rfl) ⟨2413322, by rfl⟩ : syracuseStep 3217763 = 4826645) B4826645
theorem B2145175 : Blo 2143435 2145175 := bstep (se 1 (by rfl) ⟨1608881, by rfl⟩ : syracuseStep 2145175 = 3217763) B3217763
theorem B8144981 : Blo 2143435 8144981 := bbase (se 8 (by rfl) ⟨47724, by rfl⟩ : syracuseStep 8144981 = 95449) (by norm_num)
theorem B5429987 : Blo 2143435 5429987 := bstep (se 1 (by rfl) ⟨4072490, by rfl⟩ : syracuseStep 5429987 = 8144981) B8144981
theorem B3619991 : Blo 2143435 3619991 := bstep (se 1 (by rfl) ⟨2714993, by rfl⟩ : syracuseStep 3619991 = 5429987) B5429987
theorem B2413327 : Blo 2143435 2413327 := bstep (se 1 (by rfl) ⟨1809995, by rfl⟩ : syracuseStep 2413327 = 3619991) B3619991
theorem B3217769 : Blo 2143435 3217769 := bstep (se 2 (by rfl) ⟨1206663, by rfl⟩ : syracuseStep 3217769 = 2413327) B2413327
theorem B2145179 : Blo 2143435 2145179 := bstep (se 1 (by rfl) ⟨1608884, by rfl⟩ : syracuseStep 2145179 = 3217769) B3217769
theorem B12217493 : Blo 2143435 12217493 := bbase (se 6 (by rfl) ⟨286347, by rfl⟩ : syracuseStep 12217493 = 572695) (by norm_num)
theorem B8144995 : Blo 2143435 8144995 := bstep (se 1 (by rfl) ⟨6108746, by rfl⟩ : syracuseStep 8144995 = 12217493) B12217493
theorem B10859993 : Blo 2143435 10859993 := bstep (se 2 (by rfl) ⟨4072497, by rfl⟩ : syracuseStep 10859993 = 8144995) B8144995
theorem B7239995 : Blo 2143435 7239995 := bstep (se 1 (by rfl) ⟨5429996, by rfl⟩ : syracuseStep 7239995 = 10859993) B10859993
theorem B4826663 : Blo 2143435 4826663 := bstep (se 1 (by rfl) ⟨3619997, by rfl⟩ : syracuseStep 4826663 = 7239995) B7239995
theorem B3217775 : Blo 2143435 3217775 := bstep (se 1 (by rfl) ⟨2413331, by rfl⟩ : syracuseStep 3217775 = 4826663) B4826663
theorem B2145183 : Blo 2143435 2145183 := bstep (se 1 (by rfl) ⟨1608887, by rfl⟩ : syracuseStep 2145183 = 3217775) B3217775
theorem B3217781 : Blo 2143435 3217781 := bbase (se 5 (by rfl) ⟨150833, by rfl⟩ : syracuseStep 3217781 = 301667) (by norm_num)
theorem B2145187 : Blo 2143435 2145187 := bstep (se 1 (by rfl) ⟨1608890, by rfl⟩ : syracuseStep 2145187 = 3217781) B3217781
theorem B2290789 : Blo 2143435 2290789 := bbase (se 4 (by rfl) ⟨214761, by rfl⟩ : syracuseStep 2290789 = 429523) (by norm_num)
theorem B3054385 : Blo 2143435 3054385 := bstep (se 2 (by rfl) ⟨1145394, by rfl⟩ : syracuseStep 3054385 = 2290789) B2290789
theorem B4072513 : Blo 2143435 4072513 := bstep (se 2 (by rfl) ⟨1527192, by rfl⟩ : syracuseStep 4072513 = 3054385) B3054385
theorem B5430017 : Blo 2143435 5430017 := bstep (se 2 (by rfl) ⟨2036256, by rfl⟩ : syracuseStep 5430017 = 4072513) B4072513
theorem B3620011 : Blo 2143435 3620011 := bstep (se 1 (by rfl) ⟨2715008, by rfl⟩ : syracuseStep 3620011 = 5430017) B5430017
theorem B4826681 : Blo 2143435 4826681 := bstep (se 2 (by rfl) ⟨1810005, by rfl⟩ : syracuseStep 4826681 = 3620011) B3620011
theorem B3217787 : Blo 2143435 3217787 := bstep (se 1 (by rfl) ⟨2413340, by rfl⟩ : syracuseStep 3217787 = 4826681) B4826681
theorem B2145191 : Blo 2143435 2145191 := bstep (se 1 (by rfl) ⟨1608893, by rfl⟩ : syracuseStep 2145191 = 3217787) B3217787
theorem B2413345 : Blo 2143435 2413345 := bbase (se 2 (by rfl) ⟨905004, by rfl⟩ : syracuseStep 2413345 = 1810009) (by norm_num)
theorem B3217793 : Blo 2143435 3217793 := bstep (se 2 (by rfl) ⟨1206672, by rfl⟩ : syracuseStep 3217793 = 2413345) B2413345
theorem B2145195 : Blo 2143435 2145195 := bstep (se 1 (by rfl) ⟨1608896, by rfl⟩ : syracuseStep 2145195 = 3217793) B3217793
theorem B5430037 : Blo 2143435 5430037 := bbase (se 6 (by rfl) ⟨127266, by rfl⟩ : syracuseStep 5430037 = 254533) (by norm_num)
theorem B7240049 : Blo 2143435 7240049 := bstep (se 2 (by rfl) ⟨2715018, by rfl⟩ : syracuseStep 7240049 = 5430037) B5430037
theorem B4826699 : Blo 2143435 4826699 := bstep (se 1 (by rfl) ⟨3620024, by rfl⟩ : syracuseStep 4826699 = 7240049) B7240049
theorem B3217799 : Blo 2143435 3217799 := bstep (se 1 (by rfl) ⟨2413349, by rfl⟩ : syracuseStep 3217799 = 4826699) B4826699
theorem B2145199 : Blo 2143435 2145199 := bstep (se 1 (by rfl) ⟨1608899, by rfl⟩ : syracuseStep 2145199 = 3217799) B3217799
theorem B3217805 : Blo 2143435 3217805 := bbase (se 3 (by rfl) ⟨603338, by rfl⟩ : syracuseStep 3217805 = 1206677) (by norm_num)
theorem B2145203 : Blo 2143435 2145203 := bstep (se 1 (by rfl) ⟨1608902, by rfl⟩ : syracuseStep 2145203 = 3217805) B3217805
theorem B4826717 : Blo 2143435 4826717 := bbase (se 3 (by rfl) ⟨905009, by rfl⟩ : syracuseStep 4826717 = 1810019) (by norm_num)
theorem B3217811 : Blo 2143435 3217811 := bstep (se 1 (by rfl) ⟨2413358, by rfl⟩ : syracuseStep 3217811 = 4826717) B4826717
theorem B2145207 : Blo 2143435 2145207 := bstep (se 1 (by rfl) ⟨1608905, by rfl⟩ : syracuseStep 2145207 = 3217811) B3217811
theorem B3620045 : Blo 2143435 3620045 := bbase (se 3 (by rfl) ⟨678758, by rfl⟩ : syracuseStep 3620045 = 1357517) (by norm_num)
theorem B2413363 : Blo 2143435 2413363 := bstep (se 1 (by rfl) ⟨1810022, by rfl⟩ : syracuseStep 2413363 = 3620045) B3620045
theorem B3217817 : Blo 2143435 3217817 := bstep (se 2 (by rfl) ⟨1206681, by rfl⟩ : syracuseStep 3217817 = 2413363) B2413363
theorem B2145211 : Blo 2143435 2145211 := bstep (se 1 (by rfl) ⟨1608908, by rfl⟩ : syracuseStep 2145211 = 3217817) B3217817
theorem B13744885 : Blo 2143435 13744885 := bbase (se 5 (by rfl) ⟨644291, by rfl⟩ : syracuseStep 13744885 = 1288583) (by norm_num)
theorem B18326513 : Blo 2143435 18326513 := bstep (se 2 (by rfl) ⟨6872442, by rfl⟩ : syracuseStep 18326513 = 13744885) B13744885
theorem B12217675 : Blo 2143435 12217675 := bstep (se 1 (by rfl) ⟨9163256, by rfl⟩ : syracuseStep 12217675 = 18326513) B18326513
theorem B16290233 : Blo 2143435 16290233 := bstep (se 2 (by rfl) ⟨6108837, by rfl⟩ : syracuseStep 16290233 = 12217675) B12217675
theorem B10860155 : Blo 2143435 10860155 := bstep (se 1 (by rfl) ⟨8145116, by rfl⟩ : syracuseStep 10860155 = 16290233) B16290233
theorem B7240103 : Blo 2143435 7240103 := bstep (se 1 (by rfl) ⟨5430077, by rfl⟩ : syracuseStep 7240103 = 10860155) B10860155
theorem B4826735 : Blo 2143435 4826735 := bstep (se 1 (by rfl) ⟨3620051, by rfl⟩ : syracuseStep 4826735 = 7240103) B7240103
theorem B3217823 : Blo 2143435 3217823 := bstep (se 1 (by rfl) ⟨2413367, by rfl⟩ : syracuseStep 3217823 = 4826735) B4826735
theorem B2145215 : Blo 2143435 2145215 := bstep (se 1 (by rfl) ⟨1608911, by rfl⟩ : syracuseStep 2145215 = 3217823) B3217823
theorem B3217829 : Blo 2143435 3217829 := bbase (se 4 (by rfl) ⟨301671, by rfl⟩ : syracuseStep 3217829 = 603343) (by norm_num)
theorem B2145219 : Blo 2143435 2145219 := bstep (se 1 (by rfl) ⟨1608914, by rfl⟩ : syracuseStep 2145219 = 3217829) B3217829
theorem B2715049 : Blo 2143435 2715049 := bbase (se 2 (by rfl) ⟨1018143, by rfl⟩ : syracuseStep 2715049 = 2036287) (by norm_num)
theorem B3620065 : Blo 2143435 3620065 := bstep (se 2 (by rfl) ⟨1357524, by rfl⟩ : syracuseStep 3620065 = 2715049) B2715049
theorem B4826753 : Blo 2143435 4826753 := bstep (se 2 (by rfl) ⟨1810032, by rfl⟩ : syracuseStep 4826753 = 3620065) B3620065
theorem B3217835 : Blo 2143435 3217835 := bstep (se 1 (by rfl) ⟨2413376, by rfl⟩ : syracuseStep 3217835 = 4826753) B4826753
theorem B2145223 : Blo 2143435 2145223 := bstep (se 1 (by rfl) ⟨1608917, by rfl⟩ : syracuseStep 2145223 = 3217835) B3217835
theorem B2413381 : Blo 2143435 2413381 := bbase (se 4 (by rfl) ⟨226254, by rfl⟩ : syracuseStep 2413381 = 452509) (by norm_num)
theorem B3217841 : Blo 2143435 3217841 := bstep (se 2 (by rfl) ⟨1206690, by rfl⟩ : syracuseStep 3217841 = 2413381) B2413381
theorem B2145227 : Blo 2143435 2145227 := bstep (se 1 (by rfl) ⟨1608920, by rfl⟩ : syracuseStep 2145227 = 3217841) B3217841
theorem B4072589 : Blo 2143435 4072589 := bbase (se 3 (by rfl) ⟨763610, by rfl⟩ : syracuseStep 4072589 = 1527221) (by norm_num)
theorem B2715059 : Blo 2143435 2715059 := bstep (se 1 (by rfl) ⟨2036294, by rfl⟩ : syracuseStep 2715059 = 4072589) B4072589
theorem B7240157 : Blo 2143435 7240157 := bstep (se 3 (by rfl) ⟨1357529, by rfl⟩ : syracuseStep 7240157 = 2715059) B2715059
theorem B4826771 : Blo 2143435 4826771 := bstep (se 1 (by rfl) ⟨3620078, by rfl⟩ : syracuseStep 4826771 = 7240157) B7240157
theorem B3217847 : Blo 2143435 3217847 := bstep (se 1 (by rfl) ⟨2413385, by rfl⟩ : syracuseStep 3217847 = 4826771) B4826771
theorem B2145231 : Blo 2143435 2145231 := bstep (se 1 (by rfl) ⟨1608923, by rfl⟩ : syracuseStep 2145231 = 3217847) B3217847
theorem B3217853 : Blo 2143435 3217853 := bbase (se 3 (by rfl) ⟨603347, by rfl⟩ : syracuseStep 3217853 = 1206695) (by norm_num)
theorem B2145235 : Blo 2143435 2145235 := bstep (se 1 (by rfl) ⟨1608926, by rfl⟩ : syracuseStep 2145235 = 3217853) B3217853
theorem B4826789 : Blo 2143435 4826789 := bbase (se 4 (by rfl) ⟨452511, by rfl⟩ : syracuseStep 4826789 = 905023) (by norm_num)
theorem B3217859 : Blo 2143435 3217859 := bstep (se 1 (by rfl) ⟨2413394, by rfl⟩ : syracuseStep 3217859 = 4826789) B4826789
theorem B2145239 : Blo 2143435 2145239 := bstep (se 1 (by rfl) ⟨1608929, by rfl⟩ : syracuseStep 2145239 = 3217859) B3217859
theorem B5430149 : Blo 2143435 5430149 := bbase (se 4 (by rfl) ⟨509076, by rfl⟩ : syracuseStep 5430149 = 1018153) (by norm_num)
theorem B3620099 : Blo 2143435 3620099 := bstep (se 1 (by rfl) ⟨2715074, by rfl⟩ : syracuseStep 3620099 = 5430149) B5430149
theorem B2413399 : Blo 2143435 2413399 := bstep (se 1 (by rfl) ⟨1810049, by rfl⟩ : syracuseStep 2413399 = 3620099) B3620099
theorem B3217865 : Blo 2143435 3217865 := bstep (se 2 (by rfl) ⟨1206699, by rfl⟩ : syracuseStep 3217865 = 2413399) B2413399
theorem B2145243 : Blo 2143435 2145243 := bstep (se 1 (by rfl) ⟨1608932, by rfl⟩ : syracuseStep 2145243 = 3217865) B3217865
theorem B2577205 : Blo 2143435 2577205 := bbase (se 5 (by rfl) ⟨120806, by rfl⟩ : syracuseStep 2577205 = 241613) (by norm_num)
theorem B3436273 : Blo 2143435 3436273 := bstep (se 2 (by rfl) ⟨1288602, by rfl⟩ : syracuseStep 3436273 = 2577205) B2577205
theorem B4581697 : Blo 2143435 4581697 := bstep (se 2 (by rfl) ⟨1718136, by rfl⟩ : syracuseStep 4581697 = 3436273) B3436273
theorem B6108929 : Blo 2143435 6108929 := bstep (se 2 (by rfl) ⟨2290848, by rfl⟩ : syracuseStep 6108929 = 4581697) B4581697
theorem B4072619 : Blo 2143435 4072619 := bstep (se 1 (by rfl) ⟨3054464, by rfl⟩ : syracuseStep 4072619 = 6108929) B6108929
theorem B10860317 : Blo 2143435 10860317 := bstep (se 3 (by rfl) ⟨2036309, by rfl⟩ : syracuseStep 10860317 = 4072619) B4072619
theorem B7240211 : Blo 2143435 7240211 := bstep (se 1 (by rfl) ⟨5430158, by rfl⟩ : syracuseStep 7240211 = 10860317) B10860317
theorem B4826807 : Blo 2143435 4826807 := bstep (se 1 (by rfl) ⟨3620105, by rfl⟩ : syracuseStep 4826807 = 7240211) B7240211
theorem B3217871 : Blo 2143435 3217871 := bstep (se 1 (by rfl) ⟨2413403, by rfl⟩ : syracuseStep 3217871 = 4826807) B4826807
theorem B2145247 : Blo 2143435 2145247 := bstep (se 1 (by rfl) ⟨1608935, by rfl⟩ : syracuseStep 2145247 = 3217871) B3217871
theorem B3217877 : Blo 2143435 3217877 := bbase (se 7 (by rfl) ⟨37709, by rfl⟩ : syracuseStep 3217877 = 75419) (by norm_num)
theorem B2145251 : Blo 2143435 2145251 := bstep (se 1 (by rfl) ⟨1608938, by rfl⟩ : syracuseStep 2145251 = 3217877) B3217877
theorem B8145269 : Blo 2143435 8145269 := bbase (se 5 (by rfl) ⟨381809, by rfl⟩ : syracuseStep 8145269 = 763619) (by norm_num)
theorem B5430179 : Blo 2143435 5430179 := bstep (se 1 (by rfl) ⟨4072634, by rfl⟩ : syracuseStep 5430179 = 8145269) B8145269
theorem B3620119 : Blo 2143435 3620119 := bstep (se 1 (by rfl) ⟨2715089, by rfl⟩ : syracuseStep 3620119 = 5430179) B5430179
theorem B4826825 : Blo 2143435 4826825 := bstep (se 2 (by rfl) ⟨1810059, by rfl⟩ : syracuseStep 4826825 = 3620119) B3620119
theorem B3217883 : Blo 2143435 3217883 := bstep (se 1 (by rfl) ⟨2413412, by rfl⟩ : syracuseStep 3217883 = 4826825) B4826825
theorem B2145255 : Blo 2143435 2145255 := bstep (se 1 (by rfl) ⟨1608941, by rfl⟩ : syracuseStep 2145255 = 3217883) B3217883
theorem B2413417 : Blo 2143435 2413417 := bbase (se 2 (by rfl) ⟨905031, by rfl⟩ : syracuseStep 2413417 = 1810063) (by norm_num)
theorem B3217889 : Blo 2143435 3217889 := bstep (se 2 (by rfl) ⟨1206708, by rfl⟩ : syracuseStep 3217889 = 2413417) B2413417
theorem B2145259 : Blo 2143435 2145259 := bstep (se 1 (by rfl) ⟨1608944, by rfl⟩ : syracuseStep 2145259 = 3217889) B3217889
theorem B6872597 : Blo 2143435 6872597 := bbase (se 6 (by rfl) ⟨161076, by rfl⟩ : syracuseStep 6872597 = 322153) (by norm_num)
theorem B4581731 : Blo 2143435 4581731 := bstep (se 1 (by rfl) ⟨3436298, by rfl⟩ : syracuseStep 4581731 = 6872597) B6872597
theorem B12217949 : Blo 2143435 12217949 := bstep (se 3 (by rfl) ⟨2290865, by rfl⟩ : syracuseStep 12217949 = 4581731) B4581731
theorem B8145299 : Blo 2143435 8145299 := bstep (se 1 (by rfl) ⟨6108974, by rfl⟩ : syracuseStep 8145299 = 12217949) B12217949
theorem B5430199 : Blo 2143435 5430199 := bstep (se 1 (by rfl) ⟨4072649, by rfl⟩ : syracuseStep 5430199 = 8145299) B8145299
theorem B7240265 : Blo 2143435 7240265 := bstep (se 2 (by rfl) ⟨2715099, by rfl⟩ : syracuseStep 7240265 = 5430199) B5430199
theorem B4826843 : Blo 2143435 4826843 := bstep (se 1 (by rfl) ⟨3620132, by rfl⟩ : syracuseStep 4826843 = 7240265) B7240265
theorem B3217895 : Blo 2143435 3217895 := bstep (se 1 (by rfl) ⟨2413421, by rfl⟩ : syracuseStep 3217895 = 4826843) B4826843
theorem B2145263 : Blo 2143435 2145263 := bstep (se 1 (by rfl) ⟨1608947, by rfl⟩ : syracuseStep 2145263 = 3217895) B3217895
theorem B3217901 : Blo 2143435 3217901 := bbase (se 3 (by rfl) ⟨603356, by rfl⟩ : syracuseStep 3217901 = 1206713) (by norm_num)
theorem B2145267 : Blo 2143435 2145267 := bstep (se 1 (by rfl) ⟨1608950, by rfl⟩ : syracuseStep 2145267 = 3217901) B3217901
theorem B4826861 : Blo 2143435 4826861 := bbase (se 3 (by rfl) ⟨905036, by rfl⟩ : syracuseStep 4826861 = 1810073) (by norm_num)
theorem B3217907 : Blo 2143435 3217907 := bstep (se 1 (by rfl) ⟨2413430, by rfl⟩ : syracuseStep 3217907 = 4826861) B4826861
theorem B2145271 : Blo 2143435 2145271 := bstep (se 1 (by rfl) ⟨1608953, by rfl⟩ : syracuseStep 2145271 = 3217907) B3217907
theorem B3096181 : Blo 2143435 3096181 := bbase (se 5 (by rfl) ⟨145133, by rfl⟩ : syracuseStep 3096181 = 290267) (by norm_num)
theorem B4128241 : Blo 2143435 4128241 := bstep (se 2 (by rfl) ⟨1548090, by rfl⟩ : syracuseStep 4128241 = 3096181) B3096181
theorem B5504321 : Blo 2143435 5504321 := bstep (se 2 (by rfl) ⟨2064120, by rfl⟩ : syracuseStep 5504321 = 4128241) B4128241
theorem B3669547 : Blo 2143435 3669547 := bstep (se 1 (by rfl) ⟨2752160, by rfl⟩ : syracuseStep 3669547 = 5504321) B5504321
theorem B4892729 : Blo 2143435 4892729 := bstep (se 2 (by rfl) ⟨1834773, by rfl⟩ : syracuseStep 4892729 = 3669547) B3669547
theorem B13047277 : Blo 2143435 13047277 := bstep (se 3 (by rfl) ⟨2446364, by rfl⟩ : syracuseStep 13047277 = 4892729) B4892729
theorem B17396369 : Blo 2143435 17396369 := bstep (se 2 (by rfl) ⟨6523638, by rfl⟩ : syracuseStep 17396369 = 13047277) B13047277
theorem B11597579 : Blo 2143435 11597579 := bstep (se 1 (by rfl) ⟨8698184, by rfl⟩ : syracuseStep 11597579 = 17396369) B17396369
theorem B7731719 : Blo 2143435 7731719 := bstep (se 1 (by rfl) ⟨5798789, by rfl⟩ : syracuseStep 7731719 = 11597579) B11597579
theorem B5154479 : Blo 2143435 5154479 := bstep (se 1 (by rfl) ⟨3865859, by rfl⟩ : syracuseStep 5154479 = 7731719) B7731719
theorem B3436319 : Blo 2143435 3436319 := bstep (se 1 (by rfl) ⟨2577239, by rfl⟩ : syracuseStep 3436319 = 5154479) B5154479
theorem B2290879 : Blo 2143435 2290879 := bstep (se 1 (by rfl) ⟨1718159, by rfl⟩ : syracuseStep 2290879 = 3436319) B3436319
theorem B3054505 : Blo 2143435 3054505 := bstep (se 2 (by rfl) ⟨1145439, by rfl⟩ : syracuseStep 3054505 = 2290879) B2290879
theorem B4072673 : Blo 2143435 4072673 := bstep (se 2 (by rfl) ⟨1527252, by rfl⟩ : syracuseStep 4072673 = 3054505) B3054505
theorem B2715115 : Blo 2143435 2715115 := bstep (se 1 (by rfl) ⟨2036336, by rfl⟩ : syracuseStep 2715115 = 4072673) B4072673
theorem B3620153 : Blo 2143435 3620153 := bstep (se 2 (by rfl) ⟨1357557, by rfl⟩ : syracuseStep 3620153 = 2715115) B2715115
theorem B2413435 : Blo 2143435 2413435 := bstep (se 1 (by rfl) ⟨1810076, by rfl⟩ : syracuseStep 2413435 = 3620153) B3620153
theorem B3217913 : Blo 2143435 3217913 := bstep (se 2 (by rfl) ⟨1206717, by rfl⟩ : syracuseStep 3217913 = 2413435) B2413435
theorem B2145275 : Blo 2143435 2145275 := bstep (se 1 (by rfl) ⟨1608956, by rfl⟩ : syracuseStep 2145275 = 3217913) B3217913
theorem B2479745 : Blo 2143435 2479745 := bbase (se 2 (by rfl) ⟨929904, by rfl⟩ : syracuseStep 2479745 = 1859809) (by norm_num)
theorem B6612653 : Blo 2143435 6612653 := bstep (se 3 (by rfl) ⟨1239872, by rfl⟩ : syracuseStep 6612653 = 2479745) B2479745
theorem B4408435 : Blo 2143435 4408435 := bstep (se 1 (by rfl) ⟨3306326, by rfl⟩ : syracuseStep 4408435 = 6612653) B6612653
theorem B23511653 : Blo 2143435 23511653 := bstep (se 4 (by rfl) ⟨2204217, by rfl⟩ : syracuseStep 23511653 = 4408435) B4408435
theorem B15674435 : Blo 2143435 15674435 := bstep (se 1 (by rfl) ⟨11755826, by rfl⟩ : syracuseStep 15674435 = 23511653) B23511653
theorem B10449623 : Blo 2143435 10449623 := bstep (se 1 (by rfl) ⟨7837217, by rfl⟩ : syracuseStep 10449623 = 15674435) B15674435
theorem B6966415 : Blo 2143435 6966415 := bstep (se 1 (by rfl) ⟨5224811, by rfl⟩ : syracuseStep 6966415 = 10449623) B10449623
theorem B37154213 : Blo 2143435 37154213 := bstep (se 4 (by rfl) ⟨3483207, by rfl⟩ : syracuseStep 37154213 = 6966415) B6966415
theorem B24769475 : Blo 2143435 24769475 := bstep (se 1 (by rfl) ⟨18577106, by rfl⟩ : syracuseStep 24769475 = 37154213) B37154213
theorem B16512983 : Blo 2143435 16512983 := bstep (se 1 (by rfl) ⟨12384737, by rfl⟩ : syracuseStep 16512983 = 24769475) B24769475
theorem B11008655 : Blo 2143435 11008655 := bstep (se 1 (by rfl) ⟨8256491, by rfl⟩ : syracuseStep 11008655 = 16512983) B16512983
theorem B7339103 : Blo 2143435 7339103 := bstep (se 1 (by rfl) ⟨5504327, by rfl⟩ : syracuseStep 7339103 = 11008655) B11008655
theorem B4892735 : Blo 2143435 4892735 := bstep (se 1 (by rfl) ⟨3669551, by rfl⟩ : syracuseStep 4892735 = 7339103) B7339103
theorem B3261823 : Blo 2143435 3261823 := bstep (se 1 (by rfl) ⟨2446367, by rfl⟩ : syracuseStep 3261823 = 4892735) B4892735
theorem B17396389 : Blo 2143435 17396389 := bstep (se 4 (by rfl) ⟨1630911, by rfl⟩ : syracuseStep 17396389 = 3261823) B3261823
theorem B92780741 : Blo 2143435 92780741 := bstep (se 4 (by rfl) ⟨8698194, by rfl⟩ : syracuseStep 92780741 = 17396389) B17396389
theorem B61853827 : Blo 2143435 61853827 := bstep (se 1 (by rfl) ⟨46390370, by rfl⟩ : syracuseStep 61853827 = 92780741) B92780741
theorem B82471769 : Blo 2143435 82471769 := bstep (se 2 (by rfl) ⟨30926913, by rfl⟩ : syracuseStep 82471769 = 61853827) B61853827
theorem B54981179 : Blo 2143435 54981179 := bstep (se 1 (by rfl) ⟨41235884, by rfl⟩ : syracuseStep 54981179 = 82471769) B82471769
theorem B36654119 : Blo 2143435 36654119 := bstep (se 1 (by rfl) ⟨27490589, by rfl⟩ : syracuseStep 36654119 = 54981179) B54981179
theorem B24436079 : Blo 2143435 24436079 := bstep (se 1 (by rfl) ⟨18327059, by rfl⟩ : syracuseStep 24436079 = 36654119) B36654119
theorem B16290719 : Blo 2143435 16290719 := bstep (se 1 (by rfl) ⟨12218039, by rfl⟩ : syracuseStep 16290719 = 24436079) B24436079
theorem B10860479 : Blo 2143435 10860479 := bstep (se 1 (by rfl) ⟨8145359, by rfl⟩ : syracuseStep 10860479 = 16290719) B16290719
theorem B7240319 : Blo 2143435 7240319 := bstep (se 1 (by rfl) ⟨5430239, by rfl⟩ : syracuseStep 7240319 = 10860479) B10860479
theorem B4826879 : Blo 2143435 4826879 := bstep (se 1 (by rfl) ⟨3620159, by rfl⟩ : syracuseStep 4826879 = 7240319) B7240319
theorem B3217919 : Blo 2143435 3217919 := bstep (se 1 (by rfl) ⟨2413439, by rfl⟩ : syracuseStep 3217919 = 4826879) B4826879
theorem B2145279 : Blo 2143435 2145279 := bstep (se 1 (by rfl) ⟨1608959, by rfl⟩ : syracuseStep 2145279 = 3217919) B3217919
theorem B3217925 : Blo 2143435 3217925 := bbase (se 4 (by rfl) ⟨301680, by rfl⟩ : syracuseStep 3217925 = 603361) (by norm_num)
theorem B2145283 : Blo 2143435 2145283 := bstep (se 1 (by rfl) ⟨1608962, by rfl⟩ : syracuseStep 2145283 = 3217925) B3217925
theorem B3620173 : Blo 2143435 3620173 := bbase (se 3 (by rfl) ⟨678782, by rfl⟩ : syracuseStep 3620173 = 1357565) (by norm_num)
theorem B4826897 : Blo 2143435 4826897 := bstep (se 2 (by rfl) ⟨1810086, by rfl⟩ : syracuseStep 4826897 = 3620173) B3620173
theorem B3217931 : Blo 2143435 3217931 := bstep (se 1 (by rfl) ⟨2413448, by rfl⟩ : syracuseStep 3217931 = 4826897) B4826897
theorem B2145287 : Blo 2143435 2145287 := bstep (se 1 (by rfl) ⟨1608965, by rfl⟩ : syracuseStep 2145287 = 3217931) B3217931
theorem B2413453 : Blo 2143435 2413453 := bbase (se 3 (by rfl) ⟨452522, by rfl⟩ : syracuseStep 2413453 = 905045) (by norm_num)
theorem B3217937 : Blo 2143435 3217937 := bstep (se 2 (by rfl) ⟨1206726, by rfl⟩ : syracuseStep 3217937 = 2413453) B2413453
theorem B2145291 : Blo 2143435 2145291 := bstep (se 1 (by rfl) ⟨1608968, by rfl⟩ : syracuseStep 2145291 = 3217937) B3217937
theorem B7240373 : Blo 2143435 7240373 := bbase (se 5 (by rfl) ⟨339392, by rfl⟩ : syracuseStep 7240373 = 678785) (by norm_num)
theorem B4826915 : Blo 2143435 4826915 := bstep (se 1 (by rfl) ⟨3620186, by rfl⟩ : syracuseStep 4826915 = 7240373) B7240373
theorem B3217943 : Blo 2143435 3217943 := bstep (se 1 (by rfl) ⟨2413457, by rfl⟩ : syracuseStep 3217943 = 4826915) B4826915
theorem B2145295 : Blo 2143435 2145295 := bstep (se 1 (by rfl) ⟨1608971, by rfl⟩ : syracuseStep 2145295 = 3217943) B3217943
theorem B3217949 : Blo 2143435 3217949 := bbase (se 3 (by rfl) ⟨603365, by rfl⟩ : syracuseStep 3217949 = 1206731) (by norm_num)
theorem B2145299 : Blo 2143435 2145299 := bstep (se 1 (by rfl) ⟨1608974, by rfl⟩ : syracuseStep 2145299 = 3217949) B3217949
theorem B4826933 : Blo 2143435 4826933 := bbase (se 5 (by rfl) ⟨226262, by rfl⟩ : syracuseStep 4826933 = 452525) (by norm_num)
theorem B3217955 : Blo 2143435 3217955 := bstep (se 1 (by rfl) ⟨2413466, by rfl⟩ : syracuseStep 3217955 = 4826933) B4826933
theorem B2145303 : Blo 2143435 2145303 := bstep (se 1 (by rfl) ⟨1608977, by rfl⟩ : syracuseStep 2145303 = 3217955) B3217955
theorem B2577277 : Blo 2143435 2577277 := bbase (se 3 (by rfl) ⟨483239, by rfl⟩ : syracuseStep 2577277 = 966479) (by norm_num)
theorem B13745477 : Blo 2143435 13745477 := bstep (se 4 (by rfl) ⟨1288638, by rfl⟩ : syracuseStep 13745477 = 2577277) B2577277
theorem B9163651 : Blo 2143435 9163651 := bstep (se 1 (by rfl) ⟨6872738, by rfl⟩ : syracuseStep 9163651 = 13745477) B13745477
theorem B12218201 : Blo 2143435 12218201 := bstep (se 2 (by rfl) ⟨4581825, by rfl⟩ : syracuseStep 12218201 = 9163651) B9163651
theorem B8145467 : Blo 2143435 8145467 := bstep (se 1 (by rfl) ⟨6109100, by rfl⟩ : syracuseStep 8145467 = 12218201) B12218201
theorem B5430311 : Blo 2143435 5430311 := bstep (se 1 (by rfl) ⟨4072733, by rfl⟩ : syracuseStep 5430311 = 8145467) B8145467
theorem B3620207 : Blo 2143435 3620207 := bstep (se 1 (by rfl) ⟨2715155, by rfl⟩ : syracuseStep 3620207 = 5430311) B5430311
theorem B2413471 : Blo 2143435 2413471 := bstep (se 1 (by rfl) ⟨1810103, by rfl⟩ : syracuseStep 2413471 = 3620207) B3620207
theorem B3217961 : Blo 2143435 3217961 := bstep (se 2 (by rfl) ⟨1206735, by rfl⟩ : syracuseStep 3217961 = 2413471) B2413471
theorem B2145307 : Blo 2143435 2145307 := bstep (se 1 (by rfl) ⟨1608980, by rfl⟩ : syracuseStep 2145307 = 3217961) B3217961
theorem B7731845 : Blo 2143435 7731845 := bbase (se 4 (by rfl) ⟨724860, by rfl⟩ : syracuseStep 7731845 = 1449721) (by norm_num)
theorem B5154563 : Blo 2143435 5154563 := bstep (se 1 (by rfl) ⟨3865922, by rfl⟩ : syracuseStep 5154563 = 7731845) B7731845
theorem B13745501 : Blo 2143435 13745501 := bstep (se 3 (by rfl) ⟨2577281, by rfl⟩ : syracuseStep 13745501 = 5154563) B5154563
theorem B9163667 : Blo 2143435 9163667 := bstep (se 1 (by rfl) ⟨6872750, by rfl⟩ : syracuseStep 9163667 = 13745501) B13745501
theorem B6109111 : Blo 2143435 6109111 := bstep (se 1 (by rfl) ⟨4581833, by rfl⟩ : syracuseStep 6109111 = 9163667) B9163667
theorem B8145481 : Blo 2143435 8145481 := bstep (se 2 (by rfl) ⟨3054555, by rfl⟩ : syracuseStep 8145481 = 6109111) B6109111
theorem B10860641 : Blo 2143435 10860641 := bstep (se 2 (by rfl) ⟨4072740, by rfl⟩ : syracuseStep 10860641 = 8145481) B8145481
theorem B7240427 : Blo 2143435 7240427 := bstep (se 1 (by rfl) ⟨5430320, by rfl⟩ : syracuseStep 7240427 = 10860641) B10860641
theorem B4826951 : Blo 2143435 4826951 := bstep (se 1 (by rfl) ⟨3620213, by rfl⟩ : syracuseStep 4826951 = 7240427) B7240427
theorem B3217967 : Blo 2143435 3217967 := bstep (se 1 (by rfl) ⟨2413475, by rfl⟩ : syracuseStep 3217967 = 4826951) B4826951
theorem B2145311 : Blo 2143435 2145311 := bstep (se 1 (by rfl) ⟨1608983, by rfl⟩ : syracuseStep 2145311 = 3217967) B3217967
theorem B3217973 : Blo 2143435 3217973 := bbase (se 5 (by rfl) ⟨150842, by rfl⟩ : syracuseStep 3217973 = 301685) (by norm_num)
theorem B2145315 : Blo 2143435 2145315 := bstep (se 1 (by rfl) ⟨1608986, by rfl⟩ : syracuseStep 2145315 = 3217973) B3217973
theorem B5430341 : Blo 2143435 5430341 := bbase (se 4 (by rfl) ⟨509094, by rfl⟩ : syracuseStep 5430341 = 1018189) (by norm_num)
theorem B3620227 : Blo 2143435 3620227 := bstep (se 1 (by rfl) ⟨2715170, by rfl⟩ : syracuseStep 3620227 = 5430341) B5430341
theorem B4826969 : Blo 2143435 4826969 := bstep (se 2 (by rfl) ⟨1810113, by rfl⟩ : syracuseStep 4826969 = 3620227) B3620227
theorem B3217979 : Blo 2143435 3217979 := bstep (se 1 (by rfl) ⟨2413484, by rfl⟩ : syracuseStep 3217979 = 4826969) B4826969
theorem B2145319 : Blo 2143435 2145319 := bstep (se 1 (by rfl) ⟨1608989, by rfl⟩ : syracuseStep 2145319 = 3217979) B3217979
theorem B2413489 : Blo 2143435 2413489 := bbase (se 2 (by rfl) ⟨905058, by rfl⟩ : syracuseStep 2413489 = 1810117) (by norm_num)
theorem B3217985 : Blo 2143435 3217985 := bstep (se 2 (by rfl) ⟨1206744, by rfl⟩ : syracuseStep 3217985 = 2413489) B2413489
theorem B2145323 : Blo 2143435 2145323 := bstep (se 1 (by rfl) ⟨1608992, by rfl⟩ : syracuseStep 2145323 = 3217985) B3217985
theorem B6109157 : Blo 2143435 6109157 := bbase (se 4 (by rfl) ⟨572733, by rfl⟩ : syracuseStep 6109157 = 1145467) (by norm_num)
theorem B4072771 : Blo 2143435 4072771 := bstep (se 1 (by rfl) ⟨3054578, by rfl⟩ : syracuseStep 4072771 = 6109157) B6109157
theorem B5430361 : Blo 2143435 5430361 := bstep (se 2 (by rfl) ⟨2036385, by rfl⟩ : syracuseStep 5430361 = 4072771) B4072771
theorem B7240481 : Blo 2143435 7240481 := bstep (se 2 (by rfl) ⟨2715180, by rfl⟩ : syracuseStep 7240481 = 5430361) B5430361
theorem B4826987 : Blo 2143435 4826987 := bstep (se 1 (by rfl) ⟨3620240, by rfl⟩ : syracuseStep 4826987 = 7240481) B7240481
theorem B3217991 : Blo 2143435 3217991 := bstep (se 1 (by rfl) ⟨2413493, by rfl⟩ : syracuseStep 3217991 = 4826987) B4826987
theorem B2145327 : Blo 2143435 2145327 := bstep (se 1 (by rfl) ⟨1608995, by rfl⟩ : syracuseStep 2145327 = 3217991) B3217991
theorem B3217997 : Blo 2143435 3217997 := bbase (se 3 (by rfl) ⟨603374, by rfl⟩ : syracuseStep 3217997 = 1206749) (by norm_num)
theorem B2145331 : Blo 2143435 2145331 := bstep (se 1 (by rfl) ⟨1608998, by rfl⟩ : syracuseStep 2145331 = 3217997) B3217997
theorem B4827005 : Blo 2143435 4827005 := bbase (se 3 (by rfl) ⟨905063, by rfl⟩ : syracuseStep 4827005 = 1810127) (by norm_num)
theorem B3218003 : Blo 2143435 3218003 := bstep (se 1 (by rfl) ⟨2413502, by rfl⟩ : syracuseStep 3218003 = 4827005) B4827005
theorem B2145335 : Blo 2143435 2145335 := bstep (se 1 (by rfl) ⟨1609001, by rfl⟩ : syracuseStep 2145335 = 3218003) B3218003
theorem B3620261 : Blo 2143435 3620261 := bbase (se 4 (by rfl) ⟨339399, by rfl⟩ : syracuseStep 3620261 = 678799) (by norm_num)
theorem B2413507 : Blo 2143435 2413507 := bstep (se 1 (by rfl) ⟨1810130, by rfl⟩ : syracuseStep 2413507 = 3620261) B3620261
theorem B3218009 : Blo 2143435 3218009 := bstep (se 2 (by rfl) ⟨1206753, by rfl⟩ : syracuseStep 3218009 = 2413507) B2413507
theorem B2145339 : Blo 2143435 2145339 := bstep (se 1 (by rfl) ⟨1609004, by rfl⟩ : syracuseStep 2145339 = 3218009) B3218009
theorem B3865981 : Blo 2143435 3865981 := bbase (se 3 (by rfl) ⟨724871, by rfl⟩ : syracuseStep 3865981 = 1449743) (by norm_num)
theorem B5154641 : Blo 2143435 5154641 := bstep (se 2 (by rfl) ⟨1932990, by rfl⟩ : syracuseStep 5154641 = 3865981) B3865981
theorem B3436427 : Blo 2143435 3436427 := bstep (se 1 (by rfl) ⟨2577320, by rfl⟩ : syracuseStep 3436427 = 5154641) B5154641
theorem B2290951 : Blo 2143435 2290951 := bstep (se 1 (by rfl) ⟨1718213, by rfl⟩ : syracuseStep 2290951 = 3436427) B3436427
theorem B3054601 : Blo 2143435 3054601 := bstep (se 2 (by rfl) ⟨1145475, by rfl⟩ : syracuseStep 3054601 = 2290951) B2290951
theorem B16291205 : Blo 2143435 16291205 := bstep (se 4 (by rfl) ⟨1527300, by rfl⟩ : syracuseStep 16291205 = 3054601) B3054601
theorem B10860803 : Blo 2143435 10860803 := bstep (se 1 (by rfl) ⟨8145602, by rfl⟩ : syracuseStep 10860803 = 16291205) B16291205
theorem B7240535 : Blo 2143435 7240535 := bstep (se 1 (by rfl) ⟨5430401, by rfl⟩ : syracuseStep 7240535 = 10860803) B10860803
theorem B4827023 : Blo 2143435 4827023 := bstep (se 1 (by rfl) ⟨3620267, by rfl⟩ : syracuseStep 4827023 = 7240535) B7240535
theorem B3218015 : Blo 2143435 3218015 := bstep (se 1 (by rfl) ⟨2413511, by rfl⟩ : syracuseStep 3218015 = 4827023) B4827023
theorem B2145343 : Blo 2143435 2145343 := bstep (se 1 (by rfl) ⟨1609007, by rfl⟩ : syracuseStep 2145343 = 3218015) B3218015
theorem B3218021 : Blo 2143435 3218021 := bbase (se 4 (by rfl) ⟨301689, by rfl⟩ : syracuseStep 3218021 = 603379) (by norm_num)
theorem B2145347 : Blo 2143435 2145347 := bstep (se 1 (by rfl) ⟨1609010, by rfl⟩ : syracuseStep 2145347 = 3218021) B3218021
theorem B3054613 : Blo 2143435 3054613 := bbase (se 6 (by rfl) ⟨71592, by rfl⟩ : syracuseStep 3054613 = 143185) (by norm_num)
theorem B4072817 : Blo 2143435 4072817 := bstep (se 2 (by rfl) ⟨1527306, by rfl⟩ : syracuseStep 4072817 = 3054613) B3054613
theorem B2715211 : Blo 2143435 2715211 := bstep (se 1 (by rfl) ⟨2036408, by rfl⟩ : syracuseStep 2715211 = 4072817) B4072817
theorem B3620281 : Blo 2143435 3620281 := bstep (se 2 (by rfl) ⟨1357605, by rfl⟩ : syracuseStep 3620281 = 2715211) B2715211
theorem B4827041 : Blo 2143435 4827041 := bstep (se 2 (by rfl) ⟨1810140, by rfl⟩ : syracuseStep 4827041 = 3620281) B3620281
theorem B3218027 : Blo 2143435 3218027 := bstep (se 1 (by rfl) ⟨2413520, by rfl⟩ : syracuseStep 3218027 = 4827041) B4827041
theorem B2145351 : Blo 2143435 2145351 := bstep (se 1 (by rfl) ⟨1609013, by rfl⟩ : syracuseStep 2145351 = 3218027) B3218027
theorem B2413525 : Blo 2143435 2413525 := bbase (se 7 (by rfl) ⟨28283, by rfl⟩ : syracuseStep 2413525 = 56567) (by norm_num)
theorem B3218033 : Blo 2143435 3218033 := bstep (se 2 (by rfl) ⟨1206762, by rfl⟩ : syracuseStep 3218033 = 2413525) B2413525
theorem B2145355 : Blo 2143435 2145355 := bstep (se 1 (by rfl) ⟨1609016, by rfl⟩ : syracuseStep 2145355 = 3218033) B3218033
theorem B2715221 : Blo 2143435 2715221 := bbase (se 8 (by rfl) ⟨15909, by rfl⟩ : syracuseStep 2715221 = 31819) (by norm_num)
theorem B7240589 : Blo 2143435 7240589 := bstep (se 3 (by rfl) ⟨1357610, by rfl⟩ : syracuseStep 7240589 = 2715221) B2715221
theorem B4827059 : Blo 2143435 4827059 := bstep (se 1 (by rfl) ⟨3620294, by rfl⟩ : syracuseStep 4827059 = 7240589) B7240589
theorem B3218039 : Blo 2143435 3218039 := bstep (se 1 (by rfl) ⟨2413529, by rfl⟩ : syracuseStep 3218039 = 4827059) B4827059
theorem B2145359 : Blo 2143435 2145359 := bstep (se 1 (by rfl) ⟨1609019, by rfl⟩ : syracuseStep 2145359 = 3218039) B3218039
theorem B3218045 : Blo 2143435 3218045 := bbase (se 3 (by rfl) ⟨603383, by rfl⟩ : syracuseStep 3218045 = 1206767) (by norm_num)
theorem B2145363 : Blo 2143435 2145363 := bstep (se 1 (by rfl) ⟨1609022, by rfl⟩ : syracuseStep 2145363 = 3218045) B3218045
theorem B4827077 : Blo 2143435 4827077 := bbase (se 4 (by rfl) ⟨452538, by rfl⟩ : syracuseStep 4827077 = 905077) (by norm_num)
theorem B3218051 : Blo 2143435 3218051 := bstep (se 1 (by rfl) ⟨2413538, by rfl⟩ : syracuseStep 3218051 = 4827077) B4827077
theorem B2145367 : Blo 2143435 2145367 := bstep (se 1 (by rfl) ⟨1609025, by rfl⟩ : syracuseStep 2145367 = 3218051) B3218051
theorem B9163925 : Blo 2143435 9163925 := bbase (se 6 (by rfl) ⟨214779, by rfl⟩ : syracuseStep 9163925 = 429559) (by norm_num)
theorem B6109283 : Blo 2143435 6109283 := bstep (se 1 (by rfl) ⟨4581962, by rfl⟩ : syracuseStep 6109283 = 9163925) B9163925
theorem B4072855 : Blo 2143435 4072855 := bstep (se 1 (by rfl) ⟨3054641, by rfl⟩ : syracuseStep 4072855 = 6109283) B6109283
theorem B5430473 : Blo 2143435 5430473 := bstep (se 2 (by rfl) ⟨2036427, by rfl⟩ : syracuseStep 5430473 = 4072855) B4072855
theorem B3620315 : Blo 2143435 3620315 := bstep (se 1 (by rfl) ⟨2715236, by rfl⟩ : syracuseStep 3620315 = 5430473) B5430473
theorem B2413543 : Blo 2143435 2413543 := bstep (se 1 (by rfl) ⟨1810157, by rfl⟩ : syracuseStep 2413543 = 3620315) B3620315
theorem B3218057 : Blo 2143435 3218057 := bstep (se 2 (by rfl) ⟨1206771, by rfl⟩ : syracuseStep 3218057 = 2413543) B2413543
theorem B2145371 : Blo 2143435 2145371 := bstep (se 1 (by rfl) ⟨1609028, by rfl⟩ : syracuseStep 2145371 = 3218057) B3218057
theorem B10860965 : Blo 2143435 10860965 := bbase (se 4 (by rfl) ⟨1018215, by rfl⟩ : syracuseStep 10860965 = 2036431) (by norm_num)
theorem B7240643 : Blo 2143435 7240643 := bstep (se 1 (by rfl) ⟨5430482, by rfl⟩ : syracuseStep 7240643 = 10860965) B10860965
theorem B4827095 : Blo 2143435 4827095 := bstep (se 1 (by rfl) ⟨3620321, by rfl⟩ : syracuseStep 4827095 = 7240643) B7240643
theorem B3218063 : Blo 2143435 3218063 := bstep (se 1 (by rfl) ⟨2413547, by rfl⟩ : syracuseStep 3218063 = 4827095) B4827095
theorem B2145375 : Blo 2143435 2145375 := bstep (se 1 (by rfl) ⟨1609031, by rfl⟩ : syracuseStep 2145375 = 3218063) B3218063
theorem B3218069 : Blo 2143435 3218069 := bbase (se 6 (by rfl) ⟨75423, by rfl⟩ : syracuseStep 3218069 = 150847) (by norm_num)
theorem B2145379 : Blo 2143435 2145379 := bstep (se 1 (by rfl) ⟨1609034, by rfl⟩ : syracuseStep 2145379 = 3218069) B3218069
theorem B4349309 : Blo 2143435 4349309 := bbase (se 3 (by rfl) ⟨815495, by rfl⟩ : syracuseStep 4349309 = 1630991) (by norm_num)
theorem B11598157 : Blo 2143435 11598157 := bstep (se 3 (by rfl) ⟨2174654, by rfl⟩ : syracuseStep 11598157 = 4349309) B4349309
theorem B15464209 : Blo 2143435 15464209 := bstep (se 2 (by rfl) ⟨5799078, by rfl⟩ : syracuseStep 15464209 = 11598157) B11598157
theorem B20618945 : Blo 2143435 20618945 := bstep (se 2 (by rfl) ⟨7732104, by rfl⟩ : syracuseStep 20618945 = 15464209) B15464209
theorem B13745963 : Blo 2143435 13745963 := bstep (se 1 (by rfl) ⟨10309472, by rfl⟩ : syracuseStep 13745963 = 20618945) B20618945
theorem B9163975 : Blo 2143435 9163975 := bstep (se 1 (by rfl) ⟨6872981, by rfl⟩ : syracuseStep 9163975 = 13745963) B13745963
theorem B12218633 : Blo 2143435 12218633 := bstep (se 2 (by rfl) ⟨4581987, by rfl⟩ : syracuseStep 12218633 = 9163975) B9163975
theorem B8145755 : Blo 2143435 8145755 := bstep (se 1 (by rfl) ⟨6109316, by rfl⟩ : syracuseStep 8145755 = 12218633) B12218633
theorem B5430503 : Blo 2143435 5430503 := bstep (se 1 (by rfl) ⟨4072877, by rfl⟩ : syracuseStep 5430503 = 8145755) B8145755
theorem B3620335 : Blo 2143435 3620335 := bstep (se 1 (by rfl) ⟨2715251, by rfl⟩ : syracuseStep 3620335 = 5430503) B5430503
theorem B4827113 : Blo 2143435 4827113 := bstep (se 2 (by rfl) ⟨1810167, by rfl⟩ : syracuseStep 4827113 = 3620335) B3620335
theorem B3218075 : Blo 2143435 3218075 := bstep (se 1 (by rfl) ⟨2413556, by rfl⟩ : syracuseStep 3218075 = 4827113) B4827113
theorem B2145383 : Blo 2143435 2145383 := bstep (se 1 (by rfl) ⟨1609037, by rfl⟩ : syracuseStep 2145383 = 3218075) B3218075
theorem B2413561 : Blo 2143435 2413561 := bbase (se 2 (by rfl) ⟨905085, by rfl⟩ : syracuseStep 2413561 = 1810171) (by norm_num)
theorem B3218081 : Blo 2143435 3218081 := bstep (se 2 (by rfl) ⟨1206780, by rfl⟩ : syracuseStep 3218081 = 2413561) B2413561
theorem B2145387 : Blo 2143435 2145387 := bstep (se 1 (by rfl) ⟨1609040, by rfl⟩ : syracuseStep 2145387 = 3218081) B3218081
theorem B17397301 : Blo 2143435 17397301 := bbase (se 5 (by rfl) ⟨815498, by rfl⟩ : syracuseStep 17397301 = 1630997) (by norm_num)
theorem B23196401 : Blo 2143435 23196401 := bstep (se 2 (by rfl) ⟨8698650, by rfl⟩ : syracuseStep 23196401 = 17397301) B17397301
theorem B15464267 : Blo 2143435 15464267 := bstep (se 1 (by rfl) ⟨11598200, by rfl⟩ : syracuseStep 15464267 = 23196401) B23196401
theorem B10309511 : Blo 2143435 10309511 := bstep (se 1 (by rfl) ⟨7732133, by rfl⟩ : syracuseStep 10309511 = 15464267) B15464267
theorem B6873007 : Blo 2143435 6873007 := bstep (se 1 (by rfl) ⟨5154755, by rfl⟩ : syracuseStep 6873007 = 10309511) B10309511
theorem B9164009 : Blo 2143435 9164009 := bstep (se 2 (by rfl) ⟨3436503, by rfl⟩ : syracuseStep 9164009 = 6873007) B6873007
theorem B6109339 : Blo 2143435 6109339 := bstep (se 1 (by rfl) ⟨4582004, by rfl⟩ : syracuseStep 6109339 = 9164009) B9164009
theorem B8145785 : Blo 2143435 8145785 := bstep (se 2 (by rfl) ⟨3054669, by rfl⟩ : syracuseStep 8145785 = 6109339) B6109339
theorem B5430523 : Blo 2143435 5430523 := bstep (se 1 (by rfl) ⟨4072892, by rfl⟩ : syracuseStep 5430523 = 8145785) B8145785
theorem B7240697 : Blo 2143435 7240697 := bstep (se 2 (by rfl) ⟨2715261, by rfl⟩ : syracuseStep 7240697 = 5430523) B5430523
theorem B4827131 : Blo 2143435 4827131 := bstep (se 1 (by rfl) ⟨3620348, by rfl⟩ : syracuseStep 4827131 = 7240697) B7240697
theorem B3218087 : Blo 2143435 3218087 := bstep (se 1 (by rfl) ⟨2413565, by rfl⟩ : syracuseStep 3218087 = 4827131) B4827131
theorem B2145391 : Blo 2143435 2145391 := bstep (se 1 (by rfl) ⟨1609043, by rfl⟩ : syracuseStep 2145391 = 3218087) B3218087
theorem B3218093 : Blo 2143435 3218093 := bbase (se 3 (by rfl) ⟨603392, by rfl⟩ : syracuseStep 3218093 = 1206785) (by norm_num)
theorem B2145395 : Blo 2143435 2145395 := bstep (se 1 (by rfl) ⟨1609046, by rfl⟩ : syracuseStep 2145395 = 3218093) B3218093
theorem B4827149 : Blo 2143435 4827149 := bbase (se 3 (by rfl) ⟨905090, by rfl⟩ : syracuseStep 4827149 = 1810181) (by norm_num)
theorem B3218099 : Blo 2143435 3218099 := bstep (se 1 (by rfl) ⟨2413574, by rfl⟩ : syracuseStep 3218099 = 4827149) B4827149
theorem B2145399 : Blo 2143435 2145399 := bstep (se 1 (by rfl) ⟨1609049, by rfl⟩ : syracuseStep 2145399 = 3218099) B3218099
theorem B2715277 : Blo 2143435 2715277 := bbase (se 3 (by rfl) ⟨509114, by rfl⟩ : syracuseStep 2715277 = 1018229) (by norm_num)
theorem B3620369 : Blo 2143435 3620369 := bstep (se 2 (by rfl) ⟨1357638, by rfl⟩ : syracuseStep 3620369 = 2715277) B2715277
theorem B2413579 : Blo 2143435 2413579 := bstep (se 1 (by rfl) ⟨1810184, by rfl⟩ : syracuseStep 2413579 = 3620369) B3620369
theorem B3218105 : Blo 2143435 3218105 := bstep (se 2 (by rfl) ⟨1206789, by rfl⟩ : syracuseStep 3218105 = 2413579) B2413579
theorem B2145403 : Blo 2143435 2145403 := bstep (se 1 (by rfl) ⟨1609052, by rfl⟩ : syracuseStep 2145403 = 3218105) B3218105
theorem B2322277 : Blo 2143435 2322277 := bbase (se 4 (by rfl) ⟨217713, by rfl⟩ : syracuseStep 2322277 = 435427) (by norm_num)
theorem B12385477 : Blo 2143435 12385477 := bstep (se 4 (by rfl) ⟨1161138, by rfl⟩ : syracuseStep 12385477 = 2322277) B2322277
theorem B16513969 : Blo 2143435 16513969 := bstep (se 2 (by rfl) ⟨6192738, by rfl⟩ : syracuseStep 16513969 = 12385477) B12385477
theorem B22018625 : Blo 2143435 22018625 := bstep (se 2 (by rfl) ⟨8256984, by rfl⟩ : syracuseStep 22018625 = 16513969) B16513969
theorem B14679083 : Blo 2143435 14679083 := bstep (se 1 (by rfl) ⟨11009312, by rfl⟩ : syracuseStep 14679083 = 22018625) B22018625
theorem B9786055 : Blo 2143435 9786055 := bstep (se 1 (by rfl) ⟨7339541, by rfl⟩ : syracuseStep 9786055 = 14679083) B14679083
theorem B13048073 : Blo 2143435 13048073 := bstep (se 2 (by rfl) ⟨4893027, by rfl⟩ : syracuseStep 13048073 = 9786055) B9786055
theorem B8698715 : Blo 2143435 8698715 := bstep (se 1 (by rfl) ⟨6524036, by rfl⟩ : syracuseStep 8698715 = 13048073) B13048073
theorem B5799143 : Blo 2143435 5799143 := bstep (se 1 (by rfl) ⟨4349357, by rfl⟩ : syracuseStep 5799143 = 8698715) B8698715
theorem B3866095 : Blo 2143435 3866095 := bstep (se 1 (by rfl) ⟨2899571, by rfl⟩ : syracuseStep 3866095 = 5799143) B5799143
theorem B20619173 : Blo 2143435 20619173 := bstep (se 4 (by rfl) ⟨1933047, by rfl⟩ : syracuseStep 20619173 = 3866095) B3866095
theorem B13746115 : Blo 2143435 13746115 := bstep (se 1 (by rfl) ⟨10309586, by rfl⟩ : syracuseStep 13746115 = 20619173) B20619173
theorem B18328153 : Blo 2143435 18328153 := bstep (se 2 (by rfl) ⟨6873057, by rfl⟩ : syracuseStep 18328153 = 13746115) B13746115
theorem B24437537 : Blo 2143435 24437537 := bstep (se 2 (by rfl) ⟨9164076, by rfl⟩ : syracuseStep 24437537 = 18328153) B18328153
theorem B16291691 : Blo 2143435 16291691 := bstep (se 1 (by rfl) ⟨12218768, by rfl⟩ : syracuseStep 16291691 = 24437537) B24437537
theorem B10861127 : Blo 2143435 10861127 := bstep (se 1 (by rfl) ⟨8145845, by rfl⟩ : syracuseStep 10861127 = 16291691) B16291691
theorem B7240751 : Blo 2143435 7240751 := bstep (se 1 (by rfl) ⟨5430563, by rfl⟩ : syracuseStep 7240751 = 10861127) B10861127
theorem B4827167 : Blo 2143435 4827167 := bstep (se 1 (by rfl) ⟨3620375, by rfl⟩ : syracuseStep 4827167 = 7240751) B7240751
theorem B3218111 : Blo 2143435 3218111 := bstep (se 1 (by rfl) ⟨2413583, by rfl⟩ : syracuseStep 3218111 = 4827167) B4827167
theorem B2145407 : Blo 2143435 2145407 := bstep (se 1 (by rfl) ⟨1609055, by rfl⟩ : syracuseStep 2145407 = 3218111) B3218111
theorem B3218117 : Blo 2143435 3218117 := bbase (se 4 (by rfl) ⟨301698, by rfl⟩ : syracuseStep 3218117 = 603397) (by norm_num)
theorem B2145411 : Blo 2143435 2145411 := bstep (se 1 (by rfl) ⟨1609058, by rfl⟩ : syracuseStep 2145411 = 3218117) B3218117
theorem B3620389 : Blo 2143435 3620389 := bbase (se 4 (by rfl) ⟨339411, by rfl⟩ : syracuseStep 3620389 = 678823) (by norm_num)
theorem B4827185 : Blo 2143435 4827185 := bstep (se 2 (by rfl) ⟨1810194, by rfl⟩ : syracuseStep 4827185 = 3620389) B3620389
theorem B3218123 : Blo 2143435 3218123 := bstep (se 1 (by rfl) ⟨2413592, by rfl⟩ : syracuseStep 3218123 = 4827185) B4827185
theorem B2145415 : Blo 2143435 2145415 := bstep (se 1 (by rfl) ⟨1609061, by rfl⟩ : syracuseStep 2145415 = 3218123) B3218123
theorem B2413597 : Blo 2143435 2413597 := bbase (se 3 (by rfl) ⟨452549, by rfl⟩ : syracuseStep 2413597 = 905099) (by norm_num)
theorem B3218129 : Blo 2143435 3218129 := bstep (se 2 (by rfl) ⟨1206798, by rfl⟩ : syracuseStep 3218129 = 2413597) B2413597
theorem B2145419 : Blo 2143435 2145419 := bstep (se 1 (by rfl) ⟨1609064, by rfl⟩ : syracuseStep 2145419 = 3218129) B3218129
theorem B7240805 : Blo 2143435 7240805 := bbase (se 4 (by rfl) ⟨678825, by rfl⟩ : syracuseStep 7240805 = 1357651) (by norm_num)
theorem B4827203 : Blo 2143435 4827203 := bstep (se 1 (by rfl) ⟨3620402, by rfl⟩ : syracuseStep 4827203 = 7240805) B7240805
theorem B3218135 : Blo 2143435 3218135 := bstep (se 1 (by rfl) ⟨2413601, by rfl⟩ : syracuseStep 3218135 = 4827203) B4827203
theorem B2145423 : Blo 2143435 2145423 := bstep (se 1 (by rfl) ⟨1609067, by rfl⟩ : syracuseStep 2145423 = 3218135) B3218135
theorem B3218141 : Blo 2143435 3218141 := bbase (se 3 (by rfl) ⟨603401, by rfl⟩ : syracuseStep 3218141 = 1206803) (by norm_num)
theorem B2145427 : Blo 2143435 2145427 := bstep (se 1 (by rfl) ⟨1609070, by rfl⟩ : syracuseStep 2145427 = 3218141) B3218141
theorem B4827221 : Blo 2143435 4827221 := bbase (se 8 (by rfl) ⟨28284, by rfl⟩ : syracuseStep 4827221 = 56569) (by norm_num)
theorem B3218147 : Blo 2143435 3218147 := bstep (se 1 (by rfl) ⟨2413610, by rfl⟩ : syracuseStep 3218147 = 4827221) B4827221
theorem B2145431 : Blo 2143435 2145431 := bstep (se 1 (by rfl) ⟨1609073, by rfl⟩ : syracuseStep 2145431 = 3218147) B3218147
theorem B5799221 : Blo 2143435 5799221 := bbase (se 5 (by rfl) ⟨271838, by rfl⟩ : syracuseStep 5799221 = 543677) (by norm_num)
theorem B3866147 : Blo 2143435 3866147 := bstep (se 1 (by rfl) ⟨2899610, by rfl⟩ : syracuseStep 3866147 = 5799221) B5799221
theorem B2577431 : Blo 2143435 2577431 := bstep (se 1 (by rfl) ⟨1933073, by rfl⟩ : syracuseStep 2577431 = 3866147) B3866147
theorem B6873149 : Blo 2143435 6873149 := bstep (se 3 (by rfl) ⟨1288715, by rfl⟩ : syracuseStep 6873149 = 2577431) B2577431
theorem B4582099 : Blo 2143435 4582099 := bstep (se 1 (by rfl) ⟨3436574, by rfl⟩ : syracuseStep 4582099 = 6873149) B6873149
theorem B6109465 : Blo 2143435 6109465 := bstep (se 2 (by rfl) ⟨2291049, by rfl⟩ : syracuseStep 6109465 = 4582099) B4582099
theorem B8145953 : Blo 2143435 8145953 := bstep (se 2 (by rfl) ⟨3054732, by rfl⟩ : syracuseStep 8145953 = 6109465) B6109465
theorem B5430635 : Blo 2143435 5430635 := bstep (se 1 (by rfl) ⟨4072976, by rfl⟩ : syracuseStep 5430635 = 8145953) B8145953
theorem B3620423 : Blo 2143435 3620423 := bstep (se 1 (by rfl) ⟨2715317, by rfl⟩ : syracuseStep 3620423 = 5430635) B5430635
theorem B2413615 : Blo 2143435 2413615 := bstep (se 1 (by rfl) ⟨1810211, by rfl⟩ : syracuseStep 2413615 = 3620423) B3620423
theorem B3218153 : Blo 2143435 3218153 := bstep (se 2 (by rfl) ⟨1206807, by rfl⟩ : syracuseStep 3218153 = 2413615) B2413615
theorem B2145435 : Blo 2143435 2145435 := bstep (se 1 (by rfl) ⟨1609076, by rfl⟩ : syracuseStep 2145435 = 3218153) B3218153
theorem C0 (j : ℕ) (h1 : 535858 ≤ j) (h2 : j ≤ 536358) : Blo 2143435 (4 * j + 3) := by
  interval_cases j
  · exact B2143435
  · exact B2143439
  · exact B2143443
  · exact B2143447
  · exact B2143451
  · exact B2143455
  · exact B2143459
  · exact B2143463
  · exact B2143467
  · exact B2143471
  · exact B2143475
  · exact B2143479
  · exact B2143483
  · exact B2143487
  · exact B2143491
  · exact B2143495
  · exact B2143499
  · exact B2143503
  · exact B2143507
  · exact B2143511
  · exact B2143515
  · exact B2143519
  · exact B2143523
  · exact B2143527
  · exact B2143531
  · exact B2143535
  · exact B2143539
  · exact B2143543
  · exact B2143547
  · exact B2143551
  · exact B2143555
  · exact B2143559
  · exact B2143563
  · exact B2143567
  · exact B2143571
  · exact B2143575
  · exact B2143579
  · exact B2143583
  · exact B2143587
  · exact B2143591
  · exact B2143595
  · exact B2143599
  · exact B2143603
  · exact B2143607
  · exact B2143611
  · exact B2143615
  · exact B2143619
  · exact B2143623
  · exact B2143627
  · exact B2143631
  · exact B2143635
  · exact B2143639
  · exact B2143643
  · exact B2143647
  · exact B2143651
  · exact B2143655
  · exact B2143659
  · exact B2143663
  · exact B2143667
  · exact B2143671
  · exact B2143675
  · exact B2143679
  · exact B2143683
  · exact B2143687
  · exact B2143691
  · exact B2143695
  · exact B2143699
  · exact B2143703
  · exact B2143707
  · exact B2143711
  · exact B2143715
  · exact B2143719
  · exact B2143723
  · exact B2143727
  · exact B2143731
  · exact B2143735
  · exact B2143739
  · exact B2143743
  · exact B2143747
  · exact B2143751
  · exact B2143755
  · exact B2143759
  · exact B2143763
  · exact B2143767
  · exact B2143771
  · exact B2143775
  · exact B2143779
  · exact B2143783
  · exact B2143787
  · exact B2143791
  · exact B2143795
  · exact B2143799
  · exact B2143803
  · exact B2143807
  · exact B2143811
  · exact B2143815
  · exact B2143819
  · exact B2143823
  · exact B2143827
  · exact B2143831
  · exact B2143835
  · exact B2143839
  · exact B2143843
  · exact B2143847
  · exact B2143851
  · exact B2143855
  · exact B2143859
  · exact B2143863
  · exact B2143867
  · exact B2143871
  · exact B2143875
  · exact B2143879
  · exact B2143883
  · exact B2143887
  · exact B2143891
  · exact B2143895
  · exact B2143899
  · exact B2143903
  · exact B2143907
  · exact B2143911
  · exact B2143915
  · exact B2143919
  · exact B2143923
  · exact B2143927
  · exact B2143931
  · exact B2143935
  · exact B2143939
  · exact B2143943
  · exact B2143947
  · exact B2143951
  · exact B2143955
  · exact B2143959
  · exact B2143963
  · exact B2143967
  · exact B2143971
  · exact B2143975
  · exact B2143979
  · exact B2143983
  · exact B2143987
  · exact B2143991
  · exact B2143995
  · exact B2143999
  · exact B2144003
  · exact B2144007
  · exact B2144011
  · exact B2144015
  · exact B2144019
  · exact B2144023
  · exact B2144027
  · exact B2144031
  · exact B2144035
  · exact B2144039
  · exact B2144043
  · exact B2144047
  · exact B2144051
  · exact B2144055
  · exact B2144059
  · exact B2144063
  · exact B2144067
  · exact B2144071
  · exact B2144075
  · exact B2144079
  · exact B2144083
  · exact B2144087
  · exact B2144091
  · exact B2144095
  · exact B2144099
  · exact B2144103
  · exact B2144107
  · exact B2144111
  · exact B2144115
  · exact B2144119
  · exact B2144123
  · exact B2144127
  · exact B2144131
  · exact B2144135
  · exact B2144139
  · exact B2144143
  · exact B2144147
  · exact B2144151
  · exact B2144155
  · exact B2144159
  · exact B2144163
  · exact B2144167
  · exact B2144171
  · exact B2144175
  · exact B2144179
  · exact B2144183
  · exact B2144187
  · exact B2144191
  · exact B2144195
  · exact B2144199
  · exact B2144203
  · exact B2144207
  · exact B2144211
  · exact B2144215
  · exact B2144219
  · exact B2144223
  · exact B2144227
  · exact B2144231
  · exact B2144235
  · exact B2144239
  · exact B2144243
  · exact B2144247
  · exact B2144251
  · exact B2144255
  · exact B2144259
  · exact B2144263
  · exact B2144267
  · exact B2144271
  · exact B2144275
  · exact B2144279
  · exact B2144283
  · exact B2144287
  · exact B2144291
  · exact B2144295
  · exact B2144299
  · exact B2144303
  · exact B2144307
  · exact B2144311
  · exact B2144315
  · exact B2144319
  · exact B2144323
  · exact B2144327
  · exact B2144331
  · exact B2144335
  · exact B2144339
  · exact B2144343
  · exact B2144347
  · exact B2144351
  · exact B2144355
  · exact B2144359
  · exact B2144363
  · exact B2144367
  · exact B2144371
  · exact B2144375
  · exact B2144379
  · exact B2144383
  · exact B2144387
  · exact B2144391
  · exact B2144395
  · exact B2144399
  · exact B2144403
  · exact B2144407
  · exact B2144411
  · exact B2144415
  · exact B2144419
  · exact B2144423
  · exact B2144427
  · exact B2144431
  · exact B2144435
  · exact B2144439
  · exact B2144443
  · exact B2144447
  · exact B2144451
  · exact B2144455
  · exact B2144459
  · exact B2144463
  · exact B2144467
  · exact B2144471
  · exact B2144475
  · exact B2144479
  · exact B2144483
  · exact B2144487
  · exact B2144491
  · exact B2144495
  · exact B2144499
  · exact B2144503
  · exact B2144507
  · exact B2144511
  · exact B2144515
  · exact B2144519
  · exact B2144523
  · exact B2144527
  · exact B2144531
  · exact B2144535
  · exact B2144539
  · exact B2144543
  · exact B2144547
  · exact B2144551
  · exact B2144555
  · exact B2144559
  · exact B2144563
  · exact B2144567
  · exact B2144571
  · exact B2144575
  · exact B2144579
  · exact B2144583
  · exact B2144587
  · exact B2144591
  · exact B2144595
  · exact B2144599
  · exact B2144603
  · exact B2144607
  · exact B2144611
  · exact B2144615
  · exact B2144619
  · exact B2144623
  · exact B2144627
  · exact B2144631
  · exact B2144635
  · exact B2144639
  · exact B2144643
  · exact B2144647
  · exact B2144651
  · exact B2144655
  · exact B2144659
  · exact B2144663
  · exact B2144667
  · exact B2144671
  · exact B2144675
  · exact B2144679
  · exact B2144683
  · exact B2144687
  · exact B2144691
  · exact B2144695
  · exact B2144699
  · exact B2144703
  · exact B2144707
  · exact B2144711
  · exact B2144715
  · exact B2144719
  · exact B2144723
  · exact B2144727
  · exact B2144731
  · exact B2144735
  · exact B2144739
  · exact B2144743
  · exact B2144747
  · exact B2144751
  · exact B2144755
  · exact B2144759
  · exact B2144763
  · exact B2144767
  · exact B2144771
  · exact B2144775
  · exact B2144779
  · exact B2144783
  · exact B2144787
  · exact B2144791
  · exact B2144795
  · exact B2144799
  · exact B2144803
  · exact B2144807
  · exact B2144811
  · exact B2144815
  · exact B2144819
  · exact B2144823
  · exact B2144827
  · exact B2144831
  · exact B2144835
  · exact B2144839
  · exact B2144843
  · exact B2144847
  · exact B2144851
  · exact B2144855
  · exact B2144859
  · exact B2144863
  · exact B2144867
  · exact B2144871
  · exact B2144875
  · exact B2144879
  · exact B2144883
  · exact B2144887
  · exact B2144891
  · exact B2144895
  · exact B2144899
  · exact B2144903
  · exact B2144907
  · exact B2144911
  · exact B2144915
  · exact B2144919
  · exact B2144923
  · exact B2144927
  · exact B2144931
  · exact B2144935
  · exact B2144939
  · exact B2144943
  · exact B2144947
  · exact B2144951
  · exact B2144955
  · exact B2144959
  · exact B2144963
  · exact B2144967
  · exact B2144971
  · exact B2144975
  · exact B2144979
  · exact B2144983
  · exact B2144987
  · exact B2144991
  · exact B2144995
  · exact B2144999
  · exact B2145003
  · exact B2145007
  · exact B2145011
  · exact B2145015
  · exact B2145019
  · exact B2145023
  · exact B2145027
  · exact B2145031
  · exact B2145035
  · exact B2145039
  · exact B2145043
  · exact B2145047
  · exact B2145051
  · exact B2145055
  · exact B2145059
  · exact B2145063
  · exact B2145067
  · exact B2145071
  · exact B2145075
  · exact B2145079
  · exact B2145083
  · exact B2145087
  · exact B2145091
  · exact B2145095
  · exact B2145099
  · exact B2145103
  · exact B2145107
  · exact B2145111
  · exact B2145115
  · exact B2145119
  · exact B2145123
  · exact B2145127
  · exact B2145131
  · exact B2145135
  · exact B2145139
  · exact B2145143
  · exact B2145147
  · exact B2145151
  · exact B2145155
  · exact B2145159
  · exact B2145163
  · exact B2145167
  · exact B2145171
  · exact B2145175
  · exact B2145179
  · exact B2145183
  · exact B2145187
  · exact B2145191
  · exact B2145195
  · exact B2145199
  · exact B2145203
  · exact B2145207
  · exact B2145211
  · exact B2145215
  · exact B2145219
  · exact B2145223
  · exact B2145227
  · exact B2145231
  · exact B2145235
  · exact B2145239
  · exact B2145243
  · exact B2145247
  · exact B2145251
  · exact B2145255
  · exact B2145259
  · exact B2145263
  · exact B2145267
  · exact B2145271
  · exact B2145275
  · exact B2145279
  · exact B2145283
  · exact B2145287
  · exact B2145291
  · exact B2145295
  · exact B2145299
  · exact B2145303
  · exact B2145307
  · exact B2145311
  · exact B2145315
  · exact B2145319
  · exact B2145323
  · exact B2145327
  · exact B2145331
  · exact B2145335
  · exact B2145339
  · exact B2145343
  · exact B2145347
  · exact B2145351
  · exact B2145355
  · exact B2145359
  · exact B2145363
  · exact B2145367
  · exact B2145371
  · exact B2145375
  · exact B2145379
  · exact B2145383
  · exact B2145387
  · exact B2145391
  · exact B2145395
  · exact B2145399
  · exact B2145403
  · exact B2145407
  · exact B2145411
  · exact B2145415
  · exact B2145419
  · exact B2145423
  · exact B2145427
  · exact B2145431
  · exact B2145435
theorem solution (m : ℕ) (hlo : 2143435 ≤ m) (hhi : m ≤ 2145435) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 535858 ≤ j := by omega
    have hj2 : j ≤ 536358 := by omega
    have hb : Blo 2143435 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
