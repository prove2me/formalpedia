-- Prove2me | solution 1 for syracuse_descends_range_2289435_2291435
-- status  : ACCEPTED   (prove)
-- author  : @chstdu
-- created : 2026-09-23T17:49:46.126064+00:00
-- url     : https://prove2.me/submissions/905a2be7-1dcb-4ca4-9fd9-db7150a23708

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

theorem B7153285 : Blo 2289435 7153285 := bbase (se 4 (by rfl) ⟨670620, by rfl⟩ : syracuseStep 7153285 = 1341241) (by norm_num)
theorem B9537713 : Blo 2289435 9537713 := bstep (se 2 (by rfl) ⟨3576642, by rfl⟩ : syracuseStep 9537713 = 7153285) B7153285
theorem B6358475 : Blo 2289435 6358475 := bstep (se 1 (by rfl) ⟨4768856, by rfl⟩ : syracuseStep 6358475 = 9537713) B9537713
theorem B4238983 : Blo 2289435 4238983 := bstep (se 1 (by rfl) ⟨3179237, by rfl⟩ : syracuseStep 4238983 = 6358475) B6358475
theorem B22607909 : Blo 2289435 22607909 := bstep (se 4 (by rfl) ⟨2119491, by rfl⟩ : syracuseStep 22607909 = 4238983) B4238983
theorem B15071939 : Blo 2289435 15071939 := bstep (se 1 (by rfl) ⟨11303954, by rfl⟩ : syracuseStep 15071939 = 22607909) B22607909
theorem B10047959 : Blo 2289435 10047959 := bstep (se 1 (by rfl) ⟨7535969, by rfl⟩ : syracuseStep 10047959 = 15071939) B15071939
theorem B6698639 : Blo 2289435 6698639 := bstep (se 1 (by rfl) ⟨5023979, by rfl⟩ : syracuseStep 6698639 = 10047959) B10047959
theorem B17863037 : Blo 2289435 17863037 := bstep (se 3 (by rfl) ⟨3349319, by rfl⟩ : syracuseStep 17863037 = 6698639) B6698639
theorem B11908691 : Blo 2289435 11908691 := bstep (se 1 (by rfl) ⟨8931518, by rfl⟩ : syracuseStep 11908691 = 17863037) B17863037
theorem B7939127 : Blo 2289435 7939127 := bstep (se 1 (by rfl) ⟨5954345, by rfl⟩ : syracuseStep 7939127 = 11908691) B11908691
theorem B5292751 : Blo 2289435 5292751 := bstep (se 1 (by rfl) ⟨3969563, by rfl⟩ : syracuseStep 5292751 = 7939127) B7939127
theorem B7057001 : Blo 2289435 7057001 := bstep (se 2 (by rfl) ⟨2646375, by rfl⟩ : syracuseStep 7057001 = 5292751) B5292751
theorem B18818669 : Blo 2289435 18818669 := bstep (se 3 (by rfl) ⟨3528500, by rfl⟩ : syracuseStep 18818669 = 7057001) B7057001
theorem B50183117 : Blo 2289435 50183117 := bstep (se 3 (by rfl) ⟨9409334, by rfl⟩ : syracuseStep 50183117 = 18818669) B18818669
theorem B33455411 : Blo 2289435 33455411 := bstep (se 1 (by rfl) ⟨25091558, by rfl⟩ : syracuseStep 33455411 = 50183117) B50183117
theorem B22303607 : Blo 2289435 22303607 := bstep (se 1 (by rfl) ⟨16727705, by rfl⟩ : syracuseStep 22303607 = 33455411) B33455411
theorem B59476285 : Blo 2289435 59476285 := bstep (se 3 (by rfl) ⟨11151803, by rfl⟩ : syracuseStep 59476285 = 22303607) B22303607
theorem B317206853 : Blo 2289435 317206853 := bstep (se 4 (by rfl) ⟨29738142, by rfl⟩ : syracuseStep 317206853 = 59476285) B59476285
theorem B211471235 : Blo 2289435 211471235 := bstep (se 1 (by rfl) ⟨158603426, by rfl⟩ : syracuseStep 211471235 = 317206853) B317206853
theorem B140980823 : Blo 2289435 140980823 := bstep (se 1 (by rfl) ⟨105735617, by rfl⟩ : syracuseStep 140980823 = 211471235) B211471235
theorem B93987215 : Blo 2289435 93987215 := bstep (se 1 (by rfl) ⟨70490411, by rfl⟩ : syracuseStep 93987215 = 140980823) B140980823
theorem B62658143 : Blo 2289435 62658143 := bstep (se 1 (by rfl) ⟨46993607, by rfl⟩ : syracuseStep 62658143 = 93987215) B93987215
theorem B41772095 : Blo 2289435 41772095 := bstep (se 1 (by rfl) ⟨31329071, by rfl⟩ : syracuseStep 41772095 = 62658143) B62658143
theorem B27848063 : Blo 2289435 27848063 := bstep (se 1 (by rfl) ⟨20886047, by rfl⟩ : syracuseStep 27848063 = 41772095) B41772095
theorem B18565375 : Blo 2289435 18565375 := bstep (se 1 (by rfl) ⟨13924031, by rfl⟩ : syracuseStep 18565375 = 27848063) B27848063
theorem B24753833 : Blo 2289435 24753833 := bstep (se 2 (by rfl) ⟨9282687, by rfl⟩ : syracuseStep 24753833 = 18565375) B18565375
theorem B16502555 : Blo 2289435 16502555 := bstep (se 1 (by rfl) ⟨12376916, by rfl⟩ : syracuseStep 16502555 = 24753833) B24753833
theorem B44006813 : Blo 2289435 44006813 := bstep (se 3 (by rfl) ⟨8251277, by rfl⟩ : syracuseStep 44006813 = 16502555) B16502555
theorem B29337875 : Blo 2289435 29337875 := bstep (se 1 (by rfl) ⟨22003406, by rfl⟩ : syracuseStep 29337875 = 44006813) B44006813
theorem B19558583 : Blo 2289435 19558583 := bstep (se 1 (by rfl) ⟨14668937, by rfl⟩ : syracuseStep 19558583 = 29337875) B29337875
theorem B13039055 : Blo 2289435 13039055 := bstep (se 1 (by rfl) ⟨9779291, by rfl⟩ : syracuseStep 13039055 = 19558583) B19558583
theorem B8692703 : Blo 2289435 8692703 := bstep (se 1 (by rfl) ⟨6519527, by rfl⟩ : syracuseStep 8692703 = 13039055) B13039055
theorem B5795135 : Blo 2289435 5795135 := bstep (se 1 (by rfl) ⟨4346351, by rfl⟩ : syracuseStep 5795135 = 8692703) B8692703
theorem B3863423 : Blo 2289435 3863423 := bstep (se 1 (by rfl) ⟨2897567, by rfl⟩ : syracuseStep 3863423 = 5795135) B5795135
theorem B2575615 : Blo 2289435 2575615 := bstep (se 1 (by rfl) ⟨1931711, by rfl⟩ : syracuseStep 2575615 = 3863423) B3863423
theorem B3434153 : Blo 2289435 3434153 := bstep (se 2 (by rfl) ⟨1287807, by rfl⟩ : syracuseStep 3434153 = 2575615) B2575615
theorem B2289435 : Blo 2289435 2289435 := bstep (se 1 (by rfl) ⟨1717076, by rfl⟩ : syracuseStep 2289435 = 3434153) B3434153
theorem B4405661 : Blo 2289435 4405661 := bbase (se 3 (by rfl) ⟨826061, by rfl⟩ : syracuseStep 4405661 = 1652123) (by norm_num)
theorem B2937107 : Blo 2289435 2937107 := bstep (se 1 (by rfl) ⟨2202830, by rfl⟩ : syracuseStep 2937107 = 4405661) B4405661
theorem B7832285 : Blo 2289435 7832285 := bstep (se 3 (by rfl) ⟨1468553, by rfl⟩ : syracuseStep 7832285 = 2937107) B2937107
theorem B5221523 : Blo 2289435 5221523 := bstep (se 1 (by rfl) ⟨3916142, by rfl⟩ : syracuseStep 5221523 = 7832285) B7832285
theorem B13924061 : Blo 2289435 13924061 := bstep (se 3 (by rfl) ⟨2610761, by rfl⟩ : syracuseStep 13924061 = 5221523) B5221523
theorem B9282707 : Blo 2289435 9282707 := bstep (se 1 (by rfl) ⟨6962030, by rfl⟩ : syracuseStep 9282707 = 13924061) B13924061
theorem B6188471 : Blo 2289435 6188471 := bstep (se 1 (by rfl) ⟨4641353, by rfl⟩ : syracuseStep 6188471 = 9282707) B9282707
theorem B4125647 : Blo 2289435 4125647 := bstep (se 1 (by rfl) ⟨3094235, by rfl⟩ : syracuseStep 4125647 = 6188471) B6188471
theorem B2750431 : Blo 2289435 2750431 := bstep (se 1 (by rfl) ⟨2062823, by rfl⟩ : syracuseStep 2750431 = 4125647) B4125647
theorem B3667241 : Blo 2289435 3667241 := bstep (se 2 (by rfl) ⟨1375215, by rfl⟩ : syracuseStep 3667241 = 2750431) B2750431
theorem B2444827 : Blo 2289435 2444827 := bstep (se 1 (by rfl) ⟨1833620, by rfl⟩ : syracuseStep 2444827 = 3667241) B3667241
theorem B3259769 : Blo 2289435 3259769 := bstep (se 2 (by rfl) ⟨1222413, by rfl⟩ : syracuseStep 3259769 = 2444827) B2444827
theorem B8692717 : Blo 2289435 8692717 := bstep (se 3 (by rfl) ⟨1629884, by rfl⟩ : syracuseStep 8692717 = 3259769) B3259769
theorem B11590289 : Blo 2289435 11590289 := bstep (se 2 (by rfl) ⟨4346358, by rfl⟩ : syracuseStep 11590289 = 8692717) B8692717
theorem B7726859 : Blo 2289435 7726859 := bstep (se 1 (by rfl) ⟨5795144, by rfl⟩ : syracuseStep 7726859 = 11590289) B11590289
theorem B5151239 : Blo 2289435 5151239 := bstep (se 1 (by rfl) ⟨3863429, by rfl⟩ : syracuseStep 5151239 = 7726859) B7726859
theorem B3434159 : Blo 2289435 3434159 := bstep (se 1 (by rfl) ⟨2575619, by rfl⟩ : syracuseStep 3434159 = 5151239) B5151239
theorem B2289439 : Blo 2289435 2289439 := bstep (se 1 (by rfl) ⟨1717079, by rfl⟩ : syracuseStep 2289439 = 3434159) B3434159
theorem B3434165 : Blo 2289435 3434165 := bbase (se 5 (by rfl) ⟨160976, by rfl⟩ : syracuseStep 3434165 = 321953) (by norm_num)
theorem B2289443 : Blo 2289435 2289443 := bstep (se 1 (by rfl) ⟨1717082, by rfl⟩ : syracuseStep 2289443 = 3434165) B3434165
theorem B5795165 : Blo 2289435 5795165 := bbase (se 3 (by rfl) ⟨1086593, by rfl⟩ : syracuseStep 5795165 = 2173187) (by norm_num)
theorem B3863443 : Blo 2289435 3863443 := bstep (se 1 (by rfl) ⟨2897582, by rfl⟩ : syracuseStep 3863443 = 5795165) B5795165
theorem B5151257 : Blo 2289435 5151257 := bstep (se 2 (by rfl) ⟨1931721, by rfl⟩ : syracuseStep 5151257 = 3863443) B3863443
theorem B3434171 : Blo 2289435 3434171 := bstep (se 1 (by rfl) ⟨2575628, by rfl⟩ : syracuseStep 3434171 = 5151257) B5151257
theorem B2289447 : Blo 2289435 2289447 := bstep (se 1 (by rfl) ⟨1717085, by rfl⟩ : syracuseStep 2289447 = 3434171) B3434171
theorem B2575633 : Blo 2289435 2575633 := bbase (se 2 (by rfl) ⟨965862, by rfl⟩ : syracuseStep 2575633 = 1931725) (by norm_num)
theorem B3434177 : Blo 2289435 3434177 := bstep (se 2 (by rfl) ⟨1287816, by rfl⟩ : syracuseStep 3434177 = 2575633) B2575633
theorem B2289451 : Blo 2289435 2289451 := bstep (se 1 (by rfl) ⟨1717088, by rfl⟩ : syracuseStep 2289451 = 3434177) B3434177
theorem B4346389 : Blo 2289435 4346389 := bbase (se 6 (by rfl) ⟨101868, by rfl⟩ : syracuseStep 4346389 = 203737) (by norm_num)
theorem B5795185 : Blo 2289435 5795185 := bstep (se 2 (by rfl) ⟨2173194, by rfl⟩ : syracuseStep 5795185 = 4346389) B4346389
theorem B7726913 : Blo 2289435 7726913 := bstep (se 2 (by rfl) ⟨2897592, by rfl⟩ : syracuseStep 7726913 = 5795185) B5795185
theorem B5151275 : Blo 2289435 5151275 := bstep (se 1 (by rfl) ⟨3863456, by rfl⟩ : syracuseStep 5151275 = 7726913) B7726913
theorem B3434183 : Blo 2289435 3434183 := bstep (se 1 (by rfl) ⟨2575637, by rfl⟩ : syracuseStep 3434183 = 5151275) B5151275
theorem B2289455 : Blo 2289435 2289455 := bstep (se 1 (by rfl) ⟨1717091, by rfl⟩ : syracuseStep 2289455 = 3434183) B3434183
theorem B3434189 : Blo 2289435 3434189 := bbase (se 3 (by rfl) ⟨643910, by rfl⟩ : syracuseStep 3434189 = 1287821) (by norm_num)
theorem B2289459 : Blo 2289435 2289459 := bstep (se 1 (by rfl) ⟨1717094, by rfl⟩ : syracuseStep 2289459 = 3434189) B3434189
theorem B5151293 : Blo 2289435 5151293 := bbase (se 3 (by rfl) ⟨965867, by rfl⟩ : syracuseStep 5151293 = 1931735) (by norm_num)
theorem B3434195 : Blo 2289435 3434195 := bstep (se 1 (by rfl) ⟨2575646, by rfl⟩ : syracuseStep 3434195 = 5151293) B5151293
theorem B2289463 : Blo 2289435 2289463 := bstep (se 1 (by rfl) ⟨1717097, by rfl⟩ : syracuseStep 2289463 = 3434195) B3434195
theorem B3863477 : Blo 2289435 3863477 := bbase (se 5 (by rfl) ⟨181100, by rfl⟩ : syracuseStep 3863477 = 362201) (by norm_num)
theorem B2575651 : Blo 2289435 2575651 := bstep (se 1 (by rfl) ⟨1931738, by rfl⟩ : syracuseStep 2575651 = 3863477) B3863477
theorem B3434201 : Blo 2289435 3434201 := bstep (se 2 (by rfl) ⟨1287825, by rfl⟩ : syracuseStep 3434201 = 2575651) B2575651
theorem B2289467 : Blo 2289435 2289467 := bstep (se 1 (by rfl) ⟨1717100, by rfl⟩ : syracuseStep 2289467 = 3434201) B3434201
theorem B2444861 : Blo 2289435 2444861 := bbase (se 3 (by rfl) ⟨458411, by rfl⟩ : syracuseStep 2444861 = 916823) (by norm_num)
theorem B6519629 : Blo 2289435 6519629 := bstep (se 3 (by rfl) ⟨1222430, by rfl⟩ : syracuseStep 6519629 = 2444861) B2444861
theorem B17385677 : Blo 2289435 17385677 := bstep (se 3 (by rfl) ⟨3259814, by rfl⟩ : syracuseStep 17385677 = 6519629) B6519629
theorem B11590451 : Blo 2289435 11590451 := bstep (se 1 (by rfl) ⟨8692838, by rfl⟩ : syracuseStep 11590451 = 17385677) B17385677
theorem B7726967 : Blo 2289435 7726967 := bstep (se 1 (by rfl) ⟨5795225, by rfl⟩ : syracuseStep 7726967 = 11590451) B11590451
theorem B5151311 : Blo 2289435 5151311 := bstep (se 1 (by rfl) ⟨3863483, by rfl⟩ : syracuseStep 5151311 = 7726967) B7726967
theorem B3434207 : Blo 2289435 3434207 := bstep (se 1 (by rfl) ⟨2575655, by rfl⟩ : syracuseStep 3434207 = 5151311) B5151311
theorem B2289471 : Blo 2289435 2289471 := bstep (se 1 (by rfl) ⟨1717103, by rfl⟩ : syracuseStep 2289471 = 3434207) B3434207
theorem B3434213 : Blo 2289435 3434213 := bbase (se 4 (by rfl) ⟨321957, by rfl⟩ : syracuseStep 3434213 = 643915) (by norm_num)
theorem B2289475 : Blo 2289435 2289475 := bstep (se 1 (by rfl) ⟨1717106, by rfl⟩ : syracuseStep 2289475 = 3434213) B3434213
theorem B6519653 : Blo 2289435 6519653 := bbase (se 4 (by rfl) ⟨611217, by rfl⟩ : syracuseStep 6519653 = 1222435) (by norm_num)
theorem B4346435 : Blo 2289435 4346435 := bstep (se 1 (by rfl) ⟨3259826, by rfl⟩ : syracuseStep 4346435 = 6519653) B6519653
theorem B2897623 : Blo 2289435 2897623 := bstep (se 1 (by rfl) ⟨2173217, by rfl⟩ : syracuseStep 2897623 = 4346435) B4346435
theorem B3863497 : Blo 2289435 3863497 := bstep (se 2 (by rfl) ⟨1448811, by rfl⟩ : syracuseStep 3863497 = 2897623) B2897623
theorem B5151329 : Blo 2289435 5151329 := bstep (se 2 (by rfl) ⟨1931748, by rfl⟩ : syracuseStep 5151329 = 3863497) B3863497
theorem B3434219 : Blo 2289435 3434219 := bstep (se 1 (by rfl) ⟨2575664, by rfl⟩ : syracuseStep 3434219 = 5151329) B5151329
theorem B2289479 : Blo 2289435 2289479 := bstep (se 1 (by rfl) ⟨1717109, by rfl⟩ : syracuseStep 2289479 = 3434219) B3434219
theorem B2575669 : Blo 2289435 2575669 := bbase (se 5 (by rfl) ⟨120734, by rfl⟩ : syracuseStep 2575669 = 241469) (by norm_num)
theorem B3434225 : Blo 2289435 3434225 := bstep (se 2 (by rfl) ⟨1287834, by rfl⟩ : syracuseStep 3434225 = 2575669) B2575669
theorem B2289483 : Blo 2289435 2289483 := bstep (se 1 (by rfl) ⟨1717112, by rfl⟩ : syracuseStep 2289483 = 3434225) B3434225
theorem B2897633 : Blo 2289435 2897633 := bbase (se 2 (by rfl) ⟨1086612, by rfl⟩ : syracuseStep 2897633 = 2173225) (by norm_num)
theorem B7727021 : Blo 2289435 7727021 := bstep (se 3 (by rfl) ⟨1448816, by rfl⟩ : syracuseStep 7727021 = 2897633) B2897633
theorem B5151347 : Blo 2289435 5151347 := bstep (se 1 (by rfl) ⟨3863510, by rfl⟩ : syracuseStep 5151347 = 7727021) B7727021
theorem B3434231 : Blo 2289435 3434231 := bstep (se 1 (by rfl) ⟨2575673, by rfl⟩ : syracuseStep 3434231 = 5151347) B5151347
theorem B2289487 : Blo 2289435 2289487 := bstep (se 1 (by rfl) ⟨1717115, by rfl⟩ : syracuseStep 2289487 = 3434231) B3434231
theorem B3434237 : Blo 2289435 3434237 := bbase (se 3 (by rfl) ⟨643919, by rfl⟩ : syracuseStep 3434237 = 1287839) (by norm_num)
theorem B2289491 : Blo 2289435 2289491 := bstep (se 1 (by rfl) ⟨1717118, by rfl⟩ : syracuseStep 2289491 = 3434237) B3434237
theorem B5151365 : Blo 2289435 5151365 := bbase (se 4 (by rfl) ⟨482940, by rfl⟩ : syracuseStep 5151365 = 965881) (by norm_num)
theorem B3434243 : Blo 2289435 3434243 := bstep (se 1 (by rfl) ⟨2575682, by rfl⟩ : syracuseStep 3434243 = 5151365) B5151365
theorem B2289495 : Blo 2289435 2289495 := bstep (se 1 (by rfl) ⟨1717121, by rfl⟩ : syracuseStep 2289495 = 3434243) B3434243
theorem B6962213 : Blo 2289435 6962213 := bbase (se 4 (by rfl) ⟨652707, by rfl⟩ : syracuseStep 6962213 = 1305415) (by norm_num)
theorem B4641475 : Blo 2289435 4641475 := bstep (se 1 (by rfl) ⟨3481106, by rfl⟩ : syracuseStep 4641475 = 6962213) B6962213
theorem B6188633 : Blo 2289435 6188633 := bstep (se 2 (by rfl) ⟨2320737, by rfl⟩ : syracuseStep 6188633 = 4641475) B4641475
theorem B4125755 : Blo 2289435 4125755 := bstep (se 1 (by rfl) ⟨3094316, by rfl⟩ : syracuseStep 4125755 = 6188633) B6188633
theorem B11002013 : Blo 2289435 11002013 := bstep (se 3 (by rfl) ⟨2062877, by rfl⟩ : syracuseStep 11002013 = 4125755) B4125755
theorem B7334675 : Blo 2289435 7334675 := bstep (se 1 (by rfl) ⟨5501006, by rfl⟩ : syracuseStep 7334675 = 11002013) B11002013
theorem B4889783 : Blo 2289435 4889783 := bstep (se 1 (by rfl) ⟨3667337, by rfl⟩ : syracuseStep 4889783 = 7334675) B7334675
theorem B3259855 : Blo 2289435 3259855 := bstep (se 1 (by rfl) ⟨2444891, by rfl⟩ : syracuseStep 3259855 = 4889783) B4889783
theorem B4346473 : Blo 2289435 4346473 := bstep (se 2 (by rfl) ⟨1629927, by rfl⟩ : syracuseStep 4346473 = 3259855) B3259855
theorem B5795297 : Blo 2289435 5795297 := bstep (se 2 (by rfl) ⟨2173236, by rfl⟩ : syracuseStep 5795297 = 4346473) B4346473
theorem B3863531 : Blo 2289435 3863531 := bstep (se 1 (by rfl) ⟨2897648, by rfl⟩ : syracuseStep 3863531 = 5795297) B5795297
theorem B2575687 : Blo 2289435 2575687 := bstep (se 1 (by rfl) ⟨1931765, by rfl⟩ : syracuseStep 2575687 = 3863531) B3863531
theorem B3434249 : Blo 2289435 3434249 := bstep (se 2 (by rfl) ⟨1287843, by rfl⟩ : syracuseStep 3434249 = 2575687) B2575687
theorem B2289499 : Blo 2289435 2289499 := bstep (se 1 (by rfl) ⟨1717124, by rfl⟩ : syracuseStep 2289499 = 3434249) B3434249
theorem B11590613 : Blo 2289435 11590613 := bbase (se 7 (by rfl) ⟨135827, by rfl⟩ : syracuseStep 11590613 = 271655) (by norm_num)
theorem B7727075 : Blo 2289435 7727075 := bstep (se 1 (by rfl) ⟨5795306, by rfl⟩ : syracuseStep 7727075 = 11590613) B11590613
theorem B5151383 : Blo 2289435 5151383 := bstep (se 1 (by rfl) ⟨3863537, by rfl⟩ : syracuseStep 5151383 = 7727075) B7727075
theorem B3434255 : Blo 2289435 3434255 := bstep (se 1 (by rfl) ⟨2575691, by rfl⟩ : syracuseStep 3434255 = 5151383) B5151383
theorem B2289503 : Blo 2289435 2289503 := bstep (se 1 (by rfl) ⟨1717127, by rfl⟩ : syracuseStep 2289503 = 3434255) B3434255
theorem B3434261 : Blo 2289435 3434261 := bbase (se 6 (by rfl) ⟨80490, by rfl⟩ : syracuseStep 3434261 = 160981) (by norm_num)
theorem B2289507 : Blo 2289435 2289507 := bstep (se 1 (by rfl) ⟨1717130, by rfl⟩ : syracuseStep 2289507 = 3434261) B3434261
theorem B12546197 : Blo 2289435 12546197 := bbase (se 6 (by rfl) ⟨294051, by rfl⟩ : syracuseStep 12546197 = 588103) (by norm_num)
theorem B8364131 : Blo 2289435 8364131 := bstep (se 1 (by rfl) ⟨6273098, by rfl⟩ : syracuseStep 8364131 = 12546197) B12546197
theorem B5576087 : Blo 2289435 5576087 := bstep (se 1 (by rfl) ⟨4182065, by rfl⟩ : syracuseStep 5576087 = 8364131) B8364131
theorem B14869565 : Blo 2289435 14869565 := bstep (se 3 (by rfl) ⟨2788043, by rfl⟩ : syracuseStep 14869565 = 5576087) B5576087
theorem B9913043 : Blo 2289435 9913043 := bstep (se 1 (by rfl) ⟨7434782, by rfl⟩ : syracuseStep 9913043 = 14869565) B14869565
theorem B26434781 : Blo 2289435 26434781 := bstep (se 3 (by rfl) ⟨4956521, by rfl⟩ : syracuseStep 26434781 = 9913043) B9913043
theorem B17623187 : Blo 2289435 17623187 := bstep (se 1 (by rfl) ⟨13217390, by rfl⟩ : syracuseStep 17623187 = 26434781) B26434781
theorem B11748791 : Blo 2289435 11748791 := bstep (se 1 (by rfl) ⟨8811593, by rfl⟩ : syracuseStep 11748791 = 17623187) B17623187
theorem B7832527 : Blo 2289435 7832527 := bstep (se 1 (by rfl) ⟨5874395, by rfl⟩ : syracuseStep 7832527 = 11748791) B11748791
theorem B41773477 : Blo 2289435 41773477 := bstep (se 4 (by rfl) ⟨3916263, by rfl⟩ : syracuseStep 41773477 = 7832527) B7832527
theorem B55697969 : Blo 2289435 55697969 := bstep (se 2 (by rfl) ⟨20886738, by rfl⟩ : syracuseStep 55697969 = 41773477) B41773477
theorem B148527917 : Blo 2289435 148527917 := bstep (se 3 (by rfl) ⟨27848984, by rfl⟩ : syracuseStep 148527917 = 55697969) B55697969
theorem B99018611 : Blo 2289435 99018611 := bstep (se 1 (by rfl) ⟨74263958, by rfl⟩ : syracuseStep 99018611 = 148527917) B148527917
theorem B66012407 : Blo 2289435 66012407 := bstep (se 1 (by rfl) ⟨49509305, by rfl⟩ : syracuseStep 66012407 = 99018611) B99018611
theorem B44008271 : Blo 2289435 44008271 := bstep (se 1 (by rfl) ⟨33006203, by rfl⟩ : syracuseStep 44008271 = 66012407) B66012407
theorem B29338847 : Blo 2289435 29338847 := bstep (se 1 (by rfl) ⟨22004135, by rfl⟩ : syracuseStep 29338847 = 44008271) B44008271
theorem B19559231 : Blo 2289435 19559231 := bstep (se 1 (by rfl) ⟨14669423, by rfl⟩ : syracuseStep 19559231 = 29338847) B29338847
theorem B13039487 : Blo 2289435 13039487 := bstep (se 1 (by rfl) ⟨9779615, by rfl⟩ : syracuseStep 13039487 = 19559231) B19559231
theorem B8692991 : Blo 2289435 8692991 := bstep (se 1 (by rfl) ⟨6519743, by rfl⟩ : syracuseStep 8692991 = 13039487) B13039487
theorem B5795327 : Blo 2289435 5795327 := bstep (se 1 (by rfl) ⟨4346495, by rfl⟩ : syracuseStep 5795327 = 8692991) B8692991
theorem B3863551 : Blo 2289435 3863551 := bstep (se 1 (by rfl) ⟨2897663, by rfl⟩ : syracuseStep 3863551 = 5795327) B5795327
theorem B5151401 : Blo 2289435 5151401 := bstep (se 2 (by rfl) ⟨1931775, by rfl⟩ : syracuseStep 5151401 = 3863551) B3863551
theorem B3434267 : Blo 2289435 3434267 := bstep (se 1 (by rfl) ⟨2575700, by rfl⟩ : syracuseStep 3434267 = 5151401) B5151401
theorem B2289511 : Blo 2289435 2289511 := bstep (se 1 (by rfl) ⟨1717133, by rfl⟩ : syracuseStep 2289511 = 3434267) B3434267
theorem B2575705 : Blo 2289435 2575705 := bbase (se 2 (by rfl) ⟨965889, by rfl⟩ : syracuseStep 2575705 = 1931779) (by norm_num)
theorem B3434273 : Blo 2289435 3434273 := bstep (se 2 (by rfl) ⟨1287852, by rfl⟩ : syracuseStep 3434273 = 2575705) B2575705
theorem B2289515 : Blo 2289435 2289515 := bstep (se 1 (by rfl) ⟨1717136, by rfl⟩ : syracuseStep 2289515 = 3434273) B3434273
theorem B2977285 : Blo 2289435 2977285 := bbase (se 4 (by rfl) ⟨279120, by rfl⟩ : syracuseStep 2977285 = 558241) (by norm_num)
theorem B3969713 : Blo 2289435 3969713 := bstep (se 2 (by rfl) ⟨1488642, by rfl⟩ : syracuseStep 3969713 = 2977285) B2977285
theorem B2646475 : Blo 2289435 2646475 := bstep (se 1 (by rfl) ⟨1984856, by rfl⟩ : syracuseStep 2646475 = 3969713) B3969713
theorem B14114533 : Blo 2289435 14114533 := bstep (se 4 (by rfl) ⟨1323237, by rfl⟩ : syracuseStep 14114533 = 2646475) B2646475
theorem B18819377 : Blo 2289435 18819377 := bstep (se 2 (by rfl) ⟨7057266, by rfl⟩ : syracuseStep 18819377 = 14114533) B14114533
theorem B12546251 : Blo 2289435 12546251 := bstep (se 1 (by rfl) ⟨9409688, by rfl⟩ : syracuseStep 12546251 = 18819377) B18819377
theorem B8364167 : Blo 2289435 8364167 := bstep (se 1 (by rfl) ⟨6273125, by rfl⟩ : syracuseStep 8364167 = 12546251) B12546251
theorem B5576111 : Blo 2289435 5576111 := bstep (se 1 (by rfl) ⟨4182083, by rfl⟩ : syracuseStep 5576111 = 8364167) B8364167
theorem B3717407 : Blo 2289435 3717407 := bstep (se 1 (by rfl) ⟨2788055, by rfl⟩ : syracuseStep 3717407 = 5576111) B5576111
theorem B2478271 : Blo 2289435 2478271 := bstep (se 1 (by rfl) ⟨1858703, by rfl⟩ : syracuseStep 2478271 = 3717407) B3717407
theorem B3304361 : Blo 2289435 3304361 := bstep (se 2 (by rfl) ⟨1239135, by rfl⟩ : syracuseStep 3304361 = 2478271) B2478271
theorem B8811629 : Blo 2289435 8811629 := bstep (se 3 (by rfl) ⟨1652180, by rfl⟩ : syracuseStep 8811629 = 3304361) B3304361
theorem B5874419 : Blo 2289435 5874419 := bstep (se 1 (by rfl) ⟨4405814, by rfl⟩ : syracuseStep 5874419 = 8811629) B8811629
theorem B3916279 : Blo 2289435 3916279 := bstep (se 1 (by rfl) ⟨2937209, by rfl⟩ : syracuseStep 3916279 = 5874419) B5874419
theorem B20886821 : Blo 2289435 20886821 := bstep (se 4 (by rfl) ⟨1958139, by rfl⟩ : syracuseStep 20886821 = 3916279) B3916279
theorem B13924547 : Blo 2289435 13924547 := bstep (se 1 (by rfl) ⟨10443410, by rfl⟩ : syracuseStep 13924547 = 20886821) B20886821
theorem B9283031 : Blo 2289435 9283031 := bstep (se 1 (by rfl) ⟨6962273, by rfl⟩ : syracuseStep 9283031 = 13924547) B13924547
theorem B6188687 : Blo 2289435 6188687 := bstep (se 1 (by rfl) ⟨4641515, by rfl⟩ : syracuseStep 6188687 = 9283031) B9283031
theorem B4125791 : Blo 2289435 4125791 := bstep (se 1 (by rfl) ⟨3094343, by rfl⟩ : syracuseStep 4125791 = 6188687) B6188687
theorem B2750527 : Blo 2289435 2750527 := bstep (se 1 (by rfl) ⟨2062895, by rfl⟩ : syracuseStep 2750527 = 4125791) B4125791
theorem B3667369 : Blo 2289435 3667369 := bstep (se 2 (by rfl) ⟨1375263, by rfl⟩ : syracuseStep 3667369 = 2750527) B2750527
theorem B4889825 : Blo 2289435 4889825 := bstep (se 2 (by rfl) ⟨1833684, by rfl⟩ : syracuseStep 4889825 = 3667369) B3667369
theorem B3259883 : Blo 2289435 3259883 := bstep (se 1 (by rfl) ⟨2444912, by rfl⟩ : syracuseStep 3259883 = 4889825) B4889825
theorem B8693021 : Blo 2289435 8693021 := bstep (se 3 (by rfl) ⟨1629941, by rfl⟩ : syracuseStep 8693021 = 3259883) B3259883
theorem B5795347 : Blo 2289435 5795347 := bstep (se 1 (by rfl) ⟨4346510, by rfl⟩ : syracuseStep 5795347 = 8693021) B8693021
theorem B7727129 : Blo 2289435 7727129 := bstep (se 2 (by rfl) ⟨2897673, by rfl⟩ : syracuseStep 7727129 = 5795347) B5795347
theorem B5151419 : Blo 2289435 5151419 := bstep (se 1 (by rfl) ⟨3863564, by rfl⟩ : syracuseStep 5151419 = 7727129) B7727129
theorem B3434279 : Blo 2289435 3434279 := bstep (se 1 (by rfl) ⟨2575709, by rfl⟩ : syracuseStep 3434279 = 5151419) B5151419
theorem B2289519 : Blo 2289435 2289519 := bstep (se 1 (by rfl) ⟨1717139, by rfl⟩ : syracuseStep 2289519 = 3434279) B3434279
theorem B3434285 : Blo 2289435 3434285 := bbase (se 3 (by rfl) ⟨643928, by rfl⟩ : syracuseStep 3434285 = 1287857) (by norm_num)
theorem B2289523 : Blo 2289435 2289523 := bstep (se 1 (by rfl) ⟨1717142, by rfl⟩ : syracuseStep 2289523 = 3434285) B3434285
theorem B5151437 : Blo 2289435 5151437 := bbase (se 3 (by rfl) ⟨965894, by rfl⟩ : syracuseStep 5151437 = 1931789) (by norm_num)
theorem B3434291 : Blo 2289435 3434291 := bstep (se 1 (by rfl) ⟨2575718, by rfl⟩ : syracuseStep 3434291 = 5151437) B5151437
theorem B2289527 : Blo 2289435 2289527 := bstep (se 1 (by rfl) ⟨1717145, by rfl⟩ : syracuseStep 2289527 = 3434291) B3434291
theorem B2897689 : Blo 2289435 2897689 := bbase (se 2 (by rfl) ⟨1086633, by rfl⟩ : syracuseStep 2897689 = 2173267) (by norm_num)
theorem B3863585 : Blo 2289435 3863585 := bstep (se 2 (by rfl) ⟨1448844, by rfl⟩ : syracuseStep 3863585 = 2897689) B2897689
theorem B2575723 : Blo 2289435 2575723 := bstep (se 1 (by rfl) ⟨1931792, by rfl⟩ : syracuseStep 2575723 = 3863585) B3863585
theorem B3434297 : Blo 2289435 3434297 := bstep (se 2 (by rfl) ⟨1287861, by rfl⟩ : syracuseStep 3434297 = 2575723) B2575723
theorem B2289531 : Blo 2289435 2289531 := bstep (se 1 (by rfl) ⟨1717148, by rfl⟩ : syracuseStep 2289531 = 3434297) B3434297
theorem B9779717 : Blo 2289435 9779717 := bbase (se 4 (by rfl) ⟨916848, by rfl⟩ : syracuseStep 9779717 = 1833697) (by norm_num)
theorem B26079245 : Blo 2289435 26079245 := bstep (se 3 (by rfl) ⟨4889858, by rfl⟩ : syracuseStep 26079245 = 9779717) B9779717
theorem B17386163 : Blo 2289435 17386163 := bstep (se 1 (by rfl) ⟨13039622, by rfl⟩ : syracuseStep 17386163 = 26079245) B26079245
theorem B11590775 : Blo 2289435 11590775 := bstep (se 1 (by rfl) ⟨8693081, by rfl⟩ : syracuseStep 11590775 = 17386163) B17386163
theorem B7727183 : Blo 2289435 7727183 := bstep (se 1 (by rfl) ⟨5795387, by rfl⟩ : syracuseStep 7727183 = 11590775) B11590775
theorem B5151455 : Blo 2289435 5151455 := bstep (se 1 (by rfl) ⟨3863591, by rfl⟩ : syracuseStep 5151455 = 7727183) B7727183
theorem B3434303 : Blo 2289435 3434303 := bstep (se 1 (by rfl) ⟨2575727, by rfl⟩ : syracuseStep 3434303 = 5151455) B5151455
theorem B2289535 : Blo 2289435 2289535 := bstep (se 1 (by rfl) ⟨1717151, by rfl⟩ : syracuseStep 2289535 = 3434303) B3434303
theorem B3434309 : Blo 2289435 3434309 := bbase (se 4 (by rfl) ⟨321966, by rfl⟩ : syracuseStep 3434309 = 643933) (by norm_num)
theorem B2289539 : Blo 2289435 2289539 := bstep (se 1 (by rfl) ⟨1717154, by rfl⟩ : syracuseStep 2289539 = 3434309) B3434309
theorem B3863605 : Blo 2289435 3863605 := bbase (se 5 (by rfl) ⟨181106, by rfl⟩ : syracuseStep 3863605 = 362213) (by norm_num)
theorem B5151473 : Blo 2289435 5151473 := bstep (se 2 (by rfl) ⟨1931802, by rfl⟩ : syracuseStep 5151473 = 3863605) B3863605
theorem B3434315 : Blo 2289435 3434315 := bstep (se 1 (by rfl) ⟨2575736, by rfl⟩ : syracuseStep 3434315 = 5151473) B5151473
theorem B2289543 : Blo 2289435 2289543 := bstep (se 1 (by rfl) ⟨1717157, by rfl⟩ : syracuseStep 2289543 = 3434315) B3434315
theorem B2575741 : Blo 2289435 2575741 := bbase (se 3 (by rfl) ⟨482951, by rfl⟩ : syracuseStep 2575741 = 965903) (by norm_num)
theorem B3434321 : Blo 2289435 3434321 := bstep (se 2 (by rfl) ⟨1287870, by rfl⟩ : syracuseStep 3434321 = 2575741) B2575741
theorem B2289547 : Blo 2289435 2289547 := bstep (se 1 (by rfl) ⟨1717160, by rfl⟩ : syracuseStep 2289547 = 3434321) B3434321
theorem B7727237 : Blo 2289435 7727237 := bbase (se 4 (by rfl) ⟨724428, by rfl⟩ : syracuseStep 7727237 = 1448857) (by norm_num)
theorem B5151491 : Blo 2289435 5151491 := bstep (se 1 (by rfl) ⟨3863618, by rfl⟩ : syracuseStep 5151491 = 7727237) B7727237
theorem B3434327 : Blo 2289435 3434327 := bstep (se 1 (by rfl) ⟨2575745, by rfl⟩ : syracuseStep 3434327 = 5151491) B5151491
theorem B2289551 : Blo 2289435 2289551 := bstep (se 1 (by rfl) ⟨1717163, by rfl⟩ : syracuseStep 2289551 = 3434327) B3434327
theorem B3434333 : Blo 2289435 3434333 := bbase (se 3 (by rfl) ⟨643937, by rfl⟩ : syracuseStep 3434333 = 1287875) (by norm_num)
theorem B2289555 : Blo 2289435 2289555 := bstep (se 1 (by rfl) ⟨1717166, by rfl⟩ : syracuseStep 2289555 = 3434333) B3434333
theorem B5151509 : Blo 2289435 5151509 := bbase (se 6 (by rfl) ⟨120738, by rfl⟩ : syracuseStep 5151509 = 241477) (by norm_num)
theorem B3434339 : Blo 2289435 3434339 := bstep (se 1 (by rfl) ⟨2575754, by rfl⟩ : syracuseStep 3434339 = 5151509) B5151509
theorem B2289559 : Blo 2289435 2289559 := bstep (se 1 (by rfl) ⟨1717169, by rfl⟩ : syracuseStep 2289559 = 3434339) B3434339
theorem B8693189 : Blo 2289435 8693189 := bbase (se 4 (by rfl) ⟨814986, by rfl⟩ : syracuseStep 8693189 = 1629973) (by norm_num)
theorem B5795459 : Blo 2289435 5795459 := bstep (se 1 (by rfl) ⟨4346594, by rfl⟩ : syracuseStep 5795459 = 8693189) B8693189
theorem B3863639 : Blo 2289435 3863639 := bstep (se 1 (by rfl) ⟨2897729, by rfl⟩ : syracuseStep 3863639 = 5795459) B5795459
theorem B2575759 : Blo 2289435 2575759 := bstep (se 1 (by rfl) ⟨1931819, by rfl⟩ : syracuseStep 2575759 = 3863639) B3863639
theorem B3434345 : Blo 2289435 3434345 := bstep (se 2 (by rfl) ⟨1287879, by rfl⟩ : syracuseStep 3434345 = 2575759) B2575759
theorem B2289563 : Blo 2289435 2289563 := bstep (se 1 (by rfl) ⟨1717172, by rfl⟩ : syracuseStep 2289563 = 3434345) B3434345
theorem B20887253 : Blo 2289435 20887253 := bbase (se 7 (by rfl) ⟨244772, by rfl⟩ : syracuseStep 20887253 = 489545) (by norm_num)
theorem B13924835 : Blo 2289435 13924835 := bstep (se 1 (by rfl) ⟨10443626, by rfl⟩ : syracuseStep 13924835 = 20887253) B20887253
theorem B9283223 : Blo 2289435 9283223 := bstep (se 1 (by rfl) ⟨6962417, by rfl⟩ : syracuseStep 9283223 = 13924835) B13924835
theorem B6188815 : Blo 2289435 6188815 := bstep (se 1 (by rfl) ⟨4641611, by rfl⟩ : syracuseStep 6188815 = 9283223) B9283223
theorem B8251753 : Blo 2289435 8251753 := bstep (se 2 (by rfl) ⟨3094407, by rfl⟩ : syracuseStep 8251753 = 6188815) B6188815
theorem B11002337 : Blo 2289435 11002337 := bstep (se 2 (by rfl) ⟨4125876, by rfl⟩ : syracuseStep 11002337 = 8251753) B8251753
theorem B7334891 : Blo 2289435 7334891 := bstep (se 1 (by rfl) ⟨5501168, by rfl⟩ : syracuseStep 7334891 = 11002337) B11002337
theorem B4889927 : Blo 2289435 4889927 := bstep (se 1 (by rfl) ⟨3667445, by rfl⟩ : syracuseStep 4889927 = 7334891) B7334891
theorem B13039805 : Blo 2289435 13039805 := bstep (se 3 (by rfl) ⟨2444963, by rfl⟩ : syracuseStep 13039805 = 4889927) B4889927
theorem B8693203 : Blo 2289435 8693203 := bstep (se 1 (by rfl) ⟨6519902, by rfl⟩ : syracuseStep 8693203 = 13039805) B13039805
theorem B11590937 : Blo 2289435 11590937 := bstep (se 2 (by rfl) ⟨4346601, by rfl⟩ : syracuseStep 11590937 = 8693203) B8693203
theorem B7727291 : Blo 2289435 7727291 := bstep (se 1 (by rfl) ⟨5795468, by rfl⟩ : syracuseStep 7727291 = 11590937) B11590937
theorem B5151527 : Blo 2289435 5151527 := bstep (se 1 (by rfl) ⟨3863645, by rfl⟩ : syracuseStep 5151527 = 7727291) B7727291
theorem B3434351 : Blo 2289435 3434351 := bstep (se 1 (by rfl) ⟨2575763, by rfl⟩ : syracuseStep 3434351 = 5151527) B5151527
theorem B2289567 : Blo 2289435 2289567 := bstep (se 1 (by rfl) ⟨1717175, by rfl⟩ : syracuseStep 2289567 = 3434351) B3434351
theorem B3434357 : Blo 2289435 3434357 := bbase (se 5 (by rfl) ⟨160985, by rfl⟩ : syracuseStep 3434357 = 321971) (by norm_num)
theorem B2289571 : Blo 2289435 2289571 := bstep (se 1 (by rfl) ⟨1717178, by rfl⟩ : syracuseStep 2289571 = 3434357) B3434357
theorem B5501189 : Blo 2289435 5501189 := bbase (se 4 (by rfl) ⟨515736, by rfl⟩ : syracuseStep 5501189 = 1031473) (by norm_num)
theorem B3667459 : Blo 2289435 3667459 := bstep (se 1 (by rfl) ⟨2750594, by rfl⟩ : syracuseStep 3667459 = 5501189) B5501189
theorem B4889945 : Blo 2289435 4889945 := bstep (se 2 (by rfl) ⟨1833729, by rfl⟩ : syracuseStep 4889945 = 3667459) B3667459
theorem B3259963 : Blo 2289435 3259963 := bstep (se 1 (by rfl) ⟨2444972, by rfl⟩ : syracuseStep 3259963 = 4889945) B4889945
theorem B4346617 : Blo 2289435 4346617 := bstep (se 2 (by rfl) ⟨1629981, by rfl⟩ : syracuseStep 4346617 = 3259963) B3259963
theorem B5795489 : Blo 2289435 5795489 := bstep (se 2 (by rfl) ⟨2173308, by rfl⟩ : syracuseStep 5795489 = 4346617) B4346617
theorem B3863659 : Blo 2289435 3863659 := bstep (se 1 (by rfl) ⟨2897744, by rfl⟩ : syracuseStep 3863659 = 5795489) B5795489
theorem B5151545 : Blo 2289435 5151545 := bstep (se 2 (by rfl) ⟨1931829, by rfl⟩ : syracuseStep 5151545 = 3863659) B3863659
theorem B3434363 : Blo 2289435 3434363 := bstep (se 1 (by rfl) ⟨2575772, by rfl⟩ : syracuseStep 3434363 = 5151545) B5151545
theorem B2289575 : Blo 2289435 2289575 := bstep (se 1 (by rfl) ⟨1717181, by rfl⟩ : syracuseStep 2289575 = 3434363) B3434363
theorem B2575777 : Blo 2289435 2575777 := bbase (se 2 (by rfl) ⟨965916, by rfl⟩ : syracuseStep 2575777 = 1931833) (by norm_num)
theorem B3434369 : Blo 2289435 3434369 := bstep (se 2 (by rfl) ⟨1287888, by rfl⟩ : syracuseStep 3434369 = 2575777) B2575777
theorem B2289579 : Blo 2289435 2289579 := bstep (se 1 (by rfl) ⟨1717184, by rfl⟩ : syracuseStep 2289579 = 3434369) B3434369
theorem B5795509 : Blo 2289435 5795509 := bbase (se 5 (by rfl) ⟨271664, by rfl⟩ : syracuseStep 5795509 = 543329) (by norm_num)
theorem B7727345 : Blo 2289435 7727345 := bstep (se 2 (by rfl) ⟨2897754, by rfl⟩ : syracuseStep 7727345 = 5795509) B5795509
theorem B5151563 : Blo 2289435 5151563 := bstep (se 1 (by rfl) ⟨3863672, by rfl⟩ : syracuseStep 5151563 = 7727345) B7727345
theorem B3434375 : Blo 2289435 3434375 := bstep (se 1 (by rfl) ⟨2575781, by rfl⟩ : syracuseStep 3434375 = 5151563) B5151563
theorem B2289583 : Blo 2289435 2289583 := bstep (se 1 (by rfl) ⟨1717187, by rfl⟩ : syracuseStep 2289583 = 3434375) B3434375
theorem B3434381 : Blo 2289435 3434381 := bbase (se 3 (by rfl) ⟨643946, by rfl⟩ : syracuseStep 3434381 = 1287893) (by norm_num)
theorem B2289587 : Blo 2289435 2289587 := bstep (se 1 (by rfl) ⟨1717190, by rfl⟩ : syracuseStep 2289587 = 3434381) B3434381
theorem B5151581 : Blo 2289435 5151581 := bbase (se 3 (by rfl) ⟨965921, by rfl⟩ : syracuseStep 5151581 = 1931843) (by norm_num)
theorem B3434387 : Blo 2289435 3434387 := bstep (se 1 (by rfl) ⟨2575790, by rfl⟩ : syracuseStep 3434387 = 5151581) B5151581
theorem B2289591 : Blo 2289435 2289591 := bstep (se 1 (by rfl) ⟨1717193, by rfl⟩ : syracuseStep 2289591 = 3434387) B3434387
theorem B3863693 : Blo 2289435 3863693 := bbase (se 3 (by rfl) ⟨724442, by rfl⟩ : syracuseStep 3863693 = 1448885) (by norm_num)
theorem B2575795 : Blo 2289435 2575795 := bstep (se 1 (by rfl) ⟨1931846, by rfl⟩ : syracuseStep 2575795 = 3863693) B3863693
theorem B3434393 : Blo 2289435 3434393 := bstep (se 2 (by rfl) ⟨1287897, by rfl⟩ : syracuseStep 3434393 = 2575795) B2575795
theorem B2289595 : Blo 2289435 2289595 := bstep (se 1 (by rfl) ⟨1717196, by rfl⟩ : syracuseStep 2289595 = 3434393) B3434393
theorem B5501245 : Blo 2289435 5501245 := bbase (se 3 (by rfl) ⟨1031483, by rfl⟩ : syracuseStep 5501245 = 2062967) (by norm_num)
theorem B7334993 : Blo 2289435 7334993 := bstep (se 2 (by rfl) ⟨2750622, by rfl⟩ : syracuseStep 7334993 = 5501245) B5501245
theorem B19559981 : Blo 2289435 19559981 := bstep (se 3 (by rfl) ⟨3667496, by rfl⟩ : syracuseStep 19559981 = 7334993) B7334993
theorem B13039987 : Blo 2289435 13039987 := bstep (se 1 (by rfl) ⟨9779990, by rfl⟩ : syracuseStep 13039987 = 19559981) B19559981
theorem B17386649 : Blo 2289435 17386649 := bstep (se 2 (by rfl) ⟨6519993, by rfl⟩ : syracuseStep 17386649 = 13039987) B13039987
theorem B11591099 : Blo 2289435 11591099 := bstep (se 1 (by rfl) ⟨8693324, by rfl⟩ : syracuseStep 11591099 = 17386649) B17386649
theorem B7727399 : Blo 2289435 7727399 := bstep (se 1 (by rfl) ⟨5795549, by rfl⟩ : syracuseStep 7727399 = 11591099) B11591099
theorem B5151599 : Blo 2289435 5151599 := bstep (se 1 (by rfl) ⟨3863699, by rfl⟩ : syracuseStep 5151599 = 7727399) B7727399
theorem B3434399 : Blo 2289435 3434399 := bstep (se 1 (by rfl) ⟨2575799, by rfl⟩ : syracuseStep 3434399 = 5151599) B5151599
theorem B2289599 : Blo 2289435 2289599 := bstep (se 1 (by rfl) ⟨1717199, by rfl⟩ : syracuseStep 2289599 = 3434399) B3434399
theorem B3434405 : Blo 2289435 3434405 := bbase (se 4 (by rfl) ⟨321975, by rfl⟩ : syracuseStep 3434405 = 643951) (by norm_num)
theorem B2289603 : Blo 2289435 2289603 := bstep (se 1 (by rfl) ⟨1717202, by rfl⟩ : syracuseStep 2289603 = 3434405) B3434405
theorem B2897785 : Blo 2289435 2897785 := bbase (se 2 (by rfl) ⟨1086669, by rfl⟩ : syracuseStep 2897785 = 2173339) (by norm_num)
theorem B3863713 : Blo 2289435 3863713 := bstep (se 2 (by rfl) ⟨1448892, by rfl⟩ : syracuseStep 3863713 = 2897785) B2897785
theorem B5151617 : Blo 2289435 5151617 := bstep (se 2 (by rfl) ⟨1931856, by rfl⟩ : syracuseStep 5151617 = 3863713) B3863713
theorem B3434411 : Blo 2289435 3434411 := bstep (se 1 (by rfl) ⟨2575808, by rfl⟩ : syracuseStep 3434411 = 5151617) B5151617
theorem B2289607 : Blo 2289435 2289607 := bstep (se 1 (by rfl) ⟨1717205, by rfl⟩ : syracuseStep 2289607 = 3434411) B3434411
theorem B2575813 : Blo 2289435 2575813 := bbase (se 4 (by rfl) ⟨241482, by rfl⟩ : syracuseStep 2575813 = 482965) (by norm_num)
theorem B3434417 : Blo 2289435 3434417 := bstep (se 2 (by rfl) ⟨1287906, by rfl⟩ : syracuseStep 3434417 = 2575813) B2575813
theorem B2289611 : Blo 2289435 2289611 := bstep (se 1 (by rfl) ⟨1717208, by rfl⟩ : syracuseStep 2289611 = 3434417) B3434417
theorem B4346693 : Blo 2289435 4346693 := bbase (se 4 (by rfl) ⟨407502, by rfl⟩ : syracuseStep 4346693 = 815005) (by norm_num)
theorem B2897795 : Blo 2289435 2897795 := bstep (se 1 (by rfl) ⟨2173346, by rfl⟩ : syracuseStep 2897795 = 4346693) B4346693
theorem B7727453 : Blo 2289435 7727453 := bstep (se 3 (by rfl) ⟨1448897, by rfl⟩ : syracuseStep 7727453 = 2897795) B2897795
theorem B5151635 : Blo 2289435 5151635 := bstep (se 1 (by rfl) ⟨3863726, by rfl⟩ : syracuseStep 5151635 = 7727453) B7727453
theorem B3434423 : Blo 2289435 3434423 := bstep (se 1 (by rfl) ⟨2575817, by rfl⟩ : syracuseStep 3434423 = 5151635) B5151635
theorem B2289615 : Blo 2289435 2289615 := bstep (se 1 (by rfl) ⟨1717211, by rfl⟩ : syracuseStep 2289615 = 3434423) B3434423
theorem B3434429 : Blo 2289435 3434429 := bbase (se 3 (by rfl) ⟨643955, by rfl⟩ : syracuseStep 3434429 = 1287911) (by norm_num)
theorem B2289619 : Blo 2289435 2289619 := bstep (se 1 (by rfl) ⟨1717214, by rfl⟩ : syracuseStep 2289619 = 3434429) B3434429
theorem B5151653 : Blo 2289435 5151653 := bbase (se 4 (by rfl) ⟨482967, by rfl⟩ : syracuseStep 5151653 = 965935) (by norm_num)
theorem B3434435 : Blo 2289435 3434435 := bstep (se 1 (by rfl) ⟨2575826, by rfl⟩ : syracuseStep 3434435 = 5151653) B5151653
theorem B2289623 : Blo 2289435 2289623 := bstep (se 1 (by rfl) ⟨1717217, by rfl⟩ : syracuseStep 2289623 = 3434435) B3434435
theorem B5795621 : Blo 2289435 5795621 := bbase (se 4 (by rfl) ⟨543339, by rfl⟩ : syracuseStep 5795621 = 1086679) (by norm_num)
theorem B3863747 : Blo 2289435 3863747 := bstep (se 1 (by rfl) ⟨2897810, by rfl⟩ : syracuseStep 3863747 = 5795621) B5795621
theorem B2575831 : Blo 2289435 2575831 := bstep (se 1 (by rfl) ⟨1931873, by rfl⟩ : syracuseStep 2575831 = 3863747) B3863747
theorem B3434441 : Blo 2289435 3434441 := bstep (se 2 (by rfl) ⟨1287915, by rfl⟩ : syracuseStep 3434441 = 2575831) B2575831
theorem B2289627 : Blo 2289435 2289627 := bstep (se 1 (by rfl) ⟨1717220, by rfl⟩ : syracuseStep 2289627 = 3434441) B3434441
theorem B6520085 : Blo 2289435 6520085 := bbase (se 6 (by rfl) ⟨152814, by rfl⟩ : syracuseStep 6520085 = 305629) (by norm_num)
theorem B4346723 : Blo 2289435 4346723 := bstep (se 1 (by rfl) ⟨3260042, by rfl⟩ : syracuseStep 4346723 = 6520085) B6520085
theorem B11591261 : Blo 2289435 11591261 := bstep (se 3 (by rfl) ⟨2173361, by rfl⟩ : syracuseStep 11591261 = 4346723) B4346723
theorem B7727507 : Blo 2289435 7727507 := bstep (se 1 (by rfl) ⟨5795630, by rfl⟩ : syracuseStep 7727507 = 11591261) B11591261
theorem B5151671 : Blo 2289435 5151671 := bstep (se 1 (by rfl) ⟨3863753, by rfl⟩ : syracuseStep 5151671 = 7727507) B7727507
theorem B3434447 : Blo 2289435 3434447 := bstep (se 1 (by rfl) ⟨2575835, by rfl⟩ : syracuseStep 3434447 = 5151671) B5151671
theorem B2289631 : Blo 2289435 2289631 := bstep (se 1 (by rfl) ⟨1717223, by rfl⟩ : syracuseStep 2289631 = 3434447) B3434447
theorem B3434453 : Blo 2289435 3434453 := bbase (se 7 (by rfl) ⟨40247, by rfl⟩ : syracuseStep 3434453 = 80495) (by norm_num)
theorem B2289635 : Blo 2289435 2289635 := bstep (se 1 (by rfl) ⟨1717226, by rfl⟩ : syracuseStep 2289635 = 3434453) B3434453
theorem B8693477 : Blo 2289435 8693477 := bbase (se 4 (by rfl) ⟨815013, by rfl⟩ : syracuseStep 8693477 = 1630027) (by norm_num)
theorem B5795651 : Blo 2289435 5795651 := bstep (se 1 (by rfl) ⟨4346738, by rfl⟩ : syracuseStep 5795651 = 8693477) B8693477
theorem B3863767 : Blo 2289435 3863767 := bstep (se 1 (by rfl) ⟨2897825, by rfl⟩ : syracuseStep 3863767 = 5795651) B5795651
theorem B5151689 : Blo 2289435 5151689 := bstep (se 2 (by rfl) ⟨1931883, by rfl⟩ : syracuseStep 5151689 = 3863767) B3863767
theorem B3434459 : Blo 2289435 3434459 := bstep (se 1 (by rfl) ⟨2575844, by rfl⟩ : syracuseStep 3434459 = 5151689) B5151689
theorem B2289639 : Blo 2289435 2289639 := bstep (se 1 (by rfl) ⟨1717229, by rfl⟩ : syracuseStep 2289639 = 3434459) B3434459
theorem B2575849 : Blo 2289435 2575849 := bbase (se 2 (by rfl) ⟨965943, by rfl⟩ : syracuseStep 2575849 = 1931887) (by norm_num)
theorem B3434465 : Blo 2289435 3434465 := bstep (se 2 (by rfl) ⟨1287924, by rfl⟩ : syracuseStep 3434465 = 2575849) B2575849
theorem B2289643 : Blo 2289435 2289643 := bstep (se 1 (by rfl) ⟨1717232, by rfl⟩ : syracuseStep 2289643 = 3434465) B3434465
theorem B2445049 : Blo 2289435 2445049 := bbase (se 2 (by rfl) ⟨916893, by rfl⟩ : syracuseStep 2445049 = 1833787) (by norm_num)
theorem B13040261 : Blo 2289435 13040261 := bstep (se 4 (by rfl) ⟨1222524, by rfl⟩ : syracuseStep 13040261 = 2445049) B2445049
theorem B8693507 : Blo 2289435 8693507 := bstep (se 1 (by rfl) ⟨6520130, by rfl⟩ : syracuseStep 8693507 = 13040261) B13040261
theorem B5795671 : Blo 2289435 5795671 := bstep (se 1 (by rfl) ⟨4346753, by rfl⟩ : syracuseStep 5795671 = 8693507) B8693507
theorem B7727561 : Blo 2289435 7727561 := bstep (se 2 (by rfl) ⟨2897835, by rfl⟩ : syracuseStep 7727561 = 5795671) B5795671
theorem B5151707 : Blo 2289435 5151707 := bstep (se 1 (by rfl) ⟨3863780, by rfl⟩ : syracuseStep 5151707 = 7727561) B7727561
theorem B3434471 : Blo 2289435 3434471 := bstep (se 1 (by rfl) ⟨2575853, by rfl⟩ : syracuseStep 3434471 = 5151707) B5151707
theorem B2289647 : Blo 2289435 2289647 := bstep (se 1 (by rfl) ⟨1717235, by rfl⟩ : syracuseStep 2289647 = 3434471) B3434471
theorem B3434477 : Blo 2289435 3434477 := bbase (se 3 (by rfl) ⟨643964, by rfl⟩ : syracuseStep 3434477 = 1287929) (by norm_num)
theorem B2289651 : Blo 2289435 2289651 := bstep (se 1 (by rfl) ⟨1717238, by rfl⟩ : syracuseStep 2289651 = 3434477) B3434477
theorem B5151725 : Blo 2289435 5151725 := bbase (se 3 (by rfl) ⟨965948, by rfl⟩ : syracuseStep 5151725 = 1931897) (by norm_num)
theorem B3434483 : Blo 2289435 3434483 := bstep (se 1 (by rfl) ⟨2575862, by rfl⟩ : syracuseStep 3434483 = 5151725) B5151725
theorem B2289655 : Blo 2289435 2289655 := bstep (se 1 (by rfl) ⟨1717241, by rfl⟩ : syracuseStep 2289655 = 3434483) B3434483
theorem B4890125 : Blo 2289435 4890125 := bbase (se 3 (by rfl) ⟨916898, by rfl⟩ : syracuseStep 4890125 = 1833797) (by norm_num)
theorem B3260083 : Blo 2289435 3260083 := bstep (se 1 (by rfl) ⟨2445062, by rfl⟩ : syracuseStep 3260083 = 4890125) B4890125
theorem B4346777 : Blo 2289435 4346777 := bstep (se 2 (by rfl) ⟨1630041, by rfl⟩ : syracuseStep 4346777 = 3260083) B3260083
theorem B2897851 : Blo 2289435 2897851 := bstep (se 1 (by rfl) ⟨2173388, by rfl⟩ : syracuseStep 2897851 = 4346777) B4346777
theorem B3863801 : Blo 2289435 3863801 := bstep (se 2 (by rfl) ⟨1448925, by rfl⟩ : syracuseStep 3863801 = 2897851) B2897851
theorem B2575867 : Blo 2289435 2575867 := bstep (se 1 (by rfl) ⟨1931900, by rfl⟩ : syracuseStep 2575867 = 3863801) B3863801
theorem B3434489 : Blo 2289435 3434489 := bstep (se 2 (by rfl) ⟨1287933, by rfl⟩ : syracuseStep 3434489 = 2575867) B2575867
theorem B2289659 : Blo 2289435 2289659 := bstep (se 1 (by rfl) ⟨1717244, by rfl⟩ : syracuseStep 2289659 = 3434489) B3434489
theorem B11025797 : Blo 2289435 11025797 := bbase (se 4 (by rfl) ⟨1033668, by rfl⟩ : syracuseStep 11025797 = 2067337) (by norm_num)
theorem B117608501 : Blo 2289435 117608501 := bstep (se 5 (by rfl) ⟨5512898, by rfl⟩ : syracuseStep 117608501 = 11025797) B11025797
theorem B78405667 : Blo 2289435 78405667 := bstep (se 1 (by rfl) ⟨58804250, by rfl⟩ : syracuseStep 78405667 = 117608501) B117608501
theorem B1672654229 : Blo 2289435 1672654229 := bstep (se 6 (by rfl) ⟨39202833, by rfl⟩ : syracuseStep 1672654229 = 78405667) B78405667
theorem B1115102819 : Blo 2289435 1115102819 := bstep (se 1 (by rfl) ⟨836327114, by rfl⟩ : syracuseStep 1115102819 = 1672654229) B1672654229
theorem B2973607517 : Blo 2289435 2973607517 := bstep (se 3 (by rfl) ⟨557551409, by rfl⟩ : syracuseStep 2973607517 = 1115102819) B1115102819
theorem B1982405011 : Blo 2289435 1982405011 := bstep (se 1 (by rfl) ⟨1486803758, by rfl⟩ : syracuseStep 1982405011 = 2973607517) B2973607517
theorem B2643206681 : Blo 2289435 2643206681 := bstep (se 2 (by rfl) ⟨991202505, by rfl⟩ : syracuseStep 2643206681 = 1982405011) B1982405011
theorem B1762137787 : Blo 2289435 1762137787 := bstep (se 1 (by rfl) ⟨1321603340, by rfl⟩ : syracuseStep 1762137787 = 2643206681) B2643206681
theorem B2349517049 : Blo 2289435 2349517049 := bstep (se 2 (by rfl) ⟨881068893, by rfl⟩ : syracuseStep 2349517049 = 1762137787) B1762137787
theorem B1566344699 : Blo 2289435 1566344699 := bstep (se 1 (by rfl) ⟨1174758524, by rfl⟩ : syracuseStep 1566344699 = 2349517049) B2349517049
theorem B1044229799 : Blo 2289435 1044229799 := bstep (se 1 (by rfl) ⟨783172349, by rfl⟩ : syracuseStep 1044229799 = 1566344699) B1566344699
theorem B696153199 : Blo 2289435 696153199 := bstep (se 1 (by rfl) ⟨522114899, by rfl⟩ : syracuseStep 696153199 = 1044229799) B1044229799
theorem B928204265 : Blo 2289435 928204265 := bstep (se 2 (by rfl) ⟨348076599, by rfl⟩ : syracuseStep 928204265 = 696153199) B696153199
theorem B618802843 : Blo 2289435 618802843 := bstep (se 1 (by rfl) ⟨464102132, by rfl⟩ : syracuseStep 618802843 = 928204265) B928204265
theorem B825070457 : Blo 2289435 825070457 := bstep (se 2 (by rfl) ⟨309401421, by rfl⟩ : syracuseStep 825070457 = 618802843) B618802843
theorem B550046971 : Blo 2289435 550046971 := bstep (se 1 (by rfl) ⟨412535228, by rfl⟩ : syracuseStep 550046971 = 825070457) B825070457
theorem B733395961 : Blo 2289435 733395961 := bstep (se 2 (by rfl) ⟨275023485, by rfl⟩ : syracuseStep 733395961 = 550046971) B550046971
theorem B977861281 : Blo 2289435 977861281 := bstep (se 2 (by rfl) ⟨366697980, by rfl⟩ : syracuseStep 977861281 = 733395961) B733395961
theorem B1303815041 : Blo 2289435 1303815041 := bstep (se 2 (by rfl) ⟨488930640, by rfl⟩ : syracuseStep 1303815041 = 977861281) B977861281
theorem B869210027 : Blo 2289435 869210027 := bstep (se 1 (by rfl) ⟨651907520, by rfl⟩ : syracuseStep 869210027 = 1303815041) B1303815041
theorem B579473351 : Blo 2289435 579473351 := bstep (se 1 (by rfl) ⟨434605013, by rfl⟩ : syracuseStep 579473351 = 869210027) B869210027
theorem B386315567 : Blo 2289435 386315567 := bstep (se 1 (by rfl) ⟨289736675, by rfl⟩ : syracuseStep 386315567 = 579473351) B579473351
theorem B257543711 : Blo 2289435 257543711 := bstep (se 1 (by rfl) ⟨193157783, by rfl⟩ : syracuseStep 257543711 = 386315567) B386315567
theorem B171695807 : Blo 2289435 171695807 := bstep (se 1 (by rfl) ⟨128771855, by rfl⟩ : syracuseStep 171695807 = 257543711) B257543711
theorem B114463871 : Blo 2289435 114463871 := bstep (se 1 (by rfl) ⟨85847903, by rfl⟩ : syracuseStep 114463871 = 171695807) B171695807
theorem B76309247 : Blo 2289435 76309247 := bstep (se 1 (by rfl) ⟨57231935, by rfl⟩ : syracuseStep 76309247 = 114463871) B114463871
theorem B203491325 : Blo 2289435 203491325 := bstep (se 3 (by rfl) ⟨38154623, by rfl⟩ : syracuseStep 203491325 = 76309247) B76309247
theorem B542643533 : Blo 2289435 542643533 := bstep (se 3 (by rfl) ⟨101745662, by rfl⟩ : syracuseStep 542643533 = 203491325) B203491325
theorem B361762355 : Blo 2289435 361762355 := bstep (se 1 (by rfl) ⟨271321766, by rfl⟩ : syracuseStep 361762355 = 542643533) B542643533
theorem B241174903 : Blo 2289435 241174903 := bstep (se 1 (by rfl) ⟨180881177, by rfl⟩ : syracuseStep 241174903 = 361762355) B361762355
theorem B321566537 : Blo 2289435 321566537 := bstep (se 2 (by rfl) ⟨120587451, by rfl⟩ : syracuseStep 321566537 = 241174903) B241174903
theorem B214377691 : Blo 2289435 214377691 := bstep (se 1 (by rfl) ⟨160783268, by rfl⟩ : syracuseStep 214377691 = 321566537) B321566537
theorem B285836921 : Blo 2289435 285836921 := bstep (se 2 (by rfl) ⟨107188845, by rfl⟩ : syracuseStep 285836921 = 214377691) B214377691
theorem B190557947 : Blo 2289435 190557947 := bstep (se 1 (by rfl) ⟨142918460, by rfl⟩ : syracuseStep 190557947 = 285836921) B285836921
theorem B127038631 : Blo 2289435 127038631 := bstep (se 1 (by rfl) ⟨95278973, by rfl⟩ : syracuseStep 127038631 = 190557947) B190557947
theorem B169384841 : Blo 2289435 169384841 := bstep (se 2 (by rfl) ⟨63519315, by rfl⟩ : syracuseStep 169384841 = 127038631) B127038631
theorem B112923227 : Blo 2289435 112923227 := bstep (se 1 (by rfl) ⟨84692420, by rfl⟩ : syracuseStep 112923227 = 169384841) B169384841
theorem B75282151 : Blo 2289435 75282151 := bstep (se 1 (by rfl) ⟨56461613, by rfl⟩ : syracuseStep 75282151 = 112923227) B112923227
theorem B100376201 : Blo 2289435 100376201 := bstep (se 2 (by rfl) ⟨37641075, by rfl⟩ : syracuseStep 100376201 = 75282151) B75282151
theorem B66917467 : Blo 2289435 66917467 := bstep (se 1 (by rfl) ⟨50188100, by rfl⟩ : syracuseStep 66917467 = 100376201) B100376201
theorem B89223289 : Blo 2289435 89223289 := bstep (se 2 (by rfl) ⟨33458733, by rfl⟩ : syracuseStep 89223289 = 66917467) B66917467
theorem B475857541 : Blo 2289435 475857541 := bstep (se 4 (by rfl) ⟨44611644, by rfl⟩ : syracuseStep 475857541 = 89223289) B89223289
theorem B634476721 : Blo 2289435 634476721 := bstep (se 2 (by rfl) ⟨237928770, by rfl⟩ : syracuseStep 634476721 = 475857541) B475857541
theorem B845968961 : Blo 2289435 845968961 := bstep (se 2 (by rfl) ⟨317238360, by rfl⟩ : syracuseStep 845968961 = 634476721) B634476721
theorem B563979307 : Blo 2289435 563979307 := bstep (se 1 (by rfl) ⟨422984480, by rfl⟩ : syracuseStep 563979307 = 845968961) B845968961
theorem B751972409 : Blo 2289435 751972409 := bstep (se 2 (by rfl) ⟨281989653, by rfl⟩ : syracuseStep 751972409 = 563979307) B563979307
theorem B501314939 : Blo 2289435 501314939 := bstep (se 1 (by rfl) ⟨375986204, by rfl⟩ : syracuseStep 501314939 = 751972409) B751972409
theorem B334209959 : Blo 2289435 334209959 := bstep (se 1 (by rfl) ⟨250657469, by rfl⟩ : syracuseStep 334209959 = 501314939) B501314939
theorem B222806639 : Blo 2289435 222806639 := bstep (se 1 (by rfl) ⟨167104979, by rfl⟩ : syracuseStep 222806639 = 334209959) B334209959
theorem B148537759 : Blo 2289435 148537759 := bstep (se 1 (by rfl) ⟨111403319, by rfl⟩ : syracuseStep 148537759 = 222806639) B222806639
theorem B198050345 : Blo 2289435 198050345 := bstep (se 2 (by rfl) ⟨74268879, by rfl⟩ : syracuseStep 198050345 = 148537759) B148537759
theorem B132033563 : Blo 2289435 132033563 := bstep (se 1 (by rfl) ⟨99025172, by rfl⟩ : syracuseStep 132033563 = 198050345) B198050345
theorem B88022375 : Blo 2289435 88022375 := bstep (se 1 (by rfl) ⟨66016781, by rfl⟩ : syracuseStep 88022375 = 132033563) B132033563
theorem B58681583 : Blo 2289435 58681583 := bstep (se 1 (by rfl) ⟨44011187, by rfl⟩ : syracuseStep 58681583 = 88022375) B88022375
theorem B39121055 : Blo 2289435 39121055 := bstep (se 1 (by rfl) ⟨29340791, by rfl⟩ : syracuseStep 39121055 = 58681583) B58681583
theorem B26080703 : Blo 2289435 26080703 := bstep (se 1 (by rfl) ⟨19560527, by rfl⟩ : syracuseStep 26080703 = 39121055) B39121055
theorem B17387135 : Blo 2289435 17387135 := bstep (se 1 (by rfl) ⟨13040351, by rfl⟩ : syracuseStep 17387135 = 26080703) B26080703
theorem B11591423 : Blo 2289435 11591423 := bstep (se 1 (by rfl) ⟨8693567, by rfl⟩ : syracuseStep 11591423 = 17387135) B17387135
theorem B7727615 : Blo 2289435 7727615 := bstep (se 1 (by rfl) ⟨5795711, by rfl⟩ : syracuseStep 7727615 = 11591423) B11591423
theorem B5151743 : Blo 2289435 5151743 := bstep (se 1 (by rfl) ⟨3863807, by rfl⟩ : syracuseStep 5151743 = 7727615) B7727615
theorem B3434495 : Blo 2289435 3434495 := bstep (se 1 (by rfl) ⟨2575871, by rfl⟩ : syracuseStep 3434495 = 5151743) B5151743
theorem B2289663 : Blo 2289435 2289663 := bstep (se 1 (by rfl) ⟨1717247, by rfl⟩ : syracuseStep 2289663 = 3434495) B3434495
theorem B3434501 : Blo 2289435 3434501 := bbase (se 4 (by rfl) ⟨321984, by rfl⟩ : syracuseStep 3434501 = 643969) (by norm_num)
theorem B2289667 : Blo 2289435 2289667 := bstep (se 1 (by rfl) ⟨1717250, by rfl⟩ : syracuseStep 2289667 = 3434501) B3434501
theorem B3863821 : Blo 2289435 3863821 := bbase (se 3 (by rfl) ⟨724466, by rfl⟩ : syracuseStep 3863821 = 1448933) (by norm_num)
theorem B5151761 : Blo 2289435 5151761 := bstep (se 2 (by rfl) ⟨1931910, by rfl⟩ : syracuseStep 5151761 = 3863821) B3863821
theorem B3434507 : Blo 2289435 3434507 := bstep (se 1 (by rfl) ⟨2575880, by rfl⟩ : syracuseStep 3434507 = 5151761) B5151761
theorem B2289671 : Blo 2289435 2289671 := bstep (se 1 (by rfl) ⟨1717253, by rfl⟩ : syracuseStep 2289671 = 3434507) B3434507
theorem B2575885 : Blo 2289435 2575885 := bbase (se 3 (by rfl) ⟨482978, by rfl⟩ : syracuseStep 2575885 = 965957) (by norm_num)
theorem B3434513 : Blo 2289435 3434513 := bstep (se 2 (by rfl) ⟨1287942, by rfl⟩ : syracuseStep 3434513 = 2575885) B2575885
theorem B2289675 : Blo 2289435 2289675 := bstep (se 1 (by rfl) ⟨1717256, by rfl⟩ : syracuseStep 2289675 = 3434513) B3434513
theorem B7727669 : Blo 2289435 7727669 := bbase (se 5 (by rfl) ⟨362234, by rfl⟩ : syracuseStep 7727669 = 724469) (by norm_num)
theorem B5151779 : Blo 2289435 5151779 := bstep (se 1 (by rfl) ⟨3863834, by rfl⟩ : syracuseStep 5151779 = 7727669) B7727669
theorem B3434519 : Blo 2289435 3434519 := bstep (se 1 (by rfl) ⟨2575889, by rfl⟩ : syracuseStep 3434519 = 5151779) B5151779
theorem B2289679 : Blo 2289435 2289679 := bstep (se 1 (by rfl) ⟨1717259, by rfl⟩ : syracuseStep 2289679 = 3434519) B3434519
theorem B3434525 : Blo 2289435 3434525 := bbase (se 3 (by rfl) ⟨643973, by rfl⟩ : syracuseStep 3434525 = 1287947) (by norm_num)
theorem B2289683 : Blo 2289435 2289683 := bstep (se 1 (by rfl) ⟨1717262, by rfl⟩ : syracuseStep 2289683 = 3434525) B3434525
theorem B5151797 : Blo 2289435 5151797 := bbase (se 5 (by rfl) ⟨241490, by rfl⟩ : syracuseStep 5151797 = 482981) (by norm_num)
theorem B3434531 : Blo 2289435 3434531 := bstep (se 1 (by rfl) ⟨2575898, by rfl⟩ : syracuseStep 3434531 = 5151797) B5151797
theorem B2289687 : Blo 2289435 2289687 := bstep (se 1 (by rfl) ⟨1717265, by rfl⟩ : syracuseStep 2289687 = 3434531) B3434531
theorem B3717685 : Blo 2289435 3717685 := bbase (se 5 (by rfl) ⟨174266, by rfl⟩ : syracuseStep 3717685 = 348533) (by norm_num)
theorem B4956913 : Blo 2289435 4956913 := bstep (se 2 (by rfl) ⟨1858842, by rfl⟩ : syracuseStep 4956913 = 3717685) B3717685
theorem B6609217 : Blo 2289435 6609217 := bstep (se 2 (by rfl) ⟨2478456, by rfl⟩ : syracuseStep 6609217 = 4956913) B4956913
theorem B8812289 : Blo 2289435 8812289 := bstep (se 2 (by rfl) ⟨3304608, by rfl⟩ : syracuseStep 8812289 = 6609217) B6609217
theorem B5874859 : Blo 2289435 5874859 := bstep (se 1 (by rfl) ⟨4406144, by rfl⟩ : syracuseStep 5874859 = 8812289) B8812289
theorem B31332581 : Blo 2289435 31332581 := bstep (se 4 (by rfl) ⟨2937429, by rfl⟩ : syracuseStep 31332581 = 5874859) B5874859
theorem B20888387 : Blo 2289435 20888387 := bstep (se 1 (by rfl) ⟨15666290, by rfl⟩ : syracuseStep 20888387 = 31332581) B31332581
theorem B13925591 : Blo 2289435 13925591 := bstep (se 1 (by rfl) ⟨10444193, by rfl⟩ : syracuseStep 13925591 = 20888387) B20888387
theorem B9283727 : Blo 2289435 9283727 := bstep (se 1 (by rfl) ⟨6962795, by rfl⟩ : syracuseStep 9283727 = 13925591) B13925591
theorem B6189151 : Blo 2289435 6189151 := bstep (se 1 (by rfl) ⟨4641863, by rfl⟩ : syracuseStep 6189151 = 9283727) B9283727
theorem B8252201 : Blo 2289435 8252201 := bstep (se 2 (by rfl) ⟨3094575, by rfl⟩ : syracuseStep 8252201 = 6189151) B6189151
theorem B5501467 : Blo 2289435 5501467 := bstep (se 1 (by rfl) ⟨4126100, by rfl⟩ : syracuseStep 5501467 = 8252201) B8252201
theorem B7335289 : Blo 2289435 7335289 := bstep (se 2 (by rfl) ⟨2750733, by rfl⟩ : syracuseStep 7335289 = 5501467) B5501467
theorem B9780385 : Blo 2289435 9780385 := bstep (se 2 (by rfl) ⟨3667644, by rfl⟩ : syracuseStep 9780385 = 7335289) B7335289
theorem B13040513 : Blo 2289435 13040513 := bstep (se 2 (by rfl) ⟨4890192, by rfl⟩ : syracuseStep 13040513 = 9780385) B9780385
theorem B8693675 : Blo 2289435 8693675 := bstep (se 1 (by rfl) ⟨6520256, by rfl⟩ : syracuseStep 8693675 = 13040513) B13040513
theorem B5795783 : Blo 2289435 5795783 := bstep (se 1 (by rfl) ⟨4346837, by rfl⟩ : syracuseStep 5795783 = 8693675) B8693675
theorem B3863855 : Blo 2289435 3863855 := bstep (se 1 (by rfl) ⟨2897891, by rfl⟩ : syracuseStep 3863855 = 5795783) B5795783
theorem B2575903 : Blo 2289435 2575903 := bstep (se 1 (by rfl) ⟨1931927, by rfl⟩ : syracuseStep 2575903 = 3863855) B3863855
theorem B3434537 : Blo 2289435 3434537 := bstep (se 2 (by rfl) ⟨1287951, by rfl⟩ : syracuseStep 3434537 = 2575903) B2575903
theorem B2289691 : Blo 2289435 2289691 := bstep (se 1 (by rfl) ⟨1717268, by rfl⟩ : syracuseStep 2289691 = 3434537) B3434537
theorem B7335301 : Blo 2289435 7335301 := bbase (se 4 (by rfl) ⟨687684, by rfl⟩ : syracuseStep 7335301 = 1375369) (by norm_num)
theorem B9780401 : Blo 2289435 9780401 := bstep (se 2 (by rfl) ⟨3667650, by rfl⟩ : syracuseStep 9780401 = 7335301) B7335301
theorem B6520267 : Blo 2289435 6520267 := bstep (se 1 (by rfl) ⟨4890200, by rfl⟩ : syracuseStep 6520267 = 9780401) B9780401
theorem B8693689 : Blo 2289435 8693689 := bstep (se 2 (by rfl) ⟨3260133, by rfl⟩ : syracuseStep 8693689 = 6520267) B6520267
theorem B11591585 : Blo 2289435 11591585 := bstep (se 2 (by rfl) ⟨4346844, by rfl⟩ : syracuseStep 11591585 = 8693689) B8693689
theorem B7727723 : Blo 2289435 7727723 := bstep (se 1 (by rfl) ⟨5795792, by rfl⟩ : syracuseStep 7727723 = 11591585) B11591585
theorem B5151815 : Blo 2289435 5151815 := bstep (se 1 (by rfl) ⟨3863861, by rfl⟩ : syracuseStep 5151815 = 7727723) B7727723
theorem B3434543 : Blo 2289435 3434543 := bstep (se 1 (by rfl) ⟨2575907, by rfl⟩ : syracuseStep 3434543 = 5151815) B5151815
theorem B2289695 : Blo 2289435 2289695 := bstep (se 1 (by rfl) ⟨1717271, by rfl⟩ : syracuseStep 2289695 = 3434543) B3434543
theorem B3434549 : Blo 2289435 3434549 := bbase (se 5 (by rfl) ⟨160994, by rfl⟩ : syracuseStep 3434549 = 321989) (by norm_num)
theorem B2289699 : Blo 2289435 2289699 := bstep (se 1 (by rfl) ⟨1717274, by rfl⟩ : syracuseStep 2289699 = 3434549) B3434549
theorem B5795813 : Blo 2289435 5795813 := bbase (se 4 (by rfl) ⟨543357, by rfl⟩ : syracuseStep 5795813 = 1086715) (by norm_num)
theorem B3863875 : Blo 2289435 3863875 := bstep (se 1 (by rfl) ⟨2897906, by rfl⟩ : syracuseStep 3863875 = 5795813) B5795813
theorem B5151833 : Blo 2289435 5151833 := bstep (se 2 (by rfl) ⟨1931937, by rfl⟩ : syracuseStep 5151833 = 3863875) B3863875
theorem B3434555 : Blo 2289435 3434555 := bstep (se 1 (by rfl) ⟨2575916, by rfl⟩ : syracuseStep 3434555 = 5151833) B5151833
theorem B2289703 : Blo 2289435 2289703 := bstep (se 1 (by rfl) ⟨1717277, by rfl⟩ : syracuseStep 2289703 = 3434555) B3434555
theorem B2575921 : Blo 2289435 2575921 := bbase (se 2 (by rfl) ⟨965970, by rfl⟩ : syracuseStep 2575921 = 1931941) (by norm_num)
theorem B3434561 : Blo 2289435 3434561 := bstep (se 2 (by rfl) ⟨1287960, by rfl⟩ : syracuseStep 3434561 = 2575921) B2575921
theorem B2289707 : Blo 2289435 2289707 := bstep (se 1 (by rfl) ⟨1717280, by rfl⟩ : syracuseStep 2289707 = 3434561) B3434561
theorem B6189205 : Blo 2289435 6189205 := bbase (se 6 (by rfl) ⟨145059, by rfl⟩ : syracuseStep 6189205 = 290119) (by norm_num)
theorem B8252273 : Blo 2289435 8252273 := bstep (se 2 (by rfl) ⟨3094602, by rfl⟩ : syracuseStep 8252273 = 6189205) B6189205
theorem B5501515 : Blo 2289435 5501515 := bstep (se 1 (by rfl) ⟨4126136, by rfl⟩ : syracuseStep 5501515 = 8252273) B8252273
theorem B7335353 : Blo 2289435 7335353 := bstep (se 2 (by rfl) ⟨2750757, by rfl⟩ : syracuseStep 7335353 = 5501515) B5501515
theorem B4890235 : Blo 2289435 4890235 := bstep (se 1 (by rfl) ⟨3667676, by rfl⟩ : syracuseStep 4890235 = 7335353) B7335353
theorem B6520313 : Blo 2289435 6520313 := bstep (se 2 (by rfl) ⟨2445117, by rfl⟩ : syracuseStep 6520313 = 4890235) B4890235
theorem B4346875 : Blo 2289435 4346875 := bstep (se 1 (by rfl) ⟨3260156, by rfl⟩ : syracuseStep 4346875 = 6520313) B6520313
theorem B5795833 : Blo 2289435 5795833 := bstep (se 2 (by rfl) ⟨2173437, by rfl⟩ : syracuseStep 5795833 = 4346875) B4346875
theorem B7727777 : Blo 2289435 7727777 := bstep (se 2 (by rfl) ⟨2897916, by rfl⟩ : syracuseStep 7727777 = 5795833) B5795833
theorem B5151851 : Blo 2289435 5151851 := bstep (se 1 (by rfl) ⟨3863888, by rfl⟩ : syracuseStep 5151851 = 7727777) B7727777
theorem B3434567 : Blo 2289435 3434567 := bstep (se 1 (by rfl) ⟨2575925, by rfl⟩ : syracuseStep 3434567 = 5151851) B5151851
theorem B2289711 : Blo 2289435 2289711 := bstep (se 1 (by rfl) ⟨1717283, by rfl⟩ : syracuseStep 2289711 = 3434567) B3434567
theorem B3434573 : Blo 2289435 3434573 := bbase (se 3 (by rfl) ⟨643982, by rfl⟩ : syracuseStep 3434573 = 1287965) (by norm_num)
theorem B2289715 : Blo 2289435 2289715 := bstep (se 1 (by rfl) ⟨1717286, by rfl⟩ : syracuseStep 2289715 = 3434573) B3434573
theorem B5151869 : Blo 2289435 5151869 := bbase (se 3 (by rfl) ⟨965975, by rfl⟩ : syracuseStep 5151869 = 1931951) (by norm_num)
theorem B3434579 : Blo 2289435 3434579 := bstep (se 1 (by rfl) ⟨2575934, by rfl⟩ : syracuseStep 3434579 = 5151869) B5151869
theorem B2289719 : Blo 2289435 2289719 := bstep (se 1 (by rfl) ⟨1717289, by rfl⟩ : syracuseStep 2289719 = 3434579) B3434579
theorem B3863909 : Blo 2289435 3863909 := bbase (se 4 (by rfl) ⟨362241, by rfl⟩ : syracuseStep 3863909 = 724483) (by norm_num)
theorem B2575939 : Blo 2289435 2575939 := bstep (se 1 (by rfl) ⟨1931954, by rfl⟩ : syracuseStep 2575939 = 3863909) B3863909
theorem B3434585 : Blo 2289435 3434585 := bstep (se 2 (by rfl) ⟨1287969, by rfl⟩ : syracuseStep 3434585 = 2575939) B2575939
theorem B2289723 : Blo 2289435 2289723 := bstep (se 1 (by rfl) ⟨1717292, by rfl⟩ : syracuseStep 2289723 = 3434585) B3434585
theorem B4890269 : Blo 2289435 4890269 := bbase (se 3 (by rfl) ⟨916925, by rfl⟩ : syracuseStep 4890269 = 1833851) (by norm_num)
theorem B3260179 : Blo 2289435 3260179 := bstep (se 1 (by rfl) ⟨2445134, by rfl⟩ : syracuseStep 3260179 = 4890269) B4890269
theorem B17387621 : Blo 2289435 17387621 := bstep (se 4 (by rfl) ⟨1630089, by rfl⟩ : syracuseStep 17387621 = 3260179) B3260179
theorem B11591747 : Blo 2289435 11591747 := bstep (se 1 (by rfl) ⟨8693810, by rfl⟩ : syracuseStep 11591747 = 17387621) B17387621
theorem B7727831 : Blo 2289435 7727831 := bstep (se 1 (by rfl) ⟨5795873, by rfl⟩ : syracuseStep 7727831 = 11591747) B11591747
theorem B5151887 : Blo 2289435 5151887 := bstep (se 1 (by rfl) ⟨3863915, by rfl⟩ : syracuseStep 5151887 = 7727831) B7727831
theorem B3434591 : Blo 2289435 3434591 := bstep (se 1 (by rfl) ⟨2575943, by rfl⟩ : syracuseStep 3434591 = 5151887) B5151887
theorem B2289727 : Blo 2289435 2289727 := bstep (se 1 (by rfl) ⟨1717295, by rfl⟩ : syracuseStep 2289727 = 3434591) B3434591
theorem B3434597 : Blo 2289435 3434597 := bbase (se 4 (by rfl) ⟨321993, by rfl⟩ : syracuseStep 3434597 = 643987) (by norm_num)
theorem B2289731 : Blo 2289435 2289731 := bstep (se 1 (by rfl) ⟨1717298, by rfl⟩ : syracuseStep 2289731 = 3434597) B3434597
theorem B9914021 : Blo 2289435 9914021 := bbase (se 4 (by rfl) ⟨929439, by rfl⟩ : syracuseStep 9914021 = 1858879) (by norm_num)
theorem B6609347 : Blo 2289435 6609347 := bstep (se 1 (by rfl) ⟨4957010, by rfl⟩ : syracuseStep 6609347 = 9914021) B9914021
theorem B4406231 : Blo 2289435 4406231 := bstep (se 1 (by rfl) ⟨3304673, by rfl⟩ : syracuseStep 4406231 = 6609347) B6609347
theorem B2937487 : Blo 2289435 2937487 := bstep (se 1 (by rfl) ⟨2203115, by rfl⟩ : syracuseStep 2937487 = 4406231) B4406231
theorem B3916649 : Blo 2289435 3916649 := bstep (se 2 (by rfl) ⟨1468743, by rfl⟩ : syracuseStep 3916649 = 2937487) B2937487
theorem B2611099 : Blo 2289435 2611099 := bstep (se 1 (by rfl) ⟨1958324, by rfl⟩ : syracuseStep 2611099 = 3916649) B3916649
theorem B3481465 : Blo 2289435 3481465 := bstep (se 2 (by rfl) ⟨1305549, by rfl⟩ : syracuseStep 3481465 = 2611099) B2611099
theorem B4641953 : Blo 2289435 4641953 := bstep (se 2 (by rfl) ⟨1740732, by rfl⟩ : syracuseStep 4641953 = 3481465) B3481465
theorem B12378541 : Blo 2289435 12378541 := bstep (se 3 (by rfl) ⟨2320976, by rfl⟩ : syracuseStep 12378541 = 4641953) B4641953
theorem B16504721 : Blo 2289435 16504721 := bstep (se 2 (by rfl) ⟨6189270, by rfl⟩ : syracuseStep 16504721 = 12378541) B12378541
theorem B11003147 : Blo 2289435 11003147 := bstep (se 1 (by rfl) ⟨8252360, by rfl⟩ : syracuseStep 11003147 = 16504721) B16504721
theorem B7335431 : Blo 2289435 7335431 := bstep (se 1 (by rfl) ⟨5501573, by rfl⟩ : syracuseStep 7335431 = 11003147) B11003147
theorem B4890287 : Blo 2289435 4890287 := bstep (se 1 (by rfl) ⟨3667715, by rfl⟩ : syracuseStep 4890287 = 7335431) B7335431
theorem B3260191 : Blo 2289435 3260191 := bstep (se 1 (by rfl) ⟨2445143, by rfl⟩ : syracuseStep 3260191 = 4890287) B4890287
theorem B4346921 : Blo 2289435 4346921 := bstep (se 2 (by rfl) ⟨1630095, by rfl⟩ : syracuseStep 4346921 = 3260191) B3260191
theorem B2897947 : Blo 2289435 2897947 := bstep (se 1 (by rfl) ⟨2173460, by rfl⟩ : syracuseStep 2897947 = 4346921) B4346921
theorem B3863929 : Blo 2289435 3863929 := bstep (se 2 (by rfl) ⟨1448973, by rfl⟩ : syracuseStep 3863929 = 2897947) B2897947
theorem B5151905 : Blo 2289435 5151905 := bstep (se 2 (by rfl) ⟨1931964, by rfl⟩ : syracuseStep 5151905 = 3863929) B3863929
theorem B3434603 : Blo 2289435 3434603 := bstep (se 1 (by rfl) ⟨2575952, by rfl⟩ : syracuseStep 3434603 = 5151905) B5151905
theorem B2289735 : Blo 2289435 2289735 := bstep (se 1 (by rfl) ⟨1717301, by rfl⟩ : syracuseStep 2289735 = 3434603) B3434603
theorem B2575957 : Blo 2289435 2575957 := bbase (se 8 (by rfl) ⟨15093, by rfl⟩ : syracuseStep 2575957 = 30187) (by norm_num)
theorem B3434609 : Blo 2289435 3434609 := bstep (se 2 (by rfl) ⟨1287978, by rfl⟩ : syracuseStep 3434609 = 2575957) B2575957
theorem B2289739 : Blo 2289435 2289739 := bstep (se 1 (by rfl) ⟨1717304, by rfl⟩ : syracuseStep 2289739 = 3434609) B3434609
theorem B2897957 : Blo 2289435 2897957 := bbase (se 4 (by rfl) ⟨271683, by rfl⟩ : syracuseStep 2897957 = 543367) (by norm_num)
theorem B7727885 : Blo 2289435 7727885 := bstep (se 3 (by rfl) ⟨1448978, by rfl⟩ : syracuseStep 7727885 = 2897957) B2897957
theorem B5151923 : Blo 2289435 5151923 := bstep (se 1 (by rfl) ⟨3863942, by rfl⟩ : syracuseStep 5151923 = 7727885) B7727885
theorem B3434615 : Blo 2289435 3434615 := bstep (se 1 (by rfl) ⟨2575961, by rfl⟩ : syracuseStep 3434615 = 5151923) B5151923
theorem B2289743 : Blo 2289435 2289743 := bstep (se 1 (by rfl) ⟨1717307, by rfl⟩ : syracuseStep 2289743 = 3434615) B3434615
theorem B3434621 : Blo 2289435 3434621 := bbase (se 3 (by rfl) ⟨643991, by rfl⟩ : syracuseStep 3434621 = 1287983) (by norm_num)
theorem B2289747 : Blo 2289435 2289747 := bstep (se 1 (by rfl) ⟨1717310, by rfl⟩ : syracuseStep 2289747 = 3434621) B3434621
theorem B5151941 : Blo 2289435 5151941 := bbase (se 4 (by rfl) ⟨482994, by rfl⟩ : syracuseStep 5151941 = 965989) (by norm_num)
theorem B3434627 : Blo 2289435 3434627 := bstep (se 1 (by rfl) ⟨2575970, by rfl⟩ : syracuseStep 3434627 = 5151941) B5151941
theorem B2289751 : Blo 2289435 2289751 := bstep (se 1 (by rfl) ⟨1717313, by rfl⟩ : syracuseStep 2289751 = 3434627) B3434627
theorem B5501621 : Blo 2289435 5501621 := bbase (se 5 (by rfl) ⟨257888, by rfl⟩ : syracuseStep 5501621 = 515777) (by norm_num)
theorem B14670989 : Blo 2289435 14670989 := bstep (se 3 (by rfl) ⟨2750810, by rfl⟩ : syracuseStep 14670989 = 5501621) B5501621
theorem B9780659 : Blo 2289435 9780659 := bstep (se 1 (by rfl) ⟨7335494, by rfl⟩ : syracuseStep 9780659 = 14670989) B14670989
theorem B6520439 : Blo 2289435 6520439 := bstep (se 1 (by rfl) ⟨4890329, by rfl⟩ : syracuseStep 6520439 = 9780659) B9780659
theorem B4346959 : Blo 2289435 4346959 := bstep (se 1 (by rfl) ⟨3260219, by rfl⟩ : syracuseStep 4346959 = 6520439) B6520439
theorem B5795945 : Blo 2289435 5795945 := bstep (se 2 (by rfl) ⟨2173479, by rfl⟩ : syracuseStep 5795945 = 4346959) B4346959
theorem B3863963 : Blo 2289435 3863963 := bstep (se 1 (by rfl) ⟨2897972, by rfl⟩ : syracuseStep 3863963 = 5795945) B5795945
theorem B2575975 : Blo 2289435 2575975 := bstep (se 1 (by rfl) ⟨1931981, by rfl⟩ : syracuseStep 2575975 = 3863963) B3863963
theorem B3434633 : Blo 2289435 3434633 := bstep (se 2 (by rfl) ⟨1287987, by rfl⟩ : syracuseStep 3434633 = 2575975) B2575975
theorem B2289755 : Blo 2289435 2289755 := bstep (se 1 (by rfl) ⟨1717316, by rfl⟩ : syracuseStep 2289755 = 3434633) B3434633
theorem B11591909 : Blo 2289435 11591909 := bbase (se 4 (by rfl) ⟨1086741, by rfl⟩ : syracuseStep 11591909 = 2173483) (by norm_num)
theorem B7727939 : Blo 2289435 7727939 := bstep (se 1 (by rfl) ⟨5795954, by rfl⟩ : syracuseStep 7727939 = 11591909) B11591909
theorem B5151959 : Blo 2289435 5151959 := bstep (se 1 (by rfl) ⟨3863969, by rfl⟩ : syracuseStep 5151959 = 7727939) B7727939
theorem B3434639 : Blo 2289435 3434639 := bstep (se 1 (by rfl) ⟨2575979, by rfl⟩ : syracuseStep 3434639 = 5151959) B5151959
theorem B2289759 : Blo 2289435 2289759 := bstep (se 1 (by rfl) ⟨1717319, by rfl⟩ : syracuseStep 2289759 = 3434639) B3434639
theorem B3434645 : Blo 2289435 3434645 := bbase (se 6 (by rfl) ⟨80499, by rfl⟩ : syracuseStep 3434645 = 160999) (by norm_num)
theorem B2289763 : Blo 2289435 2289763 := bstep (se 1 (by rfl) ⟨1717322, by rfl⟩ : syracuseStep 2289763 = 3434645) B3434645
theorem B9780709 : Blo 2289435 9780709 := bbase (se 4 (by rfl) ⟨916941, by rfl⟩ : syracuseStep 9780709 = 1833883) (by norm_num)
theorem B13040945 : Blo 2289435 13040945 := bstep (se 2 (by rfl) ⟨4890354, by rfl⟩ : syracuseStep 13040945 = 9780709) B9780709
theorem B8693963 : Blo 2289435 8693963 := bstep (se 1 (by rfl) ⟨6520472, by rfl⟩ : syracuseStep 8693963 = 13040945) B13040945
theorem B5795975 : Blo 2289435 5795975 := bstep (se 1 (by rfl) ⟨4346981, by rfl⟩ : syracuseStep 5795975 = 8693963) B8693963
theorem B3863983 : Blo 2289435 3863983 := bstep (se 1 (by rfl) ⟨2897987, by rfl⟩ : syracuseStep 3863983 = 5795975) B5795975
theorem B5151977 : Blo 2289435 5151977 := bstep (se 2 (by rfl) ⟨1931991, by rfl⟩ : syracuseStep 5151977 = 3863983) B3863983
theorem B3434651 : Blo 2289435 3434651 := bstep (se 1 (by rfl) ⟨2575988, by rfl⟩ : syracuseStep 3434651 = 5151977) B5151977
theorem B2289767 : Blo 2289435 2289767 := bstep (se 1 (by rfl) ⟨1717325, by rfl⟩ : syracuseStep 2289767 = 3434651) B3434651
theorem B2575993 : Blo 2289435 2575993 := bbase (se 2 (by rfl) ⟨965997, by rfl⟩ : syracuseStep 2575993 = 1931995) (by norm_num)
theorem B3434657 : Blo 2289435 3434657 := bstep (se 2 (by rfl) ⟨1287996, by rfl⟩ : syracuseStep 3434657 = 2575993) B2575993
theorem B2289771 : Blo 2289435 2289771 := bstep (se 1 (by rfl) ⟨1717328, by rfl⟩ : syracuseStep 2289771 = 3434657) B3434657
theorem B3481525 : Blo 2289435 3481525 := bbase (se 5 (by rfl) ⟨163196, by rfl⟩ : syracuseStep 3481525 = 326393) (by norm_num)
theorem B4642033 : Blo 2289435 4642033 := bstep (se 2 (by rfl) ⟨1740762, by rfl⟩ : syracuseStep 4642033 = 3481525) B3481525
theorem B6189377 : Blo 2289435 6189377 := bstep (se 2 (by rfl) ⟨2321016, by rfl⟩ : syracuseStep 6189377 = 4642033) B4642033
theorem B16505005 : Blo 2289435 16505005 := bstep (se 3 (by rfl) ⟨3094688, by rfl⟩ : syracuseStep 16505005 = 6189377) B6189377
theorem B22006673 : Blo 2289435 22006673 := bstep (se 2 (by rfl) ⟨8252502, by rfl⟩ : syracuseStep 22006673 = 16505005) B16505005
theorem B14671115 : Blo 2289435 14671115 := bstep (se 1 (by rfl) ⟨11003336, by rfl⟩ : syracuseStep 14671115 = 22006673) B22006673
theorem B9780743 : Blo 2289435 9780743 := bstep (se 1 (by rfl) ⟨7335557, by rfl⟩ : syracuseStep 9780743 = 14671115) B14671115
theorem B6520495 : Blo 2289435 6520495 := bstep (se 1 (by rfl) ⟨4890371, by rfl⟩ : syracuseStep 6520495 = 9780743) B9780743
theorem B8693993 : Blo 2289435 8693993 := bstep (se 2 (by rfl) ⟨3260247, by rfl⟩ : syracuseStep 8693993 = 6520495) B6520495
theorem B5795995 : Blo 2289435 5795995 := bstep (se 1 (by rfl) ⟨4346996, by rfl⟩ : syracuseStep 5795995 = 8693993) B8693993
theorem B7727993 : Blo 2289435 7727993 := bstep (se 2 (by rfl) ⟨2897997, by rfl⟩ : syracuseStep 7727993 = 5795995) B5795995
theorem B5151995 : Blo 2289435 5151995 := bstep (se 1 (by rfl) ⟨3863996, by rfl⟩ : syracuseStep 5151995 = 7727993) B7727993
theorem B3434663 : Blo 2289435 3434663 := bstep (se 1 (by rfl) ⟨2575997, by rfl⟩ : syracuseStep 3434663 = 5151995) B5151995
theorem B2289775 : Blo 2289435 2289775 := bstep (se 1 (by rfl) ⟨1717331, by rfl⟩ : syracuseStep 2289775 = 3434663) B3434663
theorem B3434669 : Blo 2289435 3434669 := bbase (se 3 (by rfl) ⟨644000, by rfl⟩ : syracuseStep 3434669 = 1288001) (by norm_num)
theorem B2289779 : Blo 2289435 2289779 := bstep (se 1 (by rfl) ⟨1717334, by rfl⟩ : syracuseStep 2289779 = 3434669) B3434669
theorem B5152013 : Blo 2289435 5152013 := bbase (se 3 (by rfl) ⟨966002, by rfl⟩ : syracuseStep 5152013 = 1932005) (by norm_num)
theorem B3434675 : Blo 2289435 3434675 := bstep (se 1 (by rfl) ⟨2576006, by rfl⟩ : syracuseStep 3434675 = 5152013) B5152013
theorem B2289783 : Blo 2289435 2289783 := bstep (se 1 (by rfl) ⟨1717337, by rfl⟩ : syracuseStep 2289783 = 3434675) B3434675
theorem B2898013 : Blo 2289435 2898013 := bbase (se 3 (by rfl) ⟨543377, by rfl⟩ : syracuseStep 2898013 = 1086755) (by norm_num)
theorem B3864017 : Blo 2289435 3864017 := bstep (se 2 (by rfl) ⟨1449006, by rfl⟩ : syracuseStep 3864017 = 2898013) B2898013
theorem B2576011 : Blo 2289435 2576011 := bstep (se 1 (by rfl) ⟨1932008, by rfl⟩ : syracuseStep 2576011 = 3864017) B3864017
theorem B3434681 : Blo 2289435 3434681 := bstep (se 2 (by rfl) ⟨1288005, by rfl⟩ : syracuseStep 3434681 = 2576011) B2576011
theorem B2289787 : Blo 2289435 2289787 := bstep (se 1 (by rfl) ⟨1717340, by rfl⟩ : syracuseStep 2289787 = 3434681) B3434681
theorem B19561621 : Blo 2289435 19561621 := bbase (se 6 (by rfl) ⟨458475, by rfl⟩ : syracuseStep 19561621 = 916951) (by norm_num)
theorem B26082161 : Blo 2289435 26082161 := bstep (se 2 (by rfl) ⟨9780810, by rfl⟩ : syracuseStep 26082161 = 19561621) B19561621
theorem B17388107 : Blo 2289435 17388107 := bstep (se 1 (by rfl) ⟨13041080, by rfl⟩ : syracuseStep 17388107 = 26082161) B26082161
theorem B11592071 : Blo 2289435 11592071 := bstep (se 1 (by rfl) ⟨8694053, by rfl⟩ : syracuseStep 11592071 = 17388107) B17388107
theorem B7728047 : Blo 2289435 7728047 := bstep (se 1 (by rfl) ⟨5796035, by rfl⟩ : syracuseStep 7728047 = 11592071) B11592071
theorem B5152031 : Blo 2289435 5152031 := bstep (se 1 (by rfl) ⟨3864023, by rfl⟩ : syracuseStep 5152031 = 7728047) B7728047
theorem B3434687 : Blo 2289435 3434687 := bstep (se 1 (by rfl) ⟨2576015, by rfl⟩ : syracuseStep 3434687 = 5152031) B5152031
theorem B2289791 : Blo 2289435 2289791 := bstep (se 1 (by rfl) ⟨1717343, by rfl⟩ : syracuseStep 2289791 = 3434687) B3434687
theorem B3434693 : Blo 2289435 3434693 := bbase (se 4 (by rfl) ⟨322002, by rfl⟩ : syracuseStep 3434693 = 644005) (by norm_num)
theorem B2289795 : Blo 2289435 2289795 := bstep (se 1 (by rfl) ⟨1717346, by rfl⟩ : syracuseStep 2289795 = 3434693) B3434693
theorem B3864037 : Blo 2289435 3864037 := bbase (se 4 (by rfl) ⟨362253, by rfl⟩ : syracuseStep 3864037 = 724507) (by norm_num)
theorem B5152049 : Blo 2289435 5152049 := bstep (se 2 (by rfl) ⟨1932018, by rfl⟩ : syracuseStep 5152049 = 3864037) B3864037
theorem B3434699 : Blo 2289435 3434699 := bstep (se 1 (by rfl) ⟨2576024, by rfl⟩ : syracuseStep 3434699 = 5152049) B5152049
theorem B2289799 : Blo 2289435 2289799 := bstep (se 1 (by rfl) ⟨1717349, by rfl⟩ : syracuseStep 2289799 = 3434699) B3434699
theorem B2576029 : Blo 2289435 2576029 := bbase (se 3 (by rfl) ⟨483005, by rfl⟩ : syracuseStep 2576029 = 966011) (by norm_num)
theorem B3434705 : Blo 2289435 3434705 := bstep (se 2 (by rfl) ⟨1288014, by rfl⟩ : syracuseStep 3434705 = 2576029) B2576029
theorem B2289803 : Blo 2289435 2289803 := bstep (se 1 (by rfl) ⟨1717352, by rfl⟩ : syracuseStep 2289803 = 3434705) B3434705
theorem B7728101 : Blo 2289435 7728101 := bbase (se 4 (by rfl) ⟨724509, by rfl⟩ : syracuseStep 7728101 = 1449019) (by norm_num)
theorem B5152067 : Blo 2289435 5152067 := bstep (se 1 (by rfl) ⟨3864050, by rfl⟩ : syracuseStep 5152067 = 7728101) B7728101
theorem B3434711 : Blo 2289435 3434711 := bstep (se 1 (by rfl) ⟨2576033, by rfl⟩ : syracuseStep 3434711 = 5152067) B5152067
theorem B2289807 : Blo 2289435 2289807 := bstep (se 1 (by rfl) ⟨1717355, by rfl⟩ : syracuseStep 2289807 = 3434711) B3434711
theorem B3434717 : Blo 2289435 3434717 := bbase (se 3 (by rfl) ⟨644009, by rfl⟩ : syracuseStep 3434717 = 1288019) (by norm_num)
theorem B2289811 : Blo 2289435 2289811 := bstep (se 1 (by rfl) ⟨1717358, by rfl⟩ : syracuseStep 2289811 = 3434717) B3434717
theorem B5152085 : Blo 2289435 5152085 := bbase (se 11 (by rfl) ⟨3773, by rfl⟩ : syracuseStep 5152085 = 7547) (by norm_num)
theorem B3434723 : Blo 2289435 3434723 := bstep (se 1 (by rfl) ⟨2576042, by rfl⟩ : syracuseStep 3434723 = 5152085) B5152085
theorem B2289815 : Blo 2289435 2289815 := bstep (se 1 (by rfl) ⟨1717361, by rfl⟩ : syracuseStep 2289815 = 3434723) B3434723
theorem B2445233 : Blo 2289435 2445233 := bbase (se 2 (by rfl) ⟨916962, by rfl⟩ : syracuseStep 2445233 = 1833925) (by norm_num)
theorem B6520621 : Blo 2289435 6520621 := bstep (se 3 (by rfl) ⟨1222616, by rfl⟩ : syracuseStep 6520621 = 2445233) B2445233
theorem B8694161 : Blo 2289435 8694161 := bstep (se 2 (by rfl) ⟨3260310, by rfl⟩ : syracuseStep 8694161 = 6520621) B6520621
theorem B5796107 : Blo 2289435 5796107 := bstep (se 1 (by rfl) ⟨4347080, by rfl⟩ : syracuseStep 5796107 = 8694161) B8694161
theorem B3864071 : Blo 2289435 3864071 := bstep (se 1 (by rfl) ⟨2898053, by rfl⟩ : syracuseStep 3864071 = 5796107) B5796107
theorem B2576047 : Blo 2289435 2576047 := bstep (se 1 (by rfl) ⟨1932035, by rfl⟩ : syracuseStep 2576047 = 3864071) B3864071
theorem B3434729 : Blo 2289435 3434729 := bstep (se 2 (by rfl) ⟨1288023, by rfl⟩ : syracuseStep 3434729 = 2576047) B2576047
theorem B2289819 : Blo 2289435 2289819 := bstep (se 1 (by rfl) ⟨1717364, by rfl⟩ : syracuseStep 2289819 = 3434729) B3434729
theorem B13926389 : Blo 2289435 13926389 := bbase (se 5 (by rfl) ⟨652799, by rfl⟩ : syracuseStep 13926389 = 1305599) (by norm_num)
theorem B37137037 : Blo 2289435 37137037 := bstep (se 3 (by rfl) ⟨6963194, by rfl⟩ : syracuseStep 37137037 = 13926389) B13926389
theorem B49516049 : Blo 2289435 49516049 := bstep (se 2 (by rfl) ⟨18568518, by rfl⟩ : syracuseStep 49516049 = 37137037) B37137037
theorem B33010699 : Blo 2289435 33010699 := bstep (se 1 (by rfl) ⟨24758024, by rfl⟩ : syracuseStep 33010699 = 49516049) B49516049
theorem B44014265 : Blo 2289435 44014265 := bstep (se 2 (by rfl) ⟨16505349, by rfl⟩ : syracuseStep 44014265 = 33010699) B33010699
theorem B29342843 : Blo 2289435 29342843 := bstep (se 1 (by rfl) ⟨22007132, by rfl⟩ : syracuseStep 29342843 = 44014265) B44014265
theorem B19561895 : Blo 2289435 19561895 := bstep (se 1 (by rfl) ⟨14671421, by rfl⟩ : syracuseStep 19561895 = 29342843) B29342843
theorem B13041263 : Blo 2289435 13041263 := bstep (se 1 (by rfl) ⟨9780947, by rfl⟩ : syracuseStep 13041263 = 19561895) B19561895
theorem B8694175 : Blo 2289435 8694175 := bstep (se 1 (by rfl) ⟨6520631, by rfl⟩ : syracuseStep 8694175 = 13041263) B13041263
theorem B11592233 : Blo 2289435 11592233 := bstep (se 2 (by rfl) ⟨4347087, by rfl⟩ : syracuseStep 11592233 = 8694175) B8694175
theorem B7728155 : Blo 2289435 7728155 := bstep (se 1 (by rfl) ⟨5796116, by rfl⟩ : syracuseStep 7728155 = 11592233) B11592233
theorem B5152103 : Blo 2289435 5152103 := bstep (se 1 (by rfl) ⟨3864077, by rfl⟩ : syracuseStep 5152103 = 7728155) B7728155
theorem B3434735 : Blo 2289435 3434735 := bstep (se 1 (by rfl) ⟨2576051, by rfl⟩ : syracuseStep 3434735 = 5152103) B5152103
theorem B2289823 : Blo 2289435 2289823 := bstep (se 1 (by rfl) ⟨1717367, by rfl⟩ : syracuseStep 2289823 = 3434735) B3434735
theorem B3434741 : Blo 2289435 3434741 := bbase (se 5 (by rfl) ⟨161003, by rfl⟩ : syracuseStep 3434741 = 322007) (by norm_num)
theorem B2289827 : Blo 2289435 2289827 := bstep (se 1 (by rfl) ⟨1717370, by rfl⟩ : syracuseStep 2289827 = 3434741) B3434741
theorem B6963221 : Blo 2289435 6963221 := bbase (se 6 (by rfl) ⟨163200, by rfl⟩ : syracuseStep 6963221 = 326401) (by norm_num)
theorem B4642147 : Blo 2289435 4642147 := bstep (se 1 (by rfl) ⟨3481610, by rfl⟩ : syracuseStep 4642147 = 6963221) B6963221
theorem B6189529 : Blo 2289435 6189529 := bstep (se 2 (by rfl) ⟨2321073, by rfl⟩ : syracuseStep 6189529 = 4642147) B4642147
theorem B8252705 : Blo 2289435 8252705 := bstep (se 2 (by rfl) ⟨3094764, by rfl⟩ : syracuseStep 8252705 = 6189529) B6189529
theorem B22007213 : Blo 2289435 22007213 := bstep (se 3 (by rfl) ⟨4126352, by rfl⟩ : syracuseStep 22007213 = 8252705) B8252705
theorem B14671475 : Blo 2289435 14671475 := bstep (se 1 (by rfl) ⟨11003606, by rfl⟩ : syracuseStep 14671475 = 22007213) B22007213
theorem B9780983 : Blo 2289435 9780983 := bstep (se 1 (by rfl) ⟨7335737, by rfl⟩ : syracuseStep 9780983 = 14671475) B14671475
theorem B6520655 : Blo 2289435 6520655 := bstep (se 1 (by rfl) ⟨4890491, by rfl⟩ : syracuseStep 6520655 = 9780983) B9780983
theorem B4347103 : Blo 2289435 4347103 := bstep (se 1 (by rfl) ⟨3260327, by rfl⟩ : syracuseStep 4347103 = 6520655) B6520655
theorem B5796137 : Blo 2289435 5796137 := bstep (se 2 (by rfl) ⟨2173551, by rfl⟩ : syracuseStep 5796137 = 4347103) B4347103
theorem B3864091 : Blo 2289435 3864091 := bstep (se 1 (by rfl) ⟨2898068, by rfl⟩ : syracuseStep 3864091 = 5796137) B5796137
theorem B5152121 : Blo 2289435 5152121 := bstep (se 2 (by rfl) ⟨1932045, by rfl⟩ : syracuseStep 5152121 = 3864091) B3864091
theorem B3434747 : Blo 2289435 3434747 := bstep (se 1 (by rfl) ⟨2576060, by rfl⟩ : syracuseStep 3434747 = 5152121) B5152121
theorem B2289831 : Blo 2289435 2289831 := bstep (se 1 (by rfl) ⟨1717373, by rfl⟩ : syracuseStep 2289831 = 3434747) B3434747
theorem B2576065 : Blo 2289435 2576065 := bbase (se 2 (by rfl) ⟨966024, by rfl⟩ : syracuseStep 2576065 = 1932049) (by norm_num)
theorem B3434753 : Blo 2289435 3434753 := bstep (se 2 (by rfl) ⟨1288032, by rfl⟩ : syracuseStep 3434753 = 2576065) B2576065
theorem B2289835 : Blo 2289435 2289835 := bstep (se 1 (by rfl) ⟨1717376, by rfl⟩ : syracuseStep 2289835 = 3434753) B3434753
theorem B5796157 : Blo 2289435 5796157 := bbase (se 3 (by rfl) ⟨1086779, by rfl⟩ : syracuseStep 5796157 = 2173559) (by norm_num)
theorem B7728209 : Blo 2289435 7728209 := bstep (se 2 (by rfl) ⟨2898078, by rfl⟩ : syracuseStep 7728209 = 5796157) B5796157
theorem B5152139 : Blo 2289435 5152139 := bstep (se 1 (by rfl) ⟨3864104, by rfl⟩ : syracuseStep 5152139 = 7728209) B7728209
theorem B3434759 : Blo 2289435 3434759 := bstep (se 1 (by rfl) ⟨2576069, by rfl⟩ : syracuseStep 3434759 = 5152139) B5152139
theorem B2289839 : Blo 2289435 2289839 := bstep (se 1 (by rfl) ⟨1717379, by rfl⟩ : syracuseStep 2289839 = 3434759) B3434759
theorem B3434765 : Blo 2289435 3434765 := bbase (se 3 (by rfl) ⟨644018, by rfl⟩ : syracuseStep 3434765 = 1288037) (by norm_num)
theorem B2289843 : Blo 2289435 2289843 := bstep (se 1 (by rfl) ⟨1717382, by rfl⟩ : syracuseStep 2289843 = 3434765) B3434765
theorem B5152157 : Blo 2289435 5152157 := bbase (se 3 (by rfl) ⟨966029, by rfl⟩ : syracuseStep 5152157 = 1932059) (by norm_num)
theorem B3434771 : Blo 2289435 3434771 := bstep (se 1 (by rfl) ⟨2576078, by rfl⟩ : syracuseStep 3434771 = 5152157) B5152157
theorem B2289847 : Blo 2289435 2289847 := bstep (se 1 (by rfl) ⟨1717385, by rfl⟩ : syracuseStep 2289847 = 3434771) B3434771
theorem B3864125 : Blo 2289435 3864125 := bbase (se 3 (by rfl) ⟨724523, by rfl⟩ : syracuseStep 3864125 = 1449047) (by norm_num)
theorem B2576083 : Blo 2289435 2576083 := bstep (se 1 (by rfl) ⟨1932062, by rfl⟩ : syracuseStep 2576083 = 3864125) B3864125
theorem B3434777 : Blo 2289435 3434777 := bstep (se 2 (by rfl) ⟨1288041, by rfl⟩ : syracuseStep 3434777 = 2576083) B2576083
theorem B2289851 : Blo 2289435 2289851 := bstep (se 1 (by rfl) ⟨1717388, by rfl⟩ : syracuseStep 2289851 = 3434777) B3434777
theorem B5501861 : Blo 2289435 5501861 := bbase (se 4 (by rfl) ⟨515799, by rfl⟩ : syracuseStep 5501861 = 1031599) (by norm_num)
theorem B3667907 : Blo 2289435 3667907 := bstep (se 1 (by rfl) ⟨2750930, by rfl⟩ : syracuseStep 3667907 = 5501861) B5501861
theorem B2445271 : Blo 2289435 2445271 := bstep (se 1 (by rfl) ⟨1833953, by rfl⟩ : syracuseStep 2445271 = 3667907) B3667907
theorem B13041445 : Blo 2289435 13041445 := bstep (se 4 (by rfl) ⟨1222635, by rfl⟩ : syracuseStep 13041445 = 2445271) B2445271
theorem B17388593 : Blo 2289435 17388593 := bstep (se 2 (by rfl) ⟨6520722, by rfl⟩ : syracuseStep 17388593 = 13041445) B13041445
theorem B11592395 : Blo 2289435 11592395 := bstep (se 1 (by rfl) ⟨8694296, by rfl⟩ : syracuseStep 11592395 = 17388593) B17388593
theorem B7728263 : Blo 2289435 7728263 := bstep (se 1 (by rfl) ⟨5796197, by rfl⟩ : syracuseStep 7728263 = 11592395) B11592395
theorem B5152175 : Blo 2289435 5152175 := bstep (se 1 (by rfl) ⟨3864131, by rfl⟩ : syracuseStep 5152175 = 7728263) B7728263
theorem B3434783 : Blo 2289435 3434783 := bstep (se 1 (by rfl) ⟨2576087, by rfl⟩ : syracuseStep 3434783 = 5152175) B5152175
theorem B2289855 : Blo 2289435 2289855 := bstep (se 1 (by rfl) ⟨1717391, by rfl⟩ : syracuseStep 2289855 = 3434783) B3434783
theorem B3434789 : Blo 2289435 3434789 := bbase (se 4 (by rfl) ⟨322011, by rfl⟩ : syracuseStep 3434789 = 644023) (by norm_num)
theorem B2289859 : Blo 2289435 2289859 := bstep (se 1 (by rfl) ⟨1717394, by rfl⟩ : syracuseStep 2289859 = 3434789) B3434789
theorem B2898109 : Blo 2289435 2898109 := bbase (se 3 (by rfl) ⟨543395, by rfl⟩ : syracuseStep 2898109 = 1086791) (by norm_num)
theorem B3864145 : Blo 2289435 3864145 := bstep (se 2 (by rfl) ⟨1449054, by rfl⟩ : syracuseStep 3864145 = 2898109) B2898109
theorem B5152193 : Blo 2289435 5152193 := bstep (se 2 (by rfl) ⟨1932072, by rfl⟩ : syracuseStep 5152193 = 3864145) B3864145
theorem B3434795 : Blo 2289435 3434795 := bstep (se 1 (by rfl) ⟨2576096, by rfl⟩ : syracuseStep 3434795 = 5152193) B5152193
theorem B2289863 : Blo 2289435 2289863 := bstep (se 1 (by rfl) ⟨1717397, by rfl⟩ : syracuseStep 2289863 = 3434795) B3434795
theorem B2576101 : Blo 2289435 2576101 := bbase (se 4 (by rfl) ⟨241509, by rfl⟩ : syracuseStep 2576101 = 483019) (by norm_num)
theorem B3434801 : Blo 2289435 3434801 := bstep (se 2 (by rfl) ⟨1288050, by rfl⟩ : syracuseStep 3434801 = 2576101) B2576101
theorem B2289867 : Blo 2289435 2289867 := bstep (se 1 (by rfl) ⟨1717400, by rfl⟩ : syracuseStep 2289867 = 3434801) B3434801
theorem B3667933 : Blo 2289435 3667933 := bbase (se 3 (by rfl) ⟨687737, by rfl⟩ : syracuseStep 3667933 = 1375475) (by norm_num)
theorem B4890577 : Blo 2289435 4890577 := bstep (se 2 (by rfl) ⟨1833966, by rfl⟩ : syracuseStep 4890577 = 3667933) B3667933
theorem B6520769 : Blo 2289435 6520769 := bstep (se 2 (by rfl) ⟨2445288, by rfl⟩ : syracuseStep 6520769 = 4890577) B4890577
theorem B4347179 : Blo 2289435 4347179 := bstep (se 1 (by rfl) ⟨3260384, by rfl⟩ : syracuseStep 4347179 = 6520769) B6520769
theorem B2898119 : Blo 2289435 2898119 := bstep (se 1 (by rfl) ⟨2173589, by rfl⟩ : syracuseStep 2898119 = 4347179) B4347179
theorem B7728317 : Blo 2289435 7728317 := bstep (se 3 (by rfl) ⟨1449059, by rfl⟩ : syracuseStep 7728317 = 2898119) B2898119
theorem B5152211 : Blo 2289435 5152211 := bstep (se 1 (by rfl) ⟨3864158, by rfl⟩ : syracuseStep 5152211 = 7728317) B7728317
theorem B3434807 : Blo 2289435 3434807 := bstep (se 1 (by rfl) ⟨2576105, by rfl⟩ : syracuseStep 3434807 = 5152211) B5152211
theorem B2289871 : Blo 2289435 2289871 := bstep (se 1 (by rfl) ⟨1717403, by rfl⟩ : syracuseStep 2289871 = 3434807) B3434807
theorem B3434813 : Blo 2289435 3434813 := bbase (se 3 (by rfl) ⟨644027, by rfl⟩ : syracuseStep 3434813 = 1288055) (by norm_num)
theorem B2289875 : Blo 2289435 2289875 := bstep (se 1 (by rfl) ⟨1717406, by rfl⟩ : syracuseStep 2289875 = 3434813) B3434813
theorem B5152229 : Blo 2289435 5152229 := bbase (se 4 (by rfl) ⟨483021, by rfl⟩ : syracuseStep 5152229 = 966043) (by norm_num)
theorem B3434819 : Blo 2289435 3434819 := bstep (se 1 (by rfl) ⟨2576114, by rfl⟩ : syracuseStep 3434819 = 5152229) B5152229
theorem B2289879 : Blo 2289435 2289879 := bstep (se 1 (by rfl) ⟨1717409, by rfl⟩ : syracuseStep 2289879 = 3434819) B3434819
theorem B5796269 : Blo 2289435 5796269 := bbase (se 3 (by rfl) ⟨1086800, by rfl⟩ : syracuseStep 5796269 = 2173601) (by norm_num)
theorem B3864179 : Blo 2289435 3864179 := bstep (se 1 (by rfl) ⟨2898134, by rfl⟩ : syracuseStep 3864179 = 5796269) B5796269
theorem B2576119 : Blo 2289435 2576119 := bstep (se 1 (by rfl) ⟨1932089, by rfl⟩ : syracuseStep 2576119 = 3864179) B3864179
theorem B3434825 : Blo 2289435 3434825 := bstep (se 2 (by rfl) ⟨1288059, by rfl⟩ : syracuseStep 3434825 = 2576119) B2576119
theorem B2289883 : Blo 2289435 2289883 := bstep (se 1 (by rfl) ⟨1717412, by rfl⟩ : syracuseStep 2289883 = 3434825) B3434825
theorem B2750969 : Blo 2289435 2750969 := bbase (se 2 (by rfl) ⟨1031613, by rfl⟩ : syracuseStep 2750969 = 2063227) (by norm_num)
theorem B7335917 : Blo 2289435 7335917 := bstep (se 3 (by rfl) ⟨1375484, by rfl⟩ : syracuseStep 7335917 = 2750969) B2750969
theorem B4890611 : Blo 2289435 4890611 := bstep (se 1 (by rfl) ⟨3667958, by rfl⟩ : syracuseStep 4890611 = 7335917) B7335917
theorem B3260407 : Blo 2289435 3260407 := bstep (se 1 (by rfl) ⟨2445305, by rfl⟩ : syracuseStep 3260407 = 4890611) B4890611
theorem B4347209 : Blo 2289435 4347209 := bstep (se 2 (by rfl) ⟨1630203, by rfl⟩ : syracuseStep 4347209 = 3260407) B3260407
theorem B11592557 : Blo 2289435 11592557 := bstep (se 3 (by rfl) ⟨2173604, by rfl⟩ : syracuseStep 11592557 = 4347209) B4347209
theorem B7728371 : Blo 2289435 7728371 := bstep (se 1 (by rfl) ⟨5796278, by rfl⟩ : syracuseStep 7728371 = 11592557) B11592557
theorem B5152247 : Blo 2289435 5152247 := bstep (se 1 (by rfl) ⟨3864185, by rfl⟩ : syracuseStep 5152247 = 7728371) B7728371
theorem B3434831 : Blo 2289435 3434831 := bstep (se 1 (by rfl) ⟨2576123, by rfl⟩ : syracuseStep 3434831 = 5152247) B5152247
theorem B2289887 : Blo 2289435 2289887 := bstep (se 1 (by rfl) ⟨1717415, by rfl⟩ : syracuseStep 2289887 = 3434831) B3434831
theorem B3434837 : Blo 2289435 3434837 := bbase (se 10 (by rfl) ⟨5031, by rfl⟩ : syracuseStep 3434837 = 10063) (by norm_num)
theorem B2289891 : Blo 2289435 2289891 := bstep (se 1 (by rfl) ⟨1717418, by rfl⟩ : syracuseStep 2289891 = 3434837) B3434837
theorem B6520837 : Blo 2289435 6520837 := bbase (se 4 (by rfl) ⟨611328, by rfl⟩ : syracuseStep 6520837 = 1222657) (by norm_num)
theorem B8694449 : Blo 2289435 8694449 := bstep (se 2 (by rfl) ⟨3260418, by rfl⟩ : syracuseStep 8694449 = 6520837) B6520837
theorem B5796299 : Blo 2289435 5796299 := bstep (se 1 (by rfl) ⟨4347224, by rfl⟩ : syracuseStep 5796299 = 8694449) B8694449
theorem B3864199 : Blo 2289435 3864199 := bstep (se 1 (by rfl) ⟨2898149, by rfl⟩ : syracuseStep 3864199 = 5796299) B5796299
theorem B5152265 : Blo 2289435 5152265 := bstep (se 2 (by rfl) ⟨1932099, by rfl⟩ : syracuseStep 5152265 = 3864199) B3864199
theorem B3434843 : Blo 2289435 3434843 := bstep (se 1 (by rfl) ⟨2576132, by rfl⟩ : syracuseStep 3434843 = 5152265) B5152265
theorem B2289895 : Blo 2289435 2289895 := bstep (se 1 (by rfl) ⟨1717421, by rfl⟩ : syracuseStep 2289895 = 3434843) B3434843
theorem B2576137 : Blo 2289435 2576137 := bbase (se 2 (by rfl) ⟨966051, by rfl⟩ : syracuseStep 2576137 = 1932103) (by norm_num)
theorem B3434849 : Blo 2289435 3434849 := bstep (se 2 (by rfl) ⟨1288068, by rfl⟩ : syracuseStep 3434849 = 2576137) B2576137
theorem B2289899 : Blo 2289435 2289899 := bstep (se 1 (by rfl) ⟨1717424, by rfl⟩ : syracuseStep 2289899 = 3434849) B3434849
theorem B9914741 : Blo 2289435 9914741 := bbase (se 5 (by rfl) ⟨464753, by rfl⟩ : syracuseStep 9914741 = 929507) (by norm_num)
theorem B6609827 : Blo 2289435 6609827 := bstep (se 1 (by rfl) ⟨4957370, by rfl⟩ : syracuseStep 6609827 = 9914741) B9914741
theorem B4406551 : Blo 2289435 4406551 := bstep (se 1 (by rfl) ⟨3304913, by rfl⟩ : syracuseStep 4406551 = 6609827) B6609827
theorem B23501605 : Blo 2289435 23501605 := bstep (se 4 (by rfl) ⟨2203275, by rfl⟩ : syracuseStep 23501605 = 4406551) B4406551
theorem B31335473 : Blo 2289435 31335473 := bstep (se 2 (by rfl) ⟨11750802, by rfl⟩ : syracuseStep 31335473 = 23501605) B23501605
theorem B20890315 : Blo 2289435 20890315 := bstep (se 1 (by rfl) ⟨15667736, by rfl⟩ : syracuseStep 20890315 = 31335473) B31335473
theorem B27853753 : Blo 2289435 27853753 := bstep (se 2 (by rfl) ⟨10445157, by rfl⟩ : syracuseStep 27853753 = 20890315) B20890315
theorem B37138337 : Blo 2289435 37138337 := bstep (se 2 (by rfl) ⟨13926876, by rfl⟩ : syracuseStep 37138337 = 27853753) B27853753
theorem B24758891 : Blo 2289435 24758891 := bstep (se 1 (by rfl) ⟨18569168, by rfl⟩ : syracuseStep 24758891 = 37138337) B37138337
theorem B16505927 : Blo 2289435 16505927 := bstep (se 1 (by rfl) ⟨12379445, by rfl⟩ : syracuseStep 16505927 = 24758891) B24758891
theorem B11003951 : Blo 2289435 11003951 := bstep (se 1 (by rfl) ⟨8252963, by rfl⟩ : syracuseStep 11003951 = 16505927) B16505927
theorem B29343869 : Blo 2289435 29343869 := bstep (se 3 (by rfl) ⟨5501975, by rfl⟩ : syracuseStep 29343869 = 11003951) B11003951
theorem B19562579 : Blo 2289435 19562579 := bstep (se 1 (by rfl) ⟨14671934, by rfl⟩ : syracuseStep 19562579 = 29343869) B29343869
theorem B13041719 : Blo 2289435 13041719 := bstep (se 1 (by rfl) ⟨9781289, by rfl⟩ : syracuseStep 13041719 = 19562579) B19562579
theorem B8694479 : Blo 2289435 8694479 := bstep (se 1 (by rfl) ⟨6520859, by rfl⟩ : syracuseStep 8694479 = 13041719) B13041719
theorem B5796319 : Blo 2289435 5796319 := bstep (se 1 (by rfl) ⟨4347239, by rfl⟩ : syracuseStep 5796319 = 8694479) B8694479
theorem B7728425 : Blo 2289435 7728425 := bstep (se 2 (by rfl) ⟨2898159, by rfl⟩ : syracuseStep 7728425 = 5796319) B5796319
theorem B5152283 : Blo 2289435 5152283 := bstep (se 1 (by rfl) ⟨3864212, by rfl⟩ : syracuseStep 5152283 = 7728425) B7728425
theorem B3434855 : Blo 2289435 3434855 := bstep (se 1 (by rfl) ⟨2576141, by rfl⟩ : syracuseStep 3434855 = 5152283) B5152283
theorem B2289903 : Blo 2289435 2289903 := bstep (se 1 (by rfl) ⟨1717427, by rfl⟩ : syracuseStep 2289903 = 3434855) B3434855
theorem B3434861 : Blo 2289435 3434861 := bbase (se 3 (by rfl) ⟨644036, by rfl⟩ : syracuseStep 3434861 = 1288073) (by norm_num)
theorem B2289907 : Blo 2289435 2289907 := bstep (se 1 (by rfl) ⟨1717430, by rfl⟩ : syracuseStep 2289907 = 3434861) B3434861
theorem B5152301 : Blo 2289435 5152301 := bbase (se 3 (by rfl) ⟨966056, by rfl⟩ : syracuseStep 5152301 = 1932113) (by norm_num)
theorem B3434867 : Blo 2289435 3434867 := bstep (se 1 (by rfl) ⟨2576150, by rfl⟩ : syracuseStep 3434867 = 5152301) B5152301
theorem B2289911 : Blo 2289435 2289911 := bstep (se 1 (by rfl) ⟨1717433, by rfl⟩ : syracuseStep 2289911 = 3434867) B3434867
theorem B47644757 : Blo 2289435 47644757 := bbase (se 8 (by rfl) ⟨279168, by rfl⟩ : syracuseStep 47644757 = 558337) (by norm_num)
theorem B31763171 : Blo 2289435 31763171 := bstep (se 1 (by rfl) ⟨23822378, by rfl⟩ : syracuseStep 31763171 = 47644757) B47644757
theorem B21175447 : Blo 2289435 21175447 := bstep (se 1 (by rfl) ⟨15881585, by rfl⟩ : syracuseStep 21175447 = 31763171) B31763171
theorem B28233929 : Blo 2289435 28233929 := bstep (se 2 (by rfl) ⟨10587723, by rfl⟩ : syracuseStep 28233929 = 21175447) B21175447
theorem B18822619 : Blo 2289435 18822619 := bstep (se 1 (by rfl) ⟨14116964, by rfl⟩ : syracuseStep 18822619 = 28233929) B28233929
theorem B25096825 : Blo 2289435 25096825 := bstep (se 2 (by rfl) ⟨9411309, by rfl⟩ : syracuseStep 25096825 = 18822619) B18822619
theorem B33462433 : Blo 2289435 33462433 := bstep (se 2 (by rfl) ⟨12548412, by rfl⟩ : syracuseStep 33462433 = 25096825) B25096825
theorem B44616577 : Blo 2289435 44616577 := bstep (se 2 (by rfl) ⟨16731216, by rfl⟩ : syracuseStep 44616577 = 33462433) B33462433
theorem B59488769 : Blo 2289435 59488769 := bstep (se 2 (by rfl) ⟨22308288, by rfl⟩ : syracuseStep 59488769 = 44616577) B44616577
theorem B39659179 : Blo 2289435 39659179 := bstep (se 1 (by rfl) ⟨29744384, by rfl⟩ : syracuseStep 39659179 = 59488769) B59488769
theorem B52878905 : Blo 2289435 52878905 := bstep (se 2 (by rfl) ⟨19829589, by rfl⟩ : syracuseStep 52878905 = 39659179) B39659179
theorem B35252603 : Blo 2289435 35252603 := bstep (se 1 (by rfl) ⟨26439452, by rfl⟩ : syracuseStep 35252603 = 52878905) B52878905
theorem B23501735 : Blo 2289435 23501735 := bstep (se 1 (by rfl) ⟨17626301, by rfl⟩ : syracuseStep 23501735 = 35252603) B35252603
theorem B15667823 : Blo 2289435 15667823 := bstep (se 1 (by rfl) ⟨11750867, by rfl⟩ : syracuseStep 15667823 = 23501735) B23501735
theorem B10445215 : Blo 2289435 10445215 := bstep (se 1 (by rfl) ⟨7833911, by rfl⟩ : syracuseStep 10445215 = 15667823) B15667823
theorem B13926953 : Blo 2289435 13926953 := bstep (se 2 (by rfl) ⟨5222607, by rfl⟩ : syracuseStep 13926953 = 10445215) B10445215
theorem B9284635 : Blo 2289435 9284635 := bstep (se 1 (by rfl) ⟨6963476, by rfl⟩ : syracuseStep 9284635 = 13926953) B13926953
theorem B49518053 : Blo 2289435 49518053 := bstep (se 4 (by rfl) ⟨4642317, by rfl⟩ : syracuseStep 49518053 = 9284635) B9284635
theorem B33012035 : Blo 2289435 33012035 := bstep (se 1 (by rfl) ⟨24759026, by rfl⟩ : syracuseStep 33012035 = 49518053) B49518053
theorem B22008023 : Blo 2289435 22008023 := bstep (se 1 (by rfl) ⟨16506017, by rfl⟩ : syracuseStep 22008023 = 33012035) B33012035
theorem B14672015 : Blo 2289435 14672015 := bstep (se 1 (by rfl) ⟨11004011, by rfl⟩ : syracuseStep 14672015 = 22008023) B22008023
theorem B9781343 : Blo 2289435 9781343 := bstep (se 1 (by rfl) ⟨7336007, by rfl⟩ : syracuseStep 9781343 = 14672015) B14672015
theorem B6520895 : Blo 2289435 6520895 := bstep (se 1 (by rfl) ⟨4890671, by rfl⟩ : syracuseStep 6520895 = 9781343) B9781343
theorem B4347263 : Blo 2289435 4347263 := bstep (se 1 (by rfl) ⟨3260447, by rfl⟩ : syracuseStep 4347263 = 6520895) B6520895
theorem B2898175 : Blo 2289435 2898175 := bstep (se 1 (by rfl) ⟨2173631, by rfl⟩ : syracuseStep 2898175 = 4347263) B4347263
theorem B3864233 : Blo 2289435 3864233 := bstep (se 2 (by rfl) ⟨1449087, by rfl⟩ : syracuseStep 3864233 = 2898175) B2898175
theorem B2576155 : Blo 2289435 2576155 := bstep (se 1 (by rfl) ⟨1932116, by rfl⟩ : syracuseStep 2576155 = 3864233) B3864233
theorem B3434873 : Blo 2289435 3434873 := bstep (se 2 (by rfl) ⟨1288077, by rfl⟩ : syracuseStep 3434873 = 2576155) B2576155
theorem B2289915 : Blo 2289435 2289915 := bstep (se 1 (by rfl) ⟨1717436, by rfl⟩ : syracuseStep 2289915 = 3434873) B3434873
theorem B7833925 : Blo 2289435 7833925 := bbase (se 4 (by rfl) ⟨734430, by rfl⟩ : syracuseStep 7833925 = 1468861) (by norm_num)
theorem B10445233 : Blo 2289435 10445233 := bstep (se 2 (by rfl) ⟨3916962, by rfl⟩ : syracuseStep 10445233 = 7833925) B7833925
theorem B13926977 : Blo 2289435 13926977 := bstep (se 2 (by rfl) ⟨5222616, by rfl⟩ : syracuseStep 13926977 = 10445233) B10445233
theorem B9284651 : Blo 2289435 9284651 := bstep (se 1 (by rfl) ⟨6963488, by rfl⟩ : syracuseStep 9284651 = 13926977) B13926977
theorem B6189767 : Blo 2289435 6189767 := bstep (se 1 (by rfl) ⟨4642325, by rfl⟩ : syracuseStep 6189767 = 9284651) B9284651
theorem B4126511 : Blo 2289435 4126511 := bstep (se 1 (by rfl) ⟨3094883, by rfl⟩ : syracuseStep 4126511 = 6189767) B6189767
theorem B2751007 : Blo 2289435 2751007 := bstep (se 1 (by rfl) ⟨2063255, by rfl⟩ : syracuseStep 2751007 = 4126511) B4126511
theorem B3668009 : Blo 2289435 3668009 := bstep (se 2 (by rfl) ⟨1375503, by rfl⟩ : syracuseStep 3668009 = 2751007) B2751007
theorem B39125429 : Blo 2289435 39125429 := bstep (se 5 (by rfl) ⟨1834004, by rfl⟩ : syracuseStep 39125429 = 3668009) B3668009
theorem B26083619 : Blo 2289435 26083619 := bstep (se 1 (by rfl) ⟨19562714, by rfl⟩ : syracuseStep 26083619 = 39125429) B39125429
theorem B17389079 : Blo 2289435 17389079 := bstep (se 1 (by rfl) ⟨13041809, by rfl⟩ : syracuseStep 17389079 = 26083619) B26083619
theorem B11592719 : Blo 2289435 11592719 := bstep (se 1 (by rfl) ⟨8694539, by rfl⟩ : syracuseStep 11592719 = 17389079) B17389079
theorem B7728479 : Blo 2289435 7728479 := bstep (se 1 (by rfl) ⟨5796359, by rfl⟩ : syracuseStep 7728479 = 11592719) B11592719
theorem B5152319 : Blo 2289435 5152319 := bstep (se 1 (by rfl) ⟨3864239, by rfl⟩ : syracuseStep 5152319 = 7728479) B7728479
theorem B3434879 : Blo 2289435 3434879 := bstep (se 1 (by rfl) ⟨2576159, by rfl⟩ : syracuseStep 3434879 = 5152319) B5152319
theorem B2289919 : Blo 2289435 2289919 := bstep (se 1 (by rfl) ⟨1717439, by rfl⟩ : syracuseStep 2289919 = 3434879) B3434879
theorem B3434885 : Blo 2289435 3434885 := bbase (se 4 (by rfl) ⟨322020, by rfl⟩ : syracuseStep 3434885 = 644041) (by norm_num)
theorem B2289923 : Blo 2289435 2289923 := bstep (se 1 (by rfl) ⟨1717442, by rfl⟩ : syracuseStep 2289923 = 3434885) B3434885
theorem B3864253 : Blo 2289435 3864253 := bbase (se 3 (by rfl) ⟨724547, by rfl⟩ : syracuseStep 3864253 = 1449095) (by norm_num)
theorem B5152337 : Blo 2289435 5152337 := bstep (se 2 (by rfl) ⟨1932126, by rfl⟩ : syracuseStep 5152337 = 3864253) B3864253
theorem B3434891 : Blo 2289435 3434891 := bstep (se 1 (by rfl) ⟨2576168, by rfl⟩ : syracuseStep 3434891 = 5152337) B5152337
theorem B2289927 : Blo 2289435 2289927 := bstep (se 1 (by rfl) ⟨1717445, by rfl⟩ : syracuseStep 2289927 = 3434891) B3434891
theorem B2576173 : Blo 2289435 2576173 := bbase (se 3 (by rfl) ⟨483032, by rfl⟩ : syracuseStep 2576173 = 966065) (by norm_num)
theorem B3434897 : Blo 2289435 3434897 := bstep (se 2 (by rfl) ⟨1288086, by rfl⟩ : syracuseStep 3434897 = 2576173) B2576173
theorem B2289931 : Blo 2289435 2289931 := bstep (se 1 (by rfl) ⟨1717448, by rfl⟩ : syracuseStep 2289931 = 3434897) B3434897
theorem B7728533 : Blo 2289435 7728533 := bbase (se 6 (by rfl) ⟨181137, by rfl⟩ : syracuseStep 7728533 = 362275) (by norm_num)
theorem B5152355 : Blo 2289435 5152355 := bstep (se 1 (by rfl) ⟨3864266, by rfl⟩ : syracuseStep 5152355 = 7728533) B7728533
theorem B3434903 : Blo 2289435 3434903 := bstep (se 1 (by rfl) ⟨2576177, by rfl⟩ : syracuseStep 3434903 = 5152355) B5152355
theorem B2289935 : Blo 2289435 2289935 := bstep (se 1 (by rfl) ⟨1717451, by rfl⟩ : syracuseStep 2289935 = 3434903) B3434903
theorem B3434909 : Blo 2289435 3434909 := bbase (se 3 (by rfl) ⟨644045, by rfl⟩ : syracuseStep 3434909 = 1288091) (by norm_num)
theorem B2289939 : Blo 2289435 2289939 := bstep (se 1 (by rfl) ⟨1717454, by rfl⟩ : syracuseStep 2289939 = 3434909) B3434909
theorem B5152373 : Blo 2289435 5152373 := bbase (se 5 (by rfl) ⟨241517, by rfl⟩ : syracuseStep 5152373 = 483035) (by norm_num)
theorem B3434915 : Blo 2289435 3434915 := bstep (se 1 (by rfl) ⟨2576186, by rfl⟩ : syracuseStep 3434915 = 5152373) B5152373
theorem B2289943 : Blo 2289435 2289943 := bstep (se 1 (by rfl) ⟨1717457, by rfl⟩ : syracuseStep 2289943 = 3434915) B3434915
theorem B2751041 : Blo 2289435 2751041 := bbase (se 2 (by rfl) ⟨1031640, by rfl⟩ : syracuseStep 2751041 = 2063281) (by norm_num)
theorem B7336109 : Blo 2289435 7336109 := bstep (se 3 (by rfl) ⟨1375520, by rfl⟩ : syracuseStep 7336109 = 2751041) B2751041
theorem B19562957 : Blo 2289435 19562957 := bstep (se 3 (by rfl) ⟨3668054, by rfl⟩ : syracuseStep 19562957 = 7336109) B7336109
theorem B13041971 : Blo 2289435 13041971 := bstep (se 1 (by rfl) ⟨9781478, by rfl⟩ : syracuseStep 13041971 = 19562957) B19562957
theorem B8694647 : Blo 2289435 8694647 := bstep (se 1 (by rfl) ⟨6520985, by rfl⟩ : syracuseStep 8694647 = 13041971) B13041971
theorem B5796431 : Blo 2289435 5796431 := bstep (se 1 (by rfl) ⟨4347323, by rfl⟩ : syracuseStep 5796431 = 8694647) B8694647
theorem B3864287 : Blo 2289435 3864287 := bstep (se 1 (by rfl) ⟨2898215, by rfl⟩ : syracuseStep 3864287 = 5796431) B5796431
theorem B2576191 : Blo 2289435 2576191 := bstep (se 1 (by rfl) ⟨1932143, by rfl⟩ : syracuseStep 2576191 = 3864287) B3864287
theorem B3434921 : Blo 2289435 3434921 := bstep (se 2 (by rfl) ⟨1288095, by rfl⟩ : syracuseStep 3434921 = 2576191) B2576191
theorem B2289947 : Blo 2289435 2289947 := bstep (se 1 (by rfl) ⟨1717460, by rfl⟩ : syracuseStep 2289947 = 3434921) B3434921
theorem B8694661 : Blo 2289435 8694661 := bbase (se 4 (by rfl) ⟨815124, by rfl⟩ : syracuseStep 8694661 = 1630249) (by norm_num)
theorem B11592881 : Blo 2289435 11592881 := bstep (se 2 (by rfl) ⟨4347330, by rfl⟩ : syracuseStep 11592881 = 8694661) B8694661
theorem B7728587 : Blo 2289435 7728587 := bstep (se 1 (by rfl) ⟨5796440, by rfl⟩ : syracuseStep 7728587 = 11592881) B11592881
theorem B5152391 : Blo 2289435 5152391 := bstep (se 1 (by rfl) ⟨3864293, by rfl⟩ : syracuseStep 5152391 = 7728587) B7728587
theorem B3434927 : Blo 2289435 3434927 := bstep (se 1 (by rfl) ⟨2576195, by rfl⟩ : syracuseStep 3434927 = 5152391) B5152391
theorem B2289951 : Blo 2289435 2289951 := bstep (se 1 (by rfl) ⟨1717463, by rfl⟩ : syracuseStep 2289951 = 3434927) B3434927
theorem B3434933 : Blo 2289435 3434933 := bbase (se 5 (by rfl) ⟨161012, by rfl⟩ : syracuseStep 3434933 = 322025) (by norm_num)
theorem B2289955 : Blo 2289435 2289955 := bstep (se 1 (by rfl) ⟨1717466, by rfl⟩ : syracuseStep 2289955 = 3434933) B3434933
theorem B5796461 : Blo 2289435 5796461 := bbase (se 3 (by rfl) ⟨1086836, by rfl⟩ : syracuseStep 5796461 = 2173673) (by norm_num)
theorem B3864307 : Blo 2289435 3864307 := bstep (se 1 (by rfl) ⟨2898230, by rfl⟩ : syracuseStep 3864307 = 5796461) B5796461
theorem B5152409 : Blo 2289435 5152409 := bstep (se 2 (by rfl) ⟨1932153, by rfl⟩ : syracuseStep 5152409 = 3864307) B3864307
theorem B3434939 : Blo 2289435 3434939 := bstep (se 1 (by rfl) ⟨2576204, by rfl⟩ : syracuseStep 3434939 = 5152409) B5152409
theorem B2289959 : Blo 2289435 2289959 := bstep (se 1 (by rfl) ⟨1717469, by rfl⟩ : syracuseStep 2289959 = 3434939) B3434939
theorem B2576209 : Blo 2289435 2576209 := bbase (se 2 (by rfl) ⟨966078, by rfl⟩ : syracuseStep 2576209 = 1932157) (by norm_num)
theorem B3434945 : Blo 2289435 3434945 := bstep (se 2 (by rfl) ⟨1288104, by rfl⟩ : syracuseStep 3434945 = 2576209) B2576209
theorem B2289963 : Blo 2289435 2289963 := bstep (se 1 (by rfl) ⟨1717472, by rfl⟩ : syracuseStep 2289963 = 3434945) B3434945
theorem B3094949 : Blo 2289435 3094949 := bbase (se 4 (by rfl) ⟨290151, by rfl⟩ : syracuseStep 3094949 = 580303) (by norm_num)
theorem B8253197 : Blo 2289435 8253197 := bstep (se 3 (by rfl) ⟨1547474, by rfl⟩ : syracuseStep 8253197 = 3094949) B3094949
theorem B5502131 : Blo 2289435 5502131 := bstep (se 1 (by rfl) ⟨4126598, by rfl⟩ : syracuseStep 5502131 = 8253197) B8253197
theorem B3668087 : Blo 2289435 3668087 := bstep (se 1 (by rfl) ⟨2751065, by rfl⟩ : syracuseStep 3668087 = 5502131) B5502131
theorem B2445391 : Blo 2289435 2445391 := bstep (se 1 (by rfl) ⟨1834043, by rfl⟩ : syracuseStep 2445391 = 3668087) B3668087
theorem B3260521 : Blo 2289435 3260521 := bstep (se 2 (by rfl) ⟨1222695, by rfl⟩ : syracuseStep 3260521 = 2445391) B2445391
theorem B4347361 : Blo 2289435 4347361 := bstep (se 2 (by rfl) ⟨1630260, by rfl⟩ : syracuseStep 4347361 = 3260521) B3260521
theorem B5796481 : Blo 2289435 5796481 := bstep (se 2 (by rfl) ⟨2173680, by rfl⟩ : syracuseStep 5796481 = 4347361) B4347361
theorem B7728641 : Blo 2289435 7728641 := bstep (se 2 (by rfl) ⟨2898240, by rfl⟩ : syracuseStep 7728641 = 5796481) B5796481
theorem B5152427 : Blo 2289435 5152427 := bstep (se 1 (by rfl) ⟨3864320, by rfl⟩ : syracuseStep 5152427 = 7728641) B7728641
theorem B3434951 : Blo 2289435 3434951 := bstep (se 1 (by rfl) ⟨2576213, by rfl⟩ : syracuseStep 3434951 = 5152427) B5152427
theorem B2289967 : Blo 2289435 2289967 := bstep (se 1 (by rfl) ⟨1717475, by rfl⟩ : syracuseStep 2289967 = 3434951) B3434951
theorem B3434957 : Blo 2289435 3434957 := bbase (se 3 (by rfl) ⟨644054, by rfl⟩ : syracuseStep 3434957 = 1288109) (by norm_num)
theorem B2289971 : Blo 2289435 2289971 := bstep (se 1 (by rfl) ⟨1717478, by rfl⟩ : syracuseStep 2289971 = 3434957) B3434957
theorem B5152445 : Blo 2289435 5152445 := bbase (se 3 (by rfl) ⟨966083, by rfl⟩ : syracuseStep 5152445 = 1932167) (by norm_num)
theorem B3434963 : Blo 2289435 3434963 := bstep (se 1 (by rfl) ⟨2576222, by rfl⟩ : syracuseStep 3434963 = 5152445) B5152445
theorem B2289975 : Blo 2289435 2289975 := bstep (se 1 (by rfl) ⟨1717481, by rfl⟩ : syracuseStep 2289975 = 3434963) B3434963
theorem B3864341 : Blo 2289435 3864341 := bbase (se 6 (by rfl) ⟨90570, by rfl⟩ : syracuseStep 3864341 = 181141) (by norm_num)
theorem B2576227 : Blo 2289435 2576227 := bstep (se 1 (by rfl) ⟨1932170, by rfl⟩ : syracuseStep 2576227 = 3864341) B3864341
theorem B3434969 : Blo 2289435 3434969 := bstep (se 2 (by rfl) ⟨1288113, by rfl⟩ : syracuseStep 3434969 = 2576227) B2576227
theorem B2289979 : Blo 2289435 2289979 := bstep (se 1 (by rfl) ⟨1717484, by rfl⟩ : syracuseStep 2289979 = 3434969) B3434969
theorem B13220117 : Blo 2289435 13220117 := bbase (se 6 (by rfl) ⟨309846, by rfl⟩ : syracuseStep 13220117 = 619693) (by norm_num)
theorem B8813411 : Blo 2289435 8813411 := bstep (se 1 (by rfl) ⟨6610058, by rfl⟩ : syracuseStep 8813411 = 13220117) B13220117
theorem B5875607 : Blo 2289435 5875607 := bstep (se 1 (by rfl) ⟨4406705, by rfl⟩ : syracuseStep 5875607 = 8813411) B8813411
theorem B3917071 : Blo 2289435 3917071 := bstep (se 1 (by rfl) ⟨2937803, by rfl⟩ : syracuseStep 3917071 = 5875607) B5875607
theorem B5222761 : Blo 2289435 5222761 := bstep (se 2 (by rfl) ⟨1958535, by rfl⟩ : syracuseStep 5222761 = 3917071) B3917071
theorem B111418901 : Blo 2289435 111418901 := bstep (se 6 (by rfl) ⟨2611380, by rfl⟩ : syracuseStep 111418901 = 5222761) B5222761
theorem B74279267 : Blo 2289435 74279267 := bstep (se 1 (by rfl) ⟨55709450, by rfl⟩ : syracuseStep 74279267 = 111418901) B111418901
theorem B49519511 : Blo 2289435 49519511 := bstep (se 1 (by rfl) ⟨37139633, by rfl⟩ : syracuseStep 49519511 = 74279267) B74279267
theorem B33013007 : Blo 2289435 33013007 := bstep (se 1 (by rfl) ⟨24759755, by rfl⟩ : syracuseStep 33013007 = 49519511) B49519511
theorem B22008671 : Blo 2289435 22008671 := bstep (se 1 (by rfl) ⟨16506503, by rfl⟩ : syracuseStep 22008671 = 33013007) B33013007
theorem B14672447 : Blo 2289435 14672447 := bstep (se 1 (by rfl) ⟨11004335, by rfl⟩ : syracuseStep 14672447 = 22008671) B22008671
theorem B9781631 : Blo 2289435 9781631 := bstep (se 1 (by rfl) ⟨7336223, by rfl⟩ : syracuseStep 9781631 = 14672447) B14672447
theorem B6521087 : Blo 2289435 6521087 := bstep (se 1 (by rfl) ⟨4890815, by rfl⟩ : syracuseStep 6521087 = 9781631) B9781631
theorem B17389565 : Blo 2289435 17389565 := bstep (se 3 (by rfl) ⟨3260543, by rfl⟩ : syracuseStep 17389565 = 6521087) B6521087
theorem B11593043 : Blo 2289435 11593043 := bstep (se 1 (by rfl) ⟨8694782, by rfl⟩ : syracuseStep 11593043 = 17389565) B17389565
theorem B7728695 : Blo 2289435 7728695 := bstep (se 1 (by rfl) ⟨5796521, by rfl⟩ : syracuseStep 7728695 = 11593043) B11593043
theorem B5152463 : Blo 2289435 5152463 := bstep (se 1 (by rfl) ⟨3864347, by rfl⟩ : syracuseStep 5152463 = 7728695) B7728695
theorem B3434975 : Blo 2289435 3434975 := bstep (se 1 (by rfl) ⟨2576231, by rfl⟩ : syracuseStep 3434975 = 5152463) B5152463
theorem B2289983 : Blo 2289435 2289983 := bstep (se 1 (by rfl) ⟨1717487, by rfl⟩ : syracuseStep 2289983 = 3434975) B3434975
theorem B3434981 : Blo 2289435 3434981 := bbase (se 4 (by rfl) ⟨322029, by rfl⟩ : syracuseStep 3434981 = 644059) (by norm_num)
theorem B2289987 : Blo 2289435 2289987 := bstep (se 1 (by rfl) ⟨1717490, by rfl⟩ : syracuseStep 2289987 = 3434981) B3434981
theorem B14672501 : Blo 2289435 14672501 := bbase (se 5 (by rfl) ⟨687773, by rfl⟩ : syracuseStep 14672501 = 1375547) (by norm_num)
theorem B9781667 : Blo 2289435 9781667 := bstep (se 1 (by rfl) ⟨7336250, by rfl⟩ : syracuseStep 9781667 = 14672501) B14672501
theorem B6521111 : Blo 2289435 6521111 := bstep (se 1 (by rfl) ⟨4890833, by rfl⟩ : syracuseStep 6521111 = 9781667) B9781667
theorem B4347407 : Blo 2289435 4347407 := bstep (se 1 (by rfl) ⟨3260555, by rfl⟩ : syracuseStep 4347407 = 6521111) B6521111
theorem B2898271 : Blo 2289435 2898271 := bstep (se 1 (by rfl) ⟨2173703, by rfl⟩ : syracuseStep 2898271 = 4347407) B4347407
theorem B3864361 : Blo 2289435 3864361 := bstep (se 2 (by rfl) ⟨1449135, by rfl⟩ : syracuseStep 3864361 = 2898271) B2898271
theorem B5152481 : Blo 2289435 5152481 := bstep (se 2 (by rfl) ⟨1932180, by rfl⟩ : syracuseStep 5152481 = 3864361) B3864361
theorem B3434987 : Blo 2289435 3434987 := bstep (se 1 (by rfl) ⟨2576240, by rfl⟩ : syracuseStep 3434987 = 5152481) B5152481
theorem B2289991 : Blo 2289435 2289991 := bstep (se 1 (by rfl) ⟨1717493, by rfl⟩ : syracuseStep 2289991 = 3434987) B3434987
theorem B2576245 : Blo 2289435 2576245 := bbase (se 5 (by rfl) ⟨120761, by rfl⟩ : syracuseStep 2576245 = 241523) (by norm_num)
theorem B3434993 : Blo 2289435 3434993 := bstep (se 2 (by rfl) ⟨1288122, by rfl⟩ : syracuseStep 3434993 = 2576245) B2576245
theorem B2289995 : Blo 2289435 2289995 := bstep (se 1 (by rfl) ⟨1717496, by rfl⟩ : syracuseStep 2289995 = 3434993) B3434993
theorem B2898281 : Blo 2289435 2898281 := bbase (se 2 (by rfl) ⟨1086855, by rfl⟩ : syracuseStep 2898281 = 2173711) (by norm_num)
theorem B7728749 : Blo 2289435 7728749 := bstep (se 3 (by rfl) ⟨1449140, by rfl⟩ : syracuseStep 7728749 = 2898281) B2898281
theorem B5152499 : Blo 2289435 5152499 := bstep (se 1 (by rfl) ⟨3864374, by rfl⟩ : syracuseStep 5152499 = 7728749) B7728749
theorem B3434999 : Blo 2289435 3434999 := bstep (se 1 (by rfl) ⟨2576249, by rfl⟩ : syracuseStep 3434999 = 5152499) B5152499
theorem B2289999 : Blo 2289435 2289999 := bstep (se 1 (by rfl) ⟨1717499, by rfl⟩ : syracuseStep 2289999 = 3434999) B3434999
theorem B3435005 : Blo 2289435 3435005 := bbase (se 3 (by rfl) ⟨644063, by rfl⟩ : syracuseStep 3435005 = 1288127) (by norm_num)
theorem B2290003 : Blo 2289435 2290003 := bstep (se 1 (by rfl) ⟨1717502, by rfl⟩ : syracuseStep 2290003 = 3435005) B3435005
theorem B5152517 : Blo 2289435 5152517 := bbase (se 4 (by rfl) ⟨483048, by rfl⟩ : syracuseStep 5152517 = 966097) (by norm_num)
theorem B3435011 : Blo 2289435 3435011 := bstep (se 1 (by rfl) ⟨2576258, by rfl⟩ : syracuseStep 3435011 = 5152517) B5152517
theorem B2290007 : Blo 2289435 2290007 := bstep (se 1 (by rfl) ⟨1717505, by rfl⟩ : syracuseStep 2290007 = 3435011) B3435011
theorem B4347445 : Blo 2289435 4347445 := bbase (se 5 (by rfl) ⟨203786, by rfl⟩ : syracuseStep 4347445 = 407573) (by norm_num)
theorem B5796593 : Blo 2289435 5796593 := bstep (se 2 (by rfl) ⟨2173722, by rfl⟩ : syracuseStep 5796593 = 4347445) B4347445
theorem B3864395 : Blo 2289435 3864395 := bstep (se 1 (by rfl) ⟨2898296, by rfl⟩ : syracuseStep 3864395 = 5796593) B5796593
theorem B2576263 : Blo 2289435 2576263 := bstep (se 1 (by rfl) ⟨1932197, by rfl⟩ : syracuseStep 2576263 = 3864395) B3864395
theorem B3435017 : Blo 2289435 3435017 := bstep (se 2 (by rfl) ⟨1288131, by rfl⟩ : syracuseStep 3435017 = 2576263) B2576263
theorem B2290011 : Blo 2289435 2290011 := bstep (se 1 (by rfl) ⟨1717508, by rfl⟩ : syracuseStep 2290011 = 3435017) B3435017
theorem B11593205 : Blo 2289435 11593205 := bbase (se 5 (by rfl) ⟨543431, by rfl⟩ : syracuseStep 11593205 = 1086863) (by norm_num)
theorem B7728803 : Blo 2289435 7728803 := bstep (se 1 (by rfl) ⟨5796602, by rfl⟩ : syracuseStep 7728803 = 11593205) B11593205
theorem B5152535 : Blo 2289435 5152535 := bstep (se 1 (by rfl) ⟨3864401, by rfl⟩ : syracuseStep 5152535 = 7728803) B7728803
theorem B3435023 : Blo 2289435 3435023 := bstep (se 1 (by rfl) ⟨2576267, by rfl⟩ : syracuseStep 3435023 = 5152535) B5152535
theorem B2290015 : Blo 2289435 2290015 := bstep (se 1 (by rfl) ⟨1717511, by rfl⟩ : syracuseStep 2290015 = 3435023) B3435023
theorem B3435029 : Blo 2289435 3435029 := bbase (se 6 (by rfl) ⟨80508, by rfl⟩ : syracuseStep 3435029 = 161017) (by norm_num)
theorem B2290019 : Blo 2289435 2290019 := bstep (se 1 (by rfl) ⟨1717514, by rfl⟩ : syracuseStep 2290019 = 3435029) B3435029
theorem B19563605 : Blo 2289435 19563605 := bbase (se 8 (by rfl) ⟨114630, by rfl⟩ : syracuseStep 19563605 = 229261) (by norm_num)
theorem B13042403 : Blo 2289435 13042403 := bstep (se 1 (by rfl) ⟨9781802, by rfl⟩ : syracuseStep 13042403 = 19563605) B19563605
theorem B8694935 : Blo 2289435 8694935 := bstep (se 1 (by rfl) ⟨6521201, by rfl⟩ : syracuseStep 8694935 = 13042403) B13042403
theorem B5796623 : Blo 2289435 5796623 := bstep (se 1 (by rfl) ⟨4347467, by rfl⟩ : syracuseStep 5796623 = 8694935) B8694935
theorem B3864415 : Blo 2289435 3864415 := bstep (se 1 (by rfl) ⟨2898311, by rfl⟩ : syracuseStep 3864415 = 5796623) B5796623
theorem B5152553 : Blo 2289435 5152553 := bstep (se 2 (by rfl) ⟨1932207, by rfl⟩ : syracuseStep 5152553 = 3864415) B3864415
theorem B3435035 : Blo 2289435 3435035 := bstep (se 1 (by rfl) ⟨2576276, by rfl⟩ : syracuseStep 3435035 = 5152553) B5152553
theorem B2290023 : Blo 2289435 2290023 := bstep (se 1 (by rfl) ⟨1717517, by rfl⟩ : syracuseStep 2290023 = 3435035) B3435035
theorem B2576281 : Blo 2289435 2576281 := bbase (se 2 (by rfl) ⟨966105, by rfl⟩ : syracuseStep 2576281 = 1932211) (by norm_num)
theorem B3435041 : Blo 2289435 3435041 := bstep (se 2 (by rfl) ⟨1288140, by rfl⟩ : syracuseStep 3435041 = 2576281) B2576281
theorem B2290027 : Blo 2289435 2290027 := bstep (se 1 (by rfl) ⟨1717520, by rfl⟩ : syracuseStep 2290027 = 3435041) B3435041
theorem B8694965 : Blo 2289435 8694965 := bbase (se 5 (by rfl) ⟨407576, by rfl⟩ : syracuseStep 8694965 = 815153) (by norm_num)
theorem B5796643 : Blo 2289435 5796643 := bstep (se 1 (by rfl) ⟨4347482, by rfl⟩ : syracuseStep 5796643 = 8694965) B8694965
theorem B7728857 : Blo 2289435 7728857 := bstep (se 2 (by rfl) ⟨2898321, by rfl⟩ : syracuseStep 7728857 = 5796643) B5796643
theorem B5152571 : Blo 2289435 5152571 := bstep (se 1 (by rfl) ⟨3864428, by rfl⟩ : syracuseStep 5152571 = 7728857) B7728857
theorem B3435047 : Blo 2289435 3435047 := bstep (se 1 (by rfl) ⟨2576285, by rfl⟩ : syracuseStep 3435047 = 5152571) B5152571
theorem B2290031 : Blo 2289435 2290031 := bstep (se 1 (by rfl) ⟨1717523, by rfl⟩ : syracuseStep 2290031 = 3435047) B3435047
theorem B3435053 : Blo 2289435 3435053 := bbase (se 3 (by rfl) ⟨644072, by rfl⟩ : syracuseStep 3435053 = 1288145) (by norm_num)
theorem B2290035 : Blo 2289435 2290035 := bstep (se 1 (by rfl) ⟨1717526, by rfl⟩ : syracuseStep 2290035 = 3435053) B3435053
theorem B5152589 : Blo 2289435 5152589 := bbase (se 3 (by rfl) ⟨966110, by rfl⟩ : syracuseStep 5152589 = 1932221) (by norm_num)
theorem B3435059 : Blo 2289435 3435059 := bstep (se 1 (by rfl) ⟨2576294, by rfl⟩ : syracuseStep 3435059 = 5152589) B5152589
theorem B2290039 : Blo 2289435 2290039 := bstep (se 1 (by rfl) ⟨1717529, by rfl⟩ : syracuseStep 2290039 = 3435059) B3435059
theorem B2898337 : Blo 2289435 2898337 := bbase (se 2 (by rfl) ⟨1086876, by rfl⟩ : syracuseStep 2898337 = 2173753) (by norm_num)
theorem B3864449 : Blo 2289435 3864449 := bstep (se 2 (by rfl) ⟨1449168, by rfl⟩ : syracuseStep 3864449 = 2898337) B2898337
theorem B2576299 : Blo 2289435 2576299 := bstep (se 1 (by rfl) ⟨1932224, by rfl⟩ : syracuseStep 2576299 = 3864449) B3864449
theorem B3435065 : Blo 2289435 3435065 := bstep (se 2 (by rfl) ⟨1288149, by rfl⟩ : syracuseStep 3435065 = 2576299) B2576299
theorem B2290043 : Blo 2289435 2290043 := bstep (se 1 (by rfl) ⟨1717532, by rfl⟩ : syracuseStep 2290043 = 3435065) B3435065
theorem B26085077 : Blo 2289435 26085077 := bbase (se 7 (by rfl) ⟨305684, by rfl⟩ : syracuseStep 26085077 = 611369) (by norm_num)
theorem B17390051 : Blo 2289435 17390051 := bstep (se 1 (by rfl) ⟨13042538, by rfl⟩ : syracuseStep 17390051 = 26085077) B26085077
theorem B11593367 : Blo 2289435 11593367 := bstep (se 1 (by rfl) ⟨8695025, by rfl⟩ : syracuseStep 11593367 = 17390051) B17390051
theorem B7728911 : Blo 2289435 7728911 := bstep (se 1 (by rfl) ⟨5796683, by rfl⟩ : syracuseStep 7728911 = 11593367) B11593367
theorem B5152607 : Blo 2289435 5152607 := bstep (se 1 (by rfl) ⟨3864455, by rfl⟩ : syracuseStep 5152607 = 7728911) B7728911
theorem B3435071 : Blo 2289435 3435071 := bstep (se 1 (by rfl) ⟨2576303, by rfl⟩ : syracuseStep 3435071 = 5152607) B5152607
theorem B2290047 : Blo 2289435 2290047 := bstep (se 1 (by rfl) ⟨1717535, by rfl⟩ : syracuseStep 2290047 = 3435071) B3435071
theorem B3435077 : Blo 2289435 3435077 := bbase (se 4 (by rfl) ⟨322038, by rfl⟩ : syracuseStep 3435077 = 644077) (by norm_num)
theorem B2290051 : Blo 2289435 2290051 := bstep (se 1 (by rfl) ⟨1717538, by rfl⟩ : syracuseStep 2290051 = 3435077) B3435077
theorem B3864469 : Blo 2289435 3864469 := bbase (se 6 (by rfl) ⟨90573, by rfl⟩ : syracuseStep 3864469 = 181147) (by norm_num)
theorem B5152625 : Blo 2289435 5152625 := bstep (se 2 (by rfl) ⟨1932234, by rfl⟩ : syracuseStep 5152625 = 3864469) B3864469
theorem B3435083 : Blo 2289435 3435083 := bstep (se 1 (by rfl) ⟨2576312, by rfl⟩ : syracuseStep 3435083 = 5152625) B5152625
theorem B2290055 : Blo 2289435 2290055 := bstep (se 1 (by rfl) ⟨1717541, by rfl⟩ : syracuseStep 2290055 = 3435083) B3435083
theorem B2576317 : Blo 2289435 2576317 := bbase (se 3 (by rfl) ⟨483059, by rfl⟩ : syracuseStep 2576317 = 966119) (by norm_num)
theorem B3435089 : Blo 2289435 3435089 := bstep (se 2 (by rfl) ⟨1288158, by rfl⟩ : syracuseStep 3435089 = 2576317) B2576317
theorem B2290059 : Blo 2289435 2290059 := bstep (se 1 (by rfl) ⟨1717544, by rfl⟩ : syracuseStep 2290059 = 3435089) B3435089
theorem B7728965 : Blo 2289435 7728965 := bbase (se 4 (by rfl) ⟨724590, by rfl⟩ : syracuseStep 7728965 = 1449181) (by norm_num)
theorem B5152643 : Blo 2289435 5152643 := bstep (se 1 (by rfl) ⟨3864482, by rfl⟩ : syracuseStep 5152643 = 7728965) B7728965
theorem B3435095 : Blo 2289435 3435095 := bstep (se 1 (by rfl) ⟨2576321, by rfl⟩ : syracuseStep 3435095 = 5152643) B5152643
theorem B2290063 : Blo 2289435 2290063 := bstep (se 1 (by rfl) ⟨1717547, by rfl⟩ : syracuseStep 2290063 = 3435095) B3435095
theorem B3435101 : Blo 2289435 3435101 := bbase (se 3 (by rfl) ⟨644081, by rfl⟩ : syracuseStep 3435101 = 1288163) (by norm_num)
theorem B2290067 : Blo 2289435 2290067 := bstep (se 1 (by rfl) ⟨1717550, by rfl⟩ : syracuseStep 2290067 = 3435101) B3435101
theorem B5152661 : Blo 2289435 5152661 := bbase (se 6 (by rfl) ⟨120765, by rfl⟩ : syracuseStep 5152661 = 241531) (by norm_num)
theorem B3435107 : Blo 2289435 3435107 := bstep (se 1 (by rfl) ⟨2576330, by rfl⟩ : syracuseStep 3435107 = 5152661) B5152661
theorem B2290071 : Blo 2289435 2290071 := bstep (se 1 (by rfl) ⟨1717553, by rfl⟩ : syracuseStep 2290071 = 3435107) B3435107
theorem B4891013 : Blo 2289435 4891013 := bbase (se 4 (by rfl) ⟨458532, by rfl⟩ : syracuseStep 4891013 = 917065) (by norm_num)
theorem B3260675 : Blo 2289435 3260675 := bstep (se 1 (by rfl) ⟨2445506, by rfl⟩ : syracuseStep 3260675 = 4891013) B4891013
theorem B8695133 : Blo 2289435 8695133 := bstep (se 3 (by rfl) ⟨1630337, by rfl⟩ : syracuseStep 8695133 = 3260675) B3260675
theorem B5796755 : Blo 2289435 5796755 := bstep (se 1 (by rfl) ⟨4347566, by rfl⟩ : syracuseStep 5796755 = 8695133) B8695133
theorem B3864503 : Blo 2289435 3864503 := bstep (se 1 (by rfl) ⟨2898377, by rfl⟩ : syracuseStep 3864503 = 5796755) B5796755
theorem B2576335 : Blo 2289435 2576335 := bstep (se 1 (by rfl) ⟨1932251, by rfl⟩ : syracuseStep 2576335 = 3864503) B3864503
theorem B3435113 : Blo 2289435 3435113 := bstep (se 2 (by rfl) ⟨1288167, by rfl⟩ : syracuseStep 3435113 = 2576335) B2576335
theorem B2290075 : Blo 2289435 2290075 := bstep (se 1 (by rfl) ⟨1717556, by rfl⟩ : syracuseStep 2290075 = 3435113) B3435113
theorem B5222981 : Blo 2289435 5222981 := bbase (se 4 (by rfl) ⟨489654, by rfl⟩ : syracuseStep 5222981 = 979309) (by norm_num)
theorem B13927949 : Blo 2289435 13927949 := bstep (se 3 (by rfl) ⟨2611490, by rfl⟩ : syracuseStep 13927949 = 5222981) B5222981
theorem B9285299 : Blo 2289435 9285299 := bstep (se 1 (by rfl) ⟨6963974, by rfl⟩ : syracuseStep 9285299 = 13927949) B13927949
theorem B6190199 : Blo 2289435 6190199 := bstep (se 1 (by rfl) ⟨4642649, by rfl⟩ : syracuseStep 6190199 = 9285299) B9285299
theorem B4126799 : Blo 2289435 4126799 := bstep (se 1 (by rfl) ⟨3095099, by rfl⟩ : syracuseStep 4126799 = 6190199) B6190199
theorem B11004797 : Blo 2289435 11004797 := bstep (se 3 (by rfl) ⟨2063399, by rfl⟩ : syracuseStep 11004797 = 4126799) B4126799
theorem B7336531 : Blo 2289435 7336531 := bstep (se 1 (by rfl) ⟨5502398, by rfl⟩ : syracuseStep 7336531 = 11004797) B11004797
theorem B9782041 : Blo 2289435 9782041 := bstep (se 2 (by rfl) ⟨3668265, by rfl⟩ : syracuseStep 9782041 = 7336531) B7336531
theorem B13042721 : Blo 2289435 13042721 := bstep (se 2 (by rfl) ⟨4891020, by rfl⟩ : syracuseStep 13042721 = 9782041) B9782041
theorem B8695147 : Blo 2289435 8695147 := bstep (se 1 (by rfl) ⟨6521360, by rfl⟩ : syracuseStep 8695147 = 13042721) B13042721
theorem B11593529 : Blo 2289435 11593529 := bstep (se 2 (by rfl) ⟨4347573, by rfl⟩ : syracuseStep 11593529 = 8695147) B8695147
theorem B7729019 : Blo 2289435 7729019 := bstep (se 1 (by rfl) ⟨5796764, by rfl⟩ : syracuseStep 7729019 = 11593529) B11593529
theorem B5152679 : Blo 2289435 5152679 := bstep (se 1 (by rfl) ⟨3864509, by rfl⟩ : syracuseStep 5152679 = 7729019) B7729019
theorem B3435119 : Blo 2289435 3435119 := bstep (se 1 (by rfl) ⟨2576339, by rfl⟩ : syracuseStep 3435119 = 5152679) B5152679
theorem B2290079 : Blo 2289435 2290079 := bstep (se 1 (by rfl) ⟨1717559, by rfl⟩ : syracuseStep 2290079 = 3435119) B3435119
theorem B3435125 : Blo 2289435 3435125 := bbase (se 5 (by rfl) ⟨161021, by rfl⟩ : syracuseStep 3435125 = 322043) (by norm_num)
theorem B2290083 : Blo 2289435 2290083 := bstep (se 1 (by rfl) ⟨1717562, by rfl⟩ : syracuseStep 2290083 = 3435125) B3435125
theorem B4347589 : Blo 2289435 4347589 := bbase (se 4 (by rfl) ⟨407586, by rfl⟩ : syracuseStep 4347589 = 815173) (by norm_num)
theorem B5796785 : Blo 2289435 5796785 := bstep (se 2 (by rfl) ⟨2173794, by rfl⟩ : syracuseStep 5796785 = 4347589) B4347589
theorem B3864523 : Blo 2289435 3864523 := bstep (se 1 (by rfl) ⟨2898392, by rfl⟩ : syracuseStep 3864523 = 5796785) B5796785
theorem B5152697 : Blo 2289435 5152697 := bstep (se 2 (by rfl) ⟨1932261, by rfl⟩ : syracuseStep 5152697 = 3864523) B3864523
theorem B3435131 : Blo 2289435 3435131 := bstep (se 1 (by rfl) ⟨2576348, by rfl⟩ : syracuseStep 3435131 = 5152697) B5152697
theorem B2290087 : Blo 2289435 2290087 := bstep (se 1 (by rfl) ⟨1717565, by rfl⟩ : syracuseStep 2290087 = 3435131) B3435131
theorem B2576353 : Blo 2289435 2576353 := bbase (se 2 (by rfl) ⟨966132, by rfl⟩ : syracuseStep 2576353 = 1932265) (by norm_num)
theorem B3435137 : Blo 2289435 3435137 := bstep (se 2 (by rfl) ⟨1288176, by rfl⟩ : syracuseStep 3435137 = 2576353) B2576353
theorem B2290091 : Blo 2289435 2290091 := bstep (se 1 (by rfl) ⟨1717568, by rfl⟩ : syracuseStep 2290091 = 3435137) B3435137
theorem B5796805 : Blo 2289435 5796805 := bbase (se 4 (by rfl) ⟨543450, by rfl⟩ : syracuseStep 5796805 = 1086901) (by norm_num)
theorem B7729073 : Blo 2289435 7729073 := bstep (se 2 (by rfl) ⟨2898402, by rfl⟩ : syracuseStep 7729073 = 5796805) B5796805
theorem B5152715 : Blo 2289435 5152715 := bstep (se 1 (by rfl) ⟨3864536, by rfl⟩ : syracuseStep 5152715 = 7729073) B7729073
theorem B3435143 : Blo 2289435 3435143 := bstep (se 1 (by rfl) ⟨2576357, by rfl⟩ : syracuseStep 3435143 = 5152715) B5152715
theorem B2290095 : Blo 2289435 2290095 := bstep (se 1 (by rfl) ⟨1717571, by rfl⟩ : syracuseStep 2290095 = 3435143) B3435143
theorem B3435149 : Blo 2289435 3435149 := bbase (se 3 (by rfl) ⟨644090, by rfl⟩ : syracuseStep 3435149 = 1288181) (by norm_num)
theorem B2290099 : Blo 2289435 2290099 := bstep (se 1 (by rfl) ⟨1717574, by rfl⟩ : syracuseStep 2290099 = 3435149) B3435149
theorem B5152733 : Blo 2289435 5152733 := bbase (se 3 (by rfl) ⟨966137, by rfl⟩ : syracuseStep 5152733 = 1932275) (by norm_num)
theorem B3435155 : Blo 2289435 3435155 := bstep (se 1 (by rfl) ⟨2576366, by rfl⟩ : syracuseStep 3435155 = 5152733) B5152733
theorem B2290103 : Blo 2289435 2290103 := bstep (se 1 (by rfl) ⟨1717577, by rfl⟩ : syracuseStep 2290103 = 3435155) B3435155
theorem B3864557 : Blo 2289435 3864557 := bbase (se 3 (by rfl) ⟨724604, by rfl⟩ : syracuseStep 3864557 = 1449209) (by norm_num)
theorem B2576371 : Blo 2289435 2576371 := bstep (se 1 (by rfl) ⟨1932278, by rfl⟩ : syracuseStep 2576371 = 3864557) B3864557
theorem B3435161 : Blo 2289435 3435161 := bstep (se 2 (by rfl) ⟨1288185, by rfl⟩ : syracuseStep 3435161 = 2576371) B2576371
theorem B2290107 : Blo 2289435 2290107 := bstep (se 1 (by rfl) ⟨1717580, by rfl⟩ : syracuseStep 2290107 = 3435161) B3435161
theorem B2321357 : Blo 2289435 2321357 := bbase (se 3 (by rfl) ⟨435254, by rfl⟩ : syracuseStep 2321357 = 870509) (by norm_num)
theorem B6190285 : Blo 2289435 6190285 := bstep (se 3 (by rfl) ⟨1160678, by rfl⟩ : syracuseStep 6190285 = 2321357) B2321357
theorem B8253713 : Blo 2289435 8253713 := bstep (se 2 (by rfl) ⟨3095142, by rfl⟩ : syracuseStep 8253713 = 6190285) B6190285
theorem B5502475 : Blo 2289435 5502475 := bstep (se 1 (by rfl) ⟨4126856, by rfl⟩ : syracuseStep 5502475 = 8253713) B8253713
theorem B29346533 : Blo 2289435 29346533 := bstep (se 4 (by rfl) ⟨2751237, by rfl⟩ : syracuseStep 29346533 = 5502475) B5502475
theorem B19564355 : Blo 2289435 19564355 := bstep (se 1 (by rfl) ⟨14673266, by rfl⟩ : syracuseStep 19564355 = 29346533) B29346533
theorem B13042903 : Blo 2289435 13042903 := bstep (se 1 (by rfl) ⟨9782177, by rfl⟩ : syracuseStep 13042903 = 19564355) B19564355
theorem B17390537 : Blo 2289435 17390537 := bstep (se 2 (by rfl) ⟨6521451, by rfl⟩ : syracuseStep 17390537 = 13042903) B13042903
theorem B11593691 : Blo 2289435 11593691 := bstep (se 1 (by rfl) ⟨8695268, by rfl⟩ : syracuseStep 11593691 = 17390537) B17390537
theorem B7729127 : Blo 2289435 7729127 := bstep (se 1 (by rfl) ⟨5796845, by rfl⟩ : syracuseStep 7729127 = 11593691) B11593691
theorem B5152751 : Blo 2289435 5152751 := bstep (se 1 (by rfl) ⟨3864563, by rfl⟩ : syracuseStep 5152751 = 7729127) B7729127
theorem B3435167 : Blo 2289435 3435167 := bstep (se 1 (by rfl) ⟨2576375, by rfl⟩ : syracuseStep 3435167 = 5152751) B5152751
theorem B2290111 : Blo 2289435 2290111 := bstep (se 1 (by rfl) ⟨1717583, by rfl⟩ : syracuseStep 2290111 = 3435167) B3435167
theorem B3435173 : Blo 2289435 3435173 := bbase (se 4 (by rfl) ⟨322047, by rfl⟩ : syracuseStep 3435173 = 644095) (by norm_num)
theorem B2290115 : Blo 2289435 2290115 := bstep (se 1 (by rfl) ⟨1717586, by rfl⟩ : syracuseStep 2290115 = 3435173) B3435173
theorem B2898433 : Blo 2289435 2898433 := bbase (se 2 (by rfl) ⟨1086912, by rfl⟩ : syracuseStep 2898433 = 2173825) (by norm_num)
theorem B3864577 : Blo 2289435 3864577 := bstep (se 2 (by rfl) ⟨1449216, by rfl⟩ : syracuseStep 3864577 = 2898433) B2898433
theorem B5152769 : Blo 2289435 5152769 := bstep (se 2 (by rfl) ⟨1932288, by rfl⟩ : syracuseStep 5152769 = 3864577) B3864577
theorem B3435179 : Blo 2289435 3435179 := bstep (se 1 (by rfl) ⟨2576384, by rfl⟩ : syracuseStep 3435179 = 5152769) B5152769
theorem B2290119 : Blo 2289435 2290119 := bstep (se 1 (by rfl) ⟨1717589, by rfl⟩ : syracuseStep 2290119 = 3435179) B3435179
theorem B2576389 : Blo 2289435 2576389 := bbase (se 4 (by rfl) ⟨241536, by rfl⟩ : syracuseStep 2576389 = 483073) (by norm_num)
theorem B3435185 : Blo 2289435 3435185 := bstep (se 2 (by rfl) ⟨1288194, by rfl⟩ : syracuseStep 3435185 = 2576389) B2576389
theorem B2290123 : Blo 2289435 2290123 := bstep (se 1 (by rfl) ⟨1717592, by rfl⟩ : syracuseStep 2290123 = 3435185) B3435185
theorem B3260749 : Blo 2289435 3260749 := bbase (se 3 (by rfl) ⟨611390, by rfl⟩ : syracuseStep 3260749 = 1222781) (by norm_num)
theorem B4347665 : Blo 2289435 4347665 := bstep (se 2 (by rfl) ⟨1630374, by rfl⟩ : syracuseStep 4347665 = 3260749) B3260749
theorem B2898443 : Blo 2289435 2898443 := bstep (se 1 (by rfl) ⟨2173832, by rfl⟩ : syracuseStep 2898443 = 4347665) B4347665
theorem B7729181 : Blo 2289435 7729181 := bstep (se 3 (by rfl) ⟨1449221, by rfl⟩ : syracuseStep 7729181 = 2898443) B2898443
theorem B5152787 : Blo 2289435 5152787 := bstep (se 1 (by rfl) ⟨3864590, by rfl⟩ : syracuseStep 5152787 = 7729181) B7729181
theorem B3435191 : Blo 2289435 3435191 := bstep (se 1 (by rfl) ⟨2576393, by rfl⟩ : syracuseStep 3435191 = 5152787) B5152787
theorem B2290127 : Blo 2289435 2290127 := bstep (se 1 (by rfl) ⟨1717595, by rfl⟩ : syracuseStep 2290127 = 3435191) B3435191
theorem B3435197 : Blo 2289435 3435197 := bbase (se 3 (by rfl) ⟨644099, by rfl⟩ : syracuseStep 3435197 = 1288199) (by norm_num)
theorem B2290131 : Blo 2289435 2290131 := bstep (se 1 (by rfl) ⟨1717598, by rfl⟩ : syracuseStep 2290131 = 3435197) B3435197
theorem B5152805 : Blo 2289435 5152805 := bbase (se 4 (by rfl) ⟨483075, by rfl⟩ : syracuseStep 5152805 = 966151) (by norm_num)
theorem B3435203 : Blo 2289435 3435203 := bstep (se 1 (by rfl) ⟨2576402, by rfl⟩ : syracuseStep 3435203 = 5152805) B5152805
theorem B2290135 : Blo 2289435 2290135 := bstep (se 1 (by rfl) ⟨1717601, by rfl⟩ : syracuseStep 2290135 = 3435203) B3435203
theorem B5796917 : Blo 2289435 5796917 := bbase (se 5 (by rfl) ⟨271730, by rfl⟩ : syracuseStep 5796917 = 543461) (by norm_num)
theorem B3864611 : Blo 2289435 3864611 := bstep (se 1 (by rfl) ⟨2898458, by rfl⟩ : syracuseStep 3864611 = 5796917) B5796917
theorem B2576407 : Blo 2289435 2576407 := bstep (se 1 (by rfl) ⟨1932305, by rfl⟩ : syracuseStep 2576407 = 3864611) B3864611
theorem B3435209 : Blo 2289435 3435209 := bstep (se 2 (by rfl) ⟨1288203, by rfl⟩ : syracuseStep 3435209 = 2576407) B2576407
theorem B2290139 : Blo 2289435 2290139 := bstep (se 1 (by rfl) ⟨1717604, by rfl⟩ : syracuseStep 2290139 = 3435209) B3435209
theorem B8253829 : Blo 2289435 8253829 := bbase (se 4 (by rfl) ⟨773796, by rfl⟩ : syracuseStep 8253829 = 1547593) (by norm_num)
theorem B11005105 : Blo 2289435 11005105 := bstep (se 2 (by rfl) ⟨4126914, by rfl⟩ : syracuseStep 11005105 = 8253829) B8253829
theorem B14673473 : Blo 2289435 14673473 := bstep (se 2 (by rfl) ⟨5502552, by rfl⟩ : syracuseStep 14673473 = 11005105) B11005105
theorem B9782315 : Blo 2289435 9782315 := bstep (se 1 (by rfl) ⟨7336736, by rfl⟩ : syracuseStep 9782315 = 14673473) B14673473
theorem B6521543 : Blo 2289435 6521543 := bstep (se 1 (by rfl) ⟨4891157, by rfl⟩ : syracuseStep 6521543 = 9782315) B9782315
theorem B4347695 : Blo 2289435 4347695 := bstep (se 1 (by rfl) ⟨3260771, by rfl⟩ : syracuseStep 4347695 = 6521543) B6521543
theorem B11593853 : Blo 2289435 11593853 := bstep (se 3 (by rfl) ⟨2173847, by rfl⟩ : syracuseStep 11593853 = 4347695) B4347695
theorem B7729235 : Blo 2289435 7729235 := bstep (se 1 (by rfl) ⟨5796926, by rfl⟩ : syracuseStep 7729235 = 11593853) B11593853
theorem B5152823 : Blo 2289435 5152823 := bstep (se 1 (by rfl) ⟨3864617, by rfl⟩ : syracuseStep 5152823 = 7729235) B7729235
theorem B3435215 : Blo 2289435 3435215 := bstep (se 1 (by rfl) ⟨2576411, by rfl⟩ : syracuseStep 3435215 = 5152823) B5152823
theorem B2290143 : Blo 2289435 2290143 := bstep (se 1 (by rfl) ⟨1717607, by rfl⟩ : syracuseStep 2290143 = 3435215) B3435215
theorem B3435221 : Blo 2289435 3435221 := bbase (se 7 (by rfl) ⟨40256, by rfl⟩ : syracuseStep 3435221 = 80513) (by norm_num)
theorem B2290147 : Blo 2289435 2290147 := bstep (se 1 (by rfl) ⟨1717610, by rfl⟩ : syracuseStep 2290147 = 3435221) B3435221
theorem B12380789 : Blo 2289435 12380789 := bbase (se 5 (by rfl) ⟨580349, by rfl⟩ : syracuseStep 12380789 = 1160699) (by norm_num)
theorem B8253859 : Blo 2289435 8253859 := bstep (se 1 (by rfl) ⟨6190394, by rfl⟩ : syracuseStep 8253859 = 12380789) B12380789
theorem B11005145 : Blo 2289435 11005145 := bstep (se 2 (by rfl) ⟨4126929, by rfl⟩ : syracuseStep 11005145 = 8253859) B8253859
theorem B7336763 : Blo 2289435 7336763 := bstep (se 1 (by rfl) ⟨5502572, by rfl⟩ : syracuseStep 7336763 = 11005145) B11005145
theorem B4891175 : Blo 2289435 4891175 := bstep (se 1 (by rfl) ⟨3668381, by rfl⟩ : syracuseStep 4891175 = 7336763) B7336763
theorem B3260783 : Blo 2289435 3260783 := bstep (se 1 (by rfl) ⟨2445587, by rfl⟩ : syracuseStep 3260783 = 4891175) B4891175
theorem B8695421 : Blo 2289435 8695421 := bstep (se 3 (by rfl) ⟨1630391, by rfl⟩ : syracuseStep 8695421 = 3260783) B3260783
theorem B5796947 : Blo 2289435 5796947 := bstep (se 1 (by rfl) ⟨4347710, by rfl⟩ : syracuseStep 5796947 = 8695421) B8695421
theorem B3864631 : Blo 2289435 3864631 := bstep (se 1 (by rfl) ⟨2898473, by rfl⟩ : syracuseStep 3864631 = 5796947) B5796947
theorem B5152841 : Blo 2289435 5152841 := bstep (se 2 (by rfl) ⟨1932315, by rfl⟩ : syracuseStep 5152841 = 3864631) B3864631
theorem B3435227 : Blo 2289435 3435227 := bstep (se 1 (by rfl) ⟨2576420, by rfl⟩ : syracuseStep 3435227 = 5152841) B5152841
theorem B2290151 : Blo 2289435 2290151 := bstep (se 1 (by rfl) ⟨1717613, by rfl⟩ : syracuseStep 2290151 = 3435227) B3435227
theorem B2576425 : Blo 2289435 2576425 := bbase (se 2 (by rfl) ⟨966159, by rfl⟩ : syracuseStep 2576425 = 1932319) (by norm_num)
theorem B3435233 : Blo 2289435 3435233 := bstep (se 2 (by rfl) ⟨1288212, by rfl⟩ : syracuseStep 3435233 = 2576425) B2576425
theorem B2290155 : Blo 2289435 2290155 := bstep (se 1 (by rfl) ⟨1717616, by rfl⟩ : syracuseStep 2290155 = 3435233) B3435233
theorem B41785301 : Blo 2289435 41785301 := bbase (se 7 (by rfl) ⟨489671, by rfl⟩ : syracuseStep 41785301 = 979343) (by norm_num)
theorem B27856867 : Blo 2289435 27856867 := bstep (se 1 (by rfl) ⟨20892650, by rfl⟩ : syracuseStep 27856867 = 41785301) B41785301
theorem B37142489 : Blo 2289435 37142489 := bstep (se 2 (by rfl) ⟨13928433, by rfl⟩ : syracuseStep 37142489 = 27856867) B27856867
theorem B24761659 : Blo 2289435 24761659 := bstep (se 1 (by rfl) ⟨18571244, by rfl⟩ : syracuseStep 24761659 = 37142489) B37142489
theorem B33015545 : Blo 2289435 33015545 := bstep (se 2 (by rfl) ⟨12380829, by rfl⟩ : syracuseStep 33015545 = 24761659) B24761659
theorem B22010363 : Blo 2289435 22010363 := bstep (se 1 (by rfl) ⟨16507772, by rfl⟩ : syracuseStep 22010363 = 33015545) B33015545
theorem B14673575 : Blo 2289435 14673575 := bstep (se 1 (by rfl) ⟨11005181, by rfl⟩ : syracuseStep 14673575 = 22010363) B22010363
theorem B9782383 : Blo 2289435 9782383 := bstep (se 1 (by rfl) ⟨7336787, by rfl⟩ : syracuseStep 9782383 = 14673575) B14673575
theorem B13043177 : Blo 2289435 13043177 := bstep (se 2 (by rfl) ⟨4891191, by rfl⟩ : syracuseStep 13043177 = 9782383) B9782383
theorem B8695451 : Blo 2289435 8695451 := bstep (se 1 (by rfl) ⟨6521588, by rfl⟩ : syracuseStep 8695451 = 13043177) B13043177
theorem B5796967 : Blo 2289435 5796967 := bstep (se 1 (by rfl) ⟨4347725, by rfl⟩ : syracuseStep 5796967 = 8695451) B8695451
theorem B7729289 : Blo 2289435 7729289 := bstep (se 2 (by rfl) ⟨2898483, by rfl⟩ : syracuseStep 7729289 = 5796967) B5796967
theorem B5152859 : Blo 2289435 5152859 := bstep (se 1 (by rfl) ⟨3864644, by rfl⟩ : syracuseStep 5152859 = 7729289) B7729289
theorem B3435239 : Blo 2289435 3435239 := bstep (se 1 (by rfl) ⟨2576429, by rfl⟩ : syracuseStep 3435239 = 5152859) B5152859
theorem B2290159 : Blo 2289435 2290159 := bstep (se 1 (by rfl) ⟨1717619, by rfl⟩ : syracuseStep 2290159 = 3435239) B3435239
theorem B3435245 : Blo 2289435 3435245 := bbase (se 3 (by rfl) ⟨644108, by rfl⟩ : syracuseStep 3435245 = 1288217) (by norm_num)
theorem B2290163 : Blo 2289435 2290163 := bstep (se 1 (by rfl) ⟨1717622, by rfl⟩ : syracuseStep 2290163 = 3435245) B3435245
theorem B5152877 : Blo 2289435 5152877 := bbase (se 3 (by rfl) ⟨966164, by rfl⟩ : syracuseStep 5152877 = 1932329) (by norm_num)
theorem B3435251 : Blo 2289435 3435251 := bstep (se 1 (by rfl) ⟨2576438, by rfl⟩ : syracuseStep 3435251 = 5152877) B5152877
theorem B2290167 : Blo 2289435 2290167 := bstep (se 1 (by rfl) ⟨1717625, by rfl⟩ : syracuseStep 2290167 = 3435251) B3435251
theorem B4347749 : Blo 2289435 4347749 := bbase (se 4 (by rfl) ⟨407601, by rfl⟩ : syracuseStep 4347749 = 815203) (by norm_num)
theorem B2898499 : Blo 2289435 2898499 := bstep (se 1 (by rfl) ⟨2173874, by rfl⟩ : syracuseStep 2898499 = 4347749) B4347749
theorem B3864665 : Blo 2289435 3864665 := bstep (se 2 (by rfl) ⟨1449249, by rfl⟩ : syracuseStep 3864665 = 2898499) B2898499
theorem B2576443 : Blo 2289435 2576443 := bstep (se 1 (by rfl) ⟨1932332, by rfl⟩ : syracuseStep 2576443 = 3864665) B3864665
theorem B3435257 : Blo 2289435 3435257 := bstep (se 2 (by rfl) ⟨1288221, by rfl⟩ : syracuseStep 3435257 = 2576443) B2576443
theorem B2290171 : Blo 2289435 2290171 := bstep (se 1 (by rfl) ⟨1717628, by rfl⟩ : syracuseStep 2290171 = 3435257) B3435257
theorem B4706189 : Blo 2289435 4706189 := bbase (se 3 (by rfl) ⟨882410, by rfl⟩ : syracuseStep 4706189 = 1764821) (by norm_num)
theorem B3137459 : Blo 2289435 3137459 := bstep (se 1 (by rfl) ⟨2353094, by rfl⟩ : syracuseStep 3137459 = 4706189) B4706189
theorem B8366557 : Blo 2289435 8366557 := bstep (se 3 (by rfl) ⟨1568729, by rfl⟩ : syracuseStep 8366557 = 3137459) B3137459
theorem B11155409 : Blo 2289435 11155409 := bstep (se 2 (by rfl) ⟨4183278, by rfl⟩ : syracuseStep 11155409 = 8366557) B8366557
theorem B7436939 : Blo 2289435 7436939 := bstep (se 1 (by rfl) ⟨5577704, by rfl⟩ : syracuseStep 7436939 = 11155409) B11155409
theorem B19831837 : Blo 2289435 19831837 := bstep (se 3 (by rfl) ⟨3718469, by rfl⟩ : syracuseStep 19831837 = 7436939) B7436939
theorem B26442449 : Blo 2289435 26442449 := bstep (se 2 (by rfl) ⟨9915918, by rfl⟩ : syracuseStep 26442449 = 19831837) B19831837
theorem B17628299 : Blo 2289435 17628299 := bstep (se 1 (by rfl) ⟨13221224, by rfl⟩ : syracuseStep 17628299 = 26442449) B26442449
theorem B11752199 : Blo 2289435 11752199 := bstep (se 1 (by rfl) ⟨8814149, by rfl⟩ : syracuseStep 11752199 = 17628299) B17628299
theorem B7834799 : Blo 2289435 7834799 := bstep (se 1 (by rfl) ⟨5876099, by rfl⟩ : syracuseStep 7834799 = 11752199) B11752199
theorem B5223199 : Blo 2289435 5223199 := bstep (se 1 (by rfl) ⟨3917399, by rfl⟩ : syracuseStep 5223199 = 7834799) B7834799
theorem B6964265 : Blo 2289435 6964265 := bstep (se 2 (by rfl) ⟨2611599, by rfl⟩ : syracuseStep 6964265 = 5223199) B5223199
theorem B18571373 : Blo 2289435 18571373 := bstep (se 3 (by rfl) ⟨3482132, by rfl⟩ : syracuseStep 18571373 = 6964265) B6964265
theorem B12380915 : Blo 2289435 12380915 := bstep (se 1 (by rfl) ⟨9285686, by rfl⟩ : syracuseStep 12380915 = 18571373) B18571373
theorem B8253943 : Blo 2289435 8253943 := bstep (se 1 (by rfl) ⟨6190457, by rfl⟩ : syracuseStep 8253943 = 12380915) B12380915
theorem B44021029 : Blo 2289435 44021029 := bstep (se 4 (by rfl) ⟨4126971, by rfl⟩ : syracuseStep 44021029 = 8253943) B8253943
theorem B58694705 : Blo 2289435 58694705 := bstep (se 2 (by rfl) ⟨22010514, by rfl⟩ : syracuseStep 58694705 = 44021029) B44021029
theorem B39129803 : Blo 2289435 39129803 := bstep (se 1 (by rfl) ⟨29347352, by rfl⟩ : syracuseStep 39129803 = 58694705) B58694705
theorem B26086535 : Blo 2289435 26086535 := bstep (se 1 (by rfl) ⟨19564901, by rfl⟩ : syracuseStep 26086535 = 39129803) B39129803
theorem B17391023 : Blo 2289435 17391023 := bstep (se 1 (by rfl) ⟨13043267, by rfl⟩ : syracuseStep 17391023 = 26086535) B26086535
theorem B11594015 : Blo 2289435 11594015 := bstep (se 1 (by rfl) ⟨8695511, by rfl⟩ : syracuseStep 11594015 = 17391023) B17391023
theorem B7729343 : Blo 2289435 7729343 := bstep (se 1 (by rfl) ⟨5797007, by rfl⟩ : syracuseStep 7729343 = 11594015) B11594015
theorem B5152895 : Blo 2289435 5152895 := bstep (se 1 (by rfl) ⟨3864671, by rfl⟩ : syracuseStep 5152895 = 7729343) B7729343
theorem B3435263 : Blo 2289435 3435263 := bstep (se 1 (by rfl) ⟨2576447, by rfl⟩ : syracuseStep 3435263 = 5152895) B5152895
theorem B2290175 : Blo 2289435 2290175 := bstep (se 1 (by rfl) ⟨1717631, by rfl⟩ : syracuseStep 2290175 = 3435263) B3435263
theorem B3435269 : Blo 2289435 3435269 := bbase (se 4 (by rfl) ⟨322056, by rfl⟩ : syracuseStep 3435269 = 644113) (by norm_num)
theorem B2290179 : Blo 2289435 2290179 := bstep (se 1 (by rfl) ⟨1717634, by rfl⟩ : syracuseStep 2290179 = 3435269) B3435269
theorem B3864685 : Blo 2289435 3864685 := bbase (se 3 (by rfl) ⟨724628, by rfl⟩ : syracuseStep 3864685 = 1449257) (by norm_num)
theorem B5152913 : Blo 2289435 5152913 := bstep (se 2 (by rfl) ⟨1932342, by rfl⟩ : syracuseStep 5152913 = 3864685) B3864685
theorem B3435275 : Blo 2289435 3435275 := bstep (se 1 (by rfl) ⟨2576456, by rfl⟩ : syracuseStep 3435275 = 5152913) B5152913
theorem B2290183 : Blo 2289435 2290183 := bstep (se 1 (by rfl) ⟨1717637, by rfl⟩ : syracuseStep 2290183 = 3435275) B3435275
theorem B2576461 : Blo 2289435 2576461 := bbase (se 3 (by rfl) ⟨483086, by rfl⟩ : syracuseStep 2576461 = 966173) (by norm_num)
theorem B3435281 : Blo 2289435 3435281 := bstep (se 2 (by rfl) ⟨1288230, by rfl⟩ : syracuseStep 3435281 = 2576461) B2576461
theorem B2290187 : Blo 2289435 2290187 := bstep (se 1 (by rfl) ⟨1717640, by rfl⟩ : syracuseStep 2290187 = 3435281) B3435281
theorem B7729397 : Blo 2289435 7729397 := bbase (se 5 (by rfl) ⟨362315, by rfl⟩ : syracuseStep 7729397 = 724631) (by norm_num)
theorem B5152931 : Blo 2289435 5152931 := bstep (se 1 (by rfl) ⟨3864698, by rfl⟩ : syracuseStep 5152931 = 7729397) B7729397
theorem B3435287 : Blo 2289435 3435287 := bstep (se 1 (by rfl) ⟨2576465, by rfl⟩ : syracuseStep 3435287 = 5152931) B5152931
theorem B2290191 : Blo 2289435 2290191 := bstep (se 1 (by rfl) ⟨1717643, by rfl⟩ : syracuseStep 2290191 = 3435287) B3435287
theorem B3435293 : Blo 2289435 3435293 := bbase (se 3 (by rfl) ⟨644117, by rfl⟩ : syracuseStep 3435293 = 1288235) (by norm_num)
theorem B2290195 : Blo 2289435 2290195 := bstep (se 1 (by rfl) ⟨1717646, by rfl⟩ : syracuseStep 2290195 = 3435293) B3435293
theorem B5152949 : Blo 2289435 5152949 := bbase (se 5 (by rfl) ⟨241544, by rfl⟩ : syracuseStep 5152949 = 483089) (by norm_num)
theorem B3435299 : Blo 2289435 3435299 := bstep (se 1 (by rfl) ⟨2576474, by rfl⟩ : syracuseStep 3435299 = 5152949) B5152949
theorem B2290199 : Blo 2289435 2290199 := bstep (se 1 (by rfl) ⟨1717649, by rfl⟩ : syracuseStep 2290199 = 3435299) B3435299
theorem B2751349 : Blo 2289435 2751349 := bbase (se 5 (by rfl) ⟨128969, by rfl⟩ : syracuseStep 2751349 = 257939) (by norm_num)
theorem B3668465 : Blo 2289435 3668465 := bstep (se 2 (by rfl) ⟨1375674, by rfl⟩ : syracuseStep 3668465 = 2751349) B2751349
theorem B2445643 : Blo 2289435 2445643 := bstep (se 1 (by rfl) ⟨1834232, by rfl⟩ : syracuseStep 2445643 = 3668465) B3668465
theorem B13043429 : Blo 2289435 13043429 := bstep (se 4 (by rfl) ⟨1222821, by rfl⟩ : syracuseStep 13043429 = 2445643) B2445643
theorem B8695619 : Blo 2289435 8695619 := bstep (se 1 (by rfl) ⟨6521714, by rfl⟩ : syracuseStep 8695619 = 13043429) B13043429
theorem B5797079 : Blo 2289435 5797079 := bstep (se 1 (by rfl) ⟨4347809, by rfl⟩ : syracuseStep 5797079 = 8695619) B8695619
theorem B3864719 : Blo 2289435 3864719 := bstep (se 1 (by rfl) ⟨2898539, by rfl⟩ : syracuseStep 3864719 = 5797079) B5797079
theorem B2576479 : Blo 2289435 2576479 := bstep (se 1 (by rfl) ⟨1932359, by rfl⟩ : syracuseStep 2576479 = 3864719) B3864719
theorem B3435305 : Blo 2289435 3435305 := bstep (se 2 (by rfl) ⟨1288239, by rfl⟩ : syracuseStep 3435305 = 2576479) B2576479
theorem B2290203 : Blo 2289435 2290203 := bstep (se 1 (by rfl) ⟨1717652, by rfl⟩ : syracuseStep 2290203 = 3435305) B3435305
theorem B6610709 : Blo 2289435 6610709 := bbase (se 6 (by rfl) ⟨154938, by rfl⟩ : syracuseStep 6610709 = 309877) (by norm_num)
theorem B4407139 : Blo 2289435 4407139 := bstep (se 1 (by rfl) ⟨3305354, by rfl⟩ : syracuseStep 4407139 = 6610709) B6610709
theorem B5876185 : Blo 2289435 5876185 := bstep (se 2 (by rfl) ⟨2203569, by rfl⟩ : syracuseStep 5876185 = 4407139) B4407139
theorem B7834913 : Blo 2289435 7834913 := bstep (se 2 (by rfl) ⟨2938092, by rfl⟩ : syracuseStep 7834913 = 5876185) B5876185
theorem B5223275 : Blo 2289435 5223275 := bstep (se 1 (by rfl) ⟨3917456, by rfl⟩ : syracuseStep 5223275 = 7834913) B7834913
theorem B3482183 : Blo 2289435 3482183 := bstep (se 1 (by rfl) ⟨2611637, by rfl⟩ : syracuseStep 3482183 = 5223275) B5223275
theorem B2321455 : Blo 2289435 2321455 := bstep (se 1 (by rfl) ⟨1741091, by rfl⟩ : syracuseStep 2321455 = 3482183) B3482183
theorem B3095273 : Blo 2289435 3095273 := bstep (se 2 (by rfl) ⟨1160727, by rfl⟩ : syracuseStep 3095273 = 2321455) B2321455
theorem B8254061 : Blo 2289435 8254061 := bstep (se 3 (by rfl) ⟨1547636, by rfl⟩ : syracuseStep 8254061 = 3095273) B3095273
theorem B5502707 : Blo 2289435 5502707 := bstep (se 1 (by rfl) ⟨4127030, by rfl⟩ : syracuseStep 5502707 = 8254061) B8254061
theorem B3668471 : Blo 2289435 3668471 := bstep (se 1 (by rfl) ⟨2751353, by rfl⟩ : syracuseStep 3668471 = 5502707) B5502707
theorem B2445647 : Blo 2289435 2445647 := bstep (se 1 (by rfl) ⟨1834235, by rfl⟩ : syracuseStep 2445647 = 3668471) B3668471
theorem B6521725 : Blo 2289435 6521725 := bstep (se 3 (by rfl) ⟨1222823, by rfl⟩ : syracuseStep 6521725 = 2445647) B2445647
theorem B8695633 : Blo 2289435 8695633 := bstep (se 2 (by rfl) ⟨3260862, by rfl⟩ : syracuseStep 8695633 = 6521725) B6521725
theorem B11594177 : Blo 2289435 11594177 := bstep (se 2 (by rfl) ⟨4347816, by rfl⟩ : syracuseStep 11594177 = 8695633) B8695633
theorem B7729451 : Blo 2289435 7729451 := bstep (se 1 (by rfl) ⟨5797088, by rfl⟩ : syracuseStep 7729451 = 11594177) B11594177
theorem B5152967 : Blo 2289435 5152967 := bstep (se 1 (by rfl) ⟨3864725, by rfl⟩ : syracuseStep 5152967 = 7729451) B7729451
theorem B3435311 : Blo 2289435 3435311 := bstep (se 1 (by rfl) ⟨2576483, by rfl⟩ : syracuseStep 3435311 = 5152967) B5152967
theorem B2290207 : Blo 2289435 2290207 := bstep (se 1 (by rfl) ⟨1717655, by rfl⟩ : syracuseStep 2290207 = 3435311) B3435311
theorem B3435317 : Blo 2289435 3435317 := bbase (se 5 (by rfl) ⟨161030, by rfl⟩ : syracuseStep 3435317 = 322061) (by norm_num)
theorem B2290211 : Blo 2289435 2290211 := bstep (se 1 (by rfl) ⟨1717658, by rfl⟩ : syracuseStep 2290211 = 3435317) B3435317
theorem B5797109 : Blo 2289435 5797109 := bbase (se 5 (by rfl) ⟨271739, by rfl⟩ : syracuseStep 5797109 = 543479) (by norm_num)
theorem B3864739 : Blo 2289435 3864739 := bstep (se 1 (by rfl) ⟨2898554, by rfl⟩ : syracuseStep 3864739 = 5797109) B5797109
theorem B5152985 : Blo 2289435 5152985 := bstep (se 2 (by rfl) ⟨1932369, by rfl⟩ : syracuseStep 5152985 = 3864739) B3864739
theorem B3435323 : Blo 2289435 3435323 := bstep (se 1 (by rfl) ⟨2576492, by rfl⟩ : syracuseStep 3435323 = 5152985) B5152985
theorem B2290215 : Blo 2289435 2290215 := bstep (se 1 (by rfl) ⟨1717661, by rfl⟩ : syracuseStep 2290215 = 3435323) B3435323
theorem B2576497 : Blo 2289435 2576497 := bbase (se 2 (by rfl) ⟨966186, by rfl⟩ : syracuseStep 2576497 = 1932373) (by norm_num)
theorem B3435329 : Blo 2289435 3435329 := bstep (se 2 (by rfl) ⟨1288248, by rfl⟩ : syracuseStep 3435329 = 2576497) B2576497
theorem B2290219 : Blo 2289435 2290219 := bstep (se 1 (by rfl) ⟨1717664, by rfl⟩ : syracuseStep 2290219 = 3435329) B3435329
theorem B2479033 : Blo 2289435 2479033 := bbase (se 2 (by rfl) ⟨929637, by rfl⟩ : syracuseStep 2479033 = 1859275) (by norm_num)
theorem B3305377 : Blo 2289435 3305377 := bstep (se 2 (by rfl) ⟨1239516, by rfl⟩ : syracuseStep 3305377 = 2479033) B2479033
theorem B17628677 : Blo 2289435 17628677 := bstep (se 4 (by rfl) ⟨1652688, by rfl⟩ : syracuseStep 17628677 = 3305377) B3305377
theorem B11752451 : Blo 2289435 11752451 := bstep (se 1 (by rfl) ⟨8814338, by rfl⟩ : syracuseStep 11752451 = 17628677) B17628677
theorem B7834967 : Blo 2289435 7834967 := bstep (se 1 (by rfl) ⟨5876225, by rfl⟩ : syracuseStep 7834967 = 11752451) B11752451
theorem B5223311 : Blo 2289435 5223311 := bstep (se 1 (by rfl) ⟨3917483, by rfl⟩ : syracuseStep 5223311 = 7834967) B7834967
theorem B3482207 : Blo 2289435 3482207 := bstep (se 1 (by rfl) ⟨2611655, by rfl⟩ : syracuseStep 3482207 = 5223311) B5223311
theorem B2321471 : Blo 2289435 2321471 := bstep (se 1 (by rfl) ⟨1741103, by rfl⟩ : syracuseStep 2321471 = 3482207) B3482207
theorem B6190589 : Blo 2289435 6190589 := bstep (se 3 (by rfl) ⟨1160735, by rfl⟩ : syracuseStep 6190589 = 2321471) B2321471
theorem B4127059 : Blo 2289435 4127059 := bstep (se 1 (by rfl) ⟨3095294, by rfl⟩ : syracuseStep 4127059 = 6190589) B6190589
theorem B5502745 : Blo 2289435 5502745 := bstep (se 2 (by rfl) ⟨2063529, by rfl⟩ : syracuseStep 5502745 = 4127059) B4127059
theorem B7336993 : Blo 2289435 7336993 := bstep (se 2 (by rfl) ⟨2751372, by rfl⟩ : syracuseStep 7336993 = 5502745) B5502745
theorem B9782657 : Blo 2289435 9782657 := bstep (se 2 (by rfl) ⟨3668496, by rfl⟩ : syracuseStep 9782657 = 7336993) B7336993
theorem B6521771 : Blo 2289435 6521771 := bstep (se 1 (by rfl) ⟨4891328, by rfl⟩ : syracuseStep 6521771 = 9782657) B9782657
theorem B4347847 : Blo 2289435 4347847 := bstep (se 1 (by rfl) ⟨3260885, by rfl⟩ : syracuseStep 4347847 = 6521771) B6521771
theorem B5797129 : Blo 2289435 5797129 := bstep (se 2 (by rfl) ⟨2173923, by rfl⟩ : syracuseStep 5797129 = 4347847) B4347847
theorem B7729505 : Blo 2289435 7729505 := bstep (se 2 (by rfl) ⟨2898564, by rfl⟩ : syracuseStep 7729505 = 5797129) B5797129
theorem B5153003 : Blo 2289435 5153003 := bstep (se 1 (by rfl) ⟨3864752, by rfl⟩ : syracuseStep 5153003 = 7729505) B7729505
theorem B3435335 : Blo 2289435 3435335 := bstep (se 1 (by rfl) ⟨2576501, by rfl⟩ : syracuseStep 3435335 = 5153003) B5153003
theorem B2290223 : Blo 2289435 2290223 := bstep (se 1 (by rfl) ⟨1717667, by rfl⟩ : syracuseStep 2290223 = 3435335) B3435335
theorem B3435341 : Blo 2289435 3435341 := bbase (se 3 (by rfl) ⟨644126, by rfl⟩ : syracuseStep 3435341 = 1288253) (by norm_num)
theorem B2290227 : Blo 2289435 2290227 := bstep (se 1 (by rfl) ⟨1717670, by rfl⟩ : syracuseStep 2290227 = 3435341) B3435341
theorem B5153021 : Blo 2289435 5153021 := bbase (se 3 (by rfl) ⟨966191, by rfl⟩ : syracuseStep 5153021 = 1932383) (by norm_num)
theorem B3435347 : Blo 2289435 3435347 := bstep (se 1 (by rfl) ⟨2576510, by rfl⟩ : syracuseStep 3435347 = 5153021) B5153021
theorem B2290231 : Blo 2289435 2290231 := bstep (se 1 (by rfl) ⟨1717673, by rfl⟩ : syracuseStep 2290231 = 3435347) B3435347
theorem B3864773 : Blo 2289435 3864773 := bbase (se 4 (by rfl) ⟨362322, by rfl⟩ : syracuseStep 3864773 = 724645) (by norm_num)
theorem B2576515 : Blo 2289435 2576515 := bstep (se 1 (by rfl) ⟨1932386, by rfl⟩ : syracuseStep 2576515 = 3864773) B3864773
theorem B3435353 : Blo 2289435 3435353 := bstep (se 2 (by rfl) ⟨1288257, by rfl⟩ : syracuseStep 3435353 = 2576515) B2576515
theorem B2290235 : Blo 2289435 2290235 := bstep (se 1 (by rfl) ⟨1717676, by rfl⟩ : syracuseStep 2290235 = 3435353) B3435353
theorem B17391509 : Blo 2289435 17391509 := bbase (se 6 (by rfl) ⟨407613, by rfl⟩ : syracuseStep 17391509 = 815227) (by norm_num)
theorem B11594339 : Blo 2289435 11594339 := bstep (se 1 (by rfl) ⟨8695754, by rfl⟩ : syracuseStep 11594339 = 17391509) B17391509
theorem B7729559 : Blo 2289435 7729559 := bstep (se 1 (by rfl) ⟨5797169, by rfl⟩ : syracuseStep 7729559 = 11594339) B11594339
theorem B5153039 : Blo 2289435 5153039 := bstep (se 1 (by rfl) ⟨3864779, by rfl⟩ : syracuseStep 5153039 = 7729559) B7729559
theorem B3435359 : Blo 2289435 3435359 := bstep (se 1 (by rfl) ⟨2576519, by rfl⟩ : syracuseStep 3435359 = 5153039) B5153039
theorem B2290239 : Blo 2289435 2290239 := bstep (se 1 (by rfl) ⟨1717679, by rfl⟩ : syracuseStep 2290239 = 3435359) B3435359
theorem B3435365 : Blo 2289435 3435365 := bbase (se 4 (by rfl) ⟨322065, by rfl⟩ : syracuseStep 3435365 = 644131) (by norm_num)
theorem B2290243 : Blo 2289435 2290243 := bstep (se 1 (by rfl) ⟨1717682, by rfl⟩ : syracuseStep 2290243 = 3435365) B3435365
theorem B4347893 : Blo 2289435 4347893 := bbase (se 5 (by rfl) ⟨203807, by rfl⟩ : syracuseStep 4347893 = 407615) (by norm_num)
theorem B2898595 : Blo 2289435 2898595 := bstep (se 1 (by rfl) ⟨2173946, by rfl⟩ : syracuseStep 2898595 = 4347893) B4347893
theorem B3864793 : Blo 2289435 3864793 := bstep (se 2 (by rfl) ⟨1449297, by rfl⟩ : syracuseStep 3864793 = 2898595) B2898595
theorem B5153057 : Blo 2289435 5153057 := bstep (se 2 (by rfl) ⟨1932396, by rfl⟩ : syracuseStep 5153057 = 3864793) B3864793
theorem B3435371 : Blo 2289435 3435371 := bstep (se 1 (by rfl) ⟨2576528, by rfl⟩ : syracuseStep 3435371 = 5153057) B5153057
theorem B2290247 : Blo 2289435 2290247 := bstep (se 1 (by rfl) ⟨1717685, by rfl⟩ : syracuseStep 2290247 = 3435371) B3435371
theorem B2576533 : Blo 2289435 2576533 := bbase (se 6 (by rfl) ⟨60387, by rfl⟩ : syracuseStep 2576533 = 120775) (by norm_num)
theorem B3435377 : Blo 2289435 3435377 := bstep (se 2 (by rfl) ⟨1288266, by rfl⟩ : syracuseStep 3435377 = 2576533) B2576533
theorem B2290251 : Blo 2289435 2290251 := bstep (se 1 (by rfl) ⟨1717688, by rfl⟩ : syracuseStep 2290251 = 3435377) B3435377
theorem B2898605 : Blo 2289435 2898605 := bbase (se 3 (by rfl) ⟨543488, by rfl⟩ : syracuseStep 2898605 = 1086977) (by norm_num)
theorem B7729613 : Blo 2289435 7729613 := bstep (se 3 (by rfl) ⟨1449302, by rfl⟩ : syracuseStep 7729613 = 2898605) B2898605
theorem B5153075 : Blo 2289435 5153075 := bstep (se 1 (by rfl) ⟨3864806, by rfl⟩ : syracuseStep 5153075 = 7729613) B7729613
theorem B3435383 : Blo 2289435 3435383 := bstep (se 1 (by rfl) ⟨2576537, by rfl⟩ : syracuseStep 3435383 = 5153075) B5153075
theorem B2290255 : Blo 2289435 2290255 := bstep (se 1 (by rfl) ⟨1717691, by rfl⟩ : syracuseStep 2290255 = 3435383) B3435383
theorem B3435389 : Blo 2289435 3435389 := bbase (se 3 (by rfl) ⟨644135, by rfl⟩ : syracuseStep 3435389 = 1288271) (by norm_num)
theorem B2290259 : Blo 2289435 2290259 := bstep (se 1 (by rfl) ⟨1717694, by rfl⟩ : syracuseStep 2290259 = 3435389) B3435389
theorem B5153093 : Blo 2289435 5153093 := bbase (se 4 (by rfl) ⟨483102, by rfl⟩ : syracuseStep 5153093 = 966205) (by norm_num)
theorem B3435395 : Blo 2289435 3435395 := bstep (se 1 (by rfl) ⟨2576546, by rfl⟩ : syracuseStep 3435395 = 5153093) B5153093
theorem B2290263 : Blo 2289435 2290263 := bstep (se 1 (by rfl) ⟨1717697, by rfl⟩ : syracuseStep 2290263 = 3435395) B3435395
theorem B10446821 : Blo 2289435 10446821 := bbase (se 4 (by rfl) ⟨979389, by rfl⟩ : syracuseStep 10446821 = 1958779) (by norm_num)
theorem B6964547 : Blo 2289435 6964547 := bstep (se 1 (by rfl) ⟨5223410, by rfl⟩ : syracuseStep 6964547 = 10446821) B10446821
theorem B18572125 : Blo 2289435 18572125 := bstep (se 3 (by rfl) ⟨3482273, by rfl⟩ : syracuseStep 18572125 = 6964547) B6964547
theorem B24762833 : Blo 2289435 24762833 := bstep (se 2 (by rfl) ⟨9286062, by rfl⟩ : syracuseStep 24762833 = 18572125) B18572125
theorem B16508555 : Blo 2289435 16508555 := bstep (se 1 (by rfl) ⟨12381416, by rfl⟩ : syracuseStep 16508555 = 24762833) B24762833
theorem B11005703 : Blo 2289435 11005703 := bstep (se 1 (by rfl) ⟨8254277, by rfl⟩ : syracuseStep 11005703 = 16508555) B16508555
theorem B7337135 : Blo 2289435 7337135 := bstep (se 1 (by rfl) ⟨5502851, by rfl⟩ : syracuseStep 7337135 = 11005703) B11005703
theorem B4891423 : Blo 2289435 4891423 := bstep (se 1 (by rfl) ⟨3668567, by rfl⟩ : syracuseStep 4891423 = 7337135) B7337135
theorem B6521897 : Blo 2289435 6521897 := bstep (se 2 (by rfl) ⟨2445711, by rfl⟩ : syracuseStep 6521897 = 4891423) B4891423
theorem B4347931 : Blo 2289435 4347931 := bstep (se 1 (by rfl) ⟨3260948, by rfl⟩ : syracuseStep 4347931 = 6521897) B6521897
theorem B5797241 : Blo 2289435 5797241 := bstep (se 2 (by rfl) ⟨2173965, by rfl⟩ : syracuseStep 5797241 = 4347931) B4347931
theorem B3864827 : Blo 2289435 3864827 := bstep (se 1 (by rfl) ⟨2898620, by rfl⟩ : syracuseStep 3864827 = 5797241) B5797241
theorem B2576551 : Blo 2289435 2576551 := bstep (se 1 (by rfl) ⟨1932413, by rfl⟩ : syracuseStep 2576551 = 3864827) B3864827
theorem B3435401 : Blo 2289435 3435401 := bstep (se 2 (by rfl) ⟨1288275, by rfl⟩ : syracuseStep 3435401 = 2576551) B2576551
theorem B2290267 : Blo 2289435 2290267 := bstep (se 1 (by rfl) ⟨1717700, by rfl⟩ : syracuseStep 2290267 = 3435401) B3435401
theorem B11594501 : Blo 2289435 11594501 := bbase (se 4 (by rfl) ⟨1086984, by rfl⟩ : syracuseStep 11594501 = 2173969) (by norm_num)
theorem B7729667 : Blo 2289435 7729667 := bstep (se 1 (by rfl) ⟨5797250, by rfl⟩ : syracuseStep 7729667 = 11594501) B11594501
theorem B5153111 : Blo 2289435 5153111 := bstep (se 1 (by rfl) ⟨3864833, by rfl⟩ : syracuseStep 5153111 = 7729667) B7729667
theorem B3435407 : Blo 2289435 3435407 := bstep (se 1 (by rfl) ⟨2576555, by rfl⟩ : syracuseStep 3435407 = 5153111) B5153111
theorem B2290271 : Blo 2289435 2290271 := bstep (se 1 (by rfl) ⟨1717703, by rfl⟩ : syracuseStep 2290271 = 3435407) B3435407
theorem B3435413 : Blo 2289435 3435413 := bbase (se 6 (by rfl) ⟨80517, by rfl⟩ : syracuseStep 3435413 = 161035) (by norm_num)
theorem B2290275 : Blo 2289435 2290275 := bstep (se 1 (by rfl) ⟨1717706, by rfl⟩ : syracuseStep 2290275 = 3435413) B3435413
theorem B13043861 : Blo 2289435 13043861 := bbase (se 6 (by rfl) ⟨305715, by rfl⟩ : syracuseStep 13043861 = 611431) (by norm_num)
theorem B8695907 : Blo 2289435 8695907 := bstep (se 1 (by rfl) ⟨6521930, by rfl⟩ : syracuseStep 8695907 = 13043861) B13043861
theorem B5797271 : Blo 2289435 5797271 := bstep (se 1 (by rfl) ⟨4347953, by rfl⟩ : syracuseStep 5797271 = 8695907) B8695907
theorem B3864847 : Blo 2289435 3864847 := bstep (se 1 (by rfl) ⟨2898635, by rfl⟩ : syracuseStep 3864847 = 5797271) B5797271
theorem B5153129 : Blo 2289435 5153129 := bstep (se 2 (by rfl) ⟨1932423, by rfl⟩ : syracuseStep 5153129 = 3864847) B3864847
theorem B3435419 : Blo 2289435 3435419 := bstep (se 1 (by rfl) ⟨2576564, by rfl⟩ : syracuseStep 3435419 = 5153129) B5153129
theorem B2290279 : Blo 2289435 2290279 := bstep (se 1 (by rfl) ⟨1717709, by rfl⟩ : syracuseStep 2290279 = 3435419) B3435419
theorem B2576569 : Blo 2289435 2576569 := bbase (se 2 (by rfl) ⟨966213, by rfl⟩ : syracuseStep 2576569 = 1932427) (by norm_num)
theorem B3435425 : Blo 2289435 3435425 := bstep (se 2 (by rfl) ⟨1288284, by rfl⟩ : syracuseStep 3435425 = 2576569) B2576569
theorem B2290283 : Blo 2289435 2290283 := bstep (se 1 (by rfl) ⟨1717712, by rfl⟩ : syracuseStep 2290283 = 3435425) B3435425
theorem B3095381 : Blo 2289435 3095381 := bbase (se 9 (by rfl) ⟨9068, by rfl⟩ : syracuseStep 3095381 = 18137) (by norm_num)
theorem B8254349 : Blo 2289435 8254349 := bstep (se 3 (by rfl) ⟨1547690, by rfl⟩ : syracuseStep 8254349 = 3095381) B3095381
theorem B5502899 : Blo 2289435 5502899 := bstep (se 1 (by rfl) ⟨4127174, by rfl⟩ : syracuseStep 5502899 = 8254349) B8254349
theorem B3668599 : Blo 2289435 3668599 := bstep (se 1 (by rfl) ⟨2751449, by rfl⟩ : syracuseStep 3668599 = 5502899) B5502899
theorem B4891465 : Blo 2289435 4891465 := bstep (se 2 (by rfl) ⟨1834299, by rfl⟩ : syracuseStep 4891465 = 3668599) B3668599
theorem B6521953 : Blo 2289435 6521953 := bstep (se 2 (by rfl) ⟨2445732, by rfl⟩ : syracuseStep 6521953 = 4891465) B4891465
theorem B8695937 : Blo 2289435 8695937 := bstep (se 2 (by rfl) ⟨3260976, by rfl⟩ : syracuseStep 8695937 = 6521953) B6521953
theorem B5797291 : Blo 2289435 5797291 := bstep (se 1 (by rfl) ⟨4347968, by rfl⟩ : syracuseStep 5797291 = 8695937) B8695937
theorem B7729721 : Blo 2289435 7729721 := bstep (se 2 (by rfl) ⟨2898645, by rfl⟩ : syracuseStep 7729721 = 5797291) B5797291
theorem B5153147 : Blo 2289435 5153147 := bstep (se 1 (by rfl) ⟨3864860, by rfl⟩ : syracuseStep 5153147 = 7729721) B7729721
theorem B3435431 : Blo 2289435 3435431 := bstep (se 1 (by rfl) ⟨2576573, by rfl⟩ : syracuseStep 3435431 = 5153147) B5153147
theorem B2290287 : Blo 2289435 2290287 := bstep (se 1 (by rfl) ⟨1717715, by rfl⟩ : syracuseStep 2290287 = 3435431) B3435431
theorem B3435437 : Blo 2289435 3435437 := bbase (se 3 (by rfl) ⟨644144, by rfl⟩ : syracuseStep 3435437 = 1288289) (by norm_num)
theorem B2290291 : Blo 2289435 2290291 := bstep (se 1 (by rfl) ⟨1717718, by rfl⟩ : syracuseStep 2290291 = 3435437) B3435437
theorem B5153165 : Blo 2289435 5153165 := bbase (se 3 (by rfl) ⟨966218, by rfl⟩ : syracuseStep 5153165 = 1932437) (by norm_num)
theorem B3435443 : Blo 2289435 3435443 := bstep (se 1 (by rfl) ⟨2576582, by rfl⟩ : syracuseStep 3435443 = 5153165) B5153165
theorem B2290295 : Blo 2289435 2290295 := bstep (se 1 (by rfl) ⟨1717721, by rfl⟩ : syracuseStep 2290295 = 3435443) B3435443
theorem B2898661 : Blo 2289435 2898661 := bbase (se 4 (by rfl) ⟨271749, by rfl⟩ : syracuseStep 2898661 = 543499) (by norm_num)
theorem B3864881 : Blo 2289435 3864881 := bstep (se 2 (by rfl) ⟨1449330, by rfl⟩ : syracuseStep 3864881 = 2898661) B2898661
theorem B2576587 : Blo 2289435 2576587 := bstep (se 1 (by rfl) ⟨1932440, by rfl⟩ : syracuseStep 2576587 = 3864881) B3864881
theorem B3435449 : Blo 2289435 3435449 := bstep (se 2 (by rfl) ⟨1288293, by rfl⟩ : syracuseStep 3435449 = 2576587) B2576587
theorem B2290299 : Blo 2289435 2290299 := bstep (se 1 (by rfl) ⟨1717724, by rfl⟩ : syracuseStep 2290299 = 3435449) B3435449
theorem B6610981 : Blo 2289435 6610981 := bbase (se 4 (by rfl) ⟨619779, by rfl⟩ : syracuseStep 6610981 = 1239559) (by norm_num)
theorem B8814641 : Blo 2289435 8814641 := bstep (se 2 (by rfl) ⟨3305490, by rfl⟩ : syracuseStep 8814641 = 6610981) B6610981
theorem B23505709 : Blo 2289435 23505709 := bstep (se 3 (by rfl) ⟨4407320, by rfl⟩ : syracuseStep 23505709 = 8814641) B8814641
theorem B31340945 : Blo 2289435 31340945 := bstep (se 2 (by rfl) ⟨11752854, by rfl⟩ : syracuseStep 31340945 = 23505709) B23505709
theorem B20893963 : Blo 2289435 20893963 := bstep (se 1 (by rfl) ⟨15670472, by rfl⟩ : syracuseStep 20893963 = 31340945) B31340945
theorem B27858617 : Blo 2289435 27858617 := bstep (se 2 (by rfl) ⟨10446981, by rfl⟩ : syracuseStep 27858617 = 20893963) B20893963
theorem B18572411 : Blo 2289435 18572411 := bstep (se 1 (by rfl) ⟨13929308, by rfl⟩ : syracuseStep 18572411 = 27858617) B27858617
theorem B12381607 : Blo 2289435 12381607 := bstep (se 1 (by rfl) ⟨9286205, by rfl⟩ : syracuseStep 12381607 = 18572411) B18572411
theorem B16508809 : Blo 2289435 16508809 := bstep (se 2 (by rfl) ⟨6190803, by rfl⟩ : syracuseStep 16508809 = 12381607) B12381607
theorem B22011745 : Blo 2289435 22011745 := bstep (se 2 (by rfl) ⟨8254404, by rfl⟩ : syracuseStep 22011745 = 16508809) B16508809
theorem B29348993 : Blo 2289435 29348993 := bstep (se 2 (by rfl) ⟨11005872, by rfl⟩ : syracuseStep 29348993 = 22011745) B22011745
theorem B19565995 : Blo 2289435 19565995 := bstep (se 1 (by rfl) ⟨14674496, by rfl⟩ : syracuseStep 19565995 = 29348993) B29348993
theorem B26087993 : Blo 2289435 26087993 := bstep (se 2 (by rfl) ⟨9782997, by rfl⟩ : syracuseStep 26087993 = 19565995) B19565995
theorem B17391995 : Blo 2289435 17391995 := bstep (se 1 (by rfl) ⟨13043996, by rfl⟩ : syracuseStep 17391995 = 26087993) B26087993
theorem B11594663 : Blo 2289435 11594663 := bstep (se 1 (by rfl) ⟨8695997, by rfl⟩ : syracuseStep 11594663 = 17391995) B17391995
theorem B7729775 : Blo 2289435 7729775 := bstep (se 1 (by rfl) ⟨5797331, by rfl⟩ : syracuseStep 7729775 = 11594663) B11594663
theorem B5153183 : Blo 2289435 5153183 := bstep (se 1 (by rfl) ⟨3864887, by rfl⟩ : syracuseStep 5153183 = 7729775) B7729775
theorem B3435455 : Blo 2289435 3435455 := bstep (se 1 (by rfl) ⟨2576591, by rfl⟩ : syracuseStep 3435455 = 5153183) B5153183
theorem B2290303 : Blo 2289435 2290303 := bstep (se 1 (by rfl) ⟨1717727, by rfl⟩ : syracuseStep 2290303 = 3435455) B3435455
theorem B3435461 : Blo 2289435 3435461 := bbase (se 4 (by rfl) ⟨322074, by rfl⟩ : syracuseStep 3435461 = 644149) (by norm_num)
theorem B2290307 : Blo 2289435 2290307 := bstep (se 1 (by rfl) ⟨1717730, by rfl⟩ : syracuseStep 2290307 = 3435461) B3435461
theorem B3864901 : Blo 2289435 3864901 := bbase (se 4 (by rfl) ⟨362334, by rfl⟩ : syracuseStep 3864901 = 724669) (by norm_num)
theorem B5153201 : Blo 2289435 5153201 := bstep (se 2 (by rfl) ⟨1932450, by rfl⟩ : syracuseStep 5153201 = 3864901) B3864901
theorem B3435467 : Blo 2289435 3435467 := bstep (se 1 (by rfl) ⟨2576600, by rfl⟩ : syracuseStep 3435467 = 5153201) B5153201
theorem B2290311 : Blo 2289435 2290311 := bstep (se 1 (by rfl) ⟨1717733, by rfl⟩ : syracuseStep 2290311 = 3435467) B3435467
theorem B2576605 : Blo 2289435 2576605 := bbase (se 3 (by rfl) ⟨483113, by rfl⟩ : syracuseStep 2576605 = 966227) (by norm_num)
theorem B3435473 : Blo 2289435 3435473 := bstep (se 2 (by rfl) ⟨1288302, by rfl⟩ : syracuseStep 3435473 = 2576605) B2576605
theorem B2290315 : Blo 2289435 2290315 := bstep (se 1 (by rfl) ⟨1717736, by rfl⟩ : syracuseStep 2290315 = 3435473) B3435473
theorem B7729829 : Blo 2289435 7729829 := bbase (se 4 (by rfl) ⟨724671, by rfl⟩ : syracuseStep 7729829 = 1449343) (by norm_num)
theorem B5153219 : Blo 2289435 5153219 := bstep (se 1 (by rfl) ⟨3864914, by rfl⟩ : syracuseStep 5153219 = 7729829) B7729829
theorem B3435479 : Blo 2289435 3435479 := bstep (se 1 (by rfl) ⟨2576609, by rfl⟩ : syracuseStep 3435479 = 5153219) B5153219
theorem B2290319 : Blo 2289435 2290319 := bstep (se 1 (by rfl) ⟨1717739, by rfl⟩ : syracuseStep 2290319 = 3435479) B3435479
theorem B3435485 : Blo 2289435 3435485 := bbase (se 3 (by rfl) ⟨644153, by rfl⟩ : syracuseStep 3435485 = 1288307) (by norm_num)
theorem B2290323 : Blo 2289435 2290323 := bstep (se 1 (by rfl) ⟨1717742, by rfl⟩ : syracuseStep 2290323 = 3435485) B3435485
theorem B5153237 : Blo 2289435 5153237 := bbase (se 7 (by rfl) ⟨60389, by rfl⟩ : syracuseStep 5153237 = 120779) (by norm_num)
theorem B3435491 : Blo 2289435 3435491 := bstep (se 1 (by rfl) ⟨2576618, by rfl⟩ : syracuseStep 3435491 = 5153237) B5153237
theorem B2290327 : Blo 2289435 2290327 := bstep (se 1 (by rfl) ⟨1717745, by rfl⟩ : syracuseStep 2290327 = 3435491) B3435491
theorem B6964741 : Blo 2289435 6964741 := bbase (se 4 (by rfl) ⟨652944, by rfl⟩ : syracuseStep 6964741 = 1305889) (by norm_num)
theorem B9286321 : Blo 2289435 9286321 := bstep (se 2 (by rfl) ⟨3482370, by rfl⟩ : syracuseStep 9286321 = 6964741) B6964741
theorem B12381761 : Blo 2289435 12381761 := bstep (se 2 (by rfl) ⟨4643160, by rfl⟩ : syracuseStep 12381761 = 9286321) B9286321
theorem B33018029 : Blo 2289435 33018029 := bstep (se 3 (by rfl) ⟨6190880, by rfl⟩ : syracuseStep 33018029 = 12381761) B12381761
theorem B22012019 : Blo 2289435 22012019 := bstep (se 1 (by rfl) ⟨16509014, by rfl⟩ : syracuseStep 22012019 = 33018029) B33018029
theorem B14674679 : Blo 2289435 14674679 := bstep (se 1 (by rfl) ⟨11006009, by rfl⟩ : syracuseStep 14674679 = 22012019) B22012019
theorem B9783119 : Blo 2289435 9783119 := bstep (se 1 (by rfl) ⟨7337339, by rfl⟩ : syracuseStep 9783119 = 14674679) B14674679
theorem B6522079 : Blo 2289435 6522079 := bstep (se 1 (by rfl) ⟨4891559, by rfl⟩ : syracuseStep 6522079 = 9783119) B9783119
theorem B8696105 : Blo 2289435 8696105 := bstep (se 2 (by rfl) ⟨3261039, by rfl⟩ : syracuseStep 8696105 = 6522079) B6522079
theorem B5797403 : Blo 2289435 5797403 := bstep (se 1 (by rfl) ⟨4348052, by rfl⟩ : syracuseStep 5797403 = 8696105) B8696105
theorem B3864935 : Blo 2289435 3864935 := bstep (se 1 (by rfl) ⟨2898701, by rfl⟩ : syracuseStep 3864935 = 5797403) B5797403
theorem B2576623 : Blo 2289435 2576623 := bstep (se 1 (by rfl) ⟨1932467, by rfl⟩ : syracuseStep 2576623 = 3864935) B3864935
theorem B3435497 : Blo 2289435 3435497 := bstep (se 2 (by rfl) ⟨1288311, by rfl⟩ : syracuseStep 3435497 = 2576623) B2576623
theorem B2290331 : Blo 2289435 2290331 := bstep (se 1 (by rfl) ⟨1717748, by rfl⟩ : syracuseStep 2290331 = 3435497) B3435497
theorem B12381781 : Blo 2289435 12381781 := bbase (se 8 (by rfl) ⟨72549, by rfl⟩ : syracuseStep 12381781 = 145099) (by norm_num)
theorem B16509041 : Blo 2289435 16509041 := bstep (se 2 (by rfl) ⟨6190890, by rfl⟩ : syracuseStep 16509041 = 12381781) B12381781
theorem B11006027 : Blo 2289435 11006027 := bstep (se 1 (by rfl) ⟨8254520, by rfl⟩ : syracuseStep 11006027 = 16509041) B16509041
theorem B7337351 : Blo 2289435 7337351 := bstep (se 1 (by rfl) ⟨5503013, by rfl⟩ : syracuseStep 7337351 = 11006027) B11006027
theorem B19566269 : Blo 2289435 19566269 := bstep (se 3 (by rfl) ⟨3668675, by rfl⟩ : syracuseStep 19566269 = 7337351) B7337351
theorem B13044179 : Blo 2289435 13044179 := bstep (se 1 (by rfl) ⟨9783134, by rfl⟩ : syracuseStep 13044179 = 19566269) B19566269
theorem B8696119 : Blo 2289435 8696119 := bstep (se 1 (by rfl) ⟨6522089, by rfl⟩ : syracuseStep 8696119 = 13044179) B13044179
theorem B11594825 : Blo 2289435 11594825 := bstep (se 2 (by rfl) ⟨4348059, by rfl⟩ : syracuseStep 11594825 = 8696119) B8696119
theorem B7729883 : Blo 2289435 7729883 := bstep (se 1 (by rfl) ⟨5797412, by rfl⟩ : syracuseStep 7729883 = 11594825) B11594825
theorem B5153255 : Blo 2289435 5153255 := bstep (se 1 (by rfl) ⟨3864941, by rfl⟩ : syracuseStep 5153255 = 7729883) B7729883
theorem B3435503 : Blo 2289435 3435503 := bstep (se 1 (by rfl) ⟨2576627, by rfl⟩ : syracuseStep 3435503 = 5153255) B5153255
theorem B2290335 : Blo 2289435 2290335 := bstep (se 1 (by rfl) ⟨1717751, by rfl⟩ : syracuseStep 2290335 = 3435503) B3435503
theorem B3435509 : Blo 2289435 3435509 := bbase (se 5 (by rfl) ⟨161039, by rfl⟩ : syracuseStep 3435509 = 322079) (by norm_num)
theorem B2290339 : Blo 2289435 2290339 := bstep (se 1 (by rfl) ⟨1717754, by rfl⟩ : syracuseStep 2290339 = 3435509) B3435509
theorem B2751517 : Blo 2289435 2751517 := bbase (se 3 (by rfl) ⟨515909, by rfl⟩ : syracuseStep 2751517 = 1031819) (by norm_num)
theorem B3668689 : Blo 2289435 3668689 := bstep (se 2 (by rfl) ⟨1375758, by rfl⟩ : syracuseStep 3668689 = 2751517) B2751517
theorem B4891585 : Blo 2289435 4891585 := bstep (se 2 (by rfl) ⟨1834344, by rfl⟩ : syracuseStep 4891585 = 3668689) B3668689
theorem B6522113 : Blo 2289435 6522113 := bstep (se 2 (by rfl) ⟨2445792, by rfl⟩ : syracuseStep 6522113 = 4891585) B4891585
theorem B4348075 : Blo 2289435 4348075 := bstep (se 1 (by rfl) ⟨3261056, by rfl⟩ : syracuseStep 4348075 = 6522113) B6522113
theorem B5797433 : Blo 2289435 5797433 := bstep (se 2 (by rfl) ⟨2174037, by rfl⟩ : syracuseStep 5797433 = 4348075) B4348075
theorem B3864955 : Blo 2289435 3864955 := bstep (se 1 (by rfl) ⟨2898716, by rfl⟩ : syracuseStep 3864955 = 5797433) B5797433
theorem B5153273 : Blo 2289435 5153273 := bstep (se 2 (by rfl) ⟨1932477, by rfl⟩ : syracuseStep 5153273 = 3864955) B3864955
theorem B3435515 : Blo 2289435 3435515 := bstep (se 1 (by rfl) ⟨2576636, by rfl⟩ : syracuseStep 3435515 = 5153273) B5153273
theorem B2290343 : Blo 2289435 2290343 := bstep (se 1 (by rfl) ⟨1717757, by rfl⟩ : syracuseStep 2290343 = 3435515) B3435515
theorem B2576641 : Blo 2289435 2576641 := bbase (se 2 (by rfl) ⟨966240, by rfl⟩ : syracuseStep 2576641 = 1932481) (by norm_num)
theorem B3435521 : Blo 2289435 3435521 := bstep (se 2 (by rfl) ⟨1288320, by rfl⟩ : syracuseStep 3435521 = 2576641) B2576641
theorem B2290347 : Blo 2289435 2290347 := bstep (se 1 (by rfl) ⟨1717760, by rfl⟩ : syracuseStep 2290347 = 3435521) B3435521
theorem B5797453 : Blo 2289435 5797453 := bbase (se 3 (by rfl) ⟨1087022, by rfl⟩ : syracuseStep 5797453 = 2174045) (by norm_num)
theorem B7729937 : Blo 2289435 7729937 := bstep (se 2 (by rfl) ⟨2898726, by rfl⟩ : syracuseStep 7729937 = 5797453) B5797453
theorem B5153291 : Blo 2289435 5153291 := bstep (se 1 (by rfl) ⟨3864968, by rfl⟩ : syracuseStep 5153291 = 7729937) B7729937
theorem B3435527 : Blo 2289435 3435527 := bstep (se 1 (by rfl) ⟨2576645, by rfl⟩ : syracuseStep 3435527 = 5153291) B5153291
theorem B2290351 : Blo 2289435 2290351 := bstep (se 1 (by rfl) ⟨1717763, by rfl⟩ : syracuseStep 2290351 = 3435527) B3435527
theorem B3435533 : Blo 2289435 3435533 := bbase (se 3 (by rfl) ⟨644162, by rfl⟩ : syracuseStep 3435533 = 1288325) (by norm_num)
theorem B2290355 : Blo 2289435 2290355 := bstep (se 1 (by rfl) ⟨1717766, by rfl⟩ : syracuseStep 2290355 = 3435533) B3435533
theorem B5153309 : Blo 2289435 5153309 := bbase (se 3 (by rfl) ⟨966245, by rfl⟩ : syracuseStep 5153309 = 1932491) (by norm_num)
theorem B3435539 : Blo 2289435 3435539 := bstep (se 1 (by rfl) ⟨2576654, by rfl⟩ : syracuseStep 3435539 = 5153309) B5153309
theorem B2290359 : Blo 2289435 2290359 := bstep (se 1 (by rfl) ⟨1717769, by rfl⟩ : syracuseStep 2290359 = 3435539) B3435539
theorem B3864989 : Blo 2289435 3864989 := bbase (se 3 (by rfl) ⟨724685, by rfl⟩ : syracuseStep 3864989 = 1449371) (by norm_num)
theorem B2576659 : Blo 2289435 2576659 := bstep (se 1 (by rfl) ⟨1932494, by rfl⟩ : syracuseStep 2576659 = 3864989) B3864989
theorem B3435545 : Blo 2289435 3435545 := bstep (se 2 (by rfl) ⟨1288329, by rfl⟩ : syracuseStep 3435545 = 2576659) B2576659
theorem B2290363 : Blo 2289435 2290363 := bstep (se 1 (by rfl) ⟨1717772, by rfl⟩ : syracuseStep 2290363 = 3435545) B3435545
theorem B5223637 : Blo 2289435 5223637 := bbase (se 7 (by rfl) ⟨61214, by rfl⟩ : syracuseStep 5223637 = 122429) (by norm_num)
theorem B6964849 : Blo 2289435 6964849 := bstep (se 2 (by rfl) ⟨2611818, by rfl⟩ : syracuseStep 6964849 = 5223637) B5223637
theorem B37145861 : Blo 2289435 37145861 := bstep (se 4 (by rfl) ⟨3482424, by rfl⟩ : syracuseStep 37145861 = 6964849) B6964849
theorem B24763907 : Blo 2289435 24763907 := bstep (se 1 (by rfl) ⟨18572930, by rfl⟩ : syracuseStep 24763907 = 37145861) B37145861
theorem B16509271 : Blo 2289435 16509271 := bstep (se 1 (by rfl) ⟨12381953, by rfl⟩ : syracuseStep 16509271 = 24763907) B24763907
theorem B22012361 : Blo 2289435 22012361 := bstep (se 2 (by rfl) ⟨8254635, by rfl⟩ : syracuseStep 22012361 = 16509271) B16509271
theorem B14674907 : Blo 2289435 14674907 := bstep (se 1 (by rfl) ⟨11006180, by rfl⟩ : syracuseStep 14674907 = 22012361) B22012361
theorem B9783271 : Blo 2289435 9783271 := bstep (se 1 (by rfl) ⟨7337453, by rfl⟩ : syracuseStep 9783271 = 14674907) B14674907
theorem B13044361 : Blo 2289435 13044361 := bstep (se 2 (by rfl) ⟨4891635, by rfl⟩ : syracuseStep 13044361 = 9783271) B9783271
theorem B17392481 : Blo 2289435 17392481 := bstep (se 2 (by rfl) ⟨6522180, by rfl⟩ : syracuseStep 17392481 = 13044361) B13044361
theorem B11594987 : Blo 2289435 11594987 := bstep (se 1 (by rfl) ⟨8696240, by rfl⟩ : syracuseStep 11594987 = 17392481) B17392481
theorem B7729991 : Blo 2289435 7729991 := bstep (se 1 (by rfl) ⟨5797493, by rfl⟩ : syracuseStep 7729991 = 11594987) B11594987
theorem B5153327 : Blo 2289435 5153327 := bstep (se 1 (by rfl) ⟨3864995, by rfl⟩ : syracuseStep 5153327 = 7729991) B7729991
theorem B3435551 : Blo 2289435 3435551 := bstep (se 1 (by rfl) ⟨2576663, by rfl⟩ : syracuseStep 3435551 = 5153327) B5153327
theorem B2290367 : Blo 2289435 2290367 := bstep (se 1 (by rfl) ⟨1717775, by rfl⟩ : syracuseStep 2290367 = 3435551) B3435551
theorem B3435557 : Blo 2289435 3435557 := bbase (se 4 (by rfl) ⟨322083, by rfl⟩ : syracuseStep 3435557 = 644167) (by norm_num)
theorem B2290371 : Blo 2289435 2290371 := bstep (se 1 (by rfl) ⟨1717778, by rfl⟩ : syracuseStep 2290371 = 3435557) B3435557
theorem B2898757 : Blo 2289435 2898757 := bbase (se 4 (by rfl) ⟨271758, by rfl⟩ : syracuseStep 2898757 = 543517) (by norm_num)
theorem B3865009 : Blo 2289435 3865009 := bstep (se 2 (by rfl) ⟨1449378, by rfl⟩ : syracuseStep 3865009 = 2898757) B2898757
theorem B5153345 : Blo 2289435 5153345 := bstep (se 2 (by rfl) ⟨1932504, by rfl⟩ : syracuseStep 5153345 = 3865009) B3865009
theorem B3435563 : Blo 2289435 3435563 := bstep (se 1 (by rfl) ⟨2576672, by rfl⟩ : syracuseStep 3435563 = 5153345) B5153345
theorem B2290375 : Blo 2289435 2290375 := bstep (se 1 (by rfl) ⟨1717781, by rfl⟩ : syracuseStep 2290375 = 3435563) B3435563
theorem B2576677 : Blo 2289435 2576677 := bbase (se 4 (by rfl) ⟨241563, by rfl⟩ : syracuseStep 2576677 = 483127) (by norm_num)
theorem B3435569 : Blo 2289435 3435569 := bstep (se 2 (by rfl) ⟨1288338, by rfl⟩ : syracuseStep 3435569 = 2576677) B2576677
theorem B2290379 : Blo 2289435 2290379 := bstep (se 1 (by rfl) ⟨1717784, by rfl⟩ : syracuseStep 2290379 = 3435569) B3435569
theorem B2751565 : Blo 2289435 2751565 := bbase (se 3 (by rfl) ⟨515918, by rfl⟩ : syracuseStep 2751565 = 1031837) (by norm_num)
theorem B3668753 : Blo 2289435 3668753 := bstep (se 2 (by rfl) ⟨1375782, by rfl⟩ : syracuseStep 3668753 = 2751565) B2751565
theorem B9783341 : Blo 2289435 9783341 := bstep (se 3 (by rfl) ⟨1834376, by rfl⟩ : syracuseStep 9783341 = 3668753) B3668753
theorem B6522227 : Blo 2289435 6522227 := bstep (se 1 (by rfl) ⟨4891670, by rfl⟩ : syracuseStep 6522227 = 9783341) B9783341
theorem B4348151 : Blo 2289435 4348151 := bstep (se 1 (by rfl) ⟨3261113, by rfl⟩ : syracuseStep 4348151 = 6522227) B6522227
theorem B2898767 : Blo 2289435 2898767 := bstep (se 1 (by rfl) ⟨2174075, by rfl⟩ : syracuseStep 2898767 = 4348151) B4348151
theorem B7730045 : Blo 2289435 7730045 := bstep (se 3 (by rfl) ⟨1449383, by rfl⟩ : syracuseStep 7730045 = 2898767) B2898767
theorem B5153363 : Blo 2289435 5153363 := bstep (se 1 (by rfl) ⟨3865022, by rfl⟩ : syracuseStep 5153363 = 7730045) B7730045
theorem B3435575 : Blo 2289435 3435575 := bstep (se 1 (by rfl) ⟨2576681, by rfl⟩ : syracuseStep 3435575 = 5153363) B5153363
theorem B2290383 : Blo 2289435 2290383 := bstep (se 1 (by rfl) ⟨1717787, by rfl⟩ : syracuseStep 2290383 = 3435575) B3435575
theorem B3435581 : Blo 2289435 3435581 := bbase (se 3 (by rfl) ⟨644171, by rfl⟩ : syracuseStep 3435581 = 1288343) (by norm_num)
theorem B2290387 : Blo 2289435 2290387 := bstep (se 1 (by rfl) ⟨1717790, by rfl⟩ : syracuseStep 2290387 = 3435581) B3435581
theorem B5153381 : Blo 2289435 5153381 := bbase (se 4 (by rfl) ⟨483129, by rfl⟩ : syracuseStep 5153381 = 966259) (by norm_num)
theorem B3435587 : Blo 2289435 3435587 := bstep (se 1 (by rfl) ⟨2576690, by rfl⟩ : syracuseStep 3435587 = 5153381) B5153381
theorem B2290391 : Blo 2289435 2290391 := bstep (se 1 (by rfl) ⟨1717793, by rfl⟩ : syracuseStep 2290391 = 3435587) B3435587
theorem B5797565 : Blo 2289435 5797565 := bbase (se 3 (by rfl) ⟨1087043, by rfl⟩ : syracuseStep 5797565 = 2174087) (by norm_num)
theorem B3865043 : Blo 2289435 3865043 := bstep (se 1 (by rfl) ⟨2898782, by rfl⟩ : syracuseStep 3865043 = 5797565) B5797565
theorem B2576695 : Blo 2289435 2576695 := bstep (se 1 (by rfl) ⟨1932521, by rfl⟩ : syracuseStep 2576695 = 3865043) B3865043
theorem B3435593 : Blo 2289435 3435593 := bstep (se 2 (by rfl) ⟨1288347, by rfl⟩ : syracuseStep 3435593 = 2576695) B2576695
theorem B2290395 : Blo 2289435 2290395 := bstep (se 1 (by rfl) ⟨1717796, by rfl⟩ : syracuseStep 2290395 = 3435593) B3435593
theorem B4348181 : Blo 2289435 4348181 := bbase (se 6 (by rfl) ⟨101910, by rfl⟩ : syracuseStep 4348181 = 203821) (by norm_num)
theorem B11595149 : Blo 2289435 11595149 := bstep (se 3 (by rfl) ⟨2174090, by rfl⟩ : syracuseStep 11595149 = 4348181) B4348181
theorem B7730099 : Blo 2289435 7730099 := bstep (se 1 (by rfl) ⟨5797574, by rfl⟩ : syracuseStep 7730099 = 11595149) B11595149
theorem B5153399 : Blo 2289435 5153399 := bstep (se 1 (by rfl) ⟨3865049, by rfl⟩ : syracuseStep 5153399 = 7730099) B7730099
theorem B3435599 : Blo 2289435 3435599 := bstep (se 1 (by rfl) ⟨2576699, by rfl⟩ : syracuseStep 3435599 = 5153399) B5153399
theorem B2290399 : Blo 2289435 2290399 := bstep (se 1 (by rfl) ⟨1717799, by rfl⟩ : syracuseStep 2290399 = 3435599) B3435599
theorem B3435605 : Blo 2289435 3435605 := bbase (se 8 (by rfl) ⟨20130, by rfl⟩ : syracuseStep 3435605 = 40261) (by norm_num)
theorem B2290403 : Blo 2289435 2290403 := bstep (se 1 (by rfl) ⟨1717802, by rfl⟩ : syracuseStep 2290403 = 3435605) B3435605
theorem B2611865 : Blo 2289435 2611865 := bbase (se 2 (by rfl) ⟨979449, by rfl⟩ : syracuseStep 2611865 = 1958899) (by norm_num)
theorem B6964973 : Blo 2289435 6964973 := bstep (se 3 (by rfl) ⟨1305932, by rfl⟩ : syracuseStep 6964973 = 2611865) B2611865
theorem B4643315 : Blo 2289435 4643315 := bstep (se 1 (by rfl) ⟨3482486, by rfl⟩ : syracuseStep 4643315 = 6964973) B6964973
theorem B3095543 : Blo 2289435 3095543 := bstep (se 1 (by rfl) ⟨2321657, by rfl⟩ : syracuseStep 3095543 = 4643315) B4643315
theorem B8254781 : Blo 2289435 8254781 := bstep (se 3 (by rfl) ⟨1547771, by rfl⟩ : syracuseStep 8254781 = 3095543) B3095543
theorem B5503187 : Blo 2289435 5503187 := bstep (se 1 (by rfl) ⟨4127390, by rfl⟩ : syracuseStep 5503187 = 8254781) B8254781
theorem B14675165 : Blo 2289435 14675165 := bstep (se 3 (by rfl) ⟨2751593, by rfl⟩ : syracuseStep 14675165 = 5503187) B5503187
theorem B9783443 : Blo 2289435 9783443 := bstep (se 1 (by rfl) ⟨7337582, by rfl⟩ : syracuseStep 9783443 = 14675165) B14675165
theorem B6522295 : Blo 2289435 6522295 := bstep (se 1 (by rfl) ⟨4891721, by rfl⟩ : syracuseStep 6522295 = 9783443) B9783443
theorem B8696393 : Blo 2289435 8696393 := bstep (se 2 (by rfl) ⟨3261147, by rfl⟩ : syracuseStep 8696393 = 6522295) B6522295
theorem B5797595 : Blo 2289435 5797595 := bstep (se 1 (by rfl) ⟨4348196, by rfl⟩ : syracuseStep 5797595 = 8696393) B8696393
theorem B3865063 : Blo 2289435 3865063 := bstep (se 1 (by rfl) ⟨2898797, by rfl⟩ : syracuseStep 3865063 = 5797595) B5797595
theorem B5153417 : Blo 2289435 5153417 := bstep (se 2 (by rfl) ⟨1932531, by rfl⟩ : syracuseStep 5153417 = 3865063) B3865063
theorem B3435611 : Blo 2289435 3435611 := bstep (se 1 (by rfl) ⟨2576708, by rfl⟩ : syracuseStep 3435611 = 5153417) B5153417
theorem B2290407 : Blo 2289435 2290407 := bstep (se 1 (by rfl) ⟨1717805, by rfl⟩ : syracuseStep 2290407 = 3435611) B3435611
theorem B2576713 : Blo 2289435 2576713 := bbase (se 2 (by rfl) ⟨966267, by rfl⟩ : syracuseStep 2576713 = 1932535) (by norm_num)
theorem B3435617 : Blo 2289435 3435617 := bstep (se 2 (by rfl) ⟨1288356, by rfl⟩ : syracuseStep 3435617 = 2576713) B2576713
theorem B2290411 : Blo 2289435 2290411 := bstep (se 1 (by rfl) ⟨1717808, by rfl⟩ : syracuseStep 2290411 = 3435617) B3435617
theorem B2321665 : Blo 2289435 2321665 := bbase (se 2 (by rfl) ⟨870624, by rfl⟩ : syracuseStep 2321665 = 1741249) (by norm_num)
theorem B49528853 : Blo 2289435 49528853 := bstep (se 6 (by rfl) ⟨1160832, by rfl⟩ : syracuseStep 49528853 = 2321665) B2321665
theorem B33019235 : Blo 2289435 33019235 := bstep (se 1 (by rfl) ⟨24764426, by rfl⟩ : syracuseStep 33019235 = 49528853) B49528853
theorem B22012823 : Blo 2289435 22012823 := bstep (se 1 (by rfl) ⟨16509617, by rfl⟩ : syracuseStep 22012823 = 33019235) B33019235
theorem B14675215 : Blo 2289435 14675215 := bstep (se 1 (by rfl) ⟨11006411, by rfl⟩ : syracuseStep 14675215 = 22012823) B22012823
theorem B19566953 : Blo 2289435 19566953 := bstep (se 2 (by rfl) ⟨7337607, by rfl⟩ : syracuseStep 19566953 = 14675215) B14675215
theorem B13044635 : Blo 2289435 13044635 := bstep (se 1 (by rfl) ⟨9783476, by rfl⟩ : syracuseStep 13044635 = 19566953) B19566953
theorem B8696423 : Blo 2289435 8696423 := bstep (se 1 (by rfl) ⟨6522317, by rfl⟩ : syracuseStep 8696423 = 13044635) B13044635
theorem B5797615 : Blo 2289435 5797615 := bstep (se 1 (by rfl) ⟨4348211, by rfl⟩ : syracuseStep 5797615 = 8696423) B8696423
theorem B7730153 : Blo 2289435 7730153 := bstep (se 2 (by rfl) ⟨2898807, by rfl⟩ : syracuseStep 7730153 = 5797615) B5797615
theorem B5153435 : Blo 2289435 5153435 := bstep (se 1 (by rfl) ⟨3865076, by rfl⟩ : syracuseStep 5153435 = 7730153) B7730153
theorem B3435623 : Blo 2289435 3435623 := bstep (se 1 (by rfl) ⟨2576717, by rfl⟩ : syracuseStep 3435623 = 5153435) B5153435
theorem B2290415 : Blo 2289435 2290415 := bstep (se 1 (by rfl) ⟨1717811, by rfl⟩ : syracuseStep 2290415 = 3435623) B3435623
theorem B3435629 : Blo 2289435 3435629 := bbase (se 3 (by rfl) ⟨644180, by rfl⟩ : syracuseStep 3435629 = 1288361) (by norm_num)
theorem B2290419 : Blo 2289435 2290419 := bstep (se 1 (by rfl) ⟨1717814, by rfl⟩ : syracuseStep 2290419 = 3435629) B3435629
theorem B5153453 : Blo 2289435 5153453 := bbase (se 3 (by rfl) ⟨966272, by rfl⟩ : syracuseStep 5153453 = 1932545) (by norm_num)
theorem B3435635 : Blo 2289435 3435635 := bstep (se 1 (by rfl) ⟨2576726, by rfl⟩ : syracuseStep 3435635 = 5153453) B5153453
theorem B2290423 : Blo 2289435 2290423 := bstep (se 1 (by rfl) ⟨1717817, by rfl⟩ : syracuseStep 2290423 = 3435635) B3435635
theorem B4891765 : Blo 2289435 4891765 := bbase (se 5 (by rfl) ⟨229301, by rfl⟩ : syracuseStep 4891765 = 458603) (by norm_num)
theorem B6522353 : Blo 2289435 6522353 := bstep (se 2 (by rfl) ⟨2445882, by rfl⟩ : syracuseStep 6522353 = 4891765) B4891765
theorem B4348235 : Blo 2289435 4348235 := bstep (se 1 (by rfl) ⟨3261176, by rfl⟩ : syracuseStep 4348235 = 6522353) B6522353
theorem B2898823 : Blo 2289435 2898823 := bstep (se 1 (by rfl) ⟨2174117, by rfl⟩ : syracuseStep 2898823 = 4348235) B4348235
theorem B3865097 : Blo 2289435 3865097 := bstep (se 2 (by rfl) ⟨1449411, by rfl⟩ : syracuseStep 3865097 = 2898823) B2898823
theorem B2576731 : Blo 2289435 2576731 := bstep (se 1 (by rfl) ⟨1932548, by rfl⟩ : syracuseStep 2576731 = 3865097) B3865097
theorem B3435641 : Blo 2289435 3435641 := bstep (se 2 (by rfl) ⟨1288365, by rfl⟩ : syracuseStep 3435641 = 2576731) B2576731
theorem B2290427 : Blo 2289435 2290427 := bstep (se 1 (by rfl) ⟨1717820, by rfl⟩ : syracuseStep 2290427 = 3435641) B3435641
theorem B3718885 : Blo 2289435 3718885 := bbase (se 4 (by rfl) ⟨348645, by rfl⟩ : syracuseStep 3718885 = 697291) (by norm_num)
theorem B4958513 : Blo 2289435 4958513 := bstep (se 2 (by rfl) ⟨1859442, by rfl⟩ : syracuseStep 4958513 = 3718885) B3718885
theorem B3305675 : Blo 2289435 3305675 := bstep (se 1 (by rfl) ⟨2479256, by rfl⟩ : syracuseStep 3305675 = 4958513) B4958513
theorem B8815133 : Blo 2289435 8815133 := bstep (se 3 (by rfl) ⟨1652837, by rfl⟩ : syracuseStep 8815133 = 3305675) B3305675
theorem B23507021 : Blo 2289435 23507021 := bstep (se 3 (by rfl) ⟨4407566, by rfl⟩ : syracuseStep 23507021 = 8815133) B8815133
theorem B62685389 : Blo 2289435 62685389 := bstep (se 3 (by rfl) ⟨11753510, by rfl⟩ : syracuseStep 62685389 = 23507021) B23507021
theorem B41790259 : Blo 2289435 41790259 := bstep (se 1 (by rfl) ⟨31342694, by rfl⟩ : syracuseStep 41790259 = 62685389) B62685389
theorem B55720345 : Blo 2289435 55720345 := bstep (se 2 (by rfl) ⟨20895129, by rfl⟩ : syracuseStep 55720345 = 41790259) B41790259
theorem B74293793 : Blo 2289435 74293793 := bstep (se 2 (by rfl) ⟨27860172, by rfl⟩ : syracuseStep 74293793 = 55720345) B55720345
theorem B49529195 : Blo 2289435 49529195 := bstep (se 1 (by rfl) ⟨37146896, by rfl⟩ : syracuseStep 49529195 = 74293793) B74293793
theorem B33019463 : Blo 2289435 33019463 := bstep (se 1 (by rfl) ⟨24764597, by rfl⟩ : syracuseStep 33019463 = 49529195) B49529195
theorem B22012975 : Blo 2289435 22012975 := bstep (se 1 (by rfl) ⟨16509731, by rfl⟩ : syracuseStep 22012975 = 33019463) B33019463
theorem B29350633 : Blo 2289435 29350633 := bstep (se 2 (by rfl) ⟨11006487, by rfl⟩ : syracuseStep 29350633 = 22012975) B22012975
theorem B39134177 : Blo 2289435 39134177 := bstep (se 2 (by rfl) ⟨14675316, by rfl⟩ : syracuseStep 39134177 = 29350633) B29350633
theorem B26089451 : Blo 2289435 26089451 := bstep (se 1 (by rfl) ⟨19567088, by rfl⟩ : syracuseStep 26089451 = 39134177) B39134177
theorem B17392967 : Blo 2289435 17392967 := bstep (se 1 (by rfl) ⟨13044725, by rfl⟩ : syracuseStep 17392967 = 26089451) B26089451
theorem B11595311 : Blo 2289435 11595311 := bstep (se 1 (by rfl) ⟨8696483, by rfl⟩ : syracuseStep 11595311 = 17392967) B17392967
theorem B7730207 : Blo 2289435 7730207 := bstep (se 1 (by rfl) ⟨5797655, by rfl⟩ : syracuseStep 7730207 = 11595311) B11595311
theorem B5153471 : Blo 2289435 5153471 := bstep (se 1 (by rfl) ⟨3865103, by rfl⟩ : syracuseStep 5153471 = 7730207) B7730207
theorem B3435647 : Blo 2289435 3435647 := bstep (se 1 (by rfl) ⟨2576735, by rfl⟩ : syracuseStep 3435647 = 5153471) B5153471
theorem B2290431 : Blo 2289435 2290431 := bstep (se 1 (by rfl) ⟨1717823, by rfl⟩ : syracuseStep 2290431 = 3435647) B3435647
theorem B3435653 : Blo 2289435 3435653 := bbase (se 4 (by rfl) ⟨322092, by rfl⟩ : syracuseStep 3435653 = 644185) (by norm_num)
theorem B2290435 : Blo 2289435 2290435 := bstep (se 1 (by rfl) ⟨1717826, by rfl⟩ : syracuseStep 2290435 = 3435653) B3435653
theorem B3865117 : Blo 2289435 3865117 := bbase (se 3 (by rfl) ⟨724709, by rfl⟩ : syracuseStep 3865117 = 1449419) (by norm_num)
theorem B5153489 : Blo 2289435 5153489 := bstep (se 2 (by rfl) ⟨1932558, by rfl⟩ : syracuseStep 5153489 = 3865117) B3865117
theorem B3435659 : Blo 2289435 3435659 := bstep (se 1 (by rfl) ⟨2576744, by rfl⟩ : syracuseStep 3435659 = 5153489) B5153489
theorem B2290439 : Blo 2289435 2290439 := bstep (se 1 (by rfl) ⟨1717829, by rfl⟩ : syracuseStep 2290439 = 3435659) B3435659
theorem B2576749 : Blo 2289435 2576749 := bbase (se 3 (by rfl) ⟨483140, by rfl⟩ : syracuseStep 2576749 = 966281) (by norm_num)
theorem B3435665 : Blo 2289435 3435665 := bstep (se 2 (by rfl) ⟨1288374, by rfl⟩ : syracuseStep 3435665 = 2576749) B2576749
theorem B2290443 : Blo 2289435 2290443 := bstep (se 1 (by rfl) ⟨1717832, by rfl⟩ : syracuseStep 2290443 = 3435665) B3435665
theorem B7730261 : Blo 2289435 7730261 := bbase (se 8 (by rfl) ⟨45294, by rfl⟩ : syracuseStep 7730261 = 90589) (by norm_num)
theorem B5153507 : Blo 2289435 5153507 := bstep (se 1 (by rfl) ⟨3865130, by rfl⟩ : syracuseStep 5153507 = 7730261) B7730261
theorem B3435671 : Blo 2289435 3435671 := bstep (se 1 (by rfl) ⟨2576753, by rfl⟩ : syracuseStep 3435671 = 5153507) B5153507
theorem B2290447 : Blo 2289435 2290447 := bstep (se 1 (by rfl) ⟨1717835, by rfl⟩ : syracuseStep 2290447 = 3435671) B3435671
theorem B3435677 : Blo 2289435 3435677 := bbase (se 3 (by rfl) ⟨644189, by rfl⟩ : syracuseStep 3435677 = 1288379) (by norm_num)
theorem B2290451 : Blo 2289435 2290451 := bstep (se 1 (by rfl) ⟨1717838, by rfl⟩ : syracuseStep 2290451 = 3435677) B3435677
theorem B5153525 : Blo 2289435 5153525 := bbase (se 5 (by rfl) ⟨241571, by rfl⟩ : syracuseStep 5153525 = 483143) (by norm_num)
theorem B3435683 : Blo 2289435 3435683 := bstep (se 1 (by rfl) ⟨2576762, by rfl⟩ : syracuseStep 3435683 = 5153525) B5153525
theorem B2290455 : Blo 2289435 2290455 := bstep (se 1 (by rfl) ⟨1717841, by rfl⟩ : syracuseStep 2290455 = 3435683) B3435683
theorem B29350997 : Blo 2289435 29350997 := bbase (se 8 (by rfl) ⟨171978, by rfl⟩ : syracuseStep 29350997 = 343957) (by norm_num)
theorem B19567331 : Blo 2289435 19567331 := bstep (se 1 (by rfl) ⟨14675498, by rfl⟩ : syracuseStep 19567331 = 29350997) B29350997
theorem B13044887 : Blo 2289435 13044887 := bstep (se 1 (by rfl) ⟨9783665, by rfl⟩ : syracuseStep 13044887 = 19567331) B19567331
theorem B8696591 : Blo 2289435 8696591 := bstep (se 1 (by rfl) ⟨6522443, by rfl⟩ : syracuseStep 8696591 = 13044887) B13044887
theorem B5797727 : Blo 2289435 5797727 := bstep (se 1 (by rfl) ⟨4348295, by rfl⟩ : syracuseStep 5797727 = 8696591) B8696591
theorem B3865151 : Blo 2289435 3865151 := bstep (se 1 (by rfl) ⟨2898863, by rfl⟩ : syracuseStep 3865151 = 5797727) B5797727
theorem B2576767 : Blo 2289435 2576767 := bstep (se 1 (by rfl) ⟨1932575, by rfl⟩ : syracuseStep 2576767 = 3865151) B3865151
theorem B3435689 : Blo 2289435 3435689 := bstep (se 2 (by rfl) ⟨1288383, by rfl⟩ : syracuseStep 3435689 = 2576767) B2576767
theorem B2290459 : Blo 2289435 2290459 := bstep (se 1 (by rfl) ⟨1717844, by rfl⟩ : syracuseStep 2290459 = 3435689) B3435689
theorem B2751661 : Blo 2289435 2751661 := bbase (se 3 (by rfl) ⟨515936, by rfl⟩ : syracuseStep 2751661 = 1031873) (by norm_num)
theorem B3668881 : Blo 2289435 3668881 := bstep (se 2 (by rfl) ⟨1375830, by rfl⟩ : syracuseStep 3668881 = 2751661) B2751661
theorem B4891841 : Blo 2289435 4891841 := bstep (se 2 (by rfl) ⟨1834440, by rfl⟩ : syracuseStep 4891841 = 3668881) B3668881
theorem B3261227 : Blo 2289435 3261227 := bstep (se 1 (by rfl) ⟨2445920, by rfl⟩ : syracuseStep 3261227 = 4891841) B4891841
theorem B8696605 : Blo 2289435 8696605 := bstep (se 3 (by rfl) ⟨1630613, by rfl⟩ : syracuseStep 8696605 = 3261227) B3261227
theorem B11595473 : Blo 2289435 11595473 := bstep (se 2 (by rfl) ⟨4348302, by rfl⟩ : syracuseStep 11595473 = 8696605) B8696605
theorem B7730315 : Blo 2289435 7730315 := bstep (se 1 (by rfl) ⟨5797736, by rfl⟩ : syracuseStep 7730315 = 11595473) B11595473
theorem B5153543 : Blo 2289435 5153543 := bstep (se 1 (by rfl) ⟨3865157, by rfl⟩ : syracuseStep 5153543 = 7730315) B7730315
theorem B3435695 : Blo 2289435 3435695 := bstep (se 1 (by rfl) ⟨2576771, by rfl⟩ : syracuseStep 3435695 = 5153543) B5153543
theorem B2290463 : Blo 2289435 2290463 := bstep (se 1 (by rfl) ⟨1717847, by rfl⟩ : syracuseStep 2290463 = 3435695) B3435695
theorem B3435701 : Blo 2289435 3435701 := bbase (se 5 (by rfl) ⟨161048, by rfl⟩ : syracuseStep 3435701 = 322097) (by norm_num)
theorem B2290467 : Blo 2289435 2290467 := bstep (se 1 (by rfl) ⟨1717850, by rfl⟩ : syracuseStep 2290467 = 3435701) B3435701
theorem B5797757 : Blo 2289435 5797757 := bbase (se 3 (by rfl) ⟨1087079, by rfl⟩ : syracuseStep 5797757 = 2174159) (by norm_num)
theorem B3865171 : Blo 2289435 3865171 := bstep (se 1 (by rfl) ⟨2898878, by rfl⟩ : syracuseStep 3865171 = 5797757) B5797757
theorem B5153561 : Blo 2289435 5153561 := bstep (se 2 (by rfl) ⟨1932585, by rfl⟩ : syracuseStep 5153561 = 3865171) B3865171
theorem B3435707 : Blo 2289435 3435707 := bstep (se 1 (by rfl) ⟨2576780, by rfl⟩ : syracuseStep 3435707 = 5153561) B5153561
theorem B2290471 : Blo 2289435 2290471 := bstep (se 1 (by rfl) ⟨1717853, by rfl⟩ : syracuseStep 2290471 = 3435707) B3435707
theorem B2576785 : Blo 2289435 2576785 := bbase (se 2 (by rfl) ⟨966294, by rfl⟩ : syracuseStep 2576785 = 1932589) (by norm_num)
theorem B3435713 : Blo 2289435 3435713 := bstep (se 2 (by rfl) ⟨1288392, by rfl⟩ : syracuseStep 3435713 = 2576785) B2576785
theorem B2290475 : Blo 2289435 2290475 := bstep (se 1 (by rfl) ⟨1717856, by rfl⟩ : syracuseStep 2290475 = 3435713) B3435713
theorem B4348333 : Blo 2289435 4348333 := bbase (se 3 (by rfl) ⟨815312, by rfl⟩ : syracuseStep 4348333 = 1630625) (by norm_num)
theorem B5797777 : Blo 2289435 5797777 := bstep (se 2 (by rfl) ⟨2174166, by rfl⟩ : syracuseStep 5797777 = 4348333) B4348333
theorem B7730369 : Blo 2289435 7730369 := bstep (se 2 (by rfl) ⟨2898888, by rfl⟩ : syracuseStep 7730369 = 5797777) B5797777
theorem B5153579 : Blo 2289435 5153579 := bstep (se 1 (by rfl) ⟨3865184, by rfl⟩ : syracuseStep 5153579 = 7730369) B7730369
theorem B3435719 : Blo 2289435 3435719 := bstep (se 1 (by rfl) ⟨2576789, by rfl⟩ : syracuseStep 3435719 = 5153579) B5153579
theorem B2290479 : Blo 2289435 2290479 := bstep (se 1 (by rfl) ⟨1717859, by rfl⟩ : syracuseStep 2290479 = 3435719) B3435719
theorem B3435725 : Blo 2289435 3435725 := bbase (se 3 (by rfl) ⟨644198, by rfl⟩ : syracuseStep 3435725 = 1288397) (by norm_num)
theorem B2290483 : Blo 2289435 2290483 := bstep (se 1 (by rfl) ⟨1717862, by rfl⟩ : syracuseStep 2290483 = 3435725) B3435725
theorem B5153597 : Blo 2289435 5153597 := bbase (se 3 (by rfl) ⟨966299, by rfl⟩ : syracuseStep 5153597 = 1932599) (by norm_num)
theorem B3435731 : Blo 2289435 3435731 := bstep (se 1 (by rfl) ⟨2576798, by rfl⟩ : syracuseStep 3435731 = 5153597) B5153597
theorem B2290487 : Blo 2289435 2290487 := bstep (se 1 (by rfl) ⟨1717865, by rfl⟩ : syracuseStep 2290487 = 3435731) B3435731
theorem B3865205 : Blo 2289435 3865205 := bbase (se 5 (by rfl) ⟨181181, by rfl⟩ : syracuseStep 3865205 = 362363) (by norm_num)
theorem B2576803 : Blo 2289435 2576803 := bstep (se 1 (by rfl) ⟨1932602, by rfl⟩ : syracuseStep 2576803 = 3865205) B3865205
theorem B3435737 : Blo 2289435 3435737 := bstep (se 2 (by rfl) ⟨1288401, by rfl⟩ : syracuseStep 3435737 = 2576803) B2576803
theorem B2290491 : Blo 2289435 2290491 := bstep (se 1 (by rfl) ⟨1717868, by rfl⟩ : syracuseStep 2290491 = 3435737) B3435737
theorem B4891909 : Blo 2289435 4891909 := bbase (se 4 (by rfl) ⟨458616, by rfl⟩ : syracuseStep 4891909 = 917233) (by norm_num)
theorem B6522545 : Blo 2289435 6522545 := bstep (se 2 (by rfl) ⟨2445954, by rfl⟩ : syracuseStep 6522545 = 4891909) B4891909
theorem B17393453 : Blo 2289435 17393453 := bstep (se 3 (by rfl) ⟨3261272, by rfl⟩ : syracuseStep 17393453 = 6522545) B6522545
theorem B11595635 : Blo 2289435 11595635 := bstep (se 1 (by rfl) ⟨8696726, by rfl⟩ : syracuseStep 11595635 = 17393453) B17393453
theorem B7730423 : Blo 2289435 7730423 := bstep (se 1 (by rfl) ⟨5797817, by rfl⟩ : syracuseStep 7730423 = 11595635) B11595635
theorem B5153615 : Blo 2289435 5153615 := bstep (se 1 (by rfl) ⟨3865211, by rfl⟩ : syracuseStep 5153615 = 7730423) B7730423
theorem B3435743 : Blo 2289435 3435743 := bstep (se 1 (by rfl) ⟨2576807, by rfl⟩ : syracuseStep 3435743 = 5153615) B5153615
theorem B2290495 : Blo 2289435 2290495 := bstep (se 1 (by rfl) ⟨1717871, by rfl⟩ : syracuseStep 2290495 = 3435743) B3435743
theorem B3435749 : Blo 2289435 3435749 := bbase (se 4 (by rfl) ⟨322101, by rfl⟩ : syracuseStep 3435749 = 644203) (by norm_num)
theorem B2290499 : Blo 2289435 2290499 := bstep (se 1 (by rfl) ⟨1717874, by rfl⟩ : syracuseStep 2290499 = 3435749) B3435749
theorem B11006837 : Blo 2289435 11006837 := bbase (se 5 (by rfl) ⟨515945, by rfl⟩ : syracuseStep 11006837 = 1031891) (by norm_num)
theorem B7337891 : Blo 2289435 7337891 := bstep (se 1 (by rfl) ⟨5503418, by rfl⟩ : syracuseStep 7337891 = 11006837) B11006837
theorem B4891927 : Blo 2289435 4891927 := bstep (se 1 (by rfl) ⟨3668945, by rfl⟩ : syracuseStep 4891927 = 7337891) B7337891
theorem B6522569 : Blo 2289435 6522569 := bstep (se 2 (by rfl) ⟨2445963, by rfl⟩ : syracuseStep 6522569 = 4891927) B4891927
theorem B4348379 : Blo 2289435 4348379 := bstep (se 1 (by rfl) ⟨3261284, by rfl⟩ : syracuseStep 4348379 = 6522569) B6522569
theorem B2898919 : Blo 2289435 2898919 := bstep (se 1 (by rfl) ⟨2174189, by rfl⟩ : syracuseStep 2898919 = 4348379) B4348379
theorem B3865225 : Blo 2289435 3865225 := bstep (se 2 (by rfl) ⟨1449459, by rfl⟩ : syracuseStep 3865225 = 2898919) B2898919
theorem B5153633 : Blo 2289435 5153633 := bstep (se 2 (by rfl) ⟨1932612, by rfl⟩ : syracuseStep 5153633 = 3865225) B3865225
theorem B3435755 : Blo 2289435 3435755 := bstep (se 1 (by rfl) ⟨2576816, by rfl⟩ : syracuseStep 3435755 = 5153633) B5153633
theorem B2290503 : Blo 2289435 2290503 := bstep (se 1 (by rfl) ⟨1717877, by rfl⟩ : syracuseStep 2290503 = 3435755) B3435755
theorem B2576821 : Blo 2289435 2576821 := bbase (se 5 (by rfl) ⟨120788, by rfl⟩ : syracuseStep 2576821 = 241577) (by norm_num)
theorem B3435761 : Blo 2289435 3435761 := bstep (se 2 (by rfl) ⟨1288410, by rfl⟩ : syracuseStep 3435761 = 2576821) B2576821
theorem B2290507 : Blo 2289435 2290507 := bstep (se 1 (by rfl) ⟨1717880, by rfl⟩ : syracuseStep 2290507 = 3435761) B3435761
theorem B2898929 : Blo 2289435 2898929 := bbase (se 2 (by rfl) ⟨1087098, by rfl⟩ : syracuseStep 2898929 = 2174197) (by norm_num)
theorem B7730477 : Blo 2289435 7730477 := bstep (se 3 (by rfl) ⟨1449464, by rfl⟩ : syracuseStep 7730477 = 2898929) B2898929
theorem B5153651 : Blo 2289435 5153651 := bstep (se 1 (by rfl) ⟨3865238, by rfl⟩ : syracuseStep 5153651 = 7730477) B7730477
theorem B3435767 : Blo 2289435 3435767 := bstep (se 1 (by rfl) ⟨2576825, by rfl⟩ : syracuseStep 3435767 = 5153651) B5153651
theorem B2290511 : Blo 2289435 2290511 := bstep (se 1 (by rfl) ⟨1717883, by rfl⟩ : syracuseStep 2290511 = 3435767) B3435767
theorem B3435773 : Blo 2289435 3435773 := bbase (se 3 (by rfl) ⟨644207, by rfl⟩ : syracuseStep 3435773 = 1288415) (by norm_num)
theorem B2290515 : Blo 2289435 2290515 := bstep (se 1 (by rfl) ⟨1717886, by rfl⟩ : syracuseStep 2290515 = 3435773) B3435773
theorem B5153669 : Blo 2289435 5153669 := bbase (se 4 (by rfl) ⟨483156, by rfl⟩ : syracuseStep 5153669 = 966313) (by norm_num)
theorem B3435779 : Blo 2289435 3435779 := bstep (se 1 (by rfl) ⟨2576834, by rfl⟩ : syracuseStep 3435779 = 5153669) B5153669
theorem B2290519 : Blo 2289435 2290519 := bstep (se 1 (by rfl) ⟨1717889, by rfl⟩ : syracuseStep 2290519 = 3435779) B3435779
theorem B2445985 : Blo 2289435 2445985 := bbase (se 2 (by rfl) ⟨917244, by rfl⟩ : syracuseStep 2445985 = 1834489) (by norm_num)
theorem B3261313 : Blo 2289435 3261313 := bstep (se 2 (by rfl) ⟨1222992, by rfl⟩ : syracuseStep 3261313 = 2445985) B2445985
theorem B4348417 : Blo 2289435 4348417 := bstep (se 2 (by rfl) ⟨1630656, by rfl⟩ : syracuseStep 4348417 = 3261313) B3261313
theorem B5797889 : Blo 2289435 5797889 := bstep (se 2 (by rfl) ⟨2174208, by rfl⟩ : syracuseStep 5797889 = 4348417) B4348417
theorem B3865259 : Blo 2289435 3865259 := bstep (se 1 (by rfl) ⟨2898944, by rfl⟩ : syracuseStep 3865259 = 5797889) B5797889
theorem B2576839 : Blo 2289435 2576839 := bstep (se 1 (by rfl) ⟨1932629, by rfl⟩ : syracuseStep 2576839 = 3865259) B3865259
theorem B3435785 : Blo 2289435 3435785 := bstep (se 2 (by rfl) ⟨1288419, by rfl⟩ : syracuseStep 3435785 = 2576839) B2576839
theorem B2290523 : Blo 2289435 2290523 := bstep (se 1 (by rfl) ⟨1717892, by rfl⟩ : syracuseStep 2290523 = 3435785) B3435785
theorem B11595797 : Blo 2289435 11595797 := bbase (se 6 (by rfl) ⟨271776, by rfl⟩ : syracuseStep 11595797 = 543553) (by norm_num)
theorem B7730531 : Blo 2289435 7730531 := bstep (se 1 (by rfl) ⟨5797898, by rfl⟩ : syracuseStep 7730531 = 11595797) B11595797
theorem B5153687 : Blo 2289435 5153687 := bstep (se 1 (by rfl) ⟨3865265, by rfl⟩ : syracuseStep 5153687 = 7730531) B7730531
theorem B3435791 : Blo 2289435 3435791 := bstep (se 1 (by rfl) ⟨2576843, by rfl⟩ : syracuseStep 3435791 = 5153687) B5153687
theorem B2290527 : Blo 2289435 2290527 := bstep (se 1 (by rfl) ⟨1717895, by rfl⟩ : syracuseStep 2290527 = 3435791) B3435791
theorem B3435797 : Blo 2289435 3435797 := bbase (se 6 (by rfl) ⟨80526, by rfl⟩ : syracuseStep 3435797 = 161053) (by norm_num)
theorem B2290531 : Blo 2289435 2290531 := bstep (se 1 (by rfl) ⟨1717898, by rfl⟩ : syracuseStep 2290531 = 3435797) B3435797
theorem B89257301 : Blo 2289435 89257301 := bbase (se 13 (by rfl) ⟨16343, by rfl⟩ : syracuseStep 89257301 = 32687) (by norm_num)
theorem B59504867 : Blo 2289435 59504867 := bstep (se 1 (by rfl) ⟨44628650, by rfl⟩ : syracuseStep 59504867 = 89257301) B89257301
theorem B39669911 : Blo 2289435 39669911 := bstep (se 1 (by rfl) ⟨29752433, by rfl⟩ : syracuseStep 39669911 = 59504867) B59504867
theorem B26446607 : Blo 2289435 26446607 := bstep (se 1 (by rfl) ⟨19834955, by rfl⟩ : syracuseStep 26446607 = 39669911) B39669911
theorem B17631071 : Blo 2289435 17631071 := bstep (se 1 (by rfl) ⟨13223303, by rfl⟩ : syracuseStep 17631071 = 26446607) B26446607
theorem B11754047 : Blo 2289435 11754047 := bstep (se 1 (by rfl) ⟨8815535, by rfl⟩ : syracuseStep 11754047 = 17631071) B17631071
theorem B7836031 : Blo 2289435 7836031 := bstep (se 1 (by rfl) ⟨5877023, by rfl⟩ : syracuseStep 7836031 = 11754047) B11754047
theorem B10448041 : Blo 2289435 10448041 := bstep (se 2 (by rfl) ⟨3918015, by rfl⟩ : syracuseStep 10448041 = 7836031) B7836031
theorem B13930721 : Blo 2289435 13930721 := bstep (se 2 (by rfl) ⟨5224020, by rfl⟩ : syracuseStep 13930721 = 10448041) B10448041
theorem B9287147 : Blo 2289435 9287147 := bstep (se 1 (by rfl) ⟨6965360, by rfl⟩ : syracuseStep 9287147 = 13930721) B13930721
theorem B24765725 : Blo 2289435 24765725 := bstep (se 3 (by rfl) ⟨4643573, by rfl⟩ : syracuseStep 24765725 = 9287147) B9287147
theorem B16510483 : Blo 2289435 16510483 := bstep (se 1 (by rfl) ⟨12382862, by rfl⟩ : syracuseStep 16510483 = 24765725) B24765725
theorem B22013977 : Blo 2289435 22013977 := bstep (se 2 (by rfl) ⟨8255241, by rfl⟩ : syracuseStep 22013977 = 16510483) B16510483
theorem B29351969 : Blo 2289435 29351969 := bstep (se 2 (by rfl) ⟨11006988, by rfl⟩ : syracuseStep 29351969 = 22013977) B22013977
theorem B19567979 : Blo 2289435 19567979 := bstep (se 1 (by rfl) ⟨14675984, by rfl⟩ : syracuseStep 19567979 = 29351969) B29351969
theorem B13045319 : Blo 2289435 13045319 := bstep (se 1 (by rfl) ⟨9783989, by rfl⟩ : syracuseStep 13045319 = 19567979) B19567979
theorem B8696879 : Blo 2289435 8696879 := bstep (se 1 (by rfl) ⟨6522659, by rfl⟩ : syracuseStep 8696879 = 13045319) B13045319
theorem B5797919 : Blo 2289435 5797919 := bstep (se 1 (by rfl) ⟨4348439, by rfl⟩ : syracuseStep 5797919 = 8696879) B8696879
theorem B3865279 : Blo 2289435 3865279 := bstep (se 1 (by rfl) ⟨2898959, by rfl⟩ : syracuseStep 3865279 = 5797919) B5797919
theorem B5153705 : Blo 2289435 5153705 := bstep (se 2 (by rfl) ⟨1932639, by rfl⟩ : syracuseStep 5153705 = 3865279) B3865279
theorem B3435803 : Blo 2289435 3435803 := bstep (se 1 (by rfl) ⟨2576852, by rfl⟩ : syracuseStep 3435803 = 5153705) B5153705
theorem B2290535 : Blo 2289435 2290535 := bstep (se 1 (by rfl) ⟨1717901, by rfl⟩ : syracuseStep 2290535 = 3435803) B3435803
theorem B2576857 : Blo 2289435 2576857 := bbase (se 2 (by rfl) ⟨966321, by rfl⟩ : syracuseStep 2576857 = 1932643) (by norm_num)
theorem B3435809 : Blo 2289435 3435809 := bstep (se 2 (by rfl) ⟨1288428, by rfl⟩ : syracuseStep 3435809 = 2576857) B2576857
theorem B2290539 : Blo 2289435 2290539 := bstep (se 1 (by rfl) ⟨1717904, by rfl⟩ : syracuseStep 2290539 = 3435809) B3435809
theorem B3261341 : Blo 2289435 3261341 := bbase (se 3 (by rfl) ⟨611501, by rfl⟩ : syracuseStep 3261341 = 1223003) (by norm_num)
theorem B8696909 : Blo 2289435 8696909 := bstep (se 3 (by rfl) ⟨1630670, by rfl⟩ : syracuseStep 8696909 = 3261341) B3261341
theorem B5797939 : Blo 2289435 5797939 := bstep (se 1 (by rfl) ⟨4348454, by rfl⟩ : syracuseStep 5797939 = 8696909) B8696909
theorem B7730585 : Blo 2289435 7730585 := bstep (se 2 (by rfl) ⟨2898969, by rfl⟩ : syracuseStep 7730585 = 5797939) B5797939
theorem B5153723 : Blo 2289435 5153723 := bstep (se 1 (by rfl) ⟨3865292, by rfl⟩ : syracuseStep 5153723 = 7730585) B7730585
theorem B3435815 : Blo 2289435 3435815 := bstep (se 1 (by rfl) ⟨2576861, by rfl⟩ : syracuseStep 3435815 = 5153723) B5153723
theorem B2290543 : Blo 2289435 2290543 := bstep (se 1 (by rfl) ⟨1717907, by rfl⟩ : syracuseStep 2290543 = 3435815) B3435815
theorem B3435821 : Blo 2289435 3435821 := bbase (se 3 (by rfl) ⟨644216, by rfl⟩ : syracuseStep 3435821 = 1288433) (by norm_num)
theorem B2290547 : Blo 2289435 2290547 := bstep (se 1 (by rfl) ⟨1717910, by rfl⟩ : syracuseStep 2290547 = 3435821) B3435821
theorem B5153741 : Blo 2289435 5153741 := bbase (se 3 (by rfl) ⟨966326, by rfl⟩ : syracuseStep 5153741 = 1932653) (by norm_num)
theorem B3435827 : Blo 2289435 3435827 := bstep (se 1 (by rfl) ⟨2576870, by rfl⟩ : syracuseStep 3435827 = 5153741) B5153741
theorem B2290551 : Blo 2289435 2290551 := bstep (se 1 (by rfl) ⟨1717913, by rfl⟩ : syracuseStep 2290551 = 3435827) B3435827
theorem B2898985 : Blo 2289435 2898985 := bbase (se 2 (by rfl) ⟨1087119, by rfl⟩ : syracuseStep 2898985 = 2174239) (by norm_num)
theorem B3865313 : Blo 2289435 3865313 := bstep (se 2 (by rfl) ⟨1449492, by rfl⟩ : syracuseStep 3865313 = 2898985) B2898985
theorem B2576875 : Blo 2289435 2576875 := bstep (se 1 (by rfl) ⟨1932656, by rfl⟩ : syracuseStep 2576875 = 3865313) B3865313
theorem B3435833 : Blo 2289435 3435833 := bstep (se 2 (by rfl) ⟨1288437, by rfl⟩ : syracuseStep 3435833 = 2576875) B2576875
theorem B2290555 : Blo 2289435 2290555 := bstep (se 1 (by rfl) ⟨1717916, by rfl⟩ : syracuseStep 2290555 = 3435833) B3435833
theorem B3350965 : Blo 2289435 3350965 := bbase (se 5 (by rfl) ⟨157076, by rfl⟩ : syracuseStep 3350965 = 314153) (by norm_num)
theorem B4467953 : Blo 2289435 4467953 := bstep (se 2 (by rfl) ⟨1675482, by rfl⟩ : syracuseStep 4467953 = 3350965) B3350965
theorem B2978635 : Blo 2289435 2978635 := bstep (se 1 (by rfl) ⟨2233976, by rfl⟩ : syracuseStep 2978635 = 4467953) B4467953
theorem B3971513 : Blo 2289435 3971513 := bstep (se 2 (by rfl) ⟨1489317, by rfl⟩ : syracuseStep 3971513 = 2978635) B2978635
theorem B2647675 : Blo 2289435 2647675 := bstep (se 1 (by rfl) ⟨1985756, by rfl⟩ : syracuseStep 2647675 = 3971513) B3971513
theorem B3530233 : Blo 2289435 3530233 := bstep (se 2 (by rfl) ⟨1323837, by rfl⟩ : syracuseStep 3530233 = 2647675) B2647675
theorem B4706977 : Blo 2289435 4706977 := bstep (se 2 (by rfl) ⟨1765116, by rfl⟩ : syracuseStep 4706977 = 3530233) B3530233
theorem B6275969 : Blo 2289435 6275969 := bstep (se 2 (by rfl) ⟨2353488, by rfl⟩ : syracuseStep 6275969 = 4706977) B4706977
theorem B4183979 : Blo 2289435 4183979 := bstep (se 1 (by rfl) ⟨3137984, by rfl⟩ : syracuseStep 4183979 = 6275969) B6275969
theorem B44629109 : Blo 2289435 44629109 := bstep (se 5 (by rfl) ⟨2091989, by rfl⟩ : syracuseStep 44629109 = 4183979) B4183979
theorem B29752739 : Blo 2289435 29752739 := bstep (se 1 (by rfl) ⟨22314554, by rfl⟩ : syracuseStep 29752739 = 44629109) B44629109
theorem B19835159 : Blo 2289435 19835159 := bstep (se 1 (by rfl) ⟨14876369, by rfl⟩ : syracuseStep 19835159 = 29752739) B29752739
theorem B52893757 : Blo 2289435 52893757 := bstep (se 3 (by rfl) ⟨9917579, by rfl⟩ : syracuseStep 52893757 = 19835159) B19835159
theorem B70525009 : Blo 2289435 70525009 := bstep (se 2 (by rfl) ⟨26446878, by rfl⟩ : syracuseStep 70525009 = 52893757) B52893757
theorem B94033345 : Blo 2289435 94033345 := bstep (se 2 (by rfl) ⟨35262504, by rfl⟩ : syracuseStep 94033345 = 70525009) B70525009
theorem B125377793 : Blo 2289435 125377793 := bstep (se 2 (by rfl) ⟨47016672, by rfl⟩ : syracuseStep 125377793 = 94033345) B94033345
theorem B83585195 : Blo 2289435 83585195 := bstep (se 1 (by rfl) ⟨62688896, by rfl⟩ : syracuseStep 83585195 = 125377793) B125377793
theorem B55723463 : Blo 2289435 55723463 := bstep (se 1 (by rfl) ⟨41792597, by rfl⟩ : syracuseStep 55723463 = 83585195) B83585195
theorem B37148975 : Blo 2289435 37148975 := bstep (se 1 (by rfl) ⟨27861731, by rfl⟩ : syracuseStep 37148975 = 55723463) B55723463
theorem B24765983 : Blo 2289435 24765983 := bstep (se 1 (by rfl) ⟨18574487, by rfl⟩ : syracuseStep 24765983 = 37148975) B37148975
theorem B16510655 : Blo 2289435 16510655 := bstep (se 1 (by rfl) ⟨12382991, by rfl⟩ : syracuseStep 16510655 = 24765983) B24765983
theorem B11007103 : Blo 2289435 11007103 := bstep (se 1 (by rfl) ⟨8255327, by rfl⟩ : syracuseStep 11007103 = 16510655) B16510655
theorem B14676137 : Blo 2289435 14676137 := bstep (se 2 (by rfl) ⟨5503551, by rfl⟩ : syracuseStep 14676137 = 11007103) B11007103
theorem B9784091 : Blo 2289435 9784091 := bstep (se 1 (by rfl) ⟨7338068, by rfl⟩ : syracuseStep 9784091 = 14676137) B14676137
theorem B26090909 : Blo 2289435 26090909 := bstep (se 3 (by rfl) ⟨4892045, by rfl⟩ : syracuseStep 26090909 = 9784091) B9784091
theorem B17393939 : Blo 2289435 17393939 := bstep (se 1 (by rfl) ⟨13045454, by rfl⟩ : syracuseStep 17393939 = 26090909) B26090909
theorem B11595959 : Blo 2289435 11595959 := bstep (se 1 (by rfl) ⟨8696969, by rfl⟩ : syracuseStep 11595959 = 17393939) B17393939
theorem B7730639 : Blo 2289435 7730639 := bstep (se 1 (by rfl) ⟨5797979, by rfl⟩ : syracuseStep 7730639 = 11595959) B11595959
theorem B5153759 : Blo 2289435 5153759 := bstep (se 1 (by rfl) ⟨3865319, by rfl⟩ : syracuseStep 5153759 = 7730639) B7730639
theorem B3435839 : Blo 2289435 3435839 := bstep (se 1 (by rfl) ⟨2576879, by rfl⟩ : syracuseStep 3435839 = 5153759) B5153759
theorem B2290559 : Blo 2289435 2290559 := bstep (se 1 (by rfl) ⟨1717919, by rfl⟩ : syracuseStep 2290559 = 3435839) B3435839
theorem B3435845 : Blo 2289435 3435845 := bbase (se 4 (by rfl) ⟨322110, by rfl⟩ : syracuseStep 3435845 = 644221) (by norm_num)
theorem B2290563 : Blo 2289435 2290563 := bstep (se 1 (by rfl) ⟨1717922, by rfl⟩ : syracuseStep 2290563 = 3435845) B3435845
theorem B3865333 : Blo 2289435 3865333 := bbase (se 5 (by rfl) ⟨181187, by rfl⟩ : syracuseStep 3865333 = 362375) (by norm_num)
theorem B5153777 : Blo 2289435 5153777 := bstep (se 2 (by rfl) ⟨1932666, by rfl⟩ : syracuseStep 5153777 = 3865333) B3865333
theorem B3435851 : Blo 2289435 3435851 := bstep (se 1 (by rfl) ⟨2576888, by rfl⟩ : syracuseStep 3435851 = 5153777) B5153777
theorem B2290567 : Blo 2289435 2290567 := bstep (se 1 (by rfl) ⟨1717925, by rfl⟩ : syracuseStep 2290567 = 3435851) B3435851
theorem B2576893 : Blo 2289435 2576893 := bbase (se 3 (by rfl) ⟨483167, by rfl⟩ : syracuseStep 2576893 = 966335) (by norm_num)
theorem B3435857 : Blo 2289435 3435857 := bstep (se 2 (by rfl) ⟨1288446, by rfl⟩ : syracuseStep 3435857 = 2576893) B2576893
theorem B2290571 : Blo 2289435 2290571 := bstep (se 1 (by rfl) ⟨1717928, by rfl⟩ : syracuseStep 2290571 = 3435857) B3435857
theorem B7730693 : Blo 2289435 7730693 := bbase (se 4 (by rfl) ⟨724752, by rfl⟩ : syracuseStep 7730693 = 1449505) (by norm_num)
theorem B5153795 : Blo 2289435 5153795 := bstep (se 1 (by rfl) ⟨3865346, by rfl⟩ : syracuseStep 5153795 = 7730693) B7730693
theorem B3435863 : Blo 2289435 3435863 := bstep (se 1 (by rfl) ⟨2576897, by rfl⟩ : syracuseStep 3435863 = 5153795) B5153795
theorem B2290575 : Blo 2289435 2290575 := bstep (se 1 (by rfl) ⟨1717931, by rfl⟩ : syracuseStep 2290575 = 3435863) B3435863
theorem B3435869 : Blo 2289435 3435869 := bbase (se 3 (by rfl) ⟨644225, by rfl⟩ : syracuseStep 3435869 = 1288451) (by norm_num)
theorem B2290579 : Blo 2289435 2290579 := bstep (se 1 (by rfl) ⟨1717934, by rfl⟩ : syracuseStep 2290579 = 3435869) B3435869
theorem B5153813 : Blo 2289435 5153813 := bbase (se 6 (by rfl) ⟨120792, by rfl⟩ : syracuseStep 5153813 = 241585) (by norm_num)
theorem B3435875 : Blo 2289435 3435875 := bstep (se 1 (by rfl) ⟨2576906, by rfl⟩ : syracuseStep 3435875 = 5153813) B5153813
theorem B2290583 : Blo 2289435 2290583 := bstep (se 1 (by rfl) ⟨1717937, by rfl⟩ : syracuseStep 2290583 = 3435875) B3435875
theorem B8697077 : Blo 2289435 8697077 := bbase (se 5 (by rfl) ⟨407675, by rfl⟩ : syracuseStep 8697077 = 815351) (by norm_num)
theorem B5798051 : Blo 2289435 5798051 := bstep (se 1 (by rfl) ⟨4348538, by rfl⟩ : syracuseStep 5798051 = 8697077) B8697077
theorem B3865367 : Blo 2289435 3865367 := bstep (se 1 (by rfl) ⟨2899025, by rfl⟩ : syracuseStep 3865367 = 5798051) B5798051
theorem B2576911 : Blo 2289435 2576911 := bstep (se 1 (by rfl) ⟨1932683, by rfl⟩ : syracuseStep 2576911 = 3865367) B3865367
theorem B3435881 : Blo 2289435 3435881 := bstep (se 2 (by rfl) ⟨1288455, by rfl⟩ : syracuseStep 3435881 = 2576911) B2576911
theorem B2290587 : Blo 2289435 2290587 := bstep (se 1 (by rfl) ⟨1717940, by rfl⟩ : syracuseStep 2290587 = 3435881) B3435881
theorem B2446057 : Blo 2289435 2446057 := bbase (se 2 (by rfl) ⟨917271, by rfl⟩ : syracuseStep 2446057 = 1834543) (by norm_num)
theorem B13045637 : Blo 2289435 13045637 := bstep (se 4 (by rfl) ⟨1223028, by rfl⟩ : syracuseStep 13045637 = 2446057) B2446057
theorem B8697091 : Blo 2289435 8697091 := bstep (se 1 (by rfl) ⟨6522818, by rfl⟩ : syracuseStep 8697091 = 13045637) B13045637
theorem B11596121 : Blo 2289435 11596121 := bstep (se 2 (by rfl) ⟨4348545, by rfl⟩ : syracuseStep 11596121 = 8697091) B8697091
theorem B7730747 : Blo 2289435 7730747 := bstep (se 1 (by rfl) ⟨5798060, by rfl⟩ : syracuseStep 7730747 = 11596121) B11596121
theorem B5153831 : Blo 2289435 5153831 := bstep (se 1 (by rfl) ⟨3865373, by rfl⟩ : syracuseStep 5153831 = 7730747) B7730747
theorem B3435887 : Blo 2289435 3435887 := bstep (se 1 (by rfl) ⟨2576915, by rfl⟩ : syracuseStep 3435887 = 5153831) B5153831
theorem B2290591 : Blo 2289435 2290591 := bstep (se 1 (by rfl) ⟨1717943, by rfl⟩ : syracuseStep 2290591 = 3435887) B3435887
theorem B3435893 : Blo 2289435 3435893 := bbase (se 5 (by rfl) ⟨161057, by rfl⟩ : syracuseStep 3435893 = 322115) (by norm_num)
theorem B2290595 : Blo 2289435 2290595 := bstep (se 1 (by rfl) ⟨1717946, by rfl⟩ : syracuseStep 2290595 = 3435893) B3435893
theorem B3261421 : Blo 2289435 3261421 := bbase (se 3 (by rfl) ⟨611516, by rfl⟩ : syracuseStep 3261421 = 1223033) (by norm_num)
theorem B4348561 : Blo 2289435 4348561 := bstep (se 2 (by rfl) ⟨1630710, by rfl⟩ : syracuseStep 4348561 = 3261421) B3261421
theorem B5798081 : Blo 2289435 5798081 := bstep (se 2 (by rfl) ⟨2174280, by rfl⟩ : syracuseStep 5798081 = 4348561) B4348561
theorem B3865387 : Blo 2289435 3865387 := bstep (se 1 (by rfl) ⟨2899040, by rfl⟩ : syracuseStep 3865387 = 5798081) B5798081
theorem B5153849 : Blo 2289435 5153849 := bstep (se 2 (by rfl) ⟨1932693, by rfl⟩ : syracuseStep 5153849 = 3865387) B3865387
theorem B3435899 : Blo 2289435 3435899 := bstep (se 1 (by rfl) ⟨2576924, by rfl⟩ : syracuseStep 3435899 = 5153849) B5153849
theorem B2290599 : Blo 2289435 2290599 := bstep (se 1 (by rfl) ⟨1717949, by rfl⟩ : syracuseStep 2290599 = 3435899) B3435899
theorem B2576929 : Blo 2289435 2576929 := bbase (se 2 (by rfl) ⟨966348, by rfl⟩ : syracuseStep 2576929 = 1932697) (by norm_num)
theorem B3435905 : Blo 2289435 3435905 := bstep (se 2 (by rfl) ⟨1288464, by rfl⟩ : syracuseStep 3435905 = 2576929) B2576929
theorem B2290603 : Blo 2289435 2290603 := bstep (se 1 (by rfl) ⟨1717952, by rfl⟩ : syracuseStep 2290603 = 3435905) B3435905
theorem B5798101 : Blo 2289435 5798101 := bbase (se 7 (by rfl) ⟨67946, by rfl⟩ : syracuseStep 5798101 = 135893) (by norm_num)
theorem B7730801 : Blo 2289435 7730801 := bstep (se 2 (by rfl) ⟨2899050, by rfl⟩ : syracuseStep 7730801 = 5798101) B5798101
theorem B5153867 : Blo 2289435 5153867 := bstep (se 1 (by rfl) ⟨3865400, by rfl⟩ : syracuseStep 5153867 = 7730801) B7730801
theorem B3435911 : Blo 2289435 3435911 := bstep (se 1 (by rfl) ⟨2576933, by rfl⟩ : syracuseStep 3435911 = 5153867) B5153867
theorem B2290607 : Blo 2289435 2290607 := bstep (se 1 (by rfl) ⟨1717955, by rfl⟩ : syracuseStep 2290607 = 3435911) B3435911
theorem B3435917 : Blo 2289435 3435917 := bbase (se 3 (by rfl) ⟨644234, by rfl⟩ : syracuseStep 3435917 = 1288469) (by norm_num)
theorem B2290611 : Blo 2289435 2290611 := bstep (se 1 (by rfl) ⟨1717958, by rfl⟩ : syracuseStep 2290611 = 3435917) B3435917
theorem B5153885 : Blo 2289435 5153885 := bbase (se 3 (by rfl) ⟨966353, by rfl⟩ : syracuseStep 5153885 = 1932707) (by norm_num)
theorem B3435923 : Blo 2289435 3435923 := bstep (se 1 (by rfl) ⟨2576942, by rfl⟩ : syracuseStep 3435923 = 5153885) B5153885
theorem B2290615 : Blo 2289435 2290615 := bstep (se 1 (by rfl) ⟨1717961, by rfl⟩ : syracuseStep 2290615 = 3435923) B3435923
theorem B3865421 : Blo 2289435 3865421 := bbase (se 3 (by rfl) ⟨724766, by rfl⟩ : syracuseStep 3865421 = 1449533) (by norm_num)
theorem B2576947 : Blo 2289435 2576947 := bstep (se 1 (by rfl) ⟨1932710, by rfl⟩ : syracuseStep 2576947 = 3865421) B3865421
theorem B3435929 : Blo 2289435 3435929 := bstep (se 2 (by rfl) ⟨1288473, by rfl⟩ : syracuseStep 3435929 = 2576947) B2576947
theorem B2290619 : Blo 2289435 2290619 := bstep (se 1 (by rfl) ⟨1717964, by rfl⟩ : syracuseStep 2290619 = 3435929) B3435929
theorem B6191669 : Blo 2289435 6191669 := bbase (se 5 (by rfl) ⟨290234, by rfl⟩ : syracuseStep 6191669 = 580469) (by norm_num)
theorem B4127779 : Blo 2289435 4127779 := bstep (se 1 (by rfl) ⟨3095834, by rfl⟩ : syracuseStep 4127779 = 6191669) B6191669
theorem B22014821 : Blo 2289435 22014821 := bstep (se 4 (by rfl) ⟨2063889, by rfl⟩ : syracuseStep 22014821 = 4127779) B4127779
theorem B14676547 : Blo 2289435 14676547 := bstep (se 1 (by rfl) ⟨11007410, by rfl⟩ : syracuseStep 14676547 = 22014821) B22014821
theorem B19568729 : Blo 2289435 19568729 := bstep (se 2 (by rfl) ⟨7338273, by rfl⟩ : syracuseStep 19568729 = 14676547) B14676547
theorem B13045819 : Blo 2289435 13045819 := bstep (se 1 (by rfl) ⟨9784364, by rfl⟩ : syracuseStep 13045819 = 19568729) B19568729
theorem B17394425 : Blo 2289435 17394425 := bstep (se 2 (by rfl) ⟨6522909, by rfl⟩ : syracuseStep 17394425 = 13045819) B13045819
theorem B11596283 : Blo 2289435 11596283 := bstep (se 1 (by rfl) ⟨8697212, by rfl⟩ : syracuseStep 11596283 = 17394425) B17394425
theorem B7730855 : Blo 2289435 7730855 := bstep (se 1 (by rfl) ⟨5798141, by rfl⟩ : syracuseStep 7730855 = 11596283) B11596283
theorem B5153903 : Blo 2289435 5153903 := bstep (se 1 (by rfl) ⟨3865427, by rfl⟩ : syracuseStep 5153903 = 7730855) B7730855
theorem B3435935 : Blo 2289435 3435935 := bstep (se 1 (by rfl) ⟨2576951, by rfl⟩ : syracuseStep 3435935 = 5153903) B5153903
theorem B2290623 : Blo 2289435 2290623 := bstep (se 1 (by rfl) ⟨1717967, by rfl⟩ : syracuseStep 2290623 = 3435935) B3435935
theorem B3435941 : Blo 2289435 3435941 := bbase (se 4 (by rfl) ⟨322119, by rfl⟩ : syracuseStep 3435941 = 644239) (by norm_num)
theorem B2290627 : Blo 2289435 2290627 := bstep (se 1 (by rfl) ⟨1717970, by rfl⟩ : syracuseStep 2290627 = 3435941) B3435941
theorem B2899081 : Blo 2289435 2899081 := bbase (se 2 (by rfl) ⟨1087155, by rfl⟩ : syracuseStep 2899081 = 2174311) (by norm_num)
theorem B3865441 : Blo 2289435 3865441 := bstep (se 2 (by rfl) ⟨1449540, by rfl⟩ : syracuseStep 3865441 = 2899081) B2899081
theorem B5153921 : Blo 2289435 5153921 := bstep (se 2 (by rfl) ⟨1932720, by rfl⟩ : syracuseStep 5153921 = 3865441) B3865441
theorem B3435947 : Blo 2289435 3435947 := bstep (se 1 (by rfl) ⟨2576960, by rfl⟩ : syracuseStep 3435947 = 5153921) B5153921
theorem B2290631 : Blo 2289435 2290631 := bstep (se 1 (by rfl) ⟨1717973, by rfl⟩ : syracuseStep 2290631 = 3435947) B3435947
theorem B2576965 : Blo 2289435 2576965 := bbase (se 4 (by rfl) ⟨241590, by rfl⟩ : syracuseStep 2576965 = 483181) (by norm_num)
theorem B3435953 : Blo 2289435 3435953 := bstep (se 2 (by rfl) ⟨1288482, by rfl⟩ : syracuseStep 3435953 = 2576965) B2576965
theorem B2290635 : Blo 2289435 2290635 := bstep (se 1 (by rfl) ⟨1717976, by rfl⟩ : syracuseStep 2290635 = 3435953) B3435953
theorem B4348637 : Blo 2289435 4348637 := bbase (se 3 (by rfl) ⟨815369, by rfl⟩ : syracuseStep 4348637 = 1630739) (by norm_num)
theorem B2899091 : Blo 2289435 2899091 := bstep (se 1 (by rfl) ⟨2174318, by rfl⟩ : syracuseStep 2899091 = 4348637) B4348637
theorem B7730909 : Blo 2289435 7730909 := bstep (se 3 (by rfl) ⟨1449545, by rfl⟩ : syracuseStep 7730909 = 2899091) B2899091
theorem B5153939 : Blo 2289435 5153939 := bstep (se 1 (by rfl) ⟨3865454, by rfl⟩ : syracuseStep 5153939 = 7730909) B7730909
theorem B3435959 : Blo 2289435 3435959 := bstep (se 1 (by rfl) ⟨2576969, by rfl⟩ : syracuseStep 3435959 = 5153939) B5153939
theorem B2290639 : Blo 2289435 2290639 := bstep (se 1 (by rfl) ⟨1717979, by rfl⟩ : syracuseStep 2290639 = 3435959) B3435959
theorem B3435965 : Blo 2289435 3435965 := bbase (se 3 (by rfl) ⟨644243, by rfl⟩ : syracuseStep 3435965 = 1288487) (by norm_num)
theorem B2290643 : Blo 2289435 2290643 := bstep (se 1 (by rfl) ⟨1717982, by rfl⟩ : syracuseStep 2290643 = 3435965) B3435965
theorem B5153957 : Blo 2289435 5153957 := bbase (se 4 (by rfl) ⟨483183, by rfl⟩ : syracuseStep 5153957 = 966367) (by norm_num)
theorem B3435971 : Blo 2289435 3435971 := bstep (se 1 (by rfl) ⟨2576978, by rfl⟩ : syracuseStep 3435971 = 5153957) B5153957
theorem B2290647 : Blo 2289435 2290647 := bstep (se 1 (by rfl) ⟨1717985, by rfl⟩ : syracuseStep 2290647 = 3435971) B3435971
theorem B5798213 : Blo 2289435 5798213 := bbase (se 4 (by rfl) ⟨543582, by rfl⟩ : syracuseStep 5798213 = 1087165) (by norm_num)
theorem B3865475 : Blo 2289435 3865475 := bstep (se 1 (by rfl) ⟨2899106, by rfl⟩ : syracuseStep 3865475 = 5798213) B5798213
theorem B2576983 : Blo 2289435 2576983 := bstep (se 1 (by rfl) ⟨1932737, by rfl⟩ : syracuseStep 2576983 = 3865475) B3865475
theorem B3435977 : Blo 2289435 3435977 := bstep (se 2 (by rfl) ⟨1288491, by rfl⟩ : syracuseStep 3435977 = 2576983) B2576983
theorem B2290651 : Blo 2289435 2290651 := bstep (se 1 (by rfl) ⟨1717988, by rfl⟩ : syracuseStep 2290651 = 3435977) B3435977
theorem B32206933 : Blo 2289435 32206933 := bbase (se 8 (by rfl) ⟨188712, by rfl⟩ : syracuseStep 32206933 = 377425) (by norm_num)
theorem B42942577 : Blo 2289435 42942577 := bstep (se 2 (by rfl) ⟨16103466, by rfl⟩ : syracuseStep 42942577 = 32206933) B32206933
theorem B57256769 : Blo 2289435 57256769 := bstep (se 2 (by rfl) ⟨21471288, by rfl⟩ : syracuseStep 57256769 = 42942577) B42942577
theorem B38171179 : Blo 2289435 38171179 := bstep (se 1 (by rfl) ⟨28628384, by rfl⟩ : syracuseStep 38171179 = 57256769) B57256769
theorem B50894905 : Blo 2289435 50894905 := bstep (se 2 (by rfl) ⟨19085589, by rfl⟩ : syracuseStep 50894905 = 38171179) B38171179
theorem B67859873 : Blo 2289435 67859873 := bstep (se 2 (by rfl) ⟨25447452, by rfl⟩ : syracuseStep 67859873 = 50894905) B50894905
theorem B45239915 : Blo 2289435 45239915 := bstep (se 1 (by rfl) ⟨33929936, by rfl⟩ : syracuseStep 45239915 = 67859873) B67859873
theorem B120639773 : Blo 2289435 120639773 := bstep (se 3 (by rfl) ⟨22619957, by rfl⟩ : syracuseStep 120639773 = 45239915) B45239915
theorem B80426515 : Blo 2289435 80426515 := bstep (se 1 (by rfl) ⟨60319886, by rfl⟩ : syracuseStep 80426515 = 120639773) B120639773
theorem B107235353 : Blo 2289435 107235353 := bstep (se 2 (by rfl) ⟨40213257, by rfl⟩ : syracuseStep 107235353 = 80426515) B80426515
theorem B71490235 : Blo 2289435 71490235 := bstep (se 1 (by rfl) ⟨53617676, by rfl⟩ : syracuseStep 71490235 = 107235353) B107235353
theorem B95320313 : Blo 2289435 95320313 := bstep (se 2 (by rfl) ⟨35745117, by rfl⟩ : syracuseStep 95320313 = 71490235) B71490235
theorem B63546875 : Blo 2289435 63546875 := bstep (se 1 (by rfl) ⟨47660156, by rfl⟩ : syracuseStep 63546875 = 95320313) B95320313
theorem B42364583 : Blo 2289435 42364583 := bstep (se 1 (by rfl) ⟨31773437, by rfl⟩ : syracuseStep 42364583 = 63546875) B63546875
theorem B28243055 : Blo 2289435 28243055 := bstep (se 1 (by rfl) ⟨21182291, by rfl⟩ : syracuseStep 28243055 = 42364583) B42364583
theorem B18828703 : Blo 2289435 18828703 := bstep (se 1 (by rfl) ⟨14121527, by rfl⟩ : syracuseStep 18828703 = 28243055) B28243055
theorem B100419749 : Blo 2289435 100419749 := bstep (se 4 (by rfl) ⟨9414351, by rfl⟩ : syracuseStep 100419749 = 18828703) B18828703
theorem B66946499 : Blo 2289435 66946499 := bstep (se 1 (by rfl) ⟨50209874, by rfl⟩ : syracuseStep 66946499 = 100419749) B100419749
theorem B44630999 : Blo 2289435 44630999 := bstep (se 1 (by rfl) ⟨33473249, by rfl⟩ : syracuseStep 44630999 = 66946499) B66946499
theorem B29753999 : Blo 2289435 29753999 := bstep (se 1 (by rfl) ⟨22315499, by rfl⟩ : syracuseStep 29753999 = 44630999) B44630999
theorem B19835999 : Blo 2289435 19835999 := bstep (se 1 (by rfl) ⟨14876999, by rfl⟩ : syracuseStep 19835999 = 29753999) B29753999
theorem B13223999 : Blo 2289435 13223999 := bstep (se 1 (by rfl) ⟨9917999, by rfl⟩ : syracuseStep 13223999 = 19835999) B19835999
theorem B8815999 : Blo 2289435 8815999 := bstep (se 1 (by rfl) ⟨6611999, by rfl⟩ : syracuseStep 8815999 = 13223999) B13223999
theorem B11754665 : Blo 2289435 11754665 := bstep (se 2 (by rfl) ⟨4407999, by rfl⟩ : syracuseStep 11754665 = 8815999) B8815999
theorem B7836443 : Blo 2289435 7836443 := bstep (se 1 (by rfl) ⟨5877332, by rfl⟩ : syracuseStep 7836443 = 11754665) B11754665
theorem B5224295 : Blo 2289435 5224295 := bstep (se 1 (by rfl) ⟨3918221, by rfl⟩ : syracuseStep 5224295 = 7836443) B7836443
theorem B13931453 : Blo 2289435 13931453 := bstep (se 3 (by rfl) ⟨2612147, by rfl⟩ : syracuseStep 13931453 = 5224295) B5224295
theorem B9287635 : Blo 2289435 9287635 := bstep (se 1 (by rfl) ⟨6965726, by rfl⟩ : syracuseStep 9287635 = 13931453) B13931453
theorem B12383513 : Blo 2289435 12383513 := bstep (se 2 (by rfl) ⟨4643817, by rfl⟩ : syracuseStep 12383513 = 9287635) B9287635
theorem B8255675 : Blo 2289435 8255675 := bstep (se 1 (by rfl) ⟨6191756, by rfl⟩ : syracuseStep 8255675 = 12383513) B12383513
theorem B5503783 : Blo 2289435 5503783 := bstep (se 1 (by rfl) ⟨4127837, by rfl⟩ : syracuseStep 5503783 = 8255675) B8255675
theorem B7338377 : Blo 2289435 7338377 := bstep (se 2 (by rfl) ⟨2751891, by rfl⟩ : syracuseStep 7338377 = 5503783) B5503783
theorem B4892251 : Blo 2289435 4892251 := bstep (se 1 (by rfl) ⟨3669188, by rfl⟩ : syracuseStep 4892251 = 7338377) B7338377
theorem B6523001 : Blo 2289435 6523001 := bstep (se 2 (by rfl) ⟨2446125, by rfl⟩ : syracuseStep 6523001 = 4892251) B4892251
theorem B4348667 : Blo 2289435 4348667 := bstep (se 1 (by rfl) ⟨3261500, by rfl⟩ : syracuseStep 4348667 = 6523001) B6523001
theorem B11596445 : Blo 2289435 11596445 := bstep (se 3 (by rfl) ⟨2174333, by rfl⟩ : syracuseStep 11596445 = 4348667) B4348667
theorem B7730963 : Blo 2289435 7730963 := bstep (se 1 (by rfl) ⟨5798222, by rfl⟩ : syracuseStep 7730963 = 11596445) B11596445
theorem B5153975 : Blo 2289435 5153975 := bstep (se 1 (by rfl) ⟨3865481, by rfl⟩ : syracuseStep 5153975 = 7730963) B7730963
theorem B3435983 : Blo 2289435 3435983 := bstep (se 1 (by rfl) ⟨2576987, by rfl⟩ : syracuseStep 3435983 = 5153975) B5153975
theorem B2290655 : Blo 2289435 2290655 := bstep (se 1 (by rfl) ⟨1717991, by rfl⟩ : syracuseStep 2290655 = 3435983) B3435983
theorem B3435989 : Blo 2289435 3435989 := bbase (se 7 (by rfl) ⟨40265, by rfl⟩ : syracuseStep 3435989 = 80531) (by norm_num)
theorem B2290659 : Blo 2289435 2290659 := bstep (se 1 (by rfl) ⟨1717994, by rfl⟩ : syracuseStep 2290659 = 3435989) B3435989
theorem B8697365 : Blo 2289435 8697365 := bbase (se 6 (by rfl) ⟨203844, by rfl⟩ : syracuseStep 8697365 = 407689) (by norm_num)
theorem B5798243 : Blo 2289435 5798243 := bstep (se 1 (by rfl) ⟨4348682, by rfl⟩ : syracuseStep 5798243 = 8697365) B8697365
theorem B3865495 : Blo 2289435 3865495 := bstep (se 1 (by rfl) ⟨2899121, by rfl⟩ : syracuseStep 3865495 = 5798243) B5798243
theorem B5153993 : Blo 2289435 5153993 := bstep (se 2 (by rfl) ⟨1932747, by rfl⟩ : syracuseStep 5153993 = 3865495) B3865495
theorem B3435995 : Blo 2289435 3435995 := bstep (se 1 (by rfl) ⟨2576996, by rfl⟩ : syracuseStep 3435995 = 5153993) B5153993
theorem B2290663 : Blo 2289435 2290663 := bstep (se 1 (by rfl) ⟨1717997, by rfl⟩ : syracuseStep 2290663 = 3435995) B3435995
theorem B2577001 : Blo 2289435 2577001 := bbase (se 2 (by rfl) ⟨966375, by rfl⟩ : syracuseStep 2577001 = 1932751) (by norm_num)
theorem B3436001 : Blo 2289435 3436001 := bstep (se 2 (by rfl) ⟨1288500, by rfl⟩ : syracuseStep 3436001 = 2577001) B2577001
theorem B2290667 : Blo 2289435 2290667 := bstep (se 1 (by rfl) ⟨1718000, by rfl⟩ : syracuseStep 2290667 = 3436001) B3436001
theorem B4892285 : Blo 2289435 4892285 := bbase (se 3 (by rfl) ⟨917303, by rfl⟩ : syracuseStep 4892285 = 1834607) (by norm_num)
theorem B13046093 : Blo 2289435 13046093 := bstep (se 3 (by rfl) ⟨2446142, by rfl⟩ : syracuseStep 13046093 = 4892285) B4892285
theorem B8697395 : Blo 2289435 8697395 := bstep (se 1 (by rfl) ⟨6523046, by rfl⟩ : syracuseStep 8697395 = 13046093) B13046093
theorem B5798263 : Blo 2289435 5798263 := bstep (se 1 (by rfl) ⟨4348697, by rfl⟩ : syracuseStep 5798263 = 8697395) B8697395
theorem B7731017 : Blo 2289435 7731017 := bstep (se 2 (by rfl) ⟨2899131, by rfl⟩ : syracuseStep 7731017 = 5798263) B5798263
theorem B5154011 : Blo 2289435 5154011 := bstep (se 1 (by rfl) ⟨3865508, by rfl⟩ : syracuseStep 5154011 = 7731017) B7731017
theorem B3436007 : Blo 2289435 3436007 := bstep (se 1 (by rfl) ⟨2577005, by rfl⟩ : syracuseStep 3436007 = 5154011) B5154011
theorem B2290671 : Blo 2289435 2290671 := bstep (se 1 (by rfl) ⟨1718003, by rfl⟩ : syracuseStep 2290671 = 3436007) B3436007
theorem B3436013 : Blo 2289435 3436013 := bbase (se 3 (by rfl) ⟨644252, by rfl⟩ : syracuseStep 3436013 = 1288505) (by norm_num)
theorem B2290675 : Blo 2289435 2290675 := bstep (se 1 (by rfl) ⟨1718006, by rfl⟩ : syracuseStep 2290675 = 3436013) B3436013
theorem B5154029 : Blo 2289435 5154029 := bbase (se 3 (by rfl) ⟨966380, by rfl⟩ : syracuseStep 5154029 = 1932761) (by norm_num)
theorem B3436019 : Blo 2289435 3436019 := bstep (se 1 (by rfl) ⟨2577014, by rfl⟩ : syracuseStep 3436019 = 5154029) B5154029
theorem B2290679 : Blo 2289435 2290679 := bstep (se 1 (by rfl) ⟨1718009, by rfl⟩ : syracuseStep 2290679 = 3436019) B3436019
theorem B3261541 : Blo 2289435 3261541 := bbase (se 4 (by rfl) ⟨305769, by rfl⟩ : syracuseStep 3261541 = 611539) (by norm_num)
theorem B4348721 : Blo 2289435 4348721 := bstep (se 2 (by rfl) ⟨1630770, by rfl⟩ : syracuseStep 4348721 = 3261541) B3261541
theorem B2899147 : Blo 2289435 2899147 := bstep (se 1 (by rfl) ⟨2174360, by rfl⟩ : syracuseStep 2899147 = 4348721) B4348721
theorem B3865529 : Blo 2289435 3865529 := bstep (se 2 (by rfl) ⟨1449573, by rfl⟩ : syracuseStep 3865529 = 2899147) B2899147
theorem B2577019 : Blo 2289435 2577019 := bstep (se 1 (by rfl) ⟨1932764, by rfl⟩ : syracuseStep 2577019 = 3865529) B3865529
theorem B3436025 : Blo 2289435 3436025 := bstep (se 2 (by rfl) ⟨1288509, by rfl⟩ : syracuseStep 3436025 = 2577019) B2577019
theorem B2290683 : Blo 2289435 2290683 := bstep (se 1 (by rfl) ⟨1718012, by rfl⟩ : syracuseStep 2290683 = 3436025) B3436025
theorem B13224181 : Blo 2289435 13224181 := bbase (se 5 (by rfl) ⟨619883, by rfl⟩ : syracuseStep 13224181 = 1239767) (by norm_num)
theorem B17632241 : Blo 2289435 17632241 := bstep (se 2 (by rfl) ⟨6612090, by rfl⟩ : syracuseStep 17632241 = 13224181) B13224181
theorem B11754827 : Blo 2289435 11754827 := bstep (se 1 (by rfl) ⟨8816120, by rfl⟩ : syracuseStep 11754827 = 17632241) B17632241
theorem B7836551 : Blo 2289435 7836551 := bstep (se 1 (by rfl) ⟨5877413, by rfl⟩ : syracuseStep 7836551 = 11754827) B11754827
theorem B5224367 : Blo 2289435 5224367 := bstep (se 1 (by rfl) ⟨3918275, by rfl⟩ : syracuseStep 5224367 = 7836551) B7836551
theorem B3482911 : Blo 2289435 3482911 := bstep (se 1 (by rfl) ⟨2612183, by rfl⟩ : syracuseStep 3482911 = 5224367) B5224367
theorem B4643881 : Blo 2289435 4643881 := bstep (se 2 (by rfl) ⟨1741455, by rfl⟩ : syracuseStep 4643881 = 3482911) B3482911
theorem B24767365 : Blo 2289435 24767365 := bstep (se 4 (by rfl) ⟨2321940, by rfl⟩ : syracuseStep 24767365 = 4643881) B4643881
theorem B33023153 : Blo 2289435 33023153 := bstep (se 2 (by rfl) ⟨12383682, by rfl⟩ : syracuseStep 33023153 = 24767365) B24767365
theorem B88061741 : Blo 2289435 88061741 := bstep (se 3 (by rfl) ⟨16511576, by rfl⟩ : syracuseStep 88061741 = 33023153) B33023153
theorem B58707827 : Blo 2289435 58707827 := bstep (se 1 (by rfl) ⟨44030870, by rfl⟩ : syracuseStep 58707827 = 88061741) B88061741
theorem B39138551 : Blo 2289435 39138551 := bstep (se 1 (by rfl) ⟨29353913, by rfl⟩ : syracuseStep 39138551 = 58707827) B58707827
theorem B26092367 : Blo 2289435 26092367 := bstep (se 1 (by rfl) ⟨19569275, by rfl⟩ : syracuseStep 26092367 = 39138551) B39138551
theorem B17394911 : Blo 2289435 17394911 := bstep (se 1 (by rfl) ⟨13046183, by rfl⟩ : syracuseStep 17394911 = 26092367) B26092367
theorem B11596607 : Blo 2289435 11596607 := bstep (se 1 (by rfl) ⟨8697455, by rfl⟩ : syracuseStep 11596607 = 17394911) B17394911
theorem B7731071 : Blo 2289435 7731071 := bstep (se 1 (by rfl) ⟨5798303, by rfl⟩ : syracuseStep 7731071 = 11596607) B11596607
theorem B5154047 : Blo 2289435 5154047 := bstep (se 1 (by rfl) ⟨3865535, by rfl⟩ : syracuseStep 5154047 = 7731071) B7731071
theorem B3436031 : Blo 2289435 3436031 := bstep (se 1 (by rfl) ⟨2577023, by rfl⟩ : syracuseStep 3436031 = 5154047) B5154047
theorem B2290687 : Blo 2289435 2290687 := bstep (se 1 (by rfl) ⟨1718015, by rfl⟩ : syracuseStep 2290687 = 3436031) B3436031
theorem B3436037 : Blo 2289435 3436037 := bbase (se 4 (by rfl) ⟨322128, by rfl⟩ : syracuseStep 3436037 = 644257) (by norm_num)
theorem B2290691 : Blo 2289435 2290691 := bstep (se 1 (by rfl) ⟨1718018, by rfl⟩ : syracuseStep 2290691 = 3436037) B3436037
theorem B3865549 : Blo 2289435 3865549 := bbase (se 3 (by rfl) ⟨724790, by rfl⟩ : syracuseStep 3865549 = 1449581) (by norm_num)
theorem B5154065 : Blo 2289435 5154065 := bstep (se 2 (by rfl) ⟨1932774, by rfl⟩ : syracuseStep 5154065 = 3865549) B3865549
theorem B3436043 : Blo 2289435 3436043 := bstep (se 1 (by rfl) ⟨2577032, by rfl⟩ : syracuseStep 3436043 = 5154065) B5154065
theorem B2290695 : Blo 2289435 2290695 := bstep (se 1 (by rfl) ⟨1718021, by rfl⟩ : syracuseStep 2290695 = 3436043) B3436043
theorem B2577037 : Blo 2289435 2577037 := bbase (se 3 (by rfl) ⟨483194, by rfl⟩ : syracuseStep 2577037 = 966389) (by norm_num)
theorem B3436049 : Blo 2289435 3436049 := bstep (se 2 (by rfl) ⟨1288518, by rfl⟩ : syracuseStep 3436049 = 2577037) B2577037
theorem B2290699 : Blo 2289435 2290699 := bstep (se 1 (by rfl) ⟨1718024, by rfl⟩ : syracuseStep 2290699 = 3436049) B3436049
theorem B7731125 : Blo 2289435 7731125 := bbase (se 5 (by rfl) ⟨362396, by rfl⟩ : syracuseStep 7731125 = 724793) (by norm_num)
theorem B5154083 : Blo 2289435 5154083 := bstep (se 1 (by rfl) ⟨3865562, by rfl⟩ : syracuseStep 5154083 = 7731125) B7731125
theorem B3436055 : Blo 2289435 3436055 := bstep (se 1 (by rfl) ⟨2577041, by rfl⟩ : syracuseStep 3436055 = 5154083) B5154083
theorem B2290703 : Blo 2289435 2290703 := bstep (se 1 (by rfl) ⟨1718027, by rfl⟩ : syracuseStep 2290703 = 3436055) B3436055
theorem B3436061 : Blo 2289435 3436061 := bbase (se 3 (by rfl) ⟨644261, by rfl⟩ : syracuseStep 3436061 = 1288523) (by norm_num)
theorem B2290707 : Blo 2289435 2290707 := bstep (se 1 (by rfl) ⟨1718030, by rfl⟩ : syracuseStep 2290707 = 3436061) B3436061
theorem B5154101 : Blo 2289435 5154101 := bbase (se 5 (by rfl) ⟨241598, by rfl⟩ : syracuseStep 5154101 = 483197) (by norm_num)
theorem B3436067 : Blo 2289435 3436067 := bstep (se 1 (by rfl) ⟨2577050, by rfl⟩ : syracuseStep 3436067 = 5154101) B5154101
theorem B2290711 : Blo 2289435 2290711 := bstep (se 1 (by rfl) ⟨1718033, by rfl⟩ : syracuseStep 2290711 = 3436067) B3436067
theorem B6965909 : Blo 2289435 6965909 := bbase (se 6 (by rfl) ⟨163263, by rfl⟩ : syracuseStep 6965909 = 326527) (by norm_num)
theorem B4643939 : Blo 2289435 4643939 := bstep (se 1 (by rfl) ⟨3482954, by rfl⟩ : syracuseStep 4643939 = 6965909) B6965909
theorem B12383837 : Blo 2289435 12383837 := bstep (se 3 (by rfl) ⟨2321969, by rfl⟩ : syracuseStep 12383837 = 4643939) B4643939
theorem B8255891 : Blo 2289435 8255891 := bstep (se 1 (by rfl) ⟨6191918, by rfl⟩ : syracuseStep 8255891 = 12383837) B12383837
theorem B22015709 : Blo 2289435 22015709 := bstep (se 3 (by rfl) ⟨4127945, by rfl⟩ : syracuseStep 22015709 = 8255891) B8255891
theorem B14677139 : Blo 2289435 14677139 := bstep (se 1 (by rfl) ⟨11007854, by rfl⟩ : syracuseStep 14677139 = 22015709) B22015709
theorem B9784759 : Blo 2289435 9784759 := bstep (se 1 (by rfl) ⟨7338569, by rfl⟩ : syracuseStep 9784759 = 14677139) B14677139
theorem B13046345 : Blo 2289435 13046345 := bstep (se 2 (by rfl) ⟨4892379, by rfl⟩ : syracuseStep 13046345 = 9784759) B9784759
theorem B8697563 : Blo 2289435 8697563 := bstep (se 1 (by rfl) ⟨6523172, by rfl⟩ : syracuseStep 8697563 = 13046345) B13046345
theorem B5798375 : Blo 2289435 5798375 := bstep (se 1 (by rfl) ⟨4348781, by rfl⟩ : syracuseStep 5798375 = 8697563) B8697563
theorem B3865583 : Blo 2289435 3865583 := bstep (se 1 (by rfl) ⟨2899187, by rfl⟩ : syracuseStep 3865583 = 5798375) B5798375
theorem B2577055 : Blo 2289435 2577055 := bstep (se 1 (by rfl) ⟨1932791, by rfl⟩ : syracuseStep 2577055 = 3865583) B3865583
theorem B3436073 : Blo 2289435 3436073 := bstep (se 2 (by rfl) ⟨1288527, by rfl⟩ : syracuseStep 3436073 = 2577055) B2577055
theorem B2290715 : Blo 2289435 2290715 := bstep (se 1 (by rfl) ⟨1718036, by rfl⟩ : syracuseStep 2290715 = 3436073) B3436073
theorem B9287893 : Blo 2289435 9287893 := bbase (se 7 (by rfl) ⟨108842, by rfl⟩ : syracuseStep 9287893 = 217685) (by norm_num)
theorem B12383857 : Blo 2289435 12383857 := bstep (se 2 (by rfl) ⟨4643946, by rfl⟩ : syracuseStep 12383857 = 9287893) B9287893
theorem B16511809 : Blo 2289435 16511809 := bstep (se 2 (by rfl) ⟨6191928, by rfl⟩ : syracuseStep 16511809 = 12383857) B12383857
theorem B22015745 : Blo 2289435 22015745 := bstep (se 2 (by rfl) ⟨8255904, by rfl⟩ : syracuseStep 22015745 = 16511809) B16511809
theorem B14677163 : Blo 2289435 14677163 := bstep (se 1 (by rfl) ⟨11007872, by rfl⟩ : syracuseStep 14677163 = 22015745) B22015745
theorem B9784775 : Blo 2289435 9784775 := bstep (se 1 (by rfl) ⟨7338581, by rfl⟩ : syracuseStep 9784775 = 14677163) B14677163
theorem B6523183 : Blo 2289435 6523183 := bstep (se 1 (by rfl) ⟨4892387, by rfl⟩ : syracuseStep 6523183 = 9784775) B9784775
theorem B8697577 : Blo 2289435 8697577 := bstep (se 2 (by rfl) ⟨3261591, by rfl⟩ : syracuseStep 8697577 = 6523183) B6523183
theorem B11596769 : Blo 2289435 11596769 := bstep (se 2 (by rfl) ⟨4348788, by rfl⟩ : syracuseStep 11596769 = 8697577) B8697577
theorem B7731179 : Blo 2289435 7731179 := bstep (se 1 (by rfl) ⟨5798384, by rfl⟩ : syracuseStep 7731179 = 11596769) B11596769
theorem B5154119 : Blo 2289435 5154119 := bstep (se 1 (by rfl) ⟨3865589, by rfl⟩ : syracuseStep 5154119 = 7731179) B7731179
theorem B3436079 : Blo 2289435 3436079 := bstep (se 1 (by rfl) ⟨2577059, by rfl⟩ : syracuseStep 3436079 = 5154119) B5154119
theorem B2290719 : Blo 2289435 2290719 := bstep (se 1 (by rfl) ⟨1718039, by rfl⟩ : syracuseStep 2290719 = 3436079) B3436079
theorem B3436085 : Blo 2289435 3436085 := bbase (se 5 (by rfl) ⟨161066, by rfl⟩ : syracuseStep 3436085 = 322133) (by norm_num)
theorem B2290723 : Blo 2289435 2290723 := bstep (se 1 (by rfl) ⟨1718042, by rfl⟩ : syracuseStep 2290723 = 3436085) B3436085
theorem B5798405 : Blo 2289435 5798405 := bbase (se 4 (by rfl) ⟨543600, by rfl⟩ : syracuseStep 5798405 = 1087201) (by norm_num)
theorem B3865603 : Blo 2289435 3865603 := bstep (se 1 (by rfl) ⟨2899202, by rfl⟩ : syracuseStep 3865603 = 5798405) B5798405
theorem B5154137 : Blo 2289435 5154137 := bstep (se 2 (by rfl) ⟨1932801, by rfl⟩ : syracuseStep 5154137 = 3865603) B3865603
theorem B3436091 : Blo 2289435 3436091 := bstep (se 1 (by rfl) ⟨2577068, by rfl⟩ : syracuseStep 3436091 = 5154137) B5154137
theorem B2290727 : Blo 2289435 2290727 := bstep (se 1 (by rfl) ⟨1718045, by rfl⟩ : syracuseStep 2290727 = 3436091) B3436091
theorem B2577073 : Blo 2289435 2577073 := bbase (se 2 (by rfl) ⟨966402, by rfl⟩ : syracuseStep 2577073 = 1932805) (by norm_num)
theorem B3436097 : Blo 2289435 3436097 := bstep (se 2 (by rfl) ⟨1288536, by rfl⟩ : syracuseStep 3436097 = 2577073) B2577073
theorem B2290731 : Blo 2289435 2290731 := bstep (se 1 (by rfl) ⟨1718048, by rfl⟩ : syracuseStep 2290731 = 3436097) B3436097
theorem B3669317 : Blo 2289435 3669317 := bbase (se 4 (by rfl) ⟨343998, by rfl⟩ : syracuseStep 3669317 = 687997) (by norm_num)
theorem B2446211 : Blo 2289435 2446211 := bstep (se 1 (by rfl) ⟨1834658, by rfl⟩ : syracuseStep 2446211 = 3669317) B3669317
theorem B6523229 : Blo 2289435 6523229 := bstep (se 3 (by rfl) ⟨1223105, by rfl⟩ : syracuseStep 6523229 = 2446211) B2446211
theorem B4348819 : Blo 2289435 4348819 := bstep (se 1 (by rfl) ⟨3261614, by rfl⟩ : syracuseStep 4348819 = 6523229) B6523229
theorem B5798425 : Blo 2289435 5798425 := bstep (se 2 (by rfl) ⟨2174409, by rfl⟩ : syracuseStep 5798425 = 4348819) B4348819
theorem B7731233 : Blo 2289435 7731233 := bstep (se 2 (by rfl) ⟨2899212, by rfl⟩ : syracuseStep 7731233 = 5798425) B5798425
theorem B5154155 : Blo 2289435 5154155 := bstep (se 1 (by rfl) ⟨3865616, by rfl⟩ : syracuseStep 5154155 = 7731233) B7731233
theorem B3436103 : Blo 2289435 3436103 := bstep (se 1 (by rfl) ⟨2577077, by rfl⟩ : syracuseStep 3436103 = 5154155) B5154155
theorem B2290735 : Blo 2289435 2290735 := bstep (se 1 (by rfl) ⟨1718051, by rfl⟩ : syracuseStep 2290735 = 3436103) B3436103
theorem B3436109 : Blo 2289435 3436109 := bbase (se 3 (by rfl) ⟨644270, by rfl⟩ : syracuseStep 3436109 = 1288541) (by norm_num)
theorem B2290739 : Blo 2289435 2290739 := bstep (se 1 (by rfl) ⟨1718054, by rfl⟩ : syracuseStep 2290739 = 3436109) B3436109
theorem B5154173 : Blo 2289435 5154173 := bbase (se 3 (by rfl) ⟨966407, by rfl⟩ : syracuseStep 5154173 = 1932815) (by norm_num)
theorem B3436115 : Blo 2289435 3436115 := bstep (se 1 (by rfl) ⟨2577086, by rfl⟩ : syracuseStep 3436115 = 5154173) B5154173
theorem B2290743 : Blo 2289435 2290743 := bstep (se 1 (by rfl) ⟨1718057, by rfl⟩ : syracuseStep 2290743 = 3436115) B3436115
theorem B3865637 : Blo 2289435 3865637 := bbase (se 4 (by rfl) ⟨362403, by rfl⟩ : syracuseStep 3865637 = 724807) (by norm_num)
theorem B2577091 : Blo 2289435 2577091 := bstep (se 1 (by rfl) ⟨1932818, by rfl⟩ : syracuseStep 2577091 = 3865637) B3865637
theorem B3436121 : Blo 2289435 3436121 := bstep (se 2 (by rfl) ⟨1288545, by rfl⟩ : syracuseStep 3436121 = 2577091) B2577091
theorem B2290747 : Blo 2289435 2290747 := bstep (se 1 (by rfl) ⟨1718060, by rfl⟩ : syracuseStep 2290747 = 3436121) B3436121
theorem B3261637 : Blo 2289435 3261637 := bbase (se 4 (by rfl) ⟨305778, by rfl⟩ : syracuseStep 3261637 = 611557) (by norm_num)
theorem B17395397 : Blo 2289435 17395397 := bstep (se 4 (by rfl) ⟨1630818, by rfl⟩ : syracuseStep 17395397 = 3261637) B3261637
theorem B11596931 : Blo 2289435 11596931 := bstep (se 1 (by rfl) ⟨8697698, by rfl⟩ : syracuseStep 11596931 = 17395397) B17395397
theorem B7731287 : Blo 2289435 7731287 := bstep (se 1 (by rfl) ⟨5798465, by rfl⟩ : syracuseStep 7731287 = 11596931) B11596931
theorem B5154191 : Blo 2289435 5154191 := bstep (se 1 (by rfl) ⟨3865643, by rfl⟩ : syracuseStep 5154191 = 7731287) B7731287
theorem B3436127 : Blo 2289435 3436127 := bstep (se 1 (by rfl) ⟨2577095, by rfl⟩ : syracuseStep 3436127 = 5154191) B5154191
theorem B2290751 : Blo 2289435 2290751 := bstep (se 1 (by rfl) ⟨1718063, by rfl⟩ : syracuseStep 2290751 = 3436127) B3436127
theorem B3436133 : Blo 2289435 3436133 := bbase (se 4 (by rfl) ⟨322137, by rfl⟩ : syracuseStep 3436133 = 644275) (by norm_num)
theorem B2290755 : Blo 2289435 2290755 := bstep (se 1 (by rfl) ⟨1718066, by rfl⟩ : syracuseStep 2290755 = 3436133) B3436133
theorem B2446237 : Blo 2289435 2446237 := bbase (se 3 (by rfl) ⟨458669, by rfl⟩ : syracuseStep 2446237 = 917339) (by norm_num)
theorem B3261649 : Blo 2289435 3261649 := bstep (se 2 (by rfl) ⟨1223118, by rfl⟩ : syracuseStep 3261649 = 2446237) B2446237
theorem B4348865 : Blo 2289435 4348865 := bstep (se 2 (by rfl) ⟨1630824, by rfl⟩ : syracuseStep 4348865 = 3261649) B3261649
theorem B2899243 : Blo 2289435 2899243 := bstep (se 1 (by rfl) ⟨2174432, by rfl⟩ : syracuseStep 2899243 = 4348865) B4348865
theorem B3865657 : Blo 2289435 3865657 := bstep (se 2 (by rfl) ⟨1449621, by rfl⟩ : syracuseStep 3865657 = 2899243) B2899243
theorem B5154209 : Blo 2289435 5154209 := bstep (se 2 (by rfl) ⟨1932828, by rfl⟩ : syracuseStep 5154209 = 3865657) B3865657
theorem B3436139 : Blo 2289435 3436139 := bstep (se 1 (by rfl) ⟨2577104, by rfl⟩ : syracuseStep 3436139 = 5154209) B5154209
theorem B2290759 : Blo 2289435 2290759 := bstep (se 1 (by rfl) ⟨1718069, by rfl⟩ : syracuseStep 2290759 = 3436139) B3436139
theorem B2577109 : Blo 2289435 2577109 := bbase (se 7 (by rfl) ⟨30200, by rfl⟩ : syracuseStep 2577109 = 60401) (by norm_num)
theorem B3436145 : Blo 2289435 3436145 := bstep (se 2 (by rfl) ⟨1288554, by rfl⟩ : syracuseStep 3436145 = 2577109) B2577109
theorem B2290763 : Blo 2289435 2290763 := bstep (se 1 (by rfl) ⟨1718072, by rfl⟩ : syracuseStep 2290763 = 3436145) B3436145
theorem B2899253 : Blo 2289435 2899253 := bbase (se 5 (by rfl) ⟨135902, by rfl⟩ : syracuseStep 2899253 = 271805) (by norm_num)
theorem B7731341 : Blo 2289435 7731341 := bstep (se 3 (by rfl) ⟨1449626, by rfl⟩ : syracuseStep 7731341 = 2899253) B2899253
theorem B5154227 : Blo 2289435 5154227 := bstep (se 1 (by rfl) ⟨3865670, by rfl⟩ : syracuseStep 5154227 = 7731341) B7731341
theorem B3436151 : Blo 2289435 3436151 := bstep (se 1 (by rfl) ⟨2577113, by rfl⟩ : syracuseStep 3436151 = 5154227) B5154227
theorem B2290767 : Blo 2289435 2290767 := bstep (se 1 (by rfl) ⟨1718075, by rfl⟩ : syracuseStep 2290767 = 3436151) B3436151
theorem B3436157 : Blo 2289435 3436157 := bbase (se 3 (by rfl) ⟨644279, by rfl⟩ : syracuseStep 3436157 = 1288559) (by norm_num)
theorem B2290771 : Blo 2289435 2290771 := bstep (se 1 (by rfl) ⟨1718078, by rfl⟩ : syracuseStep 2290771 = 3436157) B3436157
theorem B5154245 : Blo 2289435 5154245 := bbase (se 4 (by rfl) ⟨483210, by rfl⟩ : syracuseStep 5154245 = 966421) (by norm_num)
theorem B3436163 : Blo 2289435 3436163 := bstep (se 1 (by rfl) ⟨2577122, by rfl⟩ : syracuseStep 3436163 = 5154245) B5154245
theorem B2290775 : Blo 2289435 2290775 := bstep (se 1 (by rfl) ⟨1718081, by rfl⟩ : syracuseStep 2290775 = 3436163) B3436163
theorem B16512245 : Blo 2289435 16512245 := bbase (se 5 (by rfl) ⟨774011, by rfl⟩ : syracuseStep 16512245 = 1548023) (by norm_num)
theorem B11008163 : Blo 2289435 11008163 := bstep (se 1 (by rfl) ⟨8256122, by rfl⟩ : syracuseStep 11008163 = 16512245) B16512245
theorem B7338775 : Blo 2289435 7338775 := bstep (se 1 (by rfl) ⟨5504081, by rfl⟩ : syracuseStep 7338775 = 11008163) B11008163
theorem B9785033 : Blo 2289435 9785033 := bstep (se 2 (by rfl) ⟨3669387, by rfl⟩ : syracuseStep 9785033 = 7338775) B7338775
theorem B6523355 : Blo 2289435 6523355 := bstep (se 1 (by rfl) ⟨4892516, by rfl⟩ : syracuseStep 6523355 = 9785033) B9785033
theorem B4348903 : Blo 2289435 4348903 := bstep (se 1 (by rfl) ⟨3261677, by rfl⟩ : syracuseStep 4348903 = 6523355) B6523355
theorem B5798537 : Blo 2289435 5798537 := bstep (se 2 (by rfl) ⟨2174451, by rfl⟩ : syracuseStep 5798537 = 4348903) B4348903
theorem B3865691 : Blo 2289435 3865691 := bstep (se 1 (by rfl) ⟨2899268, by rfl⟩ : syracuseStep 3865691 = 5798537) B5798537
theorem B2577127 : Blo 2289435 2577127 := bstep (se 1 (by rfl) ⟨1932845, by rfl⟩ : syracuseStep 2577127 = 3865691) B3865691
theorem B3436169 : Blo 2289435 3436169 := bstep (se 2 (by rfl) ⟨1288563, by rfl⟩ : syracuseStep 3436169 = 2577127) B2577127
theorem B2290779 : Blo 2289435 2290779 := bstep (se 1 (by rfl) ⟨1718084, by rfl⟩ : syracuseStep 2290779 = 3436169) B3436169
theorem B11597093 : Blo 2289435 11597093 := bbase (se 4 (by rfl) ⟨1087227, by rfl⟩ : syracuseStep 11597093 = 2174455) (by norm_num)
theorem B7731395 : Blo 2289435 7731395 := bstep (se 1 (by rfl) ⟨5798546, by rfl⟩ : syracuseStep 7731395 = 11597093) B11597093
theorem B5154263 : Blo 2289435 5154263 := bstep (se 1 (by rfl) ⟨3865697, by rfl⟩ : syracuseStep 5154263 = 7731395) B7731395
theorem B3436175 : Blo 2289435 3436175 := bstep (se 1 (by rfl) ⟨2577131, by rfl⟩ : syracuseStep 3436175 = 5154263) B5154263
theorem B2290783 : Blo 2289435 2290783 := bstep (se 1 (by rfl) ⟨1718087, by rfl⟩ : syracuseStep 2290783 = 3436175) B3436175
theorem B3436181 : Blo 2289435 3436181 := bbase (se 6 (by rfl) ⟨80535, by rfl⟩ : syracuseStep 3436181 = 161071) (by norm_num)
theorem B2290787 : Blo 2289435 2290787 := bstep (se 1 (by rfl) ⟨1718090, by rfl⟩ : syracuseStep 2290787 = 3436181) B3436181
theorem B4299365 : Blo 2289435 4299365 := bbase (se 4 (by rfl) ⟨403065, by rfl⟩ : syracuseStep 4299365 = 806131) (by norm_num)
theorem B11464973 : Blo 2289435 11464973 := bstep (se 3 (by rfl) ⟨2149682, by rfl⟩ : syracuseStep 11464973 = 4299365) B4299365
theorem B7643315 : Blo 2289435 7643315 := bstep (se 1 (by rfl) ⟨5732486, by rfl⟩ : syracuseStep 7643315 = 11464973) B11464973
theorem B5095543 : Blo 2289435 5095543 := bstep (se 1 (by rfl) ⟨3821657, by rfl⟩ : syracuseStep 5095543 = 7643315) B7643315
theorem B6794057 : Blo 2289435 6794057 := bstep (se 2 (by rfl) ⟨2547771, by rfl⟩ : syracuseStep 6794057 = 5095543) B5095543
theorem B4529371 : Blo 2289435 4529371 := bstep (se 1 (by rfl) ⟨3397028, by rfl⟩ : syracuseStep 4529371 = 6794057) B6794057
theorem B6039161 : Blo 2289435 6039161 := bstep (se 2 (by rfl) ⟨2264685, by rfl⟩ : syracuseStep 6039161 = 4529371) B4529371
theorem B4026107 : Blo 2289435 4026107 := bstep (se 1 (by rfl) ⟨3019580, by rfl⟩ : syracuseStep 4026107 = 6039161) B6039161
theorem B2684071 : Blo 2289435 2684071 := bstep (se 1 (by rfl) ⟨2013053, by rfl⟩ : syracuseStep 2684071 = 4026107) B4026107
theorem B3578761 : Blo 2289435 3578761 := bstep (se 2 (by rfl) ⟨1342035, by rfl⟩ : syracuseStep 3578761 = 2684071) B2684071
theorem B19086725 : Blo 2289435 19086725 := bstep (se 4 (by rfl) ⟨1789380, by rfl⟩ : syracuseStep 19086725 = 3578761) B3578761
theorem B50897933 : Blo 2289435 50897933 := bstep (se 3 (by rfl) ⟨9543362, by rfl⟩ : syracuseStep 50897933 = 19086725) B19086725
theorem B33931955 : Blo 2289435 33931955 := bstep (se 1 (by rfl) ⟨25448966, by rfl⟩ : syracuseStep 33931955 = 50897933) B50897933
theorem B22621303 : Blo 2289435 22621303 := bstep (se 1 (by rfl) ⟨16965977, by rfl⟩ : syracuseStep 22621303 = 33931955) B33931955
theorem B30161737 : Blo 2289435 30161737 := bstep (se 2 (by rfl) ⟨11310651, by rfl⟩ : syracuseStep 30161737 = 22621303) B22621303
theorem B40215649 : Blo 2289435 40215649 := bstep (se 2 (by rfl) ⟨15080868, by rfl⟩ : syracuseStep 40215649 = 30161737) B30161737
theorem B53620865 : Blo 2289435 53620865 := bstep (se 2 (by rfl) ⟨20107824, by rfl⟩ : syracuseStep 53620865 = 40215649) B40215649
theorem B35747243 : Blo 2289435 35747243 := bstep (se 1 (by rfl) ⟨26810432, by rfl⟩ : syracuseStep 35747243 = 53620865) B53620865
theorem B23831495 : Blo 2289435 23831495 := bstep (se 1 (by rfl) ⟨17873621, by rfl⟩ : syracuseStep 23831495 = 35747243) B35747243
theorem B15887663 : Blo 2289435 15887663 := bstep (se 1 (by rfl) ⟨11915747, by rfl⟩ : syracuseStep 15887663 = 23831495) B23831495
theorem B10591775 : Blo 2289435 10591775 := bstep (se 1 (by rfl) ⟨7943831, by rfl⟩ : syracuseStep 10591775 = 15887663) B15887663
theorem B7061183 : Blo 2289435 7061183 := bstep (se 1 (by rfl) ⟨5295887, by rfl⟩ : syracuseStep 7061183 = 10591775) B10591775
theorem B4707455 : Blo 2289435 4707455 := bstep (se 1 (by rfl) ⟨3530591, by rfl⟩ : syracuseStep 4707455 = 7061183) B7061183
theorem B12553213 : Blo 2289435 12553213 := bstep (se 3 (by rfl) ⟨2353727, by rfl⟩ : syracuseStep 12553213 = 4707455) B4707455
theorem B16737617 : Blo 2289435 16737617 := bstep (se 2 (by rfl) ⟨6276606, by rfl⟩ : syracuseStep 16737617 = 12553213) B12553213
theorem B11158411 : Blo 2289435 11158411 := bstep (se 1 (by rfl) ⟨8368808, by rfl⟩ : syracuseStep 11158411 = 16737617) B16737617
theorem B14877881 : Blo 2289435 14877881 := bstep (se 2 (by rfl) ⟨5579205, by rfl⟩ : syracuseStep 14877881 = 11158411) B11158411
theorem B9918587 : Blo 2289435 9918587 := bstep (se 1 (by rfl) ⟨7438940, by rfl⟩ : syracuseStep 9918587 = 14877881) B14877881
theorem B6612391 : Blo 2289435 6612391 := bstep (se 1 (by rfl) ⟨4959293, by rfl⟩ : syracuseStep 6612391 = 9918587) B9918587
theorem B8816521 : Blo 2289435 8816521 := bstep (se 2 (by rfl) ⟨3306195, by rfl⟩ : syracuseStep 8816521 = 6612391) B6612391
theorem B11755361 : Blo 2289435 11755361 := bstep (se 2 (by rfl) ⟨4408260, by rfl⟩ : syracuseStep 11755361 = 8816521) B8816521
theorem B7836907 : Blo 2289435 7836907 := bstep (se 1 (by rfl) ⟨5877680, by rfl⟩ : syracuseStep 7836907 = 11755361) B11755361
theorem B10449209 : Blo 2289435 10449209 := bstep (se 2 (by rfl) ⟨3918453, by rfl⟩ : syracuseStep 10449209 = 7836907) B7836907
theorem B27864557 : Blo 2289435 27864557 := bstep (se 3 (by rfl) ⟨5224604, by rfl⟩ : syracuseStep 27864557 = 10449209) B10449209
theorem B18576371 : Blo 2289435 18576371 := bstep (se 1 (by rfl) ⟨13932278, by rfl⟩ : syracuseStep 18576371 = 27864557) B27864557
theorem B12384247 : Blo 2289435 12384247 := bstep (se 1 (by rfl) ⟨9288185, by rfl⟩ : syracuseStep 12384247 = 18576371) B18576371
theorem B16512329 : Blo 2289435 16512329 := bstep (se 2 (by rfl) ⟨6192123, by rfl⟩ : syracuseStep 16512329 = 12384247) B12384247
theorem B11008219 : Blo 2289435 11008219 := bstep (se 1 (by rfl) ⟨8256164, by rfl⟩ : syracuseStep 11008219 = 16512329) B16512329
theorem B14677625 : Blo 2289435 14677625 := bstep (se 2 (by rfl) ⟨5504109, by rfl⟩ : syracuseStep 14677625 = 11008219) B11008219
theorem B9785083 : Blo 2289435 9785083 := bstep (se 1 (by rfl) ⟨7338812, by rfl⟩ : syracuseStep 9785083 = 14677625) B14677625
theorem B13046777 : Blo 2289435 13046777 := bstep (se 2 (by rfl) ⟨4892541, by rfl⟩ : syracuseStep 13046777 = 9785083) B9785083
theorem B8697851 : Blo 2289435 8697851 := bstep (se 1 (by rfl) ⟨6523388, by rfl⟩ : syracuseStep 8697851 = 13046777) B13046777
theorem B5798567 : Blo 2289435 5798567 := bstep (se 1 (by rfl) ⟨4348925, by rfl⟩ : syracuseStep 5798567 = 8697851) B8697851
theorem B3865711 : Blo 2289435 3865711 := bstep (se 1 (by rfl) ⟨2899283, by rfl⟩ : syracuseStep 3865711 = 5798567) B5798567
theorem B5154281 : Blo 2289435 5154281 := bstep (se 2 (by rfl) ⟨1932855, by rfl⟩ : syracuseStep 5154281 = 3865711) B3865711
theorem B3436187 : Blo 2289435 3436187 := bstep (se 1 (by rfl) ⟨2577140, by rfl⟩ : syracuseStep 3436187 = 5154281) B5154281
theorem B2290791 : Blo 2289435 2290791 := bstep (se 1 (by rfl) ⟨1718093, by rfl⟩ : syracuseStep 2290791 = 3436187) B3436187
theorem B2577145 : Blo 2289435 2577145 := bbase (se 2 (by rfl) ⟨966429, by rfl⟩ : syracuseStep 2577145 = 1932859) (by norm_num)
theorem B3436193 : Blo 2289435 3436193 := bstep (se 2 (by rfl) ⟨1288572, by rfl⟩ : syracuseStep 3436193 = 2577145) B2577145
theorem B2290795 : Blo 2289435 2290795 := bstep (se 1 (by rfl) ⟨1718096, by rfl⟩ : syracuseStep 2290795 = 3436193) B3436193
theorem B3918469 : Blo 2289435 3918469 := bbase (se 4 (by rfl) ⟨367356, by rfl⟩ : syracuseStep 3918469 = 734713) (by norm_num)
theorem B5224625 : Blo 2289435 5224625 := bstep (se 2 (by rfl) ⟨1959234, by rfl⟩ : syracuseStep 5224625 = 3918469) B3918469
theorem B3483083 : Blo 2289435 3483083 := bstep (se 1 (by rfl) ⟨2612312, by rfl⟩ : syracuseStep 3483083 = 5224625) B5224625
theorem B2322055 : Blo 2289435 2322055 := bstep (se 1 (by rfl) ⟨1741541, by rfl⟩ : syracuseStep 2322055 = 3483083) B3483083
theorem B3096073 : Blo 2289435 3096073 := bstep (se 2 (by rfl) ⟨1161027, by rfl⟩ : syracuseStep 3096073 = 2322055) B2322055
theorem B4128097 : Blo 2289435 4128097 := bstep (se 2 (by rfl) ⟨1548036, by rfl⟩ : syracuseStep 4128097 = 3096073) B3096073
theorem B5504129 : Blo 2289435 5504129 := bstep (se 2 (by rfl) ⟨2064048, by rfl⟩ : syracuseStep 5504129 = 4128097) B4128097
theorem B3669419 : Blo 2289435 3669419 := bstep (se 1 (by rfl) ⟨2752064, by rfl⟩ : syracuseStep 3669419 = 5504129) B5504129
theorem B9785117 : Blo 2289435 9785117 := bstep (se 3 (by rfl) ⟨1834709, by rfl⟩ : syracuseStep 9785117 = 3669419) B3669419
theorem B6523411 : Blo 2289435 6523411 := bstep (se 1 (by rfl) ⟨4892558, by rfl⟩ : syracuseStep 6523411 = 9785117) B9785117
theorem B8697881 : Blo 2289435 8697881 := bstep (se 2 (by rfl) ⟨3261705, by rfl⟩ : syracuseStep 8697881 = 6523411) B6523411
theorem B5798587 : Blo 2289435 5798587 := bstep (se 1 (by rfl) ⟨4348940, by rfl⟩ : syracuseStep 5798587 = 8697881) B8697881
theorem B7731449 : Blo 2289435 7731449 := bstep (se 2 (by rfl) ⟨2899293, by rfl⟩ : syracuseStep 7731449 = 5798587) B5798587
theorem B5154299 : Blo 2289435 5154299 := bstep (se 1 (by rfl) ⟨3865724, by rfl⟩ : syracuseStep 5154299 = 7731449) B7731449
theorem B3436199 : Blo 2289435 3436199 := bstep (se 1 (by rfl) ⟨2577149, by rfl⟩ : syracuseStep 3436199 = 5154299) B5154299
theorem B2290799 : Blo 2289435 2290799 := bstep (se 1 (by rfl) ⟨1718099, by rfl⟩ : syracuseStep 2290799 = 3436199) B3436199
theorem B3436205 : Blo 2289435 3436205 := bbase (se 3 (by rfl) ⟨644288, by rfl⟩ : syracuseStep 3436205 = 1288577) (by norm_num)
theorem B2290803 : Blo 2289435 2290803 := bstep (se 1 (by rfl) ⟨1718102, by rfl⟩ : syracuseStep 2290803 = 3436205) B3436205
theorem B5154317 : Blo 2289435 5154317 := bbase (se 3 (by rfl) ⟨966434, by rfl⟩ : syracuseStep 5154317 = 1932869) (by norm_num)
theorem B3436211 : Blo 2289435 3436211 := bstep (se 1 (by rfl) ⟨2577158, by rfl⟩ : syracuseStep 3436211 = 5154317) B5154317
theorem B2290807 : Blo 2289435 2290807 := bstep (se 1 (by rfl) ⟨1718105, by rfl⟩ : syracuseStep 2290807 = 3436211) B3436211
theorem B2899309 : Blo 2289435 2899309 := bbase (se 3 (by rfl) ⟨543620, by rfl⟩ : syracuseStep 2899309 = 1087241) (by norm_num)
theorem B3865745 : Blo 2289435 3865745 := bstep (se 2 (by rfl) ⟨1449654, by rfl⟩ : syracuseStep 3865745 = 2899309) B2899309
theorem B2577163 : Blo 2289435 2577163 := bstep (se 1 (by rfl) ⟨1932872, by rfl⟩ : syracuseStep 2577163 = 3865745) B3865745
theorem B3436217 : Blo 2289435 3436217 := bstep (se 2 (by rfl) ⟨1288581, by rfl⟩ : syracuseStep 3436217 = 2577163) B2577163
theorem B2290811 : Blo 2289435 2290811 := bstep (se 1 (by rfl) ⟨1718108, by rfl⟩ : syracuseStep 2290811 = 3436217) B3436217
theorem B4128125 : Blo 2289435 4128125 := bbase (se 3 (by rfl) ⟨774023, by rfl⟩ : syracuseStep 4128125 = 1548047) (by norm_num)
theorem B11008333 : Blo 2289435 11008333 := bstep (se 3 (by rfl) ⟨2064062, by rfl⟩ : syracuseStep 11008333 = 4128125) B4128125
theorem B14677777 : Blo 2289435 14677777 := bstep (se 2 (by rfl) ⟨5504166, by rfl⟩ : syracuseStep 14677777 = 11008333) B11008333
theorem B19570369 : Blo 2289435 19570369 := bstep (se 2 (by rfl) ⟨7338888, by rfl⟩ : syracuseStep 19570369 = 14677777) B14677777
theorem B26093825 : Blo 2289435 26093825 := bstep (se 2 (by rfl) ⟨9785184, by rfl⟩ : syracuseStep 26093825 = 19570369) B19570369
theorem B17395883 : Blo 2289435 17395883 := bstep (se 1 (by rfl) ⟨13046912, by rfl⟩ : syracuseStep 17395883 = 26093825) B26093825
theorem B11597255 : Blo 2289435 11597255 := bstep (se 1 (by rfl) ⟨8697941, by rfl⟩ : syracuseStep 11597255 = 17395883) B17395883
theorem B7731503 : Blo 2289435 7731503 := bstep (se 1 (by rfl) ⟨5798627, by rfl⟩ : syracuseStep 7731503 = 11597255) B11597255
theorem B5154335 : Blo 2289435 5154335 := bstep (se 1 (by rfl) ⟨3865751, by rfl⟩ : syracuseStep 5154335 = 7731503) B7731503
theorem B3436223 : Blo 2289435 3436223 := bstep (se 1 (by rfl) ⟨2577167, by rfl⟩ : syracuseStep 3436223 = 5154335) B5154335
theorem B2290815 : Blo 2289435 2290815 := bstep (se 1 (by rfl) ⟨1718111, by rfl⟩ : syracuseStep 2290815 = 3436223) B3436223
theorem B3436229 : Blo 2289435 3436229 := bbase (se 4 (by rfl) ⟨322146, by rfl⟩ : syracuseStep 3436229 = 644293) (by norm_num)
theorem B2290819 : Blo 2289435 2290819 := bstep (se 1 (by rfl) ⟨1718114, by rfl⟩ : syracuseStep 2290819 = 3436229) B3436229
theorem B3865765 : Blo 2289435 3865765 := bbase (se 4 (by rfl) ⟨362415, by rfl⟩ : syracuseStep 3865765 = 724831) (by norm_num)
theorem B5154353 : Blo 2289435 5154353 := bstep (se 2 (by rfl) ⟨1932882, by rfl⟩ : syracuseStep 5154353 = 3865765) B3865765
theorem B3436235 : Blo 2289435 3436235 := bstep (se 1 (by rfl) ⟨2577176, by rfl⟩ : syracuseStep 3436235 = 5154353) B5154353
theorem B2290823 : Blo 2289435 2290823 := bstep (se 1 (by rfl) ⟨1718117, by rfl⟩ : syracuseStep 2290823 = 3436235) B3436235
theorem B2577181 : Blo 2289435 2577181 := bbase (se 3 (by rfl) ⟨483221, by rfl⟩ : syracuseStep 2577181 = 966443) (by norm_num)
theorem B3436241 : Blo 2289435 3436241 := bstep (se 2 (by rfl) ⟨1288590, by rfl⟩ : syracuseStep 3436241 = 2577181) B2577181
theorem B2290827 : Blo 2289435 2290827 := bstep (se 1 (by rfl) ⟨1718120, by rfl⟩ : syracuseStep 2290827 = 3436241) B3436241
theorem B7731557 : Blo 2289435 7731557 := bbase (se 4 (by rfl) ⟨724833, by rfl⟩ : syracuseStep 7731557 = 1449667) (by norm_num)
theorem B5154371 : Blo 2289435 5154371 := bstep (se 1 (by rfl) ⟨3865778, by rfl⟩ : syracuseStep 5154371 = 7731557) B7731557
theorem B3436247 : Blo 2289435 3436247 := bstep (se 1 (by rfl) ⟨2577185, by rfl⟩ : syracuseStep 3436247 = 5154371) B5154371
theorem B2290831 : Blo 2289435 2290831 := bstep (se 1 (by rfl) ⟨1718123, by rfl⟩ : syracuseStep 2290831 = 3436247) B3436247
theorem B3436253 : Blo 2289435 3436253 := bbase (se 3 (by rfl) ⟨644297, by rfl⟩ : syracuseStep 3436253 = 1288595) (by norm_num)
theorem B2290835 : Blo 2289435 2290835 := bstep (se 1 (by rfl) ⟨1718126, by rfl⟩ : syracuseStep 2290835 = 3436253) B3436253
theorem B5154389 : Blo 2289435 5154389 := bbase (se 8 (by rfl) ⟨30201, by rfl⟩ : syracuseStep 5154389 = 60403) (by norm_num)
theorem B3436259 : Blo 2289435 3436259 := bstep (se 1 (by rfl) ⟨2577194, by rfl⟩ : syracuseStep 3436259 = 5154389) B5154389
theorem B2290839 : Blo 2289435 2290839 := bstep (se 1 (by rfl) ⟨1718129, by rfl⟩ : syracuseStep 2290839 = 3436259) B3436259
theorem B4892653 : Blo 2289435 4892653 := bbase (se 3 (by rfl) ⟨917372, by rfl⟩ : syracuseStep 4892653 = 1834745) (by norm_num)
theorem B6523537 : Blo 2289435 6523537 := bstep (se 2 (by rfl) ⟨2446326, by rfl⟩ : syracuseStep 6523537 = 4892653) B4892653
theorem B8698049 : Blo 2289435 8698049 := bstep (se 2 (by rfl) ⟨3261768, by rfl⟩ : syracuseStep 8698049 = 6523537) B6523537
theorem B5798699 : Blo 2289435 5798699 := bstep (se 1 (by rfl) ⟨4349024, by rfl⟩ : syracuseStep 5798699 = 8698049) B8698049
theorem B3865799 : Blo 2289435 3865799 := bstep (se 1 (by rfl) ⟨2899349, by rfl⟩ : syracuseStep 3865799 = 5798699) B5798699
theorem B2577199 : Blo 2289435 2577199 := bstep (se 1 (by rfl) ⟨1932899, by rfl⟩ : syracuseStep 2577199 = 3865799) B3865799
theorem B3436265 : Blo 2289435 3436265 := bstep (se 2 (by rfl) ⟨1288599, by rfl⟩ : syracuseStep 3436265 = 2577199) B2577199
theorem B2290843 : Blo 2289435 2290843 := bstep (se 1 (by rfl) ⟨1718132, by rfl⟩ : syracuseStep 2290843 = 3436265) B3436265
theorem B3530677 : Blo 2289435 3530677 := bbase (se 5 (by rfl) ⟨165500, by rfl⟩ : syracuseStep 3530677 = 331001) (by norm_num)
theorem B4707569 : Blo 2289435 4707569 := bstep (se 2 (by rfl) ⟨1765338, by rfl⟩ : syracuseStep 4707569 = 3530677) B3530677
theorem B12553517 : Blo 2289435 12553517 := bstep (se 3 (by rfl) ⟨2353784, by rfl⟩ : syracuseStep 12553517 = 4707569) B4707569
theorem B8369011 : Blo 2289435 8369011 := bstep (se 1 (by rfl) ⟨6276758, by rfl⟩ : syracuseStep 8369011 = 12553517) B12553517
theorem B44634725 : Blo 2289435 44634725 := bstep (se 4 (by rfl) ⟨4184505, by rfl⟩ : syracuseStep 44634725 = 8369011) B8369011
theorem B29756483 : Blo 2289435 29756483 := bstep (se 1 (by rfl) ⟨22317362, by rfl⟩ : syracuseStep 29756483 = 44634725) B44634725
theorem B19837655 : Blo 2289435 19837655 := bstep (se 1 (by rfl) ⟨14878241, by rfl⟩ : syracuseStep 19837655 = 29756483) B29756483
theorem B13225103 : Blo 2289435 13225103 := bstep (se 1 (by rfl) ⟨9918827, by rfl⟩ : syracuseStep 13225103 = 19837655) B19837655
theorem B8816735 : Blo 2289435 8816735 := bstep (se 1 (by rfl) ⟨6612551, by rfl⟩ : syracuseStep 8816735 = 13225103) B13225103
theorem B23511293 : Blo 2289435 23511293 := bstep (se 3 (by rfl) ⟨4408367, by rfl⟩ : syracuseStep 23511293 = 8816735) B8816735
theorem B15674195 : Blo 2289435 15674195 := bstep (se 1 (by rfl) ⟨11755646, by rfl⟩ : syracuseStep 15674195 = 23511293) B23511293
theorem B41797853 : Blo 2289435 41797853 := bstep (se 3 (by rfl) ⟨7837097, by rfl⟩ : syracuseStep 41797853 = 15674195) B15674195
theorem B27865235 : Blo 2289435 27865235 := bstep (se 1 (by rfl) ⟨20898926, by rfl⟩ : syracuseStep 27865235 = 41797853) B41797853
theorem B18576823 : Blo 2289435 18576823 := bstep (se 1 (by rfl) ⟨13932617, by rfl⟩ : syracuseStep 18576823 = 27865235) B27865235
theorem B24769097 : Blo 2289435 24769097 := bstep (se 2 (by rfl) ⟨9288411, by rfl⟩ : syracuseStep 24769097 = 18576823) B18576823
theorem B16512731 : Blo 2289435 16512731 := bstep (se 1 (by rfl) ⟨12384548, by rfl⟩ : syracuseStep 16512731 = 24769097) B24769097
theorem B11008487 : Blo 2289435 11008487 := bstep (se 1 (by rfl) ⟨8256365, by rfl⟩ : syracuseStep 11008487 = 16512731) B16512731
theorem B29355965 : Blo 2289435 29355965 := bstep (se 3 (by rfl) ⟨5504243, by rfl⟩ : syracuseStep 29355965 = 11008487) B11008487
theorem B19570643 : Blo 2289435 19570643 := bstep (se 1 (by rfl) ⟨14677982, by rfl⟩ : syracuseStep 19570643 = 29355965) B29355965
theorem B13047095 : Blo 2289435 13047095 := bstep (se 1 (by rfl) ⟨9785321, by rfl⟩ : syracuseStep 13047095 = 19570643) B19570643
theorem B8698063 : Blo 2289435 8698063 := bstep (se 1 (by rfl) ⟨6523547, by rfl⟩ : syracuseStep 8698063 = 13047095) B13047095
theorem B11597417 : Blo 2289435 11597417 := bstep (se 2 (by rfl) ⟨4349031, by rfl⟩ : syracuseStep 11597417 = 8698063) B8698063
theorem B7731611 : Blo 2289435 7731611 := bstep (se 1 (by rfl) ⟨5798708, by rfl⟩ : syracuseStep 7731611 = 11597417) B11597417
theorem B5154407 : Blo 2289435 5154407 := bstep (se 1 (by rfl) ⟨3865805, by rfl⟩ : syracuseStep 5154407 = 7731611) B7731611
theorem B3436271 : Blo 2289435 3436271 := bstep (se 1 (by rfl) ⟨2577203, by rfl⟩ : syracuseStep 3436271 = 5154407) B5154407
theorem B2290847 : Blo 2289435 2290847 := bstep (se 1 (by rfl) ⟨1718135, by rfl⟩ : syracuseStep 2290847 = 3436271) B3436271
theorem B3436277 : Blo 2289435 3436277 := bbase (se 5 (by rfl) ⟨161075, by rfl⟩ : syracuseStep 3436277 = 322151) (by norm_num)
theorem B2290851 : Blo 2289435 2290851 := bstep (se 1 (by rfl) ⟨1718138, by rfl⟩ : syracuseStep 2290851 = 3436277) B3436277
theorem B3669509 : Blo 2289435 3669509 := bbase (se 4 (by rfl) ⟨344016, by rfl⟩ : syracuseStep 3669509 = 688033) (by norm_num)
theorem B9785357 : Blo 2289435 9785357 := bstep (se 3 (by rfl) ⟨1834754, by rfl⟩ : syracuseStep 9785357 = 3669509) B3669509
theorem B6523571 : Blo 2289435 6523571 := bstep (se 1 (by rfl) ⟨4892678, by rfl⟩ : syracuseStep 6523571 = 9785357) B9785357
theorem B4349047 : Blo 2289435 4349047 := bstep (se 1 (by rfl) ⟨3261785, by rfl⟩ : syracuseStep 4349047 = 6523571) B6523571
theorem B5798729 : Blo 2289435 5798729 := bstep (se 2 (by rfl) ⟨2174523, by rfl⟩ : syracuseStep 5798729 = 4349047) B4349047
theorem B3865819 : Blo 2289435 3865819 := bstep (se 1 (by rfl) ⟨2899364, by rfl⟩ : syracuseStep 3865819 = 5798729) B5798729
theorem B5154425 : Blo 2289435 5154425 := bstep (se 2 (by rfl) ⟨1932909, by rfl⟩ : syracuseStep 5154425 = 3865819) B3865819
theorem B3436283 : Blo 2289435 3436283 := bstep (se 1 (by rfl) ⟨2577212, by rfl⟩ : syracuseStep 3436283 = 5154425) B5154425
theorem B2290855 : Blo 2289435 2290855 := bstep (se 1 (by rfl) ⟨1718141, by rfl⟩ : syracuseStep 2290855 = 3436283) B3436283
theorem B2577217 : Blo 2289435 2577217 := bbase (se 2 (by rfl) ⟨966456, by rfl⟩ : syracuseStep 2577217 = 1932913) (by norm_num)
theorem B3436289 : Blo 2289435 3436289 := bstep (se 2 (by rfl) ⟨1288608, by rfl⟩ : syracuseStep 3436289 = 2577217) B2577217
theorem B2290859 : Blo 2289435 2290859 := bstep (se 1 (by rfl) ⟨1718144, by rfl⟩ : syracuseStep 2290859 = 3436289) B3436289
theorem B5798749 : Blo 2289435 5798749 := bbase (se 3 (by rfl) ⟨1087265, by rfl⟩ : syracuseStep 5798749 = 2174531) (by norm_num)
theorem B7731665 : Blo 2289435 7731665 := bstep (se 2 (by rfl) ⟨2899374, by rfl⟩ : syracuseStep 7731665 = 5798749) B5798749
theorem B5154443 : Blo 2289435 5154443 := bstep (se 1 (by rfl) ⟨3865832, by rfl⟩ : syracuseStep 5154443 = 7731665) B7731665
theorem B3436295 : Blo 2289435 3436295 := bstep (se 1 (by rfl) ⟨2577221, by rfl⟩ : syracuseStep 3436295 = 5154443) B5154443
theorem B2290863 : Blo 2289435 2290863 := bstep (se 1 (by rfl) ⟨1718147, by rfl⟩ : syracuseStep 2290863 = 3436295) B3436295
theorem B3436301 : Blo 2289435 3436301 := bbase (se 3 (by rfl) ⟨644306, by rfl⟩ : syracuseStep 3436301 = 1288613) (by norm_num)
theorem B2290867 : Blo 2289435 2290867 := bstep (se 1 (by rfl) ⟨1718150, by rfl⟩ : syracuseStep 2290867 = 3436301) B3436301
theorem B5154461 : Blo 2289435 5154461 := bbase (se 3 (by rfl) ⟨966461, by rfl⟩ : syracuseStep 5154461 = 1932923) (by norm_num)
theorem B3436307 : Blo 2289435 3436307 := bstep (se 1 (by rfl) ⟨2577230, by rfl⟩ : syracuseStep 3436307 = 5154461) B5154461
theorem B2290871 : Blo 2289435 2290871 := bstep (se 1 (by rfl) ⟨1718153, by rfl⟩ : syracuseStep 2290871 = 3436307) B3436307
theorem B3865853 : Blo 2289435 3865853 := bbase (se 3 (by rfl) ⟨724847, by rfl⟩ : syracuseStep 3865853 = 1449695) (by norm_num)
theorem B2577235 : Blo 2289435 2577235 := bstep (se 1 (by rfl) ⟨1932926, by rfl⟩ : syracuseStep 2577235 = 3865853) B3865853
theorem B3436313 : Blo 2289435 3436313 := bstep (se 2 (by rfl) ⟨1288617, by rfl⟩ : syracuseStep 3436313 = 2577235) B2577235
theorem B2290875 : Blo 2289435 2290875 := bstep (se 1 (by rfl) ⟨1718156, by rfl⟩ : syracuseStep 2290875 = 3436313) B3436313
theorem B3096181 : Blo 2289435 3096181 := bbase (se 5 (by rfl) ⟨145133, by rfl⟩ : syracuseStep 3096181 = 290267) (by norm_num)
theorem B4128241 : Blo 2289435 4128241 := bstep (se 2 (by rfl) ⟨1548090, by rfl⟩ : syracuseStep 4128241 = 3096181) B3096181
theorem B5504321 : Blo 2289435 5504321 := bstep (se 2 (by rfl) ⟨2064120, by rfl⟩ : syracuseStep 5504321 = 4128241) B4128241
theorem B3669547 : Blo 2289435 3669547 := bstep (se 1 (by rfl) ⟨2752160, by rfl⟩ : syracuseStep 3669547 = 5504321) B5504321
theorem B4892729 : Blo 2289435 4892729 := bstep (se 2 (by rfl) ⟨1834773, by rfl⟩ : syracuseStep 4892729 = 3669547) B3669547
theorem B13047277 : Blo 2289435 13047277 := bstep (se 3 (by rfl) ⟨2446364, by rfl⟩ : syracuseStep 13047277 = 4892729) B4892729
theorem B17396369 : Blo 2289435 17396369 := bstep (se 2 (by rfl) ⟨6523638, by rfl⟩ : syracuseStep 17396369 = 13047277) B13047277
theorem B11597579 : Blo 2289435 11597579 := bstep (se 1 (by rfl) ⟨8698184, by rfl⟩ : syracuseStep 11597579 = 17396369) B17396369
theorem B7731719 : Blo 2289435 7731719 := bstep (se 1 (by rfl) ⟨5798789, by rfl⟩ : syracuseStep 7731719 = 11597579) B11597579
theorem B5154479 : Blo 2289435 5154479 := bstep (se 1 (by rfl) ⟨3865859, by rfl⟩ : syracuseStep 5154479 = 7731719) B7731719
theorem B3436319 : Blo 2289435 3436319 := bstep (se 1 (by rfl) ⟨2577239, by rfl⟩ : syracuseStep 3436319 = 5154479) B5154479
theorem B2290879 : Blo 2289435 2290879 := bstep (se 1 (by rfl) ⟨1718159, by rfl⟩ : syracuseStep 2290879 = 3436319) B3436319
theorem B3436325 : Blo 2289435 3436325 := bbase (se 4 (by rfl) ⟨322155, by rfl⟩ : syracuseStep 3436325 = 644311) (by norm_num)
theorem B2290883 : Blo 2289435 2290883 := bstep (se 1 (by rfl) ⟨1718162, by rfl⟩ : syracuseStep 2290883 = 3436325) B3436325
theorem B2899405 : Blo 2289435 2899405 := bbase (se 3 (by rfl) ⟨543638, by rfl⟩ : syracuseStep 2899405 = 1087277) (by norm_num)
theorem B3865873 : Blo 2289435 3865873 := bstep (se 2 (by rfl) ⟨1449702, by rfl⟩ : syracuseStep 3865873 = 2899405) B2899405
theorem B5154497 : Blo 2289435 5154497 := bstep (se 2 (by rfl) ⟨1932936, by rfl⟩ : syracuseStep 5154497 = 3865873) B3865873
theorem B3436331 : Blo 2289435 3436331 := bstep (se 1 (by rfl) ⟨2577248, by rfl⟩ : syracuseStep 3436331 = 5154497) B5154497
theorem B2290887 : Blo 2289435 2290887 := bstep (se 1 (by rfl) ⟨1718165, by rfl⟩ : syracuseStep 2290887 = 3436331) B3436331
theorem B2577253 : Blo 2289435 2577253 := bbase (se 4 (by rfl) ⟨241617, by rfl⟩ : syracuseStep 2577253 = 483235) (by norm_num)
theorem B3436337 : Blo 2289435 3436337 := bstep (se 2 (by rfl) ⟨1288626, by rfl⟩ : syracuseStep 3436337 = 2577253) B2577253
theorem B2290891 : Blo 2289435 2290891 := bstep (se 1 (by rfl) ⟨1718168, by rfl⟩ : syracuseStep 2290891 = 3436337) B3436337
theorem B6523685 : Blo 2289435 6523685 := bbase (se 4 (by rfl) ⟨611595, by rfl⟩ : syracuseStep 6523685 = 1223191) (by norm_num)
theorem B4349123 : Blo 2289435 4349123 := bstep (se 1 (by rfl) ⟨3261842, by rfl⟩ : syracuseStep 4349123 = 6523685) B6523685
theorem B2899415 : Blo 2289435 2899415 := bstep (se 1 (by rfl) ⟨2174561, by rfl⟩ : syracuseStep 2899415 = 4349123) B4349123
theorem B7731773 : Blo 2289435 7731773 := bstep (se 3 (by rfl) ⟨1449707, by rfl⟩ : syracuseStep 7731773 = 2899415) B2899415
theorem B5154515 : Blo 2289435 5154515 := bstep (se 1 (by rfl) ⟨3865886, by rfl⟩ : syracuseStep 5154515 = 7731773) B7731773
theorem B3436343 : Blo 2289435 3436343 := bstep (se 1 (by rfl) ⟨2577257, by rfl⟩ : syracuseStep 3436343 = 5154515) B5154515
theorem B2290895 : Blo 2289435 2290895 := bstep (se 1 (by rfl) ⟨1718171, by rfl⟩ : syracuseStep 2290895 = 3436343) B3436343
theorem B3436349 : Blo 2289435 3436349 := bbase (se 3 (by rfl) ⟨644315, by rfl⟩ : syracuseStep 3436349 = 1288631) (by norm_num)
theorem B2290899 : Blo 2289435 2290899 := bstep (se 1 (by rfl) ⟨1718174, by rfl⟩ : syracuseStep 2290899 = 3436349) B3436349
theorem B5154533 : Blo 2289435 5154533 := bbase (se 4 (by rfl) ⟨483237, by rfl⟩ : syracuseStep 5154533 = 966475) (by norm_num)
theorem B3436355 : Blo 2289435 3436355 := bstep (se 1 (by rfl) ⟨2577266, by rfl⟩ : syracuseStep 3436355 = 5154533) B5154533
theorem B2290903 : Blo 2289435 2290903 := bstep (se 1 (by rfl) ⟨1718177, by rfl⟩ : syracuseStep 2290903 = 3436355) B3436355
theorem B5798861 : Blo 2289435 5798861 := bbase (se 3 (by rfl) ⟨1087286, by rfl⟩ : syracuseStep 5798861 = 2174573) (by norm_num)
theorem B3865907 : Blo 2289435 3865907 := bstep (se 1 (by rfl) ⟨2899430, by rfl⟩ : syracuseStep 3865907 = 5798861) B5798861
theorem B2577271 : Blo 2289435 2577271 := bstep (se 1 (by rfl) ⟨1932953, by rfl⟩ : syracuseStep 2577271 = 3865907) B3865907
theorem B3436361 : Blo 2289435 3436361 := bstep (se 2 (by rfl) ⟨1288635, by rfl⟩ : syracuseStep 3436361 = 2577271) B2577271
theorem B2290907 : Blo 2289435 2290907 := bstep (se 1 (by rfl) ⟨1718180, by rfl⟩ : syracuseStep 2290907 = 3436361) B3436361
theorem B3483253 : Blo 2289435 3483253 := bbase (se 5 (by rfl) ⟨163277, by rfl⟩ : syracuseStep 3483253 = 326555) (by norm_num)
theorem B18577349 : Blo 2289435 18577349 := bstep (se 4 (by rfl) ⟨1741626, by rfl⟩ : syracuseStep 18577349 = 3483253) B3483253
theorem B12384899 : Blo 2289435 12384899 := bstep (se 1 (by rfl) ⟨9288674, by rfl⟩ : syracuseStep 12384899 = 18577349) B18577349
theorem B8256599 : Blo 2289435 8256599 := bstep (se 1 (by rfl) ⟨6192449, by rfl⟩ : syracuseStep 8256599 = 12384899) B12384899
theorem B5504399 : Blo 2289435 5504399 := bstep (se 1 (by rfl) ⟨4128299, by rfl⟩ : syracuseStep 5504399 = 8256599) B8256599
theorem B3669599 : Blo 2289435 3669599 := bstep (se 1 (by rfl) ⟨2752199, by rfl⟩ : syracuseStep 3669599 = 5504399) B5504399
theorem B2446399 : Blo 2289435 2446399 := bstep (se 1 (by rfl) ⟨1834799, by rfl⟩ : syracuseStep 2446399 = 3669599) B3669599
theorem B3261865 : Blo 2289435 3261865 := bstep (se 2 (by rfl) ⟨1223199, by rfl⟩ : syracuseStep 3261865 = 2446399) B2446399
theorem B4349153 : Blo 2289435 4349153 := bstep (se 2 (by rfl) ⟨1630932, by rfl⟩ : syracuseStep 4349153 = 3261865) B3261865
theorem B11597741 : Blo 2289435 11597741 := bstep (se 3 (by rfl) ⟨2174576, by rfl⟩ : syracuseStep 11597741 = 4349153) B4349153
theorem B7731827 : Blo 2289435 7731827 := bstep (se 1 (by rfl) ⟨5798870, by rfl⟩ : syracuseStep 7731827 = 11597741) B11597741
theorem B5154551 : Blo 2289435 5154551 := bstep (se 1 (by rfl) ⟨3865913, by rfl⟩ : syracuseStep 5154551 = 7731827) B7731827
theorem B3436367 : Blo 2289435 3436367 := bstep (se 1 (by rfl) ⟨2577275, by rfl⟩ : syracuseStep 3436367 = 5154551) B5154551
theorem B2290911 : Blo 2289435 2290911 := bstep (se 1 (by rfl) ⟨1718183, by rfl⟩ : syracuseStep 2290911 = 3436367) B3436367
theorem B3436373 : Blo 2289435 3436373 := bbase (se 9 (by rfl) ⟨10067, by rfl⟩ : syracuseStep 3436373 = 20135) (by norm_num)
theorem B2290915 : Blo 2289435 2290915 := bstep (se 1 (by rfl) ⟨1718186, by rfl⟩ : syracuseStep 2290915 = 3436373) B3436373
theorem B2612449 : Blo 2289435 2612449 := bbase (se 2 (by rfl) ⟨979668, by rfl⟩ : syracuseStep 2612449 = 1959337) (by norm_num)
theorem B3483265 : Blo 2289435 3483265 := bstep (se 2 (by rfl) ⟨1306224, by rfl⟩ : syracuseStep 3483265 = 2612449) B2612449
theorem B4644353 : Blo 2289435 4644353 := bstep (se 2 (by rfl) ⟨1741632, by rfl⟩ : syracuseStep 4644353 = 3483265) B3483265
theorem B3096235 : Blo 2289435 3096235 := bstep (se 1 (by rfl) ⟨2322176, by rfl⟩ : syracuseStep 3096235 = 4644353) B4644353
theorem B16513253 : Blo 2289435 16513253 := bstep (se 4 (by rfl) ⟨1548117, by rfl⟩ : syracuseStep 16513253 = 3096235) B3096235
theorem B11008835 : Blo 2289435 11008835 := bstep (se 1 (by rfl) ⟨8256626, by rfl⟩ : syracuseStep 11008835 = 16513253) B16513253
theorem B7339223 : Blo 2289435 7339223 := bstep (se 1 (by rfl) ⟨5504417, by rfl⟩ : syracuseStep 7339223 = 11008835) B11008835
theorem B4892815 : Blo 2289435 4892815 := bstep (se 1 (by rfl) ⟨3669611, by rfl⟩ : syracuseStep 4892815 = 7339223) B7339223
theorem B6523753 : Blo 2289435 6523753 := bstep (se 2 (by rfl) ⟨2446407, by rfl⟩ : syracuseStep 6523753 = 4892815) B4892815
theorem B8698337 : Blo 2289435 8698337 := bstep (se 2 (by rfl) ⟨3261876, by rfl⟩ : syracuseStep 8698337 = 6523753) B6523753
theorem B5798891 : Blo 2289435 5798891 := bstep (se 1 (by rfl) ⟨4349168, by rfl⟩ : syracuseStep 5798891 = 8698337) B8698337
theorem B3865927 : Blo 2289435 3865927 := bstep (se 1 (by rfl) ⟨2899445, by rfl⟩ : syracuseStep 3865927 = 5798891) B5798891
theorem B5154569 : Blo 2289435 5154569 := bstep (se 2 (by rfl) ⟨1932963, by rfl⟩ : syracuseStep 5154569 = 3865927) B3865927
theorem B3436379 : Blo 2289435 3436379 := bstep (se 1 (by rfl) ⟨2577284, by rfl⟩ : syracuseStep 3436379 = 5154569) B5154569
theorem B2290919 : Blo 2289435 2290919 := bstep (se 1 (by rfl) ⟨1718189, by rfl⟩ : syracuseStep 2290919 = 3436379) B3436379
theorem B2577289 : Blo 2289435 2577289 := bbase (se 2 (by rfl) ⟨966483, by rfl⟩ : syracuseStep 2577289 = 1932967) (by norm_num)
theorem B3436385 : Blo 2289435 3436385 := bstep (se 2 (by rfl) ⟨1288644, by rfl⟩ : syracuseStep 3436385 = 2577289) B2577289
theorem B2290923 : Blo 2289435 2290923 := bstep (se 1 (by rfl) ⟨1718192, by rfl⟩ : syracuseStep 2290923 = 3436385) B3436385
theorem B6039517 : Blo 2289435 6039517 := bbase (se 3 (by rfl) ⟨1132409, by rfl⟩ : syracuseStep 6039517 = 2264819) (by norm_num)
theorem B8052689 : Blo 2289435 8052689 := bstep (se 2 (by rfl) ⟨3019758, by rfl⟩ : syracuseStep 8052689 = 6039517) B6039517
theorem B5368459 : Blo 2289435 5368459 := bstep (se 1 (by rfl) ⟨4026344, by rfl⟩ : syracuseStep 5368459 = 8052689) B8052689
theorem B7157945 : Blo 2289435 7157945 := bstep (se 2 (by rfl) ⟨2684229, by rfl⟩ : syracuseStep 7157945 = 5368459) B5368459
theorem B4771963 : Blo 2289435 4771963 := bstep (se 1 (by rfl) ⟨3578972, by rfl⟩ : syracuseStep 4771963 = 7157945) B7157945
theorem B25450469 : Blo 2289435 25450469 := bstep (se 4 (by rfl) ⟨2385981, by rfl⟩ : syracuseStep 25450469 = 4771963) B4771963
theorem B16966979 : Blo 2289435 16966979 := bstep (se 1 (by rfl) ⟨12725234, by rfl⟩ : syracuseStep 16966979 = 25450469) B25450469
theorem B11311319 : Blo 2289435 11311319 := bstep (se 1 (by rfl) ⟨8483489, by rfl⟩ : syracuseStep 11311319 = 16966979) B16966979
theorem B7540879 : Blo 2289435 7540879 := bstep (se 1 (by rfl) ⟨5655659, by rfl⟩ : syracuseStep 7540879 = 11311319) B11311319
theorem B10054505 : Blo 2289435 10054505 := bstep (se 2 (by rfl) ⟨3770439, by rfl⟩ : syracuseStep 10054505 = 7540879) B7540879
theorem B6703003 : Blo 2289435 6703003 := bstep (se 1 (by rfl) ⟨5027252, by rfl⟩ : syracuseStep 6703003 = 10054505) B10054505
theorem B35749349 : Blo 2289435 35749349 := bstep (se 4 (by rfl) ⟨3351501, by rfl⟩ : syracuseStep 35749349 = 6703003) B6703003
theorem B23832899 : Blo 2289435 23832899 := bstep (se 1 (by rfl) ⟨17874674, by rfl⟩ : syracuseStep 23832899 = 35749349) B35749349
theorem B15888599 : Blo 2289435 15888599 := bstep (se 1 (by rfl) ⟨11916449, by rfl⟩ : syracuseStep 15888599 = 23832899) B23832899
theorem B10592399 : Blo 2289435 10592399 := bstep (se 1 (by rfl) ⟨7944299, by rfl⟩ : syracuseStep 10592399 = 15888599) B15888599
theorem B7061599 : Blo 2289435 7061599 := bstep (se 1 (by rfl) ⟨5296199, by rfl⟩ : syracuseStep 7061599 = 10592399) B10592399
theorem B37661861 : Blo 2289435 37661861 := bstep (se 4 (by rfl) ⟨3530799, by rfl⟩ : syracuseStep 37661861 = 7061599) B7061599
theorem B25107907 : Blo 2289435 25107907 := bstep (se 1 (by rfl) ⟨18830930, by rfl⟩ : syracuseStep 25107907 = 37661861) B37661861
theorem B33477209 : Blo 2289435 33477209 := bstep (se 2 (by rfl) ⟨12553953, by rfl⟩ : syracuseStep 33477209 = 25107907) B25107907
theorem B22318139 : Blo 2289435 22318139 := bstep (se 1 (by rfl) ⟨16738604, by rfl⟩ : syracuseStep 22318139 = 33477209) B33477209
theorem B14878759 : Blo 2289435 14878759 := bstep (se 1 (by rfl) ⟨11159069, by rfl⟩ : syracuseStep 14878759 = 22318139) B22318139
theorem B19838345 : Blo 2289435 19838345 := bstep (se 2 (by rfl) ⟨7439379, by rfl⟩ : syracuseStep 19838345 = 14878759) B14878759
theorem B52902253 : Blo 2289435 52902253 := bstep (se 3 (by rfl) ⟨9919172, by rfl⟩ : syracuseStep 52902253 = 19838345) B19838345
theorem B282145349 : Blo 2289435 282145349 := bstep (se 4 (by rfl) ⟨26451126, by rfl⟩ : syracuseStep 282145349 = 52902253) B52902253
theorem B188096899 : Blo 2289435 188096899 := bstep (se 1 (by rfl) ⟨141072674, by rfl⟩ : syracuseStep 188096899 = 282145349) B282145349
theorem B250795865 : Blo 2289435 250795865 := bstep (se 2 (by rfl) ⟨94048449, by rfl⟩ : syracuseStep 250795865 = 188096899) B188096899
theorem B167197243 : Blo 2289435 167197243 := bstep (se 1 (by rfl) ⟨125397932, by rfl⟩ : syracuseStep 167197243 = 250795865) B250795865
theorem B222929657 : Blo 2289435 222929657 := bstep (se 2 (by rfl) ⟨83598621, by rfl⟩ : syracuseStep 222929657 = 167197243) B167197243
theorem B148619771 : Blo 2289435 148619771 := bstep (se 1 (by rfl) ⟨111464828, by rfl⟩ : syracuseStep 148619771 = 222929657) B222929657
theorem B99079847 : Blo 2289435 99079847 := bstep (se 1 (by rfl) ⟨74309885, by rfl⟩ : syracuseStep 99079847 = 148619771) B148619771
theorem B66053231 : Blo 2289435 66053231 := bstep (se 1 (by rfl) ⟨49539923, by rfl⟩ : syracuseStep 66053231 = 99079847) B99079847
theorem B44035487 : Blo 2289435 44035487 := bstep (se 1 (by rfl) ⟨33026615, by rfl⟩ : syracuseStep 44035487 = 66053231) B66053231
theorem B29356991 : Blo 2289435 29356991 := bstep (se 1 (by rfl) ⟨22017743, by rfl⟩ : syracuseStep 29356991 = 44035487) B44035487
theorem B19571327 : Blo 2289435 19571327 := bstep (se 1 (by rfl) ⟨14678495, by rfl⟩ : syracuseStep 19571327 = 29356991) B29356991
theorem B13047551 : Blo 2289435 13047551 := bstep (se 1 (by rfl) ⟨9785663, by rfl⟩ : syracuseStep 13047551 = 19571327) B19571327
theorem B8698367 : Blo 2289435 8698367 := bstep (se 1 (by rfl) ⟨6523775, by rfl⟩ : syracuseStep 8698367 = 13047551) B13047551
theorem B5798911 : Blo 2289435 5798911 := bstep (se 1 (by rfl) ⟨4349183, by rfl⟩ : syracuseStep 5798911 = 8698367) B8698367
theorem B7731881 : Blo 2289435 7731881 := bstep (se 2 (by rfl) ⟨2899455, by rfl⟩ : syracuseStep 7731881 = 5798911) B5798911
theorem B5154587 : Blo 2289435 5154587 := bstep (se 1 (by rfl) ⟨3865940, by rfl⟩ : syracuseStep 5154587 = 7731881) B7731881
theorem B3436391 : Blo 2289435 3436391 := bstep (se 1 (by rfl) ⟨2577293, by rfl⟩ : syracuseStep 3436391 = 5154587) B5154587
theorem B2290927 : Blo 2289435 2290927 := bstep (se 1 (by rfl) ⟨1718195, by rfl⟩ : syracuseStep 2290927 = 3436391) B3436391
theorem B3436397 : Blo 2289435 3436397 := bbase (se 3 (by rfl) ⟨644324, by rfl⟩ : syracuseStep 3436397 = 1288649) (by norm_num)
theorem B2290931 : Blo 2289435 2290931 := bstep (se 1 (by rfl) ⟨1718198, by rfl⟩ : syracuseStep 2290931 = 3436397) B3436397
theorem B5154605 : Blo 2289435 5154605 := bbase (se 3 (by rfl) ⟨966488, by rfl⟩ : syracuseStep 5154605 = 1932977) (by norm_num)
theorem B3436403 : Blo 2289435 3436403 := bstep (se 1 (by rfl) ⟨2577302, by rfl⟩ : syracuseStep 3436403 = 5154605) B5154605
theorem B2290935 : Blo 2289435 2290935 := bstep (se 1 (by rfl) ⟨1718201, by rfl⟩ : syracuseStep 2290935 = 3436403) B3436403
theorem B9785717 : Blo 2289435 9785717 := bbase (se 5 (by rfl) ⟨458705, by rfl⟩ : syracuseStep 9785717 = 917411) (by norm_num)
theorem B6523811 : Blo 2289435 6523811 := bstep (se 1 (by rfl) ⟨4892858, by rfl⟩ : syracuseStep 6523811 = 9785717) B9785717
theorem B4349207 : Blo 2289435 4349207 := bstep (se 1 (by rfl) ⟨3261905, by rfl⟩ : syracuseStep 4349207 = 6523811) B6523811
theorem B2899471 : Blo 2289435 2899471 := bstep (se 1 (by rfl) ⟨2174603, by rfl⟩ : syracuseStep 2899471 = 4349207) B4349207
theorem B3865961 : Blo 2289435 3865961 := bstep (se 2 (by rfl) ⟨1449735, by rfl⟩ : syracuseStep 3865961 = 2899471) B2899471
theorem B2577307 : Blo 2289435 2577307 := bstep (se 1 (by rfl) ⟨1932980, by rfl⟩ : syracuseStep 2577307 = 3865961) B3865961
theorem B3436409 : Blo 2289435 3436409 := bstep (se 2 (by rfl) ⟨1288653, by rfl⟩ : syracuseStep 3436409 = 2577307) B2577307
theorem B2290939 : Blo 2289435 2290939 := bstep (se 1 (by rfl) ⟨1718204, by rfl⟩ : syracuseStep 2290939 = 3436409) B3436409
theorem B2752237 : Blo 2289435 2752237 := bbase (se 3 (by rfl) ⟨516044, by rfl⟩ : syracuseStep 2752237 = 1032089) (by norm_num)
theorem B14678597 : Blo 2289435 14678597 := bstep (se 4 (by rfl) ⟨1376118, by rfl⟩ : syracuseStep 14678597 = 2752237) B2752237
theorem B39142925 : Blo 2289435 39142925 := bstep (se 3 (by rfl) ⟨7339298, by rfl⟩ : syracuseStep 39142925 = 14678597) B14678597
theorem B26095283 : Blo 2289435 26095283 := bstep (se 1 (by rfl) ⟨19571462, by rfl⟩ : syracuseStep 26095283 = 39142925) B39142925
theorem B17396855 : Blo 2289435 17396855 := bstep (se 1 (by rfl) ⟨13047641, by rfl⟩ : syracuseStep 17396855 = 26095283) B26095283
theorem B11597903 : Blo 2289435 11597903 := bstep (se 1 (by rfl) ⟨8698427, by rfl⟩ : syracuseStep 11597903 = 17396855) B17396855
theorem B7731935 : Blo 2289435 7731935 := bstep (se 1 (by rfl) ⟨5798951, by rfl⟩ : syracuseStep 7731935 = 11597903) B11597903
theorem B5154623 : Blo 2289435 5154623 := bstep (se 1 (by rfl) ⟨3865967, by rfl⟩ : syracuseStep 5154623 = 7731935) B7731935
theorem B3436415 : Blo 2289435 3436415 := bstep (se 1 (by rfl) ⟨2577311, by rfl⟩ : syracuseStep 3436415 = 5154623) B5154623
theorem B2290943 : Blo 2289435 2290943 := bstep (se 1 (by rfl) ⟨1718207, by rfl⟩ : syracuseStep 2290943 = 3436415) B3436415
theorem B3436421 : Blo 2289435 3436421 := bbase (se 4 (by rfl) ⟨322164, by rfl⟩ : syracuseStep 3436421 = 644329) (by norm_num)
theorem B2290947 : Blo 2289435 2290947 := bstep (se 1 (by rfl) ⟨1718210, by rfl⟩ : syracuseStep 2290947 = 3436421) B3436421
theorem B3865981 : Blo 2289435 3865981 := bbase (se 3 (by rfl) ⟨724871, by rfl⟩ : syracuseStep 3865981 = 1449743) (by norm_num)
theorem B5154641 : Blo 2289435 5154641 := bstep (se 2 (by rfl) ⟨1932990, by rfl⟩ : syracuseStep 5154641 = 3865981) B3865981
theorem B3436427 : Blo 2289435 3436427 := bstep (se 1 (by rfl) ⟨2577320, by rfl⟩ : syracuseStep 3436427 = 5154641) B5154641
theorem B2290951 : Blo 2289435 2290951 := bstep (se 1 (by rfl) ⟨1718213, by rfl⟩ : syracuseStep 2290951 = 3436427) B3436427
theorem B2577325 : Blo 2289435 2577325 := bbase (se 3 (by rfl) ⟨483248, by rfl⟩ : syracuseStep 2577325 = 966497) (by norm_num)
theorem B3436433 : Blo 2289435 3436433 := bstep (se 2 (by rfl) ⟨1288662, by rfl⟩ : syracuseStep 3436433 = 2577325) B2577325
theorem B2290955 : Blo 2289435 2290955 := bstep (se 1 (by rfl) ⟨1718216, by rfl⟩ : syracuseStep 2290955 = 3436433) B3436433
theorem B7731989 : Blo 2289435 7731989 := bbase (se 6 (by rfl) ⟨181218, by rfl⟩ : syracuseStep 7731989 = 362437) (by norm_num)
theorem B5154659 : Blo 2289435 5154659 := bstep (se 1 (by rfl) ⟨3865994, by rfl⟩ : syracuseStep 5154659 = 7731989) B7731989
theorem B3436439 : Blo 2289435 3436439 := bstep (se 1 (by rfl) ⟨2577329, by rfl⟩ : syracuseStep 3436439 = 5154659) B5154659
theorem B2290959 : Blo 2289435 2290959 := bstep (se 1 (by rfl) ⟨1718219, by rfl⟩ : syracuseStep 2290959 = 3436439) B3436439
theorem B3436445 : Blo 2289435 3436445 := bbase (se 3 (by rfl) ⟨644333, by rfl⟩ : syracuseStep 3436445 = 1288667) (by norm_num)
theorem B2290963 : Blo 2289435 2290963 := bstep (se 1 (by rfl) ⟨1718222, by rfl⟩ : syracuseStep 2290963 = 3436445) B3436445
theorem B5154677 : Blo 2289435 5154677 := bbase (se 5 (by rfl) ⟨241625, by rfl⟩ : syracuseStep 5154677 = 483251) (by norm_num)
theorem B3436451 : Blo 2289435 3436451 := bstep (se 1 (by rfl) ⟨2577338, by rfl⟩ : syracuseStep 3436451 = 5154677) B5154677
theorem B2290967 : Blo 2289435 2290967 := bstep (se 1 (by rfl) ⟨1718225, by rfl⟩ : syracuseStep 2290967 = 3436451) B3436451
theorem B7439525 : Blo 2289435 7439525 := bbase (se 4 (by rfl) ⟨697455, by rfl⟩ : syracuseStep 7439525 = 1394911) (by norm_num)
theorem B4959683 : Blo 2289435 4959683 := bstep (se 1 (by rfl) ⟨3719762, by rfl⟩ : syracuseStep 4959683 = 7439525) B7439525
theorem B3306455 : Blo 2289435 3306455 := bstep (se 1 (by rfl) ⟨2479841, by rfl⟩ : syracuseStep 3306455 = 4959683) B4959683
theorem B35268853 : Blo 2289435 35268853 := bstep (se 5 (by rfl) ⟨1653227, by rfl⟩ : syracuseStep 35268853 = 3306455) B3306455
theorem B47025137 : Blo 2289435 47025137 := bstep (se 2 (by rfl) ⟨17634426, by rfl⟩ : syracuseStep 47025137 = 35268853) B35268853
theorem B31350091 : Blo 2289435 31350091 := bstep (se 1 (by rfl) ⟨23512568, by rfl⟩ : syracuseStep 31350091 = 47025137) B47025137
theorem B41800121 : Blo 2289435 41800121 := bstep (se 2 (by rfl) ⟨15675045, by rfl⟩ : syracuseStep 41800121 = 31350091) B31350091
theorem B27866747 : Blo 2289435 27866747 := bstep (se 1 (by rfl) ⟨20900060, by rfl⟩ : syracuseStep 27866747 = 41800121) B41800121
theorem B18577831 : Blo 2289435 18577831 := bstep (se 1 (by rfl) ⟨13933373, by rfl⟩ : syracuseStep 18577831 = 27866747) B27866747
theorem B24770441 : Blo 2289435 24770441 := bstep (se 2 (by rfl) ⟨9288915, by rfl⟩ : syracuseStep 24770441 = 18577831) B18577831
theorem B16513627 : Blo 2289435 16513627 := bstep (se 1 (by rfl) ⟨12385220, by rfl⟩ : syracuseStep 16513627 = 24770441) B24770441
theorem B22018169 : Blo 2289435 22018169 := bstep (se 2 (by rfl) ⟨8256813, by rfl⟩ : syracuseStep 22018169 = 16513627) B16513627
theorem B14678779 : Blo 2289435 14678779 := bstep (se 1 (by rfl) ⟨11009084, by rfl⟩ : syracuseStep 14678779 = 22018169) B22018169
theorem B19571705 : Blo 2289435 19571705 := bstep (se 2 (by rfl) ⟨7339389, by rfl⟩ : syracuseStep 19571705 = 14678779) B14678779
theorem B13047803 : Blo 2289435 13047803 := bstep (se 1 (by rfl) ⟨9785852, by rfl⟩ : syracuseStep 13047803 = 19571705) B19571705
theorem B8698535 : Blo 2289435 8698535 := bstep (se 1 (by rfl) ⟨6523901, by rfl⟩ : syracuseStep 8698535 = 13047803) B13047803
theorem B5799023 : Blo 2289435 5799023 := bstep (se 1 (by rfl) ⟨4349267, by rfl⟩ : syracuseStep 5799023 = 8698535) B8698535
theorem B3866015 : Blo 2289435 3866015 := bstep (se 1 (by rfl) ⟨2899511, by rfl⟩ : syracuseStep 3866015 = 5799023) B5799023
theorem B2577343 : Blo 2289435 2577343 := bstep (se 1 (by rfl) ⟨1933007, by rfl⟩ : syracuseStep 2577343 = 3866015) B3866015
theorem B3436457 : Blo 2289435 3436457 := bstep (se 2 (by rfl) ⟨1288671, by rfl⟩ : syracuseStep 3436457 = 2577343) B2577343
theorem B2290971 : Blo 2289435 2290971 := bstep (se 1 (by rfl) ⟨1718228, by rfl⟩ : syracuseStep 2290971 = 3436457) B3436457
theorem B8698549 : Blo 2289435 8698549 := bbase (se 5 (by rfl) ⟨407744, by rfl⟩ : syracuseStep 8698549 = 815489) (by norm_num)
theorem B11598065 : Blo 2289435 11598065 := bstep (se 2 (by rfl) ⟨4349274, by rfl⟩ : syracuseStep 11598065 = 8698549) B8698549
theorem B7732043 : Blo 2289435 7732043 := bstep (se 1 (by rfl) ⟨5799032, by rfl⟩ : syracuseStep 7732043 = 11598065) B11598065
theorem B5154695 : Blo 2289435 5154695 := bstep (se 1 (by rfl) ⟨3866021, by rfl⟩ : syracuseStep 5154695 = 7732043) B7732043
theorem B3436463 : Blo 2289435 3436463 := bstep (se 1 (by rfl) ⟨2577347, by rfl⟩ : syracuseStep 3436463 = 5154695) B5154695
theorem B2290975 : Blo 2289435 2290975 := bstep (se 1 (by rfl) ⟨1718231, by rfl⟩ : syracuseStep 2290975 = 3436463) B3436463
theorem B3436469 : Blo 2289435 3436469 := bbase (se 5 (by rfl) ⟨161084, by rfl⟩ : syracuseStep 3436469 = 322169) (by norm_num)
theorem B2290979 : Blo 2289435 2290979 := bstep (se 1 (by rfl) ⟨1718234, by rfl⟩ : syracuseStep 2290979 = 3436469) B3436469
theorem B5799053 : Blo 2289435 5799053 := bbase (se 3 (by rfl) ⟨1087322, by rfl⟩ : syracuseStep 5799053 = 2174645) (by norm_num)
theorem B3866035 : Blo 2289435 3866035 := bstep (se 1 (by rfl) ⟨2899526, by rfl⟩ : syracuseStep 3866035 = 5799053) B5799053
theorem B5154713 : Blo 2289435 5154713 := bstep (se 2 (by rfl) ⟨1933017, by rfl⟩ : syracuseStep 5154713 = 3866035) B3866035
theorem B3436475 : Blo 2289435 3436475 := bstep (se 1 (by rfl) ⟨2577356, by rfl⟩ : syracuseStep 3436475 = 5154713) B5154713
theorem B2290983 : Blo 2289435 2290983 := bstep (se 1 (by rfl) ⟨1718237, by rfl⟩ : syracuseStep 2290983 = 3436475) B3436475
theorem B2577361 : Blo 2289435 2577361 := bbase (se 2 (by rfl) ⟨966510, by rfl⟩ : syracuseStep 2577361 = 1933021) (by norm_num)
theorem B3436481 : Blo 2289435 3436481 := bstep (se 2 (by rfl) ⟨1288680, by rfl⟩ : syracuseStep 3436481 = 2577361) B2577361
theorem B2290987 : Blo 2289435 2290987 := bstep (se 1 (by rfl) ⟨1718240, by rfl⟩ : syracuseStep 2290987 = 3436481) B3436481
theorem B3918797 : Blo 2289435 3918797 := bbase (se 3 (by rfl) ⟨734774, by rfl⟩ : syracuseStep 3918797 = 1469549) (by norm_num)
theorem B2612531 : Blo 2289435 2612531 := bstep (se 1 (by rfl) ⟨1959398, by rfl⟩ : syracuseStep 2612531 = 3918797) B3918797
theorem B6966749 : Blo 2289435 6966749 := bstep (se 3 (by rfl) ⟨1306265, by rfl⟩ : syracuseStep 6966749 = 2612531) B2612531
theorem B18577997 : Blo 2289435 18577997 := bstep (se 3 (by rfl) ⟨3483374, by rfl⟩ : syracuseStep 18577997 = 6966749) B6966749
theorem B12385331 : Blo 2289435 12385331 := bstep (se 1 (by rfl) ⟨9288998, by rfl⟩ : syracuseStep 12385331 = 18577997) B18577997
theorem B8256887 : Blo 2289435 8256887 := bstep (se 1 (by rfl) ⟨6192665, by rfl⟩ : syracuseStep 8256887 = 12385331) B12385331
theorem B5504591 : Blo 2289435 5504591 := bstep (se 1 (by rfl) ⟨4128443, by rfl⟩ : syracuseStep 5504591 = 8256887) B8256887
theorem B3669727 : Blo 2289435 3669727 := bstep (se 1 (by rfl) ⟨2752295, by rfl⟩ : syracuseStep 3669727 = 5504591) B5504591
theorem B4892969 : Blo 2289435 4892969 := bstep (se 2 (by rfl) ⟨1834863, by rfl⟩ : syracuseStep 4892969 = 3669727) B3669727
theorem B3261979 : Blo 2289435 3261979 := bstep (se 1 (by rfl) ⟨2446484, by rfl⟩ : syracuseStep 3261979 = 4892969) B4892969
theorem B4349305 : Blo 2289435 4349305 := bstep (se 2 (by rfl) ⟨1630989, by rfl⟩ : syracuseStep 4349305 = 3261979) B3261979
theorem B5799073 : Blo 2289435 5799073 := bstep (se 2 (by rfl) ⟨2174652, by rfl⟩ : syracuseStep 5799073 = 4349305) B4349305
theorem B7732097 : Blo 2289435 7732097 := bstep (se 2 (by rfl) ⟨2899536, by rfl⟩ : syracuseStep 7732097 = 5799073) B5799073
theorem B5154731 : Blo 2289435 5154731 := bstep (se 1 (by rfl) ⟨3866048, by rfl⟩ : syracuseStep 5154731 = 7732097) B7732097
theorem B3436487 : Blo 2289435 3436487 := bstep (se 1 (by rfl) ⟨2577365, by rfl⟩ : syracuseStep 3436487 = 5154731) B5154731
theorem B2290991 : Blo 2289435 2290991 := bstep (se 1 (by rfl) ⟨1718243, by rfl⟩ : syracuseStep 2290991 = 3436487) B3436487
theorem B3436493 : Blo 2289435 3436493 := bbase (se 3 (by rfl) ⟨644342, by rfl⟩ : syracuseStep 3436493 = 1288685) (by norm_num)
theorem B2290995 : Blo 2289435 2290995 := bstep (se 1 (by rfl) ⟨1718246, by rfl⟩ : syracuseStep 2290995 = 3436493) B3436493
theorem B5154749 : Blo 2289435 5154749 := bbase (se 3 (by rfl) ⟨966515, by rfl⟩ : syracuseStep 5154749 = 1933031) (by norm_num)
theorem B3436499 : Blo 2289435 3436499 := bstep (se 1 (by rfl) ⟨2577374, by rfl⟩ : syracuseStep 3436499 = 5154749) B5154749
theorem B2290999 : Blo 2289435 2290999 := bstep (se 1 (by rfl) ⟨1718249, by rfl⟩ : syracuseStep 2290999 = 3436499) B3436499
theorem B3866069 : Blo 2289435 3866069 := bbase (se 7 (by rfl) ⟨45305, by rfl⟩ : syracuseStep 3866069 = 90611) (by norm_num)
theorem B2577379 : Blo 2289435 2577379 := bstep (se 1 (by rfl) ⟨1933034, by rfl⟩ : syracuseStep 2577379 = 3866069) B3866069
theorem B3436505 : Blo 2289435 3436505 := bstep (se 2 (by rfl) ⟨1288689, by rfl⟩ : syracuseStep 3436505 = 2577379) B2577379
theorem B2291003 : Blo 2289435 2291003 := bstep (se 1 (by rfl) ⟨1718252, by rfl⟩ : syracuseStep 2291003 = 3436505) B3436505
theorem B9786005 : Blo 2289435 9786005 := bbase (se 6 (by rfl) ⟨229359, by rfl⟩ : syracuseStep 9786005 = 458719) (by norm_num)
theorem B6524003 : Blo 2289435 6524003 := bstep (se 1 (by rfl) ⟨4893002, by rfl⟩ : syracuseStep 6524003 = 9786005) B9786005
theorem B17397341 : Blo 2289435 17397341 := bstep (se 3 (by rfl) ⟨3262001, by rfl⟩ : syracuseStep 17397341 = 6524003) B6524003
theorem B11598227 : Blo 2289435 11598227 := bstep (se 1 (by rfl) ⟨8698670, by rfl⟩ : syracuseStep 11598227 = 17397341) B17397341
theorem B7732151 : Blo 2289435 7732151 := bstep (se 1 (by rfl) ⟨5799113, by rfl⟩ : syracuseStep 7732151 = 11598227) B11598227
theorem B5154767 : Blo 2289435 5154767 := bstep (se 1 (by rfl) ⟨3866075, by rfl⟩ : syracuseStep 5154767 = 7732151) B7732151
theorem B3436511 : Blo 2289435 3436511 := bstep (se 1 (by rfl) ⟨2577383, by rfl⟩ : syracuseStep 3436511 = 5154767) B5154767
theorem B2291007 : Blo 2289435 2291007 := bstep (se 1 (by rfl) ⟨1718255, by rfl⟩ : syracuseStep 2291007 = 3436511) B3436511
theorem B3436517 : Blo 2289435 3436517 := bbase (se 4 (by rfl) ⟨322173, by rfl⟩ : syracuseStep 3436517 = 644347) (by norm_num)
theorem B2291011 : Blo 2289435 2291011 := bstep (se 1 (by rfl) ⟨1718258, by rfl⟩ : syracuseStep 2291011 = 3436517) B3436517
theorem B3096365 : Blo 2289435 3096365 := bbase (se 3 (by rfl) ⟨580568, by rfl⟩ : syracuseStep 3096365 = 1161137) (by norm_num)
theorem B8256973 : Blo 2289435 8256973 := bstep (se 3 (by rfl) ⟨1548182, by rfl⟩ : syracuseStep 8256973 = 3096365) B3096365
theorem B11009297 : Blo 2289435 11009297 := bstep (se 2 (by rfl) ⟨4128486, by rfl⟩ : syracuseStep 11009297 = 8256973) B8256973
theorem B7339531 : Blo 2289435 7339531 := bstep (se 1 (by rfl) ⟨5504648, by rfl⟩ : syracuseStep 7339531 = 11009297) B11009297
theorem B9786041 : Blo 2289435 9786041 := bstep (se 2 (by rfl) ⟨3669765, by rfl⟩ : syracuseStep 9786041 = 7339531) B7339531
theorem B6524027 : Blo 2289435 6524027 := bstep (se 1 (by rfl) ⟨4893020, by rfl⟩ : syracuseStep 6524027 = 9786041) B9786041
theorem B4349351 : Blo 2289435 4349351 := bstep (se 1 (by rfl) ⟨3262013, by rfl⟩ : syracuseStep 4349351 = 6524027) B6524027
theorem B2899567 : Blo 2289435 2899567 := bstep (se 1 (by rfl) ⟨2174675, by rfl⟩ : syracuseStep 2899567 = 4349351) B4349351
theorem B3866089 : Blo 2289435 3866089 := bstep (se 2 (by rfl) ⟨1449783, by rfl⟩ : syracuseStep 3866089 = 2899567) B2899567
theorem B5154785 : Blo 2289435 5154785 := bstep (se 2 (by rfl) ⟨1933044, by rfl⟩ : syracuseStep 5154785 = 3866089) B3866089
theorem B3436523 : Blo 2289435 3436523 := bstep (se 1 (by rfl) ⟨2577392, by rfl⟩ : syracuseStep 3436523 = 5154785) B5154785
theorem B2291015 : Blo 2289435 2291015 := bstep (se 1 (by rfl) ⟨1718261, by rfl⟩ : syracuseStep 2291015 = 3436523) B3436523
theorem B2577397 : Blo 2289435 2577397 := bbase (se 5 (by rfl) ⟨120815, by rfl⟩ : syracuseStep 2577397 = 241631) (by norm_num)
theorem B3436529 : Blo 2289435 3436529 := bstep (se 2 (by rfl) ⟨1288698, by rfl⟩ : syracuseStep 3436529 = 2577397) B2577397
theorem B2291019 : Blo 2289435 2291019 := bstep (se 1 (by rfl) ⟨1718264, by rfl⟩ : syracuseStep 2291019 = 3436529) B3436529
theorem B2899577 : Blo 2289435 2899577 := bbase (se 2 (by rfl) ⟨1087341, by rfl⟩ : syracuseStep 2899577 = 2174683) (by norm_num)
theorem B7732205 : Blo 2289435 7732205 := bstep (se 3 (by rfl) ⟨1449788, by rfl⟩ : syracuseStep 7732205 = 2899577) B2899577
theorem B5154803 : Blo 2289435 5154803 := bstep (se 1 (by rfl) ⟨3866102, by rfl⟩ : syracuseStep 5154803 = 7732205) B7732205
theorem B3436535 : Blo 2289435 3436535 := bstep (se 1 (by rfl) ⟨2577401, by rfl⟩ : syracuseStep 3436535 = 5154803) B5154803
theorem B2291023 : Blo 2289435 2291023 := bstep (se 1 (by rfl) ⟨1718267, by rfl⟩ : syracuseStep 2291023 = 3436535) B3436535
theorem B3436541 : Blo 2289435 3436541 := bbase (se 3 (by rfl) ⟨644351, by rfl⟩ : syracuseStep 3436541 = 1288703) (by norm_num)
theorem B2291027 : Blo 2289435 2291027 := bstep (se 1 (by rfl) ⟨1718270, by rfl⟩ : syracuseStep 2291027 = 3436541) B3436541
theorem B5154821 : Blo 2289435 5154821 := bbase (se 4 (by rfl) ⟨483264, by rfl⟩ : syracuseStep 5154821 = 966529) (by norm_num)
theorem B3436547 : Blo 2289435 3436547 := bstep (se 1 (by rfl) ⟨2577410, by rfl⟩ : syracuseStep 3436547 = 5154821) B5154821
theorem B2291031 : Blo 2289435 2291031 := bstep (se 1 (by rfl) ⟨1718273, by rfl⟩ : syracuseStep 2291031 = 3436547) B3436547
theorem B4349389 : Blo 2289435 4349389 := bbase (se 3 (by rfl) ⟨815510, by rfl⟩ : syracuseStep 4349389 = 1631021) (by norm_num)
theorem B5799185 : Blo 2289435 5799185 := bstep (se 2 (by rfl) ⟨2174694, by rfl⟩ : syracuseStep 5799185 = 4349389) B4349389
theorem B3866123 : Blo 2289435 3866123 := bstep (se 1 (by rfl) ⟨2899592, by rfl⟩ : syracuseStep 3866123 = 5799185) B5799185
theorem B2577415 : Blo 2289435 2577415 := bstep (se 1 (by rfl) ⟨1933061, by rfl⟩ : syracuseStep 2577415 = 3866123) B3866123
theorem B3436553 : Blo 2289435 3436553 := bstep (se 2 (by rfl) ⟨1288707, by rfl⟩ : syracuseStep 3436553 = 2577415) B2577415
theorem B2291035 : Blo 2289435 2291035 := bstep (se 1 (by rfl) ⟨1718276, by rfl⟩ : syracuseStep 2291035 = 3436553) B3436553
theorem B11598389 : Blo 2289435 11598389 := bbase (se 5 (by rfl) ⟨543674, by rfl⟩ : syracuseStep 11598389 = 1087349) (by norm_num)
theorem B7732259 : Blo 2289435 7732259 := bstep (se 1 (by rfl) ⟨5799194, by rfl⟩ : syracuseStep 7732259 = 11598389) B11598389
theorem B5154839 : Blo 2289435 5154839 := bstep (se 1 (by rfl) ⟨3866129, by rfl⟩ : syracuseStep 5154839 = 7732259) B7732259
theorem B3436559 : Blo 2289435 3436559 := bstep (se 1 (by rfl) ⟨2577419, by rfl⟩ : syracuseStep 3436559 = 5154839) B5154839
theorem B2291039 : Blo 2289435 2291039 := bstep (se 1 (by rfl) ⟨1718279, by rfl⟩ : syracuseStep 2291039 = 3436559) B3436559
theorem B3436565 : Blo 2289435 3436565 := bbase (se 6 (by rfl) ⟨80544, by rfl⟩ : syracuseStep 3436565 = 161089) (by norm_num)
theorem B2291043 : Blo 2289435 2291043 := bstep (se 1 (by rfl) ⟨1718282, by rfl⟩ : syracuseStep 2291043 = 3436565) B3436565
theorem B3306565 : Blo 2289435 3306565 := bbase (se 4 (by rfl) ⟨309990, by rfl⟩ : syracuseStep 3306565 = 619981) (by norm_num)
theorem B4408753 : Blo 2289435 4408753 := bstep (se 2 (by rfl) ⟨1653282, by rfl⟩ : syracuseStep 4408753 = 3306565) B3306565
theorem B5878337 : Blo 2289435 5878337 := bstep (se 2 (by rfl) ⟨2204376, by rfl⟩ : syracuseStep 5878337 = 4408753) B4408753
theorem B62702261 : Blo 2289435 62702261 := bstep (se 5 (by rfl) ⟨2939168, by rfl⟩ : syracuseStep 62702261 = 5878337) B5878337
theorem B41801507 : Blo 2289435 41801507 := bstep (se 1 (by rfl) ⟨31351130, by rfl⟩ : syracuseStep 41801507 = 62702261) B62702261
theorem B27867671 : Blo 2289435 27867671 := bstep (se 1 (by rfl) ⟨20900753, by rfl⟩ : syracuseStep 27867671 = 41801507) B41801507
theorem B18578447 : Blo 2289435 18578447 := bstep (se 1 (by rfl) ⟨13933835, by rfl⟩ : syracuseStep 18578447 = 27867671) B27867671
theorem B12385631 : Blo 2289435 12385631 := bstep (se 1 (by rfl) ⟨9289223, by rfl⟩ : syracuseStep 12385631 = 18578447) B18578447
theorem B8257087 : Blo 2289435 8257087 := bstep (se 1 (by rfl) ⟨6192815, by rfl⟩ : syracuseStep 8257087 = 12385631) B12385631
theorem B11009449 : Blo 2289435 11009449 := bstep (se 2 (by rfl) ⟨4128543, by rfl⟩ : syracuseStep 11009449 = 8257087) B8257087
theorem B14679265 : Blo 2289435 14679265 := bstep (se 2 (by rfl) ⟨5504724, by rfl⟩ : syracuseStep 14679265 = 11009449) B11009449
theorem B19572353 : Blo 2289435 19572353 := bstep (se 2 (by rfl) ⟨7339632, by rfl⟩ : syracuseStep 19572353 = 14679265) B14679265
theorem B13048235 : Blo 2289435 13048235 := bstep (se 1 (by rfl) ⟨9786176, by rfl⟩ : syracuseStep 13048235 = 19572353) B19572353
theorem B8698823 : Blo 2289435 8698823 := bstep (se 1 (by rfl) ⟨6524117, by rfl⟩ : syracuseStep 8698823 = 13048235) B13048235
theorem B5799215 : Blo 2289435 5799215 := bstep (se 1 (by rfl) ⟨4349411, by rfl⟩ : syracuseStep 5799215 = 8698823) B8698823
theorem B3866143 : Blo 2289435 3866143 := bstep (se 1 (by rfl) ⟨2899607, by rfl⟩ : syracuseStep 3866143 = 5799215) B5799215
theorem B5154857 : Blo 2289435 5154857 := bstep (se 2 (by rfl) ⟨1933071, by rfl⟩ : syracuseStep 5154857 = 3866143) B3866143
theorem B3436571 : Blo 2289435 3436571 := bstep (se 1 (by rfl) ⟨2577428, by rfl⟩ : syracuseStep 3436571 = 5154857) B5154857
theorem B2291047 : Blo 2289435 2291047 := bstep (se 1 (by rfl) ⟨1718285, by rfl⟩ : syracuseStep 2291047 = 3436571) B3436571
theorem B2577433 : Blo 2289435 2577433 := bbase (se 2 (by rfl) ⟨966537, by rfl⟩ : syracuseStep 2577433 = 1933075) (by norm_num)
theorem B3436577 : Blo 2289435 3436577 := bstep (se 2 (by rfl) ⟨1288716, by rfl⟩ : syracuseStep 3436577 = 2577433) B2577433
theorem B2291051 : Blo 2289435 2291051 := bstep (se 1 (by rfl) ⟨1718288, by rfl⟩ : syracuseStep 2291051 = 3436577) B3436577
theorem B8698853 : Blo 2289435 8698853 := bbase (se 4 (by rfl) ⟨815517, by rfl⟩ : syracuseStep 8698853 = 1631035) (by norm_num)
theorem B5799235 : Blo 2289435 5799235 := bstep (se 1 (by rfl) ⟨4349426, by rfl⟩ : syracuseStep 5799235 = 8698853) B8698853
theorem B7732313 : Blo 2289435 7732313 := bstep (se 2 (by rfl) ⟨2899617, by rfl⟩ : syracuseStep 7732313 = 5799235) B5799235
theorem B5154875 : Blo 2289435 5154875 := bstep (se 1 (by rfl) ⟨3866156, by rfl⟩ : syracuseStep 5154875 = 7732313) B7732313
theorem B3436583 : Blo 2289435 3436583 := bstep (se 1 (by rfl) ⟨2577437, by rfl⟩ : syracuseStep 3436583 = 5154875) B5154875
theorem B2291055 : Blo 2289435 2291055 := bstep (se 1 (by rfl) ⟨1718291, by rfl⟩ : syracuseStep 2291055 = 3436583) B3436583
theorem B3436589 : Blo 2289435 3436589 := bbase (se 3 (by rfl) ⟨644360, by rfl⟩ : syracuseStep 3436589 = 1288721) (by norm_num)
theorem B2291059 : Blo 2289435 2291059 := bstep (se 1 (by rfl) ⟨1718294, by rfl⟩ : syracuseStep 2291059 = 3436589) B3436589
theorem B5154893 : Blo 2289435 5154893 := bbase (se 3 (by rfl) ⟨966542, by rfl⟩ : syracuseStep 5154893 = 1933085) (by norm_num)
theorem B3436595 : Blo 2289435 3436595 := bstep (se 1 (by rfl) ⟨2577446, by rfl⟩ : syracuseStep 3436595 = 5154893) B5154893
theorem B2291063 : Blo 2289435 2291063 := bstep (se 1 (by rfl) ⟨1718297, by rfl⟩ : syracuseStep 2291063 = 3436595) B3436595
theorem B2899633 : Blo 2289435 2899633 := bbase (se 2 (by rfl) ⟨1087362, by rfl⟩ : syracuseStep 2899633 = 2174725) (by norm_num)
theorem B3866177 : Blo 2289435 3866177 := bstep (se 2 (by rfl) ⟨1449816, by rfl⟩ : syracuseStep 3866177 = 2899633) B2899633
theorem B2577451 : Blo 2289435 2577451 := bstep (se 1 (by rfl) ⟨1933088, by rfl⟩ : syracuseStep 2577451 = 3866177) B3866177
theorem B3436601 : Blo 2289435 3436601 := bstep (se 2 (by rfl) ⟨1288725, by rfl⟩ : syracuseStep 3436601 = 2577451) B2577451
theorem B2291067 : Blo 2289435 2291067 := bstep (se 1 (by rfl) ⟨1718300, by rfl⟩ : syracuseStep 2291067 = 3436601) B3436601
theorem B4644661 : Blo 2289435 4644661 := bbase (se 5 (by rfl) ⟨217718, by rfl⟩ : syracuseStep 4644661 = 435437) (by norm_num)
theorem B6192881 : Blo 2289435 6192881 := bstep (se 2 (by rfl) ⟨2322330, by rfl⟩ : syracuseStep 6192881 = 4644661) B4644661
theorem B4128587 : Blo 2289435 4128587 := bstep (se 1 (by rfl) ⟨3096440, by rfl⟩ : syracuseStep 4128587 = 6192881) B6192881
theorem B2752391 : Blo 2289435 2752391 := bstep (se 1 (by rfl) ⟨2064293, by rfl⟩ : syracuseStep 2752391 = 4128587) B4128587
theorem B7339709 : Blo 2289435 7339709 := bstep (se 3 (by rfl) ⟨1376195, by rfl⟩ : syracuseStep 7339709 = 2752391) B2752391
theorem B4893139 : Blo 2289435 4893139 := bstep (se 1 (by rfl) ⟨3669854, by rfl⟩ : syracuseStep 4893139 = 7339709) B7339709
theorem B26096741 : Blo 2289435 26096741 := bstep (se 4 (by rfl) ⟨2446569, by rfl⟩ : syracuseStep 26096741 = 4893139) B4893139
theorem B17397827 : Blo 2289435 17397827 := bstep (se 1 (by rfl) ⟨13048370, by rfl⟩ : syracuseStep 17397827 = 26096741) B26096741
theorem B11598551 : Blo 2289435 11598551 := bstep (se 1 (by rfl) ⟨8698913, by rfl⟩ : syracuseStep 11598551 = 17397827) B17397827
theorem B7732367 : Blo 2289435 7732367 := bstep (se 1 (by rfl) ⟨5799275, by rfl⟩ : syracuseStep 7732367 = 11598551) B11598551
theorem B5154911 : Blo 2289435 5154911 := bstep (se 1 (by rfl) ⟨3866183, by rfl⟩ : syracuseStep 5154911 = 7732367) B7732367
theorem B3436607 : Blo 2289435 3436607 := bstep (se 1 (by rfl) ⟨2577455, by rfl⟩ : syracuseStep 3436607 = 5154911) B5154911
theorem B2291071 : Blo 2289435 2291071 := bstep (se 1 (by rfl) ⟨1718303, by rfl⟩ : syracuseStep 2291071 = 3436607) B3436607
theorem B3436613 : Blo 2289435 3436613 := bbase (se 4 (by rfl) ⟨322182, by rfl⟩ : syracuseStep 3436613 = 644365) (by norm_num)
theorem B2291075 : Blo 2289435 2291075 := bstep (se 1 (by rfl) ⟨1718306, by rfl⟩ : syracuseStep 2291075 = 3436613) B3436613
theorem B3866197 : Blo 2289435 3866197 := bbase (se 8 (by rfl) ⟨22653, by rfl⟩ : syracuseStep 3866197 = 45307) (by norm_num)
theorem B5154929 : Blo 2289435 5154929 := bstep (se 2 (by rfl) ⟨1933098, by rfl⟩ : syracuseStep 5154929 = 3866197) B3866197
theorem B3436619 : Blo 2289435 3436619 := bstep (se 1 (by rfl) ⟨2577464, by rfl⟩ : syracuseStep 3436619 = 5154929) B5154929
theorem B2291079 : Blo 2289435 2291079 := bstep (se 1 (by rfl) ⟨1718309, by rfl⟩ : syracuseStep 2291079 = 3436619) B3436619
theorem B2577469 : Blo 2289435 2577469 := bbase (se 3 (by rfl) ⟨483275, by rfl⟩ : syracuseStep 2577469 = 966551) (by norm_num)
theorem B3436625 : Blo 2289435 3436625 := bstep (se 2 (by rfl) ⟨1288734, by rfl⟩ : syracuseStep 3436625 = 2577469) B2577469
theorem B2291083 : Blo 2289435 2291083 := bstep (se 1 (by rfl) ⟨1718312, by rfl⟩ : syracuseStep 2291083 = 3436625) B3436625
theorem B7732421 : Blo 2289435 7732421 := bbase (se 4 (by rfl) ⟨724914, by rfl⟩ : syracuseStep 7732421 = 1449829) (by norm_num)
theorem B5154947 : Blo 2289435 5154947 := bstep (se 1 (by rfl) ⟨3866210, by rfl⟩ : syracuseStep 5154947 = 7732421) B7732421
theorem B3436631 : Blo 2289435 3436631 := bstep (se 1 (by rfl) ⟨2577473, by rfl⟩ : syracuseStep 3436631 = 5154947) B5154947
theorem B2291087 : Blo 2289435 2291087 := bstep (se 1 (by rfl) ⟨1718315, by rfl⟩ : syracuseStep 2291087 = 3436631) B3436631
theorem B3436637 : Blo 2289435 3436637 := bbase (se 3 (by rfl) ⟨644369, by rfl⟩ : syracuseStep 3436637 = 1288739) (by norm_num)
theorem B2291091 : Blo 2289435 2291091 := bstep (se 1 (by rfl) ⟨1718318, by rfl⟩ : syracuseStep 2291091 = 3436637) B3436637
theorem B5154965 : Blo 2289435 5154965 := bbase (se 6 (by rfl) ⟨120819, by rfl⟩ : syracuseStep 5154965 = 241639) (by norm_num)
theorem B3436643 : Blo 2289435 3436643 := bstep (se 1 (by rfl) ⟨2577482, by rfl⟩ : syracuseStep 3436643 = 5154965) B5154965
theorem B2291095 : Blo 2289435 2291095 := bstep (se 1 (by rfl) ⟨1718321, by rfl⟩ : syracuseStep 2291095 = 3436643) B3436643
theorem B3262133 : Blo 2289435 3262133 := bbase (se 5 (by rfl) ⟨152912, by rfl⟩ : syracuseStep 3262133 = 305825) (by norm_num)
theorem B8699021 : Blo 2289435 8699021 := bstep (se 3 (by rfl) ⟨1631066, by rfl⟩ : syracuseStep 8699021 = 3262133) B3262133
theorem B5799347 : Blo 2289435 5799347 := bstep (se 1 (by rfl) ⟨4349510, by rfl⟩ : syracuseStep 5799347 = 8699021) B8699021
theorem B3866231 : Blo 2289435 3866231 := bstep (se 1 (by rfl) ⟨2899673, by rfl⟩ : syracuseStep 3866231 = 5799347) B5799347
theorem B2577487 : Blo 2289435 2577487 := bstep (se 1 (by rfl) ⟨1933115, by rfl⟩ : syracuseStep 2577487 = 3866231) B3866231
theorem B3436649 : Blo 2289435 3436649 := bstep (se 2 (by rfl) ⟨1288743, by rfl⟩ : syracuseStep 3436649 = 2577487) B2577487
theorem B2291099 : Blo 2289435 2291099 := bstep (se 1 (by rfl) ⟨1718324, by rfl⟩ : syracuseStep 2291099 = 3436649) B3436649
theorem B13226581 : Blo 2289435 13226581 := bbase (se 8 (by rfl) ⟨77499, by rfl⟩ : syracuseStep 13226581 = 154999) (by norm_num)
theorem B17635441 : Blo 2289435 17635441 := bstep (se 2 (by rfl) ⟨6613290, by rfl⟩ : syracuseStep 17635441 = 13226581) B13226581
theorem B23513921 : Blo 2289435 23513921 := bstep (se 2 (by rfl) ⟨8817720, by rfl⟩ : syracuseStep 23513921 = 17635441) B17635441
theorem B15675947 : Blo 2289435 15675947 := bstep (se 1 (by rfl) ⟨11756960, by rfl⟩ : syracuseStep 15675947 = 23513921) B23513921
theorem B10450631 : Blo 2289435 10450631 := bstep (se 1 (by rfl) ⟨7837973, by rfl⟩ : syracuseStep 10450631 = 15675947) B15675947
theorem B27868349 : Blo 2289435 27868349 := bstep (se 3 (by rfl) ⟨5225315, by rfl⟩ : syracuseStep 27868349 = 10450631) B10450631
theorem B18578899 : Blo 2289435 18578899 := bstep (se 1 (by rfl) ⟨13934174, by rfl⟩ : syracuseStep 18578899 = 27868349) B27868349
theorem B24771865 : Blo 2289435 24771865 := bstep (se 2 (by rfl) ⟨9289449, by rfl⟩ : syracuseStep 24771865 = 18578899) B18578899
theorem B33029153 : Blo 2289435 33029153 := bstep (se 2 (by rfl) ⟨12385932, by rfl⟩ : syracuseStep 33029153 = 24771865) B24771865
theorem B22019435 : Blo 2289435 22019435 := bstep (se 1 (by rfl) ⟨16514576, by rfl⟩ : syracuseStep 22019435 = 33029153) B33029153
theorem B14679623 : Blo 2289435 14679623 := bstep (se 1 (by rfl) ⟨11009717, by rfl⟩ : syracuseStep 14679623 = 22019435) B22019435
theorem B9786415 : Blo 2289435 9786415 := bstep (se 1 (by rfl) ⟨7339811, by rfl⟩ : syracuseStep 9786415 = 14679623) B14679623
theorem B13048553 : Blo 2289435 13048553 := bstep (se 2 (by rfl) ⟨4893207, by rfl⟩ : syracuseStep 13048553 = 9786415) B9786415
theorem B8699035 : Blo 2289435 8699035 := bstep (se 1 (by rfl) ⟨6524276, by rfl⟩ : syracuseStep 8699035 = 13048553) B13048553
theorem B11598713 : Blo 2289435 11598713 := bstep (se 2 (by rfl) ⟨4349517, by rfl⟩ : syracuseStep 11598713 = 8699035) B8699035
theorem B7732475 : Blo 2289435 7732475 := bstep (se 1 (by rfl) ⟨5799356, by rfl⟩ : syracuseStep 7732475 = 11598713) B11598713
theorem B5154983 : Blo 2289435 5154983 := bstep (se 1 (by rfl) ⟨3866237, by rfl⟩ : syracuseStep 5154983 = 7732475) B7732475
theorem B3436655 : Blo 2289435 3436655 := bstep (se 1 (by rfl) ⟨2577491, by rfl⟩ : syracuseStep 3436655 = 5154983) B5154983
theorem B2291103 : Blo 2289435 2291103 := bstep (se 1 (by rfl) ⟨1718327, by rfl⟩ : syracuseStep 2291103 = 3436655) B3436655
theorem B3436661 : Blo 2289435 3436661 := bbase (se 5 (by rfl) ⟨161093, by rfl⟩ : syracuseStep 3436661 = 322187) (by norm_num)
theorem B2291107 : Blo 2289435 2291107 := bstep (se 1 (by rfl) ⟨1718330, by rfl⟩ : syracuseStep 2291107 = 3436661) B3436661
theorem B4349533 : Blo 2289435 4349533 := bbase (se 3 (by rfl) ⟨815537, by rfl⟩ : syracuseStep 4349533 = 1631075) (by norm_num)
theorem B5799377 : Blo 2289435 5799377 := bstep (se 2 (by rfl) ⟨2174766, by rfl⟩ : syracuseStep 5799377 = 4349533) B4349533
theorem B3866251 : Blo 2289435 3866251 := bstep (se 1 (by rfl) ⟨2899688, by rfl⟩ : syracuseStep 3866251 = 5799377) B5799377
theorem B5155001 : Blo 2289435 5155001 := bstep (se 2 (by rfl) ⟨1933125, by rfl⟩ : syracuseStep 5155001 = 3866251) B3866251
theorem B3436667 : Blo 2289435 3436667 := bstep (se 1 (by rfl) ⟨2577500, by rfl⟩ : syracuseStep 3436667 = 5155001) B5155001
theorem B2291111 : Blo 2289435 2291111 := bstep (se 1 (by rfl) ⟨1718333, by rfl⟩ : syracuseStep 2291111 = 3436667) B3436667
theorem B2577505 : Blo 2289435 2577505 := bbase (se 2 (by rfl) ⟨966564, by rfl⟩ : syracuseStep 2577505 = 1933129) (by norm_num)
theorem B3436673 : Blo 2289435 3436673 := bstep (se 2 (by rfl) ⟨1288752, by rfl⟩ : syracuseStep 3436673 = 2577505) B2577505
theorem B2291115 : Blo 2289435 2291115 := bstep (se 1 (by rfl) ⟨1718336, by rfl⟩ : syracuseStep 2291115 = 3436673) B3436673
theorem B5799397 : Blo 2289435 5799397 := bbase (se 4 (by rfl) ⟨543693, by rfl⟩ : syracuseStep 5799397 = 1087387) (by norm_num)
theorem B7732529 : Blo 2289435 7732529 := bstep (se 2 (by rfl) ⟨2899698, by rfl⟩ : syracuseStep 7732529 = 5799397) B5799397
theorem B5155019 : Blo 2289435 5155019 := bstep (se 1 (by rfl) ⟨3866264, by rfl⟩ : syracuseStep 5155019 = 7732529) B7732529
theorem B3436679 : Blo 2289435 3436679 := bstep (se 1 (by rfl) ⟨2577509, by rfl⟩ : syracuseStep 3436679 = 5155019) B5155019
theorem B2291119 : Blo 2289435 2291119 := bstep (se 1 (by rfl) ⟨1718339, by rfl⟩ : syracuseStep 2291119 = 3436679) B3436679
theorem B3436685 : Blo 2289435 3436685 := bbase (se 3 (by rfl) ⟨644378, by rfl⟩ : syracuseStep 3436685 = 1288757) (by norm_num)
theorem B2291123 : Blo 2289435 2291123 := bstep (se 1 (by rfl) ⟨1718342, by rfl⟩ : syracuseStep 2291123 = 3436685) B3436685
theorem B5155037 : Blo 2289435 5155037 := bbase (se 3 (by rfl) ⟨966569, by rfl⟩ : syracuseStep 5155037 = 1933139) (by norm_num)
theorem B3436691 : Blo 2289435 3436691 := bstep (se 1 (by rfl) ⟨2577518, by rfl⟩ : syracuseStep 3436691 = 5155037) B5155037
theorem B2291127 : Blo 2289435 2291127 := bstep (se 1 (by rfl) ⟨1718345, by rfl⟩ : syracuseStep 2291127 = 3436691) B3436691
theorem B3866285 : Blo 2289435 3866285 := bbase (se 3 (by rfl) ⟨724928, by rfl⟩ : syracuseStep 3866285 = 1449857) (by norm_num)
theorem B2577523 : Blo 2289435 2577523 := bstep (se 1 (by rfl) ⟨1933142, by rfl⟩ : syracuseStep 2577523 = 3866285) B3866285
theorem B3436697 : Blo 2289435 3436697 := bstep (se 2 (by rfl) ⟨1288761, by rfl⟩ : syracuseStep 3436697 = 2577523) B2577523
theorem B2291131 : Blo 2289435 2291131 := bstep (se 1 (by rfl) ⟨1718348, by rfl⟩ : syracuseStep 2291131 = 3436697) B3436697
theorem B74316629 : Blo 2289435 74316629 := bbase (se 9 (by rfl) ⟨217724, by rfl⟩ : syracuseStep 74316629 = 435449) (by norm_num)
theorem B49544419 : Blo 2289435 49544419 := bstep (se 1 (by rfl) ⟨37158314, by rfl⟩ : syracuseStep 49544419 = 74316629) B74316629
theorem B66059225 : Blo 2289435 66059225 := bstep (se 2 (by rfl) ⟨24772209, by rfl⟩ : syracuseStep 66059225 = 49544419) B49544419
theorem B44039483 : Blo 2289435 44039483 := bstep (se 1 (by rfl) ⟨33029612, by rfl⟩ : syracuseStep 44039483 = 66059225) B66059225
theorem B29359655 : Blo 2289435 29359655 := bstep (se 1 (by rfl) ⟨22019741, by rfl⟩ : syracuseStep 29359655 = 44039483) B44039483
theorem B19573103 : Blo 2289435 19573103 := bstep (se 1 (by rfl) ⟨14679827, by rfl⟩ : syracuseStep 19573103 = 29359655) B29359655
theorem B13048735 : Blo 2289435 13048735 := bstep (se 1 (by rfl) ⟨9786551, by rfl⟩ : syracuseStep 13048735 = 19573103) B19573103
theorem B17398313 : Blo 2289435 17398313 := bstep (se 2 (by rfl) ⟨6524367, by rfl⟩ : syracuseStep 17398313 = 13048735) B13048735
theorem B11598875 : Blo 2289435 11598875 := bstep (se 1 (by rfl) ⟨8699156, by rfl⟩ : syracuseStep 11598875 = 17398313) B17398313
theorem B7732583 : Blo 2289435 7732583 := bstep (se 1 (by rfl) ⟨5799437, by rfl⟩ : syracuseStep 7732583 = 11598875) B11598875
theorem B5155055 : Blo 2289435 5155055 := bstep (se 1 (by rfl) ⟨3866291, by rfl⟩ : syracuseStep 5155055 = 7732583) B7732583
theorem B3436703 : Blo 2289435 3436703 := bstep (se 1 (by rfl) ⟨2577527, by rfl⟩ : syracuseStep 3436703 = 5155055) B5155055
theorem B2291135 : Blo 2289435 2291135 := bstep (se 1 (by rfl) ⟨1718351, by rfl⟩ : syracuseStep 2291135 = 3436703) B3436703
theorem B3436709 : Blo 2289435 3436709 := bbase (se 4 (by rfl) ⟨322191, by rfl⟩ : syracuseStep 3436709 = 644383) (by norm_num)
theorem B2291139 : Blo 2289435 2291139 := bstep (se 1 (by rfl) ⟨1718354, by rfl⟩ : syracuseStep 2291139 = 3436709) B3436709
theorem B2899729 : Blo 2289435 2899729 := bbase (se 2 (by rfl) ⟨1087398, by rfl⟩ : syracuseStep 2899729 = 2174797) (by norm_num)
theorem B3866305 : Blo 2289435 3866305 := bstep (se 2 (by rfl) ⟨1449864, by rfl⟩ : syracuseStep 3866305 = 2899729) B2899729
theorem B5155073 : Blo 2289435 5155073 := bstep (se 2 (by rfl) ⟨1933152, by rfl⟩ : syracuseStep 5155073 = 3866305) B3866305
theorem B3436715 : Blo 2289435 3436715 := bstep (se 1 (by rfl) ⟨2577536, by rfl⟩ : syracuseStep 3436715 = 5155073) B5155073
theorem B2291143 : Blo 2289435 2291143 := bstep (se 1 (by rfl) ⟨1718357, by rfl⟩ : syracuseStep 2291143 = 3436715) B3436715
theorem B2577541 : Blo 2289435 2577541 := bbase (se 4 (by rfl) ⟨241644, by rfl⟩ : syracuseStep 2577541 = 483289) (by norm_num)
theorem B3436721 : Blo 2289435 3436721 := bstep (se 2 (by rfl) ⟨1288770, by rfl⟩ : syracuseStep 3436721 = 2577541) B2577541
theorem B2291147 : Blo 2289435 2291147 := bstep (se 1 (by rfl) ⟨1718360, by rfl⟩ : syracuseStep 2291147 = 3436721) B3436721
theorem B3138797 : Blo 2289435 3138797 := bbase (se 3 (by rfl) ⟨588524, by rfl⟩ : syracuseStep 3138797 = 1177049) (by norm_num)
theorem B8370125 : Blo 2289435 8370125 := bstep (se 3 (by rfl) ⟨1569398, by rfl⟩ : syracuseStep 8370125 = 3138797) B3138797
theorem B5580083 : Blo 2289435 5580083 := bstep (se 1 (by rfl) ⟨4185062, by rfl⟩ : syracuseStep 5580083 = 8370125) B8370125
theorem B3720055 : Blo 2289435 3720055 := bstep (se 1 (by rfl) ⟨2790041, by rfl⟩ : syracuseStep 3720055 = 5580083) B5580083
theorem B4960073 : Blo 2289435 4960073 := bstep (se 2 (by rfl) ⟨1860027, by rfl⟩ : syracuseStep 4960073 = 3720055) B3720055
theorem B13226861 : Blo 2289435 13226861 := bstep (se 3 (by rfl) ⟨2480036, by rfl⟩ : syracuseStep 13226861 = 4960073) B4960073
theorem B35271629 : Blo 2289435 35271629 := bstep (se 3 (by rfl) ⟨6613430, by rfl⟩ : syracuseStep 35271629 = 13226861) B13226861
theorem B23514419 : Blo 2289435 23514419 := bstep (se 1 (by rfl) ⟨17635814, by rfl⟩ : syracuseStep 23514419 = 35271629) B35271629
theorem B62705117 : Blo 2289435 62705117 := bstep (se 3 (by rfl) ⟨11757209, by rfl⟩ : syracuseStep 62705117 = 23514419) B23514419
theorem B41803411 : Blo 2289435 41803411 := bstep (se 1 (by rfl) ⟨31352558, by rfl⟩ : syracuseStep 41803411 = 62705117) B62705117
theorem B55737881 : Blo 2289435 55737881 := bstep (se 2 (by rfl) ⟨20901705, by rfl⟩ : syracuseStep 55737881 = 41803411) B41803411
theorem B37158587 : Blo 2289435 37158587 := bstep (se 1 (by rfl) ⟨27868940, by rfl⟩ : syracuseStep 37158587 = 55737881) B55737881
theorem B24772391 : Blo 2289435 24772391 := bstep (se 1 (by rfl) ⟨18579293, by rfl⟩ : syracuseStep 24772391 = 37158587) B37158587
theorem B16514927 : Blo 2289435 16514927 := bstep (se 1 (by rfl) ⟨12386195, by rfl⟩ : syracuseStep 16514927 = 24772391) B24772391
theorem B11009951 : Blo 2289435 11009951 := bstep (se 1 (by rfl) ⟨8257463, by rfl⟩ : syracuseStep 11009951 = 16514927) B16514927
theorem B7339967 : Blo 2289435 7339967 := bstep (se 1 (by rfl) ⟨5504975, by rfl⟩ : syracuseStep 7339967 = 11009951) B11009951
theorem B4893311 : Blo 2289435 4893311 := bstep (se 1 (by rfl) ⟨3669983, by rfl⟩ : syracuseStep 4893311 = 7339967) B7339967
theorem B3262207 : Blo 2289435 3262207 := bstep (se 1 (by rfl) ⟨2446655, by rfl⟩ : syracuseStep 3262207 = 4893311) B4893311
theorem B4349609 : Blo 2289435 4349609 := bstep (se 2 (by rfl) ⟨1631103, by rfl⟩ : syracuseStep 4349609 = 3262207) B3262207
theorem B2899739 : Blo 2289435 2899739 := bstep (se 1 (by rfl) ⟨2174804, by rfl⟩ : syracuseStep 2899739 = 4349609) B4349609
theorem B7732637 : Blo 2289435 7732637 := bstep (se 3 (by rfl) ⟨1449869, by rfl⟩ : syracuseStep 7732637 = 2899739) B2899739
theorem B5155091 : Blo 2289435 5155091 := bstep (se 1 (by rfl) ⟨3866318, by rfl⟩ : syracuseStep 5155091 = 7732637) B7732637
theorem B3436727 : Blo 2289435 3436727 := bstep (se 1 (by rfl) ⟨2577545, by rfl⟩ : syracuseStep 3436727 = 5155091) B5155091
theorem B2291151 : Blo 2289435 2291151 := bstep (se 1 (by rfl) ⟨1718363, by rfl⟩ : syracuseStep 2291151 = 3436727) B3436727
theorem B3436733 : Blo 2289435 3436733 := bbase (se 3 (by rfl) ⟨644387, by rfl⟩ : syracuseStep 3436733 = 1288775) (by norm_num)
theorem B2291155 : Blo 2289435 2291155 := bstep (se 1 (by rfl) ⟨1718366, by rfl⟩ : syracuseStep 2291155 = 3436733) B3436733
theorem B5155109 : Blo 2289435 5155109 := bbase (se 4 (by rfl) ⟨483291, by rfl⟩ : syracuseStep 5155109 = 966583) (by norm_num)
theorem B3436739 : Blo 2289435 3436739 := bstep (se 1 (by rfl) ⟨2577554, by rfl⟩ : syracuseStep 3436739 = 5155109) B5155109
theorem B2291159 : Blo 2289435 2291159 := bstep (se 1 (by rfl) ⟨1718369, by rfl⟩ : syracuseStep 2291159 = 3436739) B3436739
theorem B5799509 : Blo 2289435 5799509 := bbase (se 8 (by rfl) ⟨33981, by rfl⟩ : syracuseStep 5799509 = 67963) (by norm_num)
theorem B3866339 : Blo 2289435 3866339 := bstep (se 1 (by rfl) ⟨2899754, by rfl⟩ : syracuseStep 3866339 = 5799509) B5799509
theorem B2577559 : Blo 2289435 2577559 := bstep (se 1 (by rfl) ⟨1933169, by rfl⟩ : syracuseStep 2577559 = 3866339) B3866339
theorem B3436745 : Blo 2289435 3436745 := bstep (se 2 (by rfl) ⟨1288779, by rfl⟩ : syracuseStep 3436745 = 2577559) B2577559
theorem B2291163 : Blo 2289435 2291163 := bstep (se 1 (by rfl) ⟨1718372, by rfl⟩ : syracuseStep 2291163 = 3436745) B3436745
theorem B5505013 : Blo 2289435 5505013 := bbase (se 5 (by rfl) ⟨258047, by rfl⟩ : syracuseStep 5505013 = 516095) (by norm_num)
theorem B7340017 : Blo 2289435 7340017 := bstep (se 2 (by rfl) ⟨2752506, by rfl⟩ : syracuseStep 7340017 = 5505013) B5505013
theorem B9786689 : Blo 2289435 9786689 := bstep (se 2 (by rfl) ⟨3670008, by rfl⟩ : syracuseStep 9786689 = 7340017) B7340017
theorem B6524459 : Blo 2289435 6524459 := bstep (se 1 (by rfl) ⟨4893344, by rfl⟩ : syracuseStep 6524459 = 9786689) B9786689
theorem B4349639 : Blo 2289435 4349639 := bstep (se 1 (by rfl) ⟨3262229, by rfl⟩ : syracuseStep 4349639 = 6524459) B6524459
theorem B11599037 : Blo 2289435 11599037 := bstep (se 3 (by rfl) ⟨2174819, by rfl⟩ : syracuseStep 11599037 = 4349639) B4349639
theorem B7732691 : Blo 2289435 7732691 := bstep (se 1 (by rfl) ⟨5799518, by rfl⟩ : syracuseStep 7732691 = 11599037) B11599037
theorem B5155127 : Blo 2289435 5155127 := bstep (se 1 (by rfl) ⟨3866345, by rfl⟩ : syracuseStep 5155127 = 7732691) B7732691
theorem B3436751 : Blo 2289435 3436751 := bstep (se 1 (by rfl) ⟨2577563, by rfl⟩ : syracuseStep 3436751 = 5155127) B5155127
theorem B2291167 : Blo 2289435 2291167 := bstep (se 1 (by rfl) ⟨1718375, by rfl⟩ : syracuseStep 2291167 = 3436751) B3436751
theorem B3436757 : Blo 2289435 3436757 := bbase (se 7 (by rfl) ⟨40274, by rfl⟩ : syracuseStep 3436757 = 80549) (by norm_num)
theorem B2291171 : Blo 2289435 2291171 := bstep (se 1 (by rfl) ⟨1718378, by rfl⟩ : syracuseStep 2291171 = 3436757) B3436757
theorem B2446681 : Blo 2289435 2446681 := bbase (se 2 (by rfl) ⟨917505, by rfl⟩ : syracuseStep 2446681 = 1835011) (by norm_num)
theorem B3262241 : Blo 2289435 3262241 := bstep (se 2 (by rfl) ⟨1223340, by rfl⟩ : syracuseStep 3262241 = 2446681) B2446681
theorem B8699309 : Blo 2289435 8699309 := bstep (se 3 (by rfl) ⟨1631120, by rfl⟩ : syracuseStep 8699309 = 3262241) B3262241
theorem B5799539 : Blo 2289435 5799539 := bstep (se 1 (by rfl) ⟨4349654, by rfl⟩ : syracuseStep 5799539 = 8699309) B8699309
theorem B3866359 : Blo 2289435 3866359 := bstep (se 1 (by rfl) ⟨2899769, by rfl⟩ : syracuseStep 3866359 = 5799539) B5799539
theorem B5155145 : Blo 2289435 5155145 := bstep (se 2 (by rfl) ⟨1933179, by rfl⟩ : syracuseStep 5155145 = 3866359) B3866359
theorem B3436763 : Blo 2289435 3436763 := bstep (se 1 (by rfl) ⟨2577572, by rfl⟩ : syracuseStep 3436763 = 5155145) B5155145
theorem B2291175 : Blo 2289435 2291175 := bstep (se 1 (by rfl) ⟨1718381, by rfl⟩ : syracuseStep 2291175 = 3436763) B3436763
theorem B2577577 : Blo 2289435 2577577 := bbase (se 2 (by rfl) ⟨966591, by rfl⟩ : syracuseStep 2577577 = 1933183) (by norm_num)
theorem B3436769 : Blo 2289435 3436769 := bstep (se 2 (by rfl) ⟨1288788, by rfl⟩ : syracuseStep 3436769 = 2577577) B2577577
theorem B2291179 : Blo 2289435 2291179 := bstep (se 1 (by rfl) ⟨1718384, by rfl⟩ : syracuseStep 2291179 = 3436769) B3436769
theorem B9786757 : Blo 2289435 9786757 := bbase (se 4 (by rfl) ⟨917508, by rfl⟩ : syracuseStep 9786757 = 1835017) (by norm_num)
theorem B13049009 : Blo 2289435 13049009 := bstep (se 2 (by rfl) ⟨4893378, by rfl⟩ : syracuseStep 13049009 = 9786757) B9786757
theorem B8699339 : Blo 2289435 8699339 := bstep (se 1 (by rfl) ⟨6524504, by rfl⟩ : syracuseStep 8699339 = 13049009) B13049009
theorem B5799559 : Blo 2289435 5799559 := bstep (se 1 (by rfl) ⟨4349669, by rfl⟩ : syracuseStep 5799559 = 8699339) B8699339
theorem B7732745 : Blo 2289435 7732745 := bstep (se 2 (by rfl) ⟨2899779, by rfl⟩ : syracuseStep 7732745 = 5799559) B5799559
theorem B5155163 : Blo 2289435 5155163 := bstep (se 1 (by rfl) ⟨3866372, by rfl⟩ : syracuseStep 5155163 = 7732745) B7732745
theorem B3436775 : Blo 2289435 3436775 := bstep (se 1 (by rfl) ⟨2577581, by rfl⟩ : syracuseStep 3436775 = 5155163) B5155163
theorem B2291183 : Blo 2289435 2291183 := bstep (se 1 (by rfl) ⟨1718387, by rfl⟩ : syracuseStep 2291183 = 3436775) B3436775
theorem B3436781 : Blo 2289435 3436781 := bbase (se 3 (by rfl) ⟨644396, by rfl⟩ : syracuseStep 3436781 = 1288793) (by norm_num)
theorem B2291187 : Blo 2289435 2291187 := bstep (se 1 (by rfl) ⟨1718390, by rfl⟩ : syracuseStep 2291187 = 3436781) B3436781
theorem B5155181 : Blo 2289435 5155181 := bbase (se 3 (by rfl) ⟨966596, by rfl⟩ : syracuseStep 5155181 = 1933193) (by norm_num)
theorem B3436787 : Blo 2289435 3436787 := bstep (se 1 (by rfl) ⟨2577590, by rfl⟩ : syracuseStep 3436787 = 5155181) B5155181
theorem B2291191 : Blo 2289435 2291191 := bstep (se 1 (by rfl) ⟨1718393, by rfl⟩ : syracuseStep 2291191 = 3436787) B3436787
theorem B4349693 : Blo 2289435 4349693 := bbase (se 3 (by rfl) ⟨815567, by rfl⟩ : syracuseStep 4349693 = 1631135) (by norm_num)
theorem B2899795 : Blo 2289435 2899795 := bstep (se 1 (by rfl) ⟨2174846, by rfl⟩ : syracuseStep 2899795 = 4349693) B4349693
theorem B3866393 : Blo 2289435 3866393 := bstep (se 2 (by rfl) ⟨1449897, by rfl⟩ : syracuseStep 3866393 = 2899795) B2899795
theorem B2577595 : Blo 2289435 2577595 := bstep (se 1 (by rfl) ⟨1933196, by rfl⟩ : syracuseStep 2577595 = 3866393) B3866393
theorem B3436793 : Blo 2289435 3436793 := bstep (se 2 (by rfl) ⟨1288797, by rfl⟩ : syracuseStep 3436793 = 2577595) B2577595
theorem B2291195 : Blo 2289435 2291195 := bstep (se 1 (by rfl) ⟨1718396, by rfl⟩ : syracuseStep 2291195 = 3436793) B3436793
theorem B3096613 : Blo 2289435 3096613 := bbase (se 4 (by rfl) ⟨290307, by rfl⟩ : syracuseStep 3096613 = 580615) (by norm_num)
theorem B4128817 : Blo 2289435 4128817 := bstep (se 2 (by rfl) ⟨1548306, by rfl⟩ : syracuseStep 4128817 = 3096613) B3096613
theorem B5505089 : Blo 2289435 5505089 := bstep (se 2 (by rfl) ⟨2064408, by rfl⟩ : syracuseStep 5505089 = 4128817) B4128817
theorem B58720949 : Blo 2289435 58720949 := bstep (se 5 (by rfl) ⟨2752544, by rfl⟩ : syracuseStep 58720949 = 5505089) B5505089
theorem B39147299 : Blo 2289435 39147299 := bstep (se 1 (by rfl) ⟨29360474, by rfl⟩ : syracuseStep 39147299 = 58720949) B58720949
theorem B26098199 : Blo 2289435 26098199 := bstep (se 1 (by rfl) ⟨19573649, by rfl⟩ : syracuseStep 26098199 = 39147299) B39147299
theorem B17398799 : Blo 2289435 17398799 := bstep (se 1 (by rfl) ⟨13049099, by rfl⟩ : syracuseStep 17398799 = 26098199) B26098199
theorem B11599199 : Blo 2289435 11599199 := bstep (se 1 (by rfl) ⟨8699399, by rfl⟩ : syracuseStep 11599199 = 17398799) B17398799
theorem B7732799 : Blo 2289435 7732799 := bstep (se 1 (by rfl) ⟨5799599, by rfl⟩ : syracuseStep 7732799 = 11599199) B11599199
theorem B5155199 : Blo 2289435 5155199 := bstep (se 1 (by rfl) ⟨3866399, by rfl⟩ : syracuseStep 5155199 = 7732799) B7732799
theorem B3436799 : Blo 2289435 3436799 := bstep (se 1 (by rfl) ⟨2577599, by rfl⟩ : syracuseStep 3436799 = 5155199) B5155199
theorem B2291199 : Blo 2289435 2291199 := bstep (se 1 (by rfl) ⟨1718399, by rfl⟩ : syracuseStep 2291199 = 3436799) B3436799
theorem B3436805 : Blo 2289435 3436805 := bbase (se 4 (by rfl) ⟨322200, by rfl⟩ : syracuseStep 3436805 = 644401) (by norm_num)
theorem B2291203 : Blo 2289435 2291203 := bstep (se 1 (by rfl) ⟨1718402, by rfl⟩ : syracuseStep 2291203 = 3436805) B3436805
theorem B3866413 : Blo 2289435 3866413 := bbase (se 3 (by rfl) ⟨724952, by rfl⟩ : syracuseStep 3866413 = 1449905) (by norm_num)
theorem B5155217 : Blo 2289435 5155217 := bstep (se 2 (by rfl) ⟨1933206, by rfl⟩ : syracuseStep 5155217 = 3866413) B3866413
theorem B3436811 : Blo 2289435 3436811 := bstep (se 1 (by rfl) ⟨2577608, by rfl⟩ : syracuseStep 3436811 = 5155217) B5155217
theorem B2291207 : Blo 2289435 2291207 := bstep (se 1 (by rfl) ⟨1718405, by rfl⟩ : syracuseStep 2291207 = 3436811) B3436811
theorem B2577613 : Blo 2289435 2577613 := bbase (se 3 (by rfl) ⟨483302, by rfl⟩ : syracuseStep 2577613 = 966605) (by norm_num)
theorem B3436817 : Blo 2289435 3436817 := bstep (se 2 (by rfl) ⟨1288806, by rfl⟩ : syracuseStep 3436817 = 2577613) B2577613
theorem B2291211 : Blo 2289435 2291211 := bstep (se 1 (by rfl) ⟨1718408, by rfl⟩ : syracuseStep 2291211 = 3436817) B3436817
theorem B7732853 : Blo 2289435 7732853 := bbase (se 5 (by rfl) ⟨362477, by rfl⟩ : syracuseStep 7732853 = 724955) (by norm_num)
theorem B5155235 : Blo 2289435 5155235 := bstep (se 1 (by rfl) ⟨3866426, by rfl⟩ : syracuseStep 5155235 = 7732853) B7732853
theorem B3436823 : Blo 2289435 3436823 := bstep (se 1 (by rfl) ⟨2577617, by rfl⟩ : syracuseStep 3436823 = 5155235) B5155235
theorem B2291215 : Blo 2289435 2291215 := bstep (se 1 (by rfl) ⟨1718411, by rfl⟩ : syracuseStep 2291215 = 3436823) B3436823
theorem B3436829 : Blo 2289435 3436829 := bbase (se 3 (by rfl) ⟨644405, by rfl⟩ : syracuseStep 3436829 = 1288811) (by norm_num)
theorem B2291219 : Blo 2289435 2291219 := bstep (se 1 (by rfl) ⟨1718414, by rfl⟩ : syracuseStep 2291219 = 3436829) B3436829
theorem B5155253 : Blo 2289435 5155253 := bbase (se 5 (by rfl) ⟨241652, by rfl⟩ : syracuseStep 5155253 = 483305) (by norm_num)
theorem B3436835 : Blo 2289435 3436835 := bstep (se 1 (by rfl) ⟨2577626, by rfl⟩ : syracuseStep 3436835 = 5155253) B5155253
theorem B2291223 : Blo 2289435 2291223 := bstep (se 1 (by rfl) ⟨1718417, by rfl⟩ : syracuseStep 2291223 = 3436835) B3436835
theorem B4128869 : Blo 2289435 4128869 := bbase (se 4 (by rfl) ⟨387081, by rfl⟩ : syracuseStep 4128869 = 774163) (by norm_num)
theorem B2752579 : Blo 2289435 2752579 := bstep (se 1 (by rfl) ⟨2064434, by rfl⟩ : syracuseStep 2752579 = 4128869) B4128869
theorem B3670105 : Blo 2289435 3670105 := bstep (se 2 (by rfl) ⟨1376289, by rfl⟩ : syracuseStep 3670105 = 2752579) B2752579
theorem B4893473 : Blo 2289435 4893473 := bstep (se 2 (by rfl) ⟨1835052, by rfl⟩ : syracuseStep 4893473 = 3670105) B3670105
theorem B13049261 : Blo 2289435 13049261 := bstep (se 3 (by rfl) ⟨2446736, by rfl⟩ : syracuseStep 13049261 = 4893473) B4893473
theorem B8699507 : Blo 2289435 8699507 := bstep (se 1 (by rfl) ⟨6524630, by rfl⟩ : syracuseStep 8699507 = 13049261) B13049261
theorem B5799671 : Blo 2289435 5799671 := bstep (se 1 (by rfl) ⟨4349753, by rfl⟩ : syracuseStep 5799671 = 8699507) B8699507
theorem B3866447 : Blo 2289435 3866447 := bstep (se 1 (by rfl) ⟨2899835, by rfl⟩ : syracuseStep 3866447 = 5799671) B5799671
theorem B2577631 : Blo 2289435 2577631 := bstep (se 1 (by rfl) ⟨1933223, by rfl⟩ : syracuseStep 2577631 = 3866447) B3866447
theorem B3436841 : Blo 2289435 3436841 := bstep (se 2 (by rfl) ⟨1288815, by rfl⟩ : syracuseStep 3436841 = 2577631) B2577631
theorem B2291227 : Blo 2289435 2291227 := bstep (se 1 (by rfl) ⟨1718420, by rfl⟩ : syracuseStep 2291227 = 3436841) B3436841
theorem B7158901 : Blo 2289435 7158901 := bbase (se 5 (by rfl) ⟨335573, by rfl⟩ : syracuseStep 7158901 = 671147) (by norm_num)
theorem B9545201 : Blo 2289435 9545201 := bstep (se 2 (by rfl) ⟨3579450, by rfl⟩ : syracuseStep 9545201 = 7158901) B7158901
theorem B6363467 : Blo 2289435 6363467 := bstep (se 1 (by rfl) ⟨4772600, by rfl⟩ : syracuseStep 6363467 = 9545201) B9545201
theorem B4242311 : Blo 2289435 4242311 := bstep (se 1 (by rfl) ⟨3181733, by rfl⟩ : syracuseStep 4242311 = 6363467) B6363467
theorem B2828207 : Blo 2289435 2828207 := bstep (se 1 (by rfl) ⟨2121155, by rfl⟩ : syracuseStep 2828207 = 4242311) B4242311
theorem B7541885 : Blo 2289435 7541885 := bstep (se 3 (by rfl) ⟨1414103, by rfl⟩ : syracuseStep 7541885 = 2828207) B2828207
theorem B5027923 : Blo 2289435 5027923 := bstep (se 1 (by rfl) ⟨3770942, by rfl⟩ : syracuseStep 5027923 = 7541885) B7541885
theorem B6703897 : Blo 2289435 6703897 := bstep (se 2 (by rfl) ⟨2513961, by rfl⟩ : syracuseStep 6703897 = 5027923) B5027923
theorem B8938529 : Blo 2289435 8938529 := bstep (se 2 (by rfl) ⟨3351948, by rfl⟩ : syracuseStep 8938529 = 6703897) B6703897
theorem B5959019 : Blo 2289435 5959019 := bstep (se 1 (by rfl) ⟨4469264, by rfl⟩ : syracuseStep 5959019 = 8938529) B8938529
theorem B15890717 : Blo 2289435 15890717 := bstep (se 3 (by rfl) ⟨2979509, by rfl⟩ : syracuseStep 15890717 = 5959019) B5959019
theorem B10593811 : Blo 2289435 10593811 := bstep (se 1 (by rfl) ⟨7945358, by rfl⟩ : syracuseStep 10593811 = 15890717) B15890717
theorem B56500325 : Blo 2289435 56500325 := bstep (se 4 (by rfl) ⟨5296905, by rfl⟩ : syracuseStep 56500325 = 10593811) B10593811
theorem B37666883 : Blo 2289435 37666883 := bstep (se 1 (by rfl) ⟨28250162, by rfl⟩ : syracuseStep 37666883 = 56500325) B56500325
theorem B25111255 : Blo 2289435 25111255 := bstep (se 1 (by rfl) ⟨18833441, by rfl⟩ : syracuseStep 25111255 = 37666883) B37666883
theorem B33481673 : Blo 2289435 33481673 := bstep (se 2 (by rfl) ⟨12555627, by rfl⟩ : syracuseStep 33481673 = 25111255) B25111255
theorem B22321115 : Blo 2289435 22321115 := bstep (se 1 (by rfl) ⟨16740836, by rfl⟩ : syracuseStep 22321115 = 33481673) B33481673
theorem B14880743 : Blo 2289435 14880743 := bstep (se 1 (by rfl) ⟨11160557, by rfl⟩ : syracuseStep 14880743 = 22321115) B22321115
theorem B9920495 : Blo 2289435 9920495 := bstep (se 1 (by rfl) ⟨7440371, by rfl⟩ : syracuseStep 9920495 = 14880743) B14880743
theorem B6613663 : Blo 2289435 6613663 := bstep (se 1 (by rfl) ⟨4960247, by rfl⟩ : syracuseStep 6613663 = 9920495) B9920495
theorem B8818217 : Blo 2289435 8818217 := bstep (se 2 (by rfl) ⟨3306831, by rfl⟩ : syracuseStep 8818217 = 6613663) B6613663
theorem B5878811 : Blo 2289435 5878811 := bstep (se 1 (by rfl) ⟨4409108, by rfl⟩ : syracuseStep 5878811 = 8818217) B8818217
theorem B3919207 : Blo 2289435 3919207 := bstep (se 1 (by rfl) ⟨2939405, by rfl⟩ : syracuseStep 3919207 = 5878811) B5878811
theorem B5225609 : Blo 2289435 5225609 := bstep (se 2 (by rfl) ⟨1959603, by rfl⟩ : syracuseStep 5225609 = 3919207) B3919207
theorem B3483739 : Blo 2289435 3483739 := bstep (se 1 (by rfl) ⟨2612804, by rfl⟩ : syracuseStep 3483739 = 5225609) B5225609
theorem B18579941 : Blo 2289435 18579941 := bstep (se 4 (by rfl) ⟨1741869, by rfl⟩ : syracuseStep 18579941 = 3483739) B3483739
theorem B12386627 : Blo 2289435 12386627 := bstep (se 1 (by rfl) ⟨9289970, by rfl⟩ : syracuseStep 12386627 = 18579941) B18579941
theorem B8257751 : Blo 2289435 8257751 := bstep (se 1 (by rfl) ⟨6193313, by rfl⟩ : syracuseStep 8257751 = 12386627) B12386627
theorem B5505167 : Blo 2289435 5505167 := bstep (se 1 (by rfl) ⟨4128875, by rfl⟩ : syracuseStep 5505167 = 8257751) B8257751
theorem B3670111 : Blo 2289435 3670111 := bstep (se 1 (by rfl) ⟨2752583, by rfl⟩ : syracuseStep 3670111 = 5505167) B5505167
theorem B4893481 : Blo 2289435 4893481 := bstep (se 2 (by rfl) ⟨1835055, by rfl⟩ : syracuseStep 4893481 = 3670111) B3670111
theorem B6524641 : Blo 2289435 6524641 := bstep (se 2 (by rfl) ⟨2446740, by rfl⟩ : syracuseStep 6524641 = 4893481) B4893481
theorem B8699521 : Blo 2289435 8699521 := bstep (se 2 (by rfl) ⟨3262320, by rfl⟩ : syracuseStep 8699521 = 6524641) B6524641
theorem B11599361 : Blo 2289435 11599361 := bstep (se 2 (by rfl) ⟨4349760, by rfl⟩ : syracuseStep 11599361 = 8699521) B8699521
theorem B7732907 : Blo 2289435 7732907 := bstep (se 1 (by rfl) ⟨5799680, by rfl⟩ : syracuseStep 7732907 = 11599361) B11599361
theorem B5155271 : Blo 2289435 5155271 := bstep (se 1 (by rfl) ⟨3866453, by rfl⟩ : syracuseStep 5155271 = 7732907) B7732907
theorem B3436847 : Blo 2289435 3436847 := bstep (se 1 (by rfl) ⟨2577635, by rfl⟩ : syracuseStep 3436847 = 5155271) B5155271
theorem B2291231 : Blo 2289435 2291231 := bstep (se 1 (by rfl) ⟨1718423, by rfl⟩ : syracuseStep 2291231 = 3436847) B3436847
theorem B3436853 : Blo 2289435 3436853 := bbase (se 5 (by rfl) ⟨161102, by rfl⟩ : syracuseStep 3436853 = 322205) (by norm_num)
theorem B2291235 : Blo 2289435 2291235 := bstep (se 1 (by rfl) ⟨1718426, by rfl⟩ : syracuseStep 2291235 = 3436853) B3436853
theorem B5799701 : Blo 2289435 5799701 := bbase (se 6 (by rfl) ⟨135930, by rfl⟩ : syracuseStep 5799701 = 271861) (by norm_num)
theorem B3866467 : Blo 2289435 3866467 := bstep (se 1 (by rfl) ⟨2899850, by rfl⟩ : syracuseStep 3866467 = 5799701) B5799701
theorem B5155289 : Blo 2289435 5155289 := bstep (se 2 (by rfl) ⟨1933233, by rfl⟩ : syracuseStep 5155289 = 3866467) B3866467
theorem B3436859 : Blo 2289435 3436859 := bstep (se 1 (by rfl) ⟨2577644, by rfl⟩ : syracuseStep 3436859 = 5155289) B5155289
theorem B2291239 : Blo 2289435 2291239 := bstep (se 1 (by rfl) ⟨1718429, by rfl⟩ : syracuseStep 2291239 = 3436859) B3436859
theorem B2577649 : Blo 2289435 2577649 := bbase (se 2 (by rfl) ⟨966618, by rfl⟩ : syracuseStep 2577649 = 1933237) (by norm_num)
theorem B3436865 : Blo 2289435 3436865 := bstep (se 2 (by rfl) ⟨1288824, by rfl⟩ : syracuseStep 3436865 = 2577649) B2577649
theorem B2291243 : Blo 2289435 2291243 := bstep (se 1 (by rfl) ⟨1718432, by rfl⟩ : syracuseStep 2291243 = 3436865) B3436865
theorem B22020821 : Blo 2289435 22020821 := bbase (se 7 (by rfl) ⟨258056, by rfl⟩ : syracuseStep 22020821 = 516113) (by norm_num)
theorem B14680547 : Blo 2289435 14680547 := bstep (se 1 (by rfl) ⟨11010410, by rfl⟩ : syracuseStep 14680547 = 22020821) B22020821
theorem B9787031 : Blo 2289435 9787031 := bstep (se 1 (by rfl) ⟨7340273, by rfl⟩ : syracuseStep 9787031 = 14680547) B14680547
theorem B6524687 : Blo 2289435 6524687 := bstep (se 1 (by rfl) ⟨4893515, by rfl⟩ : syracuseStep 6524687 = 9787031) B9787031
theorem B4349791 : Blo 2289435 4349791 := bstep (se 1 (by rfl) ⟨3262343, by rfl⟩ : syracuseStep 4349791 = 6524687) B6524687
theorem B5799721 : Blo 2289435 5799721 := bstep (se 2 (by rfl) ⟨2174895, by rfl⟩ : syracuseStep 5799721 = 4349791) B4349791
theorem B7732961 : Blo 2289435 7732961 := bstep (se 2 (by rfl) ⟨2899860, by rfl⟩ : syracuseStep 7732961 = 5799721) B5799721
theorem B5155307 : Blo 2289435 5155307 := bstep (se 1 (by rfl) ⟨3866480, by rfl⟩ : syracuseStep 5155307 = 7732961) B7732961
theorem B3436871 : Blo 2289435 3436871 := bstep (se 1 (by rfl) ⟨2577653, by rfl⟩ : syracuseStep 3436871 = 5155307) B5155307
theorem B2291247 : Blo 2289435 2291247 := bstep (se 1 (by rfl) ⟨1718435, by rfl⟩ : syracuseStep 2291247 = 3436871) B3436871
theorem B3436877 : Blo 2289435 3436877 := bbase (se 3 (by rfl) ⟨644414, by rfl⟩ : syracuseStep 3436877 = 1288829) (by norm_num)
theorem B2291251 : Blo 2289435 2291251 := bstep (se 1 (by rfl) ⟨1718438, by rfl⟩ : syracuseStep 2291251 = 3436877) B3436877
theorem B5155325 : Blo 2289435 5155325 := bbase (se 3 (by rfl) ⟨966623, by rfl⟩ : syracuseStep 5155325 = 1933247) (by norm_num)
theorem B3436883 : Blo 2289435 3436883 := bstep (se 1 (by rfl) ⟨2577662, by rfl⟩ : syracuseStep 3436883 = 5155325) B5155325
theorem B2291255 : Blo 2289435 2291255 := bstep (se 1 (by rfl) ⟨1718441, by rfl⟩ : syracuseStep 2291255 = 3436883) B3436883
theorem B3866501 : Blo 2289435 3866501 := bbase (se 4 (by rfl) ⟨362484, by rfl⟩ : syracuseStep 3866501 = 724969) (by norm_num)
theorem B2577667 : Blo 2289435 2577667 := bstep (se 1 (by rfl) ⟨1933250, by rfl⟩ : syracuseStep 2577667 = 3866501) B3866501
theorem B3436889 : Blo 2289435 3436889 := bstep (se 2 (by rfl) ⟨1288833, by rfl⟩ : syracuseStep 3436889 = 2577667) B2577667
theorem B2291259 : Blo 2289435 2291259 := bstep (se 1 (by rfl) ⟨1718444, by rfl⟩ : syracuseStep 2291259 = 3436889) B3436889
theorem B17399285 : Blo 2289435 17399285 := bbase (se 5 (by rfl) ⟨815591, by rfl⟩ : syracuseStep 17399285 = 1631183) (by norm_num)
theorem B11599523 : Blo 2289435 11599523 := bstep (se 1 (by rfl) ⟨8699642, by rfl⟩ : syracuseStep 11599523 = 17399285) B17399285
theorem B7733015 : Blo 2289435 7733015 := bstep (se 1 (by rfl) ⟨5799761, by rfl⟩ : syracuseStep 7733015 = 11599523) B11599523
theorem B5155343 : Blo 2289435 5155343 := bstep (se 1 (by rfl) ⟨3866507, by rfl⟩ : syracuseStep 5155343 = 7733015) B7733015
theorem B3436895 : Blo 2289435 3436895 := bstep (se 1 (by rfl) ⟨2577671, by rfl⟩ : syracuseStep 3436895 = 5155343) B5155343
theorem B2291263 : Blo 2289435 2291263 := bstep (se 1 (by rfl) ⟨1718447, by rfl⟩ : syracuseStep 2291263 = 3436895) B3436895
theorem B3436901 : Blo 2289435 3436901 := bbase (se 4 (by rfl) ⟨322209, by rfl⟩ : syracuseStep 3436901 = 644419) (by norm_num)
theorem B2291267 : Blo 2289435 2291267 := bstep (se 1 (by rfl) ⟨1718450, by rfl⟩ : syracuseStep 2291267 = 3436901) B3436901
theorem B4349837 : Blo 2289435 4349837 := bbase (se 3 (by rfl) ⟨815594, by rfl⟩ : syracuseStep 4349837 = 1631189) (by norm_num)
theorem B2899891 : Blo 2289435 2899891 := bstep (se 1 (by rfl) ⟨2174918, by rfl⟩ : syracuseStep 2899891 = 4349837) B4349837
theorem B3866521 : Blo 2289435 3866521 := bstep (se 2 (by rfl) ⟨1449945, by rfl⟩ : syracuseStep 3866521 = 2899891) B2899891
theorem B5155361 : Blo 2289435 5155361 := bstep (se 2 (by rfl) ⟨1933260, by rfl⟩ : syracuseStep 5155361 = 3866521) B3866521
theorem B3436907 : Blo 2289435 3436907 := bstep (se 1 (by rfl) ⟨2577680, by rfl⟩ : syracuseStep 3436907 = 5155361) B5155361
theorem B2291271 : Blo 2289435 2291271 := bstep (se 1 (by rfl) ⟨1718453, by rfl⟩ : syracuseStep 2291271 = 3436907) B3436907
theorem B2577685 : Blo 2289435 2577685 := bbase (se 6 (by rfl) ⟨60414, by rfl⟩ : syracuseStep 2577685 = 120829) (by norm_num)
theorem B3436913 : Blo 2289435 3436913 := bstep (se 2 (by rfl) ⟨1288842, by rfl⟩ : syracuseStep 3436913 = 2577685) B2577685
theorem B2291275 : Blo 2289435 2291275 := bstep (se 1 (by rfl) ⟨1718456, by rfl⟩ : syracuseStep 2291275 = 3436913) B3436913
theorem B2899901 : Blo 2289435 2899901 := bbase (se 3 (by rfl) ⟨543731, by rfl⟩ : syracuseStep 2899901 = 1087463) (by norm_num)
theorem B7733069 : Blo 2289435 7733069 := bstep (se 3 (by rfl) ⟨1449950, by rfl⟩ : syracuseStep 7733069 = 2899901) B2899901
theorem B5155379 : Blo 2289435 5155379 := bstep (se 1 (by rfl) ⟨3866534, by rfl⟩ : syracuseStep 5155379 = 7733069) B7733069
theorem B3436919 : Blo 2289435 3436919 := bstep (se 1 (by rfl) ⟨2577689, by rfl⟩ : syracuseStep 3436919 = 5155379) B5155379
theorem B2291279 : Blo 2289435 2291279 := bstep (se 1 (by rfl) ⟨1718459, by rfl⟩ : syracuseStep 2291279 = 3436919) B3436919
theorem B3436925 : Blo 2289435 3436925 := bbase (se 3 (by rfl) ⟨644423, by rfl⟩ : syracuseStep 3436925 = 1288847) (by norm_num)
theorem B2291283 : Blo 2289435 2291283 := bstep (se 1 (by rfl) ⟨1718462, by rfl⟩ : syracuseStep 2291283 = 3436925) B3436925
theorem B5155397 : Blo 2289435 5155397 := bbase (se 4 (by rfl) ⟨483318, by rfl⟩ : syracuseStep 5155397 = 966637) (by norm_num)
theorem B3436931 : Blo 2289435 3436931 := bstep (se 1 (by rfl) ⟨2577698, by rfl⟩ : syracuseStep 3436931 = 5155397) B5155397
theorem B2291287 : Blo 2289435 2291287 := bstep (se 1 (by rfl) ⟨1718465, by rfl⟩ : syracuseStep 2291287 = 3436931) B3436931
theorem B2446805 : Blo 2289435 2446805 := bbase (se 7 (by rfl) ⟨28673, by rfl⟩ : syracuseStep 2446805 = 57347) (by norm_num)
theorem B6524813 : Blo 2289435 6524813 := bstep (se 3 (by rfl) ⟨1223402, by rfl⟩ : syracuseStep 6524813 = 2446805) B2446805
theorem B4349875 : Blo 2289435 4349875 := bstep (se 1 (by rfl) ⟨3262406, by rfl⟩ : syracuseStep 4349875 = 6524813) B6524813
theorem B5799833 : Blo 2289435 5799833 := bstep (se 2 (by rfl) ⟨2174937, by rfl⟩ : syracuseStep 5799833 = 4349875) B4349875
theorem B3866555 : Blo 2289435 3866555 := bstep (se 1 (by rfl) ⟨2899916, by rfl⟩ : syracuseStep 3866555 = 5799833) B5799833
theorem B2577703 : Blo 2289435 2577703 := bstep (se 1 (by rfl) ⟨1933277, by rfl⟩ : syracuseStep 2577703 = 3866555) B3866555
theorem B3436937 : Blo 2289435 3436937 := bstep (se 2 (by rfl) ⟨1288851, by rfl⟩ : syracuseStep 3436937 = 2577703) B2577703
theorem B2291291 : Blo 2289435 2291291 := bstep (se 1 (by rfl) ⟨1718468, by rfl⟩ : syracuseStep 2291291 = 3436937) B3436937
theorem B11599685 : Blo 2289435 11599685 := bbase (se 4 (by rfl) ⟨1087470, by rfl⟩ : syracuseStep 11599685 = 2174941) (by norm_num)
theorem B7733123 : Blo 2289435 7733123 := bstep (se 1 (by rfl) ⟨5799842, by rfl⟩ : syracuseStep 7733123 = 11599685) B11599685
theorem B5155415 : Blo 2289435 5155415 := bstep (se 1 (by rfl) ⟨3866561, by rfl⟩ : syracuseStep 5155415 = 7733123) B7733123
theorem B3436943 : Blo 2289435 3436943 := bstep (se 1 (by rfl) ⟨2577707, by rfl⟩ : syracuseStep 3436943 = 5155415) B5155415
theorem B2291295 : Blo 2289435 2291295 := bstep (se 1 (by rfl) ⟨1718471, by rfl⟩ : syracuseStep 2291295 = 3436943) B3436943
theorem B3436949 : Blo 2289435 3436949 := bbase (se 6 (by rfl) ⟨80553, by rfl⟩ : syracuseStep 3436949 = 161107) (by norm_num)
theorem B2291299 : Blo 2289435 2291299 := bstep (se 1 (by rfl) ⟨1718474, by rfl⟩ : syracuseStep 2291299 = 3436949) B3436949
theorem B7340453 : Blo 2289435 7340453 := bbase (se 4 (by rfl) ⟨688167, by rfl⟩ : syracuseStep 7340453 = 1376335) (by norm_num)
theorem B4893635 : Blo 2289435 4893635 := bstep (se 1 (by rfl) ⟨3670226, by rfl⟩ : syracuseStep 4893635 = 7340453) B7340453
theorem B13049693 : Blo 2289435 13049693 := bstep (se 3 (by rfl) ⟨2446817, by rfl⟩ : syracuseStep 13049693 = 4893635) B4893635
theorem B8699795 : Blo 2289435 8699795 := bstep (se 1 (by rfl) ⟨6524846, by rfl⟩ : syracuseStep 8699795 = 13049693) B13049693
theorem B5799863 : Blo 2289435 5799863 := bstep (se 1 (by rfl) ⟨4349897, by rfl⟩ : syracuseStep 5799863 = 8699795) B8699795
theorem B3866575 : Blo 2289435 3866575 := bstep (se 1 (by rfl) ⟨2899931, by rfl⟩ : syracuseStep 3866575 = 5799863) B5799863
theorem B5155433 : Blo 2289435 5155433 := bstep (se 2 (by rfl) ⟨1933287, by rfl⟩ : syracuseStep 5155433 = 3866575) B3866575
theorem B3436955 : Blo 2289435 3436955 := bstep (se 1 (by rfl) ⟨2577716, by rfl⟩ : syracuseStep 3436955 = 5155433) B5155433
theorem B2291303 : Blo 2289435 2291303 := bstep (se 1 (by rfl) ⟨1718477, by rfl⟩ : syracuseStep 2291303 = 3436955) B3436955
theorem B2577721 : Blo 2289435 2577721 := bbase (se 2 (by rfl) ⟨966645, by rfl⟩ : syracuseStep 2577721 = 1933291) (by norm_num)
theorem B3436961 : Blo 2289435 3436961 := bstep (se 2 (by rfl) ⟨1288860, by rfl⟩ : syracuseStep 3436961 = 2577721) B2577721
theorem B2291307 : Blo 2289435 2291307 := bstep (se 1 (by rfl) ⟨1718480, by rfl⟩ : syracuseStep 2291307 = 3436961) B3436961
theorem B6524869 : Blo 2289435 6524869 := bbase (se 4 (by rfl) ⟨611706, by rfl⟩ : syracuseStep 6524869 = 1223413) (by norm_num)
theorem B8699825 : Blo 2289435 8699825 := bstep (se 2 (by rfl) ⟨3262434, by rfl⟩ : syracuseStep 8699825 = 6524869) B6524869
theorem B5799883 : Blo 2289435 5799883 := bstep (se 1 (by rfl) ⟨4349912, by rfl⟩ : syracuseStep 5799883 = 8699825) B8699825
theorem B7733177 : Blo 2289435 7733177 := bstep (se 2 (by rfl) ⟨2899941, by rfl⟩ : syracuseStep 7733177 = 5799883) B5799883
theorem B5155451 : Blo 2289435 5155451 := bstep (se 1 (by rfl) ⟨3866588, by rfl⟩ : syracuseStep 5155451 = 7733177) B7733177
theorem B3436967 : Blo 2289435 3436967 := bstep (se 1 (by rfl) ⟨2577725, by rfl⟩ : syracuseStep 3436967 = 5155451) B5155451
theorem B2291311 : Blo 2289435 2291311 := bstep (se 1 (by rfl) ⟨1718483, by rfl⟩ : syracuseStep 2291311 = 3436967) B3436967
theorem B3436973 : Blo 2289435 3436973 := bbase (se 3 (by rfl) ⟨644432, by rfl⟩ : syracuseStep 3436973 = 1288865) (by norm_num)
theorem B2291315 : Blo 2289435 2291315 := bstep (se 1 (by rfl) ⟨1718486, by rfl⟩ : syracuseStep 2291315 = 3436973) B3436973
theorem B5155469 : Blo 2289435 5155469 := bbase (se 3 (by rfl) ⟨966650, by rfl⟩ : syracuseStep 5155469 = 1933301) (by norm_num)
theorem B3436979 : Blo 2289435 3436979 := bstep (se 1 (by rfl) ⟨2577734, by rfl⟩ : syracuseStep 3436979 = 5155469) B5155469
theorem B2291319 : Blo 2289435 2291319 := bstep (se 1 (by rfl) ⟨1718489, by rfl⟩ : syracuseStep 2291319 = 3436979) B3436979
theorem B2899957 : Blo 2289435 2899957 := bbase (se 5 (by rfl) ⟨135935, by rfl⟩ : syracuseStep 2899957 = 271871) (by norm_num)
theorem B3866609 : Blo 2289435 3866609 := bstep (se 2 (by rfl) ⟨1449978, by rfl⟩ : syracuseStep 3866609 = 2899957) B2899957
theorem B2577739 : Blo 2289435 2577739 := bstep (se 1 (by rfl) ⟨1933304, by rfl⟩ : syracuseStep 2577739 = 3866609) B3866609
theorem B3436985 : Blo 2289435 3436985 := bstep (se 2 (by rfl) ⟨1288869, by rfl⟩ : syracuseStep 3436985 = 2577739) B2577739
theorem B2291323 : Blo 2289435 2291323 := bstep (se 1 (by rfl) ⟨1718492, by rfl⟩ : syracuseStep 2291323 = 3436985) B3436985
theorem B5297125 : Blo 2289435 5297125 := bbase (se 4 (by rfl) ⟨496605, by rfl⟩ : syracuseStep 5297125 = 993211) (by norm_num)
theorem B7062833 : Blo 2289435 7062833 := bstep (se 2 (by rfl) ⟨2648562, by rfl⟩ : syracuseStep 7062833 = 5297125) B5297125
theorem B18834221 : Blo 2289435 18834221 := bstep (se 3 (by rfl) ⟨3531416, by rfl⟩ : syracuseStep 18834221 = 7062833) B7062833
theorem B12556147 : Blo 2289435 12556147 := bstep (se 1 (by rfl) ⟨9417110, by rfl⟩ : syracuseStep 12556147 = 18834221) B18834221
theorem B16741529 : Blo 2289435 16741529 := bstep (se 2 (by rfl) ⟨6278073, by rfl⟩ : syracuseStep 16741529 = 12556147) B12556147
theorem B11161019 : Blo 2289435 11161019 := bstep (se 1 (by rfl) ⟨8370764, by rfl⟩ : syracuseStep 11161019 = 16741529) B16741529
theorem B7440679 : Blo 2289435 7440679 := bstep (se 1 (by rfl) ⟨5580509, by rfl⟩ : syracuseStep 7440679 = 11161019) B11161019
theorem B39683621 : Blo 2289435 39683621 := bstep (se 4 (by rfl) ⟨3720339, by rfl⟩ : syracuseStep 39683621 = 7440679) B7440679
theorem B26455747 : Blo 2289435 26455747 := bstep (se 1 (by rfl) ⟨19841810, by rfl⟩ : syracuseStep 26455747 = 39683621) B39683621
theorem B35274329 : Blo 2289435 35274329 := bstep (se 2 (by rfl) ⟨13227873, by rfl⟩ : syracuseStep 35274329 = 26455747) B26455747
theorem B23516219 : Blo 2289435 23516219 := bstep (se 1 (by rfl) ⟨17637164, by rfl⟩ : syracuseStep 23516219 = 35274329) B35274329
theorem B15677479 : Blo 2289435 15677479 := bstep (se 1 (by rfl) ⟨11758109, by rfl⟩ : syracuseStep 15677479 = 23516219) B23516219
theorem B20903305 : Blo 2289435 20903305 := bstep (se 2 (by rfl) ⟨7838739, by rfl⟩ : syracuseStep 20903305 = 15677479) B15677479
theorem B27871073 : Blo 2289435 27871073 := bstep (se 2 (by rfl) ⟨10451652, by rfl⟩ : syracuseStep 27871073 = 20903305) B20903305
theorem B18580715 : Blo 2289435 18580715 := bstep (se 1 (by rfl) ⟨13935536, by rfl⟩ : syracuseStep 18580715 = 27871073) B27871073
theorem B12387143 : Blo 2289435 12387143 := bstep (se 1 (by rfl) ⟨9290357, by rfl⟩ : syracuseStep 12387143 = 18580715) B18580715
theorem B8258095 : Blo 2289435 8258095 := bstep (se 1 (by rfl) ⟨6193571, by rfl⟩ : syracuseStep 8258095 = 12387143) B12387143
theorem B44043173 : Blo 2289435 44043173 := bstep (se 4 (by rfl) ⟨4129047, by rfl⟩ : syracuseStep 44043173 = 8258095) B8258095
theorem B29362115 : Blo 2289435 29362115 := bstep (se 1 (by rfl) ⟨22021586, by rfl⟩ : syracuseStep 29362115 = 44043173) B44043173
theorem B19574743 : Blo 2289435 19574743 := bstep (se 1 (by rfl) ⟨14681057, by rfl⟩ : syracuseStep 19574743 = 29362115) B29362115
theorem B26099657 : Blo 2289435 26099657 := bstep (se 2 (by rfl) ⟨9787371, by rfl⟩ : syracuseStep 26099657 = 19574743) B19574743
theorem B17399771 : Blo 2289435 17399771 := bstep (se 1 (by rfl) ⟨13049828, by rfl⟩ : syracuseStep 17399771 = 26099657) B26099657
theorem B11599847 : Blo 2289435 11599847 := bstep (se 1 (by rfl) ⟨8699885, by rfl⟩ : syracuseStep 11599847 = 17399771) B17399771
theorem B7733231 : Blo 2289435 7733231 := bstep (se 1 (by rfl) ⟨5799923, by rfl⟩ : syracuseStep 7733231 = 11599847) B11599847
theorem B5155487 : Blo 2289435 5155487 := bstep (se 1 (by rfl) ⟨3866615, by rfl⟩ : syracuseStep 5155487 = 7733231) B7733231
theorem B3436991 : Blo 2289435 3436991 := bstep (se 1 (by rfl) ⟨2577743, by rfl⟩ : syracuseStep 3436991 = 5155487) B5155487
theorem B2291327 : Blo 2289435 2291327 := bstep (se 1 (by rfl) ⟨1718495, by rfl⟩ : syracuseStep 2291327 = 3436991) B3436991
theorem B3436997 : Blo 2289435 3436997 := bbase (se 4 (by rfl) ⟨322218, by rfl⟩ : syracuseStep 3436997 = 644437) (by norm_num)
theorem B2291331 : Blo 2289435 2291331 := bstep (se 1 (by rfl) ⟨1718498, by rfl⟩ : syracuseStep 2291331 = 3436997) B3436997
theorem B3866629 : Blo 2289435 3866629 := bbase (se 4 (by rfl) ⟨362496, by rfl⟩ : syracuseStep 3866629 = 724993) (by norm_num)
theorem B5155505 : Blo 2289435 5155505 := bstep (se 2 (by rfl) ⟨1933314, by rfl⟩ : syracuseStep 5155505 = 3866629) B3866629
theorem B3437003 : Blo 2289435 3437003 := bstep (se 1 (by rfl) ⟨2577752, by rfl⟩ : syracuseStep 3437003 = 5155505) B5155505
theorem B2291335 : Blo 2289435 2291335 := bstep (se 1 (by rfl) ⟨1718501, by rfl⟩ : syracuseStep 2291335 = 3437003) B3437003
theorem B2577757 : Blo 2289435 2577757 := bbase (se 3 (by rfl) ⟨483329, by rfl⟩ : syracuseStep 2577757 = 966659) (by norm_num)
theorem B3437009 : Blo 2289435 3437009 := bstep (se 2 (by rfl) ⟨1288878, by rfl⟩ : syracuseStep 3437009 = 2577757) B2577757
theorem B2291339 : Blo 2289435 2291339 := bstep (se 1 (by rfl) ⟨1718504, by rfl⟩ : syracuseStep 2291339 = 3437009) B3437009
theorem B7733285 : Blo 2289435 7733285 := bbase (se 4 (by rfl) ⟨724995, by rfl⟩ : syracuseStep 7733285 = 1449991) (by norm_num)
theorem B5155523 : Blo 2289435 5155523 := bstep (se 1 (by rfl) ⟨3866642, by rfl⟩ : syracuseStep 5155523 = 7733285) B7733285
theorem B3437015 : Blo 2289435 3437015 := bstep (se 1 (by rfl) ⟨2577761, by rfl⟩ : syracuseStep 3437015 = 5155523) B5155523
theorem B2291343 : Blo 2289435 2291343 := bstep (se 1 (by rfl) ⟨1718507, by rfl⟩ : syracuseStep 2291343 = 3437015) B3437015
theorem B3437021 : Blo 2289435 3437021 := bbase (se 3 (by rfl) ⟨644441, by rfl⟩ : syracuseStep 3437021 = 1288883) (by norm_num)
theorem B2291347 : Blo 2289435 2291347 := bstep (se 1 (by rfl) ⟨1718510, by rfl⟩ : syracuseStep 2291347 = 3437021) B3437021
theorem B5155541 : Blo 2289435 5155541 := bbase (se 7 (by rfl) ⟨60416, by rfl⟩ : syracuseStep 5155541 = 120833) (by norm_num)
theorem B3437027 : Blo 2289435 3437027 := bstep (se 1 (by rfl) ⟨2577770, by rfl⟩ : syracuseStep 3437027 = 5155541) B5155541
theorem B2291351 : Blo 2289435 2291351 := bstep (se 1 (by rfl) ⟨1718513, by rfl⟩ : syracuseStep 2291351 = 3437027) B3437027
theorem B9787493 : Blo 2289435 9787493 := bbase (se 4 (by rfl) ⟨917577, by rfl⟩ : syracuseStep 9787493 = 1835155) (by norm_num)
theorem B6524995 : Blo 2289435 6524995 := bstep (se 1 (by rfl) ⟨4893746, by rfl⟩ : syracuseStep 6524995 = 9787493) B9787493
theorem B8699993 : Blo 2289435 8699993 := bstep (se 2 (by rfl) ⟨3262497, by rfl⟩ : syracuseStep 8699993 = 6524995) B6524995
theorem B5799995 : Blo 2289435 5799995 := bstep (se 1 (by rfl) ⟨4349996, by rfl⟩ : syracuseStep 5799995 = 8699993) B8699993
theorem B3866663 : Blo 2289435 3866663 := bstep (se 1 (by rfl) ⟨2899997, by rfl⟩ : syracuseStep 3866663 = 5799995) B5799995
theorem B2577775 : Blo 2289435 2577775 := bstep (se 1 (by rfl) ⟨1933331, by rfl⟩ : syracuseStep 2577775 = 3866663) B3866663
theorem B3437033 : Blo 2289435 3437033 := bstep (se 2 (by rfl) ⟨1288887, by rfl⟩ : syracuseStep 3437033 = 2577775) B2577775
theorem B2291355 : Blo 2289435 2291355 := bstep (se 1 (by rfl) ⟨1718516, by rfl⟩ : syracuseStep 2291355 = 3437033) B3437033
theorem B5580589 : Blo 2289435 5580589 := bbase (se 3 (by rfl) ⟨1046360, by rfl⟩ : syracuseStep 5580589 = 2092721) (by norm_num)
theorem B7440785 : Blo 2289435 7440785 := bstep (se 2 (by rfl) ⟨2790294, by rfl⟩ : syracuseStep 7440785 = 5580589) B5580589
theorem B4960523 : Blo 2289435 4960523 := bstep (se 1 (by rfl) ⟨3720392, by rfl⟩ : syracuseStep 4960523 = 7440785) B7440785
theorem B3307015 : Blo 2289435 3307015 := bstep (se 1 (by rfl) ⟨2480261, by rfl⟩ : syracuseStep 3307015 = 4960523) B4960523
theorem B4409353 : Blo 2289435 4409353 := bstep (se 2 (by rfl) ⟨1653507, by rfl⟩ : syracuseStep 4409353 = 3307015) B3307015
theorem B5879137 : Blo 2289435 5879137 := bstep (se 2 (by rfl) ⟨2204676, by rfl⟩ : syracuseStep 5879137 = 4409353) B4409353
theorem B7838849 : Blo 2289435 7838849 := bstep (se 2 (by rfl) ⟨2939568, by rfl⟩ : syracuseStep 7838849 = 5879137) B5879137
theorem B20903597 : Blo 2289435 20903597 := bstep (se 3 (by rfl) ⟨3919424, by rfl⟩ : syracuseStep 20903597 = 7838849) B7838849
theorem B13935731 : Blo 2289435 13935731 := bstep (se 1 (by rfl) ⟨10451798, by rfl⟩ : syracuseStep 13935731 = 20903597) B20903597
theorem B37161949 : Blo 2289435 37161949 := bstep (se 3 (by rfl) ⟨6967865, by rfl⟩ : syracuseStep 37161949 = 13935731) B13935731
theorem B49549265 : Blo 2289435 49549265 := bstep (se 2 (by rfl) ⟨18580974, by rfl⟩ : syracuseStep 49549265 = 37161949) B37161949
theorem B33032843 : Blo 2289435 33032843 := bstep (se 1 (by rfl) ⟨24774632, by rfl⟩ : syracuseStep 33032843 = 49549265) B49549265
theorem B22021895 : Blo 2289435 22021895 := bstep (se 1 (by rfl) ⟨16516421, by rfl⟩ : syracuseStep 22021895 = 33032843) B33032843
theorem B14681263 : Blo 2289435 14681263 := bstep (se 1 (by rfl) ⟨11010947, by rfl⟩ : syracuseStep 14681263 = 22021895) B22021895
theorem B19575017 : Blo 2289435 19575017 := bstep (se 2 (by rfl) ⟨7340631, by rfl⟩ : syracuseStep 19575017 = 14681263) B14681263
theorem B13050011 : Blo 2289435 13050011 := bstep (se 1 (by rfl) ⟨9787508, by rfl⟩ : syracuseStep 13050011 = 19575017) B19575017
theorem B8700007 : Blo 2289435 8700007 := bstep (se 1 (by rfl) ⟨6525005, by rfl⟩ : syracuseStep 8700007 = 13050011) B13050011
theorem B11600009 : Blo 2289435 11600009 := bstep (se 2 (by rfl) ⟨4350003, by rfl⟩ : syracuseStep 11600009 = 8700007) B8700007
theorem B7733339 : Blo 2289435 7733339 := bstep (se 1 (by rfl) ⟨5800004, by rfl⟩ : syracuseStep 7733339 = 11600009) B11600009
theorem B5155559 : Blo 2289435 5155559 := bstep (se 1 (by rfl) ⟨3866669, by rfl⟩ : syracuseStep 5155559 = 7733339) B7733339
theorem B3437039 : Blo 2289435 3437039 := bstep (se 1 (by rfl) ⟨2577779, by rfl⟩ : syracuseStep 3437039 = 5155559) B5155559
theorem B2291359 : Blo 2289435 2291359 := bstep (se 1 (by rfl) ⟨1718519, by rfl⟩ : syracuseStep 2291359 = 3437039) B3437039
theorem B3437045 : Blo 2289435 3437045 := bbase (se 5 (by rfl) ⟨161111, by rfl⟩ : syracuseStep 3437045 = 322223) (by norm_num)
theorem B2291363 : Blo 2289435 2291363 := bstep (se 1 (by rfl) ⟨1718522, by rfl⟩ : syracuseStep 2291363 = 3437045) B3437045
theorem B6525029 : Blo 2289435 6525029 := bbase (se 4 (by rfl) ⟨611721, by rfl⟩ : syracuseStep 6525029 = 1223443) (by norm_num)
theorem B4350019 : Blo 2289435 4350019 := bstep (se 1 (by rfl) ⟨3262514, by rfl⟩ : syracuseStep 4350019 = 6525029) B6525029
theorem B5800025 : Blo 2289435 5800025 := bstep (se 2 (by rfl) ⟨2175009, by rfl⟩ : syracuseStep 5800025 = 4350019) B4350019
theorem B3866683 : Blo 2289435 3866683 := bstep (se 1 (by rfl) ⟨2900012, by rfl⟩ : syracuseStep 3866683 = 5800025) B5800025
theorem B5155577 : Blo 2289435 5155577 := bstep (se 2 (by rfl) ⟨1933341, by rfl⟩ : syracuseStep 5155577 = 3866683) B3866683
theorem B3437051 : Blo 2289435 3437051 := bstep (se 1 (by rfl) ⟨2577788, by rfl⟩ : syracuseStep 3437051 = 5155577) B5155577
theorem B2291367 : Blo 2289435 2291367 := bstep (se 1 (by rfl) ⟨1718525, by rfl⟩ : syracuseStep 2291367 = 3437051) B3437051
theorem B2577793 : Blo 2289435 2577793 := bbase (se 2 (by rfl) ⟨966672, by rfl⟩ : syracuseStep 2577793 = 1933345) (by norm_num)
theorem B3437057 : Blo 2289435 3437057 := bstep (se 2 (by rfl) ⟨1288896, by rfl⟩ : syracuseStep 3437057 = 2577793) B2577793
theorem B2291371 : Blo 2289435 2291371 := bstep (se 1 (by rfl) ⟨1718528, by rfl⟩ : syracuseStep 2291371 = 3437057) B3437057
theorem B5800045 : Blo 2289435 5800045 := bbase (se 3 (by rfl) ⟨1087508, by rfl⟩ : syracuseStep 5800045 = 2175017) (by norm_num)
theorem B7733393 : Blo 2289435 7733393 := bstep (se 2 (by rfl) ⟨2900022, by rfl⟩ : syracuseStep 7733393 = 5800045) B5800045
theorem B5155595 : Blo 2289435 5155595 := bstep (se 1 (by rfl) ⟨3866696, by rfl⟩ : syracuseStep 5155595 = 7733393) B7733393
theorem B3437063 : Blo 2289435 3437063 := bstep (se 1 (by rfl) ⟨2577797, by rfl⟩ : syracuseStep 3437063 = 5155595) B5155595
theorem B2291375 : Blo 2289435 2291375 := bstep (se 1 (by rfl) ⟨1718531, by rfl⟩ : syracuseStep 2291375 = 3437063) B3437063
theorem B3437069 : Blo 2289435 3437069 := bbase (se 3 (by rfl) ⟨644450, by rfl⟩ : syracuseStep 3437069 = 1288901) (by norm_num)
theorem B2291379 : Blo 2289435 2291379 := bstep (se 1 (by rfl) ⟨1718534, by rfl⟩ : syracuseStep 2291379 = 3437069) B3437069
theorem B5155613 : Blo 2289435 5155613 := bbase (se 3 (by rfl) ⟨966677, by rfl⟩ : syracuseStep 5155613 = 1933355) (by norm_num)
theorem B3437075 : Blo 2289435 3437075 := bstep (se 1 (by rfl) ⟨2577806, by rfl⟩ : syracuseStep 3437075 = 5155613) B5155613
theorem B2291383 : Blo 2289435 2291383 := bstep (se 1 (by rfl) ⟨1718537, by rfl⟩ : syracuseStep 2291383 = 3437075) B3437075
theorem B3866717 : Blo 2289435 3866717 := bbase (se 3 (by rfl) ⟨725009, by rfl⟩ : syracuseStep 3866717 = 1450019) (by norm_num)
theorem B2577811 : Blo 2289435 2577811 := bstep (se 1 (by rfl) ⟨1933358, by rfl⟩ : syracuseStep 2577811 = 3866717) B3866717
theorem B3437081 : Blo 2289435 3437081 := bstep (se 2 (by rfl) ⟨1288905, by rfl⟩ : syracuseStep 3437081 = 2577811) B2577811
theorem B2291387 : Blo 2289435 2291387 := bstep (se 1 (by rfl) ⟨1718540, by rfl⟩ : syracuseStep 2291387 = 3437081) B3437081
theorem B18581237 : Blo 2289435 18581237 := bbase (se 5 (by rfl) ⟨870995, by rfl⟩ : syracuseStep 18581237 = 1741991) (by norm_num)
theorem B12387491 : Blo 2289435 12387491 := bstep (se 1 (by rfl) ⟨9290618, by rfl⟩ : syracuseStep 12387491 = 18581237) B18581237
theorem B8258327 : Blo 2289435 8258327 := bstep (se 1 (by rfl) ⟨6193745, by rfl⟩ : syracuseStep 8258327 = 12387491) B12387491
theorem B5505551 : Blo 2289435 5505551 := bstep (se 1 (by rfl) ⟨4129163, by rfl⟩ : syracuseStep 5505551 = 8258327) B8258327
theorem B3670367 : Blo 2289435 3670367 := bstep (se 1 (by rfl) ⟨2752775, by rfl⟩ : syracuseStep 3670367 = 5505551) B5505551
theorem B9787645 : Blo 2289435 9787645 := bstep (se 3 (by rfl) ⟨1835183, by rfl⟩ : syracuseStep 9787645 = 3670367) B3670367
theorem B13050193 : Blo 2289435 13050193 := bstep (se 2 (by rfl) ⟨4893822, by rfl⟩ : syracuseStep 13050193 = 9787645) B9787645
theorem B17400257 : Blo 2289435 17400257 := bstep (se 2 (by rfl) ⟨6525096, by rfl⟩ : syracuseStep 17400257 = 13050193) B13050193
theorem B11600171 : Blo 2289435 11600171 := bstep (se 1 (by rfl) ⟨8700128, by rfl⟩ : syracuseStep 11600171 = 17400257) B17400257
theorem B7733447 : Blo 2289435 7733447 := bstep (se 1 (by rfl) ⟨5800085, by rfl⟩ : syracuseStep 7733447 = 11600171) B11600171
theorem B5155631 : Blo 2289435 5155631 := bstep (se 1 (by rfl) ⟨3866723, by rfl⟩ : syracuseStep 5155631 = 7733447) B7733447
theorem B3437087 : Blo 2289435 3437087 := bstep (se 1 (by rfl) ⟨2577815, by rfl⟩ : syracuseStep 3437087 = 5155631) B5155631
theorem B2291391 : Blo 2289435 2291391 := bstep (se 1 (by rfl) ⟨1718543, by rfl⟩ : syracuseStep 2291391 = 3437087) B3437087
theorem B3437093 : Blo 2289435 3437093 := bbase (se 4 (by rfl) ⟨322227, by rfl⟩ : syracuseStep 3437093 = 644455) (by norm_num)
theorem B2291395 : Blo 2289435 2291395 := bstep (se 1 (by rfl) ⟨1718546, by rfl⟩ : syracuseStep 2291395 = 3437093) B3437093
theorem B2900053 : Blo 2289435 2900053 := bbase (se 8 (by rfl) ⟨16992, by rfl⟩ : syracuseStep 2900053 = 33985) (by norm_num)
theorem B3866737 : Blo 2289435 3866737 := bstep (se 2 (by rfl) ⟨1450026, by rfl⟩ : syracuseStep 3866737 = 2900053) B2900053
theorem B5155649 : Blo 2289435 5155649 := bstep (se 2 (by rfl) ⟨1933368, by rfl⟩ : syracuseStep 5155649 = 3866737) B3866737
theorem B3437099 : Blo 2289435 3437099 := bstep (se 1 (by rfl) ⟨2577824, by rfl⟩ : syracuseStep 3437099 = 5155649) B5155649
theorem B2291399 : Blo 2289435 2291399 := bstep (se 1 (by rfl) ⟨1718549, by rfl⟩ : syracuseStep 2291399 = 3437099) B3437099
theorem B2577829 : Blo 2289435 2577829 := bbase (se 4 (by rfl) ⟨241671, by rfl⟩ : syracuseStep 2577829 = 483343) (by norm_num)
theorem B3437105 : Blo 2289435 3437105 := bstep (se 2 (by rfl) ⟨1288914, by rfl⟩ : syracuseStep 3437105 = 2577829) B2577829
theorem B2291403 : Blo 2289435 2291403 := bstep (se 1 (by rfl) ⟨1718552, by rfl⟩ : syracuseStep 2291403 = 3437105) B3437105
theorem B5959477 : Blo 2289435 5959477 := bbase (se 5 (by rfl) ⟨279350, by rfl⟩ : syracuseStep 5959477 = 558701) (by norm_num)
theorem B31783877 : Blo 2289435 31783877 := bstep (se 4 (by rfl) ⟨2979738, by rfl⟩ : syracuseStep 31783877 = 5959477) B5959477
theorem B21189251 : Blo 2289435 21189251 := bstep (se 1 (by rfl) ⟨15891938, by rfl⟩ : syracuseStep 21189251 = 31783877) B31783877
theorem B14126167 : Blo 2289435 14126167 := bstep (se 1 (by rfl) ⟨10594625, by rfl⟩ : syracuseStep 14126167 = 21189251) B21189251
theorem B18834889 : Blo 2289435 18834889 := bstep (se 2 (by rfl) ⟨7063083, by rfl⟩ : syracuseStep 18834889 = 14126167) B14126167
theorem B25113185 : Blo 2289435 25113185 := bstep (se 2 (by rfl) ⟨9417444, by rfl⟩ : syracuseStep 25113185 = 18834889) B18834889
theorem B16742123 : Blo 2289435 16742123 := bstep (se 1 (by rfl) ⟨12556592, by rfl⟩ : syracuseStep 16742123 = 25113185) B25113185
theorem B11161415 : Blo 2289435 11161415 := bstep (se 1 (by rfl) ⟨8371061, by rfl⟩ : syracuseStep 11161415 = 16742123) B16742123
theorem B29763773 : Blo 2289435 29763773 := bstep (se 3 (by rfl) ⟨5580707, by rfl⟩ : syracuseStep 29763773 = 11161415) B11161415
theorem B19842515 : Blo 2289435 19842515 := bstep (se 1 (by rfl) ⟨14881886, by rfl⟩ : syracuseStep 19842515 = 29763773) B29763773
theorem B13228343 : Blo 2289435 13228343 := bstep (se 1 (by rfl) ⟨9921257, by rfl⟩ : syracuseStep 13228343 = 19842515) B19842515
theorem B8818895 : Blo 2289435 8818895 := bstep (se 1 (by rfl) ⟨6614171, by rfl⟩ : syracuseStep 8818895 = 13228343) B13228343
theorem B23517053 : Blo 2289435 23517053 := bstep (se 3 (by rfl) ⟨4409447, by rfl⟩ : syracuseStep 23517053 = 8818895) B8818895
theorem B15678035 : Blo 2289435 15678035 := bstep (se 1 (by rfl) ⟨11758526, by rfl⟩ : syracuseStep 15678035 = 23517053) B23517053
theorem B10452023 : Blo 2289435 10452023 := bstep (se 1 (by rfl) ⟨7839017, by rfl⟩ : syracuseStep 10452023 = 15678035) B15678035
theorem B6968015 : Blo 2289435 6968015 := bstep (se 1 (by rfl) ⟨5226011, by rfl⟩ : syracuseStep 6968015 = 10452023) B10452023
theorem B4645343 : Blo 2289435 4645343 := bstep (se 1 (by rfl) ⟨3484007, by rfl⟩ : syracuseStep 4645343 = 6968015) B6968015
theorem B3096895 : Blo 2289435 3096895 := bstep (se 1 (by rfl) ⟨2322671, by rfl⟩ : syracuseStep 3096895 = 4645343) B4645343
theorem B4129193 : Blo 2289435 4129193 := bstep (se 2 (by rfl) ⟨1548447, by rfl⟩ : syracuseStep 4129193 = 3096895) B3096895
theorem B2752795 : Blo 2289435 2752795 := bstep (se 1 (by rfl) ⟨2064596, by rfl⟩ : syracuseStep 2752795 = 4129193) B4129193
theorem B14681573 : Blo 2289435 14681573 := bstep (se 4 (by rfl) ⟨1376397, by rfl⟩ : syracuseStep 14681573 = 2752795) B2752795
theorem B9787715 : Blo 2289435 9787715 := bstep (se 1 (by rfl) ⟨7340786, by rfl⟩ : syracuseStep 9787715 = 14681573) B14681573
theorem B6525143 : Blo 2289435 6525143 := bstep (se 1 (by rfl) ⟨4893857, by rfl⟩ : syracuseStep 6525143 = 9787715) B9787715
theorem B4350095 : Blo 2289435 4350095 := bstep (se 1 (by rfl) ⟨3262571, by rfl⟩ : syracuseStep 4350095 = 6525143) B6525143
theorem B2900063 : Blo 2289435 2900063 := bstep (se 1 (by rfl) ⟨2175047, by rfl⟩ : syracuseStep 2900063 = 4350095) B4350095
theorem B7733501 : Blo 2289435 7733501 := bstep (se 3 (by rfl) ⟨1450031, by rfl⟩ : syracuseStep 7733501 = 2900063) B2900063
theorem B5155667 : Blo 2289435 5155667 := bstep (se 1 (by rfl) ⟨3866750, by rfl⟩ : syracuseStep 5155667 = 7733501) B7733501
theorem B3437111 : Blo 2289435 3437111 := bstep (se 1 (by rfl) ⟨2577833, by rfl⟩ : syracuseStep 3437111 = 5155667) B5155667
theorem B2291407 : Blo 2289435 2291407 := bstep (se 1 (by rfl) ⟨1718555, by rfl⟩ : syracuseStep 2291407 = 3437111) B3437111
theorem B3437117 : Blo 2289435 3437117 := bbase (se 3 (by rfl) ⟨644459, by rfl⟩ : syracuseStep 3437117 = 1288919) (by norm_num)
theorem B2291411 : Blo 2289435 2291411 := bstep (se 1 (by rfl) ⟨1718558, by rfl⟩ : syracuseStep 2291411 = 3437117) B3437117
theorem B5155685 : Blo 2289435 5155685 := bbase (se 4 (by rfl) ⟨483345, by rfl⟩ : syracuseStep 5155685 = 966691) (by norm_num)
theorem B3437123 : Blo 2289435 3437123 := bstep (se 1 (by rfl) ⟨2577842, by rfl⟩ : syracuseStep 3437123 = 5155685) B5155685
theorem B2291415 : Blo 2289435 2291415 := bstep (se 1 (by rfl) ⟨1718561, by rfl⟩ : syracuseStep 2291415 = 3437123) B3437123
theorem B5800157 : Blo 2289435 5800157 := bbase (se 3 (by rfl) ⟨1087529, by rfl⟩ : syracuseStep 5800157 = 2175059) (by norm_num)
theorem B3866771 : Blo 2289435 3866771 := bstep (se 1 (by rfl) ⟨2900078, by rfl⟩ : syracuseStep 3866771 = 5800157) B5800157
theorem B2577847 : Blo 2289435 2577847 := bstep (se 1 (by rfl) ⟨1933385, by rfl⟩ : syracuseStep 2577847 = 3866771) B3866771
theorem B3437129 : Blo 2289435 3437129 := bstep (se 2 (by rfl) ⟨1288923, by rfl⟩ : syracuseStep 3437129 = 2577847) B2577847
theorem B2291419 : Blo 2289435 2291419 := bstep (se 1 (by rfl) ⟨1718564, by rfl⟩ : syracuseStep 2291419 = 3437129) B3437129
theorem B4350125 : Blo 2289435 4350125 := bbase (se 3 (by rfl) ⟨815648, by rfl⟩ : syracuseStep 4350125 = 1631297) (by norm_num)
theorem B11600333 : Blo 2289435 11600333 := bstep (se 3 (by rfl) ⟨2175062, by rfl⟩ : syracuseStep 11600333 = 4350125) B4350125
theorem B7733555 : Blo 2289435 7733555 := bstep (se 1 (by rfl) ⟨5800166, by rfl⟩ : syracuseStep 7733555 = 11600333) B11600333
theorem B5155703 : Blo 2289435 5155703 := bstep (se 1 (by rfl) ⟨3866777, by rfl⟩ : syracuseStep 5155703 = 7733555) B7733555
theorem B3437135 : Blo 2289435 3437135 := bstep (se 1 (by rfl) ⟨2577851, by rfl⟩ : syracuseStep 3437135 = 5155703) B5155703
theorem B2291423 : Blo 2289435 2291423 := bstep (se 1 (by rfl) ⟨1718567, by rfl⟩ : syracuseStep 2291423 = 3437135) B3437135
theorem B3437141 : Blo 2289435 3437141 := bbase (se 8 (by rfl) ⟨20139, by rfl⟩ : syracuseStep 3437141 = 40279) (by norm_num)
theorem B2291427 : Blo 2289435 2291427 := bstep (se 1 (by rfl) ⟨1718570, by rfl⟩ : syracuseStep 2291427 = 3437141) B3437141
theorem B11758645 : Blo 2289435 11758645 := bbase (se 5 (by rfl) ⟨551186, by rfl⟩ : syracuseStep 11758645 = 1102373) (by norm_num)
theorem B15678193 : Blo 2289435 15678193 := bstep (se 2 (by rfl) ⟨5879322, by rfl⟩ : syracuseStep 15678193 = 11758645) B11758645
theorem B20904257 : Blo 2289435 20904257 := bstep (se 2 (by rfl) ⟨7839096, by rfl⟩ : syracuseStep 20904257 = 15678193) B15678193
theorem B55744685 : Blo 2289435 55744685 := bstep (se 3 (by rfl) ⟨10452128, by rfl⟩ : syracuseStep 55744685 = 20904257) B20904257
theorem B37163123 : Blo 2289435 37163123 := bstep (se 1 (by rfl) ⟨27872342, by rfl⟩ : syracuseStep 37163123 = 55744685) B55744685
theorem B24775415 : Blo 2289435 24775415 := bstep (se 1 (by rfl) ⟨18581561, by rfl⟩ : syracuseStep 24775415 = 37163123) B37163123
theorem B16516943 : Blo 2289435 16516943 := bstep (se 1 (by rfl) ⟨12387707, by rfl⟩ : syracuseStep 16516943 = 24775415) B24775415
theorem B11011295 : Blo 2289435 11011295 := bstep (se 1 (by rfl) ⟨8258471, by rfl⟩ : syracuseStep 11011295 = 16516943) B16516943
theorem B7340863 : Blo 2289435 7340863 := bstep (se 1 (by rfl) ⟨5505647, by rfl⟩ : syracuseStep 7340863 = 11011295) B11011295
theorem B9787817 : Blo 2289435 9787817 := bstep (se 2 (by rfl) ⟨3670431, by rfl⟩ : syracuseStep 9787817 = 7340863) B7340863
theorem B6525211 : Blo 2289435 6525211 := bstep (se 1 (by rfl) ⟨4893908, by rfl⟩ : syracuseStep 6525211 = 9787817) B9787817
theorem B8700281 : Blo 2289435 8700281 := bstep (se 2 (by rfl) ⟨3262605, by rfl⟩ : syracuseStep 8700281 = 6525211) B6525211
theorem B5800187 : Blo 2289435 5800187 := bstep (se 1 (by rfl) ⟨4350140, by rfl⟩ : syracuseStep 5800187 = 8700281) B8700281
theorem B3866791 : Blo 2289435 3866791 := bstep (se 1 (by rfl) ⟨2900093, by rfl⟩ : syracuseStep 3866791 = 5800187) B5800187
theorem B5155721 : Blo 2289435 5155721 := bstep (se 2 (by rfl) ⟨1933395, by rfl⟩ : syracuseStep 5155721 = 3866791) B3866791
theorem B3437147 : Blo 2289435 3437147 := bstep (se 1 (by rfl) ⟨2577860, by rfl⟩ : syracuseStep 3437147 = 5155721) B5155721
theorem B2291431 : Blo 2289435 2291431 := bstep (se 1 (by rfl) ⟨1718573, by rfl⟩ : syracuseStep 2291431 = 3437147) B3437147
theorem B2577865 : Blo 2289435 2577865 := bbase (se 2 (by rfl) ⟨966699, by rfl⟩ : syracuseStep 2577865 = 1933399) (by norm_num)
theorem B3437153 : Blo 2289435 3437153 := bstep (se 2 (by rfl) ⟨1288932, by rfl⟩ : syracuseStep 3437153 = 2577865) B2577865
theorem B2291435 : Blo 2289435 2291435 := bstep (se 1 (by rfl) ⟨1718576, by rfl⟩ : syracuseStep 2291435 = 3437153) B3437153
theorem C0 (j : ℕ) (h1 : 572358 ≤ j) (h2 : j ≤ 572858) : Blo 2289435 (4 * j + 3) := by
  interval_cases j
  · exact B2289435
  · exact B2289439
  · exact B2289443
  · exact B2289447
  · exact B2289451
  · exact B2289455
  · exact B2289459
  · exact B2289463
  · exact B2289467
  · exact B2289471
  · exact B2289475
  · exact B2289479
  · exact B2289483
  · exact B2289487
  · exact B2289491
  · exact B2289495
  · exact B2289499
  · exact B2289503
  · exact B2289507
  · exact B2289511
  · exact B2289515
  · exact B2289519
  · exact B2289523
  · exact B2289527
  · exact B2289531
  · exact B2289535
  · exact B2289539
  · exact B2289543
  · exact B2289547
  · exact B2289551
  · exact B2289555
  · exact B2289559
  · exact B2289563
  · exact B2289567
  · exact B2289571
  · exact B2289575
  · exact B2289579
  · exact B2289583
  · exact B2289587
  · exact B2289591
  · exact B2289595
  · exact B2289599
  · exact B2289603
  · exact B2289607
  · exact B2289611
  · exact B2289615
  · exact B2289619
  · exact B2289623
  · exact B2289627
  · exact B2289631
  · exact B2289635
  · exact B2289639
  · exact B2289643
  · exact B2289647
  · exact B2289651
  · exact B2289655
  · exact B2289659
  · exact B2289663
  · exact B2289667
  · exact B2289671
  · exact B2289675
  · exact B2289679
  · exact B2289683
  · exact B2289687
  · exact B2289691
  · exact B2289695
  · exact B2289699
  · exact B2289703
  · exact B2289707
  · exact B2289711
  · exact B2289715
  · exact B2289719
  · exact B2289723
  · exact B2289727
  · exact B2289731
  · exact B2289735
  · exact B2289739
  · exact B2289743
  · exact B2289747
  · exact B2289751
  · exact B2289755
  · exact B2289759
  · exact B2289763
  · exact B2289767
  · exact B2289771
  · exact B2289775
  · exact B2289779
  · exact B2289783
  · exact B2289787
  · exact B2289791
  · exact B2289795
  · exact B2289799
  · exact B2289803
  · exact B2289807
  · exact B2289811
  · exact B2289815
  · exact B2289819
  · exact B2289823
  · exact B2289827
  · exact B2289831
  · exact B2289835
  · exact B2289839
  · exact B2289843
  · exact B2289847
  · exact B2289851
  · exact B2289855
  · exact B2289859
  · exact B2289863
  · exact B2289867
  · exact B2289871
  · exact B2289875
  · exact B2289879
  · exact B2289883
  · exact B2289887
  · exact B2289891
  · exact B2289895
  · exact B2289899
  · exact B2289903
  · exact B2289907
  · exact B2289911
  · exact B2289915
  · exact B2289919
  · exact B2289923
  · exact B2289927
  · exact B2289931
  · exact B2289935
  · exact B2289939
  · exact B2289943
  · exact B2289947
  · exact B2289951
  · exact B2289955
  · exact B2289959
  · exact B2289963
  · exact B2289967
  · exact B2289971
  · exact B2289975
  · exact B2289979
  · exact B2289983
  · exact B2289987
  · exact B2289991
  · exact B2289995
  · exact B2289999
  · exact B2290003
  · exact B2290007
  · exact B2290011
  · exact B2290015
  · exact B2290019
  · exact B2290023
  · exact B2290027
  · exact B2290031
  · exact B2290035
  · exact B2290039
  · exact B2290043
  · exact B2290047
  · exact B2290051
  · exact B2290055
  · exact B2290059
  · exact B2290063
  · exact B2290067
  · exact B2290071
  · exact B2290075
  · exact B2290079
  · exact B2290083
  · exact B2290087
  · exact B2290091
  · exact B2290095
  · exact B2290099
  · exact B2290103
  · exact B2290107
  · exact B2290111
  · exact B2290115
  · exact B2290119
  · exact B2290123
  · exact B2290127
  · exact B2290131
  · exact B2290135
  · exact B2290139
  · exact B2290143
  · exact B2290147
  · exact B2290151
  · exact B2290155
  · exact B2290159
  · exact B2290163
  · exact B2290167
  · exact B2290171
  · exact B2290175
  · exact B2290179
  · exact B2290183
  · exact B2290187
  · exact B2290191
  · exact B2290195
  · exact B2290199
  · exact B2290203
  · exact B2290207
  · exact B2290211
  · exact B2290215
  · exact B2290219
  · exact B2290223
  · exact B2290227
  · exact B2290231
  · exact B2290235
  · exact B2290239
  · exact B2290243
  · exact B2290247
  · exact B2290251
  · exact B2290255
  · exact B2290259
  · exact B2290263
  · exact B2290267
  · exact B2290271
  · exact B2290275
  · exact B2290279
  · exact B2290283
  · exact B2290287
  · exact B2290291
  · exact B2290295
  · exact B2290299
  · exact B2290303
  · exact B2290307
  · exact B2290311
  · exact B2290315
  · exact B2290319
  · exact B2290323
  · exact B2290327
  · exact B2290331
  · exact B2290335
  · exact B2290339
  · exact B2290343
  · exact B2290347
  · exact B2290351
  · exact B2290355
  · exact B2290359
  · exact B2290363
  · exact B2290367
  · exact B2290371
  · exact B2290375
  · exact B2290379
  · exact B2290383
  · exact B2290387
  · exact B2290391
  · exact B2290395
  · exact B2290399
  · exact B2290403
  · exact B2290407
  · exact B2290411
  · exact B2290415
  · exact B2290419
  · exact B2290423
  · exact B2290427
  · exact B2290431
  · exact B2290435
  · exact B2290439
  · exact B2290443
  · exact B2290447
  · exact B2290451
  · exact B2290455
  · exact B2290459
  · exact B2290463
  · exact B2290467
  · exact B2290471
  · exact B2290475
  · exact B2290479
  · exact B2290483
  · exact B2290487
  · exact B2290491
  · exact B2290495
  · exact B2290499
  · exact B2290503
  · exact B2290507
  · exact B2290511
  · exact B2290515
  · exact B2290519
  · exact B2290523
  · exact B2290527
  · exact B2290531
  · exact B2290535
  · exact B2290539
  · exact B2290543
  · exact B2290547
  · exact B2290551
  · exact B2290555
  · exact B2290559
  · exact B2290563
  · exact B2290567
  · exact B2290571
  · exact B2290575
  · exact B2290579
  · exact B2290583
  · exact B2290587
  · exact B2290591
  · exact B2290595
  · exact B2290599
  · exact B2290603
  · exact B2290607
  · exact B2290611
  · exact B2290615
  · exact B2290619
  · exact B2290623
  · exact B2290627
  · exact B2290631
  · exact B2290635
  · exact B2290639
  · exact B2290643
  · exact B2290647
  · exact B2290651
  · exact B2290655
  · exact B2290659
  · exact B2290663
  · exact B2290667
  · exact B2290671
  · exact B2290675
  · exact B2290679
  · exact B2290683
  · exact B2290687
  · exact B2290691
  · exact B2290695
  · exact B2290699
  · exact B2290703
  · exact B2290707
  · exact B2290711
  · exact B2290715
  · exact B2290719
  · exact B2290723
  · exact B2290727
  · exact B2290731
  · exact B2290735
  · exact B2290739
  · exact B2290743
  · exact B2290747
  · exact B2290751
  · exact B2290755
  · exact B2290759
  · exact B2290763
  · exact B2290767
  · exact B2290771
  · exact B2290775
  · exact B2290779
  · exact B2290783
  · exact B2290787
  · exact B2290791
  · exact B2290795
  · exact B2290799
  · exact B2290803
  · exact B2290807
  · exact B2290811
  · exact B2290815
  · exact B2290819
  · exact B2290823
  · exact B2290827
  · exact B2290831
  · exact B2290835
  · exact B2290839
  · exact B2290843
  · exact B2290847
  · exact B2290851
  · exact B2290855
  · exact B2290859
  · exact B2290863
  · exact B2290867
  · exact B2290871
  · exact B2290875
  · exact B2290879
  · exact B2290883
  · exact B2290887
  · exact B2290891
  · exact B2290895
  · exact B2290899
  · exact B2290903
  · exact B2290907
  · exact B2290911
  · exact B2290915
  · exact B2290919
  · exact B2290923
  · exact B2290927
  · exact B2290931
  · exact B2290935
  · exact B2290939
  · exact B2290943
  · exact B2290947
  · exact B2290951
  · exact B2290955
  · exact B2290959
  · exact B2290963
  · exact B2290967
  · exact B2290971
  · exact B2290975
  · exact B2290979
  · exact B2290983
  · exact B2290987
  · exact B2290991
  · exact B2290995
  · exact B2290999
  · exact B2291003
  · exact B2291007
  · exact B2291011
  · exact B2291015
  · exact B2291019
  · exact B2291023
  · exact B2291027
  · exact B2291031
  · exact B2291035
  · exact B2291039
  · exact B2291043
  · exact B2291047
  · exact B2291051
  · exact B2291055
  · exact B2291059
  · exact B2291063
  · exact B2291067
  · exact B2291071
  · exact B2291075
  · exact B2291079
  · exact B2291083
  · exact B2291087
  · exact B2291091
  · exact B2291095
  · exact B2291099
  · exact B2291103
  · exact B2291107
  · exact B2291111
  · exact B2291115
  · exact B2291119
  · exact B2291123
  · exact B2291127
  · exact B2291131
  · exact B2291135
  · exact B2291139
  · exact B2291143
  · exact B2291147
  · exact B2291151
  · exact B2291155
  · exact B2291159
  · exact B2291163
  · exact B2291167
  · exact B2291171
  · exact B2291175
  · exact B2291179
  · exact B2291183
  · exact B2291187
  · exact B2291191
  · exact B2291195
  · exact B2291199
  · exact B2291203
  · exact B2291207
  · exact B2291211
  · exact B2291215
  · exact B2291219
  · exact B2291223
  · exact B2291227
  · exact B2291231
  · exact B2291235
  · exact B2291239
  · exact B2291243
  · exact B2291247
  · exact B2291251
  · exact B2291255
  · exact B2291259
  · exact B2291263
  · exact B2291267
  · exact B2291271
  · exact B2291275
  · exact B2291279
  · exact B2291283
  · exact B2291287
  · exact B2291291
  · exact B2291295
  · exact B2291299
  · exact B2291303
  · exact B2291307
  · exact B2291311
  · exact B2291315
  · exact B2291319
  · exact B2291323
  · exact B2291327
  · exact B2291331
  · exact B2291335
  · exact B2291339
  · exact B2291343
  · exact B2291347
  · exact B2291351
  · exact B2291355
  · exact B2291359
  · exact B2291363
  · exact B2291367
  · exact B2291371
  · exact B2291375
  · exact B2291379
  · exact B2291383
  · exact B2291387
  · exact B2291391
  · exact B2291395
  · exact B2291399
  · exact B2291403
  · exact B2291407
  · exact B2291411
  · exact B2291415
  · exact B2291419
  · exact B2291423
  · exact B2291427
  · exact B2291431
  · exact B2291435
theorem solution (m : ℕ) (hlo : 2289435 ≤ m) (hhi : m ≤ 2291435) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 572358 ≤ j := by omega
    have hj2 : j ≤ 572858 := by omega
    have hb : Blo 2289435 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
