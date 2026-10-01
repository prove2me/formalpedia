-- Prove2me | solution 1 for syracuse_descends_range_2125435_2127435
-- status  : ACCEPTED   (prove)
-- author  : @chstdu
-- created : 2026-09-23T17:17:01.624784+00:00
-- url     : https://prove2.me/submissions/7f5176d3-8689-4819-ab98-1ef195db59be

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

theorem B2690005 : Blo 2125435 2690005 := bbase (se 7 (by rfl) ⟨31523, by rfl⟩ : syracuseStep 2690005 = 63047) (by norm_num)
theorem B3586673 : Blo 2125435 3586673 := bstep (se 2 (by rfl) ⟨1345002, by rfl⟩ : syracuseStep 3586673 = 2690005) B2690005
theorem B2391115 : Blo 2125435 2391115 := bstep (se 1 (by rfl) ⟨1793336, by rfl⟩ : syracuseStep 2391115 = 3586673) B3586673
theorem B3188153 : Blo 2125435 3188153 := bstep (se 2 (by rfl) ⟨1195557, by rfl⟩ : syracuseStep 3188153 = 2391115) B2391115
theorem B2125435 : Blo 2125435 2125435 := bstep (se 1 (by rfl) ⟨1594076, by rfl⟩ : syracuseStep 2125435 = 3188153) B3188153
theorem B41976917 : Blo 2125435 41976917 := bbase (se 8 (by rfl) ⟨245958, by rfl⟩ : syracuseStep 41976917 = 491917) (by norm_num)
theorem B27984611 : Blo 2125435 27984611 := bstep (se 1 (by rfl) ⟨20988458, by rfl⟩ : syracuseStep 27984611 = 41976917) B41976917
theorem B18656407 : Blo 2125435 18656407 := bstep (se 1 (by rfl) ⟨13992305, by rfl⟩ : syracuseStep 18656407 = 27984611) B27984611
theorem B24875209 : Blo 2125435 24875209 := bstep (se 2 (by rfl) ⟨9328203, by rfl⟩ : syracuseStep 24875209 = 18656407) B18656407
theorem B33166945 : Blo 2125435 33166945 := bstep (se 2 (by rfl) ⟨12437604, by rfl⟩ : syracuseStep 33166945 = 24875209) B24875209
theorem B44222593 : Blo 2125435 44222593 := bstep (se 2 (by rfl) ⟨16583472, by rfl⟩ : syracuseStep 44222593 = 33166945) B33166945
theorem B58963457 : Blo 2125435 58963457 := bstep (se 2 (by rfl) ⟨22111296, by rfl⟩ : syracuseStep 58963457 = 44222593) B44222593
theorem B39308971 : Blo 2125435 39308971 := bstep (se 1 (by rfl) ⟨29481728, by rfl⟩ : syracuseStep 39308971 = 58963457) B58963457
theorem B52411961 : Blo 2125435 52411961 := bstep (se 2 (by rfl) ⟨19654485, by rfl⟩ : syracuseStep 52411961 = 39308971) B39308971
theorem B34941307 : Blo 2125435 34941307 := bstep (se 1 (by rfl) ⟨26205980, by rfl⟩ : syracuseStep 34941307 = 52411961) B52411961
theorem B46588409 : Blo 2125435 46588409 := bstep (se 2 (by rfl) ⟨17470653, by rfl⟩ : syracuseStep 46588409 = 34941307) B34941307
theorem B31058939 : Blo 2125435 31058939 := bstep (se 1 (by rfl) ⟨23294204, by rfl⟩ : syracuseStep 31058939 = 46588409) B46588409
theorem B20705959 : Blo 2125435 20705959 := bstep (se 1 (by rfl) ⟨15529469, by rfl⟩ : syracuseStep 20705959 = 31058939) B31058939
theorem B27607945 : Blo 2125435 27607945 := bstep (se 2 (by rfl) ⟨10352979, by rfl⟩ : syracuseStep 27607945 = 20705959) B20705959
theorem B36810593 : Blo 2125435 36810593 := bstep (se 2 (by rfl) ⟨13803972, by rfl⟩ : syracuseStep 36810593 = 27607945) B27607945
theorem B1570585301 : Blo 2125435 1570585301 := bstep (se 7 (by rfl) ⟨18405296, by rfl⟩ : syracuseStep 1570585301 = 36810593) B36810593
theorem B1047056867 : Blo 2125435 1047056867 := bstep (se 1 (by rfl) ⟨785292650, by rfl⟩ : syracuseStep 1047056867 = 1570585301) B1570585301
theorem B698037911 : Blo 2125435 698037911 := bstep (se 1 (by rfl) ⟨523528433, by rfl⟩ : syracuseStep 698037911 = 1047056867) B1047056867
theorem B465358607 : Blo 2125435 465358607 := bstep (se 1 (by rfl) ⟨349018955, by rfl⟩ : syracuseStep 465358607 = 698037911) B698037911
theorem B310239071 : Blo 2125435 310239071 := bstep (se 1 (by rfl) ⟨232679303, by rfl⟩ : syracuseStep 310239071 = 465358607) B465358607
theorem B206826047 : Blo 2125435 206826047 := bstep (se 1 (by rfl) ⟨155119535, by rfl⟩ : syracuseStep 206826047 = 310239071) B310239071
theorem B137884031 : Blo 2125435 137884031 := bstep (se 1 (by rfl) ⟨103413023, by rfl⟩ : syracuseStep 137884031 = 206826047) B206826047
theorem B91922687 : Blo 2125435 91922687 := bstep (se 1 (by rfl) ⟨68942015, by rfl⟩ : syracuseStep 91922687 = 137884031) B137884031
theorem B61281791 : Blo 2125435 61281791 := bstep (se 1 (by rfl) ⟨45961343, by rfl⟩ : syracuseStep 61281791 = 91922687) B91922687
theorem B40854527 : Blo 2125435 40854527 := bstep (se 1 (by rfl) ⟨30640895, by rfl⟩ : syracuseStep 40854527 = 61281791) B61281791
theorem B27236351 : Blo 2125435 27236351 := bstep (se 1 (by rfl) ⟨20427263, by rfl⟩ : syracuseStep 27236351 = 40854527) B40854527
theorem B18157567 : Blo 2125435 18157567 := bstep (se 1 (by rfl) ⟨13618175, by rfl⟩ : syracuseStep 18157567 = 27236351) B27236351
theorem B24210089 : Blo 2125435 24210089 := bstep (se 2 (by rfl) ⟨9078783, by rfl⟩ : syracuseStep 24210089 = 18157567) B18157567
theorem B16140059 : Blo 2125435 16140059 := bstep (se 1 (by rfl) ⟨12105044, by rfl⟩ : syracuseStep 16140059 = 24210089) B24210089
theorem B10760039 : Blo 2125435 10760039 := bstep (se 1 (by rfl) ⟨8070029, by rfl⟩ : syracuseStep 10760039 = 16140059) B16140059
theorem B7173359 : Blo 2125435 7173359 := bstep (se 1 (by rfl) ⟨5380019, by rfl⟩ : syracuseStep 7173359 = 10760039) B10760039
theorem B4782239 : Blo 2125435 4782239 := bstep (se 1 (by rfl) ⟨3586679, by rfl⟩ : syracuseStep 4782239 = 7173359) B7173359
theorem B3188159 : Blo 2125435 3188159 := bstep (se 1 (by rfl) ⟨2391119, by rfl⟩ : syracuseStep 3188159 = 4782239) B4782239
theorem B2125439 : Blo 2125435 2125439 := bstep (se 1 (by rfl) ⟨1594079, by rfl⟩ : syracuseStep 2125439 = 3188159) B3188159
theorem B3188165 : Blo 2125435 3188165 := bbase (se 4 (by rfl) ⟨298890, by rfl⟩ : syracuseStep 3188165 = 597781) (by norm_num)
theorem B2125443 : Blo 2125435 2125443 := bstep (se 1 (by rfl) ⟨1594082, by rfl⟩ : syracuseStep 2125443 = 3188165) B3188165
theorem B3586693 : Blo 2125435 3586693 := bbase (se 4 (by rfl) ⟨336252, by rfl⟩ : syracuseStep 3586693 = 672505) (by norm_num)
theorem B4782257 : Blo 2125435 4782257 := bstep (se 2 (by rfl) ⟨1793346, by rfl⟩ : syracuseStep 4782257 = 3586693) B3586693
theorem B3188171 : Blo 2125435 3188171 := bstep (se 1 (by rfl) ⟨2391128, by rfl⟩ : syracuseStep 3188171 = 4782257) B4782257
theorem B2125447 : Blo 2125435 2125447 := bstep (se 1 (by rfl) ⟨1594085, by rfl⟩ : syracuseStep 2125447 = 3188171) B3188171
theorem B2391133 : Blo 2125435 2391133 := bbase (se 3 (by rfl) ⟨448337, by rfl⟩ : syracuseStep 2391133 = 896675) (by norm_num)
theorem B3188177 : Blo 2125435 3188177 := bstep (se 2 (by rfl) ⟨1195566, by rfl⟩ : syracuseStep 3188177 = 2391133) B2391133
theorem B2125451 : Blo 2125435 2125451 := bstep (se 1 (by rfl) ⟨1594088, by rfl⟩ : syracuseStep 2125451 = 3188177) B3188177
theorem B7173413 : Blo 2125435 7173413 := bbase (se 4 (by rfl) ⟨672507, by rfl⟩ : syracuseStep 7173413 = 1345015) (by norm_num)
theorem B4782275 : Blo 2125435 4782275 := bstep (se 1 (by rfl) ⟨3586706, by rfl⟩ : syracuseStep 4782275 = 7173413) B7173413
theorem B3188183 : Blo 2125435 3188183 := bstep (se 1 (by rfl) ⟨2391137, by rfl⟩ : syracuseStep 3188183 = 4782275) B4782275
theorem B2125455 : Blo 2125435 2125455 := bstep (se 1 (by rfl) ⟨1594091, by rfl⟩ : syracuseStep 2125455 = 3188183) B3188183
theorem B3188189 : Blo 2125435 3188189 := bbase (se 3 (by rfl) ⟨597785, by rfl⟩ : syracuseStep 3188189 = 1195571) (by norm_num)
theorem B2125459 : Blo 2125435 2125459 := bstep (se 1 (by rfl) ⟨1594094, by rfl⟩ : syracuseStep 2125459 = 3188189) B3188189
theorem B4782293 : Blo 2125435 4782293 := bbase (se 7 (by rfl) ⟨56042, by rfl⟩ : syracuseStep 4782293 = 112085) (by norm_num)
theorem B3188195 : Blo 2125435 3188195 := bstep (se 1 (by rfl) ⟨2391146, by rfl⟩ : syracuseStep 3188195 = 4782293) B4782293
theorem B2125463 : Blo 2125435 2125463 := bstep (se 1 (by rfl) ⟨1594097, by rfl⟩ : syracuseStep 2125463 = 3188195) B3188195
theorem B5527901 : Blo 2125435 5527901 := bbase (se 3 (by rfl) ⟨1036481, by rfl⟩ : syracuseStep 5527901 = 2072963) (by norm_num)
theorem B3685267 : Blo 2125435 3685267 := bstep (se 1 (by rfl) ⟨2763950, by rfl⟩ : syracuseStep 3685267 = 5527901) B5527901
theorem B19654757 : Blo 2125435 19654757 := bstep (se 4 (by rfl) ⟨1842633, by rfl⟩ : syracuseStep 19654757 = 3685267) B3685267
theorem B13103171 : Blo 2125435 13103171 := bstep (se 1 (by rfl) ⟨9827378, by rfl⟩ : syracuseStep 13103171 = 19654757) B19654757
theorem B8735447 : Blo 2125435 8735447 := bstep (se 1 (by rfl) ⟨6551585, by rfl⟩ : syracuseStep 8735447 = 13103171) B13103171
theorem B5823631 : Blo 2125435 5823631 := bstep (se 1 (by rfl) ⟨4367723, by rfl⟩ : syracuseStep 5823631 = 8735447) B8735447
theorem B7764841 : Blo 2125435 7764841 := bstep (se 2 (by rfl) ⟨2911815, by rfl⟩ : syracuseStep 7764841 = 5823631) B5823631
theorem B41412485 : Blo 2125435 41412485 := bstep (se 4 (by rfl) ⟨3882420, by rfl⟩ : syracuseStep 41412485 = 7764841) B7764841
theorem B27608323 : Blo 2125435 27608323 := bstep (se 1 (by rfl) ⟨20706242, by rfl⟩ : syracuseStep 27608323 = 41412485) B41412485
theorem B36811097 : Blo 2125435 36811097 := bstep (se 2 (by rfl) ⟨13804161, by rfl⟩ : syracuseStep 36811097 = 27608323) B27608323
theorem B24540731 : Blo 2125435 24540731 := bstep (se 1 (by rfl) ⟨18405548, by rfl⟩ : syracuseStep 24540731 = 36811097) B36811097
theorem B16360487 : Blo 2125435 16360487 := bstep (se 1 (by rfl) ⟨12270365, by rfl⟩ : syracuseStep 16360487 = 24540731) B24540731
theorem B10906991 : Blo 2125435 10906991 := bstep (se 1 (by rfl) ⟨8180243, by rfl⟩ : syracuseStep 10906991 = 16360487) B16360487
theorem B7271327 : Blo 2125435 7271327 := bstep (se 1 (by rfl) ⟨5453495, by rfl⟩ : syracuseStep 7271327 = 10906991) B10906991
theorem B19390205 : Blo 2125435 19390205 := bstep (se 3 (by rfl) ⟨3635663, by rfl⟩ : syracuseStep 19390205 = 7271327) B7271327
theorem B12926803 : Blo 2125435 12926803 := bstep (se 1 (by rfl) ⟨9695102, by rfl⟩ : syracuseStep 12926803 = 19390205) B19390205
theorem B17235737 : Blo 2125435 17235737 := bstep (se 2 (by rfl) ⟨6463401, by rfl⟩ : syracuseStep 17235737 = 12926803) B12926803
theorem B11490491 : Blo 2125435 11490491 := bstep (se 1 (by rfl) ⟨8617868, by rfl⟩ : syracuseStep 11490491 = 17235737) B17235737
theorem B7660327 : Blo 2125435 7660327 := bstep (se 1 (by rfl) ⟨5745245, by rfl⟩ : syracuseStep 7660327 = 11490491) B11490491
theorem B10213769 : Blo 2125435 10213769 := bstep (se 2 (by rfl) ⟨3830163, by rfl⟩ : syracuseStep 10213769 = 7660327) B7660327
theorem B6809179 : Blo 2125435 6809179 := bstep (se 1 (by rfl) ⟨5106884, by rfl⟩ : syracuseStep 6809179 = 10213769) B10213769
theorem B9078905 : Blo 2125435 9078905 := bstep (se 2 (by rfl) ⟨3404589, by rfl⟩ : syracuseStep 9078905 = 6809179) B6809179
theorem B6052603 : Blo 2125435 6052603 := bstep (se 1 (by rfl) ⟨4539452, by rfl⟩ : syracuseStep 6052603 = 9078905) B9078905
theorem B8070137 : Blo 2125435 8070137 := bstep (se 2 (by rfl) ⟨3026301, by rfl⟩ : syracuseStep 8070137 = 6052603) B6052603
theorem B5380091 : Blo 2125435 5380091 := bstep (se 1 (by rfl) ⟨4035068, by rfl⟩ : syracuseStep 5380091 = 8070137) B8070137
theorem B3586727 : Blo 2125435 3586727 := bstep (se 1 (by rfl) ⟨2690045, by rfl⟩ : syracuseStep 3586727 = 5380091) B5380091
theorem B2391151 : Blo 2125435 2391151 := bstep (se 1 (by rfl) ⟨1793363, by rfl⟩ : syracuseStep 2391151 = 3586727) B3586727
theorem B3188201 : Blo 2125435 3188201 := bstep (se 2 (by rfl) ⟨1195575, by rfl⟩ : syracuseStep 3188201 = 2391151) B2391151
theorem B2125467 : Blo 2125435 2125467 := bstep (se 1 (by rfl) ⟨1594100, by rfl⟩ : syracuseStep 2125467 = 3188201) B3188201
theorem B5106893 : Blo 2125435 5106893 := bbase (se 3 (by rfl) ⟨957542, by rfl⟩ : syracuseStep 5106893 = 1915085) (by norm_num)
theorem B13618381 : Blo 2125435 13618381 := bstep (se 3 (by rfl) ⟨2553446, by rfl⟩ : syracuseStep 13618381 = 5106893) B5106893
theorem B18157841 : Blo 2125435 18157841 := bstep (se 2 (by rfl) ⟨6809190, by rfl⟩ : syracuseStep 18157841 = 13618381) B13618381
theorem B12105227 : Blo 2125435 12105227 := bstep (se 1 (by rfl) ⟨9078920, by rfl⟩ : syracuseStep 12105227 = 18157841) B18157841
theorem B8070151 : Blo 2125435 8070151 := bstep (se 1 (by rfl) ⟨6052613, by rfl⟩ : syracuseStep 8070151 = 12105227) B12105227
theorem B10760201 : Blo 2125435 10760201 := bstep (se 2 (by rfl) ⟨4035075, by rfl⟩ : syracuseStep 10760201 = 8070151) B8070151
theorem B7173467 : Blo 2125435 7173467 := bstep (se 1 (by rfl) ⟨5380100, by rfl⟩ : syracuseStep 7173467 = 10760201) B10760201
theorem B4782311 : Blo 2125435 4782311 := bstep (se 1 (by rfl) ⟨3586733, by rfl⟩ : syracuseStep 4782311 = 7173467) B7173467
theorem B3188207 : Blo 2125435 3188207 := bstep (se 1 (by rfl) ⟨2391155, by rfl⟩ : syracuseStep 3188207 = 4782311) B4782311
theorem B2125471 : Blo 2125435 2125471 := bstep (se 1 (by rfl) ⟨1594103, by rfl⟩ : syracuseStep 2125471 = 3188207) B3188207
theorem B3188213 : Blo 2125435 3188213 := bbase (se 5 (by rfl) ⟨149447, by rfl⟩ : syracuseStep 3188213 = 298895) (by norm_num)
theorem B2125475 : Blo 2125435 2125475 := bstep (se 1 (by rfl) ⟨1594106, by rfl⟩ : syracuseStep 2125475 = 3188213) B3188213
theorem B2553457 : Blo 2125435 2553457 := bbase (se 2 (by rfl) ⟨957546, by rfl⟩ : syracuseStep 2553457 = 1915093) (by norm_num)
theorem B3404609 : Blo 2125435 3404609 := bstep (se 2 (by rfl) ⟨1276728, by rfl⟩ : syracuseStep 3404609 = 2553457) B2553457
theorem B2269739 : Blo 2125435 2269739 := bstep (se 1 (by rfl) ⟨1702304, by rfl⟩ : syracuseStep 2269739 = 3404609) B3404609
theorem B6052637 : Blo 2125435 6052637 := bstep (se 3 (by rfl) ⟨1134869, by rfl⟩ : syracuseStep 6052637 = 2269739) B2269739
theorem B4035091 : Blo 2125435 4035091 := bstep (se 1 (by rfl) ⟨3026318, by rfl⟩ : syracuseStep 4035091 = 6052637) B6052637
theorem B5380121 : Blo 2125435 5380121 := bstep (se 2 (by rfl) ⟨2017545, by rfl⟩ : syracuseStep 5380121 = 4035091) B4035091
theorem B3586747 : Blo 2125435 3586747 := bstep (se 1 (by rfl) ⟨2690060, by rfl⟩ : syracuseStep 3586747 = 5380121) B5380121
theorem B4782329 : Blo 2125435 4782329 := bstep (se 2 (by rfl) ⟨1793373, by rfl⟩ : syracuseStep 4782329 = 3586747) B3586747
theorem B3188219 : Blo 2125435 3188219 := bstep (se 1 (by rfl) ⟨2391164, by rfl⟩ : syracuseStep 3188219 = 4782329) B4782329
theorem B2125479 : Blo 2125435 2125479 := bstep (se 1 (by rfl) ⟨1594109, by rfl⟩ : syracuseStep 2125479 = 3188219) B3188219
theorem B2391169 : Blo 2125435 2391169 := bbase (se 2 (by rfl) ⟨896688, by rfl⟩ : syracuseStep 2391169 = 1793377) (by norm_num)
theorem B3188225 : Blo 2125435 3188225 := bstep (se 2 (by rfl) ⟨1195584, by rfl⟩ : syracuseStep 3188225 = 2391169) B2391169
theorem B2125483 : Blo 2125435 2125483 := bstep (se 1 (by rfl) ⟨1594112, by rfl⟩ : syracuseStep 2125483 = 3188225) B3188225
theorem B5380141 : Blo 2125435 5380141 := bbase (se 3 (by rfl) ⟨1008776, by rfl⟩ : syracuseStep 5380141 = 2017553) (by norm_num)
theorem B7173521 : Blo 2125435 7173521 := bstep (se 2 (by rfl) ⟨2690070, by rfl⟩ : syracuseStep 7173521 = 5380141) B5380141
theorem B4782347 : Blo 2125435 4782347 := bstep (se 1 (by rfl) ⟨3586760, by rfl⟩ : syracuseStep 4782347 = 7173521) B7173521
theorem B3188231 : Blo 2125435 3188231 := bstep (se 1 (by rfl) ⟨2391173, by rfl⟩ : syracuseStep 3188231 = 4782347) B4782347
theorem B2125487 : Blo 2125435 2125487 := bstep (se 1 (by rfl) ⟨1594115, by rfl⟩ : syracuseStep 2125487 = 3188231) B3188231
theorem B3188237 : Blo 2125435 3188237 := bbase (se 3 (by rfl) ⟨597794, by rfl⟩ : syracuseStep 3188237 = 1195589) (by norm_num)
theorem B2125491 : Blo 2125435 2125491 := bstep (se 1 (by rfl) ⟨1594118, by rfl⟩ : syracuseStep 2125491 = 3188237) B3188237
theorem B4782365 : Blo 2125435 4782365 := bbase (se 3 (by rfl) ⟨896693, by rfl⟩ : syracuseStep 4782365 = 1793387) (by norm_num)
theorem B3188243 : Blo 2125435 3188243 := bstep (se 1 (by rfl) ⟨2391182, by rfl⟩ : syracuseStep 3188243 = 4782365) B4782365
theorem B2125495 : Blo 2125435 2125495 := bstep (se 1 (by rfl) ⟨1594121, by rfl⟩ : syracuseStep 2125495 = 3188243) B3188243
theorem B3586781 : Blo 2125435 3586781 := bbase (se 3 (by rfl) ⟨672521, by rfl⟩ : syracuseStep 3586781 = 1345043) (by norm_num)
theorem B2391187 : Blo 2125435 2391187 := bstep (se 1 (by rfl) ⟨1793390, by rfl⟩ : syracuseStep 2391187 = 3586781) B3586781
theorem B3188249 : Blo 2125435 3188249 := bstep (se 2 (by rfl) ⟨1195593, by rfl⟩ : syracuseStep 3188249 = 2391187) B2391187
theorem B2125499 : Blo 2125435 2125499 := bstep (se 1 (by rfl) ⟨1594124, by rfl⟩ : syracuseStep 2125499 = 3188249) B3188249
theorem B2553485 : Blo 2125435 2553485 := bbase (se 3 (by rfl) ⟨478778, by rfl⟩ : syracuseStep 2553485 = 957557) (by norm_num)
theorem B6809293 : Blo 2125435 6809293 := bstep (se 3 (by rfl) ⟨1276742, by rfl⟩ : syracuseStep 6809293 = 2553485) B2553485
theorem B9079057 : Blo 2125435 9079057 := bstep (se 2 (by rfl) ⟨3404646, by rfl⟩ : syracuseStep 9079057 = 6809293) B6809293
theorem B12105409 : Blo 2125435 12105409 := bstep (se 2 (by rfl) ⟨4539528, by rfl⟩ : syracuseStep 12105409 = 9079057) B9079057
theorem B16140545 : Blo 2125435 16140545 := bstep (se 2 (by rfl) ⟨6052704, by rfl⟩ : syracuseStep 16140545 = 12105409) B12105409
theorem B10760363 : Blo 2125435 10760363 := bstep (se 1 (by rfl) ⟨8070272, by rfl⟩ : syracuseStep 10760363 = 16140545) B16140545
theorem B7173575 : Blo 2125435 7173575 := bstep (se 1 (by rfl) ⟨5380181, by rfl⟩ : syracuseStep 7173575 = 10760363) B10760363
theorem B4782383 : Blo 2125435 4782383 := bstep (se 1 (by rfl) ⟨3586787, by rfl⟩ : syracuseStep 4782383 = 7173575) B7173575
theorem B3188255 : Blo 2125435 3188255 := bstep (se 1 (by rfl) ⟨2391191, by rfl⟩ : syracuseStep 3188255 = 4782383) B4782383
theorem B2125503 : Blo 2125435 2125503 := bstep (se 1 (by rfl) ⟨1594127, by rfl⟩ : syracuseStep 2125503 = 3188255) B3188255
theorem B3188261 : Blo 2125435 3188261 := bbase (se 4 (by rfl) ⟨298899, by rfl⟩ : syracuseStep 3188261 = 597799) (by norm_num)
theorem B2125507 : Blo 2125435 2125507 := bstep (se 1 (by rfl) ⟨1594130, by rfl⟩ : syracuseStep 2125507 = 3188261) B3188261
theorem B2690101 : Blo 2125435 2690101 := bbase (se 5 (by rfl) ⟨126098, by rfl⟩ : syracuseStep 2690101 = 252197) (by norm_num)
theorem B3586801 : Blo 2125435 3586801 := bstep (se 2 (by rfl) ⟨1345050, by rfl⟩ : syracuseStep 3586801 = 2690101) B2690101
theorem B4782401 : Blo 2125435 4782401 := bstep (se 2 (by rfl) ⟨1793400, by rfl⟩ : syracuseStep 4782401 = 3586801) B3586801
theorem B3188267 : Blo 2125435 3188267 := bstep (se 1 (by rfl) ⟨2391200, by rfl⟩ : syracuseStep 3188267 = 4782401) B4782401
theorem B2125511 : Blo 2125435 2125511 := bstep (se 1 (by rfl) ⟨1594133, by rfl⟩ : syracuseStep 2125511 = 3188267) B3188267
theorem B2391205 : Blo 2125435 2391205 := bbase (se 4 (by rfl) ⟨224175, by rfl⟩ : syracuseStep 2391205 = 448351) (by norm_num)
theorem B3188273 : Blo 2125435 3188273 := bstep (se 2 (by rfl) ⟨1195602, by rfl⟩ : syracuseStep 3188273 = 2391205) B2391205
theorem B2125515 : Blo 2125435 2125515 := bstep (se 1 (by rfl) ⟨1594136, by rfl⟩ : syracuseStep 2125515 = 3188273) B3188273
theorem B2872693 : Blo 2125435 2872693 := bbase (se 5 (by rfl) ⟨134657, by rfl⟩ : syracuseStep 2872693 = 269315) (by norm_num)
theorem B3830257 : Blo 2125435 3830257 := bstep (se 2 (by rfl) ⟨1436346, by rfl⟩ : syracuseStep 3830257 = 2872693) B2872693
theorem B20428037 : Blo 2125435 20428037 := bstep (se 4 (by rfl) ⟨1915128, by rfl⟩ : syracuseStep 20428037 = 3830257) B3830257
theorem B13618691 : Blo 2125435 13618691 := bstep (se 1 (by rfl) ⟨10214018, by rfl⟩ : syracuseStep 13618691 = 20428037) B20428037
theorem B9079127 : Blo 2125435 9079127 := bstep (se 1 (by rfl) ⟨6809345, by rfl⟩ : syracuseStep 9079127 = 13618691) B13618691
theorem B6052751 : Blo 2125435 6052751 := bstep (se 1 (by rfl) ⟨4539563, by rfl⟩ : syracuseStep 6052751 = 9079127) B9079127
theorem B4035167 : Blo 2125435 4035167 := bstep (se 1 (by rfl) ⟨3026375, by rfl⟩ : syracuseStep 4035167 = 6052751) B6052751
theorem B2690111 : Blo 2125435 2690111 := bstep (se 1 (by rfl) ⟨2017583, by rfl⟩ : syracuseStep 2690111 = 4035167) B4035167
theorem B7173629 : Blo 2125435 7173629 := bstep (se 3 (by rfl) ⟨1345055, by rfl⟩ : syracuseStep 7173629 = 2690111) B2690111
theorem B4782419 : Blo 2125435 4782419 := bstep (se 1 (by rfl) ⟨3586814, by rfl⟩ : syracuseStep 4782419 = 7173629) B7173629
theorem B3188279 : Blo 2125435 3188279 := bstep (se 1 (by rfl) ⟨2391209, by rfl⟩ : syracuseStep 3188279 = 4782419) B4782419
theorem B2125519 : Blo 2125435 2125519 := bstep (se 1 (by rfl) ⟨1594139, by rfl⟩ : syracuseStep 2125519 = 3188279) B3188279
theorem B3188285 : Blo 2125435 3188285 := bbase (se 3 (by rfl) ⟨597803, by rfl⟩ : syracuseStep 3188285 = 1195607) (by norm_num)
theorem B2125523 : Blo 2125435 2125523 := bstep (se 1 (by rfl) ⟨1594142, by rfl⟩ : syracuseStep 2125523 = 3188285) B3188285
theorem B4782437 : Blo 2125435 4782437 := bbase (se 4 (by rfl) ⟨448353, by rfl⟩ : syracuseStep 4782437 = 896707) (by norm_num)
theorem B3188291 : Blo 2125435 3188291 := bstep (se 1 (by rfl) ⟨2391218, by rfl⟩ : syracuseStep 3188291 = 4782437) B4782437
theorem B2125527 : Blo 2125435 2125527 := bstep (se 1 (by rfl) ⟨1594145, by rfl⟩ : syracuseStep 2125527 = 3188291) B3188291
theorem B5380253 : Blo 2125435 5380253 := bbase (se 3 (by rfl) ⟨1008797, by rfl⟩ : syracuseStep 5380253 = 2017595) (by norm_num)
theorem B3586835 : Blo 2125435 3586835 := bstep (se 1 (by rfl) ⟨2690126, by rfl⟩ : syracuseStep 3586835 = 5380253) B5380253
theorem B2391223 : Blo 2125435 2391223 := bstep (se 1 (by rfl) ⟨1793417, by rfl⟩ : syracuseStep 2391223 = 3586835) B3586835
theorem B3188297 : Blo 2125435 3188297 := bstep (se 2 (by rfl) ⟨1195611, by rfl⟩ : syracuseStep 3188297 = 2391223) B2391223
theorem B2125531 : Blo 2125435 2125531 := bstep (se 1 (by rfl) ⟨1594148, by rfl⟩ : syracuseStep 2125531 = 3188297) B3188297
theorem B4035197 : Blo 2125435 4035197 := bbase (se 3 (by rfl) ⟨756599, by rfl⟩ : syracuseStep 4035197 = 1513199) (by norm_num)
theorem B10760525 : Blo 2125435 10760525 := bstep (se 3 (by rfl) ⟨2017598, by rfl⟩ : syracuseStep 10760525 = 4035197) B4035197
theorem B7173683 : Blo 2125435 7173683 := bstep (se 1 (by rfl) ⟨5380262, by rfl⟩ : syracuseStep 7173683 = 10760525) B10760525
theorem B4782455 : Blo 2125435 4782455 := bstep (se 1 (by rfl) ⟨3586841, by rfl⟩ : syracuseStep 4782455 = 7173683) B7173683
theorem B3188303 : Blo 2125435 3188303 := bstep (se 1 (by rfl) ⟨2391227, by rfl⟩ : syracuseStep 3188303 = 4782455) B4782455
theorem B2125535 : Blo 2125435 2125535 := bstep (se 1 (by rfl) ⟨1594151, by rfl⟩ : syracuseStep 2125535 = 3188303) B3188303
theorem B3188309 : Blo 2125435 3188309 := bbase (se 8 (by rfl) ⟨18681, by rfl⟩ : syracuseStep 3188309 = 37363) (by norm_num)
theorem B2125539 : Blo 2125435 2125539 := bstep (se 1 (by rfl) ⟨1594154, by rfl⟩ : syracuseStep 2125539 = 3188309) B3188309
theorem B4847725 : Blo 2125435 4847725 := bbase (se 3 (by rfl) ⟨908948, by rfl⟩ : syracuseStep 4847725 = 1817897) (by norm_num)
theorem B6463633 : Blo 2125435 6463633 := bstep (se 2 (by rfl) ⟨2423862, by rfl⟩ : syracuseStep 6463633 = 4847725) B4847725
theorem B8618177 : Blo 2125435 8618177 := bstep (se 2 (by rfl) ⟨3231816, by rfl⟩ : syracuseStep 8618177 = 6463633) B6463633
theorem B5745451 : Blo 2125435 5745451 := bstep (se 1 (by rfl) ⟨4309088, by rfl⟩ : syracuseStep 5745451 = 8618177) B8618177
theorem B7660601 : Blo 2125435 7660601 := bstep (se 2 (by rfl) ⟨2872725, by rfl⟩ : syracuseStep 7660601 = 5745451) B5745451
theorem B5107067 : Blo 2125435 5107067 := bstep (se 1 (by rfl) ⟨3830300, by rfl⟩ : syracuseStep 5107067 = 7660601) B7660601
theorem B3404711 : Blo 2125435 3404711 := bstep (se 1 (by rfl) ⟨2553533, by rfl⟩ : syracuseStep 3404711 = 5107067) B5107067
theorem B9079229 : Blo 2125435 9079229 := bstep (se 3 (by rfl) ⟨1702355, by rfl⟩ : syracuseStep 9079229 = 3404711) B3404711
theorem B6052819 : Blo 2125435 6052819 := bstep (se 1 (by rfl) ⟨4539614, by rfl⟩ : syracuseStep 6052819 = 9079229) B9079229
theorem B8070425 : Blo 2125435 8070425 := bstep (se 2 (by rfl) ⟨3026409, by rfl⟩ : syracuseStep 8070425 = 6052819) B6052819
theorem B5380283 : Blo 2125435 5380283 := bstep (se 1 (by rfl) ⟨4035212, by rfl⟩ : syracuseStep 5380283 = 8070425) B8070425
theorem B3586855 : Blo 2125435 3586855 := bstep (se 1 (by rfl) ⟨2690141, by rfl⟩ : syracuseStep 3586855 = 5380283) B5380283
theorem B4782473 : Blo 2125435 4782473 := bstep (se 2 (by rfl) ⟨1793427, by rfl⟩ : syracuseStep 4782473 = 3586855) B3586855
theorem B3188315 : Blo 2125435 3188315 := bstep (se 1 (by rfl) ⟨2391236, by rfl⟩ : syracuseStep 3188315 = 4782473) B4782473
theorem B2125543 : Blo 2125435 2125543 := bstep (se 1 (by rfl) ⟨1594157, by rfl⟩ : syracuseStep 2125543 = 3188315) B3188315
theorem B2391241 : Blo 2125435 2391241 := bbase (se 2 (by rfl) ⟨896715, by rfl⟩ : syracuseStep 2391241 = 1793431) (by norm_num)
theorem B3188321 : Blo 2125435 3188321 := bstep (se 2 (by rfl) ⟨1195620, by rfl⟩ : syracuseStep 3188321 = 2391241) B2391241
theorem B2125547 : Blo 2125435 2125547 := bstep (se 1 (by rfl) ⟨1594160, by rfl⟩ : syracuseStep 2125547 = 3188321) B3188321
theorem B5528117 : Blo 2125435 5528117 := bbase (se 5 (by rfl) ⟨259130, by rfl⟩ : syracuseStep 5528117 = 518261) (by norm_num)
theorem B3685411 : Blo 2125435 3685411 := bstep (se 1 (by rfl) ⟨2764058, by rfl⟩ : syracuseStep 3685411 = 5528117) B5528117
theorem B19655525 : Blo 2125435 19655525 := bstep (se 4 (by rfl) ⟨1842705, by rfl⟩ : syracuseStep 19655525 = 3685411) B3685411
theorem B13103683 : Blo 2125435 13103683 := bstep (se 1 (by rfl) ⟨9827762, by rfl⟩ : syracuseStep 13103683 = 19655525) B19655525
theorem B69886309 : Blo 2125435 69886309 := bstep (se 4 (by rfl) ⟨6551841, by rfl⟩ : syracuseStep 69886309 = 13103683) B13103683
theorem B93181745 : Blo 2125435 93181745 := bstep (se 2 (by rfl) ⟨34943154, by rfl⟩ : syracuseStep 93181745 = 69886309) B69886309
theorem B62121163 : Blo 2125435 62121163 := bstep (se 1 (by rfl) ⟨46590872, by rfl⟩ : syracuseStep 62121163 = 93181745) B93181745
theorem B82828217 : Blo 2125435 82828217 := bstep (se 2 (by rfl) ⟨31060581, by rfl⟩ : syracuseStep 82828217 = 62121163) B62121163
theorem B220875245 : Blo 2125435 220875245 := bstep (se 3 (by rfl) ⟨41414108, by rfl⟩ : syracuseStep 220875245 = 82828217) B82828217
theorem B147250163 : Blo 2125435 147250163 := bstep (se 1 (by rfl) ⟨110437622, by rfl⟩ : syracuseStep 147250163 = 220875245) B220875245
theorem B98166775 : Blo 2125435 98166775 := bstep (se 1 (by rfl) ⟨73625081, by rfl⟩ : syracuseStep 98166775 = 147250163) B147250163
theorem B130889033 : Blo 2125435 130889033 := bstep (se 2 (by rfl) ⟨49083387, by rfl⟩ : syracuseStep 130889033 = 98166775) B98166775
theorem B87259355 : Blo 2125435 87259355 := bstep (se 1 (by rfl) ⟨65444516, by rfl⟩ : syracuseStep 87259355 = 130889033) B130889033
theorem B58172903 : Blo 2125435 58172903 := bstep (se 1 (by rfl) ⟨43629677, by rfl⟩ : syracuseStep 58172903 = 87259355) B87259355
theorem B38781935 : Blo 2125435 38781935 := bstep (se 1 (by rfl) ⟨29086451, by rfl⟩ : syracuseStep 38781935 = 58172903) B58172903
theorem B25854623 : Blo 2125435 25854623 := bstep (se 1 (by rfl) ⟨19390967, by rfl⟩ : syracuseStep 25854623 = 38781935) B38781935
theorem B17236415 : Blo 2125435 17236415 := bstep (se 1 (by rfl) ⟨12927311, by rfl⟩ : syracuseStep 17236415 = 25854623) B25854623
theorem B11490943 : Blo 2125435 11490943 := bstep (se 1 (by rfl) ⟨8618207, by rfl⟩ : syracuseStep 11490943 = 17236415) B17236415
theorem B15321257 : Blo 2125435 15321257 := bstep (se 2 (by rfl) ⟨5745471, by rfl⟩ : syracuseStep 15321257 = 11490943) B11490943
theorem B10214171 : Blo 2125435 10214171 := bstep (se 1 (by rfl) ⟨7660628, by rfl⟩ : syracuseStep 10214171 = 15321257) B15321257
theorem B6809447 : Blo 2125435 6809447 := bstep (se 1 (by rfl) ⟨5107085, by rfl⟩ : syracuseStep 6809447 = 10214171) B10214171
theorem B18158525 : Blo 2125435 18158525 := bstep (se 3 (by rfl) ⟨3404723, by rfl⟩ : syracuseStep 18158525 = 6809447) B6809447
theorem B12105683 : Blo 2125435 12105683 := bstep (se 1 (by rfl) ⟨9079262, by rfl⟩ : syracuseStep 12105683 = 18158525) B18158525
theorem B8070455 : Blo 2125435 8070455 := bstep (se 1 (by rfl) ⟨6052841, by rfl⟩ : syracuseStep 8070455 = 12105683) B12105683
theorem B5380303 : Blo 2125435 5380303 := bstep (se 1 (by rfl) ⟨4035227, by rfl⟩ : syracuseStep 5380303 = 8070455) B8070455
theorem B7173737 : Blo 2125435 7173737 := bstep (se 2 (by rfl) ⟨2690151, by rfl⟩ : syracuseStep 7173737 = 5380303) B5380303
theorem B4782491 : Blo 2125435 4782491 := bstep (se 1 (by rfl) ⟨3586868, by rfl⟩ : syracuseStep 4782491 = 7173737) B7173737
theorem B3188327 : Blo 2125435 3188327 := bstep (se 1 (by rfl) ⟨2391245, by rfl⟩ : syracuseStep 3188327 = 4782491) B4782491
theorem B2125551 : Blo 2125435 2125551 := bstep (se 1 (by rfl) ⟨1594163, by rfl⟩ : syracuseStep 2125551 = 3188327) B3188327
theorem B3188333 : Blo 2125435 3188333 := bbase (se 3 (by rfl) ⟨597812, by rfl⟩ : syracuseStep 3188333 = 1195625) (by norm_num)
theorem B2125555 : Blo 2125435 2125555 := bstep (se 1 (by rfl) ⟨1594166, by rfl⟩ : syracuseStep 2125555 = 3188333) B3188333
theorem B4782509 : Blo 2125435 4782509 := bbase (se 3 (by rfl) ⟨896720, by rfl⟩ : syracuseStep 4782509 = 1793441) (by norm_num)
theorem B3188339 : Blo 2125435 3188339 := bstep (se 1 (by rfl) ⟨2391254, by rfl⟩ : syracuseStep 3188339 = 4782509) B4782509
theorem B2125559 : Blo 2125435 2125559 := bstep (se 1 (by rfl) ⟨1594169, by rfl⟩ : syracuseStep 2125559 = 3188339) B3188339
theorem B2269829 : Blo 2125435 2269829 := bbase (se 4 (by rfl) ⟨212796, by rfl⟩ : syracuseStep 2269829 = 425593) (by norm_num)
theorem B6052877 : Blo 2125435 6052877 := bstep (se 3 (by rfl) ⟨1134914, by rfl⟩ : syracuseStep 6052877 = 2269829) B2269829
theorem B4035251 : Blo 2125435 4035251 := bstep (se 1 (by rfl) ⟨3026438, by rfl⟩ : syracuseStep 4035251 = 6052877) B6052877
theorem B2690167 : Blo 2125435 2690167 := bstep (se 1 (by rfl) ⟨2017625, by rfl⟩ : syracuseStep 2690167 = 4035251) B4035251
theorem B3586889 : Blo 2125435 3586889 := bstep (se 2 (by rfl) ⟨1345083, by rfl⟩ : syracuseStep 3586889 = 2690167) B2690167
theorem B2391259 : Blo 2125435 2391259 := bstep (se 1 (by rfl) ⟨1793444, by rfl⟩ : syracuseStep 2391259 = 3586889) B3586889
theorem B3188345 : Blo 2125435 3188345 := bstep (se 2 (by rfl) ⟨1195629, by rfl⟩ : syracuseStep 3188345 = 2391259) B2391259
theorem B2125563 : Blo 2125435 2125563 := bstep (se 1 (by rfl) ⟨1594172, by rfl⟩ : syracuseStep 2125563 = 3188345) B3188345
theorem B2588401 : Blo 2125435 2588401 := bbase (se 2 (by rfl) ⟨970650, by rfl⟩ : syracuseStep 2588401 = 1941301) (by norm_num)
theorem B13804805 : Blo 2125435 13804805 := bstep (se 4 (by rfl) ⟨1294200, by rfl⟩ : syracuseStep 13804805 = 2588401) B2588401
theorem B9203203 : Blo 2125435 9203203 := bstep (se 1 (by rfl) ⟨6902402, by rfl⟩ : syracuseStep 9203203 = 13804805) B13804805
theorem B12270937 : Blo 2125435 12270937 := bstep (se 2 (by rfl) ⟨4601601, by rfl⟩ : syracuseStep 12270937 = 9203203) B9203203
theorem B16361249 : Blo 2125435 16361249 := bstep (se 2 (by rfl) ⟨6135468, by rfl⟩ : syracuseStep 16361249 = 12270937) B12270937
theorem B43629997 : Blo 2125435 43629997 := bstep (se 3 (by rfl) ⟨8180624, by rfl⟩ : syracuseStep 43629997 = 16361249) B16361249
theorem B58173329 : Blo 2125435 58173329 := bstep (se 2 (by rfl) ⟨21814998, by rfl⟩ : syracuseStep 58173329 = 43629997) B43629997
theorem B155128877 : Blo 2125435 155128877 := bstep (se 3 (by rfl) ⟨29086664, by rfl⟩ : syracuseStep 155128877 = 58173329) B58173329
theorem B103419251 : Blo 2125435 103419251 := bstep (se 1 (by rfl) ⟨77564438, by rfl⟩ : syracuseStep 103419251 = 155128877) B155128877
theorem B68946167 : Blo 2125435 68946167 := bstep (se 1 (by rfl) ⟨51709625, by rfl⟩ : syracuseStep 68946167 = 103419251) B103419251
theorem B45964111 : Blo 2125435 45964111 := bstep (se 1 (by rfl) ⟨34473083, by rfl⟩ : syracuseStep 45964111 = 68946167) B68946167
theorem B61285481 : Blo 2125435 61285481 := bstep (se 2 (by rfl) ⟨22982055, by rfl⟩ : syracuseStep 61285481 = 45964111) B45964111
theorem B40856987 : Blo 2125435 40856987 := bstep (se 1 (by rfl) ⟨30642740, by rfl⟩ : syracuseStep 40856987 = 61285481) B61285481
theorem B27237991 : Blo 2125435 27237991 := bstep (se 1 (by rfl) ⟨20428493, by rfl⟩ : syracuseStep 27237991 = 40856987) B40856987
theorem B36317321 : Blo 2125435 36317321 := bstep (se 2 (by rfl) ⟨13618995, by rfl⟩ : syracuseStep 36317321 = 27237991) B27237991
theorem B24211547 : Blo 2125435 24211547 := bstep (se 1 (by rfl) ⟨18158660, by rfl⟩ : syracuseStep 24211547 = 36317321) B36317321
theorem B16141031 : Blo 2125435 16141031 := bstep (se 1 (by rfl) ⟨12105773, by rfl⟩ : syracuseStep 16141031 = 24211547) B24211547
theorem B10760687 : Blo 2125435 10760687 := bstep (se 1 (by rfl) ⟨8070515, by rfl⟩ : syracuseStep 10760687 = 16141031) B16141031
theorem B7173791 : Blo 2125435 7173791 := bstep (se 1 (by rfl) ⟨5380343, by rfl⟩ : syracuseStep 7173791 = 10760687) B10760687
theorem B4782527 : Blo 2125435 4782527 := bstep (se 1 (by rfl) ⟨3586895, by rfl⟩ : syracuseStep 4782527 = 7173791) B7173791
theorem B3188351 : Blo 2125435 3188351 := bstep (se 1 (by rfl) ⟨2391263, by rfl⟩ : syracuseStep 3188351 = 4782527) B4782527
theorem B2125567 : Blo 2125435 2125567 := bstep (se 1 (by rfl) ⟨1594175, by rfl⟩ : syracuseStep 2125567 = 3188351) B3188351
theorem B3188357 : Blo 2125435 3188357 := bbase (se 4 (by rfl) ⟨298908, by rfl⟩ : syracuseStep 3188357 = 597817) (by norm_num)
theorem B2125571 : Blo 2125435 2125571 := bstep (se 1 (by rfl) ⟨1594178, by rfl⟩ : syracuseStep 2125571 = 3188357) B3188357
theorem B3586909 : Blo 2125435 3586909 := bbase (se 3 (by rfl) ⟨672545, by rfl⟩ : syracuseStep 3586909 = 1345091) (by norm_num)
theorem B4782545 : Blo 2125435 4782545 := bstep (se 2 (by rfl) ⟨1793454, by rfl⟩ : syracuseStep 4782545 = 3586909) B3586909
theorem B3188363 : Blo 2125435 3188363 := bstep (se 1 (by rfl) ⟨2391272, by rfl⟩ : syracuseStep 3188363 = 4782545) B4782545
theorem B2125575 : Blo 2125435 2125575 := bstep (se 1 (by rfl) ⟨1594181, by rfl⟩ : syracuseStep 2125575 = 3188363) B3188363
theorem B2391277 : Blo 2125435 2391277 := bbase (se 3 (by rfl) ⟨448364, by rfl⟩ : syracuseStep 2391277 = 896729) (by norm_num)
theorem B3188369 : Blo 2125435 3188369 := bstep (se 2 (by rfl) ⟨1195638, by rfl⟩ : syracuseStep 3188369 = 2391277) B2391277
theorem B2125579 : Blo 2125435 2125579 := bstep (se 1 (by rfl) ⟨1594184, by rfl⟩ : syracuseStep 2125579 = 3188369) B3188369
theorem B7173845 : Blo 2125435 7173845 := bbase (se 7 (by rfl) ⟨84068, by rfl⟩ : syracuseStep 7173845 = 168137) (by norm_num)
theorem B4782563 : Blo 2125435 4782563 := bstep (se 1 (by rfl) ⟨3586922, by rfl⟩ : syracuseStep 4782563 = 7173845) B7173845
theorem B3188375 : Blo 2125435 3188375 := bstep (se 1 (by rfl) ⟨2391281, by rfl⟩ : syracuseStep 3188375 = 4782563) B4782563
theorem B2125583 : Blo 2125435 2125583 := bstep (se 1 (by rfl) ⟨1594187, by rfl⟩ : syracuseStep 2125583 = 3188375) B3188375
theorem B3188381 : Blo 2125435 3188381 := bbase (se 3 (by rfl) ⟨597821, by rfl⟩ : syracuseStep 3188381 = 1195643) (by norm_num)
theorem B2125587 : Blo 2125435 2125587 := bstep (se 1 (by rfl) ⟨1594190, by rfl⟩ : syracuseStep 2125587 = 3188381) B3188381
theorem B4782581 : Blo 2125435 4782581 := bbase (se 5 (by rfl) ⟨224183, by rfl⟩ : syracuseStep 4782581 = 448367) (by norm_num)
theorem B3188387 : Blo 2125435 3188387 := bstep (se 1 (by rfl) ⟨2391290, by rfl⟩ : syracuseStep 3188387 = 4782581) B4782581
theorem B2125591 : Blo 2125435 2125591 := bstep (se 1 (by rfl) ⟨1594193, by rfl⟩ : syracuseStep 2125591 = 3188387) B3188387
theorem B74631125 : Blo 2125435 74631125 := bbase (se 7 (by rfl) ⟨874583, by rfl⟩ : syracuseStep 74631125 = 1749167) (by norm_num)
theorem B49754083 : Blo 2125435 49754083 := bstep (se 1 (by rfl) ⟨37315562, by rfl⟩ : syracuseStep 49754083 = 74631125) B74631125
theorem B66338777 : Blo 2125435 66338777 := bstep (se 2 (by rfl) ⟨24877041, by rfl⟩ : syracuseStep 66338777 = 49754083) B49754083
theorem B44225851 : Blo 2125435 44225851 := bstep (se 1 (by rfl) ⟨33169388, by rfl⟩ : syracuseStep 44225851 = 66338777) B66338777
theorem B58967801 : Blo 2125435 58967801 := bstep (se 2 (by rfl) ⟨22112925, by rfl⟩ : syracuseStep 58967801 = 44225851) B44225851
theorem B39311867 : Blo 2125435 39311867 := bstep (se 1 (by rfl) ⟨29483900, by rfl⟩ : syracuseStep 39311867 = 58967801) B58967801
theorem B26207911 : Blo 2125435 26207911 := bstep (se 1 (by rfl) ⟨19655933, by rfl⟩ : syracuseStep 26207911 = 39311867) B39311867
theorem B34943881 : Blo 2125435 34943881 := bstep (se 2 (by rfl) ⟨13103955, by rfl⟩ : syracuseStep 34943881 = 26207911) B26207911
theorem B46591841 : Blo 2125435 46591841 := bstep (se 2 (by rfl) ⟨17471940, by rfl⟩ : syracuseStep 46591841 = 34943881) B34943881
theorem B31061227 : Blo 2125435 31061227 := bstep (se 1 (by rfl) ⟨23295920, by rfl⟩ : syracuseStep 31061227 = 46591841) B46591841
theorem B41414969 : Blo 2125435 41414969 := bstep (se 2 (by rfl) ⟨15530613, by rfl⟩ : syracuseStep 41414969 = 31061227) B31061227
theorem B27609979 : Blo 2125435 27609979 := bstep (se 1 (by rfl) ⟨20707484, by rfl⟩ : syracuseStep 27609979 = 41414969) B41414969
theorem B36813305 : Blo 2125435 36813305 := bstep (se 2 (by rfl) ⟨13804989, by rfl⟩ : syracuseStep 36813305 = 27609979) B27609979
theorem B24542203 : Blo 2125435 24542203 := bstep (se 1 (by rfl) ⟨18406652, by rfl⟩ : syracuseStep 24542203 = 36813305) B36813305
theorem B32722937 : Blo 2125435 32722937 := bstep (se 2 (by rfl) ⟨12271101, by rfl⟩ : syracuseStep 32722937 = 24542203) B24542203
theorem B21815291 : Blo 2125435 21815291 := bstep (se 1 (by rfl) ⟨16361468, by rfl⟩ : syracuseStep 21815291 = 32722937) B32722937
theorem B58174109 : Blo 2125435 58174109 := bstep (se 3 (by rfl) ⟨10907645, by rfl⟩ : syracuseStep 58174109 = 21815291) B21815291
theorem B38782739 : Blo 2125435 38782739 := bstep (se 1 (by rfl) ⟨29087054, by rfl⟩ : syracuseStep 38782739 = 58174109) B58174109
theorem B25855159 : Blo 2125435 25855159 := bstep (se 1 (by rfl) ⟨19391369, by rfl⟩ : syracuseStep 25855159 = 38782739) B38782739
theorem B34473545 : Blo 2125435 34473545 := bstep (se 2 (by rfl) ⟨12927579, by rfl⟩ : syracuseStep 34473545 = 25855159) B25855159
theorem B22982363 : Blo 2125435 22982363 := bstep (se 1 (by rfl) ⟨17236772, by rfl⟩ : syracuseStep 22982363 = 34473545) B34473545
theorem B15321575 : Blo 2125435 15321575 := bstep (se 1 (by rfl) ⟨11491181, by rfl⟩ : syracuseStep 15321575 = 22982363) B22982363
theorem B40857533 : Blo 2125435 40857533 := bstep (se 3 (by rfl) ⟨7660787, by rfl⟩ : syracuseStep 40857533 = 15321575) B15321575
theorem B27238355 : Blo 2125435 27238355 := bstep (se 1 (by rfl) ⟨20428766, by rfl⟩ : syracuseStep 27238355 = 40857533) B40857533
theorem B18158903 : Blo 2125435 18158903 := bstep (se 1 (by rfl) ⟨13619177, by rfl⟩ : syracuseStep 18158903 = 27238355) B27238355
theorem B12105935 : Blo 2125435 12105935 := bstep (se 1 (by rfl) ⟨9079451, by rfl⟩ : syracuseStep 12105935 = 18158903) B18158903
theorem B8070623 : Blo 2125435 8070623 := bstep (se 1 (by rfl) ⟨6052967, by rfl⟩ : syracuseStep 8070623 = 12105935) B12105935
theorem B5380415 : Blo 2125435 5380415 := bstep (se 1 (by rfl) ⟨4035311, by rfl⟩ : syracuseStep 5380415 = 8070623) B8070623
theorem B3586943 : Blo 2125435 3586943 := bstep (se 1 (by rfl) ⟨2690207, by rfl⟩ : syracuseStep 3586943 = 5380415) B5380415
theorem B2391295 : Blo 2125435 2391295 := bstep (se 1 (by rfl) ⟨1793471, by rfl⟩ : syracuseStep 2391295 = 3586943) B3586943
theorem B3188393 : Blo 2125435 3188393 := bstep (se 2 (by rfl) ⟨1195647, by rfl⟩ : syracuseStep 3188393 = 2391295) B2391295
theorem B2125595 : Blo 2125435 2125595 := bstep (se 1 (by rfl) ⟨1594196, by rfl⟩ : syracuseStep 2125595 = 3188393) B3188393
theorem B2553601 : Blo 2125435 2553601 := bbase (se 2 (by rfl) ⟨957600, by rfl⟩ : syracuseStep 2553601 = 1915201) (by norm_num)
theorem B3404801 : Blo 2125435 3404801 := bstep (se 2 (by rfl) ⟨1276800, by rfl⟩ : syracuseStep 3404801 = 2553601) B2553601
theorem B2269867 : Blo 2125435 2269867 := bstep (se 1 (by rfl) ⟨1702400, by rfl⟩ : syracuseStep 2269867 = 3404801) B3404801
theorem B3026489 : Blo 2125435 3026489 := bstep (se 2 (by rfl) ⟨1134933, by rfl⟩ : syracuseStep 3026489 = 2269867) B2269867
theorem B8070637 : Blo 2125435 8070637 := bstep (se 3 (by rfl) ⟨1513244, by rfl⟩ : syracuseStep 8070637 = 3026489) B3026489
theorem B10760849 : Blo 2125435 10760849 := bstep (se 2 (by rfl) ⟨4035318, by rfl⟩ : syracuseStep 10760849 = 8070637) B8070637
theorem B7173899 : Blo 2125435 7173899 := bstep (se 1 (by rfl) ⟨5380424, by rfl⟩ : syracuseStep 7173899 = 10760849) B10760849
theorem B4782599 : Blo 2125435 4782599 := bstep (se 1 (by rfl) ⟨3586949, by rfl⟩ : syracuseStep 4782599 = 7173899) B7173899
theorem B3188399 : Blo 2125435 3188399 := bstep (se 1 (by rfl) ⟨2391299, by rfl⟩ : syracuseStep 3188399 = 4782599) B4782599
theorem B2125599 : Blo 2125435 2125599 := bstep (se 1 (by rfl) ⟨1594199, by rfl⟩ : syracuseStep 2125599 = 3188399) B3188399
theorem B3188405 : Blo 2125435 3188405 := bbase (se 5 (by rfl) ⟨149456, by rfl⟩ : syracuseStep 3188405 = 298913) (by norm_num)
theorem B2125603 : Blo 2125435 2125603 := bstep (se 1 (by rfl) ⟨1594202, by rfl⟩ : syracuseStep 2125603 = 3188405) B3188405
theorem B5380445 : Blo 2125435 5380445 := bbase (se 3 (by rfl) ⟨1008833, by rfl⟩ : syracuseStep 5380445 = 2017667) (by norm_num)
theorem B3586963 : Blo 2125435 3586963 := bstep (se 1 (by rfl) ⟨2690222, by rfl⟩ : syracuseStep 3586963 = 5380445) B5380445
theorem B4782617 : Blo 2125435 4782617 := bstep (se 2 (by rfl) ⟨1793481, by rfl⟩ : syracuseStep 4782617 = 3586963) B3586963
theorem B3188411 : Blo 2125435 3188411 := bstep (se 1 (by rfl) ⟨2391308, by rfl⟩ : syracuseStep 3188411 = 4782617) B4782617
theorem B2125607 : Blo 2125435 2125607 := bstep (se 1 (by rfl) ⟨1594205, by rfl⟩ : syracuseStep 2125607 = 3188411) B3188411
theorem B2391313 : Blo 2125435 2391313 := bbase (se 2 (by rfl) ⟨896742, by rfl⟩ : syracuseStep 2391313 = 1793485) (by norm_num)
theorem B3188417 : Blo 2125435 3188417 := bstep (se 2 (by rfl) ⟨1195656, by rfl⟩ : syracuseStep 3188417 = 2391313) B2391313
theorem B2125611 : Blo 2125435 2125611 := bstep (se 1 (by rfl) ⟨1594208, by rfl⟩ : syracuseStep 2125611 = 3188417) B3188417
theorem B4035349 : Blo 2125435 4035349 := bbase (se 6 (by rfl) ⟨94578, by rfl⟩ : syracuseStep 4035349 = 189157) (by norm_num)
theorem B5380465 : Blo 2125435 5380465 := bstep (se 2 (by rfl) ⟨2017674, by rfl⟩ : syracuseStep 5380465 = 4035349) B4035349
theorem B7173953 : Blo 2125435 7173953 := bstep (se 2 (by rfl) ⟨2690232, by rfl⟩ : syracuseStep 7173953 = 5380465) B5380465
theorem B4782635 : Blo 2125435 4782635 := bstep (se 1 (by rfl) ⟨3586976, by rfl⟩ : syracuseStep 4782635 = 7173953) B7173953
theorem B3188423 : Blo 2125435 3188423 := bstep (se 1 (by rfl) ⟨2391317, by rfl⟩ : syracuseStep 3188423 = 4782635) B4782635
theorem B2125615 : Blo 2125435 2125615 := bstep (se 1 (by rfl) ⟨1594211, by rfl⟩ : syracuseStep 2125615 = 3188423) B3188423
theorem B3188429 : Blo 2125435 3188429 := bbase (se 3 (by rfl) ⟨597830, by rfl⟩ : syracuseStep 3188429 = 1195661) (by norm_num)
theorem B2125619 : Blo 2125435 2125619 := bstep (se 1 (by rfl) ⟨1594214, by rfl⟩ : syracuseStep 2125619 = 3188429) B3188429
theorem B4782653 : Blo 2125435 4782653 := bbase (se 3 (by rfl) ⟨896747, by rfl⟩ : syracuseStep 4782653 = 1793495) (by norm_num)
theorem B3188435 : Blo 2125435 3188435 := bstep (se 1 (by rfl) ⟨2391326, by rfl⟩ : syracuseStep 3188435 = 4782653) B4782653
theorem B2125623 : Blo 2125435 2125623 := bstep (se 1 (by rfl) ⟨1594217, by rfl⟩ : syracuseStep 2125623 = 3188435) B3188435
theorem B3586997 : Blo 2125435 3586997 := bbase (se 5 (by rfl) ⟨168140, by rfl⟩ : syracuseStep 3586997 = 336281) (by norm_num)
theorem B2391331 : Blo 2125435 2391331 := bstep (se 1 (by rfl) ⟨1793498, by rfl⟩ : syracuseStep 2391331 = 3586997) B3586997
theorem B3188441 : Blo 2125435 3188441 := bstep (se 2 (by rfl) ⟨1195665, by rfl⟩ : syracuseStep 3188441 = 2391331) B2391331
theorem B2125627 : Blo 2125435 2125627 := bstep (se 1 (by rfl) ⟨1594220, by rfl⟩ : syracuseStep 2125627 = 3188441) B3188441
theorem B2269901 : Blo 2125435 2269901 := bbase (se 3 (by rfl) ⟨425606, by rfl⟩ : syracuseStep 2269901 = 851213) (by norm_num)
theorem B6053069 : Blo 2125435 6053069 := bstep (se 3 (by rfl) ⟨1134950, by rfl⟩ : syracuseStep 6053069 = 2269901) B2269901
theorem B16141517 : Blo 2125435 16141517 := bstep (se 3 (by rfl) ⟨3026534, by rfl⟩ : syracuseStep 16141517 = 6053069) B6053069
theorem B10761011 : Blo 2125435 10761011 := bstep (se 1 (by rfl) ⟨8070758, by rfl⟩ : syracuseStep 10761011 = 16141517) B16141517
theorem B7174007 : Blo 2125435 7174007 := bstep (se 1 (by rfl) ⟨5380505, by rfl⟩ : syracuseStep 7174007 = 10761011) B10761011
theorem B4782671 : Blo 2125435 4782671 := bstep (se 1 (by rfl) ⟨3587003, by rfl⟩ : syracuseStep 4782671 = 7174007) B7174007
theorem B3188447 : Blo 2125435 3188447 := bstep (se 1 (by rfl) ⟨2391335, by rfl⟩ : syracuseStep 3188447 = 4782671) B4782671
theorem B2125631 : Blo 2125435 2125631 := bstep (se 1 (by rfl) ⟨1594223, by rfl⟩ : syracuseStep 2125631 = 3188447) B3188447
theorem B3188453 : Blo 2125435 3188453 := bbase (se 4 (by rfl) ⟨298917, by rfl⟩ : syracuseStep 3188453 = 597835) (by norm_num)
theorem B2125635 : Blo 2125435 2125635 := bstep (se 1 (by rfl) ⟨1594226, by rfl⟩ : syracuseStep 2125635 = 3188453) B3188453
theorem B6053093 : Blo 2125435 6053093 := bbase (se 4 (by rfl) ⟨567477, by rfl⟩ : syracuseStep 6053093 = 1134955) (by norm_num)
theorem B4035395 : Blo 2125435 4035395 := bstep (se 1 (by rfl) ⟨3026546, by rfl⟩ : syracuseStep 4035395 = 6053093) B6053093
theorem B2690263 : Blo 2125435 2690263 := bstep (se 1 (by rfl) ⟨2017697, by rfl⟩ : syracuseStep 2690263 = 4035395) B4035395
theorem B3587017 : Blo 2125435 3587017 := bstep (se 2 (by rfl) ⟨1345131, by rfl⟩ : syracuseStep 3587017 = 2690263) B2690263
theorem B4782689 : Blo 2125435 4782689 := bstep (se 2 (by rfl) ⟨1793508, by rfl⟩ : syracuseStep 4782689 = 3587017) B3587017
theorem B3188459 : Blo 2125435 3188459 := bstep (se 1 (by rfl) ⟨2391344, by rfl⟩ : syracuseStep 3188459 = 4782689) B4782689
theorem B2125639 : Blo 2125435 2125639 := bstep (se 1 (by rfl) ⟨1594229, by rfl⟩ : syracuseStep 2125639 = 3188459) B3188459
theorem B2391349 : Blo 2125435 2391349 := bbase (se 5 (by rfl) ⟨112094, by rfl⟩ : syracuseStep 2391349 = 224189) (by norm_num)
theorem B3188465 : Blo 2125435 3188465 := bstep (se 2 (by rfl) ⟨1195674, by rfl⟩ : syracuseStep 3188465 = 2391349) B2391349
theorem B2125643 : Blo 2125435 2125643 := bstep (se 1 (by rfl) ⟨1594232, by rfl⟩ : syracuseStep 2125643 = 3188465) B3188465
theorem B2690273 : Blo 2125435 2690273 := bbase (se 2 (by rfl) ⟨1008852, by rfl⟩ : syracuseStep 2690273 = 2017705) (by norm_num)
theorem B7174061 : Blo 2125435 7174061 := bstep (se 3 (by rfl) ⟨1345136, by rfl⟩ : syracuseStep 7174061 = 2690273) B2690273
theorem B4782707 : Blo 2125435 4782707 := bstep (se 1 (by rfl) ⟨3587030, by rfl⟩ : syracuseStep 4782707 = 7174061) B7174061
theorem B3188471 : Blo 2125435 3188471 := bstep (se 1 (by rfl) ⟨2391353, by rfl⟩ : syracuseStep 3188471 = 4782707) B4782707
theorem B2125647 : Blo 2125435 2125647 := bstep (se 1 (by rfl) ⟨1594235, by rfl⟩ : syracuseStep 2125647 = 3188471) B3188471
theorem B3188477 : Blo 2125435 3188477 := bbase (se 3 (by rfl) ⟨597839, by rfl⟩ : syracuseStep 3188477 = 1195679) (by norm_num)
theorem B2125651 : Blo 2125435 2125651 := bstep (se 1 (by rfl) ⟨1594238, by rfl⟩ : syracuseStep 2125651 = 3188477) B3188477
theorem B4782725 : Blo 2125435 4782725 := bbase (se 4 (by rfl) ⟨448380, by rfl⟩ : syracuseStep 4782725 = 896761) (by norm_num)
theorem B3188483 : Blo 2125435 3188483 := bstep (se 1 (by rfl) ⟨2391362, by rfl⟩ : syracuseStep 3188483 = 4782725) B4782725
theorem B2125655 : Blo 2125435 2125655 := bstep (se 1 (by rfl) ⟨1594241, by rfl⟩ : syracuseStep 2125655 = 3188483) B3188483
theorem B10214693 : Blo 2125435 10214693 := bbase (se 4 (by rfl) ⟨957627, by rfl⟩ : syracuseStep 10214693 = 1915255) (by norm_num)
theorem B6809795 : Blo 2125435 6809795 := bstep (se 1 (by rfl) ⟨5107346, by rfl⟩ : syracuseStep 6809795 = 10214693) B10214693
theorem B4539863 : Blo 2125435 4539863 := bstep (se 1 (by rfl) ⟨3404897, by rfl⟩ : syracuseStep 4539863 = 6809795) B6809795
theorem B3026575 : Blo 2125435 3026575 := bstep (se 1 (by rfl) ⟨2269931, by rfl⟩ : syracuseStep 3026575 = 4539863) B4539863
theorem B4035433 : Blo 2125435 4035433 := bstep (se 2 (by rfl) ⟨1513287, by rfl⟩ : syracuseStep 4035433 = 3026575) B3026575
theorem B5380577 : Blo 2125435 5380577 := bstep (se 2 (by rfl) ⟨2017716, by rfl⟩ : syracuseStep 5380577 = 4035433) B4035433
theorem B3587051 : Blo 2125435 3587051 := bstep (se 1 (by rfl) ⟨2690288, by rfl⟩ : syracuseStep 3587051 = 5380577) B5380577
theorem B2391367 : Blo 2125435 2391367 := bstep (se 1 (by rfl) ⟨1793525, by rfl⟩ : syracuseStep 2391367 = 3587051) B3587051
theorem B3188489 : Blo 2125435 3188489 := bstep (se 2 (by rfl) ⟨1195683, by rfl⟩ : syracuseStep 3188489 = 2391367) B2391367
theorem B2125659 : Blo 2125435 2125659 := bstep (se 1 (by rfl) ⟨1594244, by rfl⟩ : syracuseStep 2125659 = 3188489) B3188489
theorem B10761173 : Blo 2125435 10761173 := bbase (se 7 (by rfl) ⟨126107, by rfl⟩ : syracuseStep 10761173 = 252215) (by norm_num)
theorem B7174115 : Blo 2125435 7174115 := bstep (se 1 (by rfl) ⟨5380586, by rfl⟩ : syracuseStep 7174115 = 10761173) B10761173
theorem B4782743 : Blo 2125435 4782743 := bstep (se 1 (by rfl) ⟨3587057, by rfl⟩ : syracuseStep 4782743 = 7174115) B7174115
theorem B3188495 : Blo 2125435 3188495 := bstep (se 1 (by rfl) ⟨2391371, by rfl⟩ : syracuseStep 3188495 = 4782743) B4782743
theorem B2125663 : Blo 2125435 2125663 := bstep (se 1 (by rfl) ⟨1594247, by rfl⟩ : syracuseStep 2125663 = 3188495) B3188495
theorem B3188501 : Blo 2125435 3188501 := bbase (se 6 (by rfl) ⟨74730, by rfl⟩ : syracuseStep 3188501 = 149461) (by norm_num)
theorem B2125667 : Blo 2125435 2125667 := bstep (se 1 (by rfl) ⟨1594250, by rfl⟩ : syracuseStep 2125667 = 3188501) B3188501
theorem B111950677 : Blo 2125435 111950677 := bbase (se 9 (by rfl) ⟨327980, by rfl⟩ : syracuseStep 111950677 = 655961) (by norm_num)
theorem B149267569 : Blo 2125435 149267569 := bstep (se 2 (by rfl) ⟨55975338, by rfl⟩ : syracuseStep 149267569 = 111950677) B111950677
theorem B199023425 : Blo 2125435 199023425 := bstep (se 2 (by rfl) ⟨74633784, by rfl⟩ : syracuseStep 199023425 = 149267569) B149267569
theorem B132682283 : Blo 2125435 132682283 := bstep (se 1 (by rfl) ⟨99511712, by rfl⟩ : syracuseStep 132682283 = 199023425) B199023425
theorem B88454855 : Blo 2125435 88454855 := bstep (se 1 (by rfl) ⟨66341141, by rfl⟩ : syracuseStep 88454855 = 132682283) B132682283
theorem B58969903 : Blo 2125435 58969903 := bstep (se 1 (by rfl) ⟨44227427, by rfl⟩ : syracuseStep 58969903 = 88454855) B88454855
theorem B78626537 : Blo 2125435 78626537 := bstep (se 2 (by rfl) ⟨29484951, by rfl⟩ : syracuseStep 78626537 = 58969903) B58969903
theorem B52417691 : Blo 2125435 52417691 := bstep (se 1 (by rfl) ⟨39313268, by rfl⟩ : syracuseStep 52417691 = 78626537) B78626537
theorem B34945127 : Blo 2125435 34945127 := bstep (se 1 (by rfl) ⟨26208845, by rfl⟩ : syracuseStep 34945127 = 52417691) B52417691
theorem B23296751 : Blo 2125435 23296751 := bstep (se 1 (by rfl) ⟨17472563, by rfl⟩ : syracuseStep 23296751 = 34945127) B34945127
theorem B15531167 : Blo 2125435 15531167 := bstep (se 1 (by rfl) ⟨11648375, by rfl⟩ : syracuseStep 15531167 = 23296751) B23296751
theorem B10354111 : Blo 2125435 10354111 := bstep (se 1 (by rfl) ⟨7765583, by rfl⟩ : syracuseStep 10354111 = 15531167) B15531167
theorem B55221925 : Blo 2125435 55221925 := bstep (se 4 (by rfl) ⟨5177055, by rfl⟩ : syracuseStep 55221925 = 10354111) B10354111
theorem B73629233 : Blo 2125435 73629233 := bstep (se 2 (by rfl) ⟨27610962, by rfl⟩ : syracuseStep 73629233 = 55221925) B55221925
theorem B49086155 : Blo 2125435 49086155 := bstep (se 1 (by rfl) ⟨36814616, by rfl⟩ : syracuseStep 49086155 = 73629233) B73629233
theorem B32724103 : Blo 2125435 32724103 := bstep (se 1 (by rfl) ⟨24543077, by rfl⟩ : syracuseStep 32724103 = 49086155) B49086155
theorem B43632137 : Blo 2125435 43632137 := bstep (se 2 (by rfl) ⟨16362051, by rfl⟩ : syracuseStep 43632137 = 32724103) B32724103
theorem B29088091 : Blo 2125435 29088091 := bstep (se 1 (by rfl) ⟨21816068, by rfl⟩ : syracuseStep 29088091 = 43632137) B43632137
theorem B155136485 : Blo 2125435 155136485 := bstep (se 4 (by rfl) ⟨14544045, by rfl⟩ : syracuseStep 155136485 = 29088091) B29088091
theorem B103424323 : Blo 2125435 103424323 := bstep (se 1 (by rfl) ⟨77568242, by rfl⟩ : syracuseStep 103424323 = 155136485) B155136485
theorem B137899097 : Blo 2125435 137899097 := bstep (se 2 (by rfl) ⟨51712161, by rfl⟩ : syracuseStep 137899097 = 103424323) B103424323
theorem B91932731 : Blo 2125435 91932731 := bstep (se 1 (by rfl) ⟨68949548, by rfl⟩ : syracuseStep 91932731 = 137899097) B137899097
theorem B61288487 : Blo 2125435 61288487 := bstep (se 1 (by rfl) ⟨45966365, by rfl⟩ : syracuseStep 61288487 = 91932731) B91932731
theorem B40858991 : Blo 2125435 40858991 := bstep (se 1 (by rfl) ⟨30644243, by rfl⟩ : syracuseStep 40858991 = 61288487) B61288487
theorem B27239327 : Blo 2125435 27239327 := bstep (se 1 (by rfl) ⟨20429495, by rfl⟩ : syracuseStep 27239327 = 40858991) B40858991
theorem B18159551 : Blo 2125435 18159551 := bstep (se 1 (by rfl) ⟨13619663, by rfl⟩ : syracuseStep 18159551 = 27239327) B27239327
theorem B12106367 : Blo 2125435 12106367 := bstep (se 1 (by rfl) ⟨9079775, by rfl⟩ : syracuseStep 12106367 = 18159551) B18159551
theorem B8070911 : Blo 2125435 8070911 := bstep (se 1 (by rfl) ⟨6053183, by rfl⟩ : syracuseStep 8070911 = 12106367) B12106367
theorem B5380607 : Blo 2125435 5380607 := bstep (se 1 (by rfl) ⟨4035455, by rfl⟩ : syracuseStep 5380607 = 8070911) B8070911
theorem B3587071 : Blo 2125435 3587071 := bstep (se 1 (by rfl) ⟨2690303, by rfl⟩ : syracuseStep 3587071 = 5380607) B5380607
theorem B4782761 : Blo 2125435 4782761 := bstep (se 2 (by rfl) ⟨1793535, by rfl⟩ : syracuseStep 4782761 = 3587071) B3587071
theorem B3188507 : Blo 2125435 3188507 := bstep (se 1 (by rfl) ⟨2391380, by rfl⟩ : syracuseStep 3188507 = 4782761) B4782761
theorem B2125671 : Blo 2125435 2125671 := bstep (se 1 (by rfl) ⟨1594253, by rfl⟩ : syracuseStep 2125671 = 3188507) B3188507
theorem B2391385 : Blo 2125435 2391385 := bbase (se 2 (by rfl) ⟨896769, by rfl⟩ : syracuseStep 2391385 = 1793539) (by norm_num)
theorem B3188513 : Blo 2125435 3188513 := bstep (se 2 (by rfl) ⟨1195692, by rfl⟩ : syracuseStep 3188513 = 2391385) B2391385
theorem B2125675 : Blo 2125435 2125675 := bstep (se 1 (by rfl) ⟨1594256, by rfl⟩ : syracuseStep 2125675 = 3188513) B3188513
theorem B2553697 : Blo 2125435 2553697 := bbase (se 2 (by rfl) ⟨957636, by rfl⟩ : syracuseStep 2553697 = 1915273) (by norm_num)
theorem B3404929 : Blo 2125435 3404929 := bstep (se 2 (by rfl) ⟨1276848, by rfl⟩ : syracuseStep 3404929 = 2553697) B2553697
theorem B4539905 : Blo 2125435 4539905 := bstep (se 2 (by rfl) ⟨1702464, by rfl⟩ : syracuseStep 4539905 = 3404929) B3404929
theorem B3026603 : Blo 2125435 3026603 := bstep (se 1 (by rfl) ⟨2269952, by rfl⟩ : syracuseStep 3026603 = 4539905) B4539905
theorem B8070941 : Blo 2125435 8070941 := bstep (se 3 (by rfl) ⟨1513301, by rfl⟩ : syracuseStep 8070941 = 3026603) B3026603
theorem B5380627 : Blo 2125435 5380627 := bstep (se 1 (by rfl) ⟨4035470, by rfl⟩ : syracuseStep 5380627 = 8070941) B8070941
theorem B7174169 : Blo 2125435 7174169 := bstep (se 2 (by rfl) ⟨2690313, by rfl⟩ : syracuseStep 7174169 = 5380627) B5380627
theorem B4782779 : Blo 2125435 4782779 := bstep (se 1 (by rfl) ⟨3587084, by rfl⟩ : syracuseStep 4782779 = 7174169) B7174169
theorem B3188519 : Blo 2125435 3188519 := bstep (se 1 (by rfl) ⟨2391389, by rfl⟩ : syracuseStep 3188519 = 4782779) B4782779
theorem B2125679 : Blo 2125435 2125679 := bstep (se 1 (by rfl) ⟨1594259, by rfl⟩ : syracuseStep 2125679 = 3188519) B3188519
theorem B3188525 : Blo 2125435 3188525 := bbase (se 3 (by rfl) ⟨597848, by rfl⟩ : syracuseStep 3188525 = 1195697) (by norm_num)
theorem B2125683 : Blo 2125435 2125683 := bstep (se 1 (by rfl) ⟨1594262, by rfl⟩ : syracuseStep 2125683 = 3188525) B3188525
theorem B4782797 : Blo 2125435 4782797 := bbase (se 3 (by rfl) ⟨896774, by rfl⟩ : syracuseStep 4782797 = 1793549) (by norm_num)
theorem B3188531 : Blo 2125435 3188531 := bstep (se 1 (by rfl) ⟨2391398, by rfl⟩ : syracuseStep 3188531 = 4782797) B4782797
theorem B2125687 : Blo 2125435 2125687 := bstep (se 1 (by rfl) ⟨1594265, by rfl⟩ : syracuseStep 2125687 = 3188531) B3188531
theorem B2690329 : Blo 2125435 2690329 := bbase (se 2 (by rfl) ⟨1008873, by rfl⟩ : syracuseStep 2690329 = 2017747) (by norm_num)
theorem B3587105 : Blo 2125435 3587105 := bstep (se 2 (by rfl) ⟨1345164, by rfl⟩ : syracuseStep 3587105 = 2690329) B2690329
theorem B2391403 : Blo 2125435 2391403 := bstep (se 1 (by rfl) ⟨1793552, by rfl⟩ : syracuseStep 2391403 = 3587105) B3587105
theorem B3188537 : Blo 2125435 3188537 := bstep (se 2 (by rfl) ⟨1195701, by rfl⟩ : syracuseStep 3188537 = 2391403) B2391403
theorem B2125691 : Blo 2125435 2125691 := bstep (se 1 (by rfl) ⟨1594268, by rfl⟩ : syracuseStep 2125691 = 3188537) B3188537
theorem B9079877 : Blo 2125435 9079877 := bbase (se 4 (by rfl) ⟨851238, by rfl⟩ : syracuseStep 9079877 = 1702477) (by norm_num)
theorem B24213005 : Blo 2125435 24213005 := bstep (se 3 (by rfl) ⟨4539938, by rfl⟩ : syracuseStep 24213005 = 9079877) B9079877
theorem B16142003 : Blo 2125435 16142003 := bstep (se 1 (by rfl) ⟨12106502, by rfl⟩ : syracuseStep 16142003 = 24213005) B24213005
theorem B10761335 : Blo 2125435 10761335 := bstep (se 1 (by rfl) ⟨8071001, by rfl⟩ : syracuseStep 10761335 = 16142003) B16142003
theorem B7174223 : Blo 2125435 7174223 := bstep (se 1 (by rfl) ⟨5380667, by rfl⟩ : syracuseStep 7174223 = 10761335) B10761335
theorem B4782815 : Blo 2125435 4782815 := bstep (se 1 (by rfl) ⟨3587111, by rfl⟩ : syracuseStep 4782815 = 7174223) B7174223
theorem B3188543 : Blo 2125435 3188543 := bstep (se 1 (by rfl) ⟨2391407, by rfl⟩ : syracuseStep 3188543 = 4782815) B4782815
theorem B2125695 : Blo 2125435 2125695 := bstep (se 1 (by rfl) ⟨1594271, by rfl⟩ : syracuseStep 2125695 = 3188543) B3188543
theorem B3188549 : Blo 2125435 3188549 := bbase (se 4 (by rfl) ⟨298926, by rfl⟩ : syracuseStep 3188549 = 597853) (by norm_num)
theorem B2125699 : Blo 2125435 2125699 := bstep (se 1 (by rfl) ⟨1594274, by rfl⟩ : syracuseStep 2125699 = 3188549) B3188549
theorem B3587125 : Blo 2125435 3587125 := bbase (se 5 (by rfl) ⟨168146, by rfl⟩ : syracuseStep 3587125 = 336293) (by norm_num)
theorem B4782833 : Blo 2125435 4782833 := bstep (se 2 (by rfl) ⟨1793562, by rfl⟩ : syracuseStep 4782833 = 3587125) B3587125
theorem B3188555 : Blo 2125435 3188555 := bstep (se 1 (by rfl) ⟨2391416, by rfl⟩ : syracuseStep 3188555 = 4782833) B4782833
theorem B2125703 : Blo 2125435 2125703 := bstep (se 1 (by rfl) ⟨1594277, by rfl⟩ : syracuseStep 2125703 = 3188555) B3188555
theorem B2391421 : Blo 2125435 2391421 := bbase (se 3 (by rfl) ⟨448391, by rfl⟩ : syracuseStep 2391421 = 896783) (by norm_num)
theorem B3188561 : Blo 2125435 3188561 := bstep (se 2 (by rfl) ⟨1195710, by rfl⟩ : syracuseStep 3188561 = 2391421) B2391421
theorem B2125707 : Blo 2125435 2125707 := bstep (se 1 (by rfl) ⟨1594280, by rfl⟩ : syracuseStep 2125707 = 3188561) B3188561
theorem B7174277 : Blo 2125435 7174277 := bbase (se 4 (by rfl) ⟨672588, by rfl⟩ : syracuseStep 7174277 = 1345177) (by norm_num)
theorem B4782851 : Blo 2125435 4782851 := bstep (se 1 (by rfl) ⟨3587138, by rfl⟩ : syracuseStep 4782851 = 7174277) B7174277
theorem B3188567 : Blo 2125435 3188567 := bstep (se 1 (by rfl) ⟨2391425, by rfl⟩ : syracuseStep 3188567 = 4782851) B4782851
theorem B2125711 : Blo 2125435 2125711 := bstep (se 1 (by rfl) ⟨1594283, by rfl⟩ : syracuseStep 2125711 = 3188567) B3188567
theorem B3188573 : Blo 2125435 3188573 := bbase (se 3 (by rfl) ⟨597857, by rfl⟩ : syracuseStep 3188573 = 1195715) (by norm_num)
theorem B2125715 : Blo 2125435 2125715 := bstep (se 1 (by rfl) ⟨1594286, by rfl⟩ : syracuseStep 2125715 = 3188573) B3188573
theorem B4782869 : Blo 2125435 4782869 := bbase (se 6 (by rfl) ⟨112098, by rfl⟩ : syracuseStep 4782869 = 224197) (by norm_num)
theorem B3188579 : Blo 2125435 3188579 := bstep (se 1 (by rfl) ⟨2391434, by rfl⟩ : syracuseStep 3188579 = 4782869) B4782869
theorem B2125719 : Blo 2125435 2125719 := bstep (se 1 (by rfl) ⟨1594289, by rfl⟩ : syracuseStep 2125719 = 3188579) B3188579
theorem B8071109 : Blo 2125435 8071109 := bbase (se 4 (by rfl) ⟨756666, by rfl⟩ : syracuseStep 8071109 = 1513333) (by norm_num)
theorem B5380739 : Blo 2125435 5380739 := bstep (se 1 (by rfl) ⟨4035554, by rfl⟩ : syracuseStep 5380739 = 8071109) B8071109
theorem B3587159 : Blo 2125435 3587159 := bstep (se 1 (by rfl) ⟨2690369, by rfl⟩ : syracuseStep 3587159 = 5380739) B5380739
theorem B2391439 : Blo 2125435 2391439 := bstep (se 1 (by rfl) ⟨1793579, by rfl⟩ : syracuseStep 2391439 = 3587159) B3587159
theorem B3188585 : Blo 2125435 3188585 := bstep (se 2 (by rfl) ⟨1195719, by rfl⟩ : syracuseStep 3188585 = 2391439) B2391439
theorem B2125723 : Blo 2125435 2125723 := bstep (se 1 (by rfl) ⟨1594292, by rfl⟩ : syracuseStep 2125723 = 3188585) B3188585
theorem B8088005 : Blo 2125435 8088005 := bbase (se 4 (by rfl) ⟨758250, by rfl⟩ : syracuseStep 8088005 = 1516501) (by norm_num)
theorem B5392003 : Blo 2125435 5392003 := bstep (se 1 (by rfl) ⟨4044002, by rfl⟩ : syracuseStep 5392003 = 8088005) B8088005
theorem B7189337 : Blo 2125435 7189337 := bstep (se 2 (by rfl) ⟨2696001, by rfl⟩ : syracuseStep 7189337 = 5392003) B5392003
theorem B4792891 : Blo 2125435 4792891 := bstep (se 1 (by rfl) ⟨3594668, by rfl⟩ : syracuseStep 4792891 = 7189337) B7189337
theorem B6390521 : Blo 2125435 6390521 := bstep (se 2 (by rfl) ⟨2396445, by rfl⟩ : syracuseStep 6390521 = 4792891) B4792891
theorem B4260347 : Blo 2125435 4260347 := bstep (se 1 (by rfl) ⟨3195260, by rfl⟩ : syracuseStep 4260347 = 6390521) B6390521
theorem B2840231 : Blo 2125435 2840231 := bstep (se 1 (by rfl) ⟨2130173, by rfl⟩ : syracuseStep 2840231 = 4260347) B4260347
theorem B7573949 : Blo 2125435 7573949 := bstep (se 3 (by rfl) ⟨1420115, by rfl⟩ : syracuseStep 7573949 = 2840231) B2840231
theorem B5049299 : Blo 2125435 5049299 := bstep (se 1 (by rfl) ⟨3786974, by rfl⟩ : syracuseStep 5049299 = 7573949) B7573949
theorem B13464797 : Blo 2125435 13464797 := bstep (se 3 (by rfl) ⟨2524649, by rfl⟩ : syracuseStep 13464797 = 5049299) B5049299
theorem B35906125 : Blo 2125435 35906125 := bstep (se 3 (by rfl) ⟨6732398, by rfl⟩ : syracuseStep 35906125 = 13464797) B13464797
theorem B47874833 : Blo 2125435 47874833 := bstep (se 2 (by rfl) ⟨17953062, by rfl⟩ : syracuseStep 47874833 = 35906125) B35906125
theorem B31916555 : Blo 2125435 31916555 := bstep (se 1 (by rfl) ⟨23937416, by rfl⟩ : syracuseStep 31916555 = 47874833) B47874833
theorem B21277703 : Blo 2125435 21277703 := bstep (se 1 (by rfl) ⟨15958277, by rfl⟩ : syracuseStep 21277703 = 31916555) B31916555
theorem B14185135 : Blo 2125435 14185135 := bstep (se 1 (by rfl) ⟨10638851, by rfl⟩ : syracuseStep 14185135 = 21277703) B21277703
theorem B18913513 : Blo 2125435 18913513 := bstep (se 2 (by rfl) ⟨7092567, by rfl⟩ : syracuseStep 18913513 = 14185135) B14185135
theorem B25218017 : Blo 2125435 25218017 := bstep (se 2 (by rfl) ⟨9456756, by rfl⟩ : syracuseStep 25218017 = 18913513) B18913513
theorem B16812011 : Blo 2125435 16812011 := bstep (se 1 (by rfl) ⟨12609008, by rfl⟩ : syracuseStep 16812011 = 25218017) B25218017
theorem B11208007 : Blo 2125435 11208007 := bstep (se 1 (by rfl) ⟨8406005, by rfl⟩ : syracuseStep 11208007 = 16812011) B16812011
theorem B14944009 : Blo 2125435 14944009 := bstep (se 2 (by rfl) ⟨5604003, by rfl⟩ : syracuseStep 14944009 = 11208007) B11208007
theorem B19925345 : Blo 2125435 19925345 := bstep (se 2 (by rfl) ⟨7472004, by rfl⟩ : syracuseStep 19925345 = 14944009) B14944009
theorem B13283563 : Blo 2125435 13283563 := bstep (se 1 (by rfl) ⟨9962672, by rfl⟩ : syracuseStep 13283563 = 19925345) B19925345
theorem B17711417 : Blo 2125435 17711417 := bstep (se 2 (by rfl) ⟨6641781, by rfl⟩ : syracuseStep 17711417 = 13283563) B13283563
theorem B47230445 : Blo 2125435 47230445 := bstep (se 3 (by rfl) ⟨8855708, by rfl⟩ : syracuseStep 47230445 = 17711417) B17711417
theorem B31486963 : Blo 2125435 31486963 := bstep (se 1 (by rfl) ⟨23615222, by rfl⟩ : syracuseStep 31486963 = 47230445) B47230445
theorem B41982617 : Blo 2125435 41982617 := bstep (se 2 (by rfl) ⟨15743481, by rfl⟩ : syracuseStep 41982617 = 31486963) B31486963
theorem B27988411 : Blo 2125435 27988411 := bstep (se 1 (by rfl) ⟨20991308, by rfl⟩ : syracuseStep 27988411 = 41982617) B41982617
theorem B37317881 : Blo 2125435 37317881 := bstep (se 2 (by rfl) ⟨13994205, by rfl⟩ : syracuseStep 37317881 = 27988411) B27988411
theorem B24878587 : Blo 2125435 24878587 := bstep (se 1 (by rfl) ⟨18658940, by rfl⟩ : syracuseStep 24878587 = 37317881) B37317881
theorem B33171449 : Blo 2125435 33171449 := bstep (se 2 (by rfl) ⟨12439293, by rfl⟩ : syracuseStep 33171449 = 24878587) B24878587
theorem B88457197 : Blo 2125435 88457197 := bstep (se 3 (by rfl) ⟨16585724, by rfl⟩ : syracuseStep 88457197 = 33171449) B33171449
theorem B117942929 : Blo 2125435 117942929 := bstep (se 2 (by rfl) ⟨44228598, by rfl⟩ : syracuseStep 117942929 = 88457197) B88457197
theorem B78628619 : Blo 2125435 78628619 := bstep (se 1 (by rfl) ⟨58971464, by rfl⟩ : syracuseStep 78628619 = 117942929) B117942929
theorem B52419079 : Blo 2125435 52419079 := bstep (se 1 (by rfl) ⟨39314309, by rfl⟩ : syracuseStep 52419079 = 78628619) B78628619
theorem B69892105 : Blo 2125435 69892105 := bstep (se 2 (by rfl) ⟨26209539, by rfl⟩ : syracuseStep 69892105 = 52419079) B52419079
theorem B93189473 : Blo 2125435 93189473 := bstep (se 2 (by rfl) ⟨34946052, by rfl⟩ : syracuseStep 93189473 = 69892105) B69892105
theorem B62126315 : Blo 2125435 62126315 := bstep (se 1 (by rfl) ⟨46594736, by rfl⟩ : syracuseStep 62126315 = 93189473) B93189473
theorem B41417543 : Blo 2125435 41417543 := bstep (se 1 (by rfl) ⟨31063157, by rfl⟩ : syracuseStep 41417543 = 62126315) B62126315
theorem B27611695 : Blo 2125435 27611695 := bstep (se 1 (by rfl) ⟨20708771, by rfl⟩ : syracuseStep 27611695 = 41417543) B41417543
theorem B36815593 : Blo 2125435 36815593 := bstep (se 2 (by rfl) ⟨13805847, by rfl⟩ : syracuseStep 36815593 = 27611695) B27611695
theorem B49087457 : Blo 2125435 49087457 := bstep (se 2 (by rfl) ⟨18407796, by rfl⟩ : syracuseStep 49087457 = 36815593) B36815593
theorem B32724971 : Blo 2125435 32724971 := bstep (se 1 (by rfl) ⟨24543728, by rfl⟩ : syracuseStep 32724971 = 49087457) B49087457
theorem B21816647 : Blo 2125435 21816647 := bstep (se 1 (by rfl) ⟨16362485, by rfl⟩ : syracuseStep 21816647 = 32724971) B32724971
theorem B14544431 : Blo 2125435 14544431 := bstep (se 1 (by rfl) ⟨10908323, by rfl⟩ : syracuseStep 14544431 = 21816647) B21816647
theorem B9696287 : Blo 2125435 9696287 := bstep (se 1 (by rfl) ⟨7272215, by rfl⟩ : syracuseStep 9696287 = 14544431) B14544431
theorem B25856765 : Blo 2125435 25856765 := bstep (se 3 (by rfl) ⟨4848143, by rfl⟩ : syracuseStep 25856765 = 9696287) B9696287
theorem B17237843 : Blo 2125435 17237843 := bstep (se 1 (by rfl) ⟨12928382, by rfl⟩ : syracuseStep 17237843 = 25856765) B25856765
theorem B11491895 : Blo 2125435 11491895 := bstep (se 1 (by rfl) ⟨8618921, by rfl⟩ : syracuseStep 11491895 = 17237843) B17237843
theorem B7661263 : Blo 2125435 7661263 := bstep (se 1 (by rfl) ⟨5745947, by rfl⟩ : syracuseStep 7661263 = 11491895) B11491895
theorem B10215017 : Blo 2125435 10215017 := bstep (se 2 (by rfl) ⟨3830631, by rfl⟩ : syracuseStep 10215017 = 7661263) B7661263
theorem B6810011 : Blo 2125435 6810011 := bstep (se 1 (by rfl) ⟨5107508, by rfl⟩ : syracuseStep 6810011 = 10215017) B10215017
theorem B4540007 : Blo 2125435 4540007 := bstep (se 1 (by rfl) ⟨3405005, by rfl⟩ : syracuseStep 4540007 = 6810011) B6810011
theorem B12106685 : Blo 2125435 12106685 := bstep (se 3 (by rfl) ⟨2270003, by rfl⟩ : syracuseStep 12106685 = 4540007) B4540007
theorem B8071123 : Blo 2125435 8071123 := bstep (se 1 (by rfl) ⟨6053342, by rfl⟩ : syracuseStep 8071123 = 12106685) B12106685
theorem B10761497 : Blo 2125435 10761497 := bstep (se 2 (by rfl) ⟨4035561, by rfl⟩ : syracuseStep 10761497 = 8071123) B8071123
theorem B7174331 : Blo 2125435 7174331 := bstep (se 1 (by rfl) ⟨5380748, by rfl⟩ : syracuseStep 7174331 = 10761497) B10761497
theorem B4782887 : Blo 2125435 4782887 := bstep (se 1 (by rfl) ⟨3587165, by rfl⟩ : syracuseStep 4782887 = 7174331) B7174331
theorem B3188591 : Blo 2125435 3188591 := bstep (se 1 (by rfl) ⟨2391443, by rfl⟩ : syracuseStep 3188591 = 4782887) B4782887
theorem B2125727 : Blo 2125435 2125727 := bstep (se 1 (by rfl) ⟨1594295, by rfl⟩ : syracuseStep 2125727 = 3188591) B3188591
theorem B3188597 : Blo 2125435 3188597 := bbase (se 5 (by rfl) ⟨149465, by rfl⟩ : syracuseStep 3188597 = 298931) (by norm_num)
theorem B2125731 : Blo 2125435 2125731 := bstep (se 1 (by rfl) ⟨1594298, by rfl⟩ : syracuseStep 2125731 = 3188597) B3188597
theorem B3232109 : Blo 2125435 3232109 := bbase (se 3 (by rfl) ⟨606020, by rfl⟩ : syracuseStep 3232109 = 1212041) (by norm_num)
theorem B8618957 : Blo 2125435 8618957 := bstep (se 3 (by rfl) ⟨1616054, by rfl⟩ : syracuseStep 8618957 = 3232109) B3232109
theorem B5745971 : Blo 2125435 5745971 := bstep (se 1 (by rfl) ⟨4309478, by rfl⟩ : syracuseStep 5745971 = 8618957) B8618957
theorem B3830647 : Blo 2125435 3830647 := bstep (se 1 (by rfl) ⟨2872985, by rfl⟩ : syracuseStep 3830647 = 5745971) B5745971
theorem B5107529 : Blo 2125435 5107529 := bstep (se 2 (by rfl) ⟨1915323, by rfl⟩ : syracuseStep 5107529 = 3830647) B3830647
theorem B3405019 : Blo 2125435 3405019 := bstep (se 1 (by rfl) ⟨2553764, by rfl⟩ : syracuseStep 3405019 = 5107529) B5107529
theorem B4540025 : Blo 2125435 4540025 := bstep (se 2 (by rfl) ⟨1702509, by rfl⟩ : syracuseStep 4540025 = 3405019) B3405019
theorem B3026683 : Blo 2125435 3026683 := bstep (se 1 (by rfl) ⟨2270012, by rfl⟩ : syracuseStep 3026683 = 4540025) B4540025
theorem B4035577 : Blo 2125435 4035577 := bstep (se 2 (by rfl) ⟨1513341, by rfl⟩ : syracuseStep 4035577 = 3026683) B3026683
theorem B5380769 : Blo 2125435 5380769 := bstep (se 2 (by rfl) ⟨2017788, by rfl⟩ : syracuseStep 5380769 = 4035577) B4035577
theorem B3587179 : Blo 2125435 3587179 := bstep (se 1 (by rfl) ⟨2690384, by rfl⟩ : syracuseStep 3587179 = 5380769) B5380769
theorem B4782905 : Blo 2125435 4782905 := bstep (se 2 (by rfl) ⟨1793589, by rfl⟩ : syracuseStep 4782905 = 3587179) B3587179
theorem B3188603 : Blo 2125435 3188603 := bstep (se 1 (by rfl) ⟨2391452, by rfl⟩ : syracuseStep 3188603 = 4782905) B4782905
theorem B2125735 : Blo 2125435 2125735 := bstep (se 1 (by rfl) ⟨1594301, by rfl⟩ : syracuseStep 2125735 = 3188603) B3188603
theorem B2391457 : Blo 2125435 2391457 := bbase (se 2 (by rfl) ⟨896796, by rfl⟩ : syracuseStep 2391457 = 1793593) (by norm_num)
theorem B3188609 : Blo 2125435 3188609 := bstep (se 2 (by rfl) ⟨1195728, by rfl⟩ : syracuseStep 3188609 = 2391457) B2391457
theorem B2125739 : Blo 2125435 2125739 := bstep (se 1 (by rfl) ⟨1594304, by rfl⟩ : syracuseStep 2125739 = 3188609) B3188609
theorem B5380789 : Blo 2125435 5380789 := bbase (se 5 (by rfl) ⟨252224, by rfl⟩ : syracuseStep 5380789 = 504449) (by norm_num)
theorem B7174385 : Blo 2125435 7174385 := bstep (se 2 (by rfl) ⟨2690394, by rfl⟩ : syracuseStep 7174385 = 5380789) B5380789
theorem B4782923 : Blo 2125435 4782923 := bstep (se 1 (by rfl) ⟨3587192, by rfl⟩ : syracuseStep 4782923 = 7174385) B7174385
theorem B3188615 : Blo 2125435 3188615 := bstep (se 1 (by rfl) ⟨2391461, by rfl⟩ : syracuseStep 3188615 = 4782923) B4782923
theorem B2125743 : Blo 2125435 2125743 := bstep (se 1 (by rfl) ⟨1594307, by rfl⟩ : syracuseStep 2125743 = 3188615) B3188615
theorem B3188621 : Blo 2125435 3188621 := bbase (se 3 (by rfl) ⟨597866, by rfl⟩ : syracuseStep 3188621 = 1195733) (by norm_num)
theorem B2125747 : Blo 2125435 2125747 := bstep (se 1 (by rfl) ⟨1594310, by rfl⟩ : syracuseStep 2125747 = 3188621) B3188621
theorem B4782941 : Blo 2125435 4782941 := bbase (se 3 (by rfl) ⟨896801, by rfl⟩ : syracuseStep 4782941 = 1793603) (by norm_num)
theorem B3188627 : Blo 2125435 3188627 := bstep (se 1 (by rfl) ⟨2391470, by rfl⟩ : syracuseStep 3188627 = 4782941) B4782941
theorem B2125751 : Blo 2125435 2125751 := bstep (se 1 (by rfl) ⟨1594313, by rfl⟩ : syracuseStep 2125751 = 3188627) B3188627
theorem B3587213 : Blo 2125435 3587213 := bbase (se 3 (by rfl) ⟨672602, by rfl⟩ : syracuseStep 3587213 = 1345205) (by norm_num)
theorem B2391475 : Blo 2125435 2391475 := bstep (se 1 (by rfl) ⟨1793606, by rfl⟩ : syracuseStep 2391475 = 3587213) B3587213
theorem B3188633 : Blo 2125435 3188633 := bstep (se 2 (by rfl) ⟨1195737, by rfl⟩ : syracuseStep 3188633 = 2391475) B2391475
theorem B2125755 : Blo 2125435 2125755 := bstep (se 1 (by rfl) ⟨1594316, by rfl⟩ : syracuseStep 2125755 = 3188633) B3188633
theorem B2424109 : Blo 2125435 2424109 := bbase (se 3 (by rfl) ⟨454520, by rfl⟩ : syracuseStep 2424109 = 909041) (by norm_num)
theorem B3232145 : Blo 2125435 3232145 := bstep (se 2 (by rfl) ⟨1212054, by rfl⟩ : syracuseStep 3232145 = 2424109) B2424109
theorem B2154763 : Blo 2125435 2154763 := bstep (se 1 (by rfl) ⟨1616072, by rfl⟩ : syracuseStep 2154763 = 3232145) B3232145
theorem B2873017 : Blo 2125435 2873017 := bstep (se 2 (by rfl) ⟨1077381, by rfl⟩ : syracuseStep 2873017 = 2154763) B2154763
theorem B3830689 : Blo 2125435 3830689 := bstep (se 2 (by rfl) ⟨1436508, by rfl⟩ : syracuseStep 3830689 = 2873017) B2873017
theorem B5107585 : Blo 2125435 5107585 := bstep (se 2 (by rfl) ⟨1915344, by rfl⟩ : syracuseStep 5107585 = 3830689) B3830689
theorem B6810113 : Blo 2125435 6810113 := bstep (se 2 (by rfl) ⟨2553792, by rfl⟩ : syracuseStep 6810113 = 5107585) B5107585
theorem B18160301 : Blo 2125435 18160301 := bstep (se 3 (by rfl) ⟨3405056, by rfl⟩ : syracuseStep 18160301 = 6810113) B6810113
theorem B12106867 : Blo 2125435 12106867 := bstep (se 1 (by rfl) ⟨9080150, by rfl⟩ : syracuseStep 12106867 = 18160301) B18160301
theorem B16142489 : Blo 2125435 16142489 := bstep (se 2 (by rfl) ⟨6053433, by rfl⟩ : syracuseStep 16142489 = 12106867) B12106867
theorem B10761659 : Blo 2125435 10761659 := bstep (se 1 (by rfl) ⟨8071244, by rfl⟩ : syracuseStep 10761659 = 16142489) B16142489
theorem B7174439 : Blo 2125435 7174439 := bstep (se 1 (by rfl) ⟨5380829, by rfl⟩ : syracuseStep 7174439 = 10761659) B10761659
theorem B4782959 : Blo 2125435 4782959 := bstep (se 1 (by rfl) ⟨3587219, by rfl⟩ : syracuseStep 4782959 = 7174439) B7174439
theorem B3188639 : Blo 2125435 3188639 := bstep (se 1 (by rfl) ⟨2391479, by rfl⟩ : syracuseStep 3188639 = 4782959) B4782959
theorem B2125759 : Blo 2125435 2125759 := bstep (se 1 (by rfl) ⟨1594319, by rfl⟩ : syracuseStep 2125759 = 3188639) B3188639
theorem B3188645 : Blo 2125435 3188645 := bbase (se 4 (by rfl) ⟨298935, by rfl⟩ : syracuseStep 3188645 = 597871) (by norm_num)
theorem B2125763 : Blo 2125435 2125763 := bstep (se 1 (by rfl) ⟨1594322, by rfl⟩ : syracuseStep 2125763 = 3188645) B3188645
theorem B2690425 : Blo 2125435 2690425 := bbase (se 2 (by rfl) ⟨1008909, by rfl⟩ : syracuseStep 2690425 = 2017819) (by norm_num)
theorem B3587233 : Blo 2125435 3587233 := bstep (se 2 (by rfl) ⟨1345212, by rfl⟩ : syracuseStep 3587233 = 2690425) B2690425
theorem B4782977 : Blo 2125435 4782977 := bstep (se 2 (by rfl) ⟨1793616, by rfl⟩ : syracuseStep 4782977 = 3587233) B3587233
theorem B3188651 : Blo 2125435 3188651 := bstep (se 1 (by rfl) ⟨2391488, by rfl⟩ : syracuseStep 3188651 = 4782977) B4782977
theorem B2125767 : Blo 2125435 2125767 := bstep (se 1 (by rfl) ⟨1594325, by rfl⟩ : syracuseStep 2125767 = 3188651) B3188651
theorem B2391493 : Blo 2125435 2391493 := bbase (se 4 (by rfl) ⟨224202, by rfl⟩ : syracuseStep 2391493 = 448405) (by norm_num)
theorem B3188657 : Blo 2125435 3188657 := bstep (se 2 (by rfl) ⟨1195746, by rfl⟩ : syracuseStep 3188657 = 2391493) B2391493
theorem B2125771 : Blo 2125435 2125771 := bstep (se 1 (by rfl) ⟨1594328, by rfl⟩ : syracuseStep 2125771 = 3188657) B3188657
theorem B4035653 : Blo 2125435 4035653 := bbase (se 4 (by rfl) ⟨378342, by rfl⟩ : syracuseStep 4035653 = 756685) (by norm_num)
theorem B2690435 : Blo 2125435 2690435 := bstep (se 1 (by rfl) ⟨2017826, by rfl⟩ : syracuseStep 2690435 = 4035653) B4035653
theorem B7174493 : Blo 2125435 7174493 := bstep (se 3 (by rfl) ⟨1345217, by rfl⟩ : syracuseStep 7174493 = 2690435) B2690435
theorem B4782995 : Blo 2125435 4782995 := bstep (se 1 (by rfl) ⟨3587246, by rfl⟩ : syracuseStep 4782995 = 7174493) B7174493
theorem B3188663 : Blo 2125435 3188663 := bstep (se 1 (by rfl) ⟨2391497, by rfl⟩ : syracuseStep 3188663 = 4782995) B4782995
theorem B2125775 : Blo 2125435 2125775 := bstep (se 1 (by rfl) ⟨1594331, by rfl⟩ : syracuseStep 2125775 = 3188663) B3188663
theorem B3188669 : Blo 2125435 3188669 := bbase (se 3 (by rfl) ⟨597875, by rfl⟩ : syracuseStep 3188669 = 1195751) (by norm_num)
theorem B2125779 : Blo 2125435 2125779 := bstep (se 1 (by rfl) ⟨1594334, by rfl⟩ : syracuseStep 2125779 = 3188669) B3188669
theorem B4783013 : Blo 2125435 4783013 := bbase (se 4 (by rfl) ⟨448407, by rfl⟩ : syracuseStep 4783013 = 896815) (by norm_num)
theorem B3188675 : Blo 2125435 3188675 := bstep (se 1 (by rfl) ⟨2391506, by rfl⟩ : syracuseStep 3188675 = 4783013) B4783013
theorem B2125783 : Blo 2125435 2125783 := bstep (se 1 (by rfl) ⟨1594337, by rfl⟩ : syracuseStep 2125783 = 3188675) B3188675
theorem B5380901 : Blo 2125435 5380901 := bbase (se 4 (by rfl) ⟨504459, by rfl⟩ : syracuseStep 5380901 = 1008919) (by norm_num)
theorem B3587267 : Blo 2125435 3587267 := bstep (se 1 (by rfl) ⟨2690450, by rfl⟩ : syracuseStep 3587267 = 5380901) B5380901
theorem B2391511 : Blo 2125435 2391511 := bstep (se 1 (by rfl) ⟨1793633, by rfl⟩ : syracuseStep 2391511 = 3587267) B3587267
theorem B3188681 : Blo 2125435 3188681 := bstep (se 2 (by rfl) ⟨1195755, by rfl⟩ : syracuseStep 3188681 = 2391511) B2391511
theorem B2125787 : Blo 2125435 2125787 := bstep (se 1 (by rfl) ⟨1594340, by rfl⟩ : syracuseStep 2125787 = 3188681) B3188681
theorem B6053525 : Blo 2125435 6053525 := bbase (se 6 (by rfl) ⟨141879, by rfl⟩ : syracuseStep 6053525 = 283759) (by norm_num)
theorem B4035683 : Blo 2125435 4035683 := bstep (se 1 (by rfl) ⟨3026762, by rfl⟩ : syracuseStep 4035683 = 6053525) B6053525
theorem B10761821 : Blo 2125435 10761821 := bstep (se 3 (by rfl) ⟨2017841, by rfl⟩ : syracuseStep 10761821 = 4035683) B4035683
theorem B7174547 : Blo 2125435 7174547 := bstep (se 1 (by rfl) ⟨5380910, by rfl⟩ : syracuseStep 7174547 = 10761821) B10761821
theorem B4783031 : Blo 2125435 4783031 := bstep (se 1 (by rfl) ⟨3587273, by rfl⟩ : syracuseStep 4783031 = 7174547) B7174547
theorem B3188687 : Blo 2125435 3188687 := bstep (se 1 (by rfl) ⟨2391515, by rfl⟩ : syracuseStep 3188687 = 4783031) B4783031
theorem B2125791 : Blo 2125435 2125791 := bstep (se 1 (by rfl) ⟨1594343, by rfl⟩ : syracuseStep 2125791 = 3188687) B3188687
theorem B3188693 : Blo 2125435 3188693 := bbase (se 7 (by rfl) ⟨37367, by rfl⟩ : syracuseStep 3188693 = 74735) (by norm_num)
theorem B2125795 : Blo 2125435 2125795 := bstep (se 1 (by rfl) ⟨1594346, by rfl⟩ : syracuseStep 2125795 = 3188693) B3188693
theorem B8071397 : Blo 2125435 8071397 := bbase (se 4 (by rfl) ⟨756693, by rfl⟩ : syracuseStep 8071397 = 1513387) (by norm_num)
theorem B5380931 : Blo 2125435 5380931 := bstep (se 1 (by rfl) ⟨4035698, by rfl⟩ : syracuseStep 5380931 = 8071397) B8071397
theorem B3587287 : Blo 2125435 3587287 := bstep (se 1 (by rfl) ⟨2690465, by rfl⟩ : syracuseStep 3587287 = 5380931) B5380931
theorem B4783049 : Blo 2125435 4783049 := bstep (se 2 (by rfl) ⟨1793643, by rfl⟩ : syracuseStep 4783049 = 3587287) B3587287
theorem B3188699 : Blo 2125435 3188699 := bstep (se 1 (by rfl) ⟨2391524, by rfl⟩ : syracuseStep 3188699 = 4783049) B4783049
theorem B2125799 : Blo 2125435 2125799 := bstep (se 1 (by rfl) ⟨1594349, by rfl⟩ : syracuseStep 2125799 = 3188699) B3188699
theorem B2391529 : Blo 2125435 2391529 := bbase (se 2 (by rfl) ⟨896823, by rfl⟩ : syracuseStep 2391529 = 1793647) (by norm_num)
theorem B3188705 : Blo 2125435 3188705 := bstep (se 2 (by rfl) ⟨1195764, by rfl⟩ : syracuseStep 3188705 = 2391529) B2391529
theorem B2125803 : Blo 2125435 2125803 := bstep (se 1 (by rfl) ⟨1594352, by rfl⟩ : syracuseStep 2125803 = 3188705) B3188705
theorem B2270089 : Blo 2125435 2270089 := bbase (se 2 (by rfl) ⟨851283, by rfl⟩ : syracuseStep 2270089 = 1702567) (by norm_num)
theorem B12107141 : Blo 2125435 12107141 := bstep (se 4 (by rfl) ⟨1135044, by rfl⟩ : syracuseStep 12107141 = 2270089) B2270089
theorem B8071427 : Blo 2125435 8071427 := bstep (se 1 (by rfl) ⟨6053570, by rfl⟩ : syracuseStep 8071427 = 12107141) B12107141
theorem B5380951 : Blo 2125435 5380951 := bstep (se 1 (by rfl) ⟨4035713, by rfl⟩ : syracuseStep 5380951 = 8071427) B8071427
theorem B7174601 : Blo 2125435 7174601 := bstep (se 2 (by rfl) ⟨2690475, by rfl⟩ : syracuseStep 7174601 = 5380951) B5380951
theorem B4783067 : Blo 2125435 4783067 := bstep (se 1 (by rfl) ⟨3587300, by rfl⟩ : syracuseStep 4783067 = 7174601) B7174601
theorem B3188711 : Blo 2125435 3188711 := bstep (se 1 (by rfl) ⟨2391533, by rfl⟩ : syracuseStep 3188711 = 4783067) B4783067
theorem B2125807 : Blo 2125435 2125807 := bstep (se 1 (by rfl) ⟨1594355, by rfl⟩ : syracuseStep 2125807 = 3188711) B3188711
theorem B3188717 : Blo 2125435 3188717 := bbase (se 3 (by rfl) ⟨597884, by rfl⟩ : syracuseStep 3188717 = 1195769) (by norm_num)
theorem B2125811 : Blo 2125435 2125811 := bstep (se 1 (by rfl) ⟨1594358, by rfl⟩ : syracuseStep 2125811 = 3188717) B3188717
theorem B4783085 : Blo 2125435 4783085 := bbase (se 3 (by rfl) ⟨896828, by rfl⟩ : syracuseStep 4783085 = 1793657) (by norm_num)
theorem B3188723 : Blo 2125435 3188723 := bstep (se 1 (by rfl) ⟨2391542, by rfl⟩ : syracuseStep 3188723 = 4783085) B4783085
theorem B2125815 : Blo 2125435 2125815 := bstep (se 1 (by rfl) ⟨1594361, by rfl⟩ : syracuseStep 2125815 = 3188723) B3188723
theorem B4540205 : Blo 2125435 4540205 := bbase (se 3 (by rfl) ⟨851288, by rfl⟩ : syracuseStep 4540205 = 1702577) (by norm_num)
theorem B3026803 : Blo 2125435 3026803 := bstep (se 1 (by rfl) ⟨2270102, by rfl⟩ : syracuseStep 3026803 = 4540205) B4540205
theorem B4035737 : Blo 2125435 4035737 := bstep (se 2 (by rfl) ⟨1513401, by rfl⟩ : syracuseStep 4035737 = 3026803) B3026803
theorem B2690491 : Blo 2125435 2690491 := bstep (se 1 (by rfl) ⟨2017868, by rfl⟩ : syracuseStep 2690491 = 4035737) B4035737
theorem B3587321 : Blo 2125435 3587321 := bstep (se 2 (by rfl) ⟨1345245, by rfl⟩ : syracuseStep 3587321 = 2690491) B2690491
theorem B2391547 : Blo 2125435 2391547 := bstep (se 1 (by rfl) ⟨1793660, by rfl⟩ : syracuseStep 2391547 = 3587321) B3587321
theorem B3188729 : Blo 2125435 3188729 := bstep (se 2 (by rfl) ⟨1195773, by rfl⟩ : syracuseStep 3188729 = 2391547) B2391547
theorem B2125819 : Blo 2125435 2125819 := bstep (se 1 (by rfl) ⟨1594364, by rfl⟩ : syracuseStep 2125819 = 3188729) B3188729
theorem B3883069 : Blo 2125435 3883069 := bbase (se 3 (by rfl) ⟨728075, by rfl⟩ : syracuseStep 3883069 = 1456151) (by norm_num)
theorem B20709701 : Blo 2125435 20709701 := bstep (se 4 (by rfl) ⟨1941534, by rfl⟩ : syracuseStep 20709701 = 3883069) B3883069
theorem B13806467 : Blo 2125435 13806467 := bstep (se 1 (by rfl) ⟨10354850, by rfl⟩ : syracuseStep 13806467 = 20709701) B20709701
theorem B9204311 : Blo 2125435 9204311 := bstep (se 1 (by rfl) ⟨6903233, by rfl⟩ : syracuseStep 9204311 = 13806467) B13806467
theorem B24544829 : Blo 2125435 24544829 := bstep (se 3 (by rfl) ⟨4602155, by rfl⟩ : syracuseStep 24544829 = 9204311) B9204311
theorem B65452877 : Blo 2125435 65452877 := bstep (se 3 (by rfl) ⟨12272414, by rfl⟩ : syracuseStep 65452877 = 24544829) B24544829
theorem B43635251 : Blo 2125435 43635251 := bstep (se 1 (by rfl) ⟨32726438, by rfl⟩ : syracuseStep 43635251 = 65452877) B65452877
theorem B29090167 : Blo 2125435 29090167 := bstep (se 1 (by rfl) ⟨21817625, by rfl⟩ : syracuseStep 29090167 = 43635251) B43635251
theorem B155147557 : Blo 2125435 155147557 := bstep (se 4 (by rfl) ⟨14545083, by rfl⟩ : syracuseStep 155147557 = 29090167) B29090167
theorem B206863409 : Blo 2125435 206863409 := bstep (se 2 (by rfl) ⟨77573778, by rfl⟩ : syracuseStep 206863409 = 155147557) B155147557
theorem B137908939 : Blo 2125435 137908939 := bstep (se 1 (by rfl) ⟨103431704, by rfl⟩ : syracuseStep 137908939 = 206863409) B206863409
theorem B183878585 : Blo 2125435 183878585 := bstep (se 2 (by rfl) ⟨68954469, by rfl⟩ : syracuseStep 183878585 = 137908939) B137908939
theorem B122585723 : Blo 2125435 122585723 := bstep (se 1 (by rfl) ⟨91939292, by rfl⟩ : syracuseStep 122585723 = 183878585) B183878585
theorem B81723815 : Blo 2125435 81723815 := bstep (se 1 (by rfl) ⟨61292861, by rfl⟩ : syracuseStep 81723815 = 122585723) B122585723
theorem B54482543 : Blo 2125435 54482543 := bstep (se 1 (by rfl) ⟨40861907, by rfl⟩ : syracuseStep 54482543 = 81723815) B81723815
theorem B36321695 : Blo 2125435 36321695 := bstep (se 1 (by rfl) ⟨27241271, by rfl⟩ : syracuseStep 36321695 = 54482543) B54482543
theorem B24214463 : Blo 2125435 24214463 := bstep (se 1 (by rfl) ⟨18160847, by rfl⟩ : syracuseStep 24214463 = 36321695) B36321695
theorem B16142975 : Blo 2125435 16142975 := bstep (se 1 (by rfl) ⟨12107231, by rfl⟩ : syracuseStep 16142975 = 24214463) B24214463
theorem B10761983 : Blo 2125435 10761983 := bstep (se 1 (by rfl) ⟨8071487, by rfl⟩ : syracuseStep 10761983 = 16142975) B16142975
theorem B7174655 : Blo 2125435 7174655 := bstep (se 1 (by rfl) ⟨5380991, by rfl⟩ : syracuseStep 7174655 = 10761983) B10761983
theorem B4783103 : Blo 2125435 4783103 := bstep (se 1 (by rfl) ⟨3587327, by rfl⟩ : syracuseStep 4783103 = 7174655) B7174655
theorem B3188735 : Blo 2125435 3188735 := bstep (se 1 (by rfl) ⟨2391551, by rfl⟩ : syracuseStep 3188735 = 4783103) B4783103
theorem B2125823 : Blo 2125435 2125823 := bstep (se 1 (by rfl) ⟨1594367, by rfl⟩ : syracuseStep 2125823 = 3188735) B3188735
theorem B3188741 : Blo 2125435 3188741 := bbase (se 4 (by rfl) ⟨298944, by rfl⟩ : syracuseStep 3188741 = 597889) (by norm_num)
theorem B2125827 : Blo 2125435 2125827 := bstep (se 1 (by rfl) ⟨1594370, by rfl⟩ : syracuseStep 2125827 = 3188741) B3188741
theorem B3587341 : Blo 2125435 3587341 := bbase (se 3 (by rfl) ⟨672626, by rfl⟩ : syracuseStep 3587341 = 1345253) (by norm_num)
theorem B4783121 : Blo 2125435 4783121 := bstep (se 2 (by rfl) ⟨1793670, by rfl⟩ : syracuseStep 4783121 = 3587341) B3587341
theorem B3188747 : Blo 2125435 3188747 := bstep (se 1 (by rfl) ⟨2391560, by rfl⟩ : syracuseStep 3188747 = 4783121) B4783121
theorem B2125831 : Blo 2125435 2125831 := bstep (se 1 (by rfl) ⟨1594373, by rfl⟩ : syracuseStep 2125831 = 3188747) B3188747
theorem B2391565 : Blo 2125435 2391565 := bbase (se 3 (by rfl) ⟨448418, by rfl⟩ : syracuseStep 2391565 = 896837) (by norm_num)
theorem B3188753 : Blo 2125435 3188753 := bstep (se 2 (by rfl) ⟨1195782, by rfl⟩ : syracuseStep 3188753 = 2391565) B2391565
theorem B2125835 : Blo 2125435 2125835 := bstep (se 1 (by rfl) ⟨1594376, by rfl⟩ : syracuseStep 2125835 = 3188753) B3188753
theorem B7174709 : Blo 2125435 7174709 := bbase (se 5 (by rfl) ⟨336314, by rfl⟩ : syracuseStep 7174709 = 672629) (by norm_num)
theorem B4783139 : Blo 2125435 4783139 := bstep (se 1 (by rfl) ⟨3587354, by rfl⟩ : syracuseStep 4783139 = 7174709) B7174709
theorem B3188759 : Blo 2125435 3188759 := bstep (se 1 (by rfl) ⟨2391569, by rfl⟩ : syracuseStep 3188759 = 4783139) B4783139
theorem B2125839 : Blo 2125435 2125839 := bstep (se 1 (by rfl) ⟨1594379, by rfl⟩ : syracuseStep 2125839 = 3188759) B3188759
theorem B3188765 : Blo 2125435 3188765 := bbase (se 3 (by rfl) ⟨597893, by rfl⟩ : syracuseStep 3188765 = 1195787) (by norm_num)
theorem B2125843 : Blo 2125435 2125843 := bstep (se 1 (by rfl) ⟨1594382, by rfl⟩ : syracuseStep 2125843 = 3188765) B3188765
theorem B4783157 : Blo 2125435 4783157 := bbase (se 5 (by rfl) ⟨224210, by rfl⟩ : syracuseStep 4783157 = 448421) (by norm_num)
theorem B3188771 : Blo 2125435 3188771 := bstep (se 1 (by rfl) ⟨2391578, by rfl⟩ : syracuseStep 3188771 = 4783157) B4783157
theorem B2125847 : Blo 2125435 2125847 := bstep (se 1 (by rfl) ⟨1594385, by rfl⟩ : syracuseStep 2125847 = 3188771) B3188771
theorem B4090861 : Blo 2125435 4090861 := bbase (se 3 (by rfl) ⟨767036, by rfl⟩ : syracuseStep 4090861 = 1534073) (by norm_num)
theorem B5454481 : Blo 2125435 5454481 := bstep (se 2 (by rfl) ⟨2045430, by rfl⟩ : syracuseStep 5454481 = 4090861) B4090861
theorem B7272641 : Blo 2125435 7272641 := bstep (se 2 (by rfl) ⟨2727240, by rfl⟩ : syracuseStep 7272641 = 5454481) B5454481
theorem B4848427 : Blo 2125435 4848427 := bstep (se 1 (by rfl) ⟨3636320, by rfl⟩ : syracuseStep 4848427 = 7272641) B7272641
theorem B25858277 : Blo 2125435 25858277 := bstep (se 4 (by rfl) ⟨2424213, by rfl⟩ : syracuseStep 25858277 = 4848427) B4848427
theorem B17238851 : Blo 2125435 17238851 := bstep (se 1 (by rfl) ⟨12929138, by rfl⟩ : syracuseStep 17238851 = 25858277) B25858277
theorem B11492567 : Blo 2125435 11492567 := bstep (se 1 (by rfl) ⟨8619425, by rfl⟩ : syracuseStep 11492567 = 17238851) B17238851
theorem B7661711 : Blo 2125435 7661711 := bstep (se 1 (by rfl) ⟨5746283, by rfl⟩ : syracuseStep 7661711 = 11492567) B11492567
theorem B5107807 : Blo 2125435 5107807 := bstep (se 1 (by rfl) ⟨3830855, by rfl⟩ : syracuseStep 5107807 = 7661711) B7661711
theorem B6810409 : Blo 2125435 6810409 := bstep (se 2 (by rfl) ⟨2553903, by rfl⟩ : syracuseStep 6810409 = 5107807) B5107807
theorem B9080545 : Blo 2125435 9080545 := bstep (se 2 (by rfl) ⟨3405204, by rfl⟩ : syracuseStep 9080545 = 6810409) B6810409
theorem B12107393 : Blo 2125435 12107393 := bstep (se 2 (by rfl) ⟨4540272, by rfl⟩ : syracuseStep 12107393 = 9080545) B9080545
theorem B8071595 : Blo 2125435 8071595 := bstep (se 1 (by rfl) ⟨6053696, by rfl⟩ : syracuseStep 8071595 = 12107393) B12107393
theorem B5381063 : Blo 2125435 5381063 := bstep (se 1 (by rfl) ⟨4035797, by rfl⟩ : syracuseStep 5381063 = 8071595) B8071595
theorem B3587375 : Blo 2125435 3587375 := bstep (se 1 (by rfl) ⟨2690531, by rfl⟩ : syracuseStep 3587375 = 5381063) B5381063
theorem B2391583 : Blo 2125435 2391583 := bstep (se 1 (by rfl) ⟨1793687, by rfl⟩ : syracuseStep 2391583 = 3587375) B3587375
theorem B3188777 : Blo 2125435 3188777 := bstep (se 2 (by rfl) ⟨1195791, by rfl⟩ : syracuseStep 3188777 = 2391583) B2391583
theorem B2125851 : Blo 2125435 2125851 := bstep (se 1 (by rfl) ⟨1594388, by rfl⟩ : syracuseStep 2125851 = 3188777) B3188777
theorem B6810421 : Blo 2125435 6810421 := bbase (se 5 (by rfl) ⟨319238, by rfl⟩ : syracuseStep 6810421 = 638477) (by norm_num)
theorem B9080561 : Blo 2125435 9080561 := bstep (se 2 (by rfl) ⟨3405210, by rfl⟩ : syracuseStep 9080561 = 6810421) B6810421
theorem B6053707 : Blo 2125435 6053707 := bstep (se 1 (by rfl) ⟨4540280, by rfl⟩ : syracuseStep 6053707 = 9080561) B9080561
theorem B8071609 : Blo 2125435 8071609 := bstep (se 2 (by rfl) ⟨3026853, by rfl⟩ : syracuseStep 8071609 = 6053707) B6053707
theorem B10762145 : Blo 2125435 10762145 := bstep (se 2 (by rfl) ⟨4035804, by rfl⟩ : syracuseStep 10762145 = 8071609) B8071609
theorem B7174763 : Blo 2125435 7174763 := bstep (se 1 (by rfl) ⟨5381072, by rfl⟩ : syracuseStep 7174763 = 10762145) B10762145
theorem B4783175 : Blo 2125435 4783175 := bstep (se 1 (by rfl) ⟨3587381, by rfl⟩ : syracuseStep 4783175 = 7174763) B7174763
theorem B3188783 : Blo 2125435 3188783 := bstep (se 1 (by rfl) ⟨2391587, by rfl⟩ : syracuseStep 3188783 = 4783175) B4783175
theorem B2125855 : Blo 2125435 2125855 := bstep (se 1 (by rfl) ⟨1594391, by rfl⟩ : syracuseStep 2125855 = 3188783) B3188783
theorem B3188789 : Blo 2125435 3188789 := bbase (se 5 (by rfl) ⟨149474, by rfl⟩ : syracuseStep 3188789 = 298949) (by norm_num)
theorem B2125859 : Blo 2125435 2125859 := bstep (se 1 (by rfl) ⟨1594394, by rfl⟩ : syracuseStep 2125859 = 3188789) B3188789
theorem B5381093 : Blo 2125435 5381093 := bbase (se 4 (by rfl) ⟨504477, by rfl⟩ : syracuseStep 5381093 = 1008955) (by norm_num)
theorem B3587395 : Blo 2125435 3587395 := bstep (se 1 (by rfl) ⟨2690546, by rfl⟩ : syracuseStep 3587395 = 5381093) B5381093
theorem B4783193 : Blo 2125435 4783193 := bstep (se 2 (by rfl) ⟨1793697, by rfl⟩ : syracuseStep 4783193 = 3587395) B3587395
theorem B3188795 : Blo 2125435 3188795 := bstep (se 1 (by rfl) ⟨2391596, by rfl⟩ : syracuseStep 3188795 = 4783193) B4783193
theorem B2125863 : Blo 2125435 2125863 := bstep (se 1 (by rfl) ⟨1594397, by rfl⟩ : syracuseStep 2125863 = 3188795) B3188795
theorem B2391601 : Blo 2125435 2391601 := bbase (se 2 (by rfl) ⟨896850, by rfl⟩ : syracuseStep 2391601 = 1793701) (by norm_num)
theorem B3188801 : Blo 2125435 3188801 := bstep (se 2 (by rfl) ⟨1195800, by rfl⟩ : syracuseStep 3188801 = 2391601) B2391601
theorem B2125867 : Blo 2125435 2125867 := bstep (se 1 (by rfl) ⟨1594400, by rfl⟩ : syracuseStep 2125867 = 3188801) B3188801
theorem B5454533 : Blo 2125435 5454533 := bbase (se 4 (by rfl) ⟨511362, by rfl⟩ : syracuseStep 5454533 = 1022725) (by norm_num)
theorem B3636355 : Blo 2125435 3636355 := bstep (se 1 (by rfl) ⟨2727266, by rfl⟩ : syracuseStep 3636355 = 5454533) B5454533
theorem B4848473 : Blo 2125435 4848473 := bstep (se 2 (by rfl) ⟨1818177, by rfl⟩ : syracuseStep 4848473 = 3636355) B3636355
theorem B3232315 : Blo 2125435 3232315 := bstep (se 1 (by rfl) ⟨2424236, by rfl⟩ : syracuseStep 3232315 = 4848473) B4848473
theorem B17239013 : Blo 2125435 17239013 := bstep (se 4 (by rfl) ⟨1616157, by rfl⟩ : syracuseStep 17239013 = 3232315) B3232315
theorem B11492675 : Blo 2125435 11492675 := bstep (se 1 (by rfl) ⟨8619506, by rfl⟩ : syracuseStep 11492675 = 17239013) B17239013
theorem B7661783 : Blo 2125435 7661783 := bstep (se 1 (by rfl) ⟨5746337, by rfl⟩ : syracuseStep 7661783 = 11492675) B11492675
theorem B5107855 : Blo 2125435 5107855 := bstep (se 1 (by rfl) ⟨3830891, by rfl⟩ : syracuseStep 5107855 = 7661783) B7661783
theorem B6810473 : Blo 2125435 6810473 := bstep (se 2 (by rfl) ⟨2553927, by rfl⟩ : syracuseStep 6810473 = 5107855) B5107855
theorem B4540315 : Blo 2125435 4540315 := bstep (se 1 (by rfl) ⟨3405236, by rfl⟩ : syracuseStep 4540315 = 6810473) B6810473
theorem B6053753 : Blo 2125435 6053753 := bstep (se 2 (by rfl) ⟨2270157, by rfl⟩ : syracuseStep 6053753 = 4540315) B4540315
theorem B4035835 : Blo 2125435 4035835 := bstep (se 1 (by rfl) ⟨3026876, by rfl⟩ : syracuseStep 4035835 = 6053753) B6053753
theorem B5381113 : Blo 2125435 5381113 := bstep (se 2 (by rfl) ⟨2017917, by rfl⟩ : syracuseStep 5381113 = 4035835) B4035835
theorem B7174817 : Blo 2125435 7174817 := bstep (se 2 (by rfl) ⟨2690556, by rfl⟩ : syracuseStep 7174817 = 5381113) B5381113
theorem B4783211 : Blo 2125435 4783211 := bstep (se 1 (by rfl) ⟨3587408, by rfl⟩ : syracuseStep 4783211 = 7174817) B7174817
theorem B3188807 : Blo 2125435 3188807 := bstep (se 1 (by rfl) ⟨2391605, by rfl⟩ : syracuseStep 3188807 = 4783211) B4783211
theorem B2125871 : Blo 2125435 2125871 := bstep (se 1 (by rfl) ⟨1594403, by rfl⟩ : syracuseStep 2125871 = 3188807) B3188807
theorem B3188813 : Blo 2125435 3188813 := bbase (se 3 (by rfl) ⟨597902, by rfl⟩ : syracuseStep 3188813 = 1195805) (by norm_num)
theorem B2125875 : Blo 2125435 2125875 := bstep (se 1 (by rfl) ⟨1594406, by rfl⟩ : syracuseStep 2125875 = 3188813) B3188813
theorem B4783229 : Blo 2125435 4783229 := bbase (se 3 (by rfl) ⟨896855, by rfl⟩ : syracuseStep 4783229 = 1793711) (by norm_num)
theorem B3188819 : Blo 2125435 3188819 := bstep (se 1 (by rfl) ⟨2391614, by rfl⟩ : syracuseStep 3188819 = 4783229) B4783229
theorem B2125879 : Blo 2125435 2125879 := bstep (se 1 (by rfl) ⟨1594409, by rfl⟩ : syracuseStep 2125879 = 3188819) B3188819
theorem B3587429 : Blo 2125435 3587429 := bbase (se 4 (by rfl) ⟨336321, by rfl⟩ : syracuseStep 3587429 = 672643) (by norm_num)
theorem B2391619 : Blo 2125435 2391619 := bstep (se 1 (by rfl) ⟨1793714, by rfl⟩ : syracuseStep 2391619 = 3587429) B3587429
theorem B3188825 : Blo 2125435 3188825 := bstep (se 2 (by rfl) ⟨1195809, by rfl⟩ : syracuseStep 3188825 = 2391619) B2391619
theorem B2125883 : Blo 2125435 2125883 := bstep (se 1 (by rfl) ⟨1594412, by rfl⟩ : syracuseStep 2125883 = 3188825) B3188825
theorem B4540349 : Blo 2125435 4540349 := bbase (se 3 (by rfl) ⟨851315, by rfl⟩ : syracuseStep 4540349 = 1702631) (by norm_num)
theorem B3026899 : Blo 2125435 3026899 := bstep (se 1 (by rfl) ⟨2270174, by rfl⟩ : syracuseStep 3026899 = 4540349) B4540349
theorem B16143461 : Blo 2125435 16143461 := bstep (se 4 (by rfl) ⟨1513449, by rfl⟩ : syracuseStep 16143461 = 3026899) B3026899
theorem B10762307 : Blo 2125435 10762307 := bstep (se 1 (by rfl) ⟨8071730, by rfl⟩ : syracuseStep 10762307 = 16143461) B16143461
theorem B7174871 : Blo 2125435 7174871 := bstep (se 1 (by rfl) ⟨5381153, by rfl⟩ : syracuseStep 7174871 = 10762307) B10762307
theorem B4783247 : Blo 2125435 4783247 := bstep (se 1 (by rfl) ⟨3587435, by rfl⟩ : syracuseStep 4783247 = 7174871) B7174871
theorem B3188831 : Blo 2125435 3188831 := bstep (se 1 (by rfl) ⟨2391623, by rfl⟩ : syracuseStep 3188831 = 4783247) B4783247
theorem B2125887 : Blo 2125435 2125887 := bstep (se 1 (by rfl) ⟨1594415, by rfl⟩ : syracuseStep 2125887 = 3188831) B3188831
theorem B3188837 : Blo 2125435 3188837 := bbase (se 4 (by rfl) ⟨298953, by rfl⟩ : syracuseStep 3188837 = 597907) (by norm_num)
theorem B2125891 : Blo 2125435 2125891 := bstep (se 1 (by rfl) ⟨1594418, by rfl⟩ : syracuseStep 2125891 = 3188837) B3188837
theorem B8619605 : Blo 2125435 8619605 := bbase (se 8 (by rfl) ⟨50505, by rfl⟩ : syracuseStep 8619605 = 101011) (by norm_num)
theorem B5746403 : Blo 2125435 5746403 := bstep (se 1 (by rfl) ⟨4309802, by rfl⟩ : syracuseStep 5746403 = 8619605) B8619605
theorem B15323741 : Blo 2125435 15323741 := bstep (se 3 (by rfl) ⟨2873201, by rfl⟩ : syracuseStep 15323741 = 5746403) B5746403
theorem B10215827 : Blo 2125435 10215827 := bstep (se 1 (by rfl) ⟨7661870, by rfl⟩ : syracuseStep 10215827 = 15323741) B15323741
theorem B6810551 : Blo 2125435 6810551 := bstep (se 1 (by rfl) ⟨5107913, by rfl⟩ : syracuseStep 6810551 = 10215827) B10215827
theorem B4540367 : Blo 2125435 4540367 := bstep (se 1 (by rfl) ⟨3405275, by rfl⟩ : syracuseStep 4540367 = 6810551) B6810551
theorem B3026911 : Blo 2125435 3026911 := bstep (se 1 (by rfl) ⟨2270183, by rfl⟩ : syracuseStep 3026911 = 4540367) B4540367
theorem B4035881 : Blo 2125435 4035881 := bstep (se 2 (by rfl) ⟨1513455, by rfl⟩ : syracuseStep 4035881 = 3026911) B3026911
theorem B2690587 : Blo 2125435 2690587 := bstep (se 1 (by rfl) ⟨2017940, by rfl⟩ : syracuseStep 2690587 = 4035881) B4035881
theorem B3587449 : Blo 2125435 3587449 := bstep (se 2 (by rfl) ⟨1345293, by rfl⟩ : syracuseStep 3587449 = 2690587) B2690587
theorem B4783265 : Blo 2125435 4783265 := bstep (se 2 (by rfl) ⟨1793724, by rfl⟩ : syracuseStep 4783265 = 3587449) B3587449
theorem B3188843 : Blo 2125435 3188843 := bstep (se 1 (by rfl) ⟨2391632, by rfl⟩ : syracuseStep 3188843 = 4783265) B4783265
theorem B2125895 : Blo 2125435 2125895 := bstep (se 1 (by rfl) ⟨1594421, by rfl⟩ : syracuseStep 2125895 = 3188843) B3188843
theorem B2391637 : Blo 2125435 2391637 := bbase (se 8 (by rfl) ⟨14013, by rfl⟩ : syracuseStep 2391637 = 28027) (by norm_num)
theorem B3188849 : Blo 2125435 3188849 := bstep (se 2 (by rfl) ⟨1195818, by rfl⟩ : syracuseStep 3188849 = 2391637) B2391637
theorem B2125899 : Blo 2125435 2125899 := bstep (se 1 (by rfl) ⟨1594424, by rfl⟩ : syracuseStep 2125899 = 3188849) B3188849
theorem B2690597 : Blo 2125435 2690597 := bbase (se 4 (by rfl) ⟨252243, by rfl⟩ : syracuseStep 2690597 = 504487) (by norm_num)
theorem B7174925 : Blo 2125435 7174925 := bstep (se 3 (by rfl) ⟨1345298, by rfl⟩ : syracuseStep 7174925 = 2690597) B2690597
theorem B4783283 : Blo 2125435 4783283 := bstep (se 1 (by rfl) ⟨3587462, by rfl⟩ : syracuseStep 4783283 = 7174925) B7174925
theorem B3188855 : Blo 2125435 3188855 := bstep (se 1 (by rfl) ⟨2391641, by rfl⟩ : syracuseStep 3188855 = 4783283) B4783283
theorem B2125903 : Blo 2125435 2125903 := bstep (se 1 (by rfl) ⟨1594427, by rfl⟩ : syracuseStep 2125903 = 3188855) B3188855
theorem B3188861 : Blo 2125435 3188861 := bbase (se 3 (by rfl) ⟨597911, by rfl⟩ : syracuseStep 3188861 = 1195823) (by norm_num)
theorem B2125907 : Blo 2125435 2125907 := bstep (se 1 (by rfl) ⟨1594430, by rfl⟩ : syracuseStep 2125907 = 3188861) B3188861
theorem B4783301 : Blo 2125435 4783301 := bbase (se 4 (by rfl) ⟨448434, by rfl⟩ : syracuseStep 4783301 = 896869) (by norm_num)
theorem B3188867 : Blo 2125435 3188867 := bstep (se 1 (by rfl) ⟨2391650, by rfl⟩ : syracuseStep 3188867 = 4783301) B4783301
theorem B2125911 : Blo 2125435 2125911 := bstep (se 1 (by rfl) ⟨1594433, by rfl⟩ : syracuseStep 2125911 = 3188867) B3188867
theorem B2332577 : Blo 2125435 2332577 := bbase (se 2 (by rfl) ⟨874716, by rfl⟩ : syracuseStep 2332577 = 1749433) (by norm_num)
theorem B6220205 : Blo 2125435 6220205 := bstep (se 3 (by rfl) ⟨1166288, by rfl⟩ : syracuseStep 6220205 = 2332577) B2332577
theorem B4146803 : Blo 2125435 4146803 := bstep (se 1 (by rfl) ⟨3110102, by rfl⟩ : syracuseStep 4146803 = 6220205) B6220205
theorem B2764535 : Blo 2125435 2764535 := bstep (se 1 (by rfl) ⟨2073401, by rfl⟩ : syracuseStep 2764535 = 4146803) B4146803
theorem B7372093 : Blo 2125435 7372093 := bstep (se 3 (by rfl) ⟨1382267, by rfl⟩ : syracuseStep 7372093 = 2764535) B2764535
theorem B9829457 : Blo 2125435 9829457 := bstep (se 2 (by rfl) ⟨3686046, by rfl⟩ : syracuseStep 9829457 = 7372093) B7372093
theorem B6552971 : Blo 2125435 6552971 := bstep (se 1 (by rfl) ⟨4914728, by rfl⟩ : syracuseStep 6552971 = 9829457) B9829457
theorem B4368647 : Blo 2125435 4368647 := bstep (se 1 (by rfl) ⟨3276485, by rfl⟩ : syracuseStep 4368647 = 6552971) B6552971
theorem B2912431 : Blo 2125435 2912431 := bstep (se 1 (by rfl) ⟨2184323, by rfl⟩ : syracuseStep 2912431 = 4368647) B4368647
theorem B3883241 : Blo 2125435 3883241 := bstep (se 2 (by rfl) ⟨1456215, by rfl⟩ : syracuseStep 3883241 = 2912431) B2912431
theorem B10355309 : Blo 2125435 10355309 := bstep (se 3 (by rfl) ⟨1941620, by rfl⟩ : syracuseStep 10355309 = 3883241) B3883241
theorem B6903539 : Blo 2125435 6903539 := bstep (se 1 (by rfl) ⟨5177654, by rfl⟩ : syracuseStep 6903539 = 10355309) B10355309
theorem B4602359 : Blo 2125435 4602359 := bstep (se 1 (by rfl) ⟨3451769, by rfl⟩ : syracuseStep 4602359 = 6903539) B6903539
theorem B12272957 : Blo 2125435 12272957 := bstep (se 3 (by rfl) ⟨2301179, by rfl⟩ : syracuseStep 12272957 = 4602359) B4602359
theorem B8181971 : Blo 2125435 8181971 := bstep (se 1 (by rfl) ⟨6136478, by rfl⟩ : syracuseStep 8181971 = 12272957) B12272957
theorem B5454647 : Blo 2125435 5454647 := bstep (se 1 (by rfl) ⟨4090985, by rfl⟩ : syracuseStep 5454647 = 8181971) B8181971
theorem B3636431 : Blo 2125435 3636431 := bstep (se 1 (by rfl) ⟨2727323, by rfl⟩ : syracuseStep 3636431 = 5454647) B5454647
theorem B2424287 : Blo 2125435 2424287 := bstep (se 1 (by rfl) ⟨1818215, by rfl⟩ : syracuseStep 2424287 = 3636431) B3636431
theorem B6464765 : Blo 2125435 6464765 := bstep (se 3 (by rfl) ⟨1212143, by rfl⟩ : syracuseStep 6464765 = 2424287) B2424287
theorem B4309843 : Blo 2125435 4309843 := bstep (se 1 (by rfl) ⟨3232382, by rfl⟩ : syracuseStep 4309843 = 6464765) B6464765
theorem B5746457 : Blo 2125435 5746457 := bstep (se 2 (by rfl) ⟨2154921, by rfl⟩ : syracuseStep 5746457 = 4309843) B4309843
theorem B3830971 : Blo 2125435 3830971 := bstep (se 1 (by rfl) ⟨2873228, by rfl⟩ : syracuseStep 3830971 = 5746457) B5746457
theorem B5107961 : Blo 2125435 5107961 := bstep (se 2 (by rfl) ⟨1915485, by rfl⟩ : syracuseStep 5107961 = 3830971) B3830971
theorem B13621229 : Blo 2125435 13621229 := bstep (se 3 (by rfl) ⟨2553980, by rfl⟩ : syracuseStep 13621229 = 5107961) B5107961
theorem B9080819 : Blo 2125435 9080819 := bstep (se 1 (by rfl) ⟨6810614, by rfl⟩ : syracuseStep 9080819 = 13621229) B13621229
theorem B6053879 : Blo 2125435 6053879 := bstep (se 1 (by rfl) ⟨4540409, by rfl⟩ : syracuseStep 6053879 = 9080819) B9080819
theorem B4035919 : Blo 2125435 4035919 := bstep (se 1 (by rfl) ⟨3026939, by rfl⟩ : syracuseStep 4035919 = 6053879) B6053879
theorem B5381225 : Blo 2125435 5381225 := bstep (se 2 (by rfl) ⟨2017959, by rfl⟩ : syracuseStep 5381225 = 4035919) B4035919
theorem B3587483 : Blo 2125435 3587483 := bstep (se 1 (by rfl) ⟨2690612, by rfl⟩ : syracuseStep 3587483 = 5381225) B5381225
theorem B2391655 : Blo 2125435 2391655 := bstep (se 1 (by rfl) ⟨1793741, by rfl⟩ : syracuseStep 2391655 = 3587483) B3587483
theorem B3188873 : Blo 2125435 3188873 := bstep (se 2 (by rfl) ⟨1195827, by rfl⟩ : syracuseStep 3188873 = 2391655) B2391655
theorem B2125915 : Blo 2125435 2125915 := bstep (se 1 (by rfl) ⟨1594436, by rfl⟩ : syracuseStep 2125915 = 3188873) B3188873
theorem B10762469 : Blo 2125435 10762469 := bbase (se 4 (by rfl) ⟨1008981, by rfl⟩ : syracuseStep 10762469 = 2017963) (by norm_num)
theorem B7174979 : Blo 2125435 7174979 := bstep (se 1 (by rfl) ⟨5381234, by rfl⟩ : syracuseStep 7174979 = 10762469) B10762469
theorem B4783319 : Blo 2125435 4783319 := bstep (se 1 (by rfl) ⟨3587489, by rfl⟩ : syracuseStep 4783319 = 7174979) B7174979
theorem B3188879 : Blo 2125435 3188879 := bstep (se 1 (by rfl) ⟨2391659, by rfl⟩ : syracuseStep 3188879 = 4783319) B4783319
theorem B2125919 : Blo 2125435 2125919 := bstep (se 1 (by rfl) ⟨1594439, by rfl⟩ : syracuseStep 2125919 = 3188879) B3188879
theorem B3188885 : Blo 2125435 3188885 := bbase (se 6 (by rfl) ⟨74739, by rfl⟩ : syracuseStep 3188885 = 149479) (by norm_num)
theorem B2125923 : Blo 2125435 2125923 := bstep (se 1 (by rfl) ⟨1594442, by rfl⟩ : syracuseStep 2125923 = 3188885) B3188885
theorem B9080869 : Blo 2125435 9080869 := bbase (se 4 (by rfl) ⟨851331, by rfl⟩ : syracuseStep 9080869 = 1702663) (by norm_num)
theorem B12107825 : Blo 2125435 12107825 := bstep (se 2 (by rfl) ⟨4540434, by rfl⟩ : syracuseStep 12107825 = 9080869) B9080869
theorem B8071883 : Blo 2125435 8071883 := bstep (se 1 (by rfl) ⟨6053912, by rfl⟩ : syracuseStep 8071883 = 12107825) B12107825
theorem B5381255 : Blo 2125435 5381255 := bstep (se 1 (by rfl) ⟨4035941, by rfl⟩ : syracuseStep 5381255 = 8071883) B8071883
theorem B3587503 : Blo 2125435 3587503 := bstep (se 1 (by rfl) ⟨2690627, by rfl⟩ : syracuseStep 3587503 = 5381255) B5381255
theorem B4783337 : Blo 2125435 4783337 := bstep (se 2 (by rfl) ⟨1793751, by rfl⟩ : syracuseStep 4783337 = 3587503) B3587503
theorem B3188891 : Blo 2125435 3188891 := bstep (se 1 (by rfl) ⟨2391668, by rfl⟩ : syracuseStep 3188891 = 4783337) B4783337
theorem B2125927 : Blo 2125435 2125927 := bstep (se 1 (by rfl) ⟨1594445, by rfl⟩ : syracuseStep 2125927 = 3188891) B3188891
theorem B2391673 : Blo 2125435 2391673 := bbase (se 2 (by rfl) ⟨896877, by rfl⟩ : syracuseStep 2391673 = 1793755) (by norm_num)
theorem B3188897 : Blo 2125435 3188897 := bstep (se 2 (by rfl) ⟨1195836, by rfl⟩ : syracuseStep 3188897 = 2391673) B2391673
theorem B2125931 : Blo 2125435 2125931 := bstep (se 1 (by rfl) ⟨1594448, by rfl⟩ : syracuseStep 2125931 = 3188897) B3188897
theorem B3891397 : Blo 2125435 3891397 := bbase (se 4 (by rfl) ⟨364818, by rfl⟩ : syracuseStep 3891397 = 729637) (by norm_num)
theorem B5188529 : Blo 2125435 5188529 := bstep (se 2 (by rfl) ⟨1945698, by rfl⟩ : syracuseStep 5188529 = 3891397) B3891397
theorem B3459019 : Blo 2125435 3459019 := bstep (se 1 (by rfl) ⟨2594264, by rfl⟩ : syracuseStep 3459019 = 5188529) B5188529
theorem B4612025 : Blo 2125435 4612025 := bstep (se 2 (by rfl) ⟨1729509, by rfl⟩ : syracuseStep 4612025 = 3459019) B3459019
theorem B3074683 : Blo 2125435 3074683 := bstep (se 1 (by rfl) ⟨2306012, by rfl⟩ : syracuseStep 3074683 = 4612025) B4612025
theorem B4099577 : Blo 2125435 4099577 := bstep (se 2 (by rfl) ⟨1537341, by rfl⟩ : syracuseStep 4099577 = 3074683) B3074683
theorem B10932205 : Blo 2125435 10932205 := bstep (se 3 (by rfl) ⟨2049788, by rfl⟩ : syracuseStep 10932205 = 4099577) B4099577
theorem B14576273 : Blo 2125435 14576273 := bstep (se 2 (by rfl) ⟨5466102, by rfl⟩ : syracuseStep 14576273 = 10932205) B10932205
theorem B9717515 : Blo 2125435 9717515 := bstep (se 1 (by rfl) ⟨7288136, by rfl⟩ : syracuseStep 9717515 = 14576273) B14576273
theorem B6478343 : Blo 2125435 6478343 := bstep (se 1 (by rfl) ⟨4858757, by rfl⟩ : syracuseStep 6478343 = 9717515) B9717515
theorem B4318895 : Blo 2125435 4318895 := bstep (se 1 (by rfl) ⟨3239171, by rfl⟩ : syracuseStep 4318895 = 6478343) B6478343
theorem B2879263 : Blo 2125435 2879263 := bstep (se 1 (by rfl) ⟨2159447, by rfl⟩ : syracuseStep 2879263 = 4318895) B4318895
theorem B3839017 : Blo 2125435 3839017 := bstep (se 2 (by rfl) ⟨1439631, by rfl⟩ : syracuseStep 3839017 = 2879263) B2879263
theorem B5118689 : Blo 2125435 5118689 := bstep (se 2 (by rfl) ⟨1919508, by rfl⟩ : syracuseStep 5118689 = 3839017) B3839017
theorem B3412459 : Blo 2125435 3412459 := bstep (se 1 (by rfl) ⟨2559344, by rfl⟩ : syracuseStep 3412459 = 5118689) B5118689
theorem B18199781 : Blo 2125435 18199781 := bstep (se 4 (by rfl) ⟨1706229, by rfl⟩ : syracuseStep 18199781 = 3412459) B3412459
theorem B12133187 : Blo 2125435 12133187 := bstep (se 1 (by rfl) ⟨9099890, by rfl⟩ : syracuseStep 12133187 = 18199781) B18199781
theorem B8088791 : Blo 2125435 8088791 := bstep (se 1 (by rfl) ⟨6066593, by rfl⟩ : syracuseStep 8088791 = 12133187) B12133187
theorem B86280437 : Blo 2125435 86280437 := bstep (se 5 (by rfl) ⟨4044395, by rfl⟩ : syracuseStep 86280437 = 8088791) B8088791
theorem B230081165 : Blo 2125435 230081165 := bstep (se 3 (by rfl) ⟨43140218, by rfl⟩ : syracuseStep 230081165 = 86280437) B86280437
theorem B153387443 : Blo 2125435 153387443 := bstep (se 1 (by rfl) ⟨115040582, by rfl⟩ : syracuseStep 153387443 = 230081165) B230081165
theorem B409033181 : Blo 2125435 409033181 := bstep (se 3 (by rfl) ⟨76693721, by rfl⟩ : syracuseStep 409033181 = 153387443) B153387443
theorem B272688787 : Blo 2125435 272688787 := bstep (se 1 (by rfl) ⟨204516590, by rfl⟩ : syracuseStep 272688787 = 409033181) B409033181
theorem B1454340197 : Blo 2125435 1454340197 := bstep (se 4 (by rfl) ⟨136344393, by rfl⟩ : syracuseStep 1454340197 = 272688787) B272688787
theorem B969560131 : Blo 2125435 969560131 := bstep (se 1 (by rfl) ⟨727170098, by rfl⟩ : syracuseStep 969560131 = 1454340197) B1454340197
theorem B1292746841 : Blo 2125435 1292746841 := bstep (se 2 (by rfl) ⟨484780065, by rfl⟩ : syracuseStep 1292746841 = 969560131) B969560131
theorem B861831227 : Blo 2125435 861831227 := bstep (se 1 (by rfl) ⟨646373420, by rfl⟩ : syracuseStep 861831227 = 1292746841) B1292746841
theorem B574554151 : Blo 2125435 574554151 := bstep (se 1 (by rfl) ⟨430915613, by rfl⟩ : syracuseStep 574554151 = 861831227) B861831227
theorem B766072201 : Blo 2125435 766072201 := bstep (se 2 (by rfl) ⟨287277075, by rfl⟩ : syracuseStep 766072201 = 574554151) B574554151
theorem B1021429601 : Blo 2125435 1021429601 := bstep (se 2 (by rfl) ⟨383036100, by rfl⟩ : syracuseStep 1021429601 = 766072201) B766072201
theorem B680953067 : Blo 2125435 680953067 := bstep (se 1 (by rfl) ⟨510714800, by rfl⟩ : syracuseStep 680953067 = 1021429601) B1021429601
theorem B453968711 : Blo 2125435 453968711 := bstep (se 1 (by rfl) ⟨340476533, by rfl⟩ : syracuseStep 453968711 = 680953067) B680953067
theorem B302645807 : Blo 2125435 302645807 := bstep (se 1 (by rfl) ⟨226984355, by rfl⟩ : syracuseStep 302645807 = 453968711) B453968711
theorem B201763871 : Blo 2125435 201763871 := bstep (se 1 (by rfl) ⟨151322903, by rfl⟩ : syracuseStep 201763871 = 302645807) B302645807
theorem B134509247 : Blo 2125435 134509247 := bstep (se 1 (by rfl) ⟨100881935, by rfl⟩ : syracuseStep 134509247 = 201763871) B201763871
theorem B89672831 : Blo 2125435 89672831 := bstep (se 1 (by rfl) ⟨67254623, by rfl⟩ : syracuseStep 89672831 = 134509247) B134509247
theorem B59781887 : Blo 2125435 59781887 := bstep (se 1 (by rfl) ⟨44836415, by rfl⟩ : syracuseStep 59781887 = 89672831) B89672831
theorem B39854591 : Blo 2125435 39854591 := bstep (se 1 (by rfl) ⟨29890943, by rfl⟩ : syracuseStep 39854591 = 59781887) B59781887
theorem B26569727 : Blo 2125435 26569727 := bstep (se 1 (by rfl) ⟨19927295, by rfl⟩ : syracuseStep 26569727 = 39854591) B39854591
theorem B17713151 : Blo 2125435 17713151 := bstep (se 1 (by rfl) ⟨13284863, by rfl⟩ : syracuseStep 17713151 = 26569727) B26569727
theorem B11808767 : Blo 2125435 11808767 := bstep (se 1 (by rfl) ⟨8856575, by rfl⟩ : syracuseStep 11808767 = 17713151) B17713151
theorem B31490045 : Blo 2125435 31490045 := bstep (se 3 (by rfl) ⟨5904383, by rfl⟩ : syracuseStep 31490045 = 11808767) B11808767
theorem B20993363 : Blo 2125435 20993363 := bstep (se 1 (by rfl) ⟨15745022, by rfl⟩ : syracuseStep 20993363 = 31490045) B31490045
theorem B13995575 : Blo 2125435 13995575 := bstep (se 1 (by rfl) ⟨10496681, by rfl⟩ : syracuseStep 13995575 = 20993363) B20993363
theorem B9330383 : Blo 2125435 9330383 := bstep (se 1 (by rfl) ⟨6997787, by rfl⟩ : syracuseStep 9330383 = 13995575) B13995575
theorem B24881021 : Blo 2125435 24881021 := bstep (se 3 (by rfl) ⟨4665191, by rfl⟩ : syracuseStep 24881021 = 9330383) B9330383
theorem B16587347 : Blo 2125435 16587347 := bstep (se 1 (by rfl) ⟨12440510, by rfl⟩ : syracuseStep 16587347 = 24881021) B24881021
theorem B44232925 : Blo 2125435 44232925 := bstep (se 3 (by rfl) ⟨8293673, by rfl⟩ : syracuseStep 44232925 = 16587347) B16587347
theorem B58977233 : Blo 2125435 58977233 := bstep (se 2 (by rfl) ⟨22116462, by rfl⟩ : syracuseStep 58977233 = 44232925) B44232925
theorem B39318155 : Blo 2125435 39318155 := bstep (se 1 (by rfl) ⟨29488616, by rfl⟩ : syracuseStep 39318155 = 58977233) B58977233
theorem B26212103 : Blo 2125435 26212103 := bstep (se 1 (by rfl) ⟨19659077, by rfl⟩ : syracuseStep 26212103 = 39318155) B39318155
theorem B17474735 : Blo 2125435 17474735 := bstep (se 1 (by rfl) ⟨13106051, by rfl⟩ : syracuseStep 17474735 = 26212103) B26212103
theorem B46599293 : Blo 2125435 46599293 := bstep (se 3 (by rfl) ⟨8737367, by rfl⟩ : syracuseStep 46599293 = 17474735) B17474735
theorem B31066195 : Blo 2125435 31066195 := bstep (se 1 (by rfl) ⟨23299646, by rfl⟩ : syracuseStep 31066195 = 46599293) B46599293
theorem B41421593 : Blo 2125435 41421593 := bstep (se 2 (by rfl) ⟨15533097, by rfl⟩ : syracuseStep 41421593 = 31066195) B31066195
theorem B27614395 : Blo 2125435 27614395 := bstep (se 1 (by rfl) ⟨20710796, by rfl⟩ : syracuseStep 27614395 = 41421593) B41421593
theorem B36819193 : Blo 2125435 36819193 := bstep (se 2 (by rfl) ⟨13807197, by rfl⟩ : syracuseStep 36819193 = 27614395) B27614395
theorem B49092257 : Blo 2125435 49092257 := bstep (se 2 (by rfl) ⟨18409596, by rfl⟩ : syracuseStep 49092257 = 36819193) B36819193
theorem B32728171 : Blo 2125435 32728171 := bstep (se 1 (by rfl) ⟨24546128, by rfl⟩ : syracuseStep 32728171 = 49092257) B49092257
theorem B43637561 : Blo 2125435 43637561 := bstep (se 2 (by rfl) ⟨16364085, by rfl⟩ : syracuseStep 43637561 = 32728171) B32728171
theorem B29091707 : Blo 2125435 29091707 := bstep (se 1 (by rfl) ⟨21818780, by rfl⟩ : syracuseStep 29091707 = 43637561) B43637561
theorem B19394471 : Blo 2125435 19394471 := bstep (se 1 (by rfl) ⟨14545853, by rfl⟩ : syracuseStep 19394471 = 29091707) B29091707
theorem B12929647 : Blo 2125435 12929647 := bstep (se 1 (by rfl) ⟨9697235, by rfl⟩ : syracuseStep 12929647 = 19394471) B19394471
theorem B17239529 : Blo 2125435 17239529 := bstep (se 2 (by rfl) ⟨6464823, by rfl⟩ : syracuseStep 17239529 = 12929647) B12929647
theorem B11493019 : Blo 2125435 11493019 := bstep (se 1 (by rfl) ⟨8619764, by rfl⟩ : syracuseStep 11493019 = 17239529) B17239529
theorem B15324025 : Blo 2125435 15324025 := bstep (se 2 (by rfl) ⟨5746509, by rfl⟩ : syracuseStep 15324025 = 11493019) B11493019
theorem B20432033 : Blo 2125435 20432033 := bstep (se 2 (by rfl) ⟨7662012, by rfl⟩ : syracuseStep 20432033 = 15324025) B15324025
theorem B13621355 : Blo 2125435 13621355 := bstep (se 1 (by rfl) ⟨10216016, by rfl⟩ : syracuseStep 13621355 = 20432033) B20432033
theorem B9080903 : Blo 2125435 9080903 := bstep (se 1 (by rfl) ⟨6810677, by rfl⟩ : syracuseStep 9080903 = 13621355) B13621355
theorem B6053935 : Blo 2125435 6053935 := bstep (se 1 (by rfl) ⟨4540451, by rfl⟩ : syracuseStep 6053935 = 9080903) B9080903
theorem B8071913 : Blo 2125435 8071913 := bstep (se 2 (by rfl) ⟨3026967, by rfl⟩ : syracuseStep 8071913 = 6053935) B6053935
theorem B5381275 : Blo 2125435 5381275 := bstep (se 1 (by rfl) ⟨4035956, by rfl⟩ : syracuseStep 5381275 = 8071913) B8071913
theorem B7175033 : Blo 2125435 7175033 := bstep (se 2 (by rfl) ⟨2690637, by rfl⟩ : syracuseStep 7175033 = 5381275) B5381275
theorem B4783355 : Blo 2125435 4783355 := bstep (se 1 (by rfl) ⟨3587516, by rfl⟩ : syracuseStep 4783355 = 7175033) B7175033
theorem B3188903 : Blo 2125435 3188903 := bstep (se 1 (by rfl) ⟨2391677, by rfl⟩ : syracuseStep 3188903 = 4783355) B4783355
theorem B2125935 : Blo 2125435 2125935 := bstep (se 1 (by rfl) ⟨1594451, by rfl⟩ : syracuseStep 2125935 = 3188903) B3188903
theorem B3188909 : Blo 2125435 3188909 := bbase (se 3 (by rfl) ⟨597920, by rfl⟩ : syracuseStep 3188909 = 1195841) (by norm_num)
theorem B2125939 : Blo 2125435 2125939 := bstep (se 1 (by rfl) ⟨1594454, by rfl⟩ : syracuseStep 2125939 = 3188909) B3188909
theorem B4783373 : Blo 2125435 4783373 := bbase (se 3 (by rfl) ⟨896882, by rfl⟩ : syracuseStep 4783373 = 1793765) (by norm_num)
theorem B3188915 : Blo 2125435 3188915 := bstep (se 1 (by rfl) ⟨2391686, by rfl⟩ : syracuseStep 3188915 = 4783373) B4783373
theorem B2125943 : Blo 2125435 2125943 := bstep (se 1 (by rfl) ⟨1594457, by rfl⟩ : syracuseStep 2125943 = 3188915) B3188915
theorem B2690653 : Blo 2125435 2690653 := bbase (se 3 (by rfl) ⟨504497, by rfl⟩ : syracuseStep 2690653 = 1008995) (by norm_num)
theorem B3587537 : Blo 2125435 3587537 := bstep (se 2 (by rfl) ⟨1345326, by rfl⟩ : syracuseStep 3587537 = 2690653) B2690653
theorem B2391691 : Blo 2125435 2391691 := bstep (se 1 (by rfl) ⟨1793768, by rfl⟩ : syracuseStep 2391691 = 3587537) B3587537
theorem B3188921 : Blo 2125435 3188921 := bstep (se 2 (by rfl) ⟨1195845, by rfl⟩ : syracuseStep 3188921 = 2391691) B2391691
theorem B2125947 : Blo 2125435 2125947 := bstep (se 1 (by rfl) ⟨1594460, by rfl⟩ : syracuseStep 2125947 = 3188921) B3188921
theorem B18161941 : Blo 2125435 18161941 := bbase (se 6 (by rfl) ⟨425670, by rfl⟩ : syracuseStep 18161941 = 851341) (by norm_num)
theorem B24215921 : Blo 2125435 24215921 := bstep (se 2 (by rfl) ⟨9080970, by rfl⟩ : syracuseStep 24215921 = 18161941) B18161941
theorem B16143947 : Blo 2125435 16143947 := bstep (se 1 (by rfl) ⟨12107960, by rfl⟩ : syracuseStep 16143947 = 24215921) B24215921
theorem B10762631 : Blo 2125435 10762631 := bstep (se 1 (by rfl) ⟨8071973, by rfl⟩ : syracuseStep 10762631 = 16143947) B16143947
theorem B7175087 : Blo 2125435 7175087 := bstep (se 1 (by rfl) ⟨5381315, by rfl⟩ : syracuseStep 7175087 = 10762631) B10762631
theorem B4783391 : Blo 2125435 4783391 := bstep (se 1 (by rfl) ⟨3587543, by rfl⟩ : syracuseStep 4783391 = 7175087) B7175087
theorem B3188927 : Blo 2125435 3188927 := bstep (se 1 (by rfl) ⟨2391695, by rfl⟩ : syracuseStep 3188927 = 4783391) B4783391
theorem B2125951 : Blo 2125435 2125951 := bstep (se 1 (by rfl) ⟨1594463, by rfl⟩ : syracuseStep 2125951 = 3188927) B3188927
theorem B3188933 : Blo 2125435 3188933 := bbase (se 4 (by rfl) ⟨298962, by rfl⟩ : syracuseStep 3188933 = 597925) (by norm_num)
theorem B2125955 : Blo 2125435 2125955 := bstep (se 1 (by rfl) ⟨1594466, by rfl⟩ : syracuseStep 2125955 = 3188933) B3188933
theorem B3587557 : Blo 2125435 3587557 := bbase (se 4 (by rfl) ⟨336333, by rfl⟩ : syracuseStep 3587557 = 672667) (by norm_num)
theorem B4783409 : Blo 2125435 4783409 := bstep (se 2 (by rfl) ⟨1793778, by rfl⟩ : syracuseStep 4783409 = 3587557) B3587557
theorem B3188939 : Blo 2125435 3188939 := bstep (se 1 (by rfl) ⟨2391704, by rfl⟩ : syracuseStep 3188939 = 4783409) B4783409
theorem B2125959 : Blo 2125435 2125959 := bstep (se 1 (by rfl) ⟨1594469, by rfl⟩ : syracuseStep 2125959 = 3188939) B3188939
theorem B2391709 : Blo 2125435 2391709 := bbase (se 3 (by rfl) ⟨448445, by rfl⟩ : syracuseStep 2391709 = 896891) (by norm_num)
theorem B3188945 : Blo 2125435 3188945 := bstep (se 2 (by rfl) ⟨1195854, by rfl⟩ : syracuseStep 3188945 = 2391709) B2391709
theorem B2125963 : Blo 2125435 2125963 := bstep (se 1 (by rfl) ⟨1594472, by rfl⟩ : syracuseStep 2125963 = 3188945) B3188945
theorem B7175141 : Blo 2125435 7175141 := bbase (se 4 (by rfl) ⟨672669, by rfl⟩ : syracuseStep 7175141 = 1345339) (by norm_num)
theorem B4783427 : Blo 2125435 4783427 := bstep (se 1 (by rfl) ⟨3587570, by rfl⟩ : syracuseStep 4783427 = 7175141) B7175141
theorem B3188951 : Blo 2125435 3188951 := bstep (se 1 (by rfl) ⟨2391713, by rfl⟩ : syracuseStep 3188951 = 4783427) B4783427
theorem B2125967 : Blo 2125435 2125967 := bstep (se 1 (by rfl) ⟨1594475, by rfl⟩ : syracuseStep 2125967 = 3188951) B3188951
theorem B3188957 : Blo 2125435 3188957 := bbase (se 3 (by rfl) ⟨597929, by rfl⟩ : syracuseStep 3188957 = 1195859) (by norm_num)
theorem B2125971 : Blo 2125435 2125971 := bstep (se 1 (by rfl) ⟨1594478, by rfl⟩ : syracuseStep 2125971 = 3188957) B3188957
theorem B4783445 : Blo 2125435 4783445 := bbase (se 11 (by rfl) ⟨3503, by rfl⟩ : syracuseStep 4783445 = 7007) (by norm_num)
theorem B3188963 : Blo 2125435 3188963 := bstep (se 1 (by rfl) ⟨2391722, by rfl⟩ : syracuseStep 3188963 = 4783445) B4783445
theorem B2125975 : Blo 2125435 2125975 := bstep (se 1 (by rfl) ⟨1594481, by rfl⟩ : syracuseStep 2125975 = 3188963) B3188963
theorem B2270273 : Blo 2125435 2270273 := bbase (se 2 (by rfl) ⟨851352, by rfl⟩ : syracuseStep 2270273 = 1702705) (by norm_num)
theorem B6054061 : Blo 2125435 6054061 := bstep (se 3 (by rfl) ⟨1135136, by rfl⟩ : syracuseStep 6054061 = 2270273) B2270273
theorem B8072081 : Blo 2125435 8072081 := bstep (se 2 (by rfl) ⟨3027030, by rfl⟩ : syracuseStep 8072081 = 6054061) B6054061
theorem B5381387 : Blo 2125435 5381387 := bstep (se 1 (by rfl) ⟨4036040, by rfl⟩ : syracuseStep 5381387 = 8072081) B8072081
theorem B3587591 : Blo 2125435 3587591 := bstep (se 1 (by rfl) ⟨2690693, by rfl⟩ : syracuseStep 3587591 = 5381387) B5381387
theorem B2391727 : Blo 2125435 2391727 := bstep (se 1 (by rfl) ⟨1793795, by rfl⟩ : syracuseStep 2391727 = 3587591) B3587591
theorem B3188969 : Blo 2125435 3188969 := bstep (se 2 (by rfl) ⟨1195863, by rfl⟩ : syracuseStep 3188969 = 2391727) B2391727
theorem B2125979 : Blo 2125435 2125979 := bstep (se 1 (by rfl) ⟨1594484, by rfl⟩ : syracuseStep 2125979 = 3188969) B3188969
theorem B10909637 : Blo 2125435 10909637 := bbase (se 4 (by rfl) ⟨1022778, by rfl⟩ : syracuseStep 10909637 = 2045557) (by norm_num)
theorem B7273091 : Blo 2125435 7273091 := bstep (se 1 (by rfl) ⟨5454818, by rfl⟩ : syracuseStep 7273091 = 10909637) B10909637
theorem B4848727 : Blo 2125435 4848727 := bstep (se 1 (by rfl) ⟨3636545, by rfl⟩ : syracuseStep 4848727 = 7273091) B7273091
theorem B6464969 : Blo 2125435 6464969 := bstep (se 2 (by rfl) ⟨2424363, by rfl⟩ : syracuseStep 6464969 = 4848727) B4848727
theorem B4309979 : Blo 2125435 4309979 := bstep (se 1 (by rfl) ⟨3232484, by rfl⟩ : syracuseStep 4309979 = 6464969) B6464969
theorem B45973109 : Blo 2125435 45973109 := bstep (se 5 (by rfl) ⟨2154989, by rfl⟩ : syracuseStep 45973109 = 4309979) B4309979
theorem B30648739 : Blo 2125435 30648739 := bstep (se 1 (by rfl) ⟨22986554, by rfl⟩ : syracuseStep 30648739 = 45973109) B45973109
theorem B40864985 : Blo 2125435 40864985 := bstep (se 2 (by rfl) ⟨15324369, by rfl⟩ : syracuseStep 40864985 = 30648739) B30648739
theorem B27243323 : Blo 2125435 27243323 := bstep (se 1 (by rfl) ⟨20432492, by rfl⟩ : syracuseStep 27243323 = 40864985) B40864985
theorem B18162215 : Blo 2125435 18162215 := bstep (se 1 (by rfl) ⟨13621661, by rfl⟩ : syracuseStep 18162215 = 27243323) B27243323
theorem B12108143 : Blo 2125435 12108143 := bstep (se 1 (by rfl) ⟨9081107, by rfl⟩ : syracuseStep 12108143 = 18162215) B18162215
theorem B8072095 : Blo 2125435 8072095 := bstep (se 1 (by rfl) ⟨6054071, by rfl⟩ : syracuseStep 8072095 = 12108143) B12108143
theorem B10762793 : Blo 2125435 10762793 := bstep (se 2 (by rfl) ⟨4036047, by rfl⟩ : syracuseStep 10762793 = 8072095) B8072095
theorem B7175195 : Blo 2125435 7175195 := bstep (se 1 (by rfl) ⟨5381396, by rfl⟩ : syracuseStep 7175195 = 10762793) B10762793
theorem B4783463 : Blo 2125435 4783463 := bstep (se 1 (by rfl) ⟨3587597, by rfl⟩ : syracuseStep 4783463 = 7175195) B7175195
theorem B3188975 : Blo 2125435 3188975 := bstep (se 1 (by rfl) ⟨2391731, by rfl⟩ : syracuseStep 3188975 = 4783463) B4783463
theorem B2125983 : Blo 2125435 2125983 := bstep (se 1 (by rfl) ⟨1594487, by rfl⟩ : syracuseStep 2125983 = 3188975) B3188975
theorem B3188981 : Blo 2125435 3188981 := bbase (se 5 (by rfl) ⟨149483, by rfl⟩ : syracuseStep 3188981 = 298967) (by norm_num)
theorem B2125987 : Blo 2125435 2125987 := bstep (se 1 (by rfl) ⟨1594490, by rfl⟩ : syracuseStep 2125987 = 3188981) B3188981
theorem B2424373 : Blo 2125435 2424373 := bbase (se 5 (by rfl) ⟨113642, by rfl⟩ : syracuseStep 2424373 = 227285) (by norm_num)
theorem B12929989 : Blo 2125435 12929989 := bstep (se 4 (by rfl) ⟨1212186, by rfl⟩ : syracuseStep 12929989 = 2424373) B2424373
theorem B17239985 : Blo 2125435 17239985 := bstep (se 2 (by rfl) ⟨6464994, by rfl⟩ : syracuseStep 17239985 = 12929989) B12929989
theorem B11493323 : Blo 2125435 11493323 := bstep (se 1 (by rfl) ⟨8619992, by rfl⟩ : syracuseStep 11493323 = 17239985) B17239985
theorem B7662215 : Blo 2125435 7662215 := bstep (se 1 (by rfl) ⟨5746661, by rfl⟩ : syracuseStep 7662215 = 11493323) B11493323
theorem B20432573 : Blo 2125435 20432573 := bstep (se 3 (by rfl) ⟨3831107, by rfl⟩ : syracuseStep 20432573 = 7662215) B7662215
theorem B13621715 : Blo 2125435 13621715 := bstep (se 1 (by rfl) ⟨10216286, by rfl⟩ : syracuseStep 13621715 = 20432573) B20432573
theorem B9081143 : Blo 2125435 9081143 := bstep (se 1 (by rfl) ⟨6810857, by rfl⟩ : syracuseStep 9081143 = 13621715) B13621715
theorem B6054095 : Blo 2125435 6054095 := bstep (se 1 (by rfl) ⟨4540571, by rfl⟩ : syracuseStep 6054095 = 9081143) B9081143
theorem B4036063 : Blo 2125435 4036063 := bstep (se 1 (by rfl) ⟨3027047, by rfl⟩ : syracuseStep 4036063 = 6054095) B6054095
theorem B5381417 : Blo 2125435 5381417 := bstep (se 2 (by rfl) ⟨2018031, by rfl⟩ : syracuseStep 5381417 = 4036063) B4036063
theorem B3587611 : Blo 2125435 3587611 := bstep (se 1 (by rfl) ⟨2690708, by rfl⟩ : syracuseStep 3587611 = 5381417) B5381417
theorem B4783481 : Blo 2125435 4783481 := bstep (se 2 (by rfl) ⟨1793805, by rfl⟩ : syracuseStep 4783481 = 3587611) B3587611
theorem B3188987 : Blo 2125435 3188987 := bstep (se 1 (by rfl) ⟨2391740, by rfl⟩ : syracuseStep 3188987 = 4783481) B4783481
theorem B2125991 : Blo 2125435 2125991 := bstep (se 1 (by rfl) ⟨1594493, by rfl⟩ : syracuseStep 2125991 = 3188987) B3188987
theorem B2391745 : Blo 2125435 2391745 := bbase (se 2 (by rfl) ⟨896904, by rfl⟩ : syracuseStep 2391745 = 1793809) (by norm_num)
theorem B3188993 : Blo 2125435 3188993 := bstep (se 2 (by rfl) ⟨1195872, by rfl⟩ : syracuseStep 3188993 = 2391745) B2391745
theorem B2125995 : Blo 2125435 2125995 := bstep (se 1 (by rfl) ⟨1594496, by rfl⟩ : syracuseStep 2125995 = 3188993) B3188993
theorem B5381437 : Blo 2125435 5381437 := bbase (se 3 (by rfl) ⟨1009019, by rfl⟩ : syracuseStep 5381437 = 2018039) (by norm_num)
theorem B7175249 : Blo 2125435 7175249 := bstep (se 2 (by rfl) ⟨2690718, by rfl⟩ : syracuseStep 7175249 = 5381437) B5381437
theorem B4783499 : Blo 2125435 4783499 := bstep (se 1 (by rfl) ⟨3587624, by rfl⟩ : syracuseStep 4783499 = 7175249) B7175249
theorem B3188999 : Blo 2125435 3188999 := bstep (se 1 (by rfl) ⟨2391749, by rfl⟩ : syracuseStep 3188999 = 4783499) B4783499
theorem B2125999 : Blo 2125435 2125999 := bstep (se 1 (by rfl) ⟨1594499, by rfl⟩ : syracuseStep 2125999 = 3188999) B3188999
theorem B3189005 : Blo 2125435 3189005 := bbase (se 3 (by rfl) ⟨597938, by rfl⟩ : syracuseStep 3189005 = 1195877) (by norm_num)
theorem B2126003 : Blo 2125435 2126003 := bstep (se 1 (by rfl) ⟨1594502, by rfl⟩ : syracuseStep 2126003 = 3189005) B3189005
theorem B4783517 : Blo 2125435 4783517 := bbase (se 3 (by rfl) ⟨896909, by rfl⟩ : syracuseStep 4783517 = 1793819) (by norm_num)
theorem B3189011 : Blo 2125435 3189011 := bstep (se 1 (by rfl) ⟨2391758, by rfl⟩ : syracuseStep 3189011 = 4783517) B4783517
theorem B2126007 : Blo 2125435 2126007 := bstep (se 1 (by rfl) ⟨1594505, by rfl⟩ : syracuseStep 2126007 = 3189011) B3189011
theorem B3587645 : Blo 2125435 3587645 := bbase (se 3 (by rfl) ⟨672683, by rfl⟩ : syracuseStep 3587645 = 1345367) (by norm_num)
theorem B2391763 : Blo 2125435 2391763 := bstep (se 1 (by rfl) ⟨1793822, by rfl⟩ : syracuseStep 2391763 = 3587645) B3587645
theorem B3189017 : Blo 2125435 3189017 := bstep (se 2 (by rfl) ⟨1195881, by rfl⟩ : syracuseStep 3189017 = 2391763) B2391763
theorem B2126011 : Blo 2125435 2126011 := bstep (se 1 (by rfl) ⟨1594508, by rfl⟩ : syracuseStep 2126011 = 3189017) B3189017
theorem B6305365 : Blo 2125435 6305365 := bbase (se 8 (by rfl) ⟨36945, by rfl⟩ : syracuseStep 6305365 = 73891) (by norm_num)
theorem B8407153 : Blo 2125435 8407153 := bstep (se 2 (by rfl) ⟨3152682, by rfl⟩ : syracuseStep 8407153 = 6305365) B6305365
theorem B11209537 : Blo 2125435 11209537 := bstep (se 2 (by rfl) ⟨4203576, by rfl⟩ : syracuseStep 11209537 = 8407153) B8407153
theorem B14946049 : Blo 2125435 14946049 := bstep (se 2 (by rfl) ⟨5604768, by rfl⟩ : syracuseStep 14946049 = 11209537) B11209537
theorem B19928065 : Blo 2125435 19928065 := bstep (se 2 (by rfl) ⟨7473024, by rfl⟩ : syracuseStep 19928065 = 14946049) B14946049
theorem B26570753 : Blo 2125435 26570753 := bstep (se 2 (by rfl) ⟨9964032, by rfl⟩ : syracuseStep 26570753 = 19928065) B19928065
theorem B17713835 : Blo 2125435 17713835 := bstep (se 1 (by rfl) ⟨13285376, by rfl⟩ : syracuseStep 17713835 = 26570753) B26570753
theorem B11809223 : Blo 2125435 11809223 := bstep (se 1 (by rfl) ⟨8856917, by rfl⟩ : syracuseStep 11809223 = 17713835) B17713835
theorem B7872815 : Blo 2125435 7872815 := bstep (se 1 (by rfl) ⟨5904611, by rfl⟩ : syracuseStep 7872815 = 11809223) B11809223
theorem B5248543 : Blo 2125435 5248543 := bstep (se 1 (by rfl) ⟨3936407, by rfl⟩ : syracuseStep 5248543 = 7872815) B7872815
theorem B6998057 : Blo 2125435 6998057 := bstep (se 2 (by rfl) ⟨2624271, by rfl⟩ : syracuseStep 6998057 = 5248543) B5248543
theorem B4665371 : Blo 2125435 4665371 := bstep (se 1 (by rfl) ⟨3499028, by rfl⟩ : syracuseStep 4665371 = 6998057) B6998057
theorem B12440989 : Blo 2125435 12440989 := bstep (se 3 (by rfl) ⟨2332685, by rfl⟩ : syracuseStep 12440989 = 4665371) B4665371
theorem B16587985 : Blo 2125435 16587985 := bstep (se 2 (by rfl) ⟨6220494, by rfl⟩ : syracuseStep 16587985 = 12440989) B12440989
theorem B22117313 : Blo 2125435 22117313 := bstep (se 2 (by rfl) ⟨8293992, by rfl⟩ : syracuseStep 22117313 = 16587985) B16587985
theorem B14744875 : Blo 2125435 14744875 := bstep (se 1 (by rfl) ⟨11058656, by rfl⟩ : syracuseStep 14744875 = 22117313) B22117313
theorem B19659833 : Blo 2125435 19659833 := bstep (se 2 (by rfl) ⟨7372437, by rfl⟩ : syracuseStep 19659833 = 14744875) B14744875
theorem B13106555 : Blo 2125435 13106555 := bstep (se 1 (by rfl) ⟨9829916, by rfl⟩ : syracuseStep 13106555 = 19659833) B19659833
theorem B8737703 : Blo 2125435 8737703 := bstep (se 1 (by rfl) ⟨6553277, by rfl⟩ : syracuseStep 8737703 = 13106555) B13106555
theorem B5825135 : Blo 2125435 5825135 := bstep (se 1 (by rfl) ⟨4368851, by rfl⟩ : syracuseStep 5825135 = 8737703) B8737703
theorem B15533693 : Blo 2125435 15533693 := bstep (se 3 (by rfl) ⟨2912567, by rfl⟩ : syracuseStep 15533693 = 5825135) B5825135
theorem B10355795 : Blo 2125435 10355795 := bstep (se 1 (by rfl) ⟨7766846, by rfl⟩ : syracuseStep 10355795 = 15533693) B15533693
theorem B6903863 : Blo 2125435 6903863 := bstep (se 1 (by rfl) ⟨5177897, by rfl⟩ : syracuseStep 6903863 = 10355795) B10355795
theorem B4602575 : Blo 2125435 4602575 := bstep (se 1 (by rfl) ⟨3451931, by rfl⟩ : syracuseStep 4602575 = 6903863) B6903863
theorem B3068383 : Blo 2125435 3068383 := bstep (se 1 (by rfl) ⟨2301287, by rfl⟩ : syracuseStep 3068383 = 4602575) B4602575
theorem B4091177 : Blo 2125435 4091177 := bstep (se 2 (by rfl) ⟨1534191, by rfl⟩ : syracuseStep 4091177 = 3068383) B3068383
theorem B2727451 : Blo 2125435 2727451 := bstep (se 1 (by rfl) ⟨2045588, by rfl⟩ : syracuseStep 2727451 = 4091177) B4091177
theorem B14546405 : Blo 2125435 14546405 := bstep (se 4 (by rfl) ⟨1363725, by rfl⟩ : syracuseStep 14546405 = 2727451) B2727451
theorem B9697603 : Blo 2125435 9697603 := bstep (se 1 (by rfl) ⟨7273202, by rfl⟩ : syracuseStep 9697603 = 14546405) B14546405
theorem B12930137 : Blo 2125435 12930137 := bstep (se 2 (by rfl) ⟨4848801, by rfl⟩ : syracuseStep 12930137 = 9697603) B9697603
theorem B8620091 : Blo 2125435 8620091 := bstep (se 1 (by rfl) ⟨6465068, by rfl⟩ : syracuseStep 8620091 = 12930137) B12930137
theorem B5746727 : Blo 2125435 5746727 := bstep (se 1 (by rfl) ⟨4310045, by rfl⟩ : syracuseStep 5746727 = 8620091) B8620091
theorem B3831151 : Blo 2125435 3831151 := bstep (se 1 (by rfl) ⟨2873363, by rfl⟩ : syracuseStep 3831151 = 5746727) B5746727
theorem B5108201 : Blo 2125435 5108201 := bstep (se 2 (by rfl) ⟨1915575, by rfl⟩ : syracuseStep 5108201 = 3831151) B3831151
theorem B3405467 : Blo 2125435 3405467 := bstep (se 1 (by rfl) ⟨2554100, by rfl⟩ : syracuseStep 3405467 = 5108201) B5108201
theorem B2270311 : Blo 2125435 2270311 := bstep (se 1 (by rfl) ⟨1702733, by rfl⟩ : syracuseStep 2270311 = 3405467) B3405467
theorem B12108325 : Blo 2125435 12108325 := bstep (se 4 (by rfl) ⟨1135155, by rfl⟩ : syracuseStep 12108325 = 2270311) B2270311
theorem B16144433 : Blo 2125435 16144433 := bstep (se 2 (by rfl) ⟨6054162, by rfl⟩ : syracuseStep 16144433 = 12108325) B12108325
theorem B10762955 : Blo 2125435 10762955 := bstep (se 1 (by rfl) ⟨8072216, by rfl⟩ : syracuseStep 10762955 = 16144433) B16144433
theorem B7175303 : Blo 2125435 7175303 := bstep (se 1 (by rfl) ⟨5381477, by rfl⟩ : syracuseStep 7175303 = 10762955) B10762955
theorem B4783535 : Blo 2125435 4783535 := bstep (se 1 (by rfl) ⟨3587651, by rfl⟩ : syracuseStep 4783535 = 7175303) B7175303
theorem B3189023 : Blo 2125435 3189023 := bstep (se 1 (by rfl) ⟨2391767, by rfl⟩ : syracuseStep 3189023 = 4783535) B4783535
theorem B2126015 : Blo 2125435 2126015 := bstep (se 1 (by rfl) ⟨1594511, by rfl⟩ : syracuseStep 2126015 = 3189023) B3189023
theorem B3189029 : Blo 2125435 3189029 := bbase (se 4 (by rfl) ⟨298971, by rfl⟩ : syracuseStep 3189029 = 597943) (by norm_num)
theorem B2126019 : Blo 2125435 2126019 := bstep (se 1 (by rfl) ⟨1594514, by rfl⟩ : syracuseStep 2126019 = 3189029) B3189029
theorem B2690749 : Blo 2125435 2690749 := bbase (se 3 (by rfl) ⟨504515, by rfl⟩ : syracuseStep 2690749 = 1009031) (by norm_num)
theorem B3587665 : Blo 2125435 3587665 := bstep (se 2 (by rfl) ⟨1345374, by rfl⟩ : syracuseStep 3587665 = 2690749) B2690749
theorem B4783553 : Blo 2125435 4783553 := bstep (se 2 (by rfl) ⟨1793832, by rfl⟩ : syracuseStep 4783553 = 3587665) B3587665
theorem B3189035 : Blo 2125435 3189035 := bstep (se 1 (by rfl) ⟨2391776, by rfl⟩ : syracuseStep 3189035 = 4783553) B4783553
theorem B2126023 : Blo 2125435 2126023 := bstep (se 1 (by rfl) ⟨1594517, by rfl⟩ : syracuseStep 2126023 = 3189035) B3189035
theorem B2391781 : Blo 2125435 2391781 := bbase (se 4 (by rfl) ⟨224229, by rfl⟩ : syracuseStep 2391781 = 448459) (by norm_num)
theorem B3189041 : Blo 2125435 3189041 := bstep (se 2 (by rfl) ⟨1195890, by rfl⟩ : syracuseStep 3189041 = 2391781) B2391781
theorem B2126027 : Blo 2125435 2126027 := bstep (se 1 (by rfl) ⟨1594520, by rfl⟩ : syracuseStep 2126027 = 3189041) B3189041
theorem B3405493 : Blo 2125435 3405493 := bbase (se 5 (by rfl) ⟨159632, by rfl⟩ : syracuseStep 3405493 = 319265) (by norm_num)
theorem B4540657 : Blo 2125435 4540657 := bstep (se 2 (by rfl) ⟨1702746, by rfl⟩ : syracuseStep 4540657 = 3405493) B3405493
theorem B6054209 : Blo 2125435 6054209 := bstep (se 2 (by rfl) ⟨2270328, by rfl⟩ : syracuseStep 6054209 = 4540657) B4540657
theorem B4036139 : Blo 2125435 4036139 := bstep (se 1 (by rfl) ⟨3027104, by rfl⟩ : syracuseStep 4036139 = 6054209) B6054209
theorem B2690759 : Blo 2125435 2690759 := bstep (se 1 (by rfl) ⟨2018069, by rfl⟩ : syracuseStep 2690759 = 4036139) B4036139
theorem B7175357 : Blo 2125435 7175357 := bstep (se 3 (by rfl) ⟨1345379, by rfl⟩ : syracuseStep 7175357 = 2690759) B2690759
theorem B4783571 : Blo 2125435 4783571 := bstep (se 1 (by rfl) ⟨3587678, by rfl⟩ : syracuseStep 4783571 = 7175357) B7175357
theorem B3189047 : Blo 2125435 3189047 := bstep (se 1 (by rfl) ⟨2391785, by rfl⟩ : syracuseStep 3189047 = 4783571) B4783571
theorem B2126031 : Blo 2125435 2126031 := bstep (se 1 (by rfl) ⟨1594523, by rfl⟩ : syracuseStep 2126031 = 3189047) B3189047
theorem B3189053 : Blo 2125435 3189053 := bbase (se 3 (by rfl) ⟨597947, by rfl⟩ : syracuseStep 3189053 = 1195895) (by norm_num)
theorem B2126035 : Blo 2125435 2126035 := bstep (se 1 (by rfl) ⟨1594526, by rfl⟩ : syracuseStep 2126035 = 3189053) B3189053
theorem B4783589 : Blo 2125435 4783589 := bbase (se 4 (by rfl) ⟨448461, by rfl⟩ : syracuseStep 4783589 = 896923) (by norm_num)
theorem B3189059 : Blo 2125435 3189059 := bstep (se 1 (by rfl) ⟨2391794, by rfl⟩ : syracuseStep 3189059 = 4783589) B4783589
theorem B2126039 : Blo 2125435 2126039 := bstep (se 1 (by rfl) ⟨1594529, by rfl⟩ : syracuseStep 2126039 = 3189059) B3189059
theorem B5381549 : Blo 2125435 5381549 := bbase (se 3 (by rfl) ⟨1009040, by rfl⟩ : syracuseStep 5381549 = 2018081) (by norm_num)
theorem B3587699 : Blo 2125435 3587699 := bstep (se 1 (by rfl) ⟨2690774, by rfl⟩ : syracuseStep 3587699 = 5381549) B5381549
theorem B2391799 : Blo 2125435 2391799 := bstep (se 1 (by rfl) ⟨1793849, by rfl⟩ : syracuseStep 2391799 = 3587699) B3587699
theorem B3189065 : Blo 2125435 3189065 := bstep (se 2 (by rfl) ⟨1195899, by rfl⟩ : syracuseStep 3189065 = 2391799) B2391799
theorem B2126043 : Blo 2125435 2126043 := bstep (se 1 (by rfl) ⟨1594532, by rfl⟩ : syracuseStep 2126043 = 3189065) B3189065
theorem B3546821 : Blo 2125435 3546821 := bbase (se 4 (by rfl) ⟨332514, by rfl⟩ : syracuseStep 3546821 = 665029) (by norm_num)
theorem B2364547 : Blo 2125435 2364547 := bstep (se 1 (by rfl) ⟨1773410, by rfl⟩ : syracuseStep 2364547 = 3546821) B3546821
theorem B3152729 : Blo 2125435 3152729 := bstep (se 2 (by rfl) ⟨1182273, by rfl⟩ : syracuseStep 3152729 = 2364547) B2364547
theorem B8407277 : Blo 2125435 8407277 := bstep (se 3 (by rfl) ⟨1576364, by rfl⟩ : syracuseStep 8407277 = 3152729) B3152729
theorem B5604851 : Blo 2125435 5604851 := bstep (se 1 (by rfl) ⟨4203638, by rfl⟩ : syracuseStep 5604851 = 8407277) B8407277
theorem B3736567 : Blo 2125435 3736567 := bstep (se 1 (by rfl) ⟨2802425, by rfl⟩ : syracuseStep 3736567 = 5604851) B5604851
theorem B19928357 : Blo 2125435 19928357 := bstep (se 4 (by rfl) ⟨1868283, by rfl⟩ : syracuseStep 19928357 = 3736567) B3736567
theorem B13285571 : Blo 2125435 13285571 := bstep (se 1 (by rfl) ⟨9964178, by rfl⟩ : syracuseStep 13285571 = 19928357) B19928357
theorem B141712757 : Blo 2125435 141712757 := bstep (se 5 (by rfl) ⟨6642785, by rfl⟩ : syracuseStep 141712757 = 13285571) B13285571
theorem B94475171 : Blo 2125435 94475171 := bstep (se 1 (by rfl) ⟨70856378, by rfl⟩ : syracuseStep 94475171 = 141712757) B141712757
theorem B251933789 : Blo 2125435 251933789 := bstep (se 3 (by rfl) ⟨47237585, by rfl⟩ : syracuseStep 251933789 = 94475171) B94475171
theorem B167955859 : Blo 2125435 167955859 := bstep (se 1 (by rfl) ⟨125966894, by rfl⟩ : syracuseStep 167955859 = 251933789) B251933789
theorem B223941145 : Blo 2125435 223941145 := bstep (se 2 (by rfl) ⟨83977929, by rfl⟩ : syracuseStep 223941145 = 167955859) B167955859
theorem B298588193 : Blo 2125435 298588193 := bstep (se 2 (by rfl) ⟨111970572, by rfl⟩ : syracuseStep 298588193 = 223941145) B223941145
theorem B199058795 : Blo 2125435 199058795 := bstep (se 1 (by rfl) ⟨149294096, by rfl⟩ : syracuseStep 199058795 = 298588193) B298588193
theorem B132705863 : Blo 2125435 132705863 := bstep (se 1 (by rfl) ⟨99529397, by rfl⟩ : syracuseStep 132705863 = 199058795) B199058795
theorem B88470575 : Blo 2125435 88470575 := bstep (se 1 (by rfl) ⟨66352931, by rfl⟩ : syracuseStep 88470575 = 132705863) B132705863
theorem B58980383 : Blo 2125435 58980383 := bstep (se 1 (by rfl) ⟨44235287, by rfl⟩ : syracuseStep 58980383 = 88470575) B88470575
theorem B39320255 : Blo 2125435 39320255 := bstep (se 1 (by rfl) ⟨29490191, by rfl⟩ : syracuseStep 39320255 = 58980383) B58980383
theorem B26213503 : Blo 2125435 26213503 := bstep (se 1 (by rfl) ⟨19660127, by rfl⟩ : syracuseStep 26213503 = 39320255) B39320255
theorem B34951337 : Blo 2125435 34951337 := bstep (se 2 (by rfl) ⟨13106751, by rfl⟩ : syracuseStep 34951337 = 26213503) B26213503
theorem B23300891 : Blo 2125435 23300891 := bstep (se 1 (by rfl) ⟨17475668, by rfl⟩ : syracuseStep 23300891 = 34951337) B34951337
theorem B15533927 : Blo 2125435 15533927 := bstep (se 1 (by rfl) ⟨11650445, by rfl⟩ : syracuseStep 15533927 = 23300891) B23300891
theorem B10355951 : Blo 2125435 10355951 := bstep (se 1 (by rfl) ⟨7766963, by rfl⟩ : syracuseStep 10355951 = 15533927) B15533927
theorem B6903967 : Blo 2125435 6903967 := bstep (se 1 (by rfl) ⟨5177975, by rfl⟩ : syracuseStep 6903967 = 10355951) B10355951
theorem B9205289 : Blo 2125435 9205289 := bstep (se 2 (by rfl) ⟨3451983, by rfl⟩ : syracuseStep 9205289 = 6903967) B6903967
theorem B6136859 : Blo 2125435 6136859 := bstep (se 1 (by rfl) ⟨4602644, by rfl⟩ : syracuseStep 6136859 = 9205289) B9205289
theorem B4091239 : Blo 2125435 4091239 := bstep (se 1 (by rfl) ⟨3068429, by rfl⟩ : syracuseStep 4091239 = 6136859) B6136859
theorem B21819941 : Blo 2125435 21819941 := bstep (se 4 (by rfl) ⟨2045619, by rfl⟩ : syracuseStep 21819941 = 4091239) B4091239
theorem B14546627 : Blo 2125435 14546627 := bstep (se 1 (by rfl) ⟨10909970, by rfl⟩ : syracuseStep 14546627 = 21819941) B21819941
theorem B9697751 : Blo 2125435 9697751 := bstep (se 1 (by rfl) ⟨7273313, by rfl⟩ : syracuseStep 9697751 = 14546627) B14546627
theorem B6465167 : Blo 2125435 6465167 := bstep (se 1 (by rfl) ⟨4848875, by rfl⟩ : syracuseStep 6465167 = 9697751) B9697751
theorem B4310111 : Blo 2125435 4310111 := bstep (se 1 (by rfl) ⟨3232583, by rfl⟩ : syracuseStep 4310111 = 6465167) B6465167
theorem B2873407 : Blo 2125435 2873407 := bstep (se 1 (by rfl) ⟨2155055, by rfl⟩ : syracuseStep 2873407 = 4310111) B4310111
theorem B3831209 : Blo 2125435 3831209 := bstep (se 2 (by rfl) ⟨1436703, by rfl⟩ : syracuseStep 3831209 = 2873407) B2873407
theorem B2554139 : Blo 2125435 2554139 := bstep (se 1 (by rfl) ⟨1915604, by rfl⟩ : syracuseStep 2554139 = 3831209) B3831209
theorem B6811037 : Blo 2125435 6811037 := bstep (se 3 (by rfl) ⟨1277069, by rfl⟩ : syracuseStep 6811037 = 2554139) B2554139
theorem B4540691 : Blo 2125435 4540691 := bstep (se 1 (by rfl) ⟨3405518, by rfl⟩ : syracuseStep 4540691 = 6811037) B6811037
theorem B3027127 : Blo 2125435 3027127 := bstep (se 1 (by rfl) ⟨2270345, by rfl⟩ : syracuseStep 3027127 = 4540691) B4540691
theorem B4036169 : Blo 2125435 4036169 := bstep (se 2 (by rfl) ⟨1513563, by rfl⟩ : syracuseStep 4036169 = 3027127) B3027127
theorem B10763117 : Blo 2125435 10763117 := bstep (se 3 (by rfl) ⟨2018084, by rfl⟩ : syracuseStep 10763117 = 4036169) B4036169
theorem B7175411 : Blo 2125435 7175411 := bstep (se 1 (by rfl) ⟨5381558, by rfl⟩ : syracuseStep 7175411 = 10763117) B10763117
theorem B4783607 : Blo 2125435 4783607 := bstep (se 1 (by rfl) ⟨3587705, by rfl⟩ : syracuseStep 4783607 = 7175411) B7175411
theorem B3189071 : Blo 2125435 3189071 := bstep (se 1 (by rfl) ⟨2391803, by rfl⟩ : syracuseStep 3189071 = 4783607) B4783607
theorem B2126047 : Blo 2125435 2126047 := bstep (se 1 (by rfl) ⟨1594535, by rfl⟩ : syracuseStep 2126047 = 3189071) B3189071
theorem B3189077 : Blo 2125435 3189077 := bbase (se 10 (by rfl) ⟨4671, by rfl⟩ : syracuseStep 3189077 = 9343) (by norm_num)
theorem B2126051 : Blo 2125435 2126051 := bstep (se 1 (by rfl) ⟨1594538, by rfl⟩ : syracuseStep 2126051 = 3189077) B3189077
theorem B6054277 : Blo 2125435 6054277 := bbase (se 4 (by rfl) ⟨567588, by rfl⟩ : syracuseStep 6054277 = 1135177) (by norm_num)
theorem B8072369 : Blo 2125435 8072369 := bstep (se 2 (by rfl) ⟨3027138, by rfl⟩ : syracuseStep 8072369 = 6054277) B6054277
theorem B5381579 : Blo 2125435 5381579 := bstep (se 1 (by rfl) ⟨4036184, by rfl⟩ : syracuseStep 5381579 = 8072369) B8072369
theorem B3587719 : Blo 2125435 3587719 := bstep (se 1 (by rfl) ⟨2690789, by rfl⟩ : syracuseStep 3587719 = 5381579) B5381579
theorem B4783625 : Blo 2125435 4783625 := bstep (se 2 (by rfl) ⟨1793859, by rfl⟩ : syracuseStep 4783625 = 3587719) B3587719
theorem B3189083 : Blo 2125435 3189083 := bstep (se 1 (by rfl) ⟨2391812, by rfl⟩ : syracuseStep 3189083 = 4783625) B4783625
theorem B2126055 : Blo 2125435 2126055 := bstep (se 1 (by rfl) ⟨1594541, by rfl⟩ : syracuseStep 2126055 = 3189083) B3189083
theorem B2391817 : Blo 2125435 2391817 := bbase (se 2 (by rfl) ⟨896931, by rfl⟩ : syracuseStep 2391817 = 1793863) (by norm_num)
theorem B3189089 : Blo 2125435 3189089 := bstep (se 2 (by rfl) ⟨1195908, by rfl⟩ : syracuseStep 3189089 = 2391817) B2391817
theorem B2126059 : Blo 2125435 2126059 := bstep (se 1 (by rfl) ⟨1594544, by rfl⟩ : syracuseStep 2126059 = 3189089) B3189089
theorem B15745973 : Blo 2125435 15745973 := bbase (se 5 (by rfl) ⟨738092, by rfl⟩ : syracuseStep 15745973 = 1476185) (by norm_num)
theorem B41989261 : Blo 2125435 41989261 := bstep (se 3 (by rfl) ⟨7872986, by rfl⟩ : syracuseStep 41989261 = 15745973) B15745973
theorem B55985681 : Blo 2125435 55985681 := bstep (se 2 (by rfl) ⟨20994630, by rfl⟩ : syracuseStep 55985681 = 41989261) B41989261
theorem B37323787 : Blo 2125435 37323787 := bstep (se 1 (by rfl) ⟨27992840, by rfl⟩ : syracuseStep 37323787 = 55985681) B55985681
theorem B49765049 : Blo 2125435 49765049 := bstep (se 2 (by rfl) ⟨18661893, by rfl⟩ : syracuseStep 49765049 = 37323787) B37323787
theorem B33176699 : Blo 2125435 33176699 := bstep (se 1 (by rfl) ⟨24882524, by rfl⟩ : syracuseStep 33176699 = 49765049) B49765049
theorem B22117799 : Blo 2125435 22117799 := bstep (se 1 (by rfl) ⟨16588349, by rfl⟩ : syracuseStep 22117799 = 33176699) B33176699
theorem B14745199 : Blo 2125435 14745199 := bstep (se 1 (by rfl) ⟨11058899, by rfl⟩ : syracuseStep 14745199 = 22117799) B22117799
theorem B19660265 : Blo 2125435 19660265 := bstep (se 2 (by rfl) ⟨7372599, by rfl⟩ : syracuseStep 19660265 = 14745199) B14745199
theorem B13106843 : Blo 2125435 13106843 := bstep (se 1 (by rfl) ⟨9830132, by rfl⟩ : syracuseStep 13106843 = 19660265) B19660265
theorem B8737895 : Blo 2125435 8737895 := bstep (se 1 (by rfl) ⟨6553421, by rfl⟩ : syracuseStep 8737895 = 13106843) B13106843
theorem B5825263 : Blo 2125435 5825263 := bstep (se 1 (by rfl) ⟨4368947, by rfl⟩ : syracuseStep 5825263 = 8737895) B8737895
theorem B7767017 : Blo 2125435 7767017 := bstep (se 2 (by rfl) ⟨2912631, by rfl⟩ : syracuseStep 7767017 = 5825263) B5825263
theorem B5178011 : Blo 2125435 5178011 := bstep (se 1 (by rfl) ⟨3883508, by rfl⟩ : syracuseStep 5178011 = 7767017) B7767017
theorem B55232117 : Blo 2125435 55232117 := bstep (se 5 (by rfl) ⟨2589005, by rfl⟩ : syracuseStep 55232117 = 5178011) B5178011
theorem B36821411 : Blo 2125435 36821411 := bstep (se 1 (by rfl) ⟨27616058, by rfl⟩ : syracuseStep 36821411 = 55232117) B55232117
theorem B24547607 : Blo 2125435 24547607 := bstep (se 1 (by rfl) ⟨18410705, by rfl⟩ : syracuseStep 24547607 = 36821411) B36821411
theorem B16365071 : Blo 2125435 16365071 := bstep (se 1 (by rfl) ⟨12273803, by rfl⟩ : syracuseStep 16365071 = 24547607) B24547607
theorem B10910047 : Blo 2125435 10910047 := bstep (se 1 (by rfl) ⟨8182535, by rfl⟩ : syracuseStep 10910047 = 16365071) B16365071
theorem B14546729 : Blo 2125435 14546729 := bstep (se 2 (by rfl) ⟨5455023, by rfl⟩ : syracuseStep 14546729 = 10910047) B10910047
theorem B9697819 : Blo 2125435 9697819 := bstep (se 1 (by rfl) ⟨7273364, by rfl⟩ : syracuseStep 9697819 = 14546729) B14546729
theorem B12930425 : Blo 2125435 12930425 := bstep (se 2 (by rfl) ⟨4848909, by rfl⟩ : syracuseStep 12930425 = 9697819) B9697819
theorem B8620283 : Blo 2125435 8620283 := bstep (se 1 (by rfl) ⟨6465212, by rfl⟩ : syracuseStep 8620283 = 12930425) B12930425
theorem B22987421 : Blo 2125435 22987421 := bstep (se 3 (by rfl) ⟨4310141, by rfl⟩ : syracuseStep 22987421 = 8620283) B8620283
theorem B15324947 : Blo 2125435 15324947 := bstep (se 1 (by rfl) ⟨11493710, by rfl⟩ : syracuseStep 15324947 = 22987421) B22987421
theorem B10216631 : Blo 2125435 10216631 := bstep (se 1 (by rfl) ⟨7662473, by rfl⟩ : syracuseStep 10216631 = 15324947) B15324947
theorem B27244349 : Blo 2125435 27244349 := bstep (se 3 (by rfl) ⟨5108315, by rfl⟩ : syracuseStep 27244349 = 10216631) B10216631
theorem B18162899 : Blo 2125435 18162899 := bstep (se 1 (by rfl) ⟨13622174, by rfl⟩ : syracuseStep 18162899 = 27244349) B27244349
theorem B12108599 : Blo 2125435 12108599 := bstep (se 1 (by rfl) ⟨9081449, by rfl⟩ : syracuseStep 12108599 = 18162899) B18162899
theorem B8072399 : Blo 2125435 8072399 := bstep (se 1 (by rfl) ⟨6054299, by rfl⟩ : syracuseStep 8072399 = 12108599) B12108599
theorem B5381599 : Blo 2125435 5381599 := bstep (se 1 (by rfl) ⟨4036199, by rfl⟩ : syracuseStep 5381599 = 8072399) B8072399
theorem B7175465 : Blo 2125435 7175465 := bstep (se 2 (by rfl) ⟨2690799, by rfl⟩ : syracuseStep 7175465 = 5381599) B5381599
theorem B4783643 : Blo 2125435 4783643 := bstep (se 1 (by rfl) ⟨3587732, by rfl⟩ : syracuseStep 4783643 = 7175465) B7175465
theorem B3189095 : Blo 2125435 3189095 := bstep (se 1 (by rfl) ⟨2391821, by rfl⟩ : syracuseStep 3189095 = 4783643) B4783643
theorem B2126063 : Blo 2125435 2126063 := bstep (se 1 (by rfl) ⟨1594547, by rfl⟩ : syracuseStep 2126063 = 3189095) B3189095
theorem B3189101 : Blo 2125435 3189101 := bbase (se 3 (by rfl) ⟨597956, by rfl⟩ : syracuseStep 3189101 = 1195913) (by norm_num)
theorem B2126067 : Blo 2125435 2126067 := bstep (se 1 (by rfl) ⟨1594550, by rfl⟩ : syracuseStep 2126067 = 3189101) B3189101
theorem B4783661 : Blo 2125435 4783661 := bbase (se 3 (by rfl) ⟨896936, by rfl⟩ : syracuseStep 4783661 = 1793873) (by norm_num)
theorem B3189107 : Blo 2125435 3189107 := bstep (se 1 (by rfl) ⟨2391830, by rfl⟩ : syracuseStep 3189107 = 4783661) B4783661
theorem B2126071 : Blo 2125435 2126071 := bstep (se 1 (by rfl) ⟨1594553, by rfl⟩ : syracuseStep 2126071 = 3189107) B3189107
theorem B31068245 : Blo 2125435 31068245 := bbase (se 8 (by rfl) ⟨182040, by rfl⟩ : syracuseStep 31068245 = 364081) (by norm_num)
theorem B82848653 : Blo 2125435 82848653 := bstep (se 3 (by rfl) ⟨15534122, by rfl⟩ : syracuseStep 82848653 = 31068245) B31068245
theorem B55232435 : Blo 2125435 55232435 := bstep (se 1 (by rfl) ⟨41424326, by rfl⟩ : syracuseStep 55232435 = 82848653) B82848653
theorem B36821623 : Blo 2125435 36821623 := bstep (se 1 (by rfl) ⟨27616217, by rfl⟩ : syracuseStep 36821623 = 55232435) B55232435
theorem B49095497 : Blo 2125435 49095497 := bstep (se 2 (by rfl) ⟨18410811, by rfl⟩ : syracuseStep 49095497 = 36821623) B36821623
theorem B32730331 : Blo 2125435 32730331 := bstep (se 1 (by rfl) ⟨24547748, by rfl⟩ : syracuseStep 32730331 = 49095497) B49095497
theorem B43640441 : Blo 2125435 43640441 := bstep (se 2 (by rfl) ⟨16365165, by rfl⟩ : syracuseStep 43640441 = 32730331) B32730331
theorem B29093627 : Blo 2125435 29093627 := bstep (se 1 (by rfl) ⟨21820220, by rfl⟩ : syracuseStep 29093627 = 43640441) B43640441
theorem B77583005 : Blo 2125435 77583005 := bstep (se 3 (by rfl) ⟨14546813, by rfl⟩ : syracuseStep 77583005 = 29093627) B29093627
theorem B51722003 : Blo 2125435 51722003 := bstep (se 1 (by rfl) ⟨38791502, by rfl⟩ : syracuseStep 51722003 = 77583005) B77583005
theorem B34481335 : Blo 2125435 34481335 := bstep (se 1 (by rfl) ⟨25861001, by rfl⟩ : syracuseStep 34481335 = 51722003) B51722003
theorem B45975113 : Blo 2125435 45975113 := bstep (se 2 (by rfl) ⟨17240667, by rfl⟩ : syracuseStep 45975113 = 34481335) B34481335
theorem B30650075 : Blo 2125435 30650075 := bstep (se 1 (by rfl) ⟨22987556, by rfl⟩ : syracuseStep 30650075 = 45975113) B45975113
theorem B20433383 : Blo 2125435 20433383 := bstep (se 1 (by rfl) ⟨15325037, by rfl⟩ : syracuseStep 20433383 = 30650075) B30650075
theorem B13622255 : Blo 2125435 13622255 := bstep (se 1 (by rfl) ⟨10216691, by rfl⟩ : syracuseStep 13622255 = 20433383) B20433383
theorem B9081503 : Blo 2125435 9081503 := bstep (se 1 (by rfl) ⟨6811127, by rfl⟩ : syracuseStep 9081503 = 13622255) B13622255
theorem B6054335 : Blo 2125435 6054335 := bstep (se 1 (by rfl) ⟨4540751, by rfl⟩ : syracuseStep 6054335 = 9081503) B9081503
theorem B4036223 : Blo 2125435 4036223 := bstep (se 1 (by rfl) ⟨3027167, by rfl⟩ : syracuseStep 4036223 = 6054335) B6054335
theorem B2690815 : Blo 2125435 2690815 := bstep (se 1 (by rfl) ⟨2018111, by rfl⟩ : syracuseStep 2690815 = 4036223) B4036223
theorem B3587753 : Blo 2125435 3587753 := bstep (se 2 (by rfl) ⟨1345407, by rfl⟩ : syracuseStep 3587753 = 2690815) B2690815
theorem B2391835 : Blo 2125435 2391835 := bstep (se 1 (by rfl) ⟨1793876, by rfl⟩ : syracuseStep 2391835 = 3587753) B3587753
theorem B3189113 : Blo 2125435 3189113 := bstep (se 2 (by rfl) ⟨1195917, by rfl⟩ : syracuseStep 3189113 = 2391835) B2391835
theorem B2126075 : Blo 2125435 2126075 := bstep (se 1 (by rfl) ⟨1594556, by rfl⟩ : syracuseStep 2126075 = 3189113) B3189113
theorem B2554177 : Blo 2125435 2554177 := bbase (se 2 (by rfl) ⟨957816, by rfl⟩ : syracuseStep 2554177 = 1915633) (by norm_num)
theorem B3405569 : Blo 2125435 3405569 := bstep (se 2 (by rfl) ⟨1277088, by rfl⟩ : syracuseStep 3405569 = 2554177) B2554177
theorem B36326069 : Blo 2125435 36326069 := bstep (se 5 (by rfl) ⟨1702784, by rfl⟩ : syracuseStep 36326069 = 3405569) B3405569
theorem B24217379 : Blo 2125435 24217379 := bstep (se 1 (by rfl) ⟨18163034, by rfl⟩ : syracuseStep 24217379 = 36326069) B36326069
theorem B16144919 : Blo 2125435 16144919 := bstep (se 1 (by rfl) ⟨12108689, by rfl⟩ : syracuseStep 16144919 = 24217379) B24217379
theorem B10763279 : Blo 2125435 10763279 := bstep (se 1 (by rfl) ⟨8072459, by rfl⟩ : syracuseStep 10763279 = 16144919) B16144919
theorem B7175519 : Blo 2125435 7175519 := bstep (se 1 (by rfl) ⟨5381639, by rfl⟩ : syracuseStep 7175519 = 10763279) B10763279
theorem B4783679 : Blo 2125435 4783679 := bstep (se 1 (by rfl) ⟨3587759, by rfl⟩ : syracuseStep 4783679 = 7175519) B7175519
theorem B3189119 : Blo 2125435 3189119 := bstep (se 1 (by rfl) ⟨2391839, by rfl⟩ : syracuseStep 3189119 = 4783679) B4783679
theorem B2126079 : Blo 2125435 2126079 := bstep (se 1 (by rfl) ⟨1594559, by rfl⟩ : syracuseStep 2126079 = 3189119) B3189119
theorem B3189125 : Blo 2125435 3189125 := bbase (se 4 (by rfl) ⟨298980, by rfl⟩ : syracuseStep 3189125 = 597961) (by norm_num)
theorem B2126083 : Blo 2125435 2126083 := bstep (se 1 (by rfl) ⟨1594562, by rfl⟩ : syracuseStep 2126083 = 3189125) B3189125
theorem B3587773 : Blo 2125435 3587773 := bbase (se 3 (by rfl) ⟨672707, by rfl⟩ : syracuseStep 3587773 = 1345415) (by norm_num)
theorem B4783697 : Blo 2125435 4783697 := bstep (se 2 (by rfl) ⟨1793886, by rfl⟩ : syracuseStep 4783697 = 3587773) B3587773
theorem B3189131 : Blo 2125435 3189131 := bstep (se 1 (by rfl) ⟨2391848, by rfl⟩ : syracuseStep 3189131 = 4783697) B4783697
theorem B2126087 : Blo 2125435 2126087 := bstep (se 1 (by rfl) ⟨1594565, by rfl⟩ : syracuseStep 2126087 = 3189131) B3189131
theorem B2391853 : Blo 2125435 2391853 := bbase (se 3 (by rfl) ⟨448472, by rfl⟩ : syracuseStep 2391853 = 896945) (by norm_num)
theorem B3189137 : Blo 2125435 3189137 := bstep (se 2 (by rfl) ⟨1195926, by rfl⟩ : syracuseStep 3189137 = 2391853) B2391853
theorem B2126091 : Blo 2125435 2126091 := bstep (se 1 (by rfl) ⟨1594568, by rfl⟩ : syracuseStep 2126091 = 3189137) B3189137
theorem B7175573 : Blo 2125435 7175573 := bbase (se 6 (by rfl) ⟨168177, by rfl⟩ : syracuseStep 7175573 = 336355) (by norm_num)
theorem B4783715 : Blo 2125435 4783715 := bstep (se 1 (by rfl) ⟨3587786, by rfl⟩ : syracuseStep 4783715 = 7175573) B7175573
theorem B3189143 : Blo 2125435 3189143 := bstep (se 1 (by rfl) ⟨2391857, by rfl⟩ : syracuseStep 3189143 = 4783715) B4783715
theorem B2126095 : Blo 2125435 2126095 := bstep (se 1 (by rfl) ⟨1594571, by rfl⟩ : syracuseStep 2126095 = 3189143) B3189143
theorem B3189149 : Blo 2125435 3189149 := bbase (se 3 (by rfl) ⟨597965, by rfl⟩ : syracuseStep 3189149 = 1195931) (by norm_num)
theorem B2126099 : Blo 2125435 2126099 := bstep (se 1 (by rfl) ⟨1594574, by rfl⟩ : syracuseStep 2126099 = 3189149) B3189149
theorem B4783733 : Blo 2125435 4783733 := bbase (se 5 (by rfl) ⟨224237, by rfl⟩ : syracuseStep 4783733 = 448475) (by norm_num)
theorem B3189155 : Blo 2125435 3189155 := bstep (se 1 (by rfl) ⟨2391866, by rfl⟩ : syracuseStep 3189155 = 4783733) B4783733
theorem B2126103 : Blo 2125435 2126103 := bstep (se 1 (by rfl) ⟨1594577, by rfl⟩ : syracuseStep 2126103 = 3189155) B3189155
theorem B3831317 : Blo 2125435 3831317 := bbase (se 6 (by rfl) ⟨89796, by rfl⟩ : syracuseStep 3831317 = 179593) (by norm_num)
theorem B2554211 : Blo 2125435 2554211 := bstep (se 1 (by rfl) ⟨1915658, by rfl⟩ : syracuseStep 2554211 = 3831317) B3831317
theorem B6811229 : Blo 2125435 6811229 := bstep (se 3 (by rfl) ⟨1277105, by rfl⟩ : syracuseStep 6811229 = 2554211) B2554211
theorem B18163277 : Blo 2125435 18163277 := bstep (se 3 (by rfl) ⟨3405614, by rfl⟩ : syracuseStep 18163277 = 6811229) B6811229
theorem B12108851 : Blo 2125435 12108851 := bstep (se 1 (by rfl) ⟨9081638, by rfl⟩ : syracuseStep 12108851 = 18163277) B18163277
theorem B8072567 : Blo 2125435 8072567 := bstep (se 1 (by rfl) ⟨6054425, by rfl⟩ : syracuseStep 8072567 = 12108851) B12108851
theorem B5381711 : Blo 2125435 5381711 := bstep (se 1 (by rfl) ⟨4036283, by rfl⟩ : syracuseStep 5381711 = 8072567) B8072567
theorem B3587807 : Blo 2125435 3587807 := bstep (se 1 (by rfl) ⟨2690855, by rfl⟩ : syracuseStep 3587807 = 5381711) B5381711
theorem B2391871 : Blo 2125435 2391871 := bstep (se 1 (by rfl) ⟨1793903, by rfl⟩ : syracuseStep 2391871 = 3587807) B3587807
theorem B3189161 : Blo 2125435 3189161 := bstep (se 2 (by rfl) ⟨1195935, by rfl⟩ : syracuseStep 3189161 = 2391871) B2391871
theorem B2126107 : Blo 2125435 2126107 := bstep (se 1 (by rfl) ⟨1594580, by rfl⟩ : syracuseStep 2126107 = 3189161) B3189161
theorem B8072581 : Blo 2125435 8072581 := bbase (se 4 (by rfl) ⟨756804, by rfl⟩ : syracuseStep 8072581 = 1513609) (by norm_num)
theorem B10763441 : Blo 2125435 10763441 := bstep (se 2 (by rfl) ⟨4036290, by rfl⟩ : syracuseStep 10763441 = 8072581) B8072581
theorem B7175627 : Blo 2125435 7175627 := bstep (se 1 (by rfl) ⟨5381720, by rfl⟩ : syracuseStep 7175627 = 10763441) B10763441
theorem B4783751 : Blo 2125435 4783751 := bstep (se 1 (by rfl) ⟨3587813, by rfl⟩ : syracuseStep 4783751 = 7175627) B7175627
theorem B3189167 : Blo 2125435 3189167 := bstep (se 1 (by rfl) ⟨2391875, by rfl⟩ : syracuseStep 3189167 = 4783751) B4783751
theorem B2126111 : Blo 2125435 2126111 := bstep (se 1 (by rfl) ⟨1594583, by rfl⟩ : syracuseStep 2126111 = 3189167) B3189167
theorem B3189173 : Blo 2125435 3189173 := bbase (se 5 (by rfl) ⟨149492, by rfl⟩ : syracuseStep 3189173 = 298985) (by norm_num)
theorem B2126115 : Blo 2125435 2126115 := bstep (se 1 (by rfl) ⟨1594586, by rfl⟩ : syracuseStep 2126115 = 3189173) B3189173
theorem B5381741 : Blo 2125435 5381741 := bbase (se 3 (by rfl) ⟨1009076, by rfl⟩ : syracuseStep 5381741 = 2018153) (by norm_num)
theorem B3587827 : Blo 2125435 3587827 := bstep (se 1 (by rfl) ⟨2690870, by rfl⟩ : syracuseStep 3587827 = 5381741) B5381741
theorem B4783769 : Blo 2125435 4783769 := bstep (se 2 (by rfl) ⟨1793913, by rfl⟩ : syracuseStep 4783769 = 3587827) B3587827
theorem B3189179 : Blo 2125435 3189179 := bstep (se 1 (by rfl) ⟨2391884, by rfl⟩ : syracuseStep 3189179 = 4783769) B4783769
theorem B2126119 : Blo 2125435 2126119 := bstep (se 1 (by rfl) ⟨1594589, by rfl⟩ : syracuseStep 2126119 = 3189179) B3189179
theorem B2391889 : Blo 2125435 2391889 := bbase (se 2 (by rfl) ⟨896958, by rfl⟩ : syracuseStep 2391889 = 1793917) (by norm_num)
theorem B3189185 : Blo 2125435 3189185 := bstep (se 2 (by rfl) ⟨1195944, by rfl⟩ : syracuseStep 3189185 = 2391889) B2391889
theorem B2126123 : Blo 2125435 2126123 := bstep (se 1 (by rfl) ⟨1594592, by rfl⟩ : syracuseStep 2126123 = 3189185) B3189185
theorem B2424529 : Blo 2125435 2424529 := bbase (se 2 (by rfl) ⟨909198, by rfl⟩ : syracuseStep 2424529 = 1818397) (by norm_num)
theorem B3232705 : Blo 2125435 3232705 := bstep (se 2 (by rfl) ⟨1212264, by rfl⟩ : syracuseStep 3232705 = 2424529) B2424529
theorem B4310273 : Blo 2125435 4310273 := bstep (se 2 (by rfl) ⟨1616352, by rfl⟩ : syracuseStep 4310273 = 3232705) B3232705
theorem B11494061 : Blo 2125435 11494061 := bstep (se 3 (by rfl) ⟨2155136, by rfl⟩ : syracuseStep 11494061 = 4310273) B4310273
theorem B7662707 : Blo 2125435 7662707 := bstep (se 1 (by rfl) ⟨5747030, by rfl⟩ : syracuseStep 7662707 = 11494061) B11494061
theorem B5108471 : Blo 2125435 5108471 := bstep (se 1 (by rfl) ⟨3831353, by rfl⟩ : syracuseStep 5108471 = 7662707) B7662707
theorem B3405647 : Blo 2125435 3405647 := bstep (se 1 (by rfl) ⟨2554235, by rfl⟩ : syracuseStep 3405647 = 5108471) B5108471
theorem B2270431 : Blo 2125435 2270431 := bstep (se 1 (by rfl) ⟨1702823, by rfl⟩ : syracuseStep 2270431 = 3405647) B3405647
theorem B3027241 : Blo 2125435 3027241 := bstep (se 2 (by rfl) ⟨1135215, by rfl⟩ : syracuseStep 3027241 = 2270431) B2270431
theorem B4036321 : Blo 2125435 4036321 := bstep (se 2 (by rfl) ⟨1513620, by rfl⟩ : syracuseStep 4036321 = 3027241) B3027241
theorem B5381761 : Blo 2125435 5381761 := bstep (se 2 (by rfl) ⟨2018160, by rfl⟩ : syracuseStep 5381761 = 4036321) B4036321
theorem B7175681 : Blo 2125435 7175681 := bstep (se 2 (by rfl) ⟨2690880, by rfl⟩ : syracuseStep 7175681 = 5381761) B5381761
theorem B4783787 : Blo 2125435 4783787 := bstep (se 1 (by rfl) ⟨3587840, by rfl⟩ : syracuseStep 4783787 = 7175681) B7175681
theorem B3189191 : Blo 2125435 3189191 := bstep (se 1 (by rfl) ⟨2391893, by rfl⟩ : syracuseStep 3189191 = 4783787) B4783787
theorem B2126127 : Blo 2125435 2126127 := bstep (se 1 (by rfl) ⟨1594595, by rfl⟩ : syracuseStep 2126127 = 3189191) B3189191
theorem B3189197 : Blo 2125435 3189197 := bbase (se 3 (by rfl) ⟨597974, by rfl⟩ : syracuseStep 3189197 = 1195949) (by norm_num)
theorem B2126131 : Blo 2125435 2126131 := bstep (se 1 (by rfl) ⟨1594598, by rfl⟩ : syracuseStep 2126131 = 3189197) B3189197
theorem B4783805 : Blo 2125435 4783805 := bbase (se 3 (by rfl) ⟨896963, by rfl⟩ : syracuseStep 4783805 = 1793927) (by norm_num)
theorem B3189203 : Blo 2125435 3189203 := bstep (se 1 (by rfl) ⟨2391902, by rfl⟩ : syracuseStep 3189203 = 4783805) B4783805
theorem B2126135 : Blo 2125435 2126135 := bstep (se 1 (by rfl) ⟨1594601, by rfl⟩ : syracuseStep 2126135 = 3189203) B3189203
theorem B3587861 : Blo 2125435 3587861 := bbase (se 6 (by rfl) ⟨84090, by rfl⟩ : syracuseStep 3587861 = 168181) (by norm_num)
theorem B2391907 : Blo 2125435 2391907 := bstep (se 1 (by rfl) ⟨1793930, by rfl⟩ : syracuseStep 2391907 = 3587861) B3587861
theorem B3189209 : Blo 2125435 3189209 := bstep (se 2 (by rfl) ⟨1195953, by rfl⟩ : syracuseStep 3189209 = 2391907) B2391907
theorem B2126139 : Blo 2125435 2126139 := bstep (se 1 (by rfl) ⟨1594604, by rfl⟩ : syracuseStep 2126139 = 3189209) B3189209
theorem B5178205 : Blo 2125435 5178205 := bbase (se 3 (by rfl) ⟨970913, by rfl⟩ : syracuseStep 5178205 = 1941827) (by norm_num)
theorem B27617093 : Blo 2125435 27617093 := bstep (se 4 (by rfl) ⟨2589102, by rfl⟩ : syracuseStep 27617093 = 5178205) B5178205
theorem B18411395 : Blo 2125435 18411395 := bstep (se 1 (by rfl) ⟨13808546, by rfl⟩ : syracuseStep 18411395 = 27617093) B27617093
theorem B49097053 : Blo 2125435 49097053 := bstep (se 3 (by rfl) ⟨9205697, by rfl⟩ : syracuseStep 49097053 = 18411395) B18411395
theorem B65462737 : Blo 2125435 65462737 := bstep (se 2 (by rfl) ⟨24548526, by rfl⟩ : syracuseStep 65462737 = 49097053) B49097053
theorem B87283649 : Blo 2125435 87283649 := bstep (se 2 (by rfl) ⟨32731368, by rfl⟩ : syracuseStep 87283649 = 65462737) B65462737
theorem B58189099 : Blo 2125435 58189099 := bstep (se 1 (by rfl) ⟨43641824, by rfl⟩ : syracuseStep 58189099 = 87283649) B87283649
theorem B77585465 : Blo 2125435 77585465 := bstep (se 2 (by rfl) ⟨29094549, by rfl⟩ : syracuseStep 77585465 = 58189099) B58189099
theorem B51723643 : Blo 2125435 51723643 := bstep (se 1 (by rfl) ⟨38792732, by rfl⟩ : syracuseStep 51723643 = 77585465) B77585465
theorem B68964857 : Blo 2125435 68964857 := bstep (se 2 (by rfl) ⟨25861821, by rfl⟩ : syracuseStep 68964857 = 51723643) B51723643
theorem B45976571 : Blo 2125435 45976571 := bstep (se 1 (by rfl) ⟨34482428, by rfl⟩ : syracuseStep 45976571 = 68964857) B68964857
theorem B30651047 : Blo 2125435 30651047 := bstep (se 1 (by rfl) ⟨22988285, by rfl⟩ : syracuseStep 30651047 = 45976571) B45976571
theorem B20434031 : Blo 2125435 20434031 := bstep (se 1 (by rfl) ⟨15325523, by rfl⟩ : syracuseStep 20434031 = 30651047) B30651047
theorem B13622687 : Blo 2125435 13622687 := bstep (se 1 (by rfl) ⟨10217015, by rfl⟩ : syracuseStep 13622687 = 20434031) B20434031
theorem B9081791 : Blo 2125435 9081791 := bstep (se 1 (by rfl) ⟨6811343, by rfl⟩ : syracuseStep 9081791 = 13622687) B13622687
theorem B6054527 : Blo 2125435 6054527 := bstep (se 1 (by rfl) ⟨4540895, by rfl⟩ : syracuseStep 6054527 = 9081791) B9081791
theorem B16145405 : Blo 2125435 16145405 := bstep (se 3 (by rfl) ⟨3027263, by rfl⟩ : syracuseStep 16145405 = 6054527) B6054527
theorem B10763603 : Blo 2125435 10763603 := bstep (se 1 (by rfl) ⟨8072702, by rfl⟩ : syracuseStep 10763603 = 16145405) B16145405
theorem B7175735 : Blo 2125435 7175735 := bstep (se 1 (by rfl) ⟨5381801, by rfl⟩ : syracuseStep 7175735 = 10763603) B10763603
theorem B4783823 : Blo 2125435 4783823 := bstep (se 1 (by rfl) ⟨3587867, by rfl⟩ : syracuseStep 4783823 = 7175735) B7175735
theorem B3189215 : Blo 2125435 3189215 := bstep (se 1 (by rfl) ⟨2391911, by rfl⟩ : syracuseStep 3189215 = 4783823) B4783823
theorem B2126143 : Blo 2125435 2126143 := bstep (se 1 (by rfl) ⟨1594607, by rfl⟩ : syracuseStep 2126143 = 3189215) B3189215
theorem B3189221 : Blo 2125435 3189221 := bbase (se 4 (by rfl) ⟨298989, by rfl⟩ : syracuseStep 3189221 = 597979) (by norm_num)
theorem B2126147 : Blo 2125435 2126147 := bstep (se 1 (by rfl) ⟨1594610, by rfl⟩ : syracuseStep 2126147 = 3189221) B3189221
theorem B13622741 : Blo 2125435 13622741 := bbase (se 7 (by rfl) ⟨159641, by rfl⟩ : syracuseStep 13622741 = 319283) (by norm_num)
theorem B9081827 : Blo 2125435 9081827 := bstep (se 1 (by rfl) ⟨6811370, by rfl⟩ : syracuseStep 9081827 = 13622741) B13622741
theorem B6054551 : Blo 2125435 6054551 := bstep (se 1 (by rfl) ⟨4540913, by rfl⟩ : syracuseStep 6054551 = 9081827) B9081827
theorem B4036367 : Blo 2125435 4036367 := bstep (se 1 (by rfl) ⟨3027275, by rfl⟩ : syracuseStep 4036367 = 6054551) B6054551
theorem B2690911 : Blo 2125435 2690911 := bstep (se 1 (by rfl) ⟨2018183, by rfl⟩ : syracuseStep 2690911 = 4036367) B4036367
theorem B3587881 : Blo 2125435 3587881 := bstep (se 2 (by rfl) ⟨1345455, by rfl⟩ : syracuseStep 3587881 = 2690911) B2690911
theorem B4783841 : Blo 2125435 4783841 := bstep (se 2 (by rfl) ⟨1793940, by rfl⟩ : syracuseStep 4783841 = 3587881) B3587881
theorem B3189227 : Blo 2125435 3189227 := bstep (se 1 (by rfl) ⟨2391920, by rfl⟩ : syracuseStep 3189227 = 4783841) B4783841
theorem B2126151 : Blo 2125435 2126151 := bstep (se 1 (by rfl) ⟨1594613, by rfl⟩ : syracuseStep 2126151 = 3189227) B3189227
theorem B2391925 : Blo 2125435 2391925 := bbase (se 5 (by rfl) ⟨112121, by rfl⟩ : syracuseStep 2391925 = 224243) (by norm_num)
theorem B3189233 : Blo 2125435 3189233 := bstep (se 2 (by rfl) ⟨1195962, by rfl⟩ : syracuseStep 3189233 = 2391925) B2391925
theorem B2126155 : Blo 2125435 2126155 := bstep (se 1 (by rfl) ⟨1594616, by rfl⟩ : syracuseStep 2126155 = 3189233) B3189233
theorem B2690921 : Blo 2125435 2690921 := bbase (se 2 (by rfl) ⟨1009095, by rfl⟩ : syracuseStep 2690921 = 2018191) (by norm_num)
theorem B7175789 : Blo 2125435 7175789 := bstep (se 3 (by rfl) ⟨1345460, by rfl⟩ : syracuseStep 7175789 = 2690921) B2690921
theorem B4783859 : Blo 2125435 4783859 := bstep (se 1 (by rfl) ⟨3587894, by rfl⟩ : syracuseStep 4783859 = 7175789) B7175789
theorem B3189239 : Blo 2125435 3189239 := bstep (se 1 (by rfl) ⟨2391929, by rfl⟩ : syracuseStep 3189239 = 4783859) B4783859
theorem B2126159 : Blo 2125435 2126159 := bstep (se 1 (by rfl) ⟨1594619, by rfl⟩ : syracuseStep 2126159 = 3189239) B3189239
theorem B3189245 : Blo 2125435 3189245 := bbase (se 3 (by rfl) ⟨597983, by rfl⟩ : syracuseStep 3189245 = 1195967) (by norm_num)
theorem B2126163 : Blo 2125435 2126163 := bstep (se 1 (by rfl) ⟨1594622, by rfl⟩ : syracuseStep 2126163 = 3189245) B3189245
theorem B4783877 : Blo 2125435 4783877 := bbase (se 4 (by rfl) ⟨448488, by rfl⟩ : syracuseStep 4783877 = 896977) (by norm_num)
theorem B3189251 : Blo 2125435 3189251 := bstep (se 1 (by rfl) ⟨2391938, by rfl⟩ : syracuseStep 3189251 = 4783877) B4783877
theorem B2126167 : Blo 2125435 2126167 := bstep (se 1 (by rfl) ⟨1594625, by rfl⟩ : syracuseStep 2126167 = 3189251) B3189251
theorem B4036405 : Blo 2125435 4036405 := bbase (se 5 (by rfl) ⟨189206, by rfl⟩ : syracuseStep 4036405 = 378413) (by norm_num)
theorem B5381873 : Blo 2125435 5381873 := bstep (se 2 (by rfl) ⟨2018202, by rfl⟩ : syracuseStep 5381873 = 4036405) B4036405
theorem B3587915 : Blo 2125435 3587915 := bstep (se 1 (by rfl) ⟨2690936, by rfl⟩ : syracuseStep 3587915 = 5381873) B5381873
theorem B2391943 : Blo 2125435 2391943 := bstep (se 1 (by rfl) ⟨1793957, by rfl⟩ : syracuseStep 2391943 = 3587915) B3587915
theorem B3189257 : Blo 2125435 3189257 := bstep (se 2 (by rfl) ⟨1195971, by rfl⟩ : syracuseStep 3189257 = 2391943) B2391943
theorem B2126171 : Blo 2125435 2126171 := bstep (se 1 (by rfl) ⟨1594628, by rfl⟩ : syracuseStep 2126171 = 3189257) B3189257
theorem B10763765 : Blo 2125435 10763765 := bbase (se 5 (by rfl) ⟨504551, by rfl⟩ : syracuseStep 10763765 = 1009103) (by norm_num)
theorem B7175843 : Blo 2125435 7175843 := bstep (se 1 (by rfl) ⟨5381882, by rfl⟩ : syracuseStep 7175843 = 10763765) B10763765
theorem B4783895 : Blo 2125435 4783895 := bstep (se 1 (by rfl) ⟨3587921, by rfl⟩ : syracuseStep 4783895 = 7175843) B7175843
theorem B3189263 : Blo 2125435 3189263 := bstep (se 1 (by rfl) ⟨2391947, by rfl⟩ : syracuseStep 3189263 = 4783895) B4783895
theorem B2126175 : Blo 2125435 2126175 := bstep (se 1 (by rfl) ⟨1594631, by rfl⟩ : syracuseStep 2126175 = 3189263) B3189263
theorem B3189269 : Blo 2125435 3189269 := bbase (se 6 (by rfl) ⟨74748, by rfl⟩ : syracuseStep 3189269 = 149497) (by norm_num)
theorem B2126179 : Blo 2125435 2126179 := bstep (se 1 (by rfl) ⟨1594634, by rfl⟩ : syracuseStep 2126179 = 3189269) B3189269
theorem B18163925 : Blo 2125435 18163925 := bbase (se 7 (by rfl) ⟨212858, by rfl⟩ : syracuseStep 18163925 = 425717) (by norm_num)
theorem B12109283 : Blo 2125435 12109283 := bstep (se 1 (by rfl) ⟨9081962, by rfl⟩ : syracuseStep 12109283 = 18163925) B18163925
theorem B8072855 : Blo 2125435 8072855 := bstep (se 1 (by rfl) ⟨6054641, by rfl⟩ : syracuseStep 8072855 = 12109283) B12109283
theorem B5381903 : Blo 2125435 5381903 := bstep (se 1 (by rfl) ⟨4036427, by rfl⟩ : syracuseStep 5381903 = 8072855) B8072855
theorem B3587935 : Blo 2125435 3587935 := bstep (se 1 (by rfl) ⟨2690951, by rfl⟩ : syracuseStep 3587935 = 5381903) B5381903
theorem B4783913 : Blo 2125435 4783913 := bstep (se 2 (by rfl) ⟨1793967, by rfl⟩ : syracuseStep 4783913 = 3587935) B3587935
theorem B3189275 : Blo 2125435 3189275 := bstep (se 1 (by rfl) ⟨2391956, by rfl⟩ : syracuseStep 3189275 = 4783913) B4783913
theorem B2126183 : Blo 2125435 2126183 := bstep (se 1 (by rfl) ⟨1594637, by rfl⟩ : syracuseStep 2126183 = 3189275) B3189275
theorem B2391961 : Blo 2125435 2391961 := bbase (se 2 (by rfl) ⟨896985, by rfl⟩ : syracuseStep 2391961 = 1793971) (by norm_num)
theorem B3189281 : Blo 2125435 3189281 := bstep (se 2 (by rfl) ⟨1195980, by rfl⟩ : syracuseStep 3189281 = 2391961) B2391961
theorem B2126187 : Blo 2125435 2126187 := bstep (se 1 (by rfl) ⟨1594640, by rfl⟩ : syracuseStep 2126187 = 3189281) B3189281
theorem B8072885 : Blo 2125435 8072885 := bbase (se 5 (by rfl) ⟨378416, by rfl⟩ : syracuseStep 8072885 = 756833) (by norm_num)
theorem B5381923 : Blo 2125435 5381923 := bstep (se 1 (by rfl) ⟨4036442, by rfl⟩ : syracuseStep 5381923 = 8072885) B8072885
theorem B7175897 : Blo 2125435 7175897 := bstep (se 2 (by rfl) ⟨2690961, by rfl⟩ : syracuseStep 7175897 = 5381923) B5381923
theorem B4783931 : Blo 2125435 4783931 := bstep (se 1 (by rfl) ⟨3587948, by rfl⟩ : syracuseStep 4783931 = 7175897) B7175897
theorem B3189287 : Blo 2125435 3189287 := bstep (se 1 (by rfl) ⟨2391965, by rfl⟩ : syracuseStep 3189287 = 4783931) B4783931
theorem B2126191 : Blo 2125435 2126191 := bstep (se 1 (by rfl) ⟨1594643, by rfl⟩ : syracuseStep 2126191 = 3189287) B3189287
theorem B3189293 : Blo 2125435 3189293 := bbase (se 3 (by rfl) ⟨597992, by rfl⟩ : syracuseStep 3189293 = 1195985) (by norm_num)
theorem B2126195 : Blo 2125435 2126195 := bstep (se 1 (by rfl) ⟨1594646, by rfl⟩ : syracuseStep 2126195 = 3189293) B3189293
theorem B4783949 : Blo 2125435 4783949 := bbase (se 3 (by rfl) ⟨896990, by rfl⟩ : syracuseStep 4783949 = 1793981) (by norm_num)
theorem B3189299 : Blo 2125435 3189299 := bstep (se 1 (by rfl) ⟨2391974, by rfl⟩ : syracuseStep 3189299 = 4783949) B4783949
theorem B2126199 : Blo 2125435 2126199 := bstep (se 1 (by rfl) ⟨1594649, by rfl⟩ : syracuseStep 2126199 = 3189299) B3189299
theorem B2690977 : Blo 2125435 2690977 := bbase (se 2 (by rfl) ⟨1009116, by rfl⟩ : syracuseStep 2690977 = 2018233) (by norm_num)
theorem B3587969 : Blo 2125435 3587969 := bstep (se 2 (by rfl) ⟨1345488, by rfl⟩ : syracuseStep 3587969 = 2690977) B2690977
theorem B2391979 : Blo 2125435 2391979 := bstep (se 1 (by rfl) ⟨1793984, by rfl⟩ : syracuseStep 2391979 = 3587969) B3587969
theorem B3189305 : Blo 2125435 3189305 := bstep (se 2 (by rfl) ⟨1195989, by rfl⟩ : syracuseStep 3189305 = 2391979) B2391979
theorem B2126203 : Blo 2125435 2126203 := bstep (se 1 (by rfl) ⟨1594652, by rfl⟩ : syracuseStep 2126203 = 3189305) B3189305
theorem B24218837 : Blo 2125435 24218837 := bbase (se 7 (by rfl) ⟨283814, by rfl⟩ : syracuseStep 24218837 = 567629) (by norm_num)
theorem B16145891 : Blo 2125435 16145891 := bstep (se 1 (by rfl) ⟨12109418, by rfl⟩ : syracuseStep 16145891 = 24218837) B24218837
theorem B10763927 : Blo 2125435 10763927 := bstep (se 1 (by rfl) ⟨8072945, by rfl⟩ : syracuseStep 10763927 = 16145891) B16145891
theorem B7175951 : Blo 2125435 7175951 := bstep (se 1 (by rfl) ⟨5381963, by rfl⟩ : syracuseStep 7175951 = 10763927) B10763927
theorem B4783967 : Blo 2125435 4783967 := bstep (se 1 (by rfl) ⟨3587975, by rfl⟩ : syracuseStep 4783967 = 7175951) B7175951
theorem B3189311 : Blo 2125435 3189311 := bstep (se 1 (by rfl) ⟨2391983, by rfl⟩ : syracuseStep 3189311 = 4783967) B4783967
theorem B2126207 : Blo 2125435 2126207 := bstep (se 1 (by rfl) ⟨1594655, by rfl⟩ : syracuseStep 2126207 = 3189311) B3189311
theorem B3189317 : Blo 2125435 3189317 := bbase (se 4 (by rfl) ⟨298998, by rfl⟩ : syracuseStep 3189317 = 597997) (by norm_num)
theorem B2126211 : Blo 2125435 2126211 := bstep (se 1 (by rfl) ⟨1594658, by rfl⟩ : syracuseStep 2126211 = 3189317) B3189317
theorem B3587989 : Blo 2125435 3587989 := bbase (se 6 (by rfl) ⟨84093, by rfl⟩ : syracuseStep 3587989 = 168187) (by norm_num)
theorem B4783985 : Blo 2125435 4783985 := bstep (se 2 (by rfl) ⟨1793994, by rfl⟩ : syracuseStep 4783985 = 3587989) B3587989
theorem B3189323 : Blo 2125435 3189323 := bstep (se 1 (by rfl) ⟨2391992, by rfl⟩ : syracuseStep 3189323 = 4783985) B4783985
theorem B2126215 : Blo 2125435 2126215 := bstep (se 1 (by rfl) ⟨1594661, by rfl⟩ : syracuseStep 2126215 = 3189323) B3189323
theorem B2391997 : Blo 2125435 2391997 := bbase (se 3 (by rfl) ⟨448499, by rfl⟩ : syracuseStep 2391997 = 896999) (by norm_num)
theorem B3189329 : Blo 2125435 3189329 := bstep (se 2 (by rfl) ⟨1195998, by rfl⟩ : syracuseStep 3189329 = 2391997) B2391997
theorem B2126219 : Blo 2125435 2126219 := bstep (se 1 (by rfl) ⟨1594664, by rfl⟩ : syracuseStep 2126219 = 3189329) B3189329
theorem B7176005 : Blo 2125435 7176005 := bbase (se 4 (by rfl) ⟨672750, by rfl⟩ : syracuseStep 7176005 = 1345501) (by norm_num)
theorem B4784003 : Blo 2125435 4784003 := bstep (se 1 (by rfl) ⟨3588002, by rfl⟩ : syracuseStep 4784003 = 7176005) B7176005
theorem B3189335 : Blo 2125435 3189335 := bstep (se 1 (by rfl) ⟨2392001, by rfl⟩ : syracuseStep 3189335 = 4784003) B4784003
theorem B2126223 : Blo 2125435 2126223 := bstep (se 1 (by rfl) ⟨1594667, by rfl⟩ : syracuseStep 2126223 = 3189335) B3189335
theorem B3189341 : Blo 2125435 3189341 := bbase (se 3 (by rfl) ⟨598001, by rfl⟩ : syracuseStep 3189341 = 1196003) (by norm_num)
theorem B2126227 : Blo 2125435 2126227 := bstep (se 1 (by rfl) ⟨1594670, by rfl⟩ : syracuseStep 2126227 = 3189341) B3189341
theorem B4784021 : Blo 2125435 4784021 := bbase (se 6 (by rfl) ⟨112125, by rfl⟩ : syracuseStep 4784021 = 224251) (by norm_num)
theorem B3189347 : Blo 2125435 3189347 := bstep (se 1 (by rfl) ⟨2392010, by rfl⟩ : syracuseStep 3189347 = 4784021) B4784021
theorem B2126231 : Blo 2125435 2126231 := bstep (se 1 (by rfl) ⟨1594673, by rfl⟩ : syracuseStep 2126231 = 3189347) B3189347
theorem B4541093 : Blo 2125435 4541093 := bbase (se 4 (by rfl) ⟨425727, by rfl⟩ : syracuseStep 4541093 = 851455) (by norm_num)
theorem B3027395 : Blo 2125435 3027395 := bstep (se 1 (by rfl) ⟨2270546, by rfl⟩ : syracuseStep 3027395 = 4541093) B4541093
theorem B8073053 : Blo 2125435 8073053 := bstep (se 3 (by rfl) ⟨1513697, by rfl⟩ : syracuseStep 8073053 = 3027395) B3027395
theorem B5382035 : Blo 2125435 5382035 := bstep (se 1 (by rfl) ⟨4036526, by rfl⟩ : syracuseStep 5382035 = 8073053) B8073053
theorem B3588023 : Blo 2125435 3588023 := bstep (se 1 (by rfl) ⟨2691017, by rfl⟩ : syracuseStep 3588023 = 5382035) B5382035
theorem B2392015 : Blo 2125435 2392015 := bstep (se 1 (by rfl) ⟨1794011, by rfl⟩ : syracuseStep 2392015 = 3588023) B3588023
theorem B3189353 : Blo 2125435 3189353 := bstep (se 2 (by rfl) ⟨1196007, by rfl⟩ : syracuseStep 3189353 = 2392015) B2392015
theorem B2126235 : Blo 2125435 2126235 := bstep (se 1 (by rfl) ⟨1594676, by rfl⟩ : syracuseStep 2126235 = 3189353) B3189353
theorem B10217477 : Blo 2125435 10217477 := bbase (se 4 (by rfl) ⟨957888, by rfl⟩ : syracuseStep 10217477 = 1915777) (by norm_num)
theorem B6811651 : Blo 2125435 6811651 := bstep (se 1 (by rfl) ⟨5108738, by rfl⟩ : syracuseStep 6811651 = 10217477) B10217477
theorem B9082201 : Blo 2125435 9082201 := bstep (se 2 (by rfl) ⟨3405825, by rfl⟩ : syracuseStep 9082201 = 6811651) B6811651
theorem B12109601 : Blo 2125435 12109601 := bstep (se 2 (by rfl) ⟨4541100, by rfl⟩ : syracuseStep 12109601 = 9082201) B9082201
theorem B8073067 : Blo 2125435 8073067 := bstep (se 1 (by rfl) ⟨6054800, by rfl⟩ : syracuseStep 8073067 = 12109601) B12109601
theorem B10764089 : Blo 2125435 10764089 := bstep (se 2 (by rfl) ⟨4036533, by rfl⟩ : syracuseStep 10764089 = 8073067) B8073067
theorem B7176059 : Blo 2125435 7176059 := bstep (se 1 (by rfl) ⟨5382044, by rfl⟩ : syracuseStep 7176059 = 10764089) B10764089
theorem B4784039 : Blo 2125435 4784039 := bstep (se 1 (by rfl) ⟨3588029, by rfl⟩ : syracuseStep 4784039 = 7176059) B7176059
theorem B3189359 : Blo 2125435 3189359 := bstep (se 1 (by rfl) ⟨2392019, by rfl⟩ : syracuseStep 3189359 = 4784039) B4784039
theorem B2126239 : Blo 2125435 2126239 := bstep (se 1 (by rfl) ⟨1594679, by rfl⟩ : syracuseStep 2126239 = 3189359) B3189359
theorem B3189365 : Blo 2125435 3189365 := bbase (se 5 (by rfl) ⟨149501, by rfl⟩ : syracuseStep 3189365 = 299003) (by norm_num)
theorem B2126243 : Blo 2125435 2126243 := bstep (se 1 (by rfl) ⟨1594682, by rfl⟩ : syracuseStep 2126243 = 3189365) B3189365
theorem B4036549 : Blo 2125435 4036549 := bbase (se 4 (by rfl) ⟨378426, by rfl⟩ : syracuseStep 4036549 = 756853) (by norm_num)
theorem B5382065 : Blo 2125435 5382065 := bstep (se 2 (by rfl) ⟨2018274, by rfl⟩ : syracuseStep 5382065 = 4036549) B4036549
theorem B3588043 : Blo 2125435 3588043 := bstep (se 1 (by rfl) ⟨2691032, by rfl⟩ : syracuseStep 3588043 = 5382065) B5382065
theorem B4784057 : Blo 2125435 4784057 := bstep (se 2 (by rfl) ⟨1794021, by rfl⟩ : syracuseStep 4784057 = 3588043) B3588043
theorem B3189371 : Blo 2125435 3189371 := bstep (se 1 (by rfl) ⟨2392028, by rfl⟩ : syracuseStep 3189371 = 4784057) B4784057
theorem B2126247 : Blo 2125435 2126247 := bstep (se 1 (by rfl) ⟨1594685, by rfl⟩ : syracuseStep 2126247 = 3189371) B3189371
theorem B2392033 : Blo 2125435 2392033 := bbase (se 2 (by rfl) ⟨897012, by rfl⟩ : syracuseStep 2392033 = 1794025) (by norm_num)
theorem B3189377 : Blo 2125435 3189377 := bstep (se 2 (by rfl) ⟨1196016, by rfl⟩ : syracuseStep 3189377 = 2392033) B2392033
theorem B2126251 : Blo 2125435 2126251 := bstep (se 1 (by rfl) ⟨1594688, by rfl⟩ : syracuseStep 2126251 = 3189377) B3189377
theorem B5382085 : Blo 2125435 5382085 := bbase (se 4 (by rfl) ⟨504570, by rfl⟩ : syracuseStep 5382085 = 1009141) (by norm_num)
theorem B7176113 : Blo 2125435 7176113 := bstep (se 2 (by rfl) ⟨2691042, by rfl⟩ : syracuseStep 7176113 = 5382085) B5382085
theorem B4784075 : Blo 2125435 4784075 := bstep (se 1 (by rfl) ⟨3588056, by rfl⟩ : syracuseStep 4784075 = 7176113) B7176113
theorem B3189383 : Blo 2125435 3189383 := bstep (se 1 (by rfl) ⟨2392037, by rfl⟩ : syracuseStep 3189383 = 4784075) B4784075
theorem B2126255 : Blo 2125435 2126255 := bstep (se 1 (by rfl) ⟨1594691, by rfl⟩ : syracuseStep 2126255 = 3189383) B3189383
theorem B3189389 : Blo 2125435 3189389 := bbase (se 3 (by rfl) ⟨598010, by rfl⟩ : syracuseStep 3189389 = 1196021) (by norm_num)
theorem B2126259 : Blo 2125435 2126259 := bstep (se 1 (by rfl) ⟨1594694, by rfl⟩ : syracuseStep 2126259 = 3189389) B3189389
theorem B4784093 : Blo 2125435 4784093 := bbase (se 3 (by rfl) ⟨897017, by rfl⟩ : syracuseStep 4784093 = 1794035) (by norm_num)
theorem B3189395 : Blo 2125435 3189395 := bstep (se 1 (by rfl) ⟨2392046, by rfl⟩ : syracuseStep 3189395 = 4784093) B4784093
theorem B2126263 : Blo 2125435 2126263 := bstep (se 1 (by rfl) ⟨1594697, by rfl⟩ : syracuseStep 2126263 = 3189395) B3189395
theorem B3588077 : Blo 2125435 3588077 := bbase (se 3 (by rfl) ⟨672764, by rfl⟩ : syracuseStep 3588077 = 1345529) (by norm_num)
theorem B2392051 : Blo 2125435 2392051 := bstep (se 1 (by rfl) ⟨1794038, by rfl⟩ : syracuseStep 2392051 = 3588077) B3588077
theorem B3189401 : Blo 2125435 3189401 := bstep (se 2 (by rfl) ⟨1196025, by rfl⟩ : syracuseStep 3189401 = 2392051) B2392051
theorem B2126267 : Blo 2125435 2126267 := bstep (se 1 (by rfl) ⟨1594700, by rfl⟩ : syracuseStep 2126267 = 3189401) B3189401
theorem B6465845 : Blo 2125435 6465845 := bbase (se 5 (by rfl) ⟨303086, by rfl⟩ : syracuseStep 6465845 = 606173) (by norm_num)
theorem B17242253 : Blo 2125435 17242253 := bstep (se 3 (by rfl) ⟨3232922, by rfl⟩ : syracuseStep 17242253 = 6465845) B6465845
theorem B11494835 : Blo 2125435 11494835 := bstep (se 1 (by rfl) ⟨8621126, by rfl⟩ : syracuseStep 11494835 = 17242253) B17242253
theorem B7663223 : Blo 2125435 7663223 := bstep (se 1 (by rfl) ⟨5747417, by rfl⟩ : syracuseStep 7663223 = 11494835) B11494835
theorem B5108815 : Blo 2125435 5108815 := bstep (se 1 (by rfl) ⟨3831611, by rfl⟩ : syracuseStep 5108815 = 7663223) B7663223
theorem B27247013 : Blo 2125435 27247013 := bstep (se 4 (by rfl) ⟨2554407, by rfl⟩ : syracuseStep 27247013 = 5108815) B5108815
theorem B18164675 : Blo 2125435 18164675 := bstep (se 1 (by rfl) ⟨13623506, by rfl⟩ : syracuseStep 18164675 = 27247013) B27247013
theorem B12109783 : Blo 2125435 12109783 := bstep (se 1 (by rfl) ⟨9082337, by rfl⟩ : syracuseStep 12109783 = 18164675) B18164675
theorem B16146377 : Blo 2125435 16146377 := bstep (se 2 (by rfl) ⟨6054891, by rfl⟩ : syracuseStep 16146377 = 12109783) B12109783
theorem B10764251 : Blo 2125435 10764251 := bstep (se 1 (by rfl) ⟨8073188, by rfl⟩ : syracuseStep 10764251 = 16146377) B16146377
theorem B7176167 : Blo 2125435 7176167 := bstep (se 1 (by rfl) ⟨5382125, by rfl⟩ : syracuseStep 7176167 = 10764251) B10764251
theorem B4784111 : Blo 2125435 4784111 := bstep (se 1 (by rfl) ⟨3588083, by rfl⟩ : syracuseStep 4784111 = 7176167) B7176167
theorem B3189407 : Blo 2125435 3189407 := bstep (se 1 (by rfl) ⟨2392055, by rfl⟩ : syracuseStep 3189407 = 4784111) B4784111
theorem B2126271 : Blo 2125435 2126271 := bstep (se 1 (by rfl) ⟨1594703, by rfl⟩ : syracuseStep 2126271 = 3189407) B3189407
theorem B3189413 : Blo 2125435 3189413 := bbase (se 4 (by rfl) ⟨299007, by rfl⟩ : syracuseStep 3189413 = 598015) (by norm_num)
theorem B2126275 : Blo 2125435 2126275 := bstep (se 1 (by rfl) ⟨1594706, by rfl⟩ : syracuseStep 2126275 = 3189413) B3189413
theorem B2691073 : Blo 2125435 2691073 := bbase (se 2 (by rfl) ⟨1009152, by rfl⟩ : syracuseStep 2691073 = 2018305) (by norm_num)
theorem B3588097 : Blo 2125435 3588097 := bstep (se 2 (by rfl) ⟨1345536, by rfl⟩ : syracuseStep 3588097 = 2691073) B2691073
theorem B4784129 : Blo 2125435 4784129 := bstep (se 2 (by rfl) ⟨1794048, by rfl⟩ : syracuseStep 4784129 = 3588097) B3588097
theorem B3189419 : Blo 2125435 3189419 := bstep (se 1 (by rfl) ⟨2392064, by rfl⟩ : syracuseStep 3189419 = 4784129) B4784129
theorem B2126279 : Blo 2125435 2126279 := bstep (se 1 (by rfl) ⟨1594709, by rfl⟩ : syracuseStep 2126279 = 3189419) B3189419
theorem B2392069 : Blo 2125435 2392069 := bbase (se 4 (by rfl) ⟨224256, by rfl⟩ : syracuseStep 2392069 = 448513) (by norm_num)
theorem B3189425 : Blo 2125435 3189425 := bstep (se 2 (by rfl) ⟨1196034, by rfl⟩ : syracuseStep 3189425 = 2392069) B2392069
theorem B2126283 : Blo 2125435 2126283 := bstep (se 1 (by rfl) ⟨1594712, by rfl⟩ : syracuseStep 2126283 = 3189425) B3189425
theorem B3027469 : Blo 2125435 3027469 := bbase (se 3 (by rfl) ⟨567650, by rfl⟩ : syracuseStep 3027469 = 1135301) (by norm_num)
theorem B4036625 : Blo 2125435 4036625 := bstep (se 2 (by rfl) ⟨1513734, by rfl⟩ : syracuseStep 4036625 = 3027469) B3027469
theorem B2691083 : Blo 2125435 2691083 := bstep (se 1 (by rfl) ⟨2018312, by rfl⟩ : syracuseStep 2691083 = 4036625) B4036625
theorem B7176221 : Blo 2125435 7176221 := bstep (se 3 (by rfl) ⟨1345541, by rfl⟩ : syracuseStep 7176221 = 2691083) B2691083
theorem B4784147 : Blo 2125435 4784147 := bstep (se 1 (by rfl) ⟨3588110, by rfl⟩ : syracuseStep 4784147 = 7176221) B7176221
theorem B3189431 : Blo 2125435 3189431 := bstep (se 1 (by rfl) ⟨2392073, by rfl⟩ : syracuseStep 3189431 = 4784147) B4784147
theorem B2126287 : Blo 2125435 2126287 := bstep (se 1 (by rfl) ⟨1594715, by rfl⟩ : syracuseStep 2126287 = 3189431) B3189431
theorem B3189437 : Blo 2125435 3189437 := bbase (se 3 (by rfl) ⟨598019, by rfl⟩ : syracuseStep 3189437 = 1196039) (by norm_num)
theorem B2126291 : Blo 2125435 2126291 := bstep (se 1 (by rfl) ⟨1594718, by rfl⟩ : syracuseStep 2126291 = 3189437) B3189437
theorem B4784165 : Blo 2125435 4784165 := bbase (se 4 (by rfl) ⟨448515, by rfl⟩ : syracuseStep 4784165 = 897031) (by norm_num)
theorem B3189443 : Blo 2125435 3189443 := bstep (se 1 (by rfl) ⟨2392082, by rfl⟩ : syracuseStep 3189443 = 4784165) B4784165
theorem B2126295 : Blo 2125435 2126295 := bstep (se 1 (by rfl) ⟨1594721, by rfl⟩ : syracuseStep 2126295 = 3189443) B3189443
theorem B5382197 : Blo 2125435 5382197 := bbase (se 5 (by rfl) ⟨252290, by rfl⟩ : syracuseStep 5382197 = 504581) (by norm_num)
theorem B3588131 : Blo 2125435 3588131 := bstep (se 1 (by rfl) ⟨2691098, by rfl⟩ : syracuseStep 3588131 = 5382197) B5382197
theorem B2392087 : Blo 2125435 2392087 := bstep (se 1 (by rfl) ⟨1794065, by rfl⟩ : syracuseStep 2392087 = 3588131) B3588131
theorem B3189449 : Blo 2125435 3189449 := bstep (se 2 (by rfl) ⟨1196043, by rfl⟩ : syracuseStep 3189449 = 2392087) B2392087
theorem B2126299 : Blo 2125435 2126299 := bstep (se 1 (by rfl) ⟨1594724, by rfl⟩ : syracuseStep 2126299 = 3189449) B3189449
theorem B14548373 : Blo 2125435 14548373 := bbase (se 6 (by rfl) ⟨340977, by rfl⟩ : syracuseStep 14548373 = 681955) (by norm_num)
theorem B9698915 : Blo 2125435 9698915 := bstep (se 1 (by rfl) ⟨7274186, by rfl⟩ : syracuseStep 9698915 = 14548373) B14548373
theorem B6465943 : Blo 2125435 6465943 := bstep (se 1 (by rfl) ⟨4849457, by rfl⟩ : syracuseStep 6465943 = 9698915) B9698915
theorem B8621257 : Blo 2125435 8621257 := bstep (se 2 (by rfl) ⟨3232971, by rfl⟩ : syracuseStep 8621257 = 6465943) B6465943
theorem B11495009 : Blo 2125435 11495009 := bstep (se 2 (by rfl) ⟨4310628, by rfl⟩ : syracuseStep 11495009 = 8621257) B8621257
theorem B7663339 : Blo 2125435 7663339 := bstep (se 1 (by rfl) ⟨5747504, by rfl⟩ : syracuseStep 7663339 = 11495009) B11495009
theorem B10217785 : Blo 2125435 10217785 := bstep (se 2 (by rfl) ⟨3831669, by rfl⟩ : syracuseStep 10217785 = 7663339) B7663339
theorem B13623713 : Blo 2125435 13623713 := bstep (se 2 (by rfl) ⟨5108892, by rfl⟩ : syracuseStep 13623713 = 10217785) B10217785
theorem B9082475 : Blo 2125435 9082475 := bstep (se 1 (by rfl) ⟨6811856, by rfl⟩ : syracuseStep 9082475 = 13623713) B13623713
theorem B6054983 : Blo 2125435 6054983 := bstep (se 1 (by rfl) ⟨4541237, by rfl⟩ : syracuseStep 6054983 = 9082475) B9082475
theorem B4036655 : Blo 2125435 4036655 := bstep (se 1 (by rfl) ⟨3027491, by rfl⟩ : syracuseStep 4036655 = 6054983) B6054983
theorem B10764413 : Blo 2125435 10764413 := bstep (se 3 (by rfl) ⟨2018327, by rfl⟩ : syracuseStep 10764413 = 4036655) B4036655
theorem B7176275 : Blo 2125435 7176275 := bstep (se 1 (by rfl) ⟨5382206, by rfl⟩ : syracuseStep 7176275 = 10764413) B10764413
theorem B4784183 : Blo 2125435 4784183 := bstep (se 1 (by rfl) ⟨3588137, by rfl⟩ : syracuseStep 4784183 = 7176275) B7176275
theorem B3189455 : Blo 2125435 3189455 := bstep (se 1 (by rfl) ⟨2392091, by rfl⟩ : syracuseStep 3189455 = 4784183) B4784183
theorem B2126303 : Blo 2125435 2126303 := bstep (se 1 (by rfl) ⟨1594727, by rfl⟩ : syracuseStep 2126303 = 3189455) B3189455
theorem B3189461 : Blo 2125435 3189461 := bbase (se 7 (by rfl) ⟨37376, by rfl⟩ : syracuseStep 3189461 = 74753) (by norm_num)
theorem B2126307 : Blo 2125435 2126307 := bstep (se 1 (by rfl) ⟨1594730, by rfl⟩ : syracuseStep 2126307 = 3189461) B3189461
theorem B31071701 : Blo 2125435 31071701 := bbase (se 7 (by rfl) ⟨364121, by rfl⟩ : syracuseStep 31071701 = 728243) (by norm_num)
theorem B20714467 : Blo 2125435 20714467 := bstep (se 1 (by rfl) ⟨15535850, by rfl⟩ : syracuseStep 20714467 = 31071701) B31071701
theorem B27619289 : Blo 2125435 27619289 := bstep (se 2 (by rfl) ⟨10357233, by rfl⟩ : syracuseStep 27619289 = 20714467) B20714467
theorem B18412859 : Blo 2125435 18412859 := bstep (se 1 (by rfl) ⟨13809644, by rfl⟩ : syracuseStep 18412859 = 27619289) B27619289
theorem B12275239 : Blo 2125435 12275239 := bstep (se 1 (by rfl) ⟨9206429, by rfl⟩ : syracuseStep 12275239 = 18412859) B18412859
theorem B16366985 : Blo 2125435 16366985 := bstep (se 2 (by rfl) ⟨6137619, by rfl⟩ : syracuseStep 16366985 = 12275239) B12275239
theorem B10911323 : Blo 2125435 10911323 := bstep (se 1 (by rfl) ⟨8183492, by rfl⟩ : syracuseStep 10911323 = 16366985) B16366985
theorem B7274215 : Blo 2125435 7274215 := bstep (se 1 (by rfl) ⟨5455661, by rfl⟩ : syracuseStep 7274215 = 10911323) B10911323
theorem B9698953 : Blo 2125435 9698953 := bstep (se 2 (by rfl) ⟨3637107, by rfl⟩ : syracuseStep 9698953 = 7274215) B7274215
theorem B12931937 : Blo 2125435 12931937 := bstep (se 2 (by rfl) ⟨4849476, by rfl⟩ : syracuseStep 12931937 = 9698953) B9698953
theorem B8621291 : Blo 2125435 8621291 := bstep (se 1 (by rfl) ⟨6465968, by rfl⟩ : syracuseStep 8621291 = 12931937) B12931937
theorem B5747527 : Blo 2125435 5747527 := bstep (se 1 (by rfl) ⟨4310645, by rfl⟩ : syracuseStep 5747527 = 8621291) B8621291
theorem B7663369 : Blo 2125435 7663369 := bstep (se 2 (by rfl) ⟨2873763, by rfl⟩ : syracuseStep 7663369 = 5747527) B5747527
theorem B10217825 : Blo 2125435 10217825 := bstep (se 2 (by rfl) ⟨3831684, by rfl⟩ : syracuseStep 10217825 = 7663369) B7663369
theorem B6811883 : Blo 2125435 6811883 := bstep (se 1 (by rfl) ⟨5108912, by rfl⟩ : syracuseStep 6811883 = 10217825) B10217825
theorem B4541255 : Blo 2125435 4541255 := bstep (se 1 (by rfl) ⟨3405941, by rfl⟩ : syracuseStep 4541255 = 6811883) B6811883
theorem B3027503 : Blo 2125435 3027503 := bstep (se 1 (by rfl) ⟨2270627, by rfl⟩ : syracuseStep 3027503 = 4541255) B4541255
theorem B8073341 : Blo 2125435 8073341 := bstep (se 3 (by rfl) ⟨1513751, by rfl⟩ : syracuseStep 8073341 = 3027503) B3027503
theorem B5382227 : Blo 2125435 5382227 := bstep (se 1 (by rfl) ⟨4036670, by rfl⟩ : syracuseStep 5382227 = 8073341) B8073341
theorem B3588151 : Blo 2125435 3588151 := bstep (se 1 (by rfl) ⟨2691113, by rfl⟩ : syracuseStep 3588151 = 5382227) B5382227
theorem B4784201 : Blo 2125435 4784201 := bstep (se 2 (by rfl) ⟨1794075, by rfl⟩ : syracuseStep 4784201 = 3588151) B3588151
theorem B3189467 : Blo 2125435 3189467 := bstep (se 1 (by rfl) ⟨2392100, by rfl⟩ : syracuseStep 3189467 = 4784201) B4784201
theorem B2126311 : Blo 2125435 2126311 := bstep (se 1 (by rfl) ⟨1594733, by rfl⟩ : syracuseStep 2126311 = 3189467) B3189467
theorem B2392105 : Blo 2125435 2392105 := bbase (se 2 (by rfl) ⟨897039, by rfl⟩ : syracuseStep 2392105 = 1794079) (by norm_num)
theorem B3189473 : Blo 2125435 3189473 := bstep (se 2 (by rfl) ⟨1196052, by rfl⟩ : syracuseStep 3189473 = 2392105) B2392105
theorem B2126315 : Blo 2125435 2126315 := bstep (se 1 (by rfl) ⟨1594736, by rfl⟩ : syracuseStep 2126315 = 3189473) B3189473
theorem B2184737 : Blo 2125435 2184737 := bbase (se 2 (by rfl) ⟨819276, by rfl⟩ : syracuseStep 2184737 = 1638553) (by norm_num)
theorem B23303861 : Blo 2125435 23303861 := bstep (se 5 (by rfl) ⟨1092368, by rfl⟩ : syracuseStep 23303861 = 2184737) B2184737
theorem B15535907 : Blo 2125435 15535907 := bstep (se 1 (by rfl) ⟨11651930, by rfl⟩ : syracuseStep 15535907 = 23303861) B23303861
theorem B10357271 : Blo 2125435 10357271 := bstep (se 1 (by rfl) ⟨7767953, by rfl⟩ : syracuseStep 10357271 = 15535907) B15535907
theorem B6904847 : Blo 2125435 6904847 := bstep (se 1 (by rfl) ⟨5178635, by rfl⟩ : syracuseStep 6904847 = 10357271) B10357271
theorem B4603231 : Blo 2125435 4603231 := bstep (se 1 (by rfl) ⟨3452423, by rfl⟩ : syracuseStep 4603231 = 6904847) B6904847
theorem B6137641 : Blo 2125435 6137641 := bstep (se 2 (by rfl) ⟨2301615, by rfl⟩ : syracuseStep 6137641 = 4603231) B4603231
theorem B8183521 : Blo 2125435 8183521 := bstep (se 2 (by rfl) ⟨3068820, by rfl⟩ : syracuseStep 8183521 = 6137641) B6137641
theorem B10911361 : Blo 2125435 10911361 := bstep (se 2 (by rfl) ⟨4091760, by rfl⟩ : syracuseStep 10911361 = 8183521) B8183521
theorem B14548481 : Blo 2125435 14548481 := bstep (se 2 (by rfl) ⟨5455680, by rfl⟩ : syracuseStep 14548481 = 10911361) B10911361
theorem B9698987 : Blo 2125435 9698987 := bstep (se 1 (by rfl) ⟨7274240, by rfl⟩ : syracuseStep 9698987 = 14548481) B14548481
theorem B6465991 : Blo 2125435 6465991 := bstep (se 1 (by rfl) ⟨4849493, by rfl⟩ : syracuseStep 6465991 = 9698987) B9698987
theorem B8621321 : Blo 2125435 8621321 := bstep (se 2 (by rfl) ⟨3232995, by rfl⟩ : syracuseStep 8621321 = 6465991) B6465991
theorem B22990189 : Blo 2125435 22990189 := bstep (se 3 (by rfl) ⟨4310660, by rfl⟩ : syracuseStep 22990189 = 8621321) B8621321
theorem B30653585 : Blo 2125435 30653585 := bstep (se 2 (by rfl) ⟨11495094, by rfl⟩ : syracuseStep 30653585 = 22990189) B22990189
theorem B20435723 : Blo 2125435 20435723 := bstep (se 1 (by rfl) ⟨15326792, by rfl⟩ : syracuseStep 20435723 = 30653585) B30653585
theorem B13623815 : Blo 2125435 13623815 := bstep (se 1 (by rfl) ⟨10217861, by rfl⟩ : syracuseStep 13623815 = 20435723) B20435723
theorem B9082543 : Blo 2125435 9082543 := bstep (se 1 (by rfl) ⟨6811907, by rfl⟩ : syracuseStep 9082543 = 13623815) B13623815
theorem B12110057 : Blo 2125435 12110057 := bstep (se 2 (by rfl) ⟨4541271, by rfl⟩ : syracuseStep 12110057 = 9082543) B9082543
theorem B8073371 : Blo 2125435 8073371 := bstep (se 1 (by rfl) ⟨6055028, by rfl⟩ : syracuseStep 8073371 = 12110057) B12110057
theorem B5382247 : Blo 2125435 5382247 := bstep (se 1 (by rfl) ⟨4036685, by rfl⟩ : syracuseStep 5382247 = 8073371) B8073371
theorem B7176329 : Blo 2125435 7176329 := bstep (se 2 (by rfl) ⟨2691123, by rfl⟩ : syracuseStep 7176329 = 5382247) B5382247
theorem B4784219 : Blo 2125435 4784219 := bstep (se 1 (by rfl) ⟨3588164, by rfl⟩ : syracuseStep 4784219 = 7176329) B7176329
theorem B3189479 : Blo 2125435 3189479 := bstep (se 1 (by rfl) ⟨2392109, by rfl⟩ : syracuseStep 3189479 = 4784219) B4784219
theorem B2126319 : Blo 2125435 2126319 := bstep (se 1 (by rfl) ⟨1594739, by rfl⟩ : syracuseStep 2126319 = 3189479) B3189479
theorem B3189485 : Blo 2125435 3189485 := bbase (se 3 (by rfl) ⟨598028, by rfl⟩ : syracuseStep 3189485 = 1196057) (by norm_num)
theorem B2126323 : Blo 2125435 2126323 := bstep (se 1 (by rfl) ⟨1594742, by rfl⟩ : syracuseStep 2126323 = 3189485) B3189485
theorem B4784237 : Blo 2125435 4784237 := bbase (se 3 (by rfl) ⟨897044, by rfl⟩ : syracuseStep 4784237 = 1794089) (by norm_num)
theorem B3189491 : Blo 2125435 3189491 := bstep (se 1 (by rfl) ⟨2392118, by rfl⟩ : syracuseStep 3189491 = 4784237) B4784237
theorem B2126327 : Blo 2125435 2126327 := bstep (se 1 (by rfl) ⟨1594745, by rfl⟩ : syracuseStep 2126327 = 3189491) B3189491
theorem B4036709 : Blo 2125435 4036709 := bbase (se 4 (by rfl) ⟨378441, by rfl⟩ : syracuseStep 4036709 = 756883) (by norm_num)
theorem B2691139 : Blo 2125435 2691139 := bstep (se 1 (by rfl) ⟨2018354, by rfl⟩ : syracuseStep 2691139 = 4036709) B4036709
theorem B3588185 : Blo 2125435 3588185 := bstep (se 2 (by rfl) ⟨1345569, by rfl⟩ : syracuseStep 3588185 = 2691139) B2691139
theorem B2392123 : Blo 2125435 2392123 := bstep (se 1 (by rfl) ⟨1794092, by rfl⟩ : syracuseStep 2392123 = 3588185) B3588185
theorem B3189497 : Blo 2125435 3189497 := bstep (se 2 (by rfl) ⟨1196061, by rfl⟩ : syracuseStep 3189497 = 2392123) B2392123
theorem B2126331 : Blo 2125435 2126331 := bstep (se 1 (by rfl) ⟨1594748, by rfl⟩ : syracuseStep 2126331 = 3189497) B3189497
theorem B4310693 : Blo 2125435 4310693 := bbase (se 4 (by rfl) ⟨404127, by rfl⟩ : syracuseStep 4310693 = 808255) (by norm_num)
theorem B2873795 : Blo 2125435 2873795 := bstep (se 1 (by rfl) ⟨2155346, by rfl⟩ : syracuseStep 2873795 = 4310693) B4310693
theorem B7663453 : Blo 2125435 7663453 := bstep (se 3 (by rfl) ⟨1436897, by rfl⟩ : syracuseStep 7663453 = 2873795) B2873795
theorem B40871749 : Blo 2125435 40871749 := bstep (se 4 (by rfl) ⟨3831726, by rfl⟩ : syracuseStep 40871749 = 7663453) B7663453
theorem B54495665 : Blo 2125435 54495665 := bstep (se 2 (by rfl) ⟨20435874, by rfl⟩ : syracuseStep 54495665 = 40871749) B40871749
theorem B36330443 : Blo 2125435 36330443 := bstep (se 1 (by rfl) ⟨27247832, by rfl⟩ : syracuseStep 36330443 = 54495665) B54495665
theorem B24220295 : Blo 2125435 24220295 := bstep (se 1 (by rfl) ⟨18165221, by rfl⟩ : syracuseStep 24220295 = 36330443) B36330443
theorem B16146863 : Blo 2125435 16146863 := bstep (se 1 (by rfl) ⟨12110147, by rfl⟩ : syracuseStep 16146863 = 24220295) B24220295
theorem B10764575 : Blo 2125435 10764575 := bstep (se 1 (by rfl) ⟨8073431, by rfl⟩ : syracuseStep 10764575 = 16146863) B16146863
theorem B7176383 : Blo 2125435 7176383 := bstep (se 1 (by rfl) ⟨5382287, by rfl⟩ : syracuseStep 7176383 = 10764575) B10764575
theorem B4784255 : Blo 2125435 4784255 := bstep (se 1 (by rfl) ⟨3588191, by rfl⟩ : syracuseStep 4784255 = 7176383) B7176383
theorem B3189503 : Blo 2125435 3189503 := bstep (se 1 (by rfl) ⟨2392127, by rfl⟩ : syracuseStep 3189503 = 4784255) B4784255
theorem B2126335 : Blo 2125435 2126335 := bstep (se 1 (by rfl) ⟨1594751, by rfl⟩ : syracuseStep 2126335 = 3189503) B3189503
theorem B3189509 : Blo 2125435 3189509 := bbase (se 4 (by rfl) ⟨299016, by rfl⟩ : syracuseStep 3189509 = 598033) (by norm_num)
theorem B2126339 : Blo 2125435 2126339 := bstep (se 1 (by rfl) ⟨1594754, by rfl⟩ : syracuseStep 2126339 = 3189509) B3189509
theorem B3588205 : Blo 2125435 3588205 := bbase (se 3 (by rfl) ⟨672788, by rfl⟩ : syracuseStep 3588205 = 1345577) (by norm_num)
theorem B4784273 : Blo 2125435 4784273 := bstep (se 2 (by rfl) ⟨1794102, by rfl⟩ : syracuseStep 4784273 = 3588205) B3588205
theorem B3189515 : Blo 2125435 3189515 := bstep (se 1 (by rfl) ⟨2392136, by rfl⟩ : syracuseStep 3189515 = 4784273) B4784273
theorem B2126343 : Blo 2125435 2126343 := bstep (se 1 (by rfl) ⟨1594757, by rfl⟩ : syracuseStep 2126343 = 3189515) B3189515
theorem B2392141 : Blo 2125435 2392141 := bbase (se 3 (by rfl) ⟨448526, by rfl⟩ : syracuseStep 2392141 = 897053) (by norm_num)
theorem B3189521 : Blo 2125435 3189521 := bstep (se 2 (by rfl) ⟨1196070, by rfl⟩ : syracuseStep 3189521 = 2392141) B2392141
theorem B2126347 : Blo 2125435 2126347 := bstep (se 1 (by rfl) ⟨1594760, by rfl⟩ : syracuseStep 2126347 = 3189521) B3189521
theorem B7176437 : Blo 2125435 7176437 := bbase (se 5 (by rfl) ⟨336395, by rfl⟩ : syracuseStep 7176437 = 672791) (by norm_num)
theorem B4784291 : Blo 2125435 4784291 := bstep (se 1 (by rfl) ⟨3588218, by rfl⟩ : syracuseStep 4784291 = 7176437) B7176437
theorem B3189527 : Blo 2125435 3189527 := bstep (se 1 (by rfl) ⟨2392145, by rfl⟩ : syracuseStep 3189527 = 4784291) B4784291
theorem B2126351 : Blo 2125435 2126351 := bstep (se 1 (by rfl) ⟨1594763, by rfl⟩ : syracuseStep 2126351 = 3189527) B3189527
theorem B3189533 : Blo 2125435 3189533 := bbase (se 3 (by rfl) ⟨598037, by rfl⟩ : syracuseStep 3189533 = 1196075) (by norm_num)
theorem B2126355 : Blo 2125435 2126355 := bstep (se 1 (by rfl) ⟨1594766, by rfl⟩ : syracuseStep 2126355 = 3189533) B3189533
theorem B4784309 : Blo 2125435 4784309 := bbase (se 5 (by rfl) ⟨224264, by rfl⟩ : syracuseStep 4784309 = 448529) (by norm_num)
theorem B3189539 : Blo 2125435 3189539 := bstep (se 1 (by rfl) ⟨2392154, by rfl⟩ : syracuseStep 3189539 = 4784309) B4784309
theorem B2126359 : Blo 2125435 2126359 := bstep (se 1 (by rfl) ⟨1594769, by rfl⟩ : syracuseStep 2126359 = 3189539) B3189539
theorem B5747669 : Blo 2125435 5747669 := bbase (se 7 (by rfl) ⟨67355, by rfl⟩ : syracuseStep 5747669 = 134711) (by norm_num)
theorem B3831779 : Blo 2125435 3831779 := bstep (se 1 (by rfl) ⟨2873834, by rfl⟩ : syracuseStep 3831779 = 5747669) B5747669
theorem B2554519 : Blo 2125435 2554519 := bstep (se 1 (by rfl) ⟨1915889, by rfl⟩ : syracuseStep 2554519 = 3831779) B3831779
theorem B3406025 : Blo 2125435 3406025 := bstep (se 2 (by rfl) ⟨1277259, by rfl⟩ : syracuseStep 3406025 = 2554519) B2554519
theorem B2270683 : Blo 2125435 2270683 := bstep (se 1 (by rfl) ⟨1703012, by rfl⟩ : syracuseStep 2270683 = 3406025) B3406025
theorem B12110309 : Blo 2125435 12110309 := bstep (se 4 (by rfl) ⟨1135341, by rfl⟩ : syracuseStep 12110309 = 2270683) B2270683
theorem B8073539 : Blo 2125435 8073539 := bstep (se 1 (by rfl) ⟨6055154, by rfl⟩ : syracuseStep 8073539 = 12110309) B12110309
theorem B5382359 : Blo 2125435 5382359 := bstep (se 1 (by rfl) ⟨4036769, by rfl⟩ : syracuseStep 5382359 = 8073539) B8073539
theorem B3588239 : Blo 2125435 3588239 := bstep (se 1 (by rfl) ⟨2691179, by rfl⟩ : syracuseStep 3588239 = 5382359) B5382359
theorem B2392159 : Blo 2125435 2392159 := bstep (se 1 (by rfl) ⟨1794119, by rfl⟩ : syracuseStep 2392159 = 3588239) B3588239
theorem B3189545 : Blo 2125435 3189545 := bstep (se 2 (by rfl) ⟨1196079, by rfl⟩ : syracuseStep 3189545 = 2392159) B2392159
theorem B2126363 : Blo 2125435 2126363 := bstep (se 1 (by rfl) ⟨1594772, by rfl⟩ : syracuseStep 2126363 = 3189545) B3189545
theorem B3277181 : Blo 2125435 3277181 := bbase (se 3 (by rfl) ⟨614471, by rfl⟩ : syracuseStep 3277181 = 1228943) (by norm_num)
theorem B2184787 : Blo 2125435 2184787 := bstep (se 1 (by rfl) ⟨1638590, by rfl⟩ : syracuseStep 2184787 = 3277181) B3277181
theorem B2913049 : Blo 2125435 2913049 := bstep (se 2 (by rfl) ⟨1092393, by rfl⟩ : syracuseStep 2913049 = 2184787) B2184787
theorem B15536261 : Blo 2125435 15536261 := bstep (se 4 (by rfl) ⟨1456524, by rfl⟩ : syracuseStep 15536261 = 2913049) B2913049
theorem B10357507 : Blo 2125435 10357507 := bstep (se 1 (by rfl) ⟨7768130, by rfl⟩ : syracuseStep 10357507 = 15536261) B15536261
theorem B13810009 : Blo 2125435 13810009 := bstep (se 2 (by rfl) ⟨5178753, by rfl⟩ : syracuseStep 13810009 = 10357507) B10357507
theorem B18413345 : Blo 2125435 18413345 := bstep (se 2 (by rfl) ⟨6905004, by rfl⟩ : syracuseStep 18413345 = 13810009) B13810009
theorem B12275563 : Blo 2125435 12275563 := bstep (se 1 (by rfl) ⟨9206672, by rfl⟩ : syracuseStep 12275563 = 18413345) B18413345
theorem B16367417 : Blo 2125435 16367417 := bstep (se 2 (by rfl) ⟨6137781, by rfl⟩ : syracuseStep 16367417 = 12275563) B12275563
theorem B10911611 : Blo 2125435 10911611 := bstep (se 1 (by rfl) ⟨8183708, by rfl⟩ : syracuseStep 10911611 = 16367417) B16367417
theorem B7274407 : Blo 2125435 7274407 := bstep (se 1 (by rfl) ⟨5455805, by rfl⟩ : syracuseStep 7274407 = 10911611) B10911611
theorem B9699209 : Blo 2125435 9699209 := bstep (se 2 (by rfl) ⟨3637203, by rfl⟩ : syracuseStep 9699209 = 7274407) B7274407
theorem B6466139 : Blo 2125435 6466139 := bstep (se 1 (by rfl) ⟨4849604, by rfl⟩ : syracuseStep 6466139 = 9699209) B9699209
theorem B4310759 : Blo 2125435 4310759 := bstep (se 1 (by rfl) ⟨3233069, by rfl⟩ : syracuseStep 4310759 = 6466139) B6466139
theorem B11495357 : Blo 2125435 11495357 := bstep (se 3 (by rfl) ⟨2155379, by rfl⟩ : syracuseStep 11495357 = 4310759) B4310759
theorem B7663571 : Blo 2125435 7663571 := bstep (se 1 (by rfl) ⟨5747678, by rfl⟩ : syracuseStep 7663571 = 11495357) B11495357
theorem B5109047 : Blo 2125435 5109047 := bstep (se 1 (by rfl) ⟨3831785, by rfl⟩ : syracuseStep 5109047 = 7663571) B7663571
theorem B3406031 : Blo 2125435 3406031 := bstep (se 1 (by rfl) ⟨2554523, by rfl⟩ : syracuseStep 3406031 = 5109047) B5109047
theorem B2270687 : Blo 2125435 2270687 := bstep (se 1 (by rfl) ⟨1703015, by rfl⟩ : syracuseStep 2270687 = 3406031) B3406031
theorem B6055165 : Blo 2125435 6055165 := bstep (se 3 (by rfl) ⟨1135343, by rfl⟩ : syracuseStep 6055165 = 2270687) B2270687
theorem B8073553 : Blo 2125435 8073553 := bstep (se 2 (by rfl) ⟨3027582, by rfl⟩ : syracuseStep 8073553 = 6055165) B6055165
theorem B10764737 : Blo 2125435 10764737 := bstep (se 2 (by rfl) ⟨4036776, by rfl⟩ : syracuseStep 10764737 = 8073553) B8073553
theorem B7176491 : Blo 2125435 7176491 := bstep (se 1 (by rfl) ⟨5382368, by rfl⟩ : syracuseStep 7176491 = 10764737) B10764737
theorem B4784327 : Blo 2125435 4784327 := bstep (se 1 (by rfl) ⟨3588245, by rfl⟩ : syracuseStep 4784327 = 7176491) B7176491
theorem B3189551 : Blo 2125435 3189551 := bstep (se 1 (by rfl) ⟨2392163, by rfl⟩ : syracuseStep 3189551 = 4784327) B4784327
theorem B2126367 : Blo 2125435 2126367 := bstep (se 1 (by rfl) ⟨1594775, by rfl⟩ : syracuseStep 2126367 = 3189551) B3189551
theorem B3189557 : Blo 2125435 3189557 := bbase (se 5 (by rfl) ⟨149510, by rfl⟩ : syracuseStep 3189557 = 299021) (by norm_num)
theorem B2126371 : Blo 2125435 2126371 := bstep (se 1 (by rfl) ⟨1594778, by rfl⟩ : syracuseStep 2126371 = 3189557) B3189557
theorem B5382389 : Blo 2125435 5382389 := bbase (se 5 (by rfl) ⟨252299, by rfl⟩ : syracuseStep 5382389 = 504599) (by norm_num)
theorem B3588259 : Blo 2125435 3588259 := bstep (se 1 (by rfl) ⟨2691194, by rfl⟩ : syracuseStep 3588259 = 5382389) B5382389
theorem B4784345 : Blo 2125435 4784345 := bstep (se 2 (by rfl) ⟨1794129, by rfl⟩ : syracuseStep 4784345 = 3588259) B3588259
theorem B3189563 : Blo 2125435 3189563 := bstep (se 1 (by rfl) ⟨2392172, by rfl⟩ : syracuseStep 3189563 = 4784345) B4784345
theorem B2126375 : Blo 2125435 2126375 := bstep (se 1 (by rfl) ⟨1594781, by rfl⟩ : syracuseStep 2126375 = 3189563) B3189563
theorem B2392177 : Blo 2125435 2392177 := bbase (se 2 (by rfl) ⟨897066, by rfl⟩ : syracuseStep 2392177 = 1794133) (by norm_num)
theorem B3189569 : Blo 2125435 3189569 := bstep (se 2 (by rfl) ⟨1196088, by rfl⟩ : syracuseStep 3189569 = 2392177) B2392177
theorem B2126379 : Blo 2125435 2126379 := bstep (se 1 (by rfl) ⟨1594784, by rfl⟩ : syracuseStep 2126379 = 3189569) B3189569
theorem B5109085 : Blo 2125435 5109085 := bbase (se 3 (by rfl) ⟨957953, by rfl⟩ : syracuseStep 5109085 = 1915907) (by norm_num)
theorem B6812113 : Blo 2125435 6812113 := bstep (se 2 (by rfl) ⟨2554542, by rfl⟩ : syracuseStep 6812113 = 5109085) B5109085
theorem B9082817 : Blo 2125435 9082817 := bstep (se 2 (by rfl) ⟨3406056, by rfl⟩ : syracuseStep 9082817 = 6812113) B6812113
theorem B6055211 : Blo 2125435 6055211 := bstep (se 1 (by rfl) ⟨4541408, by rfl⟩ : syracuseStep 6055211 = 9082817) B9082817
theorem B4036807 : Blo 2125435 4036807 := bstep (se 1 (by rfl) ⟨3027605, by rfl⟩ : syracuseStep 4036807 = 6055211) B6055211
theorem B5382409 : Blo 2125435 5382409 := bstep (se 2 (by rfl) ⟨2018403, by rfl⟩ : syracuseStep 5382409 = 4036807) B4036807
theorem B7176545 : Blo 2125435 7176545 := bstep (se 2 (by rfl) ⟨2691204, by rfl⟩ : syracuseStep 7176545 = 5382409) B5382409
theorem B4784363 : Blo 2125435 4784363 := bstep (se 1 (by rfl) ⟨3588272, by rfl⟩ : syracuseStep 4784363 = 7176545) B7176545
theorem B3189575 : Blo 2125435 3189575 := bstep (se 1 (by rfl) ⟨2392181, by rfl⟩ : syracuseStep 3189575 = 4784363) B4784363
theorem B2126383 : Blo 2125435 2126383 := bstep (se 1 (by rfl) ⟨1594787, by rfl⟩ : syracuseStep 2126383 = 3189575) B3189575
theorem B3189581 : Blo 2125435 3189581 := bbase (se 3 (by rfl) ⟨598046, by rfl⟩ : syracuseStep 3189581 = 1196093) (by norm_num)
theorem B2126387 : Blo 2125435 2126387 := bstep (se 1 (by rfl) ⟨1594790, by rfl⟩ : syracuseStep 2126387 = 3189581) B3189581
theorem B4784381 : Blo 2125435 4784381 := bbase (se 3 (by rfl) ⟨897071, by rfl⟩ : syracuseStep 4784381 = 1794143) (by norm_num)
theorem B3189587 : Blo 2125435 3189587 := bstep (se 1 (by rfl) ⟨2392190, by rfl⟩ : syracuseStep 3189587 = 4784381) B4784381
theorem B2126391 : Blo 2125435 2126391 := bstep (se 1 (by rfl) ⟨1594793, by rfl⟩ : syracuseStep 2126391 = 3189587) B3189587
theorem B3588293 : Blo 2125435 3588293 := bbase (se 4 (by rfl) ⟨336402, by rfl⟩ : syracuseStep 3588293 = 672805) (by norm_num)
theorem B2392195 : Blo 2125435 2392195 := bstep (se 1 (by rfl) ⟨1794146, by rfl⟩ : syracuseStep 2392195 = 3588293) B3588293
theorem B3189593 : Blo 2125435 3189593 := bstep (se 2 (by rfl) ⟨1196097, by rfl⟩ : syracuseStep 3189593 = 2392195) B2392195
theorem B2126395 : Blo 2125435 2126395 := bstep (se 1 (by rfl) ⟨1594796, by rfl⟩ : syracuseStep 2126395 = 3189593) B3189593
theorem B16147349 : Blo 2125435 16147349 := bbase (se 6 (by rfl) ⟨378453, by rfl⟩ : syracuseStep 16147349 = 756907) (by norm_num)
theorem B10764899 : Blo 2125435 10764899 := bstep (se 1 (by rfl) ⟨8073674, by rfl⟩ : syracuseStep 10764899 = 16147349) B16147349
theorem B7176599 : Blo 2125435 7176599 := bstep (se 1 (by rfl) ⟨5382449, by rfl⟩ : syracuseStep 7176599 = 10764899) B10764899
theorem B4784399 : Blo 2125435 4784399 := bstep (se 1 (by rfl) ⟨3588299, by rfl⟩ : syracuseStep 4784399 = 7176599) B7176599
theorem B3189599 : Blo 2125435 3189599 := bstep (se 1 (by rfl) ⟨2392199, by rfl⟩ : syracuseStep 3189599 = 4784399) B4784399
theorem B2126399 : Blo 2125435 2126399 := bstep (se 1 (by rfl) ⟨1594799, by rfl⟩ : syracuseStep 2126399 = 3189599) B3189599
theorem B3189605 : Blo 2125435 3189605 := bbase (se 4 (by rfl) ⟨299025, by rfl⟩ : syracuseStep 3189605 = 598051) (by norm_num)
theorem B2126403 : Blo 2125435 2126403 := bstep (se 1 (by rfl) ⟨1594802, by rfl⟩ : syracuseStep 2126403 = 3189605) B3189605
theorem B4036853 : Blo 2125435 4036853 := bbase (se 5 (by rfl) ⟨189227, by rfl⟩ : syracuseStep 4036853 = 378455) (by norm_num)
theorem B2691235 : Blo 2125435 2691235 := bstep (se 1 (by rfl) ⟨2018426, by rfl⟩ : syracuseStep 2691235 = 4036853) B4036853
theorem B3588313 : Blo 2125435 3588313 := bstep (se 2 (by rfl) ⟨1345617, by rfl⟩ : syracuseStep 3588313 = 2691235) B2691235
theorem B4784417 : Blo 2125435 4784417 := bstep (se 2 (by rfl) ⟨1794156, by rfl⟩ : syracuseStep 4784417 = 3588313) B3588313
theorem B3189611 : Blo 2125435 3189611 := bstep (se 1 (by rfl) ⟨2392208, by rfl⟩ : syracuseStep 3189611 = 4784417) B4784417
theorem B2126407 : Blo 2125435 2126407 := bstep (se 1 (by rfl) ⟨1594805, by rfl⟩ : syracuseStep 2126407 = 3189611) B3189611
theorem B2392213 : Blo 2125435 2392213 := bbase (se 6 (by rfl) ⟨56067, by rfl⟩ : syracuseStep 2392213 = 112135) (by norm_num)
theorem B3189617 : Blo 2125435 3189617 := bstep (se 2 (by rfl) ⟨1196106, by rfl⟩ : syracuseStep 3189617 = 2392213) B2392213
theorem B2126411 : Blo 2125435 2126411 := bstep (se 1 (by rfl) ⟨1594808, by rfl⟩ : syracuseStep 2126411 = 3189617) B3189617
theorem B2691245 : Blo 2125435 2691245 := bbase (se 3 (by rfl) ⟨504608, by rfl⟩ : syracuseStep 2691245 = 1009217) (by norm_num)
theorem B7176653 : Blo 2125435 7176653 := bstep (se 3 (by rfl) ⟨1345622, by rfl⟩ : syracuseStep 7176653 = 2691245) B2691245
theorem B4784435 : Blo 2125435 4784435 := bstep (se 1 (by rfl) ⟨3588326, by rfl⟩ : syracuseStep 4784435 = 7176653) B7176653
theorem B3189623 : Blo 2125435 3189623 := bstep (se 1 (by rfl) ⟨2392217, by rfl⟩ : syracuseStep 3189623 = 4784435) B4784435
theorem B2126415 : Blo 2125435 2126415 := bstep (se 1 (by rfl) ⟨1594811, by rfl⟩ : syracuseStep 2126415 = 3189623) B3189623
theorem B3189629 : Blo 2125435 3189629 := bbase (se 3 (by rfl) ⟨598055, by rfl⟩ : syracuseStep 3189629 = 1196111) (by norm_num)
theorem B2126419 : Blo 2125435 2126419 := bstep (se 1 (by rfl) ⟨1594814, by rfl⟩ : syracuseStep 2126419 = 3189629) B3189629
theorem B4784453 : Blo 2125435 4784453 := bbase (se 4 (by rfl) ⟨448542, by rfl⟩ : syracuseStep 4784453 = 897085) (by norm_num)
theorem B3189635 : Blo 2125435 3189635 := bstep (se 1 (by rfl) ⟨2392226, by rfl⟩ : syracuseStep 3189635 = 4784453) B4784453
theorem B2126423 : Blo 2125435 2126423 := bstep (se 1 (by rfl) ⟨1594817, by rfl⟩ : syracuseStep 2126423 = 3189635) B3189635
theorem B4849741 : Blo 2125435 4849741 := bbase (se 3 (by rfl) ⟨909326, by rfl⟩ : syracuseStep 4849741 = 1818653) (by norm_num)
theorem B6466321 : Blo 2125435 6466321 := bstep (se 2 (by rfl) ⟨2424870, by rfl⟩ : syracuseStep 6466321 = 4849741) B4849741
theorem B34487045 : Blo 2125435 34487045 := bstep (se 4 (by rfl) ⟨3233160, by rfl⟩ : syracuseStep 34487045 = 6466321) B6466321
theorem B22991363 : Blo 2125435 22991363 := bstep (se 1 (by rfl) ⟨17243522, by rfl⟩ : syracuseStep 22991363 = 34487045) B34487045
theorem B15327575 : Blo 2125435 15327575 := bstep (se 1 (by rfl) ⟨11495681, by rfl⟩ : syracuseStep 15327575 = 22991363) B22991363
theorem B10218383 : Blo 2125435 10218383 := bstep (se 1 (by rfl) ⟨7663787, by rfl⟩ : syracuseStep 10218383 = 15327575) B15327575
theorem B6812255 : Blo 2125435 6812255 := bstep (se 1 (by rfl) ⟨5109191, by rfl⟩ : syracuseStep 6812255 = 10218383) B10218383
theorem B4541503 : Blo 2125435 4541503 := bstep (se 1 (by rfl) ⟨3406127, by rfl⟩ : syracuseStep 4541503 = 6812255) B6812255
theorem B6055337 : Blo 2125435 6055337 := bstep (se 2 (by rfl) ⟨2270751, by rfl⟩ : syracuseStep 6055337 = 4541503) B4541503
theorem B4036891 : Blo 2125435 4036891 := bstep (se 1 (by rfl) ⟨3027668, by rfl⟩ : syracuseStep 4036891 = 6055337) B6055337
theorem B5382521 : Blo 2125435 5382521 := bstep (se 2 (by rfl) ⟨2018445, by rfl⟩ : syracuseStep 5382521 = 4036891) B4036891
theorem B3588347 : Blo 2125435 3588347 := bstep (se 1 (by rfl) ⟨2691260, by rfl⟩ : syracuseStep 3588347 = 5382521) B5382521
theorem B2392231 : Blo 2125435 2392231 := bstep (se 1 (by rfl) ⟨1794173, by rfl⟩ : syracuseStep 2392231 = 3588347) B3588347
theorem B3189641 : Blo 2125435 3189641 := bstep (se 2 (by rfl) ⟨1196115, by rfl⟩ : syracuseStep 3189641 = 2392231) B2392231
theorem B2126427 : Blo 2125435 2126427 := bstep (se 1 (by rfl) ⟨1594820, by rfl⟩ : syracuseStep 2126427 = 3189641) B3189641
theorem B10765061 : Blo 2125435 10765061 := bbase (se 4 (by rfl) ⟨1009224, by rfl⟩ : syracuseStep 10765061 = 2018449) (by norm_num)
theorem B7176707 : Blo 2125435 7176707 := bstep (se 1 (by rfl) ⟨5382530, by rfl⟩ : syracuseStep 7176707 = 10765061) B10765061
theorem B4784471 : Blo 2125435 4784471 := bstep (se 1 (by rfl) ⟨3588353, by rfl⟩ : syracuseStep 4784471 = 7176707) B7176707
theorem B3189647 : Blo 2125435 3189647 := bstep (se 1 (by rfl) ⟨2392235, by rfl⟩ : syracuseStep 3189647 = 4784471) B4784471
theorem B2126431 : Blo 2125435 2126431 := bstep (se 1 (by rfl) ⟨1594823, by rfl⟩ : syracuseStep 2126431 = 3189647) B3189647
theorem B3189653 : Blo 2125435 3189653 := bbase (se 6 (by rfl) ⟨74757, by rfl⟩ : syracuseStep 3189653 = 149515) (by norm_num)
theorem B2126435 : Blo 2125435 2126435 := bstep (se 1 (by rfl) ⟨1594826, by rfl⟩ : syracuseStep 2126435 = 3189653) B3189653
theorem B12110741 : Blo 2125435 12110741 := bbase (se 6 (by rfl) ⟨283845, by rfl⟩ : syracuseStep 12110741 = 567691) (by norm_num)
theorem B8073827 : Blo 2125435 8073827 := bstep (se 1 (by rfl) ⟨6055370, by rfl⟩ : syracuseStep 8073827 = 12110741) B12110741
theorem B5382551 : Blo 2125435 5382551 := bstep (se 1 (by rfl) ⟨4036913, by rfl⟩ : syracuseStep 5382551 = 8073827) B8073827
theorem B3588367 : Blo 2125435 3588367 := bstep (se 1 (by rfl) ⟨2691275, by rfl⟩ : syracuseStep 3588367 = 5382551) B5382551
theorem B4784489 : Blo 2125435 4784489 := bstep (se 2 (by rfl) ⟨1794183, by rfl⟩ : syracuseStep 4784489 = 3588367) B3588367
theorem B3189659 : Blo 2125435 3189659 := bstep (se 1 (by rfl) ⟨2392244, by rfl⟩ : syracuseStep 3189659 = 4784489) B4784489
theorem B2126439 : Blo 2125435 2126439 := bstep (se 1 (by rfl) ⟨1594829, by rfl⟩ : syracuseStep 2126439 = 3189659) B3189659
theorem B2392249 : Blo 2125435 2392249 := bbase (se 2 (by rfl) ⟨897093, by rfl⟩ : syracuseStep 2392249 = 1794187) (by norm_num)
theorem B3189665 : Blo 2125435 3189665 := bstep (se 2 (by rfl) ⟨1196124, by rfl⟩ : syracuseStep 3189665 = 2392249) B2392249
theorem B2126443 : Blo 2125435 2126443 := bstep (se 1 (by rfl) ⟨1594832, by rfl⟩ : syracuseStep 2126443 = 3189665) B3189665
theorem B3884213 : Blo 2125435 3884213 := bbase (se 5 (by rfl) ⟨182072, by rfl⟩ : syracuseStep 3884213 = 364145) (by norm_num)
theorem B2589475 : Blo 2125435 2589475 := bstep (se 1 (by rfl) ⟨1942106, by rfl⟩ : syracuseStep 2589475 = 3884213) B3884213
theorem B3452633 : Blo 2125435 3452633 := bstep (se 2 (by rfl) ⟨1294737, by rfl⟩ : syracuseStep 3452633 = 2589475) B2589475
theorem B2301755 : Blo 2125435 2301755 := bstep (se 1 (by rfl) ⟨1726316, by rfl⟩ : syracuseStep 2301755 = 3452633) B3452633
theorem B6138013 : Blo 2125435 6138013 := bstep (se 3 (by rfl) ⟨1150877, by rfl⟩ : syracuseStep 6138013 = 2301755) B2301755
theorem B8184017 : Blo 2125435 8184017 := bstep (se 2 (by rfl) ⟨3069006, by rfl⟩ : syracuseStep 8184017 = 6138013) B6138013
theorem B5456011 : Blo 2125435 5456011 := bstep (se 1 (by rfl) ⟨4092008, by rfl⟩ : syracuseStep 5456011 = 8184017) B8184017
theorem B7274681 : Blo 2125435 7274681 := bstep (se 2 (by rfl) ⟨2728005, by rfl⟩ : syracuseStep 7274681 = 5456011) B5456011
theorem B4849787 : Blo 2125435 4849787 := bstep (se 1 (by rfl) ⟨3637340, by rfl⟩ : syracuseStep 4849787 = 7274681) B7274681
theorem B3233191 : Blo 2125435 3233191 := bstep (se 1 (by rfl) ⟨2424893, by rfl⟩ : syracuseStep 3233191 = 4849787) B4849787
theorem B4310921 : Blo 2125435 4310921 := bstep (se 2 (by rfl) ⟨1616595, by rfl⟩ : syracuseStep 4310921 = 3233191) B3233191
theorem B11495789 : Blo 2125435 11495789 := bstep (se 3 (by rfl) ⟨2155460, by rfl⟩ : syracuseStep 11495789 = 4310921) B4310921
theorem B7663859 : Blo 2125435 7663859 := bstep (se 1 (by rfl) ⟨5747894, by rfl⟩ : syracuseStep 7663859 = 11495789) B11495789
theorem B5109239 : Blo 2125435 5109239 := bstep (se 1 (by rfl) ⟨3831929, by rfl⟩ : syracuseStep 5109239 = 7663859) B7663859
theorem B3406159 : Blo 2125435 3406159 := bstep (se 1 (by rfl) ⟨2554619, by rfl⟩ : syracuseStep 3406159 = 5109239) B5109239
theorem B4541545 : Blo 2125435 4541545 := bstep (se 2 (by rfl) ⟨1703079, by rfl⟩ : syracuseStep 4541545 = 3406159) B3406159
theorem B6055393 : Blo 2125435 6055393 := bstep (se 2 (by rfl) ⟨2270772, by rfl⟩ : syracuseStep 6055393 = 4541545) B4541545
theorem B8073857 : Blo 2125435 8073857 := bstep (se 2 (by rfl) ⟨3027696, by rfl⟩ : syracuseStep 8073857 = 6055393) B6055393
theorem B5382571 : Blo 2125435 5382571 := bstep (se 1 (by rfl) ⟨4036928, by rfl⟩ : syracuseStep 5382571 = 8073857) B8073857
theorem B7176761 : Blo 2125435 7176761 := bstep (se 2 (by rfl) ⟨2691285, by rfl⟩ : syracuseStep 7176761 = 5382571) B5382571
theorem B4784507 : Blo 2125435 4784507 := bstep (se 1 (by rfl) ⟨3588380, by rfl⟩ : syracuseStep 4784507 = 7176761) B7176761
theorem B3189671 : Blo 2125435 3189671 := bstep (se 1 (by rfl) ⟨2392253, by rfl⟩ : syracuseStep 3189671 = 4784507) B4784507
theorem B2126447 : Blo 2125435 2126447 := bstep (se 1 (by rfl) ⟨1594835, by rfl⟩ : syracuseStep 2126447 = 3189671) B3189671
theorem B3189677 : Blo 2125435 3189677 := bbase (se 3 (by rfl) ⟨598064, by rfl⟩ : syracuseStep 3189677 = 1196129) (by norm_num)
theorem B2126451 : Blo 2125435 2126451 := bstep (se 1 (by rfl) ⟨1594838, by rfl⟩ : syracuseStep 2126451 = 3189677) B3189677
theorem B4784525 : Blo 2125435 4784525 := bbase (se 3 (by rfl) ⟨897098, by rfl⟩ : syracuseStep 4784525 = 1794197) (by norm_num)
theorem B3189683 : Blo 2125435 3189683 := bstep (se 1 (by rfl) ⟨2392262, by rfl⟩ : syracuseStep 3189683 = 4784525) B4784525
theorem B2126455 : Blo 2125435 2126455 := bstep (se 1 (by rfl) ⟨1594841, by rfl⟩ : syracuseStep 2126455 = 3189683) B3189683
theorem B2691301 : Blo 2125435 2691301 := bbase (se 4 (by rfl) ⟨252309, by rfl⟩ : syracuseStep 2691301 = 504619) (by norm_num)
theorem B3588401 : Blo 2125435 3588401 := bstep (se 2 (by rfl) ⟨1345650, by rfl⟩ : syracuseStep 3588401 = 2691301) B2691301
theorem B2392267 : Blo 2125435 2392267 := bstep (se 1 (by rfl) ⟨1794200, by rfl⟩ : syracuseStep 2392267 = 3588401) B3588401
theorem B3189689 : Blo 2125435 3189689 := bstep (se 2 (by rfl) ⟨1196133, by rfl⟩ : syracuseStep 3189689 = 2392267) B2392267
theorem B2126459 : Blo 2125435 2126459 := bstep (se 1 (by rfl) ⟨1594844, by rfl⟩ : syracuseStep 2126459 = 3189689) B3189689
theorem B15327829 : Blo 2125435 15327829 := bbase (se 8 (by rfl) ⟨89811, by rfl⟩ : syracuseStep 15327829 = 179623) (by norm_num)
theorem B20437105 : Blo 2125435 20437105 := bstep (se 2 (by rfl) ⟨7663914, by rfl⟩ : syracuseStep 20437105 = 15327829) B15327829
theorem B27249473 : Blo 2125435 27249473 := bstep (se 2 (by rfl) ⟨10218552, by rfl⟩ : syracuseStep 27249473 = 20437105) B20437105
theorem B18166315 : Blo 2125435 18166315 := bstep (se 1 (by rfl) ⟨13624736, by rfl⟩ : syracuseStep 18166315 = 27249473) B27249473
theorem B24221753 : Blo 2125435 24221753 := bstep (se 2 (by rfl) ⟨9083157, by rfl⟩ : syracuseStep 24221753 = 18166315) B18166315
theorem B16147835 : Blo 2125435 16147835 := bstep (se 1 (by rfl) ⟨12110876, by rfl⟩ : syracuseStep 16147835 = 24221753) B24221753
theorem B10765223 : Blo 2125435 10765223 := bstep (se 1 (by rfl) ⟨8073917, by rfl⟩ : syracuseStep 10765223 = 16147835) B16147835
theorem B7176815 : Blo 2125435 7176815 := bstep (se 1 (by rfl) ⟨5382611, by rfl⟩ : syracuseStep 7176815 = 10765223) B10765223
theorem B4784543 : Blo 2125435 4784543 := bstep (se 1 (by rfl) ⟨3588407, by rfl⟩ : syracuseStep 4784543 = 7176815) B7176815
theorem B3189695 : Blo 2125435 3189695 := bstep (se 1 (by rfl) ⟨2392271, by rfl⟩ : syracuseStep 3189695 = 4784543) B4784543
theorem B2126463 : Blo 2125435 2126463 := bstep (se 1 (by rfl) ⟨1594847, by rfl⟩ : syracuseStep 2126463 = 3189695) B3189695
theorem B3189701 : Blo 2125435 3189701 := bbase (se 4 (by rfl) ⟨299034, by rfl⟩ : syracuseStep 3189701 = 598069) (by norm_num)
theorem B2126467 : Blo 2125435 2126467 := bstep (se 1 (by rfl) ⟨1594850, by rfl⟩ : syracuseStep 2126467 = 3189701) B3189701
theorem B3588421 : Blo 2125435 3588421 := bbase (se 4 (by rfl) ⟨336414, by rfl⟩ : syracuseStep 3588421 = 672829) (by norm_num)
theorem B4784561 : Blo 2125435 4784561 := bstep (se 2 (by rfl) ⟨1794210, by rfl⟩ : syracuseStep 4784561 = 3588421) B3588421
theorem B3189707 : Blo 2125435 3189707 := bstep (se 1 (by rfl) ⟨2392280, by rfl⟩ : syracuseStep 3189707 = 4784561) B4784561
theorem B2126471 : Blo 2125435 2126471 := bstep (se 1 (by rfl) ⟨1594853, by rfl⟩ : syracuseStep 2126471 = 3189707) B3189707
theorem B2392285 : Blo 2125435 2392285 := bbase (se 3 (by rfl) ⟨448553, by rfl⟩ : syracuseStep 2392285 = 897107) (by norm_num)
theorem B3189713 : Blo 2125435 3189713 := bstep (se 2 (by rfl) ⟨1196142, by rfl⟩ : syracuseStep 3189713 = 2392285) B2392285
theorem B2126475 : Blo 2125435 2126475 := bstep (se 1 (by rfl) ⟨1594856, by rfl⟩ : syracuseStep 2126475 = 3189713) B3189713
theorem B7176869 : Blo 2125435 7176869 := bbase (se 4 (by rfl) ⟨672831, by rfl⟩ : syracuseStep 7176869 = 1345663) (by norm_num)
theorem B4784579 : Blo 2125435 4784579 := bstep (se 1 (by rfl) ⟨3588434, by rfl⟩ : syracuseStep 4784579 = 7176869) B7176869
theorem B3189719 : Blo 2125435 3189719 := bstep (se 1 (by rfl) ⟨2392289, by rfl⟩ : syracuseStep 3189719 = 4784579) B4784579
theorem B2126479 : Blo 2125435 2126479 := bstep (se 1 (by rfl) ⟨1594859, by rfl⟩ : syracuseStep 2126479 = 3189719) B3189719
theorem B3189725 : Blo 2125435 3189725 := bbase (se 3 (by rfl) ⟨598073, by rfl⟩ : syracuseStep 3189725 = 1196147) (by norm_num)
theorem B2126483 : Blo 2125435 2126483 := bstep (se 1 (by rfl) ⟨1594862, by rfl⟩ : syracuseStep 2126483 = 3189725) B3189725
theorem B4784597 : Blo 2125435 4784597 := bbase (se 7 (by rfl) ⟨56069, by rfl⟩ : syracuseStep 4784597 = 112139) (by norm_num)
theorem B3189731 : Blo 2125435 3189731 := bstep (se 1 (by rfl) ⟨2392298, by rfl⟩ : syracuseStep 3189731 = 4784597) B4784597
theorem B2126487 : Blo 2125435 2126487 := bstep (se 1 (by rfl) ⟨1594865, by rfl⟩ : syracuseStep 2126487 = 3189731) B3189731
theorem B2155505 : Blo 2125435 2155505 := bbase (se 2 (by rfl) ⟨808314, by rfl⟩ : syracuseStep 2155505 = 1616629) (by norm_num)
theorem B5748013 : Blo 2125435 5748013 := bstep (se 3 (by rfl) ⟨1077752, by rfl⟩ : syracuseStep 5748013 = 2155505) B2155505
theorem B30656069 : Blo 2125435 30656069 := bstep (se 4 (by rfl) ⟨2874006, by rfl⟩ : syracuseStep 30656069 = 5748013) B5748013
theorem B20437379 : Blo 2125435 20437379 := bstep (se 1 (by rfl) ⟨15328034, by rfl⟩ : syracuseStep 20437379 = 30656069) B30656069
theorem B13624919 : Blo 2125435 13624919 := bstep (se 1 (by rfl) ⟨10218689, by rfl⟩ : syracuseStep 13624919 = 20437379) B20437379
theorem B9083279 : Blo 2125435 9083279 := bstep (se 1 (by rfl) ⟨6812459, by rfl⟩ : syracuseStep 9083279 = 13624919) B13624919
theorem B6055519 : Blo 2125435 6055519 := bstep (se 1 (by rfl) ⟨4541639, by rfl⟩ : syracuseStep 6055519 = 9083279) B9083279
theorem B8074025 : Blo 2125435 8074025 := bstep (se 2 (by rfl) ⟨3027759, by rfl⟩ : syracuseStep 8074025 = 6055519) B6055519
theorem B5382683 : Blo 2125435 5382683 := bstep (se 1 (by rfl) ⟨4037012, by rfl⟩ : syracuseStep 5382683 = 8074025) B8074025
theorem B3588455 : Blo 2125435 3588455 := bstep (se 1 (by rfl) ⟨2691341, by rfl⟩ : syracuseStep 3588455 = 5382683) B5382683
theorem B2392303 : Blo 2125435 2392303 := bstep (se 1 (by rfl) ⟨1794227, by rfl⟩ : syracuseStep 2392303 = 3588455) B3588455
theorem B3189737 : Blo 2125435 3189737 := bstep (se 2 (by rfl) ⟨1196151, by rfl⟩ : syracuseStep 3189737 = 2392303) B2392303
theorem B2126491 : Blo 2125435 2126491 := bstep (se 1 (by rfl) ⟨1594868, by rfl⟩ : syracuseStep 2126491 = 3189737) B3189737
theorem B13810837 : Blo 2125435 13810837 := bbase (se 6 (by rfl) ⟨323691, by rfl⟩ : syracuseStep 13810837 = 647383) (by norm_num)
theorem B18414449 : Blo 2125435 18414449 := bstep (se 2 (by rfl) ⟨6905418, by rfl⟩ : syracuseStep 18414449 = 13810837) B13810837
theorem B12276299 : Blo 2125435 12276299 := bstep (se 1 (by rfl) ⟨9207224, by rfl⟩ : syracuseStep 12276299 = 18414449) B18414449
theorem B8184199 : Blo 2125435 8184199 := bstep (se 1 (by rfl) ⟨6138149, by rfl⟩ : syracuseStep 8184199 = 12276299) B12276299
theorem B10912265 : Blo 2125435 10912265 := bstep (se 2 (by rfl) ⟨4092099, by rfl⟩ : syracuseStep 10912265 = 8184199) B8184199
theorem B7274843 : Blo 2125435 7274843 := bstep (se 1 (by rfl) ⟨5456132, by rfl⟩ : syracuseStep 7274843 = 10912265) B10912265
theorem B4849895 : Blo 2125435 4849895 := bstep (se 1 (by rfl) ⟨3637421, by rfl⟩ : syracuseStep 4849895 = 7274843) B7274843
theorem B12933053 : Blo 2125435 12933053 := bstep (se 3 (by rfl) ⟨2424947, by rfl⟩ : syracuseStep 12933053 = 4849895) B4849895
theorem B8622035 : Blo 2125435 8622035 := bstep (se 1 (by rfl) ⟨6466526, by rfl⟩ : syracuseStep 8622035 = 12933053) B12933053
theorem B5748023 : Blo 2125435 5748023 := bstep (se 1 (by rfl) ⟨4311017, by rfl⟩ : syracuseStep 5748023 = 8622035) B8622035
theorem B15328061 : Blo 2125435 15328061 := bstep (se 3 (by rfl) ⟨2874011, by rfl⟩ : syracuseStep 15328061 = 5748023) B5748023
theorem B10218707 : Blo 2125435 10218707 := bstep (se 1 (by rfl) ⟨7664030, by rfl⟩ : syracuseStep 10218707 = 15328061) B15328061
theorem B6812471 : Blo 2125435 6812471 := bstep (se 1 (by rfl) ⟨5109353, by rfl⟩ : syracuseStep 6812471 = 10218707) B10218707
theorem B18166589 : Blo 2125435 18166589 := bstep (se 3 (by rfl) ⟨3406235, by rfl⟩ : syracuseStep 18166589 = 6812471) B6812471
theorem B12111059 : Blo 2125435 12111059 := bstep (se 1 (by rfl) ⟨9083294, by rfl⟩ : syracuseStep 12111059 = 18166589) B18166589
theorem B8074039 : Blo 2125435 8074039 := bstep (se 1 (by rfl) ⟨6055529, by rfl⟩ : syracuseStep 8074039 = 12111059) B12111059
theorem B10765385 : Blo 2125435 10765385 := bstep (se 2 (by rfl) ⟨4037019, by rfl⟩ : syracuseStep 10765385 = 8074039) B8074039
theorem B7176923 : Blo 2125435 7176923 := bstep (se 1 (by rfl) ⟨5382692, by rfl⟩ : syracuseStep 7176923 = 10765385) B10765385
theorem B4784615 : Blo 2125435 4784615 := bstep (se 1 (by rfl) ⟨3588461, by rfl⟩ : syracuseStep 4784615 = 7176923) B7176923
theorem B3189743 : Blo 2125435 3189743 := bstep (se 1 (by rfl) ⟨2392307, by rfl⟩ : syracuseStep 3189743 = 4784615) B4784615
theorem B2126495 : Blo 2125435 2126495 := bstep (se 1 (by rfl) ⟨1594871, by rfl⟩ : syracuseStep 2126495 = 3189743) B3189743
theorem B3189749 : Blo 2125435 3189749 := bbase (se 5 (by rfl) ⟨149519, by rfl⟩ : syracuseStep 3189749 = 299039) (by norm_num)
theorem B2126499 : Blo 2125435 2126499 := bstep (se 1 (by rfl) ⟨1594874, by rfl⟩ : syracuseStep 2126499 = 3189749) B3189749
theorem B6644213 : Blo 2125435 6644213 := bbase (se 5 (by rfl) ⟨311447, by rfl⟩ : syracuseStep 6644213 = 622895) (by norm_num)
theorem B4429475 : Blo 2125435 4429475 := bstep (se 1 (by rfl) ⟨3322106, by rfl⟩ : syracuseStep 4429475 = 6644213) B6644213
theorem B2952983 : Blo 2125435 2952983 := bstep (se 1 (by rfl) ⟨2214737, by rfl⟩ : syracuseStep 2952983 = 4429475) B4429475
theorem B7874621 : Blo 2125435 7874621 := bstep (se 3 (by rfl) ⟨1476491, by rfl⟩ : syracuseStep 7874621 = 2952983) B2952983
theorem B5249747 : Blo 2125435 5249747 := bstep (se 1 (by rfl) ⟨3937310, by rfl⟩ : syracuseStep 5249747 = 7874621) B7874621
theorem B3499831 : Blo 2125435 3499831 := bstep (se 1 (by rfl) ⟨2624873, by rfl⟩ : syracuseStep 3499831 = 5249747) B5249747
theorem B18665765 : Blo 2125435 18665765 := bstep (se 4 (by rfl) ⟨1749915, by rfl⟩ : syracuseStep 18665765 = 3499831) B3499831
theorem B12443843 : Blo 2125435 12443843 := bstep (se 1 (by rfl) ⟨9332882, by rfl⟩ : syracuseStep 12443843 = 18665765) B18665765
theorem B8295895 : Blo 2125435 8295895 := bstep (se 1 (by rfl) ⟨6221921, by rfl⟩ : syracuseStep 8295895 = 12443843) B12443843
theorem B11061193 : Blo 2125435 11061193 := bstep (se 2 (by rfl) ⟨4147947, by rfl⟩ : syracuseStep 11061193 = 8295895) B8295895
theorem B14748257 : Blo 2125435 14748257 := bstep (se 2 (by rfl) ⟨5530596, by rfl⟩ : syracuseStep 14748257 = 11061193) B11061193
theorem B39328685 : Blo 2125435 39328685 := bstep (se 3 (by rfl) ⟨7374128, by rfl⟩ : syracuseStep 39328685 = 14748257) B14748257
theorem B26219123 : Blo 2125435 26219123 := bstep (se 1 (by rfl) ⟨19664342, by rfl⟩ : syracuseStep 26219123 = 39328685) B39328685
theorem B17479415 : Blo 2125435 17479415 := bstep (se 1 (by rfl) ⟨13109561, by rfl⟩ : syracuseStep 17479415 = 26219123) B26219123
theorem B46611773 : Blo 2125435 46611773 := bstep (se 3 (by rfl) ⟨8739707, by rfl⟩ : syracuseStep 46611773 = 17479415) B17479415
theorem B31074515 : Blo 2125435 31074515 := bstep (se 1 (by rfl) ⟨23305886, by rfl⟩ : syracuseStep 31074515 = 46611773) B46611773
theorem B20716343 : Blo 2125435 20716343 := bstep (se 1 (by rfl) ⟨15537257, by rfl⟩ : syracuseStep 20716343 = 31074515) B31074515
theorem B13810895 : Blo 2125435 13810895 := bstep (se 1 (by rfl) ⟨10358171, by rfl⟩ : syracuseStep 13810895 = 20716343) B20716343
theorem B9207263 : Blo 2125435 9207263 := bstep (se 1 (by rfl) ⟨6905447, by rfl⟩ : syracuseStep 9207263 = 13810895) B13810895
theorem B6138175 : Blo 2125435 6138175 := bstep (se 1 (by rfl) ⟨4603631, by rfl⟩ : syracuseStep 6138175 = 9207263) B9207263
theorem B8184233 : Blo 2125435 8184233 := bstep (se 2 (by rfl) ⟨3069087, by rfl⟩ : syracuseStep 8184233 = 6138175) B6138175
theorem B5456155 : Blo 2125435 5456155 := bstep (se 1 (by rfl) ⟨4092116, by rfl⟩ : syracuseStep 5456155 = 8184233) B8184233
theorem B7274873 : Blo 2125435 7274873 := bstep (se 2 (by rfl) ⟨2728077, by rfl⟩ : syracuseStep 7274873 = 5456155) B5456155
theorem B19399661 : Blo 2125435 19399661 := bstep (se 3 (by rfl) ⟨3637436, by rfl⟩ : syracuseStep 19399661 = 7274873) B7274873
theorem B12933107 : Blo 2125435 12933107 := bstep (se 1 (by rfl) ⟨9699830, by rfl⟩ : syracuseStep 12933107 = 19399661) B19399661
theorem B8622071 : Blo 2125435 8622071 := bstep (se 1 (by rfl) ⟨6466553, by rfl⟩ : syracuseStep 8622071 = 12933107) B12933107
theorem B5748047 : Blo 2125435 5748047 := bstep (se 1 (by rfl) ⟨4311035, by rfl⟩ : syracuseStep 5748047 = 8622071) B8622071
theorem B3832031 : Blo 2125435 3832031 := bstep (se 1 (by rfl) ⟨2874023, by rfl⟩ : syracuseStep 3832031 = 5748047) B5748047
theorem B2554687 : Blo 2125435 2554687 := bstep (se 1 (by rfl) ⟨1916015, by rfl⟩ : syracuseStep 2554687 = 3832031) B3832031
theorem B3406249 : Blo 2125435 3406249 := bstep (se 2 (by rfl) ⟨1277343, by rfl⟩ : syracuseStep 3406249 = 2554687) B2554687
theorem B4541665 : Blo 2125435 4541665 := bstep (se 2 (by rfl) ⟨1703124, by rfl⟩ : syracuseStep 4541665 = 3406249) B3406249
theorem B6055553 : Blo 2125435 6055553 := bstep (se 2 (by rfl) ⟨2270832, by rfl⟩ : syracuseStep 6055553 = 4541665) B4541665
theorem B4037035 : Blo 2125435 4037035 := bstep (se 1 (by rfl) ⟨3027776, by rfl⟩ : syracuseStep 4037035 = 6055553) B6055553
theorem B5382713 : Blo 2125435 5382713 := bstep (se 2 (by rfl) ⟨2018517, by rfl⟩ : syracuseStep 5382713 = 4037035) B4037035
theorem B3588475 : Blo 2125435 3588475 := bstep (se 1 (by rfl) ⟨2691356, by rfl⟩ : syracuseStep 3588475 = 5382713) B5382713
theorem B4784633 : Blo 2125435 4784633 := bstep (se 2 (by rfl) ⟨1794237, by rfl⟩ : syracuseStep 4784633 = 3588475) B3588475
theorem B3189755 : Blo 2125435 3189755 := bstep (se 1 (by rfl) ⟨2392316, by rfl⟩ : syracuseStep 3189755 = 4784633) B4784633
theorem B2126503 : Blo 2125435 2126503 := bstep (se 1 (by rfl) ⟨1594877, by rfl⟩ : syracuseStep 2126503 = 3189755) B3189755
theorem B2392321 : Blo 2125435 2392321 := bbase (se 2 (by rfl) ⟨897120, by rfl⟩ : syracuseStep 2392321 = 1794241) (by norm_num)
theorem B3189761 : Blo 2125435 3189761 := bstep (se 2 (by rfl) ⟨1196160, by rfl⟩ : syracuseStep 3189761 = 2392321) B2392321
theorem B2126507 : Blo 2125435 2126507 := bstep (se 1 (by rfl) ⟨1594880, by rfl⟩ : syracuseStep 2126507 = 3189761) B3189761
theorem B5382733 : Blo 2125435 5382733 := bbase (se 3 (by rfl) ⟨1009262, by rfl⟩ : syracuseStep 5382733 = 2018525) (by norm_num)
theorem B7176977 : Blo 2125435 7176977 := bstep (se 2 (by rfl) ⟨2691366, by rfl⟩ : syracuseStep 7176977 = 5382733) B5382733
theorem B4784651 : Blo 2125435 4784651 := bstep (se 1 (by rfl) ⟨3588488, by rfl⟩ : syracuseStep 4784651 = 7176977) B7176977
theorem B3189767 : Blo 2125435 3189767 := bstep (se 1 (by rfl) ⟨2392325, by rfl⟩ : syracuseStep 3189767 = 4784651) B4784651
theorem B2126511 : Blo 2125435 2126511 := bstep (se 1 (by rfl) ⟨1594883, by rfl⟩ : syracuseStep 2126511 = 3189767) B3189767
theorem B3189773 : Blo 2125435 3189773 := bbase (se 3 (by rfl) ⟨598082, by rfl⟩ : syracuseStep 3189773 = 1196165) (by norm_num)
theorem B2126515 : Blo 2125435 2126515 := bstep (se 1 (by rfl) ⟨1594886, by rfl⟩ : syracuseStep 2126515 = 3189773) B3189773
theorem B4784669 : Blo 2125435 4784669 := bbase (se 3 (by rfl) ⟨897125, by rfl⟩ : syracuseStep 4784669 = 1794251) (by norm_num)
theorem B3189779 : Blo 2125435 3189779 := bstep (se 1 (by rfl) ⟨2392334, by rfl⟩ : syracuseStep 3189779 = 4784669) B4784669
theorem B2126519 : Blo 2125435 2126519 := bstep (se 1 (by rfl) ⟨1594889, by rfl⟩ : syracuseStep 2126519 = 3189779) B3189779
theorem B3588509 : Blo 2125435 3588509 := bbase (se 3 (by rfl) ⟨672845, by rfl⟩ : syracuseStep 3588509 = 1345691) (by norm_num)
theorem B2392339 : Blo 2125435 2392339 := bstep (se 1 (by rfl) ⟨1794254, by rfl⟩ : syracuseStep 2392339 = 3588509) B3588509
theorem B3189785 : Blo 2125435 3189785 := bstep (se 2 (by rfl) ⟨1196169, by rfl⟩ : syracuseStep 3189785 = 2392339) B2392339
theorem B2126523 : Blo 2125435 2126523 := bstep (se 1 (by rfl) ⟨1594892, by rfl⟩ : syracuseStep 2126523 = 3189785) B3189785
theorem B2155541 : Blo 2125435 2155541 := bbase (se 6 (by rfl) ⟨50520, by rfl⟩ : syracuseStep 2155541 = 101041) (by norm_num)
theorem B22992437 : Blo 2125435 22992437 := bstep (se 5 (by rfl) ⟨1077770, by rfl⟩ : syracuseStep 22992437 = 2155541) B2155541
theorem B15328291 : Blo 2125435 15328291 := bstep (se 1 (by rfl) ⟨11496218, by rfl⟩ : syracuseStep 15328291 = 22992437) B22992437
theorem B20437721 : Blo 2125435 20437721 := bstep (se 2 (by rfl) ⟨7664145, by rfl⟩ : syracuseStep 20437721 = 15328291) B15328291
theorem B13625147 : Blo 2125435 13625147 := bstep (se 1 (by rfl) ⟨10218860, by rfl⟩ : syracuseStep 13625147 = 20437721) B20437721
theorem B9083431 : Blo 2125435 9083431 := bstep (se 1 (by rfl) ⟨6812573, by rfl⟩ : syracuseStep 9083431 = 13625147) B13625147
theorem B12111241 : Blo 2125435 12111241 := bstep (se 2 (by rfl) ⟨4541715, by rfl⟩ : syracuseStep 12111241 = 9083431) B9083431
theorem B16148321 : Blo 2125435 16148321 := bstep (se 2 (by rfl) ⟨6055620, by rfl⟩ : syracuseStep 16148321 = 12111241) B12111241
theorem B10765547 : Blo 2125435 10765547 := bstep (se 1 (by rfl) ⟨8074160, by rfl⟩ : syracuseStep 10765547 = 16148321) B16148321
theorem B7177031 : Blo 2125435 7177031 := bstep (se 1 (by rfl) ⟨5382773, by rfl⟩ : syracuseStep 7177031 = 10765547) B10765547
theorem B4784687 : Blo 2125435 4784687 := bstep (se 1 (by rfl) ⟨3588515, by rfl⟩ : syracuseStep 4784687 = 7177031) B7177031
theorem B3189791 : Blo 2125435 3189791 := bstep (se 1 (by rfl) ⟨2392343, by rfl⟩ : syracuseStep 3189791 = 4784687) B4784687
theorem B2126527 : Blo 2125435 2126527 := bstep (se 1 (by rfl) ⟨1594895, by rfl⟩ : syracuseStep 2126527 = 3189791) B3189791
theorem B3189797 : Blo 2125435 3189797 := bbase (se 4 (by rfl) ⟨299043, by rfl⟩ : syracuseStep 3189797 = 598087) (by norm_num)
theorem B2126531 : Blo 2125435 2126531 := bstep (se 1 (by rfl) ⟨1594898, by rfl⟩ : syracuseStep 2126531 = 3189797) B3189797
theorem B2691397 : Blo 2125435 2691397 := bbase (se 4 (by rfl) ⟨252318, by rfl⟩ : syracuseStep 2691397 = 504637) (by norm_num)
theorem B3588529 : Blo 2125435 3588529 := bstep (se 2 (by rfl) ⟨1345698, by rfl⟩ : syracuseStep 3588529 = 2691397) B2691397
theorem B4784705 : Blo 2125435 4784705 := bstep (se 2 (by rfl) ⟨1794264, by rfl⟩ : syracuseStep 4784705 = 3588529) B3588529
theorem B3189803 : Blo 2125435 3189803 := bstep (se 1 (by rfl) ⟨2392352, by rfl⟩ : syracuseStep 3189803 = 4784705) B4784705
theorem B2126535 : Blo 2125435 2126535 := bstep (se 1 (by rfl) ⟨1594901, by rfl⟩ : syracuseStep 2126535 = 3189803) B3189803
theorem B2392357 : Blo 2125435 2392357 := bbase (se 4 (by rfl) ⟨224283, by rfl⟩ : syracuseStep 2392357 = 448567) (by norm_num)
theorem B3189809 : Blo 2125435 3189809 := bstep (se 2 (by rfl) ⟨1196178, by rfl⟩ : syracuseStep 3189809 = 2392357) B2392357
theorem B2126539 : Blo 2125435 2126539 := bstep (se 1 (by rfl) ⟨1594904, by rfl⟩ : syracuseStep 2126539 = 3189809) B3189809
theorem B2728129 : Blo 2125435 2728129 := bbase (se 2 (by rfl) ⟨1023048, by rfl⟩ : syracuseStep 2728129 = 2046097) (by norm_num)
theorem B3637505 : Blo 2125435 3637505 := bstep (se 2 (by rfl) ⟨1364064, by rfl⟩ : syracuseStep 3637505 = 2728129) B2728129
theorem B9700013 : Blo 2125435 9700013 := bstep (se 3 (by rfl) ⟨1818752, by rfl⟩ : syracuseStep 9700013 = 3637505) B3637505
theorem B6466675 : Blo 2125435 6466675 := bstep (se 1 (by rfl) ⟨4850006, by rfl⟩ : syracuseStep 6466675 = 9700013) B9700013
theorem B8622233 : Blo 2125435 8622233 := bstep (se 2 (by rfl) ⟨3233337, by rfl⟩ : syracuseStep 8622233 = 6466675) B6466675
theorem B5748155 : Blo 2125435 5748155 := bstep (se 1 (by rfl) ⟨4311116, by rfl⟩ : syracuseStep 5748155 = 8622233) B8622233
theorem B3832103 : Blo 2125435 3832103 := bstep (se 1 (by rfl) ⟨2874077, by rfl⟩ : syracuseStep 3832103 = 5748155) B5748155
theorem B2554735 : Blo 2125435 2554735 := bstep (se 1 (by rfl) ⟨1916051, by rfl⟩ : syracuseStep 2554735 = 3832103) B3832103
theorem B3406313 : Blo 2125435 3406313 := bstep (se 2 (by rfl) ⟨1277367, by rfl⟩ : syracuseStep 3406313 = 2554735) B2554735
theorem B9083501 : Blo 2125435 9083501 := bstep (se 3 (by rfl) ⟨1703156, by rfl⟩ : syracuseStep 9083501 = 3406313) B3406313
theorem B6055667 : Blo 2125435 6055667 := bstep (se 1 (by rfl) ⟨4541750, by rfl⟩ : syracuseStep 6055667 = 9083501) B9083501
theorem B4037111 : Blo 2125435 4037111 := bstep (se 1 (by rfl) ⟨3027833, by rfl⟩ : syracuseStep 4037111 = 6055667) B6055667
theorem B2691407 : Blo 2125435 2691407 := bstep (se 1 (by rfl) ⟨2018555, by rfl⟩ : syracuseStep 2691407 = 4037111) B4037111
theorem B7177085 : Blo 2125435 7177085 := bstep (se 3 (by rfl) ⟨1345703, by rfl⟩ : syracuseStep 7177085 = 2691407) B2691407
theorem B4784723 : Blo 2125435 4784723 := bstep (se 1 (by rfl) ⟨3588542, by rfl⟩ : syracuseStep 4784723 = 7177085) B7177085
theorem B3189815 : Blo 2125435 3189815 := bstep (se 1 (by rfl) ⟨2392361, by rfl⟩ : syracuseStep 3189815 = 4784723) B4784723
theorem B2126543 : Blo 2125435 2126543 := bstep (se 1 (by rfl) ⟨1594907, by rfl⟩ : syracuseStep 2126543 = 3189815) B3189815
theorem B3189821 : Blo 2125435 3189821 := bbase (se 3 (by rfl) ⟨598091, by rfl⟩ : syracuseStep 3189821 = 1196183) (by norm_num)
theorem B2126547 : Blo 2125435 2126547 := bstep (se 1 (by rfl) ⟨1594910, by rfl⟩ : syracuseStep 2126547 = 3189821) B3189821
theorem B4784741 : Blo 2125435 4784741 := bbase (se 4 (by rfl) ⟨448569, by rfl⟩ : syracuseStep 4784741 = 897139) (by norm_num)
theorem B3189827 : Blo 2125435 3189827 := bstep (se 1 (by rfl) ⟨2392370, by rfl⟩ : syracuseStep 3189827 = 4784741) B4784741
theorem B2126551 : Blo 2125435 2126551 := bstep (se 1 (by rfl) ⟨1594913, by rfl⟩ : syracuseStep 2126551 = 3189827) B3189827
theorem B5382845 : Blo 2125435 5382845 := bbase (se 3 (by rfl) ⟨1009283, by rfl⟩ : syracuseStep 5382845 = 2018567) (by norm_num)
theorem B3588563 : Blo 2125435 3588563 := bstep (se 1 (by rfl) ⟨2691422, by rfl⟩ : syracuseStep 3588563 = 5382845) B5382845
theorem B2392375 : Blo 2125435 2392375 := bstep (se 1 (by rfl) ⟨1794281, by rfl⟩ : syracuseStep 2392375 = 3588563) B3588563
theorem B3189833 : Blo 2125435 3189833 := bstep (se 2 (by rfl) ⟨1196187, by rfl⟩ : syracuseStep 3189833 = 2392375) B2392375
theorem B2126555 : Blo 2125435 2126555 := bstep (se 1 (by rfl) ⟨1594916, by rfl⟩ : syracuseStep 2126555 = 3189833) B3189833
theorem B4037141 : Blo 2125435 4037141 := bbase (se 6 (by rfl) ⟨94620, by rfl⟩ : syracuseStep 4037141 = 189241) (by norm_num)
theorem B10765709 : Blo 2125435 10765709 := bstep (se 3 (by rfl) ⟨2018570, by rfl⟩ : syracuseStep 10765709 = 4037141) B4037141
theorem B7177139 : Blo 2125435 7177139 := bstep (se 1 (by rfl) ⟨5382854, by rfl⟩ : syracuseStep 7177139 = 10765709) B10765709
theorem B4784759 : Blo 2125435 4784759 := bstep (se 1 (by rfl) ⟨3588569, by rfl⟩ : syracuseStep 4784759 = 7177139) B7177139
theorem B3189839 : Blo 2125435 3189839 := bstep (se 1 (by rfl) ⟨2392379, by rfl⟩ : syracuseStep 3189839 = 4784759) B4784759
theorem B2126559 : Blo 2125435 2126559 := bstep (se 1 (by rfl) ⟨1594919, by rfl⟩ : syracuseStep 2126559 = 3189839) B3189839
theorem B3189845 : Blo 2125435 3189845 := bbase (se 8 (by rfl) ⟨18690, by rfl⟩ : syracuseStep 3189845 = 37381) (by norm_num)
theorem B2126563 : Blo 2125435 2126563 := bstep (se 1 (by rfl) ⟨1594922, by rfl⟩ : syracuseStep 2126563 = 3189845) B3189845
theorem B11496437 : Blo 2125435 11496437 := bbase (se 5 (by rfl) ⟨538895, by rfl⟩ : syracuseStep 11496437 = 1077791) (by norm_num)
theorem B7664291 : Blo 2125435 7664291 := bstep (se 1 (by rfl) ⟨5748218, by rfl⟩ : syracuseStep 7664291 = 11496437) B11496437
theorem B5109527 : Blo 2125435 5109527 := bstep (se 1 (by rfl) ⟨3832145, by rfl⟩ : syracuseStep 5109527 = 7664291) B7664291
theorem B13625405 : Blo 2125435 13625405 := bstep (se 3 (by rfl) ⟨2554763, by rfl⟩ : syracuseStep 13625405 = 5109527) B5109527
theorem B9083603 : Blo 2125435 9083603 := bstep (se 1 (by rfl) ⟨6812702, by rfl⟩ : syracuseStep 9083603 = 13625405) B13625405
theorem B6055735 : Blo 2125435 6055735 := bstep (se 1 (by rfl) ⟨4541801, by rfl⟩ : syracuseStep 6055735 = 9083603) B9083603
theorem B8074313 : Blo 2125435 8074313 := bstep (se 2 (by rfl) ⟨3027867, by rfl⟩ : syracuseStep 8074313 = 6055735) B6055735
theorem B5382875 : Blo 2125435 5382875 := bstep (se 1 (by rfl) ⟨4037156, by rfl⟩ : syracuseStep 5382875 = 8074313) B8074313
theorem B3588583 : Blo 2125435 3588583 := bstep (se 1 (by rfl) ⟨2691437, by rfl⟩ : syracuseStep 3588583 = 5382875) B5382875
theorem B4784777 : Blo 2125435 4784777 := bstep (se 2 (by rfl) ⟨1794291, by rfl⟩ : syracuseStep 4784777 = 3588583) B3588583
theorem B3189851 : Blo 2125435 3189851 := bstep (se 1 (by rfl) ⟨2392388, by rfl⟩ : syracuseStep 3189851 = 4784777) B4784777
theorem B2126567 : Blo 2125435 2126567 := bstep (se 1 (by rfl) ⟨1594925, by rfl⟩ : syracuseStep 2126567 = 3189851) B3189851
theorem B2392393 : Blo 2125435 2392393 := bbase (se 2 (by rfl) ⟨897147, by rfl⟩ : syracuseStep 2392393 = 1794295) (by norm_num)
theorem B3189857 : Blo 2125435 3189857 := bstep (se 2 (by rfl) ⟨1196196, by rfl⟩ : syracuseStep 3189857 = 2392393) B2392393
theorem B2126571 : Blo 2125435 2126571 := bstep (se 1 (by rfl) ⟨1594928, by rfl⟩ : syracuseStep 2126571 = 3189857) B3189857
theorem B28381589 : Blo 2125435 28381589 := bbase (se 6 (by rfl) ⟨665193, by rfl⟩ : syracuseStep 28381589 = 1330387) (by norm_num)
theorem B18921059 : Blo 2125435 18921059 := bstep (se 1 (by rfl) ⟨14190794, by rfl⟩ : syracuseStep 18921059 = 28381589) B28381589
theorem B12614039 : Blo 2125435 12614039 := bstep (se 1 (by rfl) ⟨9460529, by rfl⟩ : syracuseStep 12614039 = 18921059) B18921059
theorem B8409359 : Blo 2125435 8409359 := bstep (se 1 (by rfl) ⟨6307019, by rfl⟩ : syracuseStep 8409359 = 12614039) B12614039
theorem B22424957 : Blo 2125435 22424957 := bstep (se 3 (by rfl) ⟨4204679, by rfl⟩ : syracuseStep 22424957 = 8409359) B8409359
theorem B14949971 : Blo 2125435 14949971 := bstep (se 1 (by rfl) ⟨11212478, by rfl⟩ : syracuseStep 14949971 = 22424957) B22424957
theorem B9966647 : Blo 2125435 9966647 := bstep (se 1 (by rfl) ⟨7474985, by rfl⟩ : syracuseStep 9966647 = 14949971) B14949971
theorem B6644431 : Blo 2125435 6644431 := bstep (se 1 (by rfl) ⟨4983323, by rfl⟩ : syracuseStep 6644431 = 9966647) B9966647
theorem B8859241 : Blo 2125435 8859241 := bstep (se 2 (by rfl) ⟨3322215, by rfl⟩ : syracuseStep 8859241 = 6644431) B6644431
theorem B11812321 : Blo 2125435 11812321 := bstep (se 2 (by rfl) ⟨4429620, by rfl⟩ : syracuseStep 11812321 = 8859241) B8859241
theorem B15749761 : Blo 2125435 15749761 := bstep (se 2 (by rfl) ⟨5906160, by rfl⟩ : syracuseStep 15749761 = 11812321) B11812321
theorem B20999681 : Blo 2125435 20999681 := bstep (se 2 (by rfl) ⟨7874880, by rfl⟩ : syracuseStep 20999681 = 15749761) B15749761
theorem B13999787 : Blo 2125435 13999787 := bstep (se 1 (by rfl) ⟨10499840, by rfl⟩ : syracuseStep 13999787 = 20999681) B20999681
theorem B9333191 : Blo 2125435 9333191 := bstep (se 1 (by rfl) ⟨6999893, by rfl⟩ : syracuseStep 9333191 = 13999787) B13999787
theorem B24888509 : Blo 2125435 24888509 := bstep (se 3 (by rfl) ⟨4666595, by rfl⟩ : syracuseStep 24888509 = 9333191) B9333191
theorem B16592339 : Blo 2125435 16592339 := bstep (se 1 (by rfl) ⟨12444254, by rfl⟩ : syracuseStep 16592339 = 24888509) B24888509
theorem B11061559 : Blo 2125435 11061559 := bstep (se 1 (by rfl) ⟨8296169, by rfl⟩ : syracuseStep 11061559 = 16592339) B16592339
theorem B14748745 : Blo 2125435 14748745 := bstep (se 2 (by rfl) ⟨5530779, by rfl⟩ : syracuseStep 14748745 = 11061559) B11061559
theorem B19664993 : Blo 2125435 19664993 := bstep (se 2 (by rfl) ⟨7374372, by rfl⟩ : syracuseStep 19664993 = 14748745) B14748745
theorem B13109995 : Blo 2125435 13109995 := bstep (se 1 (by rfl) ⟨9832496, by rfl⟩ : syracuseStep 13109995 = 19664993) B19664993
theorem B17479993 : Blo 2125435 17479993 := bstep (se 2 (by rfl) ⟨6554997, by rfl⟩ : syracuseStep 17479993 = 13109995) B13109995
theorem B23306657 : Blo 2125435 23306657 := bstep (se 2 (by rfl) ⟨8739996, by rfl⟩ : syracuseStep 23306657 = 17479993) B17479993
theorem B62151085 : Blo 2125435 62151085 := bstep (se 3 (by rfl) ⟨11653328, by rfl⟩ : syracuseStep 62151085 = 23306657) B23306657
theorem B82868113 : Blo 2125435 82868113 := bstep (se 2 (by rfl) ⟨31075542, by rfl⟩ : syracuseStep 82868113 = 62151085) B62151085
theorem B110490817 : Blo 2125435 110490817 := bstep (se 2 (by rfl) ⟨41434056, by rfl⟩ : syracuseStep 110490817 = 82868113) B82868113
theorem B147321089 : Blo 2125435 147321089 := bstep (se 2 (by rfl) ⟨55245408, by rfl⟩ : syracuseStep 147321089 = 110490817) B110490817
theorem B98214059 : Blo 2125435 98214059 := bstep (se 1 (by rfl) ⟨73660544, by rfl⟩ : syracuseStep 98214059 = 147321089) B147321089
theorem B65476039 : Blo 2125435 65476039 := bstep (se 1 (by rfl) ⟨49107029, by rfl⟩ : syracuseStep 65476039 = 98214059) B98214059
theorem B87301385 : Blo 2125435 87301385 := bstep (se 2 (by rfl) ⟨32738019, by rfl⟩ : syracuseStep 87301385 = 65476039) B65476039
theorem B58200923 : Blo 2125435 58200923 := bstep (se 1 (by rfl) ⟨43650692, by rfl⟩ : syracuseStep 58200923 = 87301385) B87301385
theorem B38800615 : Blo 2125435 38800615 := bstep (se 1 (by rfl) ⟨29100461, by rfl⟩ : syracuseStep 38800615 = 58200923) B58200923
theorem B51734153 : Blo 2125435 51734153 := bstep (se 2 (by rfl) ⟨19400307, by rfl⟩ : syracuseStep 51734153 = 38800615) B38800615
theorem B34489435 : Blo 2125435 34489435 := bstep (se 1 (by rfl) ⟨25867076, by rfl⟩ : syracuseStep 34489435 = 51734153) B51734153
theorem B45985913 : Blo 2125435 45985913 := bstep (se 2 (by rfl) ⟨17244717, by rfl⟩ : syracuseStep 45985913 = 34489435) B34489435
theorem B30657275 : Blo 2125435 30657275 := bstep (se 1 (by rfl) ⟨22992956, by rfl⟩ : syracuseStep 30657275 = 45985913) B45985913
theorem B20438183 : Blo 2125435 20438183 := bstep (se 1 (by rfl) ⟨15328637, by rfl⟩ : syracuseStep 20438183 = 30657275) B30657275
theorem B13625455 : Blo 2125435 13625455 := bstep (se 1 (by rfl) ⟨10219091, by rfl⟩ : syracuseStep 13625455 = 20438183) B20438183
theorem B18167273 : Blo 2125435 18167273 := bstep (se 2 (by rfl) ⟨6812727, by rfl⟩ : syracuseStep 18167273 = 13625455) B13625455
theorem B12111515 : Blo 2125435 12111515 := bstep (se 1 (by rfl) ⟨9083636, by rfl⟩ : syracuseStep 12111515 = 18167273) B18167273
theorem B8074343 : Blo 2125435 8074343 := bstep (se 1 (by rfl) ⟨6055757, by rfl⟩ : syracuseStep 8074343 = 12111515) B12111515
theorem B5382895 : Blo 2125435 5382895 := bstep (se 1 (by rfl) ⟨4037171, by rfl⟩ : syracuseStep 5382895 = 8074343) B8074343
theorem B7177193 : Blo 2125435 7177193 := bstep (se 2 (by rfl) ⟨2691447, by rfl⟩ : syracuseStep 7177193 = 5382895) B5382895
theorem B4784795 : Blo 2125435 4784795 := bstep (se 1 (by rfl) ⟨3588596, by rfl⟩ : syracuseStep 4784795 = 7177193) B7177193
theorem B3189863 : Blo 2125435 3189863 := bstep (se 1 (by rfl) ⟨2392397, by rfl⟩ : syracuseStep 3189863 = 4784795) B4784795
theorem B2126575 : Blo 2125435 2126575 := bstep (se 1 (by rfl) ⟨1594931, by rfl⟩ : syracuseStep 2126575 = 3189863) B3189863
theorem B3189869 : Blo 2125435 3189869 := bbase (se 3 (by rfl) ⟨598100, by rfl⟩ : syracuseStep 3189869 = 1196201) (by norm_num)
theorem B2126579 : Blo 2125435 2126579 := bstep (se 1 (by rfl) ⟨1594934, by rfl⟩ : syracuseStep 2126579 = 3189869) B3189869
theorem B4784813 : Blo 2125435 4784813 := bbase (se 3 (by rfl) ⟨897152, by rfl⟩ : syracuseStep 4784813 = 1794305) (by norm_num)
theorem B3189875 : Blo 2125435 3189875 := bstep (se 1 (by rfl) ⟨2392406, by rfl⟩ : syracuseStep 3189875 = 4784813) B4784813
theorem B2126583 : Blo 2125435 2126583 := bstep (se 1 (by rfl) ⟨1594937, by rfl⟩ : syracuseStep 2126583 = 3189875) B3189875
theorem B4541845 : Blo 2125435 4541845 := bbase (se 6 (by rfl) ⟨106449, by rfl⟩ : syracuseStep 4541845 = 212899) (by norm_num)
theorem B6055793 : Blo 2125435 6055793 := bstep (se 2 (by rfl) ⟨2270922, by rfl⟩ : syracuseStep 6055793 = 4541845) B4541845
theorem B4037195 : Blo 2125435 4037195 := bstep (se 1 (by rfl) ⟨3027896, by rfl⟩ : syracuseStep 4037195 = 6055793) B6055793
theorem B2691463 : Blo 2125435 2691463 := bstep (se 1 (by rfl) ⟨2018597, by rfl⟩ : syracuseStep 2691463 = 4037195) B4037195
theorem B3588617 : Blo 2125435 3588617 := bstep (se 2 (by rfl) ⟨1345731, by rfl⟩ : syracuseStep 3588617 = 2691463) B2691463
theorem B2392411 : Blo 2125435 2392411 := bstep (se 1 (by rfl) ⟨1794308, by rfl⟩ : syracuseStep 2392411 = 3588617) B3588617
theorem B3189881 : Blo 2125435 3189881 := bstep (se 2 (by rfl) ⟨1196205, by rfl⟩ : syracuseStep 3189881 = 2392411) B2392411
theorem B2126587 : Blo 2125435 2126587 := bstep (se 1 (by rfl) ⟨1594940, by rfl⟩ : syracuseStep 2126587 = 3189881) B3189881
theorem B15964757 : Blo 2125435 15964757 := bbase (se 8 (by rfl) ⟨93543, by rfl⟩ : syracuseStep 15964757 = 187087) (by norm_num)
theorem B10643171 : Blo 2125435 10643171 := bstep (se 1 (by rfl) ⟨7982378, by rfl⟩ : syracuseStep 10643171 = 15964757) B15964757
theorem B28381789 : Blo 2125435 28381789 := bstep (se 3 (by rfl) ⟨5321585, by rfl⟩ : syracuseStep 28381789 = 10643171) B10643171
theorem B37842385 : Blo 2125435 37842385 := bstep (se 2 (by rfl) ⟨14190894, by rfl⟩ : syracuseStep 37842385 = 28381789) B28381789
theorem B50456513 : Blo 2125435 50456513 := bstep (se 2 (by rfl) ⟨18921192, by rfl⟩ : syracuseStep 50456513 = 37842385) B37842385
theorem B33637675 : Blo 2125435 33637675 := bstep (se 1 (by rfl) ⟨25228256, by rfl⟩ : syracuseStep 33637675 = 50456513) B50456513
theorem B44850233 : Blo 2125435 44850233 := bstep (se 2 (by rfl) ⟨16818837, by rfl⟩ : syracuseStep 44850233 = 33637675) B33637675
theorem B119600621 : Blo 2125435 119600621 := bstep (se 3 (by rfl) ⟨22425116, by rfl⟩ : syracuseStep 119600621 = 44850233) B44850233
theorem B79733747 : Blo 2125435 79733747 := bstep (se 1 (by rfl) ⟨59800310, by rfl⟩ : syracuseStep 79733747 = 119600621) B119600621
theorem B53155831 : Blo 2125435 53155831 := bstep (se 1 (by rfl) ⟨39866873, by rfl⟩ : syracuseStep 53155831 = 79733747) B79733747
theorem B70874441 : Blo 2125435 70874441 := bstep (se 2 (by rfl) ⟨26577915, by rfl⟩ : syracuseStep 70874441 = 53155831) B53155831
theorem B47249627 : Blo 2125435 47249627 := bstep (se 1 (by rfl) ⟨35437220, by rfl⟩ : syracuseStep 47249627 = 70874441) B70874441
theorem B125999005 : Blo 2125435 125999005 := bstep (se 3 (by rfl) ⟨23624813, by rfl⟩ : syracuseStep 125999005 = 47249627) B47249627
theorem B167998673 : Blo 2125435 167998673 := bstep (se 2 (by rfl) ⟨62999502, by rfl⟩ : syracuseStep 167998673 = 125999005) B125999005
theorem B111999115 : Blo 2125435 111999115 := bstep (se 1 (by rfl) ⟨83999336, by rfl⟩ : syracuseStep 111999115 = 167998673) B167998673
theorem B597328613 : Blo 2125435 597328613 := bstep (se 4 (by rfl) ⟨55999557, by rfl⟩ : syracuseStep 597328613 = 111999115) B111999115
theorem B398219075 : Blo 2125435 398219075 := bstep (se 1 (by rfl) ⟨298664306, by rfl⟩ : syracuseStep 398219075 = 597328613) B597328613
theorem B265479383 : Blo 2125435 265479383 := bstep (se 1 (by rfl) ⟨199109537, by rfl⟩ : syracuseStep 265479383 = 398219075) B398219075
theorem B176986255 : Blo 2125435 176986255 := bstep (se 1 (by rfl) ⟨132739691, by rfl⟩ : syracuseStep 176986255 = 265479383) B265479383
theorem B235981673 : Blo 2125435 235981673 := bstep (se 2 (by rfl) ⟨88493127, by rfl⟩ : syracuseStep 235981673 = 176986255) B176986255
theorem B157321115 : Blo 2125435 157321115 := bstep (se 1 (by rfl) ⟨117990836, by rfl⟩ : syracuseStep 157321115 = 235981673) B235981673
theorem B104880743 : Blo 2125435 104880743 := bstep (se 1 (by rfl) ⟨78660557, by rfl⟩ : syracuseStep 104880743 = 157321115) B157321115
theorem B69920495 : Blo 2125435 69920495 := bstep (se 1 (by rfl) ⟨52440371, by rfl⟩ : syracuseStep 69920495 = 104880743) B104880743
theorem B46613663 : Blo 2125435 46613663 := bstep (se 1 (by rfl) ⟨34960247, by rfl⟩ : syracuseStep 46613663 = 69920495) B69920495
theorem B31075775 : Blo 2125435 31075775 := bstep (se 1 (by rfl) ⟨23306831, by rfl⟩ : syracuseStep 31075775 = 46613663) B46613663
theorem B20717183 : Blo 2125435 20717183 := bstep (se 1 (by rfl) ⟨15537887, by rfl⟩ : syracuseStep 20717183 = 31075775) B31075775
theorem B13811455 : Blo 2125435 13811455 := bstep (se 1 (by rfl) ⟨10358591, by rfl⟩ : syracuseStep 13811455 = 20717183) B20717183
theorem B18415273 : Blo 2125435 18415273 := bstep (se 2 (by rfl) ⟨6905727, by rfl⟩ : syracuseStep 18415273 = 13811455) B13811455
theorem B24553697 : Blo 2125435 24553697 := bstep (se 2 (by rfl) ⟨9207636, by rfl⟩ : syracuseStep 24553697 = 18415273) B18415273
theorem B65476525 : Blo 2125435 65476525 := bstep (se 3 (by rfl) ⟨12276848, by rfl⟩ : syracuseStep 65476525 = 24553697) B24553697
theorem B87302033 : Blo 2125435 87302033 := bstep (se 2 (by rfl) ⟨32738262, by rfl⟩ : syracuseStep 87302033 = 65476525) B65476525
theorem B58201355 : Blo 2125435 58201355 := bstep (se 1 (by rfl) ⟨43651016, by rfl⟩ : syracuseStep 58201355 = 87302033) B87302033
theorem B155203613 : Blo 2125435 155203613 := bstep (se 3 (by rfl) ⟨29100677, by rfl⟩ : syracuseStep 155203613 = 58201355) B58201355
theorem B103469075 : Blo 2125435 103469075 := bstep (se 1 (by rfl) ⟨77601806, by rfl⟩ : syracuseStep 103469075 = 155203613) B155203613
theorem B68979383 : Blo 2125435 68979383 := bstep (se 1 (by rfl) ⟨51734537, by rfl⟩ : syracuseStep 68979383 = 103469075) B103469075
theorem B45986255 : Blo 2125435 45986255 := bstep (se 1 (by rfl) ⟨34489691, by rfl⟩ : syracuseStep 45986255 = 68979383) B68979383
theorem B30657503 : Blo 2125435 30657503 := bstep (se 1 (by rfl) ⟨22993127, by rfl⟩ : syracuseStep 30657503 = 45986255) B45986255
theorem B20438335 : Blo 2125435 20438335 := bstep (se 1 (by rfl) ⟨15328751, by rfl⟩ : syracuseStep 20438335 = 30657503) B30657503
theorem B27251113 : Blo 2125435 27251113 := bstep (se 2 (by rfl) ⟨10219167, by rfl⟩ : syracuseStep 27251113 = 20438335) B20438335
theorem B36334817 : Blo 2125435 36334817 := bstep (se 2 (by rfl) ⟨13625556, by rfl⟩ : syracuseStep 36334817 = 27251113) B27251113
theorem B24223211 : Blo 2125435 24223211 := bstep (se 1 (by rfl) ⟨18167408, by rfl⟩ : syracuseStep 24223211 = 36334817) B36334817
theorem B16148807 : Blo 2125435 16148807 := bstep (se 1 (by rfl) ⟨12111605, by rfl⟩ : syracuseStep 16148807 = 24223211) B24223211
theorem B10765871 : Blo 2125435 10765871 := bstep (se 1 (by rfl) ⟨8074403, by rfl⟩ : syracuseStep 10765871 = 16148807) B16148807
theorem B7177247 : Blo 2125435 7177247 := bstep (se 1 (by rfl) ⟨5382935, by rfl⟩ : syracuseStep 7177247 = 10765871) B10765871
theorem B4784831 : Blo 2125435 4784831 := bstep (se 1 (by rfl) ⟨3588623, by rfl⟩ : syracuseStep 4784831 = 7177247) B7177247
theorem B3189887 : Blo 2125435 3189887 := bstep (se 1 (by rfl) ⟨2392415, by rfl⟩ : syracuseStep 3189887 = 4784831) B4784831
theorem B2126591 : Blo 2125435 2126591 := bstep (se 1 (by rfl) ⟨1594943, by rfl⟩ : syracuseStep 2126591 = 3189887) B3189887
theorem B3189893 : Blo 2125435 3189893 := bbase (se 4 (by rfl) ⟨299052, by rfl⟩ : syracuseStep 3189893 = 598105) (by norm_num)
theorem B2126595 : Blo 2125435 2126595 := bstep (se 1 (by rfl) ⟨1594946, by rfl⟩ : syracuseStep 2126595 = 3189893) B3189893
theorem B3588637 : Blo 2125435 3588637 := bbase (se 3 (by rfl) ⟨672869, by rfl⟩ : syracuseStep 3588637 = 1345739) (by norm_num)
theorem B4784849 : Blo 2125435 4784849 := bstep (se 2 (by rfl) ⟨1794318, by rfl⟩ : syracuseStep 4784849 = 3588637) B3588637
theorem B3189899 : Blo 2125435 3189899 := bstep (se 1 (by rfl) ⟨2392424, by rfl⟩ : syracuseStep 3189899 = 4784849) B4784849
theorem B2126599 : Blo 2125435 2126599 := bstep (se 1 (by rfl) ⟨1594949, by rfl⟩ : syracuseStep 2126599 = 3189899) B3189899
theorem B2392429 : Blo 2125435 2392429 := bbase (se 3 (by rfl) ⟨448580, by rfl⟩ : syracuseStep 2392429 = 897161) (by norm_num)
theorem B3189905 : Blo 2125435 3189905 := bstep (se 2 (by rfl) ⟨1196214, by rfl⟩ : syracuseStep 3189905 = 2392429) B2392429
theorem B2126603 : Blo 2125435 2126603 := bstep (se 1 (by rfl) ⟨1594952, by rfl⟩ : syracuseStep 2126603 = 3189905) B3189905
theorem B7177301 : Blo 2125435 7177301 := bbase (se 8 (by rfl) ⟨42054, by rfl⟩ : syracuseStep 7177301 = 84109) (by norm_num)
theorem B4784867 : Blo 2125435 4784867 := bstep (se 1 (by rfl) ⟨3588650, by rfl⟩ : syracuseStep 4784867 = 7177301) B7177301
theorem B3189911 : Blo 2125435 3189911 := bstep (se 1 (by rfl) ⟨2392433, by rfl⟩ : syracuseStep 3189911 = 4784867) B4784867
theorem B2126607 : Blo 2125435 2126607 := bstep (se 1 (by rfl) ⟨1594955, by rfl⟩ : syracuseStep 2126607 = 3189911) B3189911
theorem B3189917 : Blo 2125435 3189917 := bbase (se 3 (by rfl) ⟨598109, by rfl⟩ : syracuseStep 3189917 = 1196219) (by norm_num)
theorem B2126611 : Blo 2125435 2126611 := bstep (se 1 (by rfl) ⟨1594958, by rfl⟩ : syracuseStep 2126611 = 3189917) B3189917
theorem B4784885 : Blo 2125435 4784885 := bbase (se 5 (by rfl) ⟨224291, by rfl⟩ : syracuseStep 4784885 = 448583) (by norm_num)
theorem B3189923 : Blo 2125435 3189923 := bstep (se 1 (by rfl) ⟨2392442, by rfl⟩ : syracuseStep 3189923 = 4784885) B4784885
theorem B2126615 : Blo 2125435 2126615 := bstep (se 1 (by rfl) ⟨1594961, by rfl⟩ : syracuseStep 2126615 = 3189923) B3189923
theorem B27251477 : Blo 2125435 27251477 := bbase (se 6 (by rfl) ⟨638706, by rfl⟩ : syracuseStep 27251477 = 1277413) (by norm_num)
theorem B18167651 : Blo 2125435 18167651 := bstep (se 1 (by rfl) ⟨13625738, by rfl⟩ : syracuseStep 18167651 = 27251477) B27251477
theorem B12111767 : Blo 2125435 12111767 := bstep (se 1 (by rfl) ⟨9083825, by rfl⟩ : syracuseStep 12111767 = 18167651) B18167651
theorem B8074511 : Blo 2125435 8074511 := bstep (se 1 (by rfl) ⟨6055883, by rfl⟩ : syracuseStep 8074511 = 12111767) B12111767
theorem B5383007 : Blo 2125435 5383007 := bstep (se 1 (by rfl) ⟨4037255, by rfl⟩ : syracuseStep 5383007 = 8074511) B8074511
theorem B3588671 : Blo 2125435 3588671 := bstep (se 1 (by rfl) ⟨2691503, by rfl⟩ : syracuseStep 3588671 = 5383007) B5383007
theorem B2392447 : Blo 2125435 2392447 := bstep (se 1 (by rfl) ⟨1794335, by rfl⟩ : syracuseStep 2392447 = 3588671) B3588671
theorem B3189929 : Blo 2125435 3189929 := bstep (se 2 (by rfl) ⟨1196223, by rfl⟩ : syracuseStep 3189929 = 2392447) B2392447
theorem B2126619 : Blo 2125435 2126619 := bstep (se 1 (by rfl) ⟨1594964, by rfl⟩ : syracuseStep 2126619 = 3189929) B3189929
theorem B4850189 : Blo 2125435 4850189 := bbase (se 3 (by rfl) ⟨909410, by rfl⟩ : syracuseStep 4850189 = 1818821) (by norm_num)
theorem B3233459 : Blo 2125435 3233459 := bstep (se 1 (by rfl) ⟨2425094, by rfl⟩ : syracuseStep 3233459 = 4850189) B4850189
theorem B8622557 : Blo 2125435 8622557 := bstep (se 3 (by rfl) ⟨1616729, by rfl⟩ : syracuseStep 8622557 = 3233459) B3233459
theorem B5748371 : Blo 2125435 5748371 := bstep (se 1 (by rfl) ⟨4311278, by rfl⟩ : syracuseStep 5748371 = 8622557) B8622557
theorem B3832247 : Blo 2125435 3832247 := bstep (se 1 (by rfl) ⟨2874185, by rfl⟩ : syracuseStep 3832247 = 5748371) B5748371
theorem B2554831 : Blo 2125435 2554831 := bstep (se 1 (by rfl) ⟨1916123, by rfl⟩ : syracuseStep 2554831 = 3832247) B3832247
theorem B3406441 : Blo 2125435 3406441 := bstep (se 2 (by rfl) ⟨1277415, by rfl⟩ : syracuseStep 3406441 = 2554831) B2554831
theorem B4541921 : Blo 2125435 4541921 := bstep (se 2 (by rfl) ⟨1703220, by rfl⟩ : syracuseStep 4541921 = 3406441) B3406441
theorem B3027947 : Blo 2125435 3027947 := bstep (se 1 (by rfl) ⟨2270960, by rfl⟩ : syracuseStep 3027947 = 4541921) B4541921
theorem B8074525 : Blo 2125435 8074525 := bstep (se 3 (by rfl) ⟨1513973, by rfl⟩ : syracuseStep 8074525 = 3027947) B3027947
theorem B10766033 : Blo 2125435 10766033 := bstep (se 2 (by rfl) ⟨4037262, by rfl⟩ : syracuseStep 10766033 = 8074525) B8074525
theorem B7177355 : Blo 2125435 7177355 := bstep (se 1 (by rfl) ⟨5383016, by rfl⟩ : syracuseStep 7177355 = 10766033) B10766033
theorem B4784903 : Blo 2125435 4784903 := bstep (se 1 (by rfl) ⟨3588677, by rfl⟩ : syracuseStep 4784903 = 7177355) B7177355
theorem B3189935 : Blo 2125435 3189935 := bstep (se 1 (by rfl) ⟨2392451, by rfl⟩ : syracuseStep 3189935 = 4784903) B4784903
theorem B2126623 : Blo 2125435 2126623 := bstep (se 1 (by rfl) ⟨1594967, by rfl⟩ : syracuseStep 2126623 = 3189935) B3189935
theorem B3189941 : Blo 2125435 3189941 := bbase (se 5 (by rfl) ⟨149528, by rfl⟩ : syracuseStep 3189941 = 299057) (by norm_num)
theorem B2126627 : Blo 2125435 2126627 := bstep (se 1 (by rfl) ⟨1594970, by rfl⟩ : syracuseStep 2126627 = 3189941) B3189941
theorem B5383037 : Blo 2125435 5383037 := bbase (se 3 (by rfl) ⟨1009319, by rfl⟩ : syracuseStep 5383037 = 2018639) (by norm_num)
theorem B3588691 : Blo 2125435 3588691 := bstep (se 1 (by rfl) ⟨2691518, by rfl⟩ : syracuseStep 3588691 = 5383037) B5383037
theorem B4784921 : Blo 2125435 4784921 := bstep (se 2 (by rfl) ⟨1794345, by rfl⟩ : syracuseStep 4784921 = 3588691) B3588691
theorem B3189947 : Blo 2125435 3189947 := bstep (se 1 (by rfl) ⟨2392460, by rfl⟩ : syracuseStep 3189947 = 4784921) B4784921
theorem B2126631 : Blo 2125435 2126631 := bstep (se 1 (by rfl) ⟨1594973, by rfl⟩ : syracuseStep 2126631 = 3189947) B3189947
theorem B2392465 : Blo 2125435 2392465 := bbase (se 2 (by rfl) ⟨897174, by rfl⟩ : syracuseStep 2392465 = 1794349) (by norm_num)
theorem B3189953 : Blo 2125435 3189953 := bstep (se 2 (by rfl) ⟨1196232, by rfl⟩ : syracuseStep 3189953 = 2392465) B2392465
theorem B2126635 : Blo 2125435 2126635 := bstep (se 1 (by rfl) ⟨1594976, by rfl⟩ : syracuseStep 2126635 = 3189953) B3189953
theorem B4037293 : Blo 2125435 4037293 := bbase (se 3 (by rfl) ⟨756992, by rfl⟩ : syracuseStep 4037293 = 1513985) (by norm_num)
theorem B5383057 : Blo 2125435 5383057 := bstep (se 2 (by rfl) ⟨2018646, by rfl⟩ : syracuseStep 5383057 = 4037293) B4037293
theorem B7177409 : Blo 2125435 7177409 := bstep (se 2 (by rfl) ⟨2691528, by rfl⟩ : syracuseStep 7177409 = 5383057) B5383057
theorem B4784939 : Blo 2125435 4784939 := bstep (se 1 (by rfl) ⟨3588704, by rfl⟩ : syracuseStep 4784939 = 7177409) B7177409
theorem B3189959 : Blo 2125435 3189959 := bstep (se 1 (by rfl) ⟨2392469, by rfl⟩ : syracuseStep 3189959 = 4784939) B4784939
theorem B2126639 : Blo 2125435 2126639 := bstep (se 1 (by rfl) ⟨1594979, by rfl⟩ : syracuseStep 2126639 = 3189959) B3189959
theorem B3189965 : Blo 2125435 3189965 := bbase (se 3 (by rfl) ⟨598118, by rfl⟩ : syracuseStep 3189965 = 1196237) (by norm_num)
theorem B2126643 : Blo 2125435 2126643 := bstep (se 1 (by rfl) ⟨1594982, by rfl⟩ : syracuseStep 2126643 = 3189965) B3189965
theorem B4784957 : Blo 2125435 4784957 := bbase (se 3 (by rfl) ⟨897179, by rfl⟩ : syracuseStep 4784957 = 1794359) (by norm_num)
theorem B3189971 : Blo 2125435 3189971 := bstep (se 1 (by rfl) ⟨2392478, by rfl⟩ : syracuseStep 3189971 = 4784957) B4784957
theorem B2126647 : Blo 2125435 2126647 := bstep (se 1 (by rfl) ⟨1594985, by rfl⟩ : syracuseStep 2126647 = 3189971) B3189971
theorem B3588725 : Blo 2125435 3588725 := bbase (se 5 (by rfl) ⟨168221, by rfl⟩ : syracuseStep 3588725 = 336443) (by norm_num)
theorem B2392483 : Blo 2125435 2392483 := bstep (se 1 (by rfl) ⟨1794362, by rfl⟩ : syracuseStep 2392483 = 3588725) B3588725
theorem B3189977 : Blo 2125435 3189977 := bstep (se 2 (by rfl) ⟨1196241, by rfl⟩ : syracuseStep 3189977 = 2392483) B2392483
theorem B2126651 : Blo 2125435 2126651 := bstep (se 1 (by rfl) ⟨1594988, by rfl⟩ : syracuseStep 2126651 = 3189977) B3189977
theorem B4541989 : Blo 2125435 4541989 := bbase (se 4 (by rfl) ⟨425811, by rfl⟩ : syracuseStep 4541989 = 851623) (by norm_num)
theorem B6055985 : Blo 2125435 6055985 := bstep (se 2 (by rfl) ⟨2270994, by rfl⟩ : syracuseStep 6055985 = 4541989) B4541989
theorem B16149293 : Blo 2125435 16149293 := bstep (se 3 (by rfl) ⟨3027992, by rfl⟩ : syracuseStep 16149293 = 6055985) B6055985
theorem B10766195 : Blo 2125435 10766195 := bstep (se 1 (by rfl) ⟨8074646, by rfl⟩ : syracuseStep 10766195 = 16149293) B16149293
theorem B7177463 : Blo 2125435 7177463 := bstep (se 1 (by rfl) ⟨5383097, by rfl⟩ : syracuseStep 7177463 = 10766195) B10766195
theorem B4784975 : Blo 2125435 4784975 := bstep (se 1 (by rfl) ⟨3588731, by rfl⟩ : syracuseStep 4784975 = 7177463) B7177463
theorem B3189983 : Blo 2125435 3189983 := bstep (se 1 (by rfl) ⟨2392487, by rfl⟩ : syracuseStep 3189983 = 4784975) B4784975
theorem B2126655 : Blo 2125435 2126655 := bstep (se 1 (by rfl) ⟨1594991, by rfl⟩ : syracuseStep 2126655 = 3189983) B3189983
theorem B3189989 : Blo 2125435 3189989 := bbase (se 4 (by rfl) ⟨299061, by rfl⟩ : syracuseStep 3189989 = 598123) (by norm_num)
theorem B2126659 : Blo 2125435 2126659 := bstep (se 1 (by rfl) ⟨1594994, by rfl⟩ : syracuseStep 2126659 = 3189989) B3189989
theorem B4490245 : Blo 2125435 4490245 := bbase (se 4 (by rfl) ⟨420960, by rfl⟩ : syracuseStep 4490245 = 841921) (by norm_num)
theorem B5986993 : Blo 2125435 5986993 := bstep (se 2 (by rfl) ⟨2245122, by rfl⟩ : syracuseStep 5986993 = 4490245) B4490245
theorem B7982657 : Blo 2125435 7982657 := bstep (se 2 (by rfl) ⟨2993496, by rfl⟩ : syracuseStep 7982657 = 5986993) B5986993
theorem B5321771 : Blo 2125435 5321771 := bstep (se 1 (by rfl) ⟨3991328, by rfl⟩ : syracuseStep 5321771 = 7982657) B7982657
theorem B3547847 : Blo 2125435 3547847 := bstep (se 1 (by rfl) ⟨2660885, by rfl⟩ : syracuseStep 3547847 = 5321771) B5321771
theorem B9460925 : Blo 2125435 9460925 := bstep (se 3 (by rfl) ⟨1773923, by rfl⟩ : syracuseStep 9460925 = 3547847) B3547847
theorem B6307283 : Blo 2125435 6307283 := bstep (se 1 (by rfl) ⟨4730462, by rfl⟩ : syracuseStep 6307283 = 9460925) B9460925
theorem B4204855 : Blo 2125435 4204855 := bstep (se 1 (by rfl) ⟨3153641, by rfl⟩ : syracuseStep 4204855 = 6307283) B6307283
theorem B22425893 : Blo 2125435 22425893 := bstep (se 4 (by rfl) ⟨2102427, by rfl⟩ : syracuseStep 22425893 = 4204855) B4204855
theorem B14950595 : Blo 2125435 14950595 := bstep (se 1 (by rfl) ⟨11212946, by rfl⟩ : syracuseStep 14950595 = 22425893) B22425893
theorem B9967063 : Blo 2125435 9967063 := bstep (se 1 (by rfl) ⟨7475297, by rfl⟩ : syracuseStep 9967063 = 14950595) B14950595
theorem B13289417 : Blo 2125435 13289417 := bstep (se 2 (by rfl) ⟨4983531, by rfl⟩ : syracuseStep 13289417 = 9967063) B9967063
theorem B8859611 : Blo 2125435 8859611 := bstep (se 1 (by rfl) ⟨6644708, by rfl⟩ : syracuseStep 8859611 = 13289417) B13289417
theorem B5906407 : Blo 2125435 5906407 := bstep (se 1 (by rfl) ⟨4429805, by rfl⟩ : syracuseStep 5906407 = 8859611) B8859611
theorem B7875209 : Blo 2125435 7875209 := bstep (se 2 (by rfl) ⟨2953203, by rfl⟩ : syracuseStep 7875209 = 5906407) B5906407
theorem B21000557 : Blo 2125435 21000557 := bstep (se 3 (by rfl) ⟨3937604, by rfl⟩ : syracuseStep 21000557 = 7875209) B7875209
theorem B14000371 : Blo 2125435 14000371 := bstep (se 1 (by rfl) ⟨10500278, by rfl⟩ : syracuseStep 14000371 = 21000557) B21000557
theorem B74668645 : Blo 2125435 74668645 := bstep (se 4 (by rfl) ⟨7000185, by rfl⟩ : syracuseStep 74668645 = 14000371) B14000371
theorem B99558193 : Blo 2125435 99558193 := bstep (se 2 (by rfl) ⟨37334322, by rfl⟩ : syracuseStep 99558193 = 74668645) B74668645
theorem B132744257 : Blo 2125435 132744257 := bstep (se 2 (by rfl) ⟨49779096, by rfl⟩ : syracuseStep 132744257 = 99558193) B99558193
theorem B88496171 : Blo 2125435 88496171 := bstep (se 1 (by rfl) ⟨66372128, by rfl⟩ : syracuseStep 88496171 = 132744257) B132744257
theorem B58997447 : Blo 2125435 58997447 := bstep (se 1 (by rfl) ⟨44248085, by rfl⟩ : syracuseStep 58997447 = 88496171) B88496171
theorem B39331631 : Blo 2125435 39331631 := bstep (se 1 (by rfl) ⟨29498723, by rfl⟩ : syracuseStep 39331631 = 58997447) B58997447
theorem B26221087 : Blo 2125435 26221087 := bstep (se 1 (by rfl) ⟨19665815, by rfl⟩ : syracuseStep 26221087 = 39331631) B39331631
theorem B34961449 : Blo 2125435 34961449 := bstep (se 2 (by rfl) ⟨13110543, by rfl⟩ : syracuseStep 34961449 = 26221087) B26221087
theorem B46615265 : Blo 2125435 46615265 := bstep (se 2 (by rfl) ⟨17480724, by rfl⟩ : syracuseStep 46615265 = 34961449) B34961449
theorem B31076843 : Blo 2125435 31076843 := bstep (se 1 (by rfl) ⟨23307632, by rfl⟩ : syracuseStep 31076843 = 46615265) B46615265
theorem B82871581 : Blo 2125435 82871581 := bstep (se 3 (by rfl) ⟨15538421, by rfl⟩ : syracuseStep 82871581 = 31076843) B31076843
theorem B110495441 : Blo 2125435 110495441 := bstep (se 2 (by rfl) ⟨41435790, by rfl⟩ : syracuseStep 110495441 = 82871581) B82871581
theorem B73663627 : Blo 2125435 73663627 := bstep (se 1 (by rfl) ⟨55247720, by rfl⟩ : syracuseStep 73663627 = 110495441) B110495441
theorem B98218169 : Blo 2125435 98218169 := bstep (se 2 (by rfl) ⟨36831813, by rfl⟩ : syracuseStep 98218169 = 73663627) B73663627
theorem B65478779 : Blo 2125435 65478779 := bstep (se 1 (by rfl) ⟨49109084, by rfl⟩ : syracuseStep 65478779 = 98218169) B98218169
theorem B43652519 : Blo 2125435 43652519 := bstep (se 1 (by rfl) ⟨32739389, by rfl⟩ : syracuseStep 43652519 = 65478779) B65478779
theorem B29101679 : Blo 2125435 29101679 := bstep (se 1 (by rfl) ⟨21826259, by rfl⟩ : syracuseStep 29101679 = 43652519) B43652519
theorem B19401119 : Blo 2125435 19401119 := bstep (se 1 (by rfl) ⟨14550839, by rfl⟩ : syracuseStep 19401119 = 29101679) B29101679
theorem B12934079 : Blo 2125435 12934079 := bstep (se 1 (by rfl) ⟨9700559, by rfl⟩ : syracuseStep 12934079 = 19401119) B19401119
theorem B8622719 : Blo 2125435 8622719 := bstep (se 1 (by rfl) ⟨6467039, by rfl⟩ : syracuseStep 8622719 = 12934079) B12934079
theorem B5748479 : Blo 2125435 5748479 := bstep (se 1 (by rfl) ⟨4311359, by rfl⟩ : syracuseStep 5748479 = 8622719) B8622719
theorem B3832319 : Blo 2125435 3832319 := bstep (se 1 (by rfl) ⟨2874239, by rfl⟩ : syracuseStep 3832319 = 5748479) B5748479
theorem B10219517 : Blo 2125435 10219517 := bstep (se 3 (by rfl) ⟨1916159, by rfl⟩ : syracuseStep 10219517 = 3832319) B3832319
theorem B6813011 : Blo 2125435 6813011 := bstep (se 1 (by rfl) ⟨5109758, by rfl⟩ : syracuseStep 6813011 = 10219517) B10219517
theorem B4542007 : Blo 2125435 4542007 := bstep (se 1 (by rfl) ⟨3406505, by rfl⟩ : syracuseStep 4542007 = 6813011) B6813011
theorem B6056009 : Blo 2125435 6056009 := bstep (se 2 (by rfl) ⟨2271003, by rfl⟩ : syracuseStep 6056009 = 4542007) B4542007
theorem B4037339 : Blo 2125435 4037339 := bstep (se 1 (by rfl) ⟨3028004, by rfl⟩ : syracuseStep 4037339 = 6056009) B6056009
theorem B2691559 : Blo 2125435 2691559 := bstep (se 1 (by rfl) ⟨2018669, by rfl⟩ : syracuseStep 2691559 = 4037339) B4037339
theorem B3588745 : Blo 2125435 3588745 := bstep (se 2 (by rfl) ⟨1345779, by rfl⟩ : syracuseStep 3588745 = 2691559) B2691559
theorem B4784993 : Blo 2125435 4784993 := bstep (se 2 (by rfl) ⟨1794372, by rfl⟩ : syracuseStep 4784993 = 3588745) B3588745
theorem B3189995 : Blo 2125435 3189995 := bstep (se 1 (by rfl) ⟨2392496, by rfl⟩ : syracuseStep 3189995 = 4784993) B4784993
theorem B2126663 : Blo 2125435 2126663 := bstep (se 1 (by rfl) ⟨1594997, by rfl⟩ : syracuseStep 2126663 = 3189995) B3189995
theorem B2392501 : Blo 2125435 2392501 := bbase (se 5 (by rfl) ⟨112148, by rfl⟩ : syracuseStep 2392501 = 224297) (by norm_num)
theorem B3190001 : Blo 2125435 3190001 := bstep (se 2 (by rfl) ⟨1196250, by rfl⟩ : syracuseStep 3190001 = 2392501) B2392501
theorem B2126667 : Blo 2125435 2126667 := bstep (se 1 (by rfl) ⟨1595000, by rfl⟩ : syracuseStep 2126667 = 3190001) B3190001
theorem B2691569 : Blo 2125435 2691569 := bbase (se 2 (by rfl) ⟨1009338, by rfl⟩ : syracuseStep 2691569 = 2018677) (by norm_num)
theorem B7177517 : Blo 2125435 7177517 := bstep (se 3 (by rfl) ⟨1345784, by rfl⟩ : syracuseStep 7177517 = 2691569) B2691569
theorem B4785011 : Blo 2125435 4785011 := bstep (se 1 (by rfl) ⟨3588758, by rfl⟩ : syracuseStep 4785011 = 7177517) B7177517
theorem B3190007 : Blo 2125435 3190007 := bstep (se 1 (by rfl) ⟨2392505, by rfl⟩ : syracuseStep 3190007 = 4785011) B4785011
theorem B2126671 : Blo 2125435 2126671 := bstep (se 1 (by rfl) ⟨1595003, by rfl⟩ : syracuseStep 2126671 = 3190007) B3190007
theorem B3190013 : Blo 2125435 3190013 := bbase (se 3 (by rfl) ⟨598127, by rfl⟩ : syracuseStep 3190013 = 1196255) (by norm_num)
theorem B2126675 : Blo 2125435 2126675 := bstep (se 1 (by rfl) ⟨1595006, by rfl⟩ : syracuseStep 2126675 = 3190013) B3190013
theorem B4785029 : Blo 2125435 4785029 := bbase (se 4 (by rfl) ⟨448596, by rfl⟩ : syracuseStep 4785029 = 897193) (by norm_num)
theorem B3190019 : Blo 2125435 3190019 := bstep (se 1 (by rfl) ⟨2392514, by rfl⟩ : syracuseStep 3190019 = 4785029) B4785029
theorem B2126679 : Blo 2125435 2126679 := bstep (se 1 (by rfl) ⟨1595009, by rfl⟩ : syracuseStep 2126679 = 3190019) B3190019
theorem B2271025 : Blo 2125435 2271025 := bbase (se 2 (by rfl) ⟨851634, by rfl⟩ : syracuseStep 2271025 = 1703269) (by norm_num)
theorem B3028033 : Blo 2125435 3028033 := bstep (se 2 (by rfl) ⟨1135512, by rfl⟩ : syracuseStep 3028033 = 2271025) B2271025
theorem B4037377 : Blo 2125435 4037377 := bstep (se 2 (by rfl) ⟨1514016, by rfl⟩ : syracuseStep 4037377 = 3028033) B3028033
theorem B5383169 : Blo 2125435 5383169 := bstep (se 2 (by rfl) ⟨2018688, by rfl⟩ : syracuseStep 5383169 = 4037377) B4037377
theorem B3588779 : Blo 2125435 3588779 := bstep (se 1 (by rfl) ⟨2691584, by rfl⟩ : syracuseStep 3588779 = 5383169) B5383169
theorem B2392519 : Blo 2125435 2392519 := bstep (se 1 (by rfl) ⟨1794389, by rfl⟩ : syracuseStep 2392519 = 3588779) B3588779
theorem B3190025 : Blo 2125435 3190025 := bstep (se 2 (by rfl) ⟨1196259, by rfl⟩ : syracuseStep 3190025 = 2392519) B2392519
theorem B2126683 : Blo 2125435 2126683 := bstep (se 1 (by rfl) ⟨1595012, by rfl⟩ : syracuseStep 2126683 = 3190025) B3190025
theorem B10766357 : Blo 2125435 10766357 := bbase (se 6 (by rfl) ⟨252336, by rfl⟩ : syracuseStep 10766357 = 504673) (by norm_num)
theorem B7177571 : Blo 2125435 7177571 := bstep (se 1 (by rfl) ⟨5383178, by rfl⟩ : syracuseStep 7177571 = 10766357) B10766357
theorem B4785047 : Blo 2125435 4785047 := bstep (se 1 (by rfl) ⟨3588785, by rfl⟩ : syracuseStep 4785047 = 7177571) B7177571
theorem B3190031 : Blo 2125435 3190031 := bstep (se 1 (by rfl) ⟨2392523, by rfl⟩ : syracuseStep 3190031 = 4785047) B4785047
theorem B2126687 : Blo 2125435 2126687 := bstep (se 1 (by rfl) ⟨1595015, by rfl⟩ : syracuseStep 2126687 = 3190031) B3190031
theorem B3190037 : Blo 2125435 3190037 := bbase (se 6 (by rfl) ⟨74766, by rfl⟩ : syracuseStep 3190037 = 149533) (by norm_num)
theorem B2126691 : Blo 2125435 2126691 := bstep (se 1 (by rfl) ⟨1595018, by rfl⟩ : syracuseStep 2126691 = 3190037) B3190037
theorem B3277685 : Blo 2125435 3277685 := bbase (se 5 (by rfl) ⟨153641, by rfl⟩ : syracuseStep 3277685 = 307283) (by norm_num)
theorem B8740493 : Blo 2125435 8740493 := bstep (se 3 (by rfl) ⟨1638842, by rfl⟩ : syracuseStep 8740493 = 3277685) B3277685
theorem B5826995 : Blo 2125435 5826995 := bstep (se 1 (by rfl) ⟨4370246, by rfl⟩ : syracuseStep 5826995 = 8740493) B8740493
theorem B3884663 : Blo 2125435 3884663 := bstep (se 1 (by rfl) ⟨2913497, by rfl⟩ : syracuseStep 3884663 = 5826995) B5826995
theorem B2589775 : Blo 2125435 2589775 := bstep (se 1 (by rfl) ⟨1942331, by rfl⟩ : syracuseStep 2589775 = 3884663) B3884663
theorem B13812133 : Blo 2125435 13812133 := bstep (se 4 (by rfl) ⟨1294887, by rfl⟩ : syracuseStep 13812133 = 2589775) B2589775
theorem B18416177 : Blo 2125435 18416177 := bstep (se 2 (by rfl) ⟨6906066, by rfl⟩ : syracuseStep 18416177 = 13812133) B13812133
theorem B12277451 : Blo 2125435 12277451 := bstep (se 1 (by rfl) ⟨9208088, by rfl⟩ : syracuseStep 12277451 = 18416177) B18416177
theorem B32739869 : Blo 2125435 32739869 := bstep (se 3 (by rfl) ⟨6138725, by rfl⟩ : syracuseStep 32739869 = 12277451) B12277451
theorem B21826579 : Blo 2125435 21826579 := bstep (se 1 (by rfl) ⟨16369934, by rfl⟩ : syracuseStep 21826579 = 32739869) B32739869
theorem B29102105 : Blo 2125435 29102105 := bstep (se 2 (by rfl) ⟨10913289, by rfl⟩ : syracuseStep 29102105 = 21826579) B21826579
theorem B77605613 : Blo 2125435 77605613 := bstep (se 3 (by rfl) ⟨14551052, by rfl⟩ : syracuseStep 77605613 = 29102105) B29102105
theorem B51737075 : Blo 2125435 51737075 := bstep (se 1 (by rfl) ⟨38802806, by rfl⟩ : syracuseStep 51737075 = 77605613) B77605613
theorem B34491383 : Blo 2125435 34491383 := bstep (se 1 (by rfl) ⟨25868537, by rfl⟩ : syracuseStep 34491383 = 51737075) B51737075
theorem B22994255 : Blo 2125435 22994255 := bstep (se 1 (by rfl) ⟨17245691, by rfl⟩ : syracuseStep 22994255 = 34491383) B34491383
theorem B15329503 : Blo 2125435 15329503 := bstep (se 1 (by rfl) ⟨11497127, by rfl⟩ : syracuseStep 15329503 = 22994255) B22994255
theorem B20439337 : Blo 2125435 20439337 := bstep (se 2 (by rfl) ⟨7664751, by rfl⟩ : syracuseStep 20439337 = 15329503) B15329503
theorem B27252449 : Blo 2125435 27252449 := bstep (se 2 (by rfl) ⟨10219668, by rfl⟩ : syracuseStep 27252449 = 20439337) B20439337
theorem B18168299 : Blo 2125435 18168299 := bstep (se 1 (by rfl) ⟨13626224, by rfl⟩ : syracuseStep 18168299 = 27252449) B27252449
theorem B12112199 : Blo 2125435 12112199 := bstep (se 1 (by rfl) ⟨9084149, by rfl⟩ : syracuseStep 12112199 = 18168299) B18168299
theorem B8074799 : Blo 2125435 8074799 := bstep (se 1 (by rfl) ⟨6056099, by rfl⟩ : syracuseStep 8074799 = 12112199) B12112199
theorem B5383199 : Blo 2125435 5383199 := bstep (se 1 (by rfl) ⟨4037399, by rfl⟩ : syracuseStep 5383199 = 8074799) B8074799
theorem B3588799 : Blo 2125435 3588799 := bstep (se 1 (by rfl) ⟨2691599, by rfl⟩ : syracuseStep 3588799 = 5383199) B5383199
theorem B4785065 : Blo 2125435 4785065 := bstep (se 2 (by rfl) ⟨1794399, by rfl⟩ : syracuseStep 4785065 = 3588799) B3588799
theorem B3190043 : Blo 2125435 3190043 := bstep (se 1 (by rfl) ⟨2392532, by rfl⟩ : syracuseStep 3190043 = 4785065) B4785065
theorem B2126695 : Blo 2125435 2126695 := bstep (se 1 (by rfl) ⟨1595021, by rfl⟩ : syracuseStep 2126695 = 3190043) B3190043
theorem B2392537 : Blo 2125435 2392537 := bbase (se 2 (by rfl) ⟨897201, by rfl⟩ : syracuseStep 2392537 = 1794403) (by norm_num)
theorem B3190049 : Blo 2125435 3190049 := bstep (se 2 (by rfl) ⟨1196268, by rfl⟩ : syracuseStep 3190049 = 2392537) B2392537
theorem B2126699 : Blo 2125435 2126699 := bstep (se 1 (by rfl) ⟨1595024, by rfl⟩ : syracuseStep 2126699 = 3190049) B3190049
theorem B3028061 : Blo 2125435 3028061 := bbase (se 3 (by rfl) ⟨567761, by rfl⟩ : syracuseStep 3028061 = 1135523) (by norm_num)
theorem B8074829 : Blo 2125435 8074829 := bstep (se 3 (by rfl) ⟨1514030, by rfl⟩ : syracuseStep 8074829 = 3028061) B3028061
theorem B5383219 : Blo 2125435 5383219 := bstep (se 1 (by rfl) ⟨4037414, by rfl⟩ : syracuseStep 5383219 = 8074829) B8074829
theorem B7177625 : Blo 2125435 7177625 := bstep (se 2 (by rfl) ⟨2691609, by rfl⟩ : syracuseStep 7177625 = 5383219) B5383219
theorem B4785083 : Blo 2125435 4785083 := bstep (se 1 (by rfl) ⟨3588812, by rfl⟩ : syracuseStep 4785083 = 7177625) B7177625
theorem B3190055 : Blo 2125435 3190055 := bstep (se 1 (by rfl) ⟨2392541, by rfl⟩ : syracuseStep 3190055 = 4785083) B4785083
theorem B2126703 : Blo 2125435 2126703 := bstep (se 1 (by rfl) ⟨1595027, by rfl⟩ : syracuseStep 2126703 = 3190055) B3190055
theorem B3190061 : Blo 2125435 3190061 := bbase (se 3 (by rfl) ⟨598136, by rfl⟩ : syracuseStep 3190061 = 1196273) (by norm_num)
theorem B2126707 : Blo 2125435 2126707 := bstep (se 1 (by rfl) ⟨1595030, by rfl⟩ : syracuseStep 2126707 = 3190061) B3190061
theorem B4785101 : Blo 2125435 4785101 := bbase (se 3 (by rfl) ⟨897206, by rfl⟩ : syracuseStep 4785101 = 1794413) (by norm_num)
theorem B3190067 : Blo 2125435 3190067 := bstep (se 1 (by rfl) ⟨2392550, by rfl⟩ : syracuseStep 3190067 = 4785101) B4785101
theorem B2126711 : Blo 2125435 2126711 := bstep (se 1 (by rfl) ⟨1595033, by rfl⟩ : syracuseStep 2126711 = 3190067) B3190067
theorem B2691625 : Blo 2125435 2691625 := bbase (se 2 (by rfl) ⟨1009359, by rfl⟩ : syracuseStep 2691625 = 2018719) (by norm_num)
theorem B3588833 : Blo 2125435 3588833 := bstep (se 2 (by rfl) ⟨1345812, by rfl⟩ : syracuseStep 3588833 = 2691625) B2691625
theorem B2392555 : Blo 2125435 2392555 := bstep (se 1 (by rfl) ⟨1794416, by rfl⟩ : syracuseStep 2392555 = 3588833) B3588833
theorem B3190073 : Blo 2125435 3190073 := bstep (se 2 (by rfl) ⟨1196277, by rfl⟩ : syracuseStep 3190073 = 2392555) B2392555
theorem B2126715 : Blo 2125435 2126715 := bstep (se 1 (by rfl) ⟨1595036, by rfl⟩ : syracuseStep 2126715 = 3190073) B3190073
theorem B10913413 : Blo 2125435 10913413 := bbase (se 4 (by rfl) ⟨1023132, by rfl⟩ : syracuseStep 10913413 = 2046265) (by norm_num)
theorem B14551217 : Blo 2125435 14551217 := bstep (se 2 (by rfl) ⟨5456706, by rfl⟩ : syracuseStep 14551217 = 10913413) B10913413
theorem B9700811 : Blo 2125435 9700811 := bstep (se 1 (by rfl) ⟨7275608, by rfl⟩ : syracuseStep 9700811 = 14551217) B14551217
theorem B6467207 : Blo 2125435 6467207 := bstep (se 1 (by rfl) ⟨4850405, by rfl⟩ : syracuseStep 6467207 = 9700811) B9700811
theorem B17245885 : Blo 2125435 17245885 := bstep (se 3 (by rfl) ⟨3233603, by rfl⟩ : syracuseStep 17245885 = 6467207) B6467207
theorem B22994513 : Blo 2125435 22994513 := bstep (se 2 (by rfl) ⟨8622942, by rfl⟩ : syracuseStep 22994513 = 17245885) B17245885
theorem B15329675 : Blo 2125435 15329675 := bstep (se 1 (by rfl) ⟨11497256, by rfl⟩ : syracuseStep 15329675 = 22994513) B22994513
theorem B10219783 : Blo 2125435 10219783 := bstep (se 1 (by rfl) ⟨7664837, by rfl⟩ : syracuseStep 10219783 = 15329675) B15329675
theorem B13626377 : Blo 2125435 13626377 := bstep (se 2 (by rfl) ⟨5109891, by rfl⟩ : syracuseStep 13626377 = 10219783) B10219783
theorem B9084251 : Blo 2125435 9084251 := bstep (se 1 (by rfl) ⟨6813188, by rfl⟩ : syracuseStep 9084251 = 13626377) B13626377
theorem B24224669 : Blo 2125435 24224669 := bstep (se 3 (by rfl) ⟨4542125, by rfl⟩ : syracuseStep 24224669 = 9084251) B9084251
theorem B16149779 : Blo 2125435 16149779 := bstep (se 1 (by rfl) ⟨12112334, by rfl⟩ : syracuseStep 16149779 = 24224669) B24224669
theorem B10766519 : Blo 2125435 10766519 := bstep (se 1 (by rfl) ⟨8074889, by rfl⟩ : syracuseStep 10766519 = 16149779) B16149779
theorem B7177679 : Blo 2125435 7177679 := bstep (se 1 (by rfl) ⟨5383259, by rfl⟩ : syracuseStep 7177679 = 10766519) B10766519
theorem B4785119 : Blo 2125435 4785119 := bstep (se 1 (by rfl) ⟨3588839, by rfl⟩ : syracuseStep 4785119 = 7177679) B7177679
theorem B3190079 : Blo 2125435 3190079 := bstep (se 1 (by rfl) ⟨2392559, by rfl⟩ : syracuseStep 3190079 = 4785119) B4785119
theorem B2126719 : Blo 2125435 2126719 := bstep (se 1 (by rfl) ⟨1595039, by rfl⟩ : syracuseStep 2126719 = 3190079) B3190079
theorem B3190085 : Blo 2125435 3190085 := bbase (se 4 (by rfl) ⟨299070, by rfl⟩ : syracuseStep 3190085 = 598141) (by norm_num)
theorem B2126723 : Blo 2125435 2126723 := bstep (se 1 (by rfl) ⟨1595042, by rfl⟩ : syracuseStep 2126723 = 3190085) B3190085
theorem B3588853 : Blo 2125435 3588853 := bbase (se 5 (by rfl) ⟨168227, by rfl⟩ : syracuseStep 3588853 = 336455) (by norm_num)
theorem B4785137 : Blo 2125435 4785137 := bstep (se 2 (by rfl) ⟨1794426, by rfl⟩ : syracuseStep 4785137 = 3588853) B3588853
theorem B3190091 : Blo 2125435 3190091 := bstep (se 1 (by rfl) ⟨2392568, by rfl⟩ : syracuseStep 3190091 = 4785137) B4785137
theorem B2126727 : Blo 2125435 2126727 := bstep (se 1 (by rfl) ⟨1595045, by rfl⟩ : syracuseStep 2126727 = 3190091) B3190091
theorem B2392573 : Blo 2125435 2392573 := bbase (se 3 (by rfl) ⟨448607, by rfl⟩ : syracuseStep 2392573 = 897215) (by norm_num)
theorem B3190097 : Blo 2125435 3190097 := bstep (se 2 (by rfl) ⟨1196286, by rfl⟩ : syracuseStep 3190097 = 2392573) B2392573
theorem B2126731 : Blo 2125435 2126731 := bstep (se 1 (by rfl) ⟨1595048, by rfl⟩ : syracuseStep 2126731 = 3190097) B3190097
theorem B7177733 : Blo 2125435 7177733 := bbase (se 4 (by rfl) ⟨672912, by rfl⟩ : syracuseStep 7177733 = 1345825) (by norm_num)
theorem B4785155 : Blo 2125435 4785155 := bstep (se 1 (by rfl) ⟨3588866, by rfl⟩ : syracuseStep 4785155 = 7177733) B7177733
theorem B3190103 : Blo 2125435 3190103 := bstep (se 1 (by rfl) ⟨2392577, by rfl⟩ : syracuseStep 3190103 = 4785155) B4785155
theorem B2126735 : Blo 2125435 2126735 := bstep (se 1 (by rfl) ⟨1595051, by rfl⟩ : syracuseStep 2126735 = 3190103) B3190103
theorem B3190109 : Blo 2125435 3190109 := bbase (se 3 (by rfl) ⟨598145, by rfl⟩ : syracuseStep 3190109 = 1196291) (by norm_num)
theorem B2126739 : Blo 2125435 2126739 := bstep (se 1 (by rfl) ⟨1595054, by rfl⟩ : syracuseStep 2126739 = 3190109) B3190109
theorem B4785173 : Blo 2125435 4785173 := bbase (se 6 (by rfl) ⟨112152, by rfl⟩ : syracuseStep 4785173 = 224305) (by norm_num)
theorem B3190115 : Blo 2125435 3190115 := bstep (se 1 (by rfl) ⟨2392586, by rfl⟩ : syracuseStep 3190115 = 4785173) B4785173
theorem B2126743 : Blo 2125435 2126743 := bstep (se 1 (by rfl) ⟨1595057, by rfl⟩ : syracuseStep 2126743 = 3190115) B3190115
theorem B8074997 : Blo 2125435 8074997 := bbase (se 5 (by rfl) ⟨378515, by rfl⟩ : syracuseStep 8074997 = 757031) (by norm_num)
theorem B5383331 : Blo 2125435 5383331 := bstep (se 1 (by rfl) ⟨4037498, by rfl⟩ : syracuseStep 5383331 = 8074997) B8074997
theorem B3588887 : Blo 2125435 3588887 := bstep (se 1 (by rfl) ⟨2691665, by rfl⟩ : syracuseStep 3588887 = 5383331) B5383331
theorem B2392591 : Blo 2125435 2392591 := bstep (se 1 (by rfl) ⟨1794443, by rfl⟩ : syracuseStep 2392591 = 3588887) B3588887
theorem B3190121 : Blo 2125435 3190121 := bstep (se 2 (by rfl) ⟨1196295, by rfl⟩ : syracuseStep 3190121 = 2392591) B2392591
theorem B2126747 : Blo 2125435 2126747 := bstep (se 1 (by rfl) ⟨1595060, by rfl⟩ : syracuseStep 2126747 = 3190121) B3190121
theorem B2271097 : Blo 2125435 2271097 := bbase (se 2 (by rfl) ⟨851661, by rfl⟩ : syracuseStep 2271097 = 1703323) (by norm_num)
theorem B12112517 : Blo 2125435 12112517 := bstep (se 4 (by rfl) ⟨1135548, by rfl⟩ : syracuseStep 12112517 = 2271097) B2271097
theorem B8075011 : Blo 2125435 8075011 := bstep (se 1 (by rfl) ⟨6056258, by rfl⟩ : syracuseStep 8075011 = 12112517) B12112517
theorem B10766681 : Blo 2125435 10766681 := bstep (se 2 (by rfl) ⟨4037505, by rfl⟩ : syracuseStep 10766681 = 8075011) B8075011
theorem B7177787 : Blo 2125435 7177787 := bstep (se 1 (by rfl) ⟨5383340, by rfl⟩ : syracuseStep 7177787 = 10766681) B10766681
theorem B4785191 : Blo 2125435 4785191 := bstep (se 1 (by rfl) ⟨3588893, by rfl⟩ : syracuseStep 4785191 = 7177787) B7177787
theorem B3190127 : Blo 2125435 3190127 := bstep (se 1 (by rfl) ⟨2392595, by rfl⟩ : syracuseStep 3190127 = 4785191) B4785191
theorem B2126751 : Blo 2125435 2126751 := bstep (se 1 (by rfl) ⟨1595063, by rfl⟩ : syracuseStep 2126751 = 3190127) B3190127
theorem B3190133 : Blo 2125435 3190133 := bbase (se 5 (by rfl) ⟨149537, by rfl⟩ : syracuseStep 3190133 = 299075) (by norm_num)
theorem B2126755 : Blo 2125435 2126755 := bstep (se 1 (by rfl) ⟨1595066, by rfl⟩ : syracuseStep 2126755 = 3190133) B3190133
theorem B3028141 : Blo 2125435 3028141 := bbase (se 3 (by rfl) ⟨567776, by rfl⟩ : syracuseStep 3028141 = 1135553) (by norm_num)
theorem B4037521 : Blo 2125435 4037521 := bstep (se 2 (by rfl) ⟨1514070, by rfl⟩ : syracuseStep 4037521 = 3028141) B3028141
theorem B5383361 : Blo 2125435 5383361 := bstep (se 2 (by rfl) ⟨2018760, by rfl⟩ : syracuseStep 5383361 = 4037521) B4037521
theorem B3588907 : Blo 2125435 3588907 := bstep (se 1 (by rfl) ⟨2691680, by rfl⟩ : syracuseStep 3588907 = 5383361) B5383361
theorem B4785209 : Blo 2125435 4785209 := bstep (se 2 (by rfl) ⟨1794453, by rfl⟩ : syracuseStep 4785209 = 3588907) B3588907
theorem B3190139 : Blo 2125435 3190139 := bstep (se 1 (by rfl) ⟨2392604, by rfl⟩ : syracuseStep 3190139 = 4785209) B4785209
theorem B2126759 : Blo 2125435 2126759 := bstep (se 1 (by rfl) ⟨1595069, by rfl⟩ : syracuseStep 2126759 = 3190139) B3190139
theorem B2392609 : Blo 2125435 2392609 := bbase (se 2 (by rfl) ⟨897228, by rfl⟩ : syracuseStep 2392609 = 1794457) (by norm_num)
theorem B3190145 : Blo 2125435 3190145 := bstep (se 2 (by rfl) ⟨1196304, by rfl⟩ : syracuseStep 3190145 = 2392609) B2392609
theorem B2126763 : Blo 2125435 2126763 := bstep (se 1 (by rfl) ⟨1595072, by rfl⟩ : syracuseStep 2126763 = 3190145) B3190145
theorem B5383381 : Blo 2125435 5383381 := bbase (se 7 (by rfl) ⟨63086, by rfl⟩ : syracuseStep 5383381 = 126173) (by norm_num)
theorem B7177841 : Blo 2125435 7177841 := bstep (se 2 (by rfl) ⟨2691690, by rfl⟩ : syracuseStep 7177841 = 5383381) B5383381
theorem B4785227 : Blo 2125435 4785227 := bstep (se 1 (by rfl) ⟨3588920, by rfl⟩ : syracuseStep 4785227 = 7177841) B7177841
theorem B3190151 : Blo 2125435 3190151 := bstep (se 1 (by rfl) ⟨2392613, by rfl⟩ : syracuseStep 3190151 = 4785227) B4785227
theorem B2126767 : Blo 2125435 2126767 := bstep (se 1 (by rfl) ⟨1595075, by rfl⟩ : syracuseStep 2126767 = 3190151) B3190151
theorem B3190157 : Blo 2125435 3190157 := bbase (se 3 (by rfl) ⟨598154, by rfl⟩ : syracuseStep 3190157 = 1196309) (by norm_num)
theorem B2126771 : Blo 2125435 2126771 := bstep (se 1 (by rfl) ⟨1595078, by rfl⟩ : syracuseStep 2126771 = 3190157) B3190157
theorem B4785245 : Blo 2125435 4785245 := bbase (se 3 (by rfl) ⟨897233, by rfl⟩ : syracuseStep 4785245 = 1794467) (by norm_num)
theorem B3190163 : Blo 2125435 3190163 := bstep (se 1 (by rfl) ⟨2392622, by rfl⟩ : syracuseStep 3190163 = 4785245) B4785245
theorem B2126775 : Blo 2125435 2126775 := bstep (se 1 (by rfl) ⟨1595081, by rfl⟩ : syracuseStep 2126775 = 3190163) B3190163
theorem B3588941 : Blo 2125435 3588941 := bbase (se 3 (by rfl) ⟨672926, by rfl⟩ : syracuseStep 3588941 = 1345853) (by norm_num)
theorem B2392627 : Blo 2125435 2392627 := bstep (se 1 (by rfl) ⟨1794470, by rfl⟩ : syracuseStep 2392627 = 3588941) B3588941
theorem B3190169 : Blo 2125435 3190169 := bstep (se 2 (by rfl) ⟨1196313, by rfl⟩ : syracuseStep 3190169 = 2392627) B2392627
theorem B2126779 : Blo 2125435 2126779 := bstep (se 1 (by rfl) ⟨1595084, by rfl⟩ : syracuseStep 2126779 = 3190169) B3190169
theorem B20440181 : Blo 2125435 20440181 := bbase (se 5 (by rfl) ⟨958133, by rfl⟩ : syracuseStep 20440181 = 1916267) (by norm_num)
theorem B13626787 : Blo 2125435 13626787 := bstep (se 1 (by rfl) ⟨10220090, by rfl⟩ : syracuseStep 13626787 = 20440181) B20440181
theorem B18169049 : Blo 2125435 18169049 := bstep (se 2 (by rfl) ⟨6813393, by rfl⟩ : syracuseStep 18169049 = 13626787) B13626787
theorem B12112699 : Blo 2125435 12112699 := bstep (se 1 (by rfl) ⟨9084524, by rfl⟩ : syracuseStep 12112699 = 18169049) B18169049
theorem B16150265 : Blo 2125435 16150265 := bstep (se 2 (by rfl) ⟨6056349, by rfl⟩ : syracuseStep 16150265 = 12112699) B12112699
theorem B10766843 : Blo 2125435 10766843 := bstep (se 1 (by rfl) ⟨8075132, by rfl⟩ : syracuseStep 10766843 = 16150265) B16150265
theorem B7177895 : Blo 2125435 7177895 := bstep (se 1 (by rfl) ⟨5383421, by rfl⟩ : syracuseStep 7177895 = 10766843) B10766843
theorem B4785263 : Blo 2125435 4785263 := bstep (se 1 (by rfl) ⟨3588947, by rfl⟩ : syracuseStep 4785263 = 7177895) B7177895
theorem B3190175 : Blo 2125435 3190175 := bstep (se 1 (by rfl) ⟨2392631, by rfl⟩ : syracuseStep 3190175 = 4785263) B4785263
theorem B2126783 : Blo 2125435 2126783 := bstep (se 1 (by rfl) ⟨1595087, by rfl⟩ : syracuseStep 2126783 = 3190175) B3190175
theorem B3190181 : Blo 2125435 3190181 := bbase (se 4 (by rfl) ⟨299079, by rfl⟩ : syracuseStep 3190181 = 598159) (by norm_num)
theorem B2126787 : Blo 2125435 2126787 := bstep (se 1 (by rfl) ⟨1595090, by rfl⟩ : syracuseStep 2126787 = 3190181) B3190181
theorem B2691721 : Blo 2125435 2691721 := bbase (se 2 (by rfl) ⟨1009395, by rfl⟩ : syracuseStep 2691721 = 2018791) (by norm_num)
theorem B3588961 : Blo 2125435 3588961 := bstep (se 2 (by rfl) ⟨1345860, by rfl⟩ : syracuseStep 3588961 = 2691721) B2691721
theorem B4785281 : Blo 2125435 4785281 := bstep (se 2 (by rfl) ⟨1794480, by rfl⟩ : syracuseStep 4785281 = 3588961) B3588961
theorem B3190187 : Blo 2125435 3190187 := bstep (se 1 (by rfl) ⟨2392640, by rfl⟩ : syracuseStep 3190187 = 4785281) B4785281
theorem B2126791 : Blo 2125435 2126791 := bstep (se 1 (by rfl) ⟨1595093, by rfl⟩ : syracuseStep 2126791 = 3190187) B3190187
theorem B2392645 : Blo 2125435 2392645 := bbase (se 4 (by rfl) ⟨224310, by rfl⟩ : syracuseStep 2392645 = 448621) (by norm_num)
theorem B3190193 : Blo 2125435 3190193 := bstep (se 2 (by rfl) ⟨1196322, by rfl⟩ : syracuseStep 3190193 = 2392645) B2392645
theorem B2126795 : Blo 2125435 2126795 := bstep (se 1 (by rfl) ⟨1595096, by rfl⟩ : syracuseStep 2126795 = 3190193) B3190193
theorem B4037597 : Blo 2125435 4037597 := bbase (se 3 (by rfl) ⟨757049, by rfl⟩ : syracuseStep 4037597 = 1514099) (by norm_num)
theorem B2691731 : Blo 2125435 2691731 := bstep (se 1 (by rfl) ⟨2018798, by rfl⟩ : syracuseStep 2691731 = 4037597) B4037597
theorem B7177949 : Blo 2125435 7177949 := bstep (se 3 (by rfl) ⟨1345865, by rfl⟩ : syracuseStep 7177949 = 2691731) B2691731
theorem B4785299 : Blo 2125435 4785299 := bstep (se 1 (by rfl) ⟨3588974, by rfl⟩ : syracuseStep 4785299 = 7177949) B7177949
theorem B3190199 : Blo 2125435 3190199 := bstep (se 1 (by rfl) ⟨2392649, by rfl⟩ : syracuseStep 3190199 = 4785299) B4785299
theorem B2126799 : Blo 2125435 2126799 := bstep (se 1 (by rfl) ⟨1595099, by rfl⟩ : syracuseStep 2126799 = 3190199) B3190199
theorem B3190205 : Blo 2125435 3190205 := bbase (se 3 (by rfl) ⟨598163, by rfl⟩ : syracuseStep 3190205 = 1196327) (by norm_num)
theorem B2126803 : Blo 2125435 2126803 := bstep (se 1 (by rfl) ⟨1595102, by rfl⟩ : syracuseStep 2126803 = 3190205) B3190205
theorem B4785317 : Blo 2125435 4785317 := bbase (se 4 (by rfl) ⟨448623, by rfl⟩ : syracuseStep 4785317 = 897247) (by norm_num)
theorem B3190211 : Blo 2125435 3190211 := bstep (se 1 (by rfl) ⟨2392658, by rfl⟩ : syracuseStep 3190211 = 4785317) B4785317
theorem B2126807 : Blo 2125435 2126807 := bstep (se 1 (by rfl) ⟨1595105, by rfl⟩ : syracuseStep 2126807 = 3190211) B3190211
theorem B5383493 : Blo 2125435 5383493 := bbase (se 4 (by rfl) ⟨504702, by rfl⟩ : syracuseStep 5383493 = 1009405) (by norm_num)
theorem B3588995 : Blo 2125435 3588995 := bstep (se 1 (by rfl) ⟨2691746, by rfl⟩ : syracuseStep 3588995 = 5383493) B5383493
theorem B2392663 : Blo 2125435 2392663 := bstep (se 1 (by rfl) ⟨1794497, by rfl⟩ : syracuseStep 2392663 = 3588995) B3588995
theorem B3190217 : Blo 2125435 3190217 := bstep (se 2 (by rfl) ⟨1196331, by rfl⟩ : syracuseStep 3190217 = 2392663) B2392663
theorem B2126811 : Blo 2125435 2126811 := bstep (se 1 (by rfl) ⟨1595108, by rfl⟩ : syracuseStep 2126811 = 3190217) B3190217
theorem B2425313 : Blo 2125435 2425313 := bbase (se 2 (by rfl) ⟨909492, by rfl⟩ : syracuseStep 2425313 = 1818985) (by norm_num)
theorem B6467501 : Blo 2125435 6467501 := bstep (se 3 (by rfl) ⟨1212656, by rfl⟩ : syracuseStep 6467501 = 2425313) B2425313
theorem B4311667 : Blo 2125435 4311667 := bstep (se 1 (by rfl) ⟨3233750, by rfl⟩ : syracuseStep 4311667 = 6467501) B6467501
theorem B5748889 : Blo 2125435 5748889 := bstep (se 2 (by rfl) ⟨2155833, by rfl⟩ : syracuseStep 5748889 = 4311667) B4311667
theorem B7665185 : Blo 2125435 7665185 := bstep (se 2 (by rfl) ⟨2874444, by rfl⟩ : syracuseStep 7665185 = 5748889) B5748889
theorem B5110123 : Blo 2125435 5110123 := bstep (se 1 (by rfl) ⟨3832592, by rfl⟩ : syracuseStep 5110123 = 7665185) B7665185
theorem B6813497 : Blo 2125435 6813497 := bstep (se 2 (by rfl) ⟨2555061, by rfl⟩ : syracuseStep 6813497 = 5110123) B5110123
theorem B4542331 : Blo 2125435 4542331 := bstep (se 1 (by rfl) ⟨3406748, by rfl⟩ : syracuseStep 4542331 = 6813497) B6813497
theorem B6056441 : Blo 2125435 6056441 := bstep (se 2 (by rfl) ⟨2271165, by rfl⟩ : syracuseStep 6056441 = 4542331) B4542331
theorem B4037627 : Blo 2125435 4037627 := bstep (se 1 (by rfl) ⟨3028220, by rfl⟩ : syracuseStep 4037627 = 6056441) B6056441
theorem B10767005 : Blo 2125435 10767005 := bstep (se 3 (by rfl) ⟨2018813, by rfl⟩ : syracuseStep 10767005 = 4037627) B4037627
theorem B7178003 : Blo 2125435 7178003 := bstep (se 1 (by rfl) ⟨5383502, by rfl⟩ : syracuseStep 7178003 = 10767005) B10767005
theorem B4785335 : Blo 2125435 4785335 := bstep (se 1 (by rfl) ⟨3589001, by rfl⟩ : syracuseStep 4785335 = 7178003) B7178003
theorem B3190223 : Blo 2125435 3190223 := bstep (se 1 (by rfl) ⟨2392667, by rfl⟩ : syracuseStep 3190223 = 4785335) B4785335
theorem B2126815 : Blo 2125435 2126815 := bstep (se 1 (by rfl) ⟨1595111, by rfl⟩ : syracuseStep 2126815 = 3190223) B3190223
theorem B3190229 : Blo 2125435 3190229 := bbase (se 7 (by rfl) ⟨37385, by rfl⟩ : syracuseStep 3190229 = 74771) (by norm_num)
theorem B2126819 : Blo 2125435 2126819 := bstep (se 1 (by rfl) ⟨1595114, by rfl⟩ : syracuseStep 2126819 = 3190229) B3190229
theorem B8075285 : Blo 2125435 8075285 := bbase (se 6 (by rfl) ⟨189264, by rfl⟩ : syracuseStep 8075285 = 378529) (by norm_num)
theorem B5383523 : Blo 2125435 5383523 := bstep (se 1 (by rfl) ⟨4037642, by rfl⟩ : syracuseStep 5383523 = 8075285) B8075285
theorem B3589015 : Blo 2125435 3589015 := bstep (se 1 (by rfl) ⟨2691761, by rfl⟩ : syracuseStep 3589015 = 5383523) B5383523
theorem B4785353 : Blo 2125435 4785353 := bstep (se 2 (by rfl) ⟨1794507, by rfl⟩ : syracuseStep 4785353 = 3589015) B3589015
theorem B3190235 : Blo 2125435 3190235 := bstep (se 1 (by rfl) ⟨2392676, by rfl⟩ : syracuseStep 3190235 = 4785353) B4785353
theorem B2126823 : Blo 2125435 2126823 := bstep (se 1 (by rfl) ⟨1595117, by rfl⟩ : syracuseStep 2126823 = 3190235) B3190235
theorem B2392681 : Blo 2125435 2392681 := bbase (se 2 (by rfl) ⟨897255, by rfl⟩ : syracuseStep 2392681 = 1794511) (by norm_num)
theorem B3190241 : Blo 2125435 3190241 := bstep (se 2 (by rfl) ⟨1196340, by rfl⟩ : syracuseStep 3190241 = 2392681) B2392681
theorem B2126827 : Blo 2125435 2126827 := bstep (se 1 (by rfl) ⟨1595120, by rfl⟩ : syracuseStep 2126827 = 3190241) B3190241
theorem B4542365 : Blo 2125435 4542365 := bbase (se 3 (by rfl) ⟨851693, by rfl⟩ : syracuseStep 4542365 = 1703387) (by norm_num)
theorem B12112973 : Blo 2125435 12112973 := bstep (se 3 (by rfl) ⟨2271182, by rfl⟩ : syracuseStep 12112973 = 4542365) B4542365
theorem B8075315 : Blo 2125435 8075315 := bstep (se 1 (by rfl) ⟨6056486, by rfl⟩ : syracuseStep 8075315 = 12112973) B12112973
theorem B5383543 : Blo 2125435 5383543 := bstep (se 1 (by rfl) ⟨4037657, by rfl⟩ : syracuseStep 5383543 = 8075315) B8075315
theorem B7178057 : Blo 2125435 7178057 := bstep (se 2 (by rfl) ⟨2691771, by rfl⟩ : syracuseStep 7178057 = 5383543) B5383543
theorem B4785371 : Blo 2125435 4785371 := bstep (se 1 (by rfl) ⟨3589028, by rfl⟩ : syracuseStep 4785371 = 7178057) B7178057
theorem B3190247 : Blo 2125435 3190247 := bstep (se 1 (by rfl) ⟨2392685, by rfl⟩ : syracuseStep 3190247 = 4785371) B4785371
theorem B2126831 : Blo 2125435 2126831 := bstep (se 1 (by rfl) ⟨1595123, by rfl⟩ : syracuseStep 2126831 = 3190247) B3190247
theorem B3190253 : Blo 2125435 3190253 := bbase (se 3 (by rfl) ⟨598172, by rfl⟩ : syracuseStep 3190253 = 1196345) (by norm_num)
theorem B2126835 : Blo 2125435 2126835 := bstep (se 1 (by rfl) ⟨1595126, by rfl⟩ : syracuseStep 2126835 = 3190253) B3190253
theorem B4785389 : Blo 2125435 4785389 := bbase (se 3 (by rfl) ⟨897260, by rfl⟩ : syracuseStep 4785389 = 1794521) (by norm_num)
theorem B3190259 : Blo 2125435 3190259 := bstep (se 1 (by rfl) ⟨2392694, by rfl⟩ : syracuseStep 3190259 = 4785389) B4785389
theorem B2126839 : Blo 2125435 2126839 := bstep (se 1 (by rfl) ⟨1595129, by rfl⟩ : syracuseStep 2126839 = 3190259) B3190259
theorem B3028261 : Blo 2125435 3028261 := bbase (se 4 (by rfl) ⟨283899, by rfl⟩ : syracuseStep 3028261 = 567799) (by norm_num)
theorem B4037681 : Blo 2125435 4037681 := bstep (se 2 (by rfl) ⟨1514130, by rfl⟩ : syracuseStep 4037681 = 3028261) B3028261
theorem B2691787 : Blo 2125435 2691787 := bstep (se 1 (by rfl) ⟨2018840, by rfl⟩ : syracuseStep 2691787 = 4037681) B4037681
theorem B3589049 : Blo 2125435 3589049 := bstep (se 2 (by rfl) ⟨1345893, by rfl⟩ : syracuseStep 3589049 = 2691787) B2691787
theorem B2392699 : Blo 2125435 2392699 := bstep (se 1 (by rfl) ⟨1794524, by rfl⟩ : syracuseStep 2392699 = 3589049) B3589049
theorem B3190265 : Blo 2125435 3190265 := bstep (se 2 (by rfl) ⟨1196349, by rfl⟩ : syracuseStep 3190265 = 2392699) B2392699
theorem B2126843 : Blo 2125435 2126843 := bstep (se 1 (by rfl) ⟨1595132, by rfl⟩ : syracuseStep 2126843 = 3190265) B3190265
theorem B2728517 : Blo 2125435 2728517 := bbase (se 4 (by rfl) ⟨255798, by rfl⟩ : syracuseStep 2728517 = 511597) (by norm_num)
theorem B29104181 : Blo 2125435 29104181 := bstep (se 5 (by rfl) ⟨1364258, by rfl⟩ : syracuseStep 29104181 = 2728517) B2728517
theorem B19402787 : Blo 2125435 19402787 := bstep (se 1 (by rfl) ⟨14552090, by rfl⟩ : syracuseStep 19402787 = 29104181) B29104181
theorem B51740765 : Blo 2125435 51740765 := bstep (se 3 (by rfl) ⟨9701393, by rfl⟩ : syracuseStep 51740765 = 19402787) B19402787
theorem B34493843 : Blo 2125435 34493843 := bstep (se 1 (by rfl) ⟨25870382, by rfl⟩ : syracuseStep 34493843 = 51740765) B51740765
theorem B22995895 : Blo 2125435 22995895 := bstep (se 1 (by rfl) ⟨17246921, by rfl⟩ : syracuseStep 22995895 = 34493843) B34493843
theorem B30661193 : Blo 2125435 30661193 := bstep (se 2 (by rfl) ⟨11497947, by rfl⟩ : syracuseStep 30661193 = 22995895) B22995895
theorem B81763181 : Blo 2125435 81763181 := bstep (se 3 (by rfl) ⟨15330596, by rfl⟩ : syracuseStep 81763181 = 30661193) B30661193
theorem B54508787 : Blo 2125435 54508787 := bstep (se 1 (by rfl) ⟨40881590, by rfl⟩ : syracuseStep 54508787 = 81763181) B81763181
theorem B36339191 : Blo 2125435 36339191 := bstep (se 1 (by rfl) ⟨27254393, by rfl⟩ : syracuseStep 36339191 = 54508787) B54508787
theorem B24226127 : Blo 2125435 24226127 := bstep (se 1 (by rfl) ⟨18169595, by rfl⟩ : syracuseStep 24226127 = 36339191) B36339191
theorem B16150751 : Blo 2125435 16150751 := bstep (se 1 (by rfl) ⟨12113063, by rfl⟩ : syracuseStep 16150751 = 24226127) B24226127
theorem B10767167 : Blo 2125435 10767167 := bstep (se 1 (by rfl) ⟨8075375, by rfl⟩ : syracuseStep 10767167 = 16150751) B16150751
theorem B7178111 : Blo 2125435 7178111 := bstep (se 1 (by rfl) ⟨5383583, by rfl⟩ : syracuseStep 7178111 = 10767167) B10767167
theorem B4785407 : Blo 2125435 4785407 := bstep (se 1 (by rfl) ⟨3589055, by rfl⟩ : syracuseStep 4785407 = 7178111) B7178111
theorem B3190271 : Blo 2125435 3190271 := bstep (se 1 (by rfl) ⟨2392703, by rfl⟩ : syracuseStep 3190271 = 4785407) B4785407
theorem B2126847 : Blo 2125435 2126847 := bstep (se 1 (by rfl) ⟨1595135, by rfl⟩ : syracuseStep 2126847 = 3190271) B3190271
theorem B3190277 : Blo 2125435 3190277 := bbase (se 4 (by rfl) ⟨299088, by rfl⟩ : syracuseStep 3190277 = 598177) (by norm_num)
theorem B2126851 : Blo 2125435 2126851 := bstep (se 1 (by rfl) ⟨1595138, by rfl⟩ : syracuseStep 2126851 = 3190277) B3190277
theorem B3589069 : Blo 2125435 3589069 := bbase (se 3 (by rfl) ⟨672950, by rfl⟩ : syracuseStep 3589069 = 1345901) (by norm_num)
theorem B4785425 : Blo 2125435 4785425 := bstep (se 2 (by rfl) ⟨1794534, by rfl⟩ : syracuseStep 4785425 = 3589069) B3589069
theorem B3190283 : Blo 2125435 3190283 := bstep (se 1 (by rfl) ⟨2392712, by rfl⟩ : syracuseStep 3190283 = 4785425) B4785425
theorem B2126855 : Blo 2125435 2126855 := bstep (se 1 (by rfl) ⟨1595141, by rfl⟩ : syracuseStep 2126855 = 3190283) B3190283
theorem B2392717 : Blo 2125435 2392717 := bbase (se 3 (by rfl) ⟨448634, by rfl⟩ : syracuseStep 2392717 = 897269) (by norm_num)
theorem B3190289 : Blo 2125435 3190289 := bstep (se 2 (by rfl) ⟨1196358, by rfl⟩ : syracuseStep 3190289 = 2392717) B2392717
theorem B2126859 : Blo 2125435 2126859 := bstep (se 1 (by rfl) ⟨1595144, by rfl⟩ : syracuseStep 2126859 = 3190289) B3190289
theorem B7178165 : Blo 2125435 7178165 := bbase (se 5 (by rfl) ⟨336476, by rfl⟩ : syracuseStep 7178165 = 672953) (by norm_num)
theorem B4785443 : Blo 2125435 4785443 := bstep (se 1 (by rfl) ⟨3589082, by rfl⟩ : syracuseStep 4785443 = 7178165) B7178165
theorem B3190295 : Blo 2125435 3190295 := bstep (se 1 (by rfl) ⟨2392721, by rfl⟩ : syracuseStep 3190295 = 4785443) B4785443
theorem B2126863 : Blo 2125435 2126863 := bstep (se 1 (by rfl) ⟨1595147, by rfl⟩ : syracuseStep 2126863 = 3190295) B3190295
theorem B3190301 : Blo 2125435 3190301 := bbase (se 3 (by rfl) ⟨598181, by rfl⟩ : syracuseStep 3190301 = 1196363) (by norm_num)
theorem B2126867 : Blo 2125435 2126867 := bstep (se 1 (by rfl) ⟨1595150, by rfl⟩ : syracuseStep 2126867 = 3190301) B3190301
theorem B4785461 : Blo 2125435 4785461 := bbase (se 5 (by rfl) ⟨224318, by rfl⟩ : syracuseStep 4785461 = 448637) (by norm_num)
theorem B3190307 : Blo 2125435 3190307 := bstep (se 1 (by rfl) ⟨2392730, by rfl⟩ : syracuseStep 3190307 = 4785461) B4785461
theorem B2126871 : Blo 2125435 2126871 := bstep (se 1 (by rfl) ⟨1595153, by rfl⟩ : syracuseStep 2126871 = 3190307) B3190307
theorem B9701525 : Blo 2125435 9701525 := bbase (se 6 (by rfl) ⟨227379, by rfl⟩ : syracuseStep 9701525 = 454759) (by norm_num)
theorem B6467683 : Blo 2125435 6467683 := bstep (se 1 (by rfl) ⟨4850762, by rfl⟩ : syracuseStep 6467683 = 9701525) B9701525
theorem B8623577 : Blo 2125435 8623577 := bstep (se 2 (by rfl) ⟨3233841, by rfl⟩ : syracuseStep 8623577 = 6467683) B6467683
theorem B5749051 : Blo 2125435 5749051 := bstep (se 1 (by rfl) ⟨4311788, by rfl⟩ : syracuseStep 5749051 = 8623577) B8623577
theorem B7665401 : Blo 2125435 7665401 := bstep (se 2 (by rfl) ⟨2874525, by rfl⟩ : syracuseStep 7665401 = 5749051) B5749051
theorem B20441069 : Blo 2125435 20441069 := bstep (se 3 (by rfl) ⟨3832700, by rfl⟩ : syracuseStep 20441069 = 7665401) B7665401
theorem B13627379 : Blo 2125435 13627379 := bstep (se 1 (by rfl) ⟨10220534, by rfl⟩ : syracuseStep 13627379 = 20441069) B20441069
theorem B9084919 : Blo 2125435 9084919 := bstep (se 1 (by rfl) ⟨6813689, by rfl⟩ : syracuseStep 9084919 = 13627379) B13627379
theorem B12113225 : Blo 2125435 12113225 := bstep (se 2 (by rfl) ⟨4542459, by rfl⟩ : syracuseStep 12113225 = 9084919) B9084919
theorem B8075483 : Blo 2125435 8075483 := bstep (se 1 (by rfl) ⟨6056612, by rfl⟩ : syracuseStep 8075483 = 12113225) B12113225
theorem B5383655 : Blo 2125435 5383655 := bstep (se 1 (by rfl) ⟨4037741, by rfl⟩ : syracuseStep 5383655 = 8075483) B8075483
theorem B3589103 : Blo 2125435 3589103 := bstep (se 1 (by rfl) ⟨2691827, by rfl⟩ : syracuseStep 3589103 = 5383655) B5383655
theorem B2392735 : Blo 2125435 2392735 := bstep (se 1 (by rfl) ⟨1794551, by rfl⟩ : syracuseStep 2392735 = 3589103) B3589103
theorem B3190313 : Blo 2125435 3190313 := bstep (se 2 (by rfl) ⟨1196367, by rfl⟩ : syracuseStep 3190313 = 2392735) B2392735
theorem B2126875 : Blo 2125435 2126875 := bstep (se 1 (by rfl) ⟨1595156, by rfl⟩ : syracuseStep 2126875 = 3190313) B3190313
theorem B5749061 : Blo 2125435 5749061 := bbase (se 4 (by rfl) ⟨538974, by rfl⟩ : syracuseStep 5749061 = 1077949) (by norm_num)
theorem B15330829 : Blo 2125435 15330829 := bstep (se 3 (by rfl) ⟨2874530, by rfl⟩ : syracuseStep 15330829 = 5749061) B5749061
theorem B20441105 : Blo 2125435 20441105 := bstep (se 2 (by rfl) ⟨7665414, by rfl⟩ : syracuseStep 20441105 = 15330829) B15330829
theorem B13627403 : Blo 2125435 13627403 := bstep (se 1 (by rfl) ⟨10220552, by rfl⟩ : syracuseStep 13627403 = 20441105) B20441105
theorem B9084935 : Blo 2125435 9084935 := bstep (se 1 (by rfl) ⟨6813701, by rfl⟩ : syracuseStep 9084935 = 13627403) B13627403
theorem B6056623 : Blo 2125435 6056623 := bstep (se 1 (by rfl) ⟨4542467, by rfl⟩ : syracuseStep 6056623 = 9084935) B9084935
theorem B8075497 : Blo 2125435 8075497 := bstep (se 2 (by rfl) ⟨3028311, by rfl⟩ : syracuseStep 8075497 = 6056623) B6056623
theorem B10767329 : Blo 2125435 10767329 := bstep (se 2 (by rfl) ⟨4037748, by rfl⟩ : syracuseStep 10767329 = 8075497) B8075497
theorem B7178219 : Blo 2125435 7178219 := bstep (se 1 (by rfl) ⟨5383664, by rfl⟩ : syracuseStep 7178219 = 10767329) B10767329
theorem B4785479 : Blo 2125435 4785479 := bstep (se 1 (by rfl) ⟨3589109, by rfl⟩ : syracuseStep 4785479 = 7178219) B7178219
theorem B3190319 : Blo 2125435 3190319 := bstep (se 1 (by rfl) ⟨2392739, by rfl⟩ : syracuseStep 3190319 = 4785479) B4785479
theorem B2126879 : Blo 2125435 2126879 := bstep (se 1 (by rfl) ⟨1595159, by rfl⟩ : syracuseStep 2126879 = 3190319) B3190319
theorem B3190325 : Blo 2125435 3190325 := bbase (se 5 (by rfl) ⟨149546, by rfl⟩ : syracuseStep 3190325 = 299093) (by norm_num)
theorem B2126883 : Blo 2125435 2126883 := bstep (se 1 (by rfl) ⟨1595162, by rfl⟩ : syracuseStep 2126883 = 3190325) B3190325
theorem B5383685 : Blo 2125435 5383685 := bbase (se 4 (by rfl) ⟨504720, by rfl⟩ : syracuseStep 5383685 = 1009441) (by norm_num)
theorem B3589123 : Blo 2125435 3589123 := bstep (se 1 (by rfl) ⟨2691842, by rfl⟩ : syracuseStep 3589123 = 5383685) B5383685
theorem B4785497 : Blo 2125435 4785497 := bstep (se 2 (by rfl) ⟨1794561, by rfl⟩ : syracuseStep 4785497 = 3589123) B3589123
theorem B3190331 : Blo 2125435 3190331 := bstep (se 1 (by rfl) ⟨2392748, by rfl⟩ : syracuseStep 3190331 = 4785497) B4785497
theorem B2126887 : Blo 2125435 2126887 := bstep (se 1 (by rfl) ⟨1595165, by rfl⟩ : syracuseStep 2126887 = 3190331) B3190331
theorem B2392753 : Blo 2125435 2392753 := bbase (se 2 (by rfl) ⟨897282, by rfl⟩ : syracuseStep 2392753 = 1794565) (by norm_num)
theorem B3190337 : Blo 2125435 3190337 := bstep (se 2 (by rfl) ⟨1196376, by rfl⟩ : syracuseStep 3190337 = 2392753) B2392753
theorem B2126891 : Blo 2125435 2126891 := bstep (se 1 (by rfl) ⟨1595168, by rfl⟩ : syracuseStep 2126891 = 3190337) B3190337
theorem B3406877 : Blo 2125435 3406877 := bbase (se 3 (by rfl) ⟨638789, by rfl⟩ : syracuseStep 3406877 = 1277579) (by norm_num)
theorem B2271251 : Blo 2125435 2271251 := bstep (se 1 (by rfl) ⟨1703438, by rfl⟩ : syracuseStep 2271251 = 3406877) B3406877
theorem B6056669 : Blo 2125435 6056669 := bstep (se 3 (by rfl) ⟨1135625, by rfl⟩ : syracuseStep 6056669 = 2271251) B2271251
theorem B4037779 : Blo 2125435 4037779 := bstep (se 1 (by rfl) ⟨3028334, by rfl⟩ : syracuseStep 4037779 = 6056669) B6056669
theorem B5383705 : Blo 2125435 5383705 := bstep (se 2 (by rfl) ⟨2018889, by rfl⟩ : syracuseStep 5383705 = 4037779) B4037779
theorem B7178273 : Blo 2125435 7178273 := bstep (se 2 (by rfl) ⟨2691852, by rfl⟩ : syracuseStep 7178273 = 5383705) B5383705
theorem B4785515 : Blo 2125435 4785515 := bstep (se 1 (by rfl) ⟨3589136, by rfl⟩ : syracuseStep 4785515 = 7178273) B7178273
theorem B3190343 : Blo 2125435 3190343 := bstep (se 1 (by rfl) ⟨2392757, by rfl⟩ : syracuseStep 3190343 = 4785515) B4785515
theorem B2126895 : Blo 2125435 2126895 := bstep (se 1 (by rfl) ⟨1595171, by rfl⟩ : syracuseStep 2126895 = 3190343) B3190343
theorem B3190349 : Blo 2125435 3190349 := bbase (se 3 (by rfl) ⟨598190, by rfl⟩ : syracuseStep 3190349 = 1196381) (by norm_num)
theorem B2126899 : Blo 2125435 2126899 := bstep (se 1 (by rfl) ⟨1595174, by rfl⟩ : syracuseStep 2126899 = 3190349) B3190349
theorem B4785533 : Blo 2125435 4785533 := bbase (se 3 (by rfl) ⟨897287, by rfl⟩ : syracuseStep 4785533 = 1794575) (by norm_num)
theorem B3190355 : Blo 2125435 3190355 := bstep (se 1 (by rfl) ⟨2392766, by rfl⟩ : syracuseStep 3190355 = 4785533) B4785533
theorem B2126903 : Blo 2125435 2126903 := bstep (se 1 (by rfl) ⟨1595177, by rfl⟩ : syracuseStep 2126903 = 3190355) B3190355
theorem B3589157 : Blo 2125435 3589157 := bbase (se 4 (by rfl) ⟨336483, by rfl⟩ : syracuseStep 3589157 = 672967) (by norm_num)
theorem B2392771 : Blo 2125435 2392771 := bstep (se 1 (by rfl) ⟨1794578, by rfl⟩ : syracuseStep 2392771 = 3589157) B3589157
theorem B3190361 : Blo 2125435 3190361 := bstep (se 2 (by rfl) ⟨1196385, by rfl⟩ : syracuseStep 3190361 = 2392771) B2392771
theorem B2126907 : Blo 2125435 2126907 := bstep (se 1 (by rfl) ⟨1595180, by rfl⟩ : syracuseStep 2126907 = 3190361) B3190361
theorem B3028357 : Blo 2125435 3028357 := bbase (se 4 (by rfl) ⟨283908, by rfl⟩ : syracuseStep 3028357 = 567817) (by norm_num)
theorem B16151237 : Blo 2125435 16151237 := bstep (se 4 (by rfl) ⟨1514178, by rfl⟩ : syracuseStep 16151237 = 3028357) B3028357
theorem B10767491 : Blo 2125435 10767491 := bstep (se 1 (by rfl) ⟨8075618, by rfl⟩ : syracuseStep 10767491 = 16151237) B16151237
theorem B7178327 : Blo 2125435 7178327 := bstep (se 1 (by rfl) ⟨5383745, by rfl⟩ : syracuseStep 7178327 = 10767491) B10767491
theorem B4785551 : Blo 2125435 4785551 := bstep (se 1 (by rfl) ⟨3589163, by rfl⟩ : syracuseStep 4785551 = 7178327) B7178327
theorem B3190367 : Blo 2125435 3190367 := bstep (se 1 (by rfl) ⟨2392775, by rfl⟩ : syracuseStep 3190367 = 4785551) B4785551
theorem B2126911 : Blo 2125435 2126911 := bstep (se 1 (by rfl) ⟨1595183, by rfl⟩ : syracuseStep 2126911 = 3190367) B3190367
theorem B3190373 : Blo 2125435 3190373 := bbase (se 4 (by rfl) ⟨299097, by rfl⟩ : syracuseStep 3190373 = 598195) (by norm_num)
theorem B2126915 : Blo 2125435 2126915 := bstep (se 1 (by rfl) ⟨1595186, by rfl⟩ : syracuseStep 2126915 = 3190373) B3190373
theorem B2271277 : Blo 2125435 2271277 := bbase (se 3 (by rfl) ⟨425864, by rfl⟩ : syracuseStep 2271277 = 851729) (by norm_num)
theorem B3028369 : Blo 2125435 3028369 := bstep (se 2 (by rfl) ⟨1135638, by rfl⟩ : syracuseStep 3028369 = 2271277) B2271277
theorem B4037825 : Blo 2125435 4037825 := bstep (se 2 (by rfl) ⟨1514184, by rfl⟩ : syracuseStep 4037825 = 3028369) B3028369
theorem B2691883 : Blo 2125435 2691883 := bstep (se 1 (by rfl) ⟨2018912, by rfl⟩ : syracuseStep 2691883 = 4037825) B4037825
theorem B3589177 : Blo 2125435 3589177 := bstep (se 2 (by rfl) ⟨1345941, by rfl⟩ : syracuseStep 3589177 = 2691883) B2691883
theorem B4785569 : Blo 2125435 4785569 := bstep (se 2 (by rfl) ⟨1794588, by rfl⟩ : syracuseStep 4785569 = 3589177) B3589177
theorem B3190379 : Blo 2125435 3190379 := bstep (se 1 (by rfl) ⟨2392784, by rfl⟩ : syracuseStep 3190379 = 4785569) B4785569
theorem B2126919 : Blo 2125435 2126919 := bstep (se 1 (by rfl) ⟨1595189, by rfl⟩ : syracuseStep 2126919 = 3190379) B3190379
theorem B2392789 : Blo 2125435 2392789 := bbase (se 7 (by rfl) ⟨28040, by rfl⟩ : syracuseStep 2392789 = 56081) (by norm_num)
theorem B3190385 : Blo 2125435 3190385 := bstep (se 2 (by rfl) ⟨1196394, by rfl⟩ : syracuseStep 3190385 = 2392789) B2392789
theorem B2126923 : Blo 2125435 2126923 := bstep (se 1 (by rfl) ⟨1595192, by rfl⟩ : syracuseStep 2126923 = 3190385) B3190385
theorem B2691893 : Blo 2125435 2691893 := bbase (se 5 (by rfl) ⟨126182, by rfl⟩ : syracuseStep 2691893 = 252365) (by norm_num)
theorem B7178381 : Blo 2125435 7178381 := bstep (se 3 (by rfl) ⟨1345946, by rfl⟩ : syracuseStep 7178381 = 2691893) B2691893
theorem B4785587 : Blo 2125435 4785587 := bstep (se 1 (by rfl) ⟨3589190, by rfl⟩ : syracuseStep 4785587 = 7178381) B7178381
theorem B3190391 : Blo 2125435 3190391 := bstep (se 1 (by rfl) ⟨2392793, by rfl⟩ : syracuseStep 3190391 = 4785587) B4785587
theorem B2126927 : Blo 2125435 2126927 := bstep (se 1 (by rfl) ⟨1595195, by rfl⟩ : syracuseStep 2126927 = 3190391) B3190391
theorem B3190397 : Blo 2125435 3190397 := bbase (se 3 (by rfl) ⟨598199, by rfl⟩ : syracuseStep 3190397 = 1196399) (by norm_num)
theorem B2126931 : Blo 2125435 2126931 := bstep (se 1 (by rfl) ⟨1595198, by rfl⟩ : syracuseStep 2126931 = 3190397) B3190397
theorem B4785605 : Blo 2125435 4785605 := bbase (se 4 (by rfl) ⟨448650, by rfl⟩ : syracuseStep 4785605 = 897301) (by norm_num)
theorem B3190403 : Blo 2125435 3190403 := bstep (se 1 (by rfl) ⟨2392802, by rfl⟩ : syracuseStep 3190403 = 4785605) B4785605
theorem B2126935 : Blo 2125435 2126935 := bstep (se 1 (by rfl) ⟨1595201, by rfl⟩ : syracuseStep 2126935 = 3190403) B3190403
theorem B4850909 : Blo 2125435 4850909 := bbase (se 3 (by rfl) ⟨909545, by rfl⟩ : syracuseStep 4850909 = 1819091) (by norm_num)
theorem B3233939 : Blo 2125435 3233939 := bstep (se 1 (by rfl) ⟨2425454, by rfl⟩ : syracuseStep 3233939 = 4850909) B4850909
theorem B8623837 : Blo 2125435 8623837 := bstep (se 3 (by rfl) ⟨1616969, by rfl⟩ : syracuseStep 8623837 = 3233939) B3233939
theorem B11498449 : Blo 2125435 11498449 := bstep (se 2 (by rfl) ⟨4311918, by rfl⟩ : syracuseStep 11498449 = 8623837) B8623837
theorem B15331265 : Blo 2125435 15331265 := bstep (se 2 (by rfl) ⟨5749224, by rfl⟩ : syracuseStep 15331265 = 11498449) B11498449
theorem B10220843 : Blo 2125435 10220843 := bstep (se 1 (by rfl) ⟨7665632, by rfl⟩ : syracuseStep 10220843 = 15331265) B15331265
theorem B6813895 : Blo 2125435 6813895 := bstep (se 1 (by rfl) ⟨5110421, by rfl⟩ : syracuseStep 6813895 = 10220843) B10220843
theorem B9085193 : Blo 2125435 9085193 := bstep (se 2 (by rfl) ⟨3406947, by rfl⟩ : syracuseStep 9085193 = 6813895) B6813895
theorem B6056795 : Blo 2125435 6056795 := bstep (se 1 (by rfl) ⟨4542596, by rfl⟩ : syracuseStep 6056795 = 9085193) B9085193
theorem B4037863 : Blo 2125435 4037863 := bstep (se 1 (by rfl) ⟨3028397, by rfl⟩ : syracuseStep 4037863 = 6056795) B6056795
theorem B5383817 : Blo 2125435 5383817 := bstep (se 2 (by rfl) ⟨2018931, by rfl⟩ : syracuseStep 5383817 = 4037863) B4037863
theorem B3589211 : Blo 2125435 3589211 := bstep (se 1 (by rfl) ⟨2691908, by rfl⟩ : syracuseStep 3589211 = 5383817) B5383817
theorem B2392807 : Blo 2125435 2392807 := bstep (se 1 (by rfl) ⟨1794605, by rfl⟩ : syracuseStep 2392807 = 3589211) B3589211
theorem B3190409 : Blo 2125435 3190409 := bstep (se 2 (by rfl) ⟨1196403, by rfl⟩ : syracuseStep 3190409 = 2392807) B2392807
theorem B2126939 : Blo 2125435 2126939 := bstep (se 1 (by rfl) ⟨1595204, by rfl⟩ : syracuseStep 2126939 = 3190409) B3190409
theorem B10767653 : Blo 2125435 10767653 := bbase (se 4 (by rfl) ⟨1009467, by rfl⟩ : syracuseStep 10767653 = 2018935) (by norm_num)
theorem B7178435 : Blo 2125435 7178435 := bstep (se 1 (by rfl) ⟨5383826, by rfl⟩ : syracuseStep 7178435 = 10767653) B10767653
theorem B4785623 : Blo 2125435 4785623 := bstep (se 1 (by rfl) ⟨3589217, by rfl⟩ : syracuseStep 4785623 = 7178435) B7178435
theorem B3190415 : Blo 2125435 3190415 := bstep (se 1 (by rfl) ⟨2392811, by rfl⟩ : syracuseStep 3190415 = 4785623) B4785623
theorem B2126943 : Blo 2125435 2126943 := bstep (se 1 (by rfl) ⟨1595207, by rfl⟩ : syracuseStep 2126943 = 3190415) B3190415
theorem B3190421 : Blo 2125435 3190421 := bbase (se 6 (by rfl) ⟨74775, by rfl⟩ : syracuseStep 3190421 = 149551) (by norm_num)
theorem B2126947 : Blo 2125435 2126947 := bstep (se 1 (by rfl) ⟨1595210, by rfl⟩ : syracuseStep 2126947 = 3190421) B3190421
theorem B15331349 : Blo 2125435 15331349 := bbase (se 6 (by rfl) ⟨359328, by rfl⟩ : syracuseStep 15331349 = 718657) (by norm_num)
theorem B10220899 : Blo 2125435 10220899 := bstep (se 1 (by rfl) ⟨7665674, by rfl⟩ : syracuseStep 10220899 = 15331349) B15331349
theorem B13627865 : Blo 2125435 13627865 := bstep (se 2 (by rfl) ⟨5110449, by rfl⟩ : syracuseStep 13627865 = 10220899) B10220899
theorem B9085243 : Blo 2125435 9085243 := bstep (se 1 (by rfl) ⟨6813932, by rfl⟩ : syracuseStep 9085243 = 13627865) B13627865
theorem B12113657 : Blo 2125435 12113657 := bstep (se 2 (by rfl) ⟨4542621, by rfl⟩ : syracuseStep 12113657 = 9085243) B9085243
theorem B8075771 : Blo 2125435 8075771 := bstep (se 1 (by rfl) ⟨6056828, by rfl⟩ : syracuseStep 8075771 = 12113657) B12113657
theorem B5383847 : Blo 2125435 5383847 := bstep (se 1 (by rfl) ⟨4037885, by rfl⟩ : syracuseStep 5383847 = 8075771) B8075771
theorem B3589231 : Blo 2125435 3589231 := bstep (se 1 (by rfl) ⟨2691923, by rfl⟩ : syracuseStep 3589231 = 5383847) B5383847
theorem B4785641 : Blo 2125435 4785641 := bstep (se 2 (by rfl) ⟨1794615, by rfl⟩ : syracuseStep 4785641 = 3589231) B3589231
theorem B3190427 : Blo 2125435 3190427 := bstep (se 1 (by rfl) ⟨2392820, by rfl⟩ : syracuseStep 3190427 = 4785641) B4785641
theorem B2126951 : Blo 2125435 2126951 := bstep (se 1 (by rfl) ⟨1595213, by rfl⟩ : syracuseStep 2126951 = 3190427) B3190427
theorem B2392825 : Blo 2125435 2392825 := bbase (se 2 (by rfl) ⟨897309, by rfl⟩ : syracuseStep 2392825 = 1794619) (by norm_num)
theorem B3190433 : Blo 2125435 3190433 := bstep (se 2 (by rfl) ⟨1196412, by rfl⟩ : syracuseStep 3190433 = 2392825) B2392825
theorem B2126955 : Blo 2125435 2126955 := bstep (se 1 (by rfl) ⟨1595216, by rfl⟩ : syracuseStep 2126955 = 3190433) B3190433
theorem B5110469 : Blo 2125435 5110469 := bbase (se 4 (by rfl) ⟨479106, by rfl⟩ : syracuseStep 5110469 = 958213) (by norm_num)
theorem B3406979 : Blo 2125435 3406979 := bstep (se 1 (by rfl) ⟨2555234, by rfl⟩ : syracuseStep 3406979 = 5110469) B5110469
theorem B9085277 : Blo 2125435 9085277 := bstep (se 3 (by rfl) ⟨1703489, by rfl⟩ : syracuseStep 9085277 = 3406979) B3406979
theorem B6056851 : Blo 2125435 6056851 := bstep (se 1 (by rfl) ⟨4542638, by rfl⟩ : syracuseStep 6056851 = 9085277) B9085277
theorem B8075801 : Blo 2125435 8075801 := bstep (se 2 (by rfl) ⟨3028425, by rfl⟩ : syracuseStep 8075801 = 6056851) B6056851
theorem B5383867 : Blo 2125435 5383867 := bstep (se 1 (by rfl) ⟨4037900, by rfl⟩ : syracuseStep 5383867 = 8075801) B8075801
theorem B7178489 : Blo 2125435 7178489 := bstep (se 2 (by rfl) ⟨2691933, by rfl⟩ : syracuseStep 7178489 = 5383867) B5383867
theorem B4785659 : Blo 2125435 4785659 := bstep (se 1 (by rfl) ⟨3589244, by rfl⟩ : syracuseStep 4785659 = 7178489) B7178489
theorem B3190439 : Blo 2125435 3190439 := bstep (se 1 (by rfl) ⟨2392829, by rfl⟩ : syracuseStep 3190439 = 4785659) B4785659
theorem B2126959 : Blo 2125435 2126959 := bstep (se 1 (by rfl) ⟨1595219, by rfl⟩ : syracuseStep 2126959 = 3190439) B3190439
theorem B3190445 : Blo 2125435 3190445 := bbase (se 3 (by rfl) ⟨598208, by rfl⟩ : syracuseStep 3190445 = 1196417) (by norm_num)
theorem B2126963 : Blo 2125435 2126963 := bstep (se 1 (by rfl) ⟨1595222, by rfl⟩ : syracuseStep 2126963 = 3190445) B3190445
theorem B4785677 : Blo 2125435 4785677 := bbase (se 3 (by rfl) ⟨897314, by rfl⟩ : syracuseStep 4785677 = 1794629) (by norm_num)
theorem B3190451 : Blo 2125435 3190451 := bstep (se 1 (by rfl) ⟨2392838, by rfl⟩ : syracuseStep 3190451 = 4785677) B4785677
theorem B2126967 : Blo 2125435 2126967 := bstep (se 1 (by rfl) ⟨1595225, by rfl⟩ : syracuseStep 2126967 = 3190451) B3190451
theorem B2691949 : Blo 2125435 2691949 := bbase (se 3 (by rfl) ⟨504740, by rfl⟩ : syracuseStep 2691949 = 1009481) (by norm_num)
theorem B3589265 : Blo 2125435 3589265 := bstep (se 2 (by rfl) ⟨1345974, by rfl⟩ : syracuseStep 3589265 = 2691949) B2691949
theorem B2392843 : Blo 2125435 2392843 := bstep (se 1 (by rfl) ⟨1794632, by rfl⟩ : syracuseStep 2392843 = 3589265) B3589265
theorem B3190457 : Blo 2125435 3190457 := bstep (se 2 (by rfl) ⟨1196421, by rfl⟩ : syracuseStep 3190457 = 2392843) B2392843
theorem B2126971 : Blo 2125435 2126971 := bstep (se 1 (by rfl) ⟨1595228, by rfl⟩ : syracuseStep 2126971 = 3190457) B3190457
theorem B10221013 : Blo 2125435 10221013 := bbase (se 7 (by rfl) ⟨119777, by rfl⟩ : syracuseStep 10221013 = 239555) (by norm_num)
theorem B13628017 : Blo 2125435 13628017 := bstep (se 2 (by rfl) ⟨5110506, by rfl⟩ : syracuseStep 13628017 = 10221013) B10221013
theorem B18170689 : Blo 2125435 18170689 := bstep (se 2 (by rfl) ⟨6814008, by rfl⟩ : syracuseStep 18170689 = 13628017) B13628017
theorem B24227585 : Blo 2125435 24227585 := bstep (se 2 (by rfl) ⟨9085344, by rfl⟩ : syracuseStep 24227585 = 18170689) B18170689
theorem B16151723 : Blo 2125435 16151723 := bstep (se 1 (by rfl) ⟨12113792, by rfl⟩ : syracuseStep 16151723 = 24227585) B24227585
theorem B10767815 : Blo 2125435 10767815 := bstep (se 1 (by rfl) ⟨8075861, by rfl⟩ : syracuseStep 10767815 = 16151723) B16151723
theorem B7178543 : Blo 2125435 7178543 := bstep (se 1 (by rfl) ⟨5383907, by rfl⟩ : syracuseStep 7178543 = 10767815) B10767815
theorem B4785695 : Blo 2125435 4785695 := bstep (se 1 (by rfl) ⟨3589271, by rfl⟩ : syracuseStep 4785695 = 7178543) B7178543
theorem B3190463 : Blo 2125435 3190463 := bstep (se 1 (by rfl) ⟨2392847, by rfl⟩ : syracuseStep 3190463 = 4785695) B4785695
theorem B2126975 : Blo 2125435 2126975 := bstep (se 1 (by rfl) ⟨1595231, by rfl⟩ : syracuseStep 2126975 = 3190463) B3190463
theorem B3190469 : Blo 2125435 3190469 := bbase (se 4 (by rfl) ⟨299106, by rfl⟩ : syracuseStep 3190469 = 598213) (by norm_num)
theorem B2126979 : Blo 2125435 2126979 := bstep (se 1 (by rfl) ⟨1595234, by rfl⟩ : syracuseStep 2126979 = 3190469) B3190469
theorem B3589285 : Blo 2125435 3589285 := bbase (se 4 (by rfl) ⟨336495, by rfl⟩ : syracuseStep 3589285 = 672991) (by norm_num)
theorem B4785713 : Blo 2125435 4785713 := bstep (se 2 (by rfl) ⟨1794642, by rfl⟩ : syracuseStep 4785713 = 3589285) B3589285
theorem B3190475 : Blo 2125435 3190475 := bstep (se 1 (by rfl) ⟨2392856, by rfl⟩ : syracuseStep 3190475 = 4785713) B4785713
theorem B2126983 : Blo 2125435 2126983 := bstep (se 1 (by rfl) ⟨1595237, by rfl⟩ : syracuseStep 2126983 = 3190475) B3190475
theorem B2392861 : Blo 2125435 2392861 := bbase (se 3 (by rfl) ⟨448661, by rfl⟩ : syracuseStep 2392861 = 897323) (by norm_num)
theorem B3190481 : Blo 2125435 3190481 := bstep (se 2 (by rfl) ⟨1196430, by rfl⟩ : syracuseStep 3190481 = 2392861) B2392861
theorem B2126987 : Blo 2125435 2126987 := bstep (se 1 (by rfl) ⟨1595240, by rfl⟩ : syracuseStep 2126987 = 3190481) B3190481
theorem B7178597 : Blo 2125435 7178597 := bbase (se 4 (by rfl) ⟨672993, by rfl⟩ : syracuseStep 7178597 = 1345987) (by norm_num)
theorem B4785731 : Blo 2125435 4785731 := bstep (se 1 (by rfl) ⟨3589298, by rfl⟩ : syracuseStep 4785731 = 7178597) B7178597
theorem B3190487 : Blo 2125435 3190487 := bstep (se 1 (by rfl) ⟨2392865, by rfl⟩ : syracuseStep 3190487 = 4785731) B4785731
theorem B2126991 : Blo 2125435 2126991 := bstep (se 1 (by rfl) ⟨1595243, by rfl⟩ : syracuseStep 2126991 = 3190487) B3190487
theorem B3190493 : Blo 2125435 3190493 := bbase (se 3 (by rfl) ⟨598217, by rfl⟩ : syracuseStep 3190493 = 1196435) (by norm_num)
theorem B2126995 : Blo 2125435 2126995 := bstep (se 1 (by rfl) ⟨1595246, by rfl⟩ : syracuseStep 2126995 = 3190493) B3190493
theorem B4785749 : Blo 2125435 4785749 := bbase (se 8 (by rfl) ⟨28041, by rfl⟩ : syracuseStep 4785749 = 56083) (by norm_num)
theorem B3190499 : Blo 2125435 3190499 := bstep (se 1 (by rfl) ⟨2392874, by rfl⟩ : syracuseStep 3190499 = 4785749) B4785749
theorem B2126999 : Blo 2125435 2126999 := bstep (se 1 (by rfl) ⟨1595249, by rfl⟩ : syracuseStep 2126999 = 3190499) B3190499
theorem B4542733 : Blo 2125435 4542733 := bbase (se 3 (by rfl) ⟨851762, by rfl⟩ : syracuseStep 4542733 = 1703525) (by norm_num)
theorem B6056977 : Blo 2125435 6056977 := bstep (se 2 (by rfl) ⟨2271366, by rfl⟩ : syracuseStep 6056977 = 4542733) B4542733
theorem B8075969 : Blo 2125435 8075969 := bstep (se 2 (by rfl) ⟨3028488, by rfl⟩ : syracuseStep 8075969 = 6056977) B6056977
theorem B5383979 : Blo 2125435 5383979 := bstep (se 1 (by rfl) ⟨4037984, by rfl⟩ : syracuseStep 5383979 = 8075969) B8075969
theorem B3589319 : Blo 2125435 3589319 := bstep (se 1 (by rfl) ⟨2691989, by rfl⟩ : syracuseStep 3589319 = 5383979) B5383979
theorem B2392879 : Blo 2125435 2392879 := bstep (se 1 (by rfl) ⟨1794659, by rfl⟩ : syracuseStep 2392879 = 3589319) B3589319
theorem B3190505 : Blo 2125435 3190505 := bstep (se 2 (by rfl) ⟨1196439, by rfl⟩ : syracuseStep 3190505 = 2392879) B2392879
theorem B2127003 : Blo 2125435 2127003 := bstep (se 1 (by rfl) ⟨1595252, by rfl⟩ : syracuseStep 2127003 = 3190505) B3190505
theorem B5457445 : Blo 2125435 5457445 := bbase (se 4 (by rfl) ⟨511635, by rfl⟩ : syracuseStep 5457445 = 1023271) (by norm_num)
theorem B29106373 : Blo 2125435 29106373 := bstep (se 4 (by rfl) ⟨2728722, by rfl⟩ : syracuseStep 29106373 = 5457445) B5457445
theorem B38808497 : Blo 2125435 38808497 := bstep (se 2 (by rfl) ⟨14553186, by rfl⟩ : syracuseStep 38808497 = 29106373) B29106373
theorem B25872331 : Blo 2125435 25872331 := bstep (se 1 (by rfl) ⟨19404248, by rfl⟩ : syracuseStep 25872331 = 38808497) B38808497
theorem B34496441 : Blo 2125435 34496441 := bstep (se 2 (by rfl) ⟨12936165, by rfl⟩ : syracuseStep 34496441 = 25872331) B25872331
theorem B22997627 : Blo 2125435 22997627 := bstep (se 1 (by rfl) ⟨17248220, by rfl⟩ : syracuseStep 22997627 = 34496441) B34496441
theorem B15331751 : Blo 2125435 15331751 := bstep (se 1 (by rfl) ⟨11498813, by rfl⟩ : syracuseStep 15331751 = 22997627) B22997627
theorem B10221167 : Blo 2125435 10221167 := bstep (se 1 (by rfl) ⟨7665875, by rfl⟩ : syracuseStep 10221167 = 15331751) B15331751
theorem B27256445 : Blo 2125435 27256445 := bstep (se 3 (by rfl) ⟨5110583, by rfl⟩ : syracuseStep 27256445 = 10221167) B10221167
theorem B18170963 : Blo 2125435 18170963 := bstep (se 1 (by rfl) ⟨13628222, by rfl⟩ : syracuseStep 18170963 = 27256445) B27256445
theorem B12113975 : Blo 2125435 12113975 := bstep (se 1 (by rfl) ⟨9085481, by rfl⟩ : syracuseStep 12113975 = 18170963) B18170963
theorem B8075983 : Blo 2125435 8075983 := bstep (se 1 (by rfl) ⟨6056987, by rfl⟩ : syracuseStep 8075983 = 12113975) B12113975
theorem B10767977 : Blo 2125435 10767977 := bstep (se 2 (by rfl) ⟨4037991, by rfl⟩ : syracuseStep 10767977 = 8075983) B8075983
theorem B7178651 : Blo 2125435 7178651 := bstep (se 1 (by rfl) ⟨5383988, by rfl⟩ : syracuseStep 7178651 = 10767977) B10767977
theorem B4785767 : Blo 2125435 4785767 := bstep (se 1 (by rfl) ⟨3589325, by rfl⟩ : syracuseStep 4785767 = 7178651) B7178651
theorem B3190511 : Blo 2125435 3190511 := bstep (se 1 (by rfl) ⟨2392883, by rfl⟩ : syracuseStep 3190511 = 4785767) B4785767
theorem B2127007 : Blo 2125435 2127007 := bstep (se 1 (by rfl) ⟨1595255, by rfl⟩ : syracuseStep 2127007 = 3190511) B3190511
theorem B3190517 : Blo 2125435 3190517 := bbase (se 5 (by rfl) ⟨149555, by rfl⟩ : syracuseStep 3190517 = 299111) (by norm_num)
theorem B2127011 : Blo 2125435 2127011 := bstep (se 1 (by rfl) ⟨1595258, by rfl⟩ : syracuseStep 2127011 = 3190517) B3190517
theorem B3407069 : Blo 2125435 3407069 := bbase (se 3 (by rfl) ⟨638825, by rfl⟩ : syracuseStep 3407069 = 1277651) (by norm_num)
theorem B9085517 : Blo 2125435 9085517 := bstep (se 3 (by rfl) ⟨1703534, by rfl⟩ : syracuseStep 9085517 = 3407069) B3407069
theorem B6057011 : Blo 2125435 6057011 := bstep (se 1 (by rfl) ⟨4542758, by rfl⟩ : syracuseStep 6057011 = 9085517) B9085517
theorem B4038007 : Blo 2125435 4038007 := bstep (se 1 (by rfl) ⟨3028505, by rfl⟩ : syracuseStep 4038007 = 6057011) B6057011
theorem B5384009 : Blo 2125435 5384009 := bstep (se 2 (by rfl) ⟨2019003, by rfl⟩ : syracuseStep 5384009 = 4038007) B4038007
theorem B3589339 : Blo 2125435 3589339 := bstep (se 1 (by rfl) ⟨2692004, by rfl⟩ : syracuseStep 3589339 = 5384009) B5384009
theorem B4785785 : Blo 2125435 4785785 := bstep (se 2 (by rfl) ⟨1794669, by rfl⟩ : syracuseStep 4785785 = 3589339) B3589339
theorem B3190523 : Blo 2125435 3190523 := bstep (se 1 (by rfl) ⟨2392892, by rfl⟩ : syracuseStep 3190523 = 4785785) B4785785
theorem B2127015 : Blo 2125435 2127015 := bstep (se 1 (by rfl) ⟨1595261, by rfl⟩ : syracuseStep 2127015 = 3190523) B3190523
theorem B2392897 : Blo 2125435 2392897 := bbase (se 2 (by rfl) ⟨897336, by rfl⟩ : syracuseStep 2392897 = 1794673) (by norm_num)
theorem B3190529 : Blo 2125435 3190529 := bstep (se 2 (by rfl) ⟨1196448, by rfl⟩ : syracuseStep 3190529 = 2392897) B2392897
theorem B2127019 : Blo 2125435 2127019 := bstep (se 1 (by rfl) ⟨1595264, by rfl⟩ : syracuseStep 2127019 = 3190529) B3190529
theorem B5384029 : Blo 2125435 5384029 := bbase (se 3 (by rfl) ⟨1009505, by rfl⟩ : syracuseStep 5384029 = 2019011) (by norm_num)
theorem B7178705 : Blo 2125435 7178705 := bstep (se 2 (by rfl) ⟨2692014, by rfl⟩ : syracuseStep 7178705 = 5384029) B5384029
theorem B4785803 : Blo 2125435 4785803 := bstep (se 1 (by rfl) ⟨3589352, by rfl⟩ : syracuseStep 4785803 = 7178705) B7178705
theorem B3190535 : Blo 2125435 3190535 := bstep (se 1 (by rfl) ⟨2392901, by rfl⟩ : syracuseStep 3190535 = 4785803) B4785803
theorem B2127023 : Blo 2125435 2127023 := bstep (se 1 (by rfl) ⟨1595267, by rfl⟩ : syracuseStep 2127023 = 3190535) B3190535
theorem B3190541 : Blo 2125435 3190541 := bbase (se 3 (by rfl) ⟨598226, by rfl⟩ : syracuseStep 3190541 = 1196453) (by norm_num)
theorem B2127027 : Blo 2125435 2127027 := bstep (se 1 (by rfl) ⟨1595270, by rfl⟩ : syracuseStep 2127027 = 3190541) B3190541
theorem B4785821 : Blo 2125435 4785821 := bbase (se 3 (by rfl) ⟨897341, by rfl⟩ : syracuseStep 4785821 = 1794683) (by norm_num)
theorem B3190547 : Blo 2125435 3190547 := bstep (se 1 (by rfl) ⟨2392910, by rfl⟩ : syracuseStep 3190547 = 4785821) B4785821
theorem B2127031 : Blo 2125435 2127031 := bstep (se 1 (by rfl) ⟨1595273, by rfl⟩ : syracuseStep 2127031 = 3190547) B3190547
theorem B3589373 : Blo 2125435 3589373 := bbase (se 3 (by rfl) ⟨673007, by rfl⟩ : syracuseStep 3589373 = 1346015) (by norm_num)
theorem B2392915 : Blo 2125435 2392915 := bstep (se 1 (by rfl) ⟨1794686, by rfl⟩ : syracuseStep 2392915 = 3589373) B3589373
theorem B3190553 : Blo 2125435 3190553 := bstep (se 2 (by rfl) ⟨1196457, by rfl⟩ : syracuseStep 3190553 = 2392915) B2392915
theorem B2127035 : Blo 2125435 2127035 := bstep (se 1 (by rfl) ⟨1595276, by rfl⟩ : syracuseStep 2127035 = 3190553) B3190553
theorem B5110661 : Blo 2125435 5110661 := bbase (se 4 (by rfl) ⟨479124, by rfl⟩ : syracuseStep 5110661 = 958249) (by norm_num)
theorem B3407107 : Blo 2125435 3407107 := bstep (se 1 (by rfl) ⟨2555330, by rfl⟩ : syracuseStep 3407107 = 5110661) B5110661
theorem B4542809 : Blo 2125435 4542809 := bstep (se 2 (by rfl) ⟨1703553, by rfl⟩ : syracuseStep 4542809 = 3407107) B3407107
theorem B12114157 : Blo 2125435 12114157 := bstep (se 3 (by rfl) ⟨2271404, by rfl⟩ : syracuseStep 12114157 = 4542809) B4542809
theorem B16152209 : Blo 2125435 16152209 := bstep (se 2 (by rfl) ⟨6057078, by rfl⟩ : syracuseStep 16152209 = 12114157) B12114157
theorem B10768139 : Blo 2125435 10768139 := bstep (se 1 (by rfl) ⟨8076104, by rfl⟩ : syracuseStep 10768139 = 16152209) B16152209
theorem B7178759 : Blo 2125435 7178759 := bstep (se 1 (by rfl) ⟨5384069, by rfl⟩ : syracuseStep 7178759 = 10768139) B10768139
theorem B4785839 : Blo 2125435 4785839 := bstep (se 1 (by rfl) ⟨3589379, by rfl⟩ : syracuseStep 4785839 = 7178759) B7178759
theorem B3190559 : Blo 2125435 3190559 := bstep (se 1 (by rfl) ⟨2392919, by rfl⟩ : syracuseStep 3190559 = 4785839) B4785839
theorem B2127039 : Blo 2125435 2127039 := bstep (se 1 (by rfl) ⟨1595279, by rfl⟩ : syracuseStep 2127039 = 3190559) B3190559
theorem B3190565 : Blo 2125435 3190565 := bbase (se 4 (by rfl) ⟨299115, by rfl⟩ : syracuseStep 3190565 = 598231) (by norm_num)
theorem B2127043 : Blo 2125435 2127043 := bstep (se 1 (by rfl) ⟨1595282, by rfl⟩ : syracuseStep 2127043 = 3190565) B3190565
theorem B2692045 : Blo 2125435 2692045 := bbase (se 3 (by rfl) ⟨504758, by rfl⟩ : syracuseStep 2692045 = 1009517) (by norm_num)
theorem B3589393 : Blo 2125435 3589393 := bstep (se 2 (by rfl) ⟨1346022, by rfl⟩ : syracuseStep 3589393 = 2692045) B2692045
theorem B4785857 : Blo 2125435 4785857 := bstep (se 2 (by rfl) ⟨1794696, by rfl⟩ : syracuseStep 4785857 = 3589393) B3589393
theorem B3190571 : Blo 2125435 3190571 := bstep (se 1 (by rfl) ⟨2392928, by rfl⟩ : syracuseStep 3190571 = 4785857) B4785857
theorem B2127047 : Blo 2125435 2127047 := bstep (se 1 (by rfl) ⟨1595285, by rfl⟩ : syracuseStep 2127047 = 3190571) B3190571
theorem B2392933 : Blo 2125435 2392933 := bbase (se 4 (by rfl) ⟨224337, by rfl⟩ : syracuseStep 2392933 = 448675) (by norm_num)
theorem B3190577 : Blo 2125435 3190577 := bstep (se 2 (by rfl) ⟨1196466, by rfl⟩ : syracuseStep 3190577 = 2392933) B2392933
theorem B2127051 : Blo 2125435 2127051 := bstep (se 1 (by rfl) ⟨1595288, by rfl⟩ : syracuseStep 2127051 = 3190577) B3190577
theorem B6057125 : Blo 2125435 6057125 := bbase (se 4 (by rfl) ⟨567855, by rfl⟩ : syracuseStep 6057125 = 1135711) (by norm_num)
theorem B4038083 : Blo 2125435 4038083 := bstep (se 1 (by rfl) ⟨3028562, by rfl⟩ : syracuseStep 4038083 = 6057125) B6057125
theorem B2692055 : Blo 2125435 2692055 := bstep (se 1 (by rfl) ⟨2019041, by rfl⟩ : syracuseStep 2692055 = 4038083) B4038083
theorem B7178813 : Blo 2125435 7178813 := bstep (se 3 (by rfl) ⟨1346027, by rfl⟩ : syracuseStep 7178813 = 2692055) B2692055
theorem B4785875 : Blo 2125435 4785875 := bstep (se 1 (by rfl) ⟨3589406, by rfl⟩ : syracuseStep 4785875 = 7178813) B7178813
theorem B3190583 : Blo 2125435 3190583 := bstep (se 1 (by rfl) ⟨2392937, by rfl⟩ : syracuseStep 3190583 = 4785875) B4785875
theorem B2127055 : Blo 2125435 2127055 := bstep (se 1 (by rfl) ⟨1595291, by rfl⟩ : syracuseStep 2127055 = 3190583) B3190583
theorem B3190589 : Blo 2125435 3190589 := bbase (se 3 (by rfl) ⟨598235, by rfl⟩ : syracuseStep 3190589 = 1196471) (by norm_num)
theorem B2127059 : Blo 2125435 2127059 := bstep (se 1 (by rfl) ⟨1595294, by rfl⟩ : syracuseStep 2127059 = 3190589) B3190589
theorem B4785893 : Blo 2125435 4785893 := bbase (se 4 (by rfl) ⟨448677, by rfl⟩ : syracuseStep 4785893 = 897355) (by norm_num)
theorem B3190595 : Blo 2125435 3190595 := bstep (se 1 (by rfl) ⟨2392946, by rfl⟩ : syracuseStep 3190595 = 4785893) B4785893
theorem B2127063 : Blo 2125435 2127063 := bstep (se 1 (by rfl) ⟨1595297, by rfl⟩ : syracuseStep 2127063 = 3190595) B3190595
theorem B5384141 : Blo 2125435 5384141 := bbase (se 3 (by rfl) ⟨1009526, by rfl⟩ : syracuseStep 5384141 = 2019053) (by norm_num)
theorem B3589427 : Blo 2125435 3589427 := bstep (se 1 (by rfl) ⟨2692070, by rfl⟩ : syracuseStep 3589427 = 5384141) B5384141
theorem B2392951 : Blo 2125435 2392951 := bstep (se 1 (by rfl) ⟨1794713, by rfl⟩ : syracuseStep 2392951 = 3589427) B3589427
theorem B3190601 : Blo 2125435 3190601 := bstep (se 2 (by rfl) ⟨1196475, by rfl⟩ : syracuseStep 3190601 = 2392951) B2392951
theorem B2127067 : Blo 2125435 2127067 := bstep (se 1 (by rfl) ⟨1595300, by rfl⟩ : syracuseStep 2127067 = 3190601) B3190601
theorem B5457613 : Blo 2125435 5457613 := bbase (se 3 (by rfl) ⟨1023302, by rfl⟩ : syracuseStep 5457613 = 2046605) (by norm_num)
theorem B7276817 : Blo 2125435 7276817 := bstep (se 2 (by rfl) ⟨2728806, by rfl⟩ : syracuseStep 7276817 = 5457613) B5457613
theorem B4851211 : Blo 2125435 4851211 := bstep (se 1 (by rfl) ⟨3638408, by rfl⟩ : syracuseStep 4851211 = 7276817) B7276817
theorem B6468281 : Blo 2125435 6468281 := bstep (se 2 (by rfl) ⟨2425605, by rfl⟩ : syracuseStep 6468281 = 4851211) B4851211
theorem B4312187 : Blo 2125435 4312187 := bstep (se 1 (by rfl) ⟨3234140, by rfl⟩ : syracuseStep 4312187 = 6468281) B6468281
theorem B2874791 : Blo 2125435 2874791 := bstep (se 1 (by rfl) ⟨2156093, by rfl⟩ : syracuseStep 2874791 = 4312187) B4312187
theorem B7666109 : Blo 2125435 7666109 := bstep (se 3 (by rfl) ⟨1437395, by rfl⟩ : syracuseStep 7666109 = 2874791) B2874791
theorem B5110739 : Blo 2125435 5110739 := bstep (se 1 (by rfl) ⟨3833054, by rfl⟩ : syracuseStep 5110739 = 7666109) B7666109
theorem B3407159 : Blo 2125435 3407159 := bstep (se 1 (by rfl) ⟨2555369, by rfl⟩ : syracuseStep 3407159 = 5110739) B5110739
theorem B2271439 : Blo 2125435 2271439 := bstep (se 1 (by rfl) ⟨1703579, by rfl⟩ : syracuseStep 2271439 = 3407159) B3407159
theorem B3028585 : Blo 2125435 3028585 := bstep (se 2 (by rfl) ⟨1135719, by rfl⟩ : syracuseStep 3028585 = 2271439) B2271439
theorem B4038113 : Blo 2125435 4038113 := bstep (se 2 (by rfl) ⟨1514292, by rfl⟩ : syracuseStep 4038113 = 3028585) B3028585
theorem B10768301 : Blo 2125435 10768301 := bstep (se 3 (by rfl) ⟨2019056, by rfl⟩ : syracuseStep 10768301 = 4038113) B4038113
theorem B7178867 : Blo 2125435 7178867 := bstep (se 1 (by rfl) ⟨5384150, by rfl⟩ : syracuseStep 7178867 = 10768301) B10768301
theorem B4785911 : Blo 2125435 4785911 := bstep (se 1 (by rfl) ⟨3589433, by rfl⟩ : syracuseStep 4785911 = 7178867) B7178867
theorem B3190607 : Blo 2125435 3190607 := bstep (se 1 (by rfl) ⟨2392955, by rfl⟩ : syracuseStep 3190607 = 4785911) B4785911
theorem B2127071 : Blo 2125435 2127071 := bstep (se 1 (by rfl) ⟨1595303, by rfl⟩ : syracuseStep 2127071 = 3190607) B3190607
theorem B3190613 : Blo 2125435 3190613 := bbase (se 9 (by rfl) ⟨9347, by rfl⟩ : syracuseStep 3190613 = 18695) (by norm_num)
theorem B2127075 : Blo 2125435 2127075 := bstep (se 1 (by rfl) ⟨1595306, by rfl⟩ : syracuseStep 2127075 = 3190613) B3190613
theorem B2156101 : Blo 2125435 2156101 := bbase (se 4 (by rfl) ⟨202134, by rfl⟩ : syracuseStep 2156101 = 404269) (by norm_num)
theorem B11499205 : Blo 2125435 11499205 := bstep (se 4 (by rfl) ⟨1078050, by rfl⟩ : syracuseStep 11499205 = 2156101) B2156101
theorem B15332273 : Blo 2125435 15332273 := bstep (se 2 (by rfl) ⟨5749602, by rfl⟩ : syracuseStep 15332273 = 11499205) B11499205
theorem B10221515 : Blo 2125435 10221515 := bstep (se 1 (by rfl) ⟨7666136, by rfl⟩ : syracuseStep 10221515 = 15332273) B15332273
theorem B6814343 : Blo 2125435 6814343 := bstep (se 1 (by rfl) ⟨5110757, by rfl⟩ : syracuseStep 6814343 = 10221515) B10221515
theorem B4542895 : Blo 2125435 4542895 := bstep (se 1 (by rfl) ⟨3407171, by rfl⟩ : syracuseStep 4542895 = 6814343) B6814343
theorem B6057193 : Blo 2125435 6057193 := bstep (se 2 (by rfl) ⟨2271447, by rfl⟩ : syracuseStep 6057193 = 4542895) B4542895
theorem B8076257 : Blo 2125435 8076257 := bstep (se 2 (by rfl) ⟨3028596, by rfl⟩ : syracuseStep 8076257 = 6057193) B6057193
theorem B5384171 : Blo 2125435 5384171 := bstep (se 1 (by rfl) ⟨4038128, by rfl⟩ : syracuseStep 5384171 = 8076257) B8076257
theorem B3589447 : Blo 2125435 3589447 := bstep (se 1 (by rfl) ⟨2692085, by rfl⟩ : syracuseStep 3589447 = 5384171) B5384171
theorem B4785929 : Blo 2125435 4785929 := bstep (se 2 (by rfl) ⟨1794723, by rfl⟩ : syracuseStep 4785929 = 3589447) B3589447
theorem B3190619 : Blo 2125435 3190619 := bstep (se 1 (by rfl) ⟨2392964, by rfl⟩ : syracuseStep 3190619 = 4785929) B4785929
theorem B2127079 : Blo 2125435 2127079 := bstep (se 1 (by rfl) ⟨1595309, by rfl⟩ : syracuseStep 2127079 = 3190619) B3190619
theorem B2392969 : Blo 2125435 2392969 := bbase (se 2 (by rfl) ⟨897363, by rfl⟩ : syracuseStep 2392969 = 1794727) (by norm_num)
theorem B3190625 : Blo 2125435 3190625 := bstep (se 2 (by rfl) ⟨1196484, by rfl⟩ : syracuseStep 3190625 = 2392969) B2392969
theorem B2127083 : Blo 2125435 2127083 := bstep (se 1 (by rfl) ⟨1595312, by rfl⟩ : syracuseStep 2127083 = 3190625) B3190625
theorem B21291317 : Blo 2125435 21291317 := bbase (se 5 (by rfl) ⟨998030, by rfl⟩ : syracuseStep 21291317 = 1996061) (by norm_num)
theorem B14194211 : Blo 2125435 14194211 := bstep (se 1 (by rfl) ⟨10645658, by rfl⟩ : syracuseStep 14194211 = 21291317) B21291317
theorem B37851229 : Blo 2125435 37851229 := bstep (se 3 (by rfl) ⟨7097105, by rfl⟩ : syracuseStep 37851229 = 14194211) B14194211
theorem B50468305 : Blo 2125435 50468305 := bstep (se 2 (by rfl) ⟨18925614, by rfl⟩ : syracuseStep 50468305 = 37851229) B37851229
theorem B67291073 : Blo 2125435 67291073 := bstep (se 2 (by rfl) ⟨25234152, by rfl⟩ : syracuseStep 67291073 = 50468305) B50468305
theorem B44860715 : Blo 2125435 44860715 := bstep (se 1 (by rfl) ⟨33645536, by rfl⟩ : syracuseStep 44860715 = 67291073) B67291073
theorem B29907143 : Blo 2125435 29907143 := bstep (se 1 (by rfl) ⟨22430357, by rfl⟩ : syracuseStep 29907143 = 44860715) B44860715
theorem B19938095 : Blo 2125435 19938095 := bstep (se 1 (by rfl) ⟨14953571, by rfl⟩ : syracuseStep 19938095 = 29907143) B29907143
theorem B13292063 : Blo 2125435 13292063 := bstep (se 1 (by rfl) ⟨9969047, by rfl⟩ : syracuseStep 13292063 = 19938095) B19938095
theorem B8861375 : Blo 2125435 8861375 := bstep (se 1 (by rfl) ⟨6646031, by rfl⟩ : syracuseStep 8861375 = 13292063) B13292063
theorem B5907583 : Blo 2125435 5907583 := bstep (se 1 (by rfl) ⟨4430687, by rfl⟩ : syracuseStep 5907583 = 8861375) B8861375
theorem B7876777 : Blo 2125435 7876777 := bstep (se 2 (by rfl) ⟨2953791, by rfl⟩ : syracuseStep 7876777 = 5907583) B5907583
theorem B10502369 : Blo 2125435 10502369 := bstep (se 2 (by rfl) ⟨3938388, by rfl⟩ : syracuseStep 10502369 = 7876777) B7876777
theorem B7001579 : Blo 2125435 7001579 := bstep (se 1 (by rfl) ⟨5251184, by rfl⟩ : syracuseStep 7001579 = 10502369) B10502369
theorem B4667719 : Blo 2125435 4667719 := bstep (se 1 (by rfl) ⟨3500789, by rfl⟩ : syracuseStep 4667719 = 7001579) B7001579
theorem B6223625 : Blo 2125435 6223625 := bstep (se 2 (by rfl) ⟨2333859, by rfl⟩ : syracuseStep 6223625 = 4667719) B4667719
theorem B4149083 : Blo 2125435 4149083 := bstep (se 1 (by rfl) ⟨3111812, by rfl⟩ : syracuseStep 4149083 = 6223625) B6223625
theorem B11064221 : Blo 2125435 11064221 := bstep (se 3 (by rfl) ⟨2074541, by rfl⟩ : syracuseStep 11064221 = 4149083) B4149083
theorem B7376147 : Blo 2125435 7376147 := bstep (se 1 (by rfl) ⟨5532110, by rfl⟩ : syracuseStep 7376147 = 11064221) B11064221
theorem B78678901 : Blo 2125435 78678901 := bstep (se 5 (by rfl) ⟨3688073, by rfl⟩ : syracuseStep 78678901 = 7376147) B7376147
theorem B104905201 : Blo 2125435 104905201 := bstep (se 2 (by rfl) ⟨39339450, by rfl⟩ : syracuseStep 104905201 = 78678901) B78678901
theorem B139873601 : Blo 2125435 139873601 := bstep (se 2 (by rfl) ⟨52452600, by rfl⟩ : syracuseStep 139873601 = 104905201) B104905201
theorem B93249067 : Blo 2125435 93249067 := bstep (se 1 (by rfl) ⟨69936800, by rfl⟩ : syracuseStep 93249067 = 139873601) B139873601
theorem B124332089 : Blo 2125435 124332089 := bstep (se 2 (by rfl) ⟨46624533, by rfl⟩ : syracuseStep 124332089 = 93249067) B93249067
theorem B331552237 : Blo 2125435 331552237 := bstep (se 3 (by rfl) ⟨62166044, by rfl⟩ : syracuseStep 331552237 = 124332089) B124332089
theorem B442069649 : Blo 2125435 442069649 := bstep (se 2 (by rfl) ⟨165776118, by rfl⟩ : syracuseStep 442069649 = 331552237) B331552237
theorem B294713099 : Blo 2125435 294713099 := bstep (se 1 (by rfl) ⟨221034824, by rfl⟩ : syracuseStep 294713099 = 442069649) B442069649
theorem B196475399 : Blo 2125435 196475399 := bstep (se 1 (by rfl) ⟨147356549, by rfl⟩ : syracuseStep 196475399 = 294713099) B294713099
theorem B130983599 : Blo 2125435 130983599 := bstep (se 1 (by rfl) ⟨98237699, by rfl⟩ : syracuseStep 130983599 = 196475399) B196475399
theorem B349289597 : Blo 2125435 349289597 := bstep (se 3 (by rfl) ⟨65491799, by rfl⟩ : syracuseStep 349289597 = 130983599) B130983599
theorem B232859731 : Blo 2125435 232859731 := bstep (se 1 (by rfl) ⟨174644798, by rfl⟩ : syracuseStep 232859731 = 349289597) B349289597
theorem B310479641 : Blo 2125435 310479641 := bstep (se 2 (by rfl) ⟨116429865, by rfl⟩ : syracuseStep 310479641 = 232859731) B232859731
theorem B206986427 : Blo 2125435 206986427 := bstep (se 1 (by rfl) ⟨155239820, by rfl⟩ : syracuseStep 206986427 = 310479641) B310479641
theorem B137990951 : Blo 2125435 137990951 := bstep (se 1 (by rfl) ⟨103493213, by rfl⟩ : syracuseStep 137990951 = 206986427) B206986427
theorem B91993967 : Blo 2125435 91993967 := bstep (se 1 (by rfl) ⟨68995475, by rfl⟩ : syracuseStep 91993967 = 137990951) B137990951
theorem B61329311 : Blo 2125435 61329311 := bstep (se 1 (by rfl) ⟨45996983, by rfl⟩ : syracuseStep 61329311 = 91993967) B91993967
theorem B40886207 : Blo 2125435 40886207 := bstep (se 1 (by rfl) ⟨30664655, by rfl⟩ : syracuseStep 40886207 = 61329311) B61329311
theorem B27257471 : Blo 2125435 27257471 := bstep (se 1 (by rfl) ⟨20443103, by rfl⟩ : syracuseStep 27257471 = 40886207) B40886207
theorem B18171647 : Blo 2125435 18171647 := bstep (se 1 (by rfl) ⟨13628735, by rfl⟩ : syracuseStep 18171647 = 27257471) B27257471
theorem B12114431 : Blo 2125435 12114431 := bstep (se 1 (by rfl) ⟨9085823, by rfl⟩ : syracuseStep 12114431 = 18171647) B18171647
theorem B8076287 : Blo 2125435 8076287 := bstep (se 1 (by rfl) ⟨6057215, by rfl⟩ : syracuseStep 8076287 = 12114431) B12114431
theorem B5384191 : Blo 2125435 5384191 := bstep (se 1 (by rfl) ⟨4038143, by rfl⟩ : syracuseStep 5384191 = 8076287) B8076287
theorem B7178921 : Blo 2125435 7178921 := bstep (se 2 (by rfl) ⟨2692095, by rfl⟩ : syracuseStep 7178921 = 5384191) B5384191
theorem B4785947 : Blo 2125435 4785947 := bstep (se 1 (by rfl) ⟨3589460, by rfl⟩ : syracuseStep 4785947 = 7178921) B7178921
theorem B3190631 : Blo 2125435 3190631 := bstep (se 1 (by rfl) ⟨2392973, by rfl⟩ : syracuseStep 3190631 = 4785947) B4785947
theorem B2127087 : Blo 2125435 2127087 := bstep (se 1 (by rfl) ⟨1595315, by rfl⟩ : syracuseStep 2127087 = 3190631) B3190631
theorem B3190637 : Blo 2125435 3190637 := bbase (se 3 (by rfl) ⟨598244, by rfl⟩ : syracuseStep 3190637 = 1196489) (by norm_num)
theorem B2127091 : Blo 2125435 2127091 := bstep (se 1 (by rfl) ⟨1595318, by rfl⟩ : syracuseStep 2127091 = 3190637) B3190637
theorem B4785965 : Blo 2125435 4785965 := bbase (se 3 (by rfl) ⟨897368, by rfl⟩ : syracuseStep 4785965 = 1794737) (by norm_num)
theorem B3190643 : Blo 2125435 3190643 := bstep (se 1 (by rfl) ⟨2392982, by rfl⟩ : syracuseStep 3190643 = 4785965) B4785965
theorem B2127095 : Blo 2125435 2127095 := bstep (se 1 (by rfl) ⟨1595321, by rfl⟩ : syracuseStep 2127095 = 3190643) B3190643
theorem B9085877 : Blo 2125435 9085877 := bbase (se 5 (by rfl) ⟨425900, by rfl⟩ : syracuseStep 9085877 = 851801) (by norm_num)
theorem B6057251 : Blo 2125435 6057251 := bstep (se 1 (by rfl) ⟨4542938, by rfl⟩ : syracuseStep 6057251 = 9085877) B9085877
theorem B4038167 : Blo 2125435 4038167 := bstep (se 1 (by rfl) ⟨3028625, by rfl⟩ : syracuseStep 4038167 = 6057251) B6057251
theorem B2692111 : Blo 2125435 2692111 := bstep (se 1 (by rfl) ⟨2019083, by rfl⟩ : syracuseStep 2692111 = 4038167) B4038167
theorem B3589481 : Blo 2125435 3589481 := bstep (se 2 (by rfl) ⟨1346055, by rfl⟩ : syracuseStep 3589481 = 2692111) B2692111
theorem B2392987 : Blo 2125435 2392987 := bstep (se 1 (by rfl) ⟨1794740, by rfl⟩ : syracuseStep 2392987 = 3589481) B3589481
theorem B3190649 : Blo 2125435 3190649 := bstep (se 2 (by rfl) ⟨1196493, by rfl⟩ : syracuseStep 3190649 = 2392987) B2392987
theorem B2127099 : Blo 2125435 2127099 := bstep (se 1 (by rfl) ⟨1595324, by rfl⟩ : syracuseStep 2127099 = 3190649) B3190649
theorem B8624501 : Blo 2125435 8624501 := bbase (se 5 (by rfl) ⟨404273, by rfl⟩ : syracuseStep 8624501 = 808547) (by norm_num)
theorem B5749667 : Blo 2125435 5749667 := bstep (se 1 (by rfl) ⟨4312250, by rfl⟩ : syracuseStep 5749667 = 8624501) B8624501
theorem B3833111 : Blo 2125435 3833111 := bstep (se 1 (by rfl) ⟨2874833, by rfl⟩ : syracuseStep 3833111 = 5749667) B5749667
theorem B2555407 : Blo 2125435 2555407 := bstep (se 1 (by rfl) ⟨1916555, by rfl⟩ : syracuseStep 2555407 = 3833111) B3833111
theorem B13628837 : Blo 2125435 13628837 := bstep (se 4 (by rfl) ⟨1277703, by rfl⟩ : syracuseStep 13628837 = 2555407) B2555407
theorem B36343565 : Blo 2125435 36343565 := bstep (se 3 (by rfl) ⟨6814418, by rfl⟩ : syracuseStep 36343565 = 13628837) B13628837
theorem B24229043 : Blo 2125435 24229043 := bstep (se 1 (by rfl) ⟨18171782, by rfl⟩ : syracuseStep 24229043 = 36343565) B36343565
theorem B16152695 : Blo 2125435 16152695 := bstep (se 1 (by rfl) ⟨12114521, by rfl⟩ : syracuseStep 16152695 = 24229043) B24229043
theorem B10768463 : Blo 2125435 10768463 := bstep (se 1 (by rfl) ⟨8076347, by rfl⟩ : syracuseStep 10768463 = 16152695) B16152695
theorem B7178975 : Blo 2125435 7178975 := bstep (se 1 (by rfl) ⟨5384231, by rfl⟩ : syracuseStep 7178975 = 10768463) B10768463
theorem B4785983 : Blo 2125435 4785983 := bstep (se 1 (by rfl) ⟨3589487, by rfl⟩ : syracuseStep 4785983 = 7178975) B7178975
theorem B3190655 : Blo 2125435 3190655 := bstep (se 1 (by rfl) ⟨2392991, by rfl⟩ : syracuseStep 3190655 = 4785983) B4785983
theorem B2127103 : Blo 2125435 2127103 := bstep (se 1 (by rfl) ⟨1595327, by rfl⟩ : syracuseStep 2127103 = 3190655) B3190655
theorem B3190661 : Blo 2125435 3190661 := bbase (se 4 (by rfl) ⟨299124, by rfl⟩ : syracuseStep 3190661 = 598249) (by norm_num)
theorem B2127107 : Blo 2125435 2127107 := bstep (se 1 (by rfl) ⟨1595330, by rfl⟩ : syracuseStep 2127107 = 3190661) B3190661
theorem B3589501 : Blo 2125435 3589501 := bbase (se 3 (by rfl) ⟨673031, by rfl⟩ : syracuseStep 3589501 = 1346063) (by norm_num)
theorem B4786001 : Blo 2125435 4786001 := bstep (se 2 (by rfl) ⟨1794750, by rfl⟩ : syracuseStep 4786001 = 3589501) B3589501
theorem B3190667 : Blo 2125435 3190667 := bstep (se 1 (by rfl) ⟨2393000, by rfl⟩ : syracuseStep 3190667 = 4786001) B4786001
theorem B2127111 : Blo 2125435 2127111 := bstep (se 1 (by rfl) ⟨1595333, by rfl⟩ : syracuseStep 2127111 = 3190667) B3190667
theorem B2393005 : Blo 2125435 2393005 := bbase (se 3 (by rfl) ⟨448688, by rfl⟩ : syracuseStep 2393005 = 897377) (by norm_num)
theorem B3190673 : Blo 2125435 3190673 := bstep (se 2 (by rfl) ⟨1196502, by rfl⟩ : syracuseStep 3190673 = 2393005) B2393005
theorem B2127115 : Blo 2125435 2127115 := bstep (se 1 (by rfl) ⟨1595336, by rfl⟩ : syracuseStep 2127115 = 3190673) B3190673
theorem B7179029 : Blo 2125435 7179029 := bbase (se 6 (by rfl) ⟨168258, by rfl⟩ : syracuseStep 7179029 = 336517) (by norm_num)
theorem B4786019 : Blo 2125435 4786019 := bstep (se 1 (by rfl) ⟨3589514, by rfl⟩ : syracuseStep 4786019 = 7179029) B7179029
theorem B3190679 : Blo 2125435 3190679 := bstep (se 1 (by rfl) ⟨2393009, by rfl⟩ : syracuseStep 3190679 = 4786019) B4786019
theorem B2127119 : Blo 2125435 2127119 := bstep (se 1 (by rfl) ⟨1595339, by rfl⟩ : syracuseStep 2127119 = 3190679) B3190679
theorem B3190685 : Blo 2125435 3190685 := bbase (se 3 (by rfl) ⟨598253, by rfl⟩ : syracuseStep 3190685 = 1196507) (by norm_num)
theorem B2127123 : Blo 2125435 2127123 := bstep (se 1 (by rfl) ⟨1595342, by rfl⟩ : syracuseStep 2127123 = 3190685) B3190685
theorem B4786037 : Blo 2125435 4786037 := bbase (se 5 (by rfl) ⟨224345, by rfl⟩ : syracuseStep 4786037 = 448691) (by norm_num)
theorem B3190691 : Blo 2125435 3190691 := bstep (se 1 (by rfl) ⟨2393018, by rfl⟩ : syracuseStep 3190691 = 4786037) B4786037
theorem B2127127 : Blo 2125435 2127127 := bstep (se 1 (by rfl) ⟨1595345, by rfl⟩ : syracuseStep 2127127 = 3190691) B3190691
theorem B14554037 : Blo 2125435 14554037 := bbase (se 5 (by rfl) ⟨682220, by rfl⟩ : syracuseStep 14554037 = 1364441) (by norm_num)
theorem B38810765 : Blo 2125435 38810765 := bstep (se 3 (by rfl) ⟨7277018, by rfl⟩ : syracuseStep 38810765 = 14554037) B14554037
theorem B25873843 : Blo 2125435 25873843 := bstep (se 1 (by rfl) ⟨19405382, by rfl⟩ : syracuseStep 25873843 = 38810765) B38810765
theorem B34498457 : Blo 2125435 34498457 := bstep (se 2 (by rfl) ⟨12936921, by rfl⟩ : syracuseStep 34498457 = 25873843) B25873843
theorem B22998971 : Blo 2125435 22998971 := bstep (se 1 (by rfl) ⟨17249228, by rfl⟩ : syracuseStep 22998971 = 34498457) B34498457
theorem B15332647 : Blo 2125435 15332647 := bstep (se 1 (by rfl) ⟨11499485, by rfl⟩ : syracuseStep 15332647 = 22998971) B22998971
theorem B20443529 : Blo 2125435 20443529 := bstep (se 2 (by rfl) ⟨7666323, by rfl⟩ : syracuseStep 20443529 = 15332647) B15332647
theorem B13629019 : Blo 2125435 13629019 := bstep (se 1 (by rfl) ⟨10221764, by rfl⟩ : syracuseStep 13629019 = 20443529) B20443529
theorem B18172025 : Blo 2125435 18172025 := bstep (se 2 (by rfl) ⟨6814509, by rfl⟩ : syracuseStep 18172025 = 13629019) B13629019
theorem B12114683 : Blo 2125435 12114683 := bstep (se 1 (by rfl) ⟨9086012, by rfl⟩ : syracuseStep 12114683 = 18172025) B18172025
theorem B8076455 : Blo 2125435 8076455 := bstep (se 1 (by rfl) ⟨6057341, by rfl⟩ : syracuseStep 8076455 = 12114683) B12114683
theorem B5384303 : Blo 2125435 5384303 := bstep (se 1 (by rfl) ⟨4038227, by rfl⟩ : syracuseStep 5384303 = 8076455) B8076455
theorem B3589535 : Blo 2125435 3589535 := bstep (se 1 (by rfl) ⟨2692151, by rfl⟩ : syracuseStep 3589535 = 5384303) B5384303
theorem B2393023 : Blo 2125435 2393023 := bstep (se 1 (by rfl) ⟨1794767, by rfl⟩ : syracuseStep 2393023 = 3589535) B3589535
theorem B3190697 : Blo 2125435 3190697 := bstep (se 2 (by rfl) ⟨1196511, by rfl⟩ : syracuseStep 3190697 = 2393023) B2393023
theorem B2127131 : Blo 2125435 2127131 := bstep (se 1 (by rfl) ⟨1595348, by rfl⟩ : syracuseStep 2127131 = 3190697) B3190697
theorem B8076469 : Blo 2125435 8076469 := bbase (se 5 (by rfl) ⟨378584, by rfl⟩ : syracuseStep 8076469 = 757169) (by norm_num)
theorem B10768625 : Blo 2125435 10768625 := bstep (se 2 (by rfl) ⟨4038234, by rfl⟩ : syracuseStep 10768625 = 8076469) B8076469
theorem B7179083 : Blo 2125435 7179083 := bstep (se 1 (by rfl) ⟨5384312, by rfl⟩ : syracuseStep 7179083 = 10768625) B10768625
theorem B4786055 : Blo 2125435 4786055 := bstep (se 1 (by rfl) ⟨3589541, by rfl⟩ : syracuseStep 4786055 = 7179083) B7179083
theorem B3190703 : Blo 2125435 3190703 := bstep (se 1 (by rfl) ⟨2393027, by rfl⟩ : syracuseStep 3190703 = 4786055) B4786055
theorem B2127135 : Blo 2125435 2127135 := bstep (se 1 (by rfl) ⟨1595351, by rfl⟩ : syracuseStep 2127135 = 3190703) B3190703
theorem B3190709 : Blo 2125435 3190709 := bbase (se 5 (by rfl) ⟨149564, by rfl⟩ : syracuseStep 3190709 = 299129) (by norm_num)
theorem B2127139 : Blo 2125435 2127139 := bstep (se 1 (by rfl) ⟨1595354, by rfl⟩ : syracuseStep 2127139 = 3190709) B3190709
theorem B5384333 : Blo 2125435 5384333 := bbase (se 3 (by rfl) ⟨1009562, by rfl⟩ : syracuseStep 5384333 = 2019125) (by norm_num)
theorem B3589555 : Blo 2125435 3589555 := bstep (se 1 (by rfl) ⟨2692166, by rfl⟩ : syracuseStep 3589555 = 5384333) B5384333
theorem B4786073 : Blo 2125435 4786073 := bstep (se 2 (by rfl) ⟨1794777, by rfl⟩ : syracuseStep 4786073 = 3589555) B3589555
theorem B3190715 : Blo 2125435 3190715 := bstep (se 1 (by rfl) ⟨2393036, by rfl⟩ : syracuseStep 3190715 = 4786073) B4786073
theorem B2127143 : Blo 2125435 2127143 := bstep (se 1 (by rfl) ⟨1595357, by rfl⟩ : syracuseStep 2127143 = 3190715) B3190715
theorem B2393041 : Blo 2125435 2393041 := bbase (se 2 (by rfl) ⟨897390, by rfl⟩ : syracuseStep 2393041 = 1794781) (by norm_num)
theorem B3190721 : Blo 2125435 3190721 := bstep (se 2 (by rfl) ⟨1196520, by rfl⟩ : syracuseStep 3190721 = 2393041) B2393041
theorem B2127147 : Blo 2125435 2127147 := bstep (se 1 (by rfl) ⟨1595360, by rfl⟩ : syracuseStep 2127147 = 3190721) B3190721
theorem B4312349 : Blo 2125435 4312349 := bbase (se 3 (by rfl) ⟨808565, by rfl⟩ : syracuseStep 4312349 = 1617131) (by norm_num)
theorem B2874899 : Blo 2125435 2874899 := bstep (se 1 (by rfl) ⟨2156174, by rfl⟩ : syracuseStep 2874899 = 4312349) B4312349
theorem B7666397 : Blo 2125435 7666397 := bstep (se 3 (by rfl) ⟨1437449, by rfl⟩ : syracuseStep 7666397 = 2874899) B2874899
theorem B5110931 : Blo 2125435 5110931 := bstep (se 1 (by rfl) ⟨3833198, by rfl⟩ : syracuseStep 5110931 = 7666397) B7666397
theorem B3407287 : Blo 2125435 3407287 := bstep (se 1 (by rfl) ⟨2555465, by rfl⟩ : syracuseStep 3407287 = 5110931) B5110931
theorem B4543049 : Blo 2125435 4543049 := bstep (se 2 (by rfl) ⟨1703643, by rfl⟩ : syracuseStep 4543049 = 3407287) B3407287
theorem B3028699 : Blo 2125435 3028699 := bstep (se 1 (by rfl) ⟨2271524, by rfl⟩ : syracuseStep 3028699 = 4543049) B4543049
theorem B4038265 : Blo 2125435 4038265 := bstep (se 2 (by rfl) ⟨1514349, by rfl⟩ : syracuseStep 4038265 = 3028699) B3028699
theorem B5384353 : Blo 2125435 5384353 := bstep (se 2 (by rfl) ⟨2019132, by rfl⟩ : syracuseStep 5384353 = 4038265) B4038265
theorem B7179137 : Blo 2125435 7179137 := bstep (se 2 (by rfl) ⟨2692176, by rfl⟩ : syracuseStep 7179137 = 5384353) B5384353
theorem B4786091 : Blo 2125435 4786091 := bstep (se 1 (by rfl) ⟨3589568, by rfl⟩ : syracuseStep 4786091 = 7179137) B7179137
theorem B3190727 : Blo 2125435 3190727 := bstep (se 1 (by rfl) ⟨2393045, by rfl⟩ : syracuseStep 3190727 = 4786091) B4786091
theorem B2127151 : Blo 2125435 2127151 := bstep (se 1 (by rfl) ⟨1595363, by rfl⟩ : syracuseStep 2127151 = 3190727) B3190727
theorem B3190733 : Blo 2125435 3190733 := bbase (se 3 (by rfl) ⟨598262, by rfl⟩ : syracuseStep 3190733 = 1196525) (by norm_num)
theorem B2127155 : Blo 2125435 2127155 := bstep (se 1 (by rfl) ⟨1595366, by rfl⟩ : syracuseStep 2127155 = 3190733) B3190733
theorem B4786109 : Blo 2125435 4786109 := bbase (se 3 (by rfl) ⟨897395, by rfl⟩ : syracuseStep 4786109 = 1794791) (by norm_num)
theorem B3190739 : Blo 2125435 3190739 := bstep (se 1 (by rfl) ⟨2393054, by rfl⟩ : syracuseStep 3190739 = 4786109) B4786109
theorem B2127159 : Blo 2125435 2127159 := bstep (se 1 (by rfl) ⟨1595369, by rfl⟩ : syracuseStep 2127159 = 3190739) B3190739
theorem B3589589 : Blo 2125435 3589589 := bbase (se 7 (by rfl) ⟨42065, by rfl⟩ : syracuseStep 3589589 = 84131) (by norm_num)
theorem B2393059 : Blo 2125435 2393059 := bstep (se 1 (by rfl) ⟨1794794, by rfl⟩ : syracuseStep 2393059 = 3589589) B3589589
theorem B3190745 : Blo 2125435 3190745 := bstep (se 2 (by rfl) ⟨1196529, by rfl⟩ : syracuseStep 3190745 = 2393059) B2393059
theorem B2127163 : Blo 2125435 2127163 := bstep (se 1 (by rfl) ⟨1595372, by rfl⟩ : syracuseStep 2127163 = 3190745) B3190745
theorem B9086165 : Blo 2125435 9086165 := bbase (se 7 (by rfl) ⟨106478, by rfl⟩ : syracuseStep 9086165 = 212957) (by norm_num)
theorem B6057443 : Blo 2125435 6057443 := bstep (se 1 (by rfl) ⟨4543082, by rfl⟩ : syracuseStep 6057443 = 9086165) B9086165
theorem B16153181 : Blo 2125435 16153181 := bstep (se 3 (by rfl) ⟨3028721, by rfl⟩ : syracuseStep 16153181 = 6057443) B6057443
theorem B10768787 : Blo 2125435 10768787 := bstep (se 1 (by rfl) ⟨8076590, by rfl⟩ : syracuseStep 10768787 = 16153181) B16153181
theorem B7179191 : Blo 2125435 7179191 := bstep (se 1 (by rfl) ⟨5384393, by rfl⟩ : syracuseStep 7179191 = 10768787) B10768787
theorem B4786127 : Blo 2125435 4786127 := bstep (se 1 (by rfl) ⟨3589595, by rfl⟩ : syracuseStep 4786127 = 7179191) B7179191
theorem B3190751 : Blo 2125435 3190751 := bstep (se 1 (by rfl) ⟨2393063, by rfl⟩ : syracuseStep 3190751 = 4786127) B4786127
theorem B2127167 : Blo 2125435 2127167 := bstep (se 1 (by rfl) ⟨1595375, by rfl⟩ : syracuseStep 2127167 = 3190751) B3190751
theorem B3190757 : Blo 2125435 3190757 := bbase (se 4 (by rfl) ⟨299133, by rfl⟩ : syracuseStep 3190757 = 598267) (by norm_num)
theorem B2127171 : Blo 2125435 2127171 := bstep (se 1 (by rfl) ⟨1595378, by rfl⟩ : syracuseStep 2127171 = 3190757) B3190757
theorem B4312397 : Blo 2125435 4312397 := bbase (se 3 (by rfl) ⟨808574, by rfl⟩ : syracuseStep 4312397 = 1617149) (by norm_num)
theorem B11499725 : Blo 2125435 11499725 := bstep (se 3 (by rfl) ⟨2156198, by rfl⟩ : syracuseStep 11499725 = 4312397) B4312397
theorem B7666483 : Blo 2125435 7666483 := bstep (se 1 (by rfl) ⟨5749862, by rfl⟩ : syracuseStep 7666483 = 11499725) B11499725
theorem B10221977 : Blo 2125435 10221977 := bstep (se 2 (by rfl) ⟨3833241, by rfl⟩ : syracuseStep 10221977 = 7666483) B7666483
theorem B6814651 : Blo 2125435 6814651 := bstep (se 1 (by rfl) ⟨5110988, by rfl⟩ : syracuseStep 6814651 = 10221977) B10221977
theorem B9086201 : Blo 2125435 9086201 := bstep (se 2 (by rfl) ⟨3407325, by rfl⟩ : syracuseStep 9086201 = 6814651) B6814651
theorem B6057467 : Blo 2125435 6057467 := bstep (se 1 (by rfl) ⟨4543100, by rfl⟩ : syracuseStep 6057467 = 9086201) B9086201
theorem B4038311 : Blo 2125435 4038311 := bstep (se 1 (by rfl) ⟨3028733, by rfl⟩ : syracuseStep 4038311 = 6057467) B6057467
theorem B2692207 : Blo 2125435 2692207 := bstep (se 1 (by rfl) ⟨2019155, by rfl⟩ : syracuseStep 2692207 = 4038311) B4038311
theorem B3589609 : Blo 2125435 3589609 := bstep (se 2 (by rfl) ⟨1346103, by rfl⟩ : syracuseStep 3589609 = 2692207) B2692207
theorem B4786145 : Blo 2125435 4786145 := bstep (se 2 (by rfl) ⟨1794804, by rfl⟩ : syracuseStep 4786145 = 3589609) B3589609
theorem B3190763 : Blo 2125435 3190763 := bstep (se 1 (by rfl) ⟨2393072, by rfl⟩ : syracuseStep 3190763 = 4786145) B4786145
theorem B2127175 : Blo 2125435 2127175 := bstep (se 1 (by rfl) ⟨1595381, by rfl⟩ : syracuseStep 2127175 = 3190763) B3190763
theorem B2393077 : Blo 2125435 2393077 := bbase (se 5 (by rfl) ⟨112175, by rfl⟩ : syracuseStep 2393077 = 224351) (by norm_num)
theorem B3190769 : Blo 2125435 3190769 := bstep (se 2 (by rfl) ⟨1196538, by rfl⟩ : syracuseStep 3190769 = 2393077) B2393077
theorem B2127179 : Blo 2125435 2127179 := bstep (se 1 (by rfl) ⟨1595384, by rfl⟩ : syracuseStep 2127179 = 3190769) B3190769
theorem B2692217 : Blo 2125435 2692217 := bbase (se 2 (by rfl) ⟨1009581, by rfl⟩ : syracuseStep 2692217 = 2019163) (by norm_num)
theorem B7179245 : Blo 2125435 7179245 := bstep (se 3 (by rfl) ⟨1346108, by rfl⟩ : syracuseStep 7179245 = 2692217) B2692217
theorem B4786163 : Blo 2125435 4786163 := bstep (se 1 (by rfl) ⟨3589622, by rfl⟩ : syracuseStep 4786163 = 7179245) B7179245
theorem B3190775 : Blo 2125435 3190775 := bstep (se 1 (by rfl) ⟨2393081, by rfl⟩ : syracuseStep 3190775 = 4786163) B4786163
theorem B2127183 : Blo 2125435 2127183 := bstep (se 1 (by rfl) ⟨1595387, by rfl⟩ : syracuseStep 2127183 = 3190775) B3190775
theorem B3190781 : Blo 2125435 3190781 := bbase (se 3 (by rfl) ⟨598271, by rfl⟩ : syracuseStep 3190781 = 1196543) (by norm_num)
theorem B2127187 : Blo 2125435 2127187 := bstep (se 1 (by rfl) ⟨1595390, by rfl⟩ : syracuseStep 2127187 = 3190781) B3190781
theorem B4786181 : Blo 2125435 4786181 := bbase (se 4 (by rfl) ⟨448704, by rfl⟩ : syracuseStep 4786181 = 897409) (by norm_num)
theorem B3190787 : Blo 2125435 3190787 := bstep (se 1 (by rfl) ⟨2393090, by rfl⟩ : syracuseStep 3190787 = 4786181) B4786181
theorem B2127191 : Blo 2125435 2127191 := bstep (se 1 (by rfl) ⟨1595393, by rfl⟩ : syracuseStep 2127191 = 3190787) B3190787
theorem B4038349 : Blo 2125435 4038349 := bbase (se 3 (by rfl) ⟨757190, by rfl⟩ : syracuseStep 4038349 = 1514381) (by norm_num)
theorem B5384465 : Blo 2125435 5384465 := bstep (se 2 (by rfl) ⟨2019174, by rfl⟩ : syracuseStep 5384465 = 4038349) B4038349
theorem B3589643 : Blo 2125435 3589643 := bstep (se 1 (by rfl) ⟨2692232, by rfl⟩ : syracuseStep 3589643 = 5384465) B5384465
theorem B2393095 : Blo 2125435 2393095 := bstep (se 1 (by rfl) ⟨1794821, by rfl⟩ : syracuseStep 2393095 = 3589643) B3589643
theorem B3190793 : Blo 2125435 3190793 := bstep (se 2 (by rfl) ⟨1196547, by rfl⟩ : syracuseStep 3190793 = 2393095) B2393095
theorem B2127195 : Blo 2125435 2127195 := bstep (se 1 (by rfl) ⟨1595396, by rfl⟩ : syracuseStep 2127195 = 3190793) B3190793
theorem B10768949 : Blo 2125435 10768949 := bbase (se 5 (by rfl) ⟨504794, by rfl⟩ : syracuseStep 10768949 = 1009589) (by norm_num)
theorem B7179299 : Blo 2125435 7179299 := bstep (se 1 (by rfl) ⟨5384474, by rfl⟩ : syracuseStep 7179299 = 10768949) B10768949
theorem B4786199 : Blo 2125435 4786199 := bstep (se 1 (by rfl) ⟨3589649, by rfl⟩ : syracuseStep 4786199 = 7179299) B7179299
theorem B3190799 : Blo 2125435 3190799 := bstep (se 1 (by rfl) ⟨2393099, by rfl⟩ : syracuseStep 3190799 = 4786199) B4786199
theorem B2127199 : Blo 2125435 2127199 := bstep (se 1 (by rfl) ⟨1595399, by rfl⟩ : syracuseStep 2127199 = 3190799) B3190799
theorem B3190805 : Blo 2125435 3190805 := bbase (se 6 (by rfl) ⟨74784, by rfl⟩ : syracuseStep 3190805 = 149569) (by norm_num)
theorem B2127203 : Blo 2125435 2127203 := bstep (se 1 (by rfl) ⟨1595402, by rfl⟩ : syracuseStep 2127203 = 3190805) B3190805
theorem B7666597 : Blo 2125435 7666597 := bbase (se 4 (by rfl) ⟨718743, by rfl⟩ : syracuseStep 7666597 = 1437487) (by norm_num)
theorem B10222129 : Blo 2125435 10222129 := bstep (se 2 (by rfl) ⟨3833298, by rfl⟩ : syracuseStep 10222129 = 7666597) B7666597
theorem B13629505 : Blo 2125435 13629505 := bstep (se 2 (by rfl) ⟨5111064, by rfl⟩ : syracuseStep 13629505 = 10222129) B10222129
theorem B18172673 : Blo 2125435 18172673 := bstep (se 2 (by rfl) ⟨6814752, by rfl⟩ : syracuseStep 18172673 = 13629505) B13629505
theorem B12115115 : Blo 2125435 12115115 := bstep (se 1 (by rfl) ⟨9086336, by rfl⟩ : syracuseStep 12115115 = 18172673) B18172673
theorem B8076743 : Blo 2125435 8076743 := bstep (se 1 (by rfl) ⟨6057557, by rfl⟩ : syracuseStep 8076743 = 12115115) B12115115
theorem B5384495 : Blo 2125435 5384495 := bstep (se 1 (by rfl) ⟨4038371, by rfl⟩ : syracuseStep 5384495 = 8076743) B8076743
theorem B3589663 : Blo 2125435 3589663 := bstep (se 1 (by rfl) ⟨2692247, by rfl⟩ : syracuseStep 3589663 = 5384495) B5384495
theorem B4786217 : Blo 2125435 4786217 := bstep (se 2 (by rfl) ⟨1794831, by rfl⟩ : syracuseStep 4786217 = 3589663) B3589663
theorem B3190811 : Blo 2125435 3190811 := bstep (se 1 (by rfl) ⟨2393108, by rfl⟩ : syracuseStep 3190811 = 4786217) B4786217
theorem B2127207 : Blo 2125435 2127207 := bstep (se 1 (by rfl) ⟨1595405, by rfl⟩ : syracuseStep 2127207 = 3190811) B3190811
theorem B2393113 : Blo 2125435 2393113 := bbase (se 2 (by rfl) ⟨897417, by rfl⟩ : syracuseStep 2393113 = 1794835) (by norm_num)
theorem B3190817 : Blo 2125435 3190817 := bstep (se 2 (by rfl) ⟨1196556, by rfl⟩ : syracuseStep 3190817 = 2393113) B2393113
theorem B2127211 : Blo 2125435 2127211 := bstep (se 1 (by rfl) ⟨1595408, by rfl⟩ : syracuseStep 2127211 = 3190817) B3190817
theorem B8076773 : Blo 2125435 8076773 := bbase (se 4 (by rfl) ⟨757197, by rfl⟩ : syracuseStep 8076773 = 1514395) (by norm_num)
theorem B5384515 : Blo 2125435 5384515 := bstep (se 1 (by rfl) ⟨4038386, by rfl⟩ : syracuseStep 5384515 = 8076773) B8076773
theorem B7179353 : Blo 2125435 7179353 := bstep (se 2 (by rfl) ⟨2692257, by rfl⟩ : syracuseStep 7179353 = 5384515) B5384515
theorem B4786235 : Blo 2125435 4786235 := bstep (se 1 (by rfl) ⟨3589676, by rfl⟩ : syracuseStep 4786235 = 7179353) B7179353
theorem B3190823 : Blo 2125435 3190823 := bstep (se 1 (by rfl) ⟨2393117, by rfl⟩ : syracuseStep 3190823 = 4786235) B4786235
theorem B2127215 : Blo 2125435 2127215 := bstep (se 1 (by rfl) ⟨1595411, by rfl⟩ : syracuseStep 2127215 = 3190823) B3190823
theorem B3190829 : Blo 2125435 3190829 := bbase (se 3 (by rfl) ⟨598280, by rfl⟩ : syracuseStep 3190829 = 1196561) (by norm_num)
theorem B2127219 : Blo 2125435 2127219 := bstep (se 1 (by rfl) ⟨1595414, by rfl⟩ : syracuseStep 2127219 = 3190829) B3190829
theorem B4786253 : Blo 2125435 4786253 := bbase (se 3 (by rfl) ⟨897422, by rfl⟩ : syracuseStep 4786253 = 1794845) (by norm_num)
theorem B3190835 : Blo 2125435 3190835 := bstep (se 1 (by rfl) ⟨2393126, by rfl⟩ : syracuseStep 3190835 = 4786253) B4786253
theorem B2127223 : Blo 2125435 2127223 := bstep (se 1 (by rfl) ⟨1595417, by rfl⟩ : syracuseStep 2127223 = 3190835) B3190835
theorem B2692273 : Blo 2125435 2692273 := bbase (se 2 (by rfl) ⟨1009602, by rfl⟩ : syracuseStep 2692273 = 2019205) (by norm_num)
theorem B3589697 : Blo 2125435 3589697 := bstep (se 2 (by rfl) ⟨1346136, by rfl⟩ : syracuseStep 3589697 = 2692273) B2692273
theorem B2393131 : Blo 2125435 2393131 := bstep (se 1 (by rfl) ⟨1794848, by rfl⟩ : syracuseStep 2393131 = 3589697) B3589697
theorem B3190841 : Blo 2125435 3190841 := bstep (se 2 (by rfl) ⟨1196565, by rfl⟩ : syracuseStep 3190841 = 2393131) B2393131
theorem B2127227 : Blo 2125435 2127227 := bstep (se 1 (by rfl) ⟨1595420, by rfl⟩ : syracuseStep 2127227 = 3190841) B3190841
theorem B2555561 : Blo 2125435 2555561 := bbase (se 2 (by rfl) ⟨958335, by rfl⟩ : syracuseStep 2555561 = 1916671) (by norm_num)
theorem B6814829 : Blo 2125435 6814829 := bstep (se 3 (by rfl) ⟨1277780, by rfl⟩ : syracuseStep 6814829 = 2555561) B2555561
theorem B4543219 : Blo 2125435 4543219 := bstep (se 1 (by rfl) ⟨3407414, by rfl⟩ : syracuseStep 4543219 = 6814829) B6814829
theorem B24230501 : Blo 2125435 24230501 := bstep (se 4 (by rfl) ⟨2271609, by rfl⟩ : syracuseStep 24230501 = 4543219) B4543219
theorem B16153667 : Blo 2125435 16153667 := bstep (se 1 (by rfl) ⟨12115250, by rfl⟩ : syracuseStep 16153667 = 24230501) B24230501
theorem B10769111 : Blo 2125435 10769111 := bstep (se 1 (by rfl) ⟨8076833, by rfl⟩ : syracuseStep 10769111 = 16153667) B16153667
theorem B7179407 : Blo 2125435 7179407 := bstep (se 1 (by rfl) ⟨5384555, by rfl⟩ : syracuseStep 7179407 = 10769111) B10769111
theorem B4786271 : Blo 2125435 4786271 := bstep (se 1 (by rfl) ⟨3589703, by rfl⟩ : syracuseStep 4786271 = 7179407) B7179407
theorem B3190847 : Blo 2125435 3190847 := bstep (se 1 (by rfl) ⟨2393135, by rfl⟩ : syracuseStep 3190847 = 4786271) B4786271
theorem B2127231 : Blo 2125435 2127231 := bstep (se 1 (by rfl) ⟨1595423, by rfl⟩ : syracuseStep 2127231 = 3190847) B3190847
theorem B3190853 : Blo 2125435 3190853 := bbase (se 4 (by rfl) ⟨299142, by rfl⟩ : syracuseStep 3190853 = 598285) (by norm_num)
theorem B2127235 : Blo 2125435 2127235 := bstep (se 1 (by rfl) ⟨1595426, by rfl⟩ : syracuseStep 2127235 = 3190853) B3190853
theorem B3589717 : Blo 2125435 3589717 := bbase (se 8 (by rfl) ⟨21033, by rfl⟩ : syracuseStep 3589717 = 42067) (by norm_num)
theorem B4786289 : Blo 2125435 4786289 := bstep (se 2 (by rfl) ⟨1794858, by rfl⟩ : syracuseStep 4786289 = 3589717) B3589717
theorem B3190859 : Blo 2125435 3190859 := bstep (se 1 (by rfl) ⟨2393144, by rfl⟩ : syracuseStep 3190859 = 4786289) B4786289
theorem B2127239 : Blo 2125435 2127239 := bstep (se 1 (by rfl) ⟨1595429, by rfl⟩ : syracuseStep 2127239 = 3190859) B3190859
theorem B2393149 : Blo 2125435 2393149 := bbase (se 3 (by rfl) ⟨448715, by rfl⟩ : syracuseStep 2393149 = 897431) (by norm_num)
theorem B3190865 : Blo 2125435 3190865 := bstep (se 2 (by rfl) ⟨1196574, by rfl⟩ : syracuseStep 3190865 = 2393149) B2393149
theorem B2127243 : Blo 2125435 2127243 := bstep (se 1 (by rfl) ⟨1595432, by rfl⟩ : syracuseStep 2127243 = 3190865) B3190865
theorem B7179461 : Blo 2125435 7179461 := bbase (se 4 (by rfl) ⟨673074, by rfl⟩ : syracuseStep 7179461 = 1346149) (by norm_num)
theorem B4786307 : Blo 2125435 4786307 := bstep (se 1 (by rfl) ⟨3589730, by rfl⟩ : syracuseStep 4786307 = 7179461) B7179461
theorem B3190871 : Blo 2125435 3190871 := bstep (se 1 (by rfl) ⟨2393153, by rfl⟩ : syracuseStep 3190871 = 4786307) B4786307
theorem B2127247 : Blo 2125435 2127247 := bstep (se 1 (by rfl) ⟨1595435, by rfl⟩ : syracuseStep 2127247 = 3190871) B3190871
theorem B3190877 : Blo 2125435 3190877 := bbase (se 3 (by rfl) ⟨598289, by rfl⟩ : syracuseStep 3190877 = 1196579) (by norm_num)
theorem B2127251 : Blo 2125435 2127251 := bstep (se 1 (by rfl) ⟨1595438, by rfl⟩ : syracuseStep 2127251 = 3190877) B3190877
theorem B4786325 : Blo 2125435 4786325 := bbase (se 6 (by rfl) ⟨112179, by rfl⟩ : syracuseStep 4786325 = 224359) (by norm_num)
theorem B3190883 : Blo 2125435 3190883 := bstep (se 1 (by rfl) ⟨2393162, by rfl⟩ : syracuseStep 3190883 = 4786325) B4786325
theorem B2127255 : Blo 2125435 2127255 := bstep (se 1 (by rfl) ⟨1595441, by rfl⟩ : syracuseStep 2127255 = 3190883) B3190883
theorem B3028853 : Blo 2125435 3028853 := bbase (se 5 (by rfl) ⟨141977, by rfl⟩ : syracuseStep 3028853 = 283955) (by norm_num)
theorem B8076941 : Blo 2125435 8076941 := bstep (se 3 (by rfl) ⟨1514426, by rfl⟩ : syracuseStep 8076941 = 3028853) B3028853
theorem B5384627 : Blo 2125435 5384627 := bstep (se 1 (by rfl) ⟨4038470, by rfl⟩ : syracuseStep 5384627 = 8076941) B8076941
theorem B3589751 : Blo 2125435 3589751 := bstep (se 1 (by rfl) ⟨2692313, by rfl⟩ : syracuseStep 3589751 = 5384627) B5384627
theorem B2393167 : Blo 2125435 2393167 := bstep (se 1 (by rfl) ⟨1794875, by rfl⟩ : syracuseStep 2393167 = 3589751) B3589751
theorem B3190889 : Blo 2125435 3190889 := bstep (se 2 (by rfl) ⟨1196583, by rfl⟩ : syracuseStep 3190889 = 2393167) B2393167
theorem B2127259 : Blo 2125435 2127259 := bstep (se 1 (by rfl) ⟨1595444, by rfl⟩ : syracuseStep 2127259 = 3190889) B3190889
theorem B2458921 : Blo 2125435 2458921 := bbase (se 2 (by rfl) ⟨922095, by rfl⟩ : syracuseStep 2458921 = 1844191) (by norm_num)
theorem B3278561 : Blo 2125435 3278561 := bstep (se 2 (by rfl) ⟨1229460, by rfl⟩ : syracuseStep 3278561 = 2458921) B2458921
theorem B8742829 : Blo 2125435 8742829 := bstep (se 3 (by rfl) ⟨1639280, by rfl⟩ : syracuseStep 8742829 = 3278561) B3278561
theorem B11657105 : Blo 2125435 11657105 := bstep (se 2 (by rfl) ⟨4371414, by rfl⟩ : syracuseStep 11657105 = 8742829) B8742829
theorem B7771403 : Blo 2125435 7771403 := bstep (se 1 (by rfl) ⟨5828552, by rfl⟩ : syracuseStep 7771403 = 11657105) B11657105
theorem B5180935 : Blo 2125435 5180935 := bstep (se 1 (by rfl) ⟨3885701, by rfl⟩ : syracuseStep 5180935 = 7771403) B7771403
theorem B6907913 : Blo 2125435 6907913 := bstep (se 2 (by rfl) ⟨2590467, by rfl⟩ : syracuseStep 6907913 = 5180935) B5180935
theorem B4605275 : Blo 2125435 4605275 := bstep (se 1 (by rfl) ⟨3453956, by rfl⟩ : syracuseStep 4605275 = 6907913) B6907913
theorem B12280733 : Blo 2125435 12280733 := bstep (se 3 (by rfl) ⟨2302637, by rfl⟩ : syracuseStep 12280733 = 4605275) B4605275
theorem B8187155 : Blo 2125435 8187155 := bstep (se 1 (by rfl) ⟨6140366, by rfl⟩ : syracuseStep 8187155 = 12280733) B12280733
theorem B5458103 : Blo 2125435 5458103 := bstep (se 1 (by rfl) ⟨4093577, by rfl⟩ : syracuseStep 5458103 = 8187155) B8187155
theorem B3638735 : Blo 2125435 3638735 := bstep (se 1 (by rfl) ⟨2729051, by rfl⟩ : syracuseStep 3638735 = 5458103) B5458103
theorem B2425823 : Blo 2125435 2425823 := bstep (se 1 (by rfl) ⟨1819367, by rfl⟩ : syracuseStep 2425823 = 3638735) B3638735
theorem B25875445 : Blo 2125435 25875445 := bstep (se 5 (by rfl) ⟨1212911, by rfl⟩ : syracuseStep 25875445 = 2425823) B2425823
theorem B34500593 : Blo 2125435 34500593 := bstep (se 2 (by rfl) ⟨12937722, by rfl⟩ : syracuseStep 34500593 = 25875445) B25875445
theorem B23000395 : Blo 2125435 23000395 := bstep (se 1 (by rfl) ⟨17250296, by rfl⟩ : syracuseStep 23000395 = 34500593) B34500593
theorem B30667193 : Blo 2125435 30667193 := bstep (se 2 (by rfl) ⟨11500197, by rfl⟩ : syracuseStep 30667193 = 23000395) B23000395
theorem B20444795 : Blo 2125435 20444795 := bstep (se 1 (by rfl) ⟨15333596, by rfl⟩ : syracuseStep 20444795 = 30667193) B30667193
theorem B13629863 : Blo 2125435 13629863 := bstep (se 1 (by rfl) ⟨10222397, by rfl⟩ : syracuseStep 13629863 = 20444795) B20444795
theorem B9086575 : Blo 2125435 9086575 := bstep (se 1 (by rfl) ⟨6814931, by rfl⟩ : syracuseStep 9086575 = 13629863) B13629863
theorem B12115433 : Blo 2125435 12115433 := bstep (se 2 (by rfl) ⟨4543287, by rfl⟩ : syracuseStep 12115433 = 9086575) B9086575
theorem B8076955 : Blo 2125435 8076955 := bstep (se 1 (by rfl) ⟨6057716, by rfl⟩ : syracuseStep 8076955 = 12115433) B12115433
theorem B10769273 : Blo 2125435 10769273 := bstep (se 2 (by rfl) ⟨4038477, by rfl⟩ : syracuseStep 10769273 = 8076955) B8076955
theorem B7179515 : Blo 2125435 7179515 := bstep (se 1 (by rfl) ⟨5384636, by rfl⟩ : syracuseStep 7179515 = 10769273) B10769273
theorem B4786343 : Blo 2125435 4786343 := bstep (se 1 (by rfl) ⟨3589757, by rfl⟩ : syracuseStep 4786343 = 7179515) B7179515
theorem B3190895 : Blo 2125435 3190895 := bstep (se 1 (by rfl) ⟨2393171, by rfl⟩ : syracuseStep 3190895 = 4786343) B4786343
theorem B2127263 : Blo 2125435 2127263 := bstep (se 1 (by rfl) ⟨1595447, by rfl⟩ : syracuseStep 2127263 = 3190895) B3190895
theorem B3190901 : Blo 2125435 3190901 := bbase (se 5 (by rfl) ⟨149573, by rfl⟩ : syracuseStep 3190901 = 299147) (by norm_num)
theorem B2127267 : Blo 2125435 2127267 := bstep (se 1 (by rfl) ⟨1595450, by rfl⟩ : syracuseStep 2127267 = 3190901) B3190901
theorem B4038493 : Blo 2125435 4038493 := bbase (se 3 (by rfl) ⟨757217, by rfl⟩ : syracuseStep 4038493 = 1514435) (by norm_num)
theorem B5384657 : Blo 2125435 5384657 := bstep (se 2 (by rfl) ⟨2019246, by rfl⟩ : syracuseStep 5384657 = 4038493) B4038493
theorem B3589771 : Blo 2125435 3589771 := bstep (se 1 (by rfl) ⟨2692328, by rfl⟩ : syracuseStep 3589771 = 5384657) B5384657
theorem B4786361 : Blo 2125435 4786361 := bstep (se 2 (by rfl) ⟨1794885, by rfl⟩ : syracuseStep 4786361 = 3589771) B3589771
theorem B3190907 : Blo 2125435 3190907 := bstep (se 1 (by rfl) ⟨2393180, by rfl⟩ : syracuseStep 3190907 = 4786361) B4786361
theorem B2127271 : Blo 2125435 2127271 := bstep (se 1 (by rfl) ⟨1595453, by rfl⟩ : syracuseStep 2127271 = 3190907) B3190907
theorem B2393185 : Blo 2125435 2393185 := bbase (se 2 (by rfl) ⟨897444, by rfl⟩ : syracuseStep 2393185 = 1794889) (by norm_num)
theorem B3190913 : Blo 2125435 3190913 := bstep (se 2 (by rfl) ⟨1196592, by rfl⟩ : syracuseStep 3190913 = 2393185) B2393185
theorem B2127275 : Blo 2125435 2127275 := bstep (se 1 (by rfl) ⟨1595456, by rfl⟩ : syracuseStep 2127275 = 3190913) B3190913
theorem B5384677 : Blo 2125435 5384677 := bbase (se 4 (by rfl) ⟨504813, by rfl⟩ : syracuseStep 5384677 = 1009627) (by norm_num)
theorem B7179569 : Blo 2125435 7179569 := bstep (se 2 (by rfl) ⟨2692338, by rfl⟩ : syracuseStep 7179569 = 5384677) B5384677
theorem B4786379 : Blo 2125435 4786379 := bstep (se 1 (by rfl) ⟨3589784, by rfl⟩ : syracuseStep 4786379 = 7179569) B7179569
theorem B3190919 : Blo 2125435 3190919 := bstep (se 1 (by rfl) ⟨2393189, by rfl⟩ : syracuseStep 3190919 = 4786379) B4786379
theorem B2127279 : Blo 2125435 2127279 := bstep (se 1 (by rfl) ⟨1595459, by rfl⟩ : syracuseStep 2127279 = 3190919) B3190919
theorem B3190925 : Blo 2125435 3190925 := bbase (se 3 (by rfl) ⟨598298, by rfl⟩ : syracuseStep 3190925 = 1196597) (by norm_num)
theorem B2127283 : Blo 2125435 2127283 := bstep (se 1 (by rfl) ⟨1595462, by rfl⟩ : syracuseStep 2127283 = 3190925) B3190925
theorem B4786397 : Blo 2125435 4786397 := bbase (se 3 (by rfl) ⟨897449, by rfl⟩ : syracuseStep 4786397 = 1794899) (by norm_num)
theorem B3190931 : Blo 2125435 3190931 := bstep (se 1 (by rfl) ⟨2393198, by rfl⟩ : syracuseStep 3190931 = 4786397) B4786397
theorem B2127287 : Blo 2125435 2127287 := bstep (se 1 (by rfl) ⟨1595465, by rfl⟩ : syracuseStep 2127287 = 3190931) B3190931
theorem B3589805 : Blo 2125435 3589805 := bbase (se 3 (by rfl) ⟨673088, by rfl⟩ : syracuseStep 3589805 = 1346177) (by norm_num)
theorem B2393203 : Blo 2125435 2393203 := bstep (se 1 (by rfl) ⟨1794902, by rfl⟩ : syracuseStep 2393203 = 3589805) B3589805
theorem B3190937 : Blo 2125435 3190937 := bstep (se 2 (by rfl) ⟨1196601, by rfl⟩ : syracuseStep 3190937 = 2393203) B2393203
theorem B2127291 : Blo 2125435 2127291 := bstep (se 1 (by rfl) ⟨1595468, by rfl⟩ : syracuseStep 2127291 = 3190937) B3190937
theorem B7376869 : Blo 2125435 7376869 := bbase (se 4 (by rfl) ⟨691581, by rfl⟩ : syracuseStep 7376869 = 1383163) (by norm_num)
theorem B9835825 : Blo 2125435 9835825 := bstep (se 2 (by rfl) ⟨3688434, by rfl⟩ : syracuseStep 9835825 = 7376869) B7376869
theorem B13114433 : Blo 2125435 13114433 := bstep (se 2 (by rfl) ⟨4917912, by rfl⟩ : syracuseStep 13114433 = 9835825) B9835825
theorem B34971821 : Blo 2125435 34971821 := bstep (se 3 (by rfl) ⟨6557216, by rfl⟩ : syracuseStep 34971821 = 13114433) B13114433
theorem B23314547 : Blo 2125435 23314547 := bstep (se 1 (by rfl) ⟨17485910, by rfl⟩ : syracuseStep 23314547 = 34971821) B34971821
theorem B15543031 : Blo 2125435 15543031 := bstep (se 1 (by rfl) ⟨11657273, by rfl⟩ : syracuseStep 15543031 = 23314547) B23314547
theorem B20724041 : Blo 2125435 20724041 := bstep (se 2 (by rfl) ⟨7771515, by rfl⟩ : syracuseStep 20724041 = 15543031) B15543031
theorem B13816027 : Blo 2125435 13816027 := bstep (se 1 (by rfl) ⟨10362020, by rfl⟩ : syracuseStep 13816027 = 20724041) B20724041
theorem B73685477 : Blo 2125435 73685477 := bstep (se 4 (by rfl) ⟨6908013, by rfl⟩ : syracuseStep 73685477 = 13816027) B13816027
theorem B196494605 : Blo 2125435 196494605 := bstep (se 3 (by rfl) ⟨36842738, by rfl⟩ : syracuseStep 196494605 = 73685477) B73685477
theorem B130996403 : Blo 2125435 130996403 := bstep (se 1 (by rfl) ⟨98247302, by rfl⟩ : syracuseStep 130996403 = 196494605) B196494605
theorem B87330935 : Blo 2125435 87330935 := bstep (se 1 (by rfl) ⟨65498201, by rfl⟩ : syracuseStep 87330935 = 130996403) B130996403
theorem B58220623 : Blo 2125435 58220623 := bstep (se 1 (by rfl) ⟨43665467, by rfl⟩ : syracuseStep 58220623 = 87330935) B87330935
theorem B77627497 : Blo 2125435 77627497 := bstep (se 2 (by rfl) ⟨29110311, by rfl⟩ : syracuseStep 77627497 = 58220623) B58220623
theorem B103503329 : Blo 2125435 103503329 := bstep (se 2 (by rfl) ⟨38813748, by rfl⟩ : syracuseStep 103503329 = 77627497) B77627497
theorem B69002219 : Blo 2125435 69002219 := bstep (se 1 (by rfl) ⟨51751664, by rfl⟩ : syracuseStep 69002219 = 103503329) B103503329
theorem B46001479 : Blo 2125435 46001479 := bstep (se 1 (by rfl) ⟨34501109, by rfl⟩ : syracuseStep 46001479 = 69002219) B69002219
theorem B61335305 : Blo 2125435 61335305 := bstep (se 2 (by rfl) ⟨23000739, by rfl⟩ : syracuseStep 61335305 = 46001479) B46001479
theorem B40890203 : Blo 2125435 40890203 := bstep (se 1 (by rfl) ⟨30667652, by rfl⟩ : syracuseStep 40890203 = 61335305) B61335305
theorem B27260135 : Blo 2125435 27260135 := bstep (se 1 (by rfl) ⟨20445101, by rfl⟩ : syracuseStep 27260135 = 40890203) B40890203
theorem B18173423 : Blo 2125435 18173423 := bstep (se 1 (by rfl) ⟨13630067, by rfl⟩ : syracuseStep 18173423 = 27260135) B27260135
theorem B12115615 : Blo 2125435 12115615 := bstep (se 1 (by rfl) ⟨9086711, by rfl⟩ : syracuseStep 12115615 = 18173423) B18173423
theorem B16154153 : Blo 2125435 16154153 := bstep (se 2 (by rfl) ⟨6057807, by rfl⟩ : syracuseStep 16154153 = 12115615) B12115615
theorem B10769435 : Blo 2125435 10769435 := bstep (se 1 (by rfl) ⟨8077076, by rfl⟩ : syracuseStep 10769435 = 16154153) B16154153
theorem B7179623 : Blo 2125435 7179623 := bstep (se 1 (by rfl) ⟨5384717, by rfl⟩ : syracuseStep 7179623 = 10769435) B10769435
theorem B4786415 : Blo 2125435 4786415 := bstep (se 1 (by rfl) ⟨3589811, by rfl⟩ : syracuseStep 4786415 = 7179623) B7179623
theorem B3190943 : Blo 2125435 3190943 := bstep (se 1 (by rfl) ⟨2393207, by rfl⟩ : syracuseStep 3190943 = 4786415) B4786415
theorem B2127295 : Blo 2125435 2127295 := bstep (se 1 (by rfl) ⟨1595471, by rfl⟩ : syracuseStep 2127295 = 3190943) B3190943
theorem B3190949 : Blo 2125435 3190949 := bbase (se 4 (by rfl) ⟨299151, by rfl⟩ : syracuseStep 3190949 = 598303) (by norm_num)
theorem B2127299 : Blo 2125435 2127299 := bstep (se 1 (by rfl) ⟨1595474, by rfl⟩ : syracuseStep 2127299 = 3190949) B3190949
theorem B2692369 : Blo 2125435 2692369 := bbase (se 2 (by rfl) ⟨1009638, by rfl⟩ : syracuseStep 2692369 = 2019277) (by norm_num)
theorem B3589825 : Blo 2125435 3589825 := bstep (se 2 (by rfl) ⟨1346184, by rfl⟩ : syracuseStep 3589825 = 2692369) B2692369
theorem B4786433 : Blo 2125435 4786433 := bstep (se 2 (by rfl) ⟨1794912, by rfl⟩ : syracuseStep 4786433 = 3589825) B3589825
theorem B3190955 : Blo 2125435 3190955 := bstep (se 1 (by rfl) ⟨2393216, by rfl⟩ : syracuseStep 3190955 = 4786433) B4786433
theorem B2127303 : Blo 2125435 2127303 := bstep (se 1 (by rfl) ⟨1595477, by rfl⟩ : syracuseStep 2127303 = 3190955) B3190955
theorem B2393221 : Blo 2125435 2393221 := bbase (se 4 (by rfl) ⟨224364, by rfl⟩ : syracuseStep 2393221 = 448729) (by norm_num)
theorem B3190961 : Blo 2125435 3190961 := bstep (se 2 (by rfl) ⟨1196610, by rfl⟩ : syracuseStep 3190961 = 2393221) B2393221
theorem B2127307 : Blo 2125435 2127307 := bstep (se 1 (by rfl) ⟨1595480, by rfl⟩ : syracuseStep 2127307 = 3190961) B3190961
theorem B4851757 : Blo 2125435 4851757 := bbase (se 3 (by rfl) ⟨909704, by rfl⟩ : syracuseStep 4851757 = 1819409) (by norm_num)
theorem B25876037 : Blo 2125435 25876037 := bstep (se 4 (by rfl) ⟨2425878, by rfl⟩ : syracuseStep 25876037 = 4851757) B4851757
theorem B17250691 : Blo 2125435 17250691 := bstep (se 1 (by rfl) ⟨12938018, by rfl⟩ : syracuseStep 17250691 = 25876037) B25876037
theorem B23000921 : Blo 2125435 23000921 := bstep (se 2 (by rfl) ⟨8625345, by rfl⟩ : syracuseStep 23000921 = 17250691) B17250691
theorem B15333947 : Blo 2125435 15333947 := bstep (se 1 (by rfl) ⟨11500460, by rfl⟩ : syracuseStep 15333947 = 23000921) B23000921
theorem B10222631 : Blo 2125435 10222631 := bstep (se 1 (by rfl) ⟨7666973, by rfl⟩ : syracuseStep 10222631 = 15333947) B15333947
theorem B6815087 : Blo 2125435 6815087 := bstep (se 1 (by rfl) ⟨5111315, by rfl⟩ : syracuseStep 6815087 = 10222631) B10222631
theorem B4543391 : Blo 2125435 4543391 := bstep (se 1 (by rfl) ⟨3407543, by rfl⟩ : syracuseStep 4543391 = 6815087) B6815087
theorem B3028927 : Blo 2125435 3028927 := bstep (se 1 (by rfl) ⟨2271695, by rfl⟩ : syracuseStep 3028927 = 4543391) B4543391
theorem B4038569 : Blo 2125435 4038569 := bstep (se 2 (by rfl) ⟨1514463, by rfl⟩ : syracuseStep 4038569 = 3028927) B3028927
theorem B2692379 : Blo 2125435 2692379 := bstep (se 1 (by rfl) ⟨2019284, by rfl⟩ : syracuseStep 2692379 = 4038569) B4038569
theorem B7179677 : Blo 2125435 7179677 := bstep (se 3 (by rfl) ⟨1346189, by rfl⟩ : syracuseStep 7179677 = 2692379) B2692379
theorem B4786451 : Blo 2125435 4786451 := bstep (se 1 (by rfl) ⟨3589838, by rfl⟩ : syracuseStep 4786451 = 7179677) B7179677
theorem B3190967 : Blo 2125435 3190967 := bstep (se 1 (by rfl) ⟨2393225, by rfl⟩ : syracuseStep 3190967 = 4786451) B4786451
theorem B2127311 : Blo 2125435 2127311 := bstep (se 1 (by rfl) ⟨1595483, by rfl⟩ : syracuseStep 2127311 = 3190967) B3190967
theorem B3190973 : Blo 2125435 3190973 := bbase (se 3 (by rfl) ⟨598307, by rfl⟩ : syracuseStep 3190973 = 1196615) (by norm_num)
theorem B2127315 : Blo 2125435 2127315 := bstep (se 1 (by rfl) ⟨1595486, by rfl⟩ : syracuseStep 2127315 = 3190973) B3190973
theorem B4786469 : Blo 2125435 4786469 := bbase (se 4 (by rfl) ⟨448731, by rfl⟩ : syracuseStep 4786469 = 897463) (by norm_num)
theorem B3190979 : Blo 2125435 3190979 := bstep (se 1 (by rfl) ⟨2393234, by rfl⟩ : syracuseStep 3190979 = 4786469) B4786469
theorem B2127319 : Blo 2125435 2127319 := bstep (se 1 (by rfl) ⟨1595489, by rfl⟩ : syracuseStep 2127319 = 3190979) B3190979
theorem B5384789 : Blo 2125435 5384789 := bbase (se 8 (by rfl) ⟨31551, by rfl⟩ : syracuseStep 5384789 = 63103) (by norm_num)
theorem B3589859 : Blo 2125435 3589859 := bstep (se 1 (by rfl) ⟨2692394, by rfl⟩ : syracuseStep 3589859 = 5384789) B5384789
theorem B2393239 : Blo 2125435 2393239 := bstep (se 1 (by rfl) ⟨1794929, by rfl⟩ : syracuseStep 2393239 = 3589859) B3589859
theorem B3190985 : Blo 2125435 3190985 := bstep (se 2 (by rfl) ⟨1196619, by rfl⟩ : syracuseStep 3190985 = 2393239) B2393239
theorem B2127323 : Blo 2125435 2127323 := bstep (se 1 (by rfl) ⟨1595492, by rfl⟩ : syracuseStep 2127323 = 3190985) B3190985
theorem B2425897 : Blo 2125435 2425897 := bbase (se 2 (by rfl) ⟨909711, by rfl⟩ : syracuseStep 2425897 = 1819423) (by norm_num)
theorem B3234529 : Blo 2125435 3234529 := bstep (se 2 (by rfl) ⟨1212948, by rfl⟩ : syracuseStep 3234529 = 2425897) B2425897
theorem B4312705 : Blo 2125435 4312705 := bstep (se 2 (by rfl) ⟨1617264, by rfl⟩ : syracuseStep 4312705 = 3234529) B3234529
theorem B5750273 : Blo 2125435 5750273 := bstep (se 2 (by rfl) ⟨2156352, by rfl⟩ : syracuseStep 5750273 = 4312705) B4312705
theorem B3833515 : Blo 2125435 3833515 := bstep (se 1 (by rfl) ⟨2875136, by rfl⟩ : syracuseStep 3833515 = 5750273) B5750273
theorem B5111353 : Blo 2125435 5111353 := bstep (se 2 (by rfl) ⟨1916757, by rfl⟩ : syracuseStep 5111353 = 3833515) B3833515
theorem B6815137 : Blo 2125435 6815137 := bstep (se 2 (by rfl) ⟨2555676, by rfl⟩ : syracuseStep 6815137 = 5111353) B5111353
theorem B9086849 : Blo 2125435 9086849 := bstep (se 2 (by rfl) ⟨3407568, by rfl⟩ : syracuseStep 9086849 = 6815137) B6815137
theorem B6057899 : Blo 2125435 6057899 := bstep (se 1 (by rfl) ⟨4543424, by rfl⟩ : syracuseStep 6057899 = 9086849) B9086849
theorem B4038599 : Blo 2125435 4038599 := bstep (se 1 (by rfl) ⟨3028949, by rfl⟩ : syracuseStep 4038599 = 6057899) B6057899
theorem B10769597 : Blo 2125435 10769597 := bstep (se 3 (by rfl) ⟨2019299, by rfl⟩ : syracuseStep 10769597 = 4038599) B4038599
theorem B7179731 : Blo 2125435 7179731 := bstep (se 1 (by rfl) ⟨5384798, by rfl⟩ : syracuseStep 7179731 = 10769597) B10769597
theorem B4786487 : Blo 2125435 4786487 := bstep (se 1 (by rfl) ⟨3589865, by rfl⟩ : syracuseStep 4786487 = 7179731) B7179731
theorem B3190991 : Blo 2125435 3190991 := bstep (se 1 (by rfl) ⟨2393243, by rfl⟩ : syracuseStep 3190991 = 4786487) B4786487
theorem B2127327 : Blo 2125435 2127327 := bstep (se 1 (by rfl) ⟨1595495, by rfl⟩ : syracuseStep 2127327 = 3190991) B3190991
theorem B3190997 : Blo 2125435 3190997 := bbase (se 7 (by rfl) ⟨37394, by rfl⟩ : syracuseStep 3190997 = 74789) (by norm_num)
theorem B2127331 : Blo 2125435 2127331 := bstep (se 1 (by rfl) ⟨1595498, by rfl⟩ : syracuseStep 2127331 = 3190997) B3190997
theorem B2271721 : Blo 2125435 2271721 := bbase (se 2 (by rfl) ⟨851895, by rfl⟩ : syracuseStep 2271721 = 1703791) (by norm_num)
theorem B3028961 : Blo 2125435 3028961 := bstep (se 2 (by rfl) ⟨1135860, by rfl⟩ : syracuseStep 3028961 = 2271721) B2271721
theorem B8077229 : Blo 2125435 8077229 := bstep (se 3 (by rfl) ⟨1514480, by rfl⟩ : syracuseStep 8077229 = 3028961) B3028961
theorem B5384819 : Blo 2125435 5384819 := bstep (se 1 (by rfl) ⟨4038614, by rfl⟩ : syracuseStep 5384819 = 8077229) B8077229
theorem B3589879 : Blo 2125435 3589879 := bstep (se 1 (by rfl) ⟨2692409, by rfl⟩ : syracuseStep 3589879 = 5384819) B5384819
theorem B4786505 : Blo 2125435 4786505 := bstep (se 2 (by rfl) ⟨1794939, by rfl⟩ : syracuseStep 4786505 = 3589879) B3589879
theorem B3191003 : Blo 2125435 3191003 := bstep (se 1 (by rfl) ⟨2393252, by rfl⟩ : syracuseStep 3191003 = 4786505) B4786505
theorem B2127335 : Blo 2125435 2127335 := bstep (se 1 (by rfl) ⟨1595501, by rfl⟩ : syracuseStep 2127335 = 3191003) B3191003
theorem B2393257 : Blo 2125435 2393257 := bbase (se 2 (by rfl) ⟨897471, by rfl⟩ : syracuseStep 2393257 = 1794943) (by norm_num)
theorem B3191009 : Blo 2125435 3191009 := bstep (se 2 (by rfl) ⟨1196628, by rfl⟩ : syracuseStep 3191009 = 2393257) B2393257
theorem B2127339 : Blo 2125435 2127339 := bstep (se 1 (by rfl) ⟨1595504, by rfl⟩ : syracuseStep 2127339 = 3191009) B3191009
theorem B9086917 : Blo 2125435 9086917 := bbase (se 4 (by rfl) ⟨851898, by rfl⟩ : syracuseStep 9086917 = 1703797) (by norm_num)
theorem B12115889 : Blo 2125435 12115889 := bstep (se 2 (by rfl) ⟨4543458, by rfl⟩ : syracuseStep 12115889 = 9086917) B9086917
theorem B8077259 : Blo 2125435 8077259 := bstep (se 1 (by rfl) ⟨6057944, by rfl⟩ : syracuseStep 8077259 = 12115889) B12115889
theorem B5384839 : Blo 2125435 5384839 := bstep (se 1 (by rfl) ⟨4038629, by rfl⟩ : syracuseStep 5384839 = 8077259) B8077259
theorem B7179785 : Blo 2125435 7179785 := bstep (se 2 (by rfl) ⟨2692419, by rfl⟩ : syracuseStep 7179785 = 5384839) B5384839
theorem B4786523 : Blo 2125435 4786523 := bstep (se 1 (by rfl) ⟨3589892, by rfl⟩ : syracuseStep 4786523 = 7179785) B7179785
theorem B3191015 : Blo 2125435 3191015 := bstep (se 1 (by rfl) ⟨2393261, by rfl⟩ : syracuseStep 3191015 = 4786523) B4786523
theorem B2127343 : Blo 2125435 2127343 := bstep (se 1 (by rfl) ⟨1595507, by rfl⟩ : syracuseStep 2127343 = 3191015) B3191015
theorem B3191021 : Blo 2125435 3191021 := bbase (se 3 (by rfl) ⟨598316, by rfl⟩ : syracuseStep 3191021 = 1196633) (by norm_num)
theorem B2127347 : Blo 2125435 2127347 := bstep (se 1 (by rfl) ⟨1595510, by rfl⟩ : syracuseStep 2127347 = 3191021) B3191021
theorem B4786541 : Blo 2125435 4786541 := bbase (se 3 (by rfl) ⟨897476, by rfl⟩ : syracuseStep 4786541 = 1794953) (by norm_num)
theorem B3191027 : Blo 2125435 3191027 := bstep (se 1 (by rfl) ⟨2393270, by rfl⟩ : syracuseStep 3191027 = 4786541) B4786541
theorem B2127351 : Blo 2125435 2127351 := bstep (se 1 (by rfl) ⟨1595513, by rfl⟩ : syracuseStep 2127351 = 3191027) B3191027
theorem B4038653 : Blo 2125435 4038653 := bbase (se 3 (by rfl) ⟨757247, by rfl⟩ : syracuseStep 4038653 = 1514495) (by norm_num)
theorem B2692435 : Blo 2125435 2692435 := bstep (se 1 (by rfl) ⟨2019326, by rfl⟩ : syracuseStep 2692435 = 4038653) B4038653
theorem B3589913 : Blo 2125435 3589913 := bstep (se 2 (by rfl) ⟨1346217, by rfl⟩ : syracuseStep 3589913 = 2692435) B2692435
theorem B2393275 : Blo 2125435 2393275 := bstep (se 1 (by rfl) ⟨1794956, by rfl⟩ : syracuseStep 2393275 = 3589913) B3589913
theorem B3191033 : Blo 2125435 3191033 := bstep (se 2 (by rfl) ⟨1196637, by rfl⟩ : syracuseStep 3191033 = 2393275) B2393275
theorem B2127355 : Blo 2125435 2127355 := bstep (se 1 (by rfl) ⟨1595516, by rfl⟩ : syracuseStep 2127355 = 3191033) B3191033
theorem B5111429 : Blo 2125435 5111429 := bbase (se 4 (by rfl) ⟨479196, by rfl⟩ : syracuseStep 5111429 = 958393) (by norm_num)
theorem B54521909 : Blo 2125435 54521909 := bstep (se 5 (by rfl) ⟨2555714, by rfl⟩ : syracuseStep 54521909 = 5111429) B5111429
theorem B36347939 : Blo 2125435 36347939 := bstep (se 1 (by rfl) ⟨27260954, by rfl⟩ : syracuseStep 36347939 = 54521909) B54521909
theorem B24231959 : Blo 2125435 24231959 := bstep (se 1 (by rfl) ⟨18173969, by rfl⟩ : syracuseStep 24231959 = 36347939) B36347939
theorem B16154639 : Blo 2125435 16154639 := bstep (se 1 (by rfl) ⟨12115979, by rfl⟩ : syracuseStep 16154639 = 24231959) B24231959
theorem B10769759 : Blo 2125435 10769759 := bstep (se 1 (by rfl) ⟨8077319, by rfl⟩ : syracuseStep 10769759 = 16154639) B16154639
theorem B7179839 : Blo 2125435 7179839 := bstep (se 1 (by rfl) ⟨5384879, by rfl⟩ : syracuseStep 7179839 = 10769759) B10769759
theorem B4786559 : Blo 2125435 4786559 := bstep (se 1 (by rfl) ⟨3589919, by rfl⟩ : syracuseStep 4786559 = 7179839) B7179839
theorem B3191039 : Blo 2125435 3191039 := bstep (se 1 (by rfl) ⟨2393279, by rfl⟩ : syracuseStep 3191039 = 4786559) B4786559
theorem B2127359 : Blo 2125435 2127359 := bstep (se 1 (by rfl) ⟨1595519, by rfl⟩ : syracuseStep 2127359 = 3191039) B3191039
theorem B3191045 : Blo 2125435 3191045 := bbase (se 4 (by rfl) ⟨299160, by rfl⟩ : syracuseStep 3191045 = 598321) (by norm_num)
theorem B2127363 : Blo 2125435 2127363 := bstep (se 1 (by rfl) ⟨1595522, by rfl⟩ : syracuseStep 2127363 = 3191045) B3191045
theorem B3589933 : Blo 2125435 3589933 := bbase (se 3 (by rfl) ⟨673112, by rfl⟩ : syracuseStep 3589933 = 1346225) (by norm_num)
theorem B4786577 : Blo 2125435 4786577 := bstep (se 2 (by rfl) ⟨1794966, by rfl⟩ : syracuseStep 4786577 = 3589933) B3589933
theorem B3191051 : Blo 2125435 3191051 := bstep (se 1 (by rfl) ⟨2393288, by rfl⟩ : syracuseStep 3191051 = 4786577) B4786577
theorem B2127367 : Blo 2125435 2127367 := bstep (se 1 (by rfl) ⟨1595525, by rfl⟩ : syracuseStep 2127367 = 3191051) B3191051
theorem B2393293 : Blo 2125435 2393293 := bbase (se 3 (by rfl) ⟨448742, by rfl⟩ : syracuseStep 2393293 = 897485) (by norm_num)
theorem B3191057 : Blo 2125435 3191057 := bstep (se 2 (by rfl) ⟨1196646, by rfl⟩ : syracuseStep 3191057 = 2393293) B2393293
theorem B2127371 : Blo 2125435 2127371 := bstep (se 1 (by rfl) ⟨1595528, by rfl⟩ : syracuseStep 2127371 = 3191057) B3191057
theorem B7179893 : Blo 2125435 7179893 := bbase (se 5 (by rfl) ⟨336557, by rfl⟩ : syracuseStep 7179893 = 673115) (by norm_num)
theorem B4786595 : Blo 2125435 4786595 := bstep (se 1 (by rfl) ⟨3589946, by rfl⟩ : syracuseStep 4786595 = 7179893) B7179893
theorem B3191063 : Blo 2125435 3191063 := bstep (se 1 (by rfl) ⟨2393297, by rfl⟩ : syracuseStep 3191063 = 4786595) B4786595
theorem B2127375 : Blo 2125435 2127375 := bstep (se 1 (by rfl) ⟨1595531, by rfl⟩ : syracuseStep 2127375 = 3191063) B3191063
theorem B3191069 : Blo 2125435 3191069 := bbase (se 3 (by rfl) ⟨598325, by rfl⟩ : syracuseStep 3191069 = 1196651) (by norm_num)
theorem B2127379 : Blo 2125435 2127379 := bstep (se 1 (by rfl) ⟨1595534, by rfl⟩ : syracuseStep 2127379 = 3191069) B3191069
theorem B4786613 : Blo 2125435 4786613 := bbase (se 5 (by rfl) ⟨224372, by rfl⟩ : syracuseStep 4786613 = 448745) (by norm_num)
theorem B3191075 : Blo 2125435 3191075 := bstep (se 1 (by rfl) ⟨2393306, by rfl⟩ : syracuseStep 3191075 = 4786613) B4786613
theorem B2127383 : Blo 2125435 2127383 := bstep (se 1 (by rfl) ⟨1595537, by rfl⟩ : syracuseStep 2127383 = 3191075) B3191075
theorem B2555749 : Blo 2125435 2555749 := bbase (se 4 (by rfl) ⟨239601, by rfl⟩ : syracuseStep 2555749 = 479203) (by norm_num)
theorem B3407665 : Blo 2125435 3407665 := bstep (se 2 (by rfl) ⟨1277874, by rfl⟩ : syracuseStep 3407665 = 2555749) B2555749
theorem B4543553 : Blo 2125435 4543553 := bstep (se 2 (by rfl) ⟨1703832, by rfl⟩ : syracuseStep 4543553 = 3407665) B3407665
theorem B12116141 : Blo 2125435 12116141 := bstep (se 3 (by rfl) ⟨2271776, by rfl⟩ : syracuseStep 12116141 = 4543553) B4543553
theorem B8077427 : Blo 2125435 8077427 := bstep (se 1 (by rfl) ⟨6058070, by rfl⟩ : syracuseStep 8077427 = 12116141) B12116141
theorem B5384951 : Blo 2125435 5384951 := bstep (se 1 (by rfl) ⟨4038713, by rfl⟩ : syracuseStep 5384951 = 8077427) B8077427
theorem B3589967 : Blo 2125435 3589967 := bstep (se 1 (by rfl) ⟨2692475, by rfl⟩ : syracuseStep 3589967 = 5384951) B5384951
theorem B2393311 : Blo 2125435 2393311 := bstep (se 1 (by rfl) ⟨1794983, by rfl⟩ : syracuseStep 2393311 = 3589967) B3589967
theorem B3191081 : Blo 2125435 3191081 := bstep (se 2 (by rfl) ⟨1196655, by rfl⟩ : syracuseStep 3191081 = 2393311) B2393311
theorem B2127387 : Blo 2125435 2127387 := bstep (se 1 (by rfl) ⟨1595540, by rfl⟩ : syracuseStep 2127387 = 3191081) B3191081
theorem B6469253 : Blo 2125435 6469253 := bbase (se 4 (by rfl) ⟨606492, by rfl⟩ : syracuseStep 6469253 = 1212985) (by norm_num)
theorem B4312835 : Blo 2125435 4312835 := bstep (se 1 (by rfl) ⟨3234626, by rfl⟩ : syracuseStep 4312835 = 6469253) B6469253
theorem B2875223 : Blo 2125435 2875223 := bstep (se 1 (by rfl) ⟨2156417, by rfl⟩ : syracuseStep 2875223 = 4312835) B4312835
theorem B7667261 : Blo 2125435 7667261 := bstep (se 3 (by rfl) ⟨1437611, by rfl⟩ : syracuseStep 7667261 = 2875223) B2875223
theorem B5111507 : Blo 2125435 5111507 := bstep (se 1 (by rfl) ⟨3833630, by rfl⟩ : syracuseStep 5111507 = 7667261) B7667261
theorem B3407671 : Blo 2125435 3407671 := bstep (se 1 (by rfl) ⟨2555753, by rfl⟩ : syracuseStep 3407671 = 5111507) B5111507
theorem B4543561 : Blo 2125435 4543561 := bstep (se 2 (by rfl) ⟨1703835, by rfl⟩ : syracuseStep 4543561 = 3407671) B3407671
theorem B6058081 : Blo 2125435 6058081 := bstep (se 2 (by rfl) ⟨2271780, by rfl⟩ : syracuseStep 6058081 = 4543561) B4543561
theorem B8077441 : Blo 2125435 8077441 := bstep (se 2 (by rfl) ⟨3029040, by rfl⟩ : syracuseStep 8077441 = 6058081) B6058081
theorem B10769921 : Blo 2125435 10769921 := bstep (se 2 (by rfl) ⟨4038720, by rfl⟩ : syracuseStep 10769921 = 8077441) B8077441
theorem B7179947 : Blo 2125435 7179947 := bstep (se 1 (by rfl) ⟨5384960, by rfl⟩ : syracuseStep 7179947 = 10769921) B10769921
theorem B4786631 : Blo 2125435 4786631 := bstep (se 1 (by rfl) ⟨3589973, by rfl⟩ : syracuseStep 4786631 = 7179947) B7179947
theorem B3191087 : Blo 2125435 3191087 := bstep (se 1 (by rfl) ⟨2393315, by rfl⟩ : syracuseStep 3191087 = 4786631) B4786631
theorem B2127391 : Blo 2125435 2127391 := bstep (se 1 (by rfl) ⟨1595543, by rfl⟩ : syracuseStep 2127391 = 3191087) B3191087
theorem B3191093 : Blo 2125435 3191093 := bbase (se 5 (by rfl) ⟨149582, by rfl⟩ : syracuseStep 3191093 = 299165) (by norm_num)
theorem B2127395 : Blo 2125435 2127395 := bstep (se 1 (by rfl) ⟨1595546, by rfl⟩ : syracuseStep 2127395 = 3191093) B3191093
theorem B5384981 : Blo 2125435 5384981 := bbase (se 6 (by rfl) ⟨126210, by rfl⟩ : syracuseStep 5384981 = 252421) (by norm_num)
theorem B3589987 : Blo 2125435 3589987 := bstep (se 1 (by rfl) ⟨2692490, by rfl⟩ : syracuseStep 3589987 = 5384981) B5384981
theorem B4786649 : Blo 2125435 4786649 := bstep (se 2 (by rfl) ⟨1794993, by rfl⟩ : syracuseStep 4786649 = 3589987) B3589987
theorem B3191099 : Blo 2125435 3191099 := bstep (se 1 (by rfl) ⟨2393324, by rfl⟩ : syracuseStep 3191099 = 4786649) B4786649
theorem B2127399 : Blo 2125435 2127399 := bstep (se 1 (by rfl) ⟨1595549, by rfl⟩ : syracuseStep 2127399 = 3191099) B3191099
theorem B2393329 : Blo 2125435 2393329 := bbase (se 2 (by rfl) ⟨897498, by rfl⟩ : syracuseStep 2393329 = 1794997) (by norm_num)
theorem B3191105 : Blo 2125435 3191105 := bstep (se 2 (by rfl) ⟨1196664, by rfl⟩ : syracuseStep 3191105 = 2393329) B2393329
theorem B2127403 : Blo 2125435 2127403 := bstep (se 1 (by rfl) ⟨1595552, by rfl⟩ : syracuseStep 2127403 = 3191105) B3191105
theorem B6469301 : Blo 2125435 6469301 := bbase (se 5 (by rfl) ⟨303248, by rfl⟩ : syracuseStep 6469301 = 606497) (by norm_num)
theorem B4312867 : Blo 2125435 4312867 := bstep (se 1 (by rfl) ⟨3234650, by rfl⟩ : syracuseStep 4312867 = 6469301) B6469301
theorem B5750489 : Blo 2125435 5750489 := bstep (se 2 (by rfl) ⟨2156433, by rfl⟩ : syracuseStep 5750489 = 4312867) B4312867
theorem B3833659 : Blo 2125435 3833659 := bstep (se 1 (by rfl) ⟨2875244, by rfl⟩ : syracuseStep 3833659 = 5750489) B5750489
theorem B20446181 : Blo 2125435 20446181 := bstep (se 4 (by rfl) ⟨1916829, by rfl⟩ : syracuseStep 20446181 = 3833659) B3833659
theorem B13630787 : Blo 2125435 13630787 := bstep (se 1 (by rfl) ⟨10223090, by rfl⟩ : syracuseStep 13630787 = 20446181) B20446181
theorem B9087191 : Blo 2125435 9087191 := bstep (se 1 (by rfl) ⟨6815393, by rfl⟩ : syracuseStep 9087191 = 13630787) B13630787
theorem B6058127 : Blo 2125435 6058127 := bstep (se 1 (by rfl) ⟨4543595, by rfl⟩ : syracuseStep 6058127 = 9087191) B9087191
theorem B4038751 : Blo 2125435 4038751 := bstep (se 1 (by rfl) ⟨3029063, by rfl⟩ : syracuseStep 4038751 = 6058127) B6058127
theorem B5385001 : Blo 2125435 5385001 := bstep (se 2 (by rfl) ⟨2019375, by rfl⟩ : syracuseStep 5385001 = 4038751) B4038751
theorem B7180001 : Blo 2125435 7180001 := bstep (se 2 (by rfl) ⟨2692500, by rfl⟩ : syracuseStep 7180001 = 5385001) B5385001
theorem B4786667 : Blo 2125435 4786667 := bstep (se 1 (by rfl) ⟨3590000, by rfl⟩ : syracuseStep 4786667 = 7180001) B7180001
theorem B3191111 : Blo 2125435 3191111 := bstep (se 1 (by rfl) ⟨2393333, by rfl⟩ : syracuseStep 3191111 = 4786667) B4786667
theorem B2127407 : Blo 2125435 2127407 := bstep (se 1 (by rfl) ⟨1595555, by rfl⟩ : syracuseStep 2127407 = 3191111) B3191111
theorem B3191117 : Blo 2125435 3191117 := bbase (se 3 (by rfl) ⟨598334, by rfl⟩ : syracuseStep 3191117 = 1196669) (by norm_num)
theorem B2127411 : Blo 2125435 2127411 := bstep (se 1 (by rfl) ⟨1595558, by rfl⟩ : syracuseStep 2127411 = 3191117) B3191117
theorem B4786685 : Blo 2125435 4786685 := bbase (se 3 (by rfl) ⟨897503, by rfl⟩ : syracuseStep 4786685 = 1795007) (by norm_num)
theorem B3191123 : Blo 2125435 3191123 := bstep (se 1 (by rfl) ⟨2393342, by rfl⟩ : syracuseStep 3191123 = 4786685) B4786685
theorem B2127415 : Blo 2125435 2127415 := bstep (se 1 (by rfl) ⟨1595561, by rfl⟩ : syracuseStep 2127415 = 3191123) B3191123
theorem B3590021 : Blo 2125435 3590021 := bbase (se 4 (by rfl) ⟨336564, by rfl⟩ : syracuseStep 3590021 = 673129) (by norm_num)
theorem B2393347 : Blo 2125435 2393347 := bstep (se 1 (by rfl) ⟨1795010, by rfl⟩ : syracuseStep 2393347 = 3590021) B3590021
theorem B3191129 : Blo 2125435 3191129 := bstep (se 2 (by rfl) ⟨1196673, by rfl⟩ : syracuseStep 3191129 = 2393347) B2393347
theorem B2127419 : Blo 2125435 2127419 := bstep (se 1 (by rfl) ⟨1595564, by rfl⟩ : syracuseStep 2127419 = 3191129) B3191129
theorem B16155125 : Blo 2125435 16155125 := bbase (se 5 (by rfl) ⟨757271, by rfl⟩ : syracuseStep 16155125 = 1514543) (by norm_num)
theorem B10770083 : Blo 2125435 10770083 := bstep (se 1 (by rfl) ⟨8077562, by rfl⟩ : syracuseStep 10770083 = 16155125) B16155125
theorem B7180055 : Blo 2125435 7180055 := bstep (se 1 (by rfl) ⟨5385041, by rfl⟩ : syracuseStep 7180055 = 10770083) B10770083
theorem B4786703 : Blo 2125435 4786703 := bstep (se 1 (by rfl) ⟨3590027, by rfl⟩ : syracuseStep 4786703 = 7180055) B7180055
theorem B3191135 : Blo 2125435 3191135 := bstep (se 1 (by rfl) ⟨2393351, by rfl⟩ : syracuseStep 3191135 = 4786703) B4786703
theorem B2127423 : Blo 2125435 2127423 := bstep (se 1 (by rfl) ⟨1595567, by rfl⟩ : syracuseStep 2127423 = 3191135) B3191135
theorem B3191141 : Blo 2125435 3191141 := bbase (se 4 (by rfl) ⟨299169, by rfl⟩ : syracuseStep 3191141 = 598339) (by norm_num)
theorem B2127427 : Blo 2125435 2127427 := bstep (se 1 (by rfl) ⟨1595570, by rfl⟩ : syracuseStep 2127427 = 3191141) B3191141
theorem B4038797 : Blo 2125435 4038797 := bbase (se 3 (by rfl) ⟨757274, by rfl⟩ : syracuseStep 4038797 = 1514549) (by norm_num)
theorem B2692531 : Blo 2125435 2692531 := bstep (se 1 (by rfl) ⟨2019398, by rfl⟩ : syracuseStep 2692531 = 4038797) B4038797
theorem B3590041 : Blo 2125435 3590041 := bstep (se 2 (by rfl) ⟨1346265, by rfl⟩ : syracuseStep 3590041 = 2692531) B2692531
theorem B4786721 : Blo 2125435 4786721 := bstep (se 2 (by rfl) ⟨1795020, by rfl⟩ : syracuseStep 4786721 = 3590041) B3590041
theorem B3191147 : Blo 2125435 3191147 := bstep (se 1 (by rfl) ⟨2393360, by rfl⟩ : syracuseStep 3191147 = 4786721) B4786721
theorem B2127431 : Blo 2125435 2127431 := bstep (se 1 (by rfl) ⟨1595573, by rfl⟩ : syracuseStep 2127431 = 3191147) B3191147
theorem B2393365 : Blo 2125435 2393365 := bbase (se 6 (by rfl) ⟨56094, by rfl⟩ : syracuseStep 2393365 = 112189) (by norm_num)
theorem B3191153 : Blo 2125435 3191153 := bstep (se 2 (by rfl) ⟨1196682, by rfl⟩ : syracuseStep 3191153 = 2393365) B2393365
theorem B2127435 : Blo 2125435 2127435 := bstep (se 1 (by rfl) ⟨1595576, by rfl⟩ : syracuseStep 2127435 = 3191153) B3191153
theorem C0 (j : ℕ) (h1 : 531358 ≤ j) (h2 : j ≤ 531858) : Blo 2125435 (4 * j + 3) := by
  interval_cases j
  · exact B2125435
  · exact B2125439
  · exact B2125443
  · exact B2125447
  · exact B2125451
  · exact B2125455
  · exact B2125459
  · exact B2125463
  · exact B2125467
  · exact B2125471
  · exact B2125475
  · exact B2125479
  · exact B2125483
  · exact B2125487
  · exact B2125491
  · exact B2125495
  · exact B2125499
  · exact B2125503
  · exact B2125507
  · exact B2125511
  · exact B2125515
  · exact B2125519
  · exact B2125523
  · exact B2125527
  · exact B2125531
  · exact B2125535
  · exact B2125539
  · exact B2125543
  · exact B2125547
  · exact B2125551
  · exact B2125555
  · exact B2125559
  · exact B2125563
  · exact B2125567
  · exact B2125571
  · exact B2125575
  · exact B2125579
  · exact B2125583
  · exact B2125587
  · exact B2125591
  · exact B2125595
  · exact B2125599
  · exact B2125603
  · exact B2125607
  · exact B2125611
  · exact B2125615
  · exact B2125619
  · exact B2125623
  · exact B2125627
  · exact B2125631
  · exact B2125635
  · exact B2125639
  · exact B2125643
  · exact B2125647
  · exact B2125651
  · exact B2125655
  · exact B2125659
  · exact B2125663
  · exact B2125667
  · exact B2125671
  · exact B2125675
  · exact B2125679
  · exact B2125683
  · exact B2125687
  · exact B2125691
  · exact B2125695
  · exact B2125699
  · exact B2125703
  · exact B2125707
  · exact B2125711
  · exact B2125715
  · exact B2125719
  · exact B2125723
  · exact B2125727
  · exact B2125731
  · exact B2125735
  · exact B2125739
  · exact B2125743
  · exact B2125747
  · exact B2125751
  · exact B2125755
  · exact B2125759
  · exact B2125763
  · exact B2125767
  · exact B2125771
  · exact B2125775
  · exact B2125779
  · exact B2125783
  · exact B2125787
  · exact B2125791
  · exact B2125795
  · exact B2125799
  · exact B2125803
  · exact B2125807
  · exact B2125811
  · exact B2125815
  · exact B2125819
  · exact B2125823
  · exact B2125827
  · exact B2125831
  · exact B2125835
  · exact B2125839
  · exact B2125843
  · exact B2125847
  · exact B2125851
  · exact B2125855
  · exact B2125859
  · exact B2125863
  · exact B2125867
  · exact B2125871
  · exact B2125875
  · exact B2125879
  · exact B2125883
  · exact B2125887
  · exact B2125891
  · exact B2125895
  · exact B2125899
  · exact B2125903
  · exact B2125907
  · exact B2125911
  · exact B2125915
  · exact B2125919
  · exact B2125923
  · exact B2125927
  · exact B2125931
  · exact B2125935
  · exact B2125939
  · exact B2125943
  · exact B2125947
  · exact B2125951
  · exact B2125955
  · exact B2125959
  · exact B2125963
  · exact B2125967
  · exact B2125971
  · exact B2125975
  · exact B2125979
  · exact B2125983
  · exact B2125987
  · exact B2125991
  · exact B2125995
  · exact B2125999
  · exact B2126003
  · exact B2126007
  · exact B2126011
  · exact B2126015
  · exact B2126019
  · exact B2126023
  · exact B2126027
  · exact B2126031
  · exact B2126035
  · exact B2126039
  · exact B2126043
  · exact B2126047
  · exact B2126051
  · exact B2126055
  · exact B2126059
  · exact B2126063
  · exact B2126067
  · exact B2126071
  · exact B2126075
  · exact B2126079
  · exact B2126083
  · exact B2126087
  · exact B2126091
  · exact B2126095
  · exact B2126099
  · exact B2126103
  · exact B2126107
  · exact B2126111
  · exact B2126115
  · exact B2126119
  · exact B2126123
  · exact B2126127
  · exact B2126131
  · exact B2126135
  · exact B2126139
  · exact B2126143
  · exact B2126147
  · exact B2126151
  · exact B2126155
  · exact B2126159
  · exact B2126163
  · exact B2126167
  · exact B2126171
  · exact B2126175
  · exact B2126179
  · exact B2126183
  · exact B2126187
  · exact B2126191
  · exact B2126195
  · exact B2126199
  · exact B2126203
  · exact B2126207
  · exact B2126211
  · exact B2126215
  · exact B2126219
  · exact B2126223
  · exact B2126227
  · exact B2126231
  · exact B2126235
  · exact B2126239
  · exact B2126243
  · exact B2126247
  · exact B2126251
  · exact B2126255
  · exact B2126259
  · exact B2126263
  · exact B2126267
  · exact B2126271
  · exact B2126275
  · exact B2126279
  · exact B2126283
  · exact B2126287
  · exact B2126291
  · exact B2126295
  · exact B2126299
  · exact B2126303
  · exact B2126307
  · exact B2126311
  · exact B2126315
  · exact B2126319
  · exact B2126323
  · exact B2126327
  · exact B2126331
  · exact B2126335
  · exact B2126339
  · exact B2126343
  · exact B2126347
  · exact B2126351
  · exact B2126355
  · exact B2126359
  · exact B2126363
  · exact B2126367
  · exact B2126371
  · exact B2126375
  · exact B2126379
  · exact B2126383
  · exact B2126387
  · exact B2126391
  · exact B2126395
  · exact B2126399
  · exact B2126403
  · exact B2126407
  · exact B2126411
  · exact B2126415
  · exact B2126419
  · exact B2126423
  · exact B2126427
  · exact B2126431
  · exact B2126435
  · exact B2126439
  · exact B2126443
  · exact B2126447
  · exact B2126451
  · exact B2126455
  · exact B2126459
  · exact B2126463
  · exact B2126467
  · exact B2126471
  · exact B2126475
  · exact B2126479
  · exact B2126483
  · exact B2126487
  · exact B2126491
  · exact B2126495
  · exact B2126499
  · exact B2126503
  · exact B2126507
  · exact B2126511
  · exact B2126515
  · exact B2126519
  · exact B2126523
  · exact B2126527
  · exact B2126531
  · exact B2126535
  · exact B2126539
  · exact B2126543
  · exact B2126547
  · exact B2126551
  · exact B2126555
  · exact B2126559
  · exact B2126563
  · exact B2126567
  · exact B2126571
  · exact B2126575
  · exact B2126579
  · exact B2126583
  · exact B2126587
  · exact B2126591
  · exact B2126595
  · exact B2126599
  · exact B2126603
  · exact B2126607
  · exact B2126611
  · exact B2126615
  · exact B2126619
  · exact B2126623
  · exact B2126627
  · exact B2126631
  · exact B2126635
  · exact B2126639
  · exact B2126643
  · exact B2126647
  · exact B2126651
  · exact B2126655
  · exact B2126659
  · exact B2126663
  · exact B2126667
  · exact B2126671
  · exact B2126675
  · exact B2126679
  · exact B2126683
  · exact B2126687
  · exact B2126691
  · exact B2126695
  · exact B2126699
  · exact B2126703
  · exact B2126707
  · exact B2126711
  · exact B2126715
  · exact B2126719
  · exact B2126723
  · exact B2126727
  · exact B2126731
  · exact B2126735
  · exact B2126739
  · exact B2126743
  · exact B2126747
  · exact B2126751
  · exact B2126755
  · exact B2126759
  · exact B2126763
  · exact B2126767
  · exact B2126771
  · exact B2126775
  · exact B2126779
  · exact B2126783
  · exact B2126787
  · exact B2126791
  · exact B2126795
  · exact B2126799
  · exact B2126803
  · exact B2126807
  · exact B2126811
  · exact B2126815
  · exact B2126819
  · exact B2126823
  · exact B2126827
  · exact B2126831
  · exact B2126835
  · exact B2126839
  · exact B2126843
  · exact B2126847
  · exact B2126851
  · exact B2126855
  · exact B2126859
  · exact B2126863
  · exact B2126867
  · exact B2126871
  · exact B2126875
  · exact B2126879
  · exact B2126883
  · exact B2126887
  · exact B2126891
  · exact B2126895
  · exact B2126899
  · exact B2126903
  · exact B2126907
  · exact B2126911
  · exact B2126915
  · exact B2126919
  · exact B2126923
  · exact B2126927
  · exact B2126931
  · exact B2126935
  · exact B2126939
  · exact B2126943
  · exact B2126947
  · exact B2126951
  · exact B2126955
  · exact B2126959
  · exact B2126963
  · exact B2126967
  · exact B2126971
  · exact B2126975
  · exact B2126979
  · exact B2126983
  · exact B2126987
  · exact B2126991
  · exact B2126995
  · exact B2126999
  · exact B2127003
  · exact B2127007
  · exact B2127011
  · exact B2127015
  · exact B2127019
  · exact B2127023
  · exact B2127027
  · exact B2127031
  · exact B2127035
  · exact B2127039
  · exact B2127043
  · exact B2127047
  · exact B2127051
  · exact B2127055
  · exact B2127059
  · exact B2127063
  · exact B2127067
  · exact B2127071
  · exact B2127075
  · exact B2127079
  · exact B2127083
  · exact B2127087
  · exact B2127091
  · exact B2127095
  · exact B2127099
  · exact B2127103
  · exact B2127107
  · exact B2127111
  · exact B2127115
  · exact B2127119
  · exact B2127123
  · exact B2127127
  · exact B2127131
  · exact B2127135
  · exact B2127139
  · exact B2127143
  · exact B2127147
  · exact B2127151
  · exact B2127155
  · exact B2127159
  · exact B2127163
  · exact B2127167
  · exact B2127171
  · exact B2127175
  · exact B2127179
  · exact B2127183
  · exact B2127187
  · exact B2127191
  · exact B2127195
  · exact B2127199
  · exact B2127203
  · exact B2127207
  · exact B2127211
  · exact B2127215
  · exact B2127219
  · exact B2127223
  · exact B2127227
  · exact B2127231
  · exact B2127235
  · exact B2127239
  · exact B2127243
  · exact B2127247
  · exact B2127251
  · exact B2127255
  · exact B2127259
  · exact B2127263
  · exact B2127267
  · exact B2127271
  · exact B2127275
  · exact B2127279
  · exact B2127283
  · exact B2127287
  · exact B2127291
  · exact B2127295
  · exact B2127299
  · exact B2127303
  · exact B2127307
  · exact B2127311
  · exact B2127315
  · exact B2127319
  · exact B2127323
  · exact B2127327
  · exact B2127331
  · exact B2127335
  · exact B2127339
  · exact B2127343
  · exact B2127347
  · exact B2127351
  · exact B2127355
  · exact B2127359
  · exact B2127363
  · exact B2127367
  · exact B2127371
  · exact B2127375
  · exact B2127379
  · exact B2127383
  · exact B2127387
  · exact B2127391
  · exact B2127395
  · exact B2127399
  · exact B2127403
  · exact B2127407
  · exact B2127411
  · exact B2127415
  · exact B2127419
  · exact B2127423
  · exact B2127427
  · exact B2127431
  · exact B2127435
theorem solution (m : ℕ) (hlo : 2125435 ≤ m) (hhi : m ≤ 2127435) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 531358 ≤ j := by omega
    have hj2 : j ≤ 531858 := by omega
    have hb : Blo 2125435 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
