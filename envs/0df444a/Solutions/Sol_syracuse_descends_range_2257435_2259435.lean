-- Prove2me | solution 1 for syracuse_descends_range_2257435_2259435
-- status  : ACCEPTED   (prove)
-- author  : @chstdu
-- created : 2026-09-23T17:49:14.309344+00:00
-- url     : https://prove2.me/submissions/0ba8c575-5ca4-4126-913c-e9c3cffdf7a6

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

theorem B6864709 : Blo 2257435 6864709 := bbase (se 4 (by rfl) ⟨643566, by rfl⟩ : syracuseStep 6864709 = 1287133) (by norm_num)
theorem B9152945 : Blo 2257435 9152945 := bstep (se 2 (by rfl) ⟨3432354, by rfl⟩ : syracuseStep 9152945 = 6864709) B6864709
theorem B6101963 : Blo 2257435 6101963 := bstep (se 1 (by rfl) ⟨4576472, by rfl⟩ : syracuseStep 6101963 = 9152945) B9152945
theorem B4067975 : Blo 2257435 4067975 := bstep (se 1 (by rfl) ⟨3050981, by rfl⟩ : syracuseStep 4067975 = 6101963) B6101963
theorem B2711983 : Blo 2257435 2711983 := bstep (se 1 (by rfl) ⟨2033987, by rfl⟩ : syracuseStep 2711983 = 4067975) B4067975
theorem B3615977 : Blo 2257435 3615977 := bstep (se 2 (by rfl) ⟨1355991, by rfl⟩ : syracuseStep 3615977 = 2711983) B2711983
theorem B2410651 : Blo 2257435 2410651 := bstep (se 1 (by rfl) ⟨1807988, by rfl⟩ : syracuseStep 2410651 = 3615977) B3615977
theorem B12856805 : Blo 2257435 12856805 := bstep (se 4 (by rfl) ⟨1205325, by rfl⟩ : syracuseStep 12856805 = 2410651) B2410651
theorem B8571203 : Blo 2257435 8571203 := bstep (se 1 (by rfl) ⟨6428402, by rfl⟩ : syracuseStep 8571203 = 12856805) B12856805
theorem B5714135 : Blo 2257435 5714135 := bstep (se 1 (by rfl) ⟨4285601, by rfl⟩ : syracuseStep 5714135 = 8571203) B8571203
theorem B3809423 : Blo 2257435 3809423 := bstep (se 1 (by rfl) ⟨2857067, by rfl⟩ : syracuseStep 3809423 = 5714135) B5714135
theorem B2539615 : Blo 2257435 2539615 := bstep (se 1 (by rfl) ⟨1904711, by rfl⟩ : syracuseStep 2539615 = 3809423) B3809423
theorem B3386153 : Blo 2257435 3386153 := bstep (se 2 (by rfl) ⟨1269807, by rfl⟩ : syracuseStep 3386153 = 2539615) B2539615
theorem B2257435 : Blo 2257435 2257435 := bstep (se 1 (by rfl) ⟨1693076, by rfl⟩ : syracuseStep 2257435 = 3386153) B3386153
theorem B2644993 : Blo 2257435 2644993 := bbase (se 2 (by rfl) ⟨991872, by rfl⟩ : syracuseStep 2644993 = 1983745) (by norm_num)
theorem B14106629 : Blo 2257435 14106629 := bstep (se 4 (by rfl) ⟨1322496, by rfl⟩ : syracuseStep 14106629 = 2644993) B2644993
theorem B9404419 : Blo 2257435 9404419 := bstep (se 1 (by rfl) ⟨7053314, by rfl⟩ : syracuseStep 9404419 = 14106629) B14106629
theorem B12539225 : Blo 2257435 12539225 := bstep (se 2 (by rfl) ⟨4702209, by rfl⟩ : syracuseStep 12539225 = 9404419) B9404419
theorem B33437933 : Blo 2257435 33437933 := bstep (se 3 (by rfl) ⟨6269612, by rfl⟩ : syracuseStep 33437933 = 12539225) B12539225
theorem B22291955 : Blo 2257435 22291955 := bstep (se 1 (by rfl) ⟨16718966, by rfl⟩ : syracuseStep 22291955 = 33437933) B33437933
theorem B14861303 : Blo 2257435 14861303 := bstep (se 1 (by rfl) ⟨11145977, by rfl⟩ : syracuseStep 14861303 = 22291955) B22291955
theorem B9907535 : Blo 2257435 9907535 := bstep (se 1 (by rfl) ⟨7430651, by rfl⟩ : syracuseStep 9907535 = 14861303) B14861303
theorem B26420093 : Blo 2257435 26420093 := bstep (se 3 (by rfl) ⟨4953767, by rfl⟩ : syracuseStep 26420093 = 9907535) B9907535
theorem B17613395 : Blo 2257435 17613395 := bstep (se 1 (by rfl) ⟨13210046, by rfl⟩ : syracuseStep 17613395 = 26420093) B26420093
theorem B11742263 : Blo 2257435 11742263 := bstep (se 1 (by rfl) ⟨8806697, by rfl⟩ : syracuseStep 11742263 = 17613395) B17613395
theorem B7828175 : Blo 2257435 7828175 := bstep (se 1 (by rfl) ⟨5871131, by rfl⟩ : syracuseStep 7828175 = 11742263) B11742263
theorem B20875133 : Blo 2257435 20875133 := bstep (se 3 (by rfl) ⟨3914087, by rfl⟩ : syracuseStep 20875133 = 7828175) B7828175
theorem B13916755 : Blo 2257435 13916755 := bstep (se 1 (by rfl) ⟨10437566, by rfl⟩ : syracuseStep 13916755 = 20875133) B20875133
theorem B18555673 : Blo 2257435 18555673 := bstep (se 2 (by rfl) ⟨6958377, by rfl⟩ : syracuseStep 18555673 = 13916755) B13916755
theorem B24740897 : Blo 2257435 24740897 := bstep (se 2 (by rfl) ⟨9277836, by rfl⟩ : syracuseStep 24740897 = 18555673) B18555673
theorem B65975725 : Blo 2257435 65975725 := bstep (se 3 (by rfl) ⟨12370448, by rfl⟩ : syracuseStep 65975725 = 24740897) B24740897
theorem B87967633 : Blo 2257435 87967633 := bstep (se 2 (by rfl) ⟨32987862, by rfl⟩ : syracuseStep 87967633 = 65975725) B65975725
theorem B117290177 : Blo 2257435 117290177 := bstep (se 2 (by rfl) ⟨43983816, by rfl⟩ : syracuseStep 117290177 = 87967633) B87967633
theorem B78193451 : Blo 2257435 78193451 := bstep (se 1 (by rfl) ⟨58645088, by rfl⟩ : syracuseStep 78193451 = 117290177) B117290177
theorem B52128967 : Blo 2257435 52128967 := bstep (se 1 (by rfl) ⟨39096725, by rfl⟩ : syracuseStep 52128967 = 78193451) B78193451
theorem B69505289 : Blo 2257435 69505289 := bstep (se 2 (by rfl) ⟨26064483, by rfl⟩ : syracuseStep 69505289 = 52128967) B52128967
theorem B46336859 : Blo 2257435 46336859 := bstep (se 1 (by rfl) ⟨34752644, by rfl⟩ : syracuseStep 46336859 = 69505289) B69505289
theorem B30891239 : Blo 2257435 30891239 := bstep (se 1 (by rfl) ⟨23168429, by rfl⟩ : syracuseStep 30891239 = 46336859) B46336859
theorem B20594159 : Blo 2257435 20594159 := bstep (se 1 (by rfl) ⟨15445619, by rfl⟩ : syracuseStep 20594159 = 30891239) B30891239
theorem B13729439 : Blo 2257435 13729439 := bstep (se 1 (by rfl) ⟨10297079, by rfl⟩ : syracuseStep 13729439 = 20594159) B20594159
theorem B9152959 : Blo 2257435 9152959 := bstep (se 1 (by rfl) ⟨6864719, by rfl⟩ : syracuseStep 9152959 = 13729439) B13729439
theorem B12203945 : Blo 2257435 12203945 := bstep (se 2 (by rfl) ⟨4576479, by rfl⟩ : syracuseStep 12203945 = 9152959) B9152959
theorem B8135963 : Blo 2257435 8135963 := bstep (se 1 (by rfl) ⟨6101972, by rfl⟩ : syracuseStep 8135963 = 12203945) B12203945
theorem B5423975 : Blo 2257435 5423975 := bstep (se 1 (by rfl) ⟨4067981, by rfl⟩ : syracuseStep 5423975 = 8135963) B8135963
theorem B3615983 : Blo 2257435 3615983 := bstep (se 1 (by rfl) ⟨2711987, by rfl⟩ : syracuseStep 3615983 = 5423975) B5423975
theorem B2410655 : Blo 2257435 2410655 := bstep (se 1 (by rfl) ⟨1807991, by rfl⟩ : syracuseStep 2410655 = 3615983) B3615983
theorem B6428413 : Blo 2257435 6428413 := bstep (se 3 (by rfl) ⟨1205327, by rfl⟩ : syracuseStep 6428413 = 2410655) B2410655
theorem B8571217 : Blo 2257435 8571217 := bstep (se 2 (by rfl) ⟨3214206, by rfl⟩ : syracuseStep 8571217 = 6428413) B6428413
theorem B11428289 : Blo 2257435 11428289 := bstep (se 2 (by rfl) ⟨4285608, by rfl⟩ : syracuseStep 11428289 = 8571217) B8571217
theorem B7618859 : Blo 2257435 7618859 := bstep (se 1 (by rfl) ⟨5714144, by rfl⟩ : syracuseStep 7618859 = 11428289) B11428289
theorem B5079239 : Blo 2257435 5079239 := bstep (se 1 (by rfl) ⟨3809429, by rfl⟩ : syracuseStep 5079239 = 7618859) B7618859
theorem B3386159 : Blo 2257435 3386159 := bstep (se 1 (by rfl) ⟨2539619, by rfl⟩ : syracuseStep 3386159 = 5079239) B5079239
theorem B2257439 : Blo 2257435 2257439 := bstep (se 1 (by rfl) ⟨1693079, by rfl⟩ : syracuseStep 2257439 = 3386159) B3386159
theorem B3386165 : Blo 2257435 3386165 := bbase (se 5 (by rfl) ⟨158726, by rfl⟩ : syracuseStep 3386165 = 317453) (by norm_num)
theorem B2257443 : Blo 2257435 2257443 := bstep (se 1 (by rfl) ⟨1693082, by rfl⟩ : syracuseStep 2257443 = 3386165) B3386165
theorem B5714165 : Blo 2257435 5714165 := bbase (se 5 (by rfl) ⟨267851, by rfl⟩ : syracuseStep 5714165 = 535703) (by norm_num)
theorem B3809443 : Blo 2257435 3809443 := bstep (se 1 (by rfl) ⟨2857082, by rfl⟩ : syracuseStep 3809443 = 5714165) B5714165
theorem B5079257 : Blo 2257435 5079257 := bstep (se 2 (by rfl) ⟨1904721, by rfl⟩ : syracuseStep 5079257 = 3809443) B3809443
theorem B3386171 : Blo 2257435 3386171 := bstep (se 1 (by rfl) ⟨2539628, by rfl⟩ : syracuseStep 3386171 = 5079257) B5079257
theorem B2257447 : Blo 2257435 2257447 := bstep (se 1 (by rfl) ⟨1693085, by rfl⟩ : syracuseStep 2257447 = 3386171) B3386171
theorem B2539633 : Blo 2257435 2539633 := bbase (se 2 (by rfl) ⟨952362, by rfl⟩ : syracuseStep 2539633 = 1904725) (by norm_num)
theorem B3386177 : Blo 2257435 3386177 := bstep (se 2 (by rfl) ⟨1269816, by rfl⟩ : syracuseStep 3386177 = 2539633) B2539633
theorem B2257451 : Blo 2257435 2257451 := bstep (se 1 (by rfl) ⟨1693088, by rfl⟩ : syracuseStep 2257451 = 3386177) B3386177
theorem B5424013 : Blo 2257435 5424013 := bbase (se 3 (by rfl) ⟨1017002, by rfl⟩ : syracuseStep 5424013 = 2034005) (by norm_num)
theorem B7232017 : Blo 2257435 7232017 := bstep (se 2 (by rfl) ⟨2712006, by rfl⟩ : syracuseStep 7232017 = 5424013) B5424013
theorem B9642689 : Blo 2257435 9642689 := bstep (se 2 (by rfl) ⟨3616008, by rfl⟩ : syracuseStep 9642689 = 7232017) B7232017
theorem B6428459 : Blo 2257435 6428459 := bstep (se 1 (by rfl) ⟨4821344, by rfl⟩ : syracuseStep 6428459 = 9642689) B9642689
theorem B4285639 : Blo 2257435 4285639 := bstep (se 1 (by rfl) ⟨3214229, by rfl⟩ : syracuseStep 4285639 = 6428459) B6428459
theorem B5714185 : Blo 2257435 5714185 := bstep (se 2 (by rfl) ⟨2142819, by rfl⟩ : syracuseStep 5714185 = 4285639) B4285639
theorem B7618913 : Blo 2257435 7618913 := bstep (se 2 (by rfl) ⟨2857092, by rfl⟩ : syracuseStep 7618913 = 5714185) B5714185
theorem B5079275 : Blo 2257435 5079275 := bstep (se 1 (by rfl) ⟨3809456, by rfl⟩ : syracuseStep 5079275 = 7618913) B7618913
theorem B3386183 : Blo 2257435 3386183 := bstep (se 1 (by rfl) ⟨2539637, by rfl⟩ : syracuseStep 3386183 = 5079275) B5079275
theorem B2257455 : Blo 2257435 2257455 := bstep (se 1 (by rfl) ⟨1693091, by rfl⟩ : syracuseStep 2257455 = 3386183) B3386183
theorem B3386189 : Blo 2257435 3386189 := bbase (se 3 (by rfl) ⟨634910, by rfl⟩ : syracuseStep 3386189 = 1269821) (by norm_num)
theorem B2257459 : Blo 2257435 2257459 := bstep (se 1 (by rfl) ⟨1693094, by rfl⟩ : syracuseStep 2257459 = 3386189) B3386189
theorem B5079293 : Blo 2257435 5079293 := bbase (se 3 (by rfl) ⟨952367, by rfl⟩ : syracuseStep 5079293 = 1904735) (by norm_num)
theorem B3386195 : Blo 2257435 3386195 := bstep (se 1 (by rfl) ⟨2539646, by rfl⟩ : syracuseStep 3386195 = 5079293) B5079293
theorem B2257463 : Blo 2257435 2257463 := bstep (se 1 (by rfl) ⟨1693097, by rfl⟩ : syracuseStep 2257463 = 3386195) B3386195
theorem B3809477 : Blo 2257435 3809477 := bbase (se 4 (by rfl) ⟨357138, by rfl⟩ : syracuseStep 3809477 = 714277) (by norm_num)
theorem B2539651 : Blo 2257435 2539651 := bstep (se 1 (by rfl) ⟨1904738, by rfl⟩ : syracuseStep 2539651 = 3809477) B3809477
theorem B3386201 : Blo 2257435 3386201 := bstep (se 2 (by rfl) ⟨1269825, by rfl⟩ : syracuseStep 3386201 = 2539651) B2539651
theorem B2257467 : Blo 2257435 2257467 := bstep (se 1 (by rfl) ⟨1693100, by rfl⟩ : syracuseStep 2257467 = 3386201) B3386201
theorem B17142677 : Blo 2257435 17142677 := bbase (se 6 (by rfl) ⟨401781, by rfl⟩ : syracuseStep 17142677 = 803563) (by norm_num)
theorem B11428451 : Blo 2257435 11428451 := bstep (se 1 (by rfl) ⟨8571338, by rfl⟩ : syracuseStep 11428451 = 17142677) B17142677
theorem B7618967 : Blo 2257435 7618967 := bstep (se 1 (by rfl) ⟨5714225, by rfl⟩ : syracuseStep 7618967 = 11428451) B11428451
theorem B5079311 : Blo 2257435 5079311 := bstep (se 1 (by rfl) ⟨3809483, by rfl⟩ : syracuseStep 5079311 = 7618967) B7618967
theorem B3386207 : Blo 2257435 3386207 := bstep (se 1 (by rfl) ⟨2539655, by rfl⟩ : syracuseStep 3386207 = 5079311) B5079311
theorem B2257471 : Blo 2257435 2257471 := bstep (se 1 (by rfl) ⟨1693103, by rfl⟩ : syracuseStep 2257471 = 3386207) B3386207
theorem B3386213 : Blo 2257435 3386213 := bbase (se 4 (by rfl) ⟨317457, by rfl⟩ : syracuseStep 3386213 = 634915) (by norm_num)
theorem B2257475 : Blo 2257435 2257475 := bstep (se 1 (by rfl) ⟨1693106, by rfl⟩ : syracuseStep 2257475 = 3386213) B3386213
theorem B4285685 : Blo 2257435 4285685 := bbase (se 5 (by rfl) ⟨200891, by rfl⟩ : syracuseStep 4285685 = 401783) (by norm_num)
theorem B2857123 : Blo 2257435 2857123 := bstep (se 1 (by rfl) ⟨2142842, by rfl⟩ : syracuseStep 2857123 = 4285685) B4285685
theorem B3809497 : Blo 2257435 3809497 := bstep (se 2 (by rfl) ⟨1428561, by rfl⟩ : syracuseStep 3809497 = 2857123) B2857123
theorem B5079329 : Blo 2257435 5079329 := bstep (se 2 (by rfl) ⟨1904748, by rfl⟩ : syracuseStep 5079329 = 3809497) B3809497
theorem B3386219 : Blo 2257435 3386219 := bstep (se 1 (by rfl) ⟨2539664, by rfl⟩ : syracuseStep 3386219 = 5079329) B5079329
theorem B2257479 : Blo 2257435 2257479 := bstep (se 1 (by rfl) ⟨1693109, by rfl⟩ : syracuseStep 2257479 = 3386219) B3386219
theorem B2539669 : Blo 2257435 2539669 := bbase (se 6 (by rfl) ⟨59523, by rfl⟩ : syracuseStep 2539669 = 119047) (by norm_num)
theorem B3386225 : Blo 2257435 3386225 := bstep (se 2 (by rfl) ⟨1269834, by rfl⟩ : syracuseStep 3386225 = 2539669) B2539669
theorem B2257483 : Blo 2257435 2257483 := bstep (se 1 (by rfl) ⟨1693112, by rfl⟩ : syracuseStep 2257483 = 3386225) B3386225
theorem B2857133 : Blo 2257435 2857133 := bbase (se 3 (by rfl) ⟨535712, by rfl⟩ : syracuseStep 2857133 = 1071425) (by norm_num)
theorem B7619021 : Blo 2257435 7619021 := bstep (se 3 (by rfl) ⟨1428566, by rfl⟩ : syracuseStep 7619021 = 2857133) B2857133
theorem B5079347 : Blo 2257435 5079347 := bstep (se 1 (by rfl) ⟨3809510, by rfl⟩ : syracuseStep 5079347 = 7619021) B7619021
theorem B3386231 : Blo 2257435 3386231 := bstep (se 1 (by rfl) ⟨2539673, by rfl⟩ : syracuseStep 3386231 = 5079347) B5079347
theorem B2257487 : Blo 2257435 2257487 := bstep (se 1 (by rfl) ⟨1693115, by rfl⟩ : syracuseStep 2257487 = 3386231) B3386231
theorem B3386237 : Blo 2257435 3386237 := bbase (se 3 (by rfl) ⟨634919, by rfl⟩ : syracuseStep 3386237 = 1269839) (by norm_num)
theorem B2257491 : Blo 2257435 2257491 := bstep (se 1 (by rfl) ⟨1693118, by rfl⟩ : syracuseStep 2257491 = 3386237) B3386237
theorem B5079365 : Blo 2257435 5079365 := bbase (se 4 (by rfl) ⟨476190, by rfl⟩ : syracuseStep 5079365 = 952381) (by norm_num)
theorem B3386243 : Blo 2257435 3386243 := bstep (se 1 (by rfl) ⟨2539682, by rfl⟩ : syracuseStep 3386243 = 5079365) B5079365
theorem B2257495 : Blo 2257435 2257495 := bstep (se 1 (by rfl) ⟨1693121, by rfl⟩ : syracuseStep 2257495 = 3386243) B3386243
theorem B5792261 : Blo 2257435 5792261 := bbase (se 4 (by rfl) ⟨543024, by rfl⟩ : syracuseStep 5792261 = 1086049) (by norm_num)
theorem B61784117 : Blo 2257435 61784117 := bstep (se 5 (by rfl) ⟨2896130, by rfl⟩ : syracuseStep 61784117 = 5792261) B5792261
theorem B41189411 : Blo 2257435 41189411 := bstep (se 1 (by rfl) ⟨30892058, by rfl⟩ : syracuseStep 41189411 = 61784117) B61784117
theorem B27459607 : Blo 2257435 27459607 := bstep (se 1 (by rfl) ⟨20594705, by rfl⟩ : syracuseStep 27459607 = 41189411) B41189411
theorem B36612809 : Blo 2257435 36612809 := bstep (se 2 (by rfl) ⟨13729803, by rfl⟩ : syracuseStep 36612809 = 27459607) B27459607
theorem B24408539 : Blo 2257435 24408539 := bstep (se 1 (by rfl) ⟨18306404, by rfl⟩ : syracuseStep 24408539 = 36612809) B36612809
theorem B16272359 : Blo 2257435 16272359 := bstep (se 1 (by rfl) ⟨12204269, by rfl⟩ : syracuseStep 16272359 = 24408539) B24408539
theorem B10848239 : Blo 2257435 10848239 := bstep (se 1 (by rfl) ⟨8136179, by rfl⟩ : syracuseStep 10848239 = 16272359) B16272359
theorem B7232159 : Blo 2257435 7232159 := bstep (se 1 (by rfl) ⟨5424119, by rfl⟩ : syracuseStep 7232159 = 10848239) B10848239
theorem B4821439 : Blo 2257435 4821439 := bstep (se 1 (by rfl) ⟨3616079, by rfl⟩ : syracuseStep 4821439 = 7232159) B7232159
theorem B6428585 : Blo 2257435 6428585 := bstep (se 2 (by rfl) ⟨2410719, by rfl⟩ : syracuseStep 6428585 = 4821439) B4821439
theorem B4285723 : Blo 2257435 4285723 := bstep (se 1 (by rfl) ⟨3214292, by rfl⟩ : syracuseStep 4285723 = 6428585) B6428585
theorem B5714297 : Blo 2257435 5714297 := bstep (se 2 (by rfl) ⟨2142861, by rfl⟩ : syracuseStep 5714297 = 4285723) B4285723
theorem B3809531 : Blo 2257435 3809531 := bstep (se 1 (by rfl) ⟨2857148, by rfl⟩ : syracuseStep 3809531 = 5714297) B5714297
theorem B2539687 : Blo 2257435 2539687 := bstep (se 1 (by rfl) ⟨1904765, by rfl⟩ : syracuseStep 2539687 = 3809531) B3809531
theorem B3386249 : Blo 2257435 3386249 := bstep (se 2 (by rfl) ⟨1269843, by rfl⟩ : syracuseStep 3386249 = 2539687) B2539687
theorem B2257499 : Blo 2257435 2257499 := bstep (se 1 (by rfl) ⟨1693124, by rfl⟩ : syracuseStep 2257499 = 3386249) B3386249
theorem B11428613 : Blo 2257435 11428613 := bbase (se 4 (by rfl) ⟨1071432, by rfl⟩ : syracuseStep 11428613 = 2142865) (by norm_num)
theorem B7619075 : Blo 2257435 7619075 := bstep (se 1 (by rfl) ⟨5714306, by rfl⟩ : syracuseStep 7619075 = 11428613) B11428613
theorem B5079383 : Blo 2257435 5079383 := bstep (se 1 (by rfl) ⟨3809537, by rfl⟩ : syracuseStep 5079383 = 7619075) B7619075
theorem B3386255 : Blo 2257435 3386255 := bstep (se 1 (by rfl) ⟨2539691, by rfl⟩ : syracuseStep 3386255 = 5079383) B5079383
theorem B2257503 : Blo 2257435 2257503 := bstep (se 1 (by rfl) ⟨1693127, by rfl⟩ : syracuseStep 2257503 = 3386255) B3386255
theorem B3386261 : Blo 2257435 3386261 := bbase (se 6 (by rfl) ⟨79365, by rfl⟩ : syracuseStep 3386261 = 158731) (by norm_num)
theorem B2257507 : Blo 2257435 2257507 := bstep (se 1 (by rfl) ⟨1693130, by rfl⟩ : syracuseStep 2257507 = 3386261) B3386261
theorem B12857237 : Blo 2257435 12857237 := bbase (se 6 (by rfl) ⟨301341, by rfl⟩ : syracuseStep 12857237 = 602683) (by norm_num)
theorem B8571491 : Blo 2257435 8571491 := bstep (se 1 (by rfl) ⟨6428618, by rfl⟩ : syracuseStep 8571491 = 12857237) B12857237
theorem B5714327 : Blo 2257435 5714327 := bstep (se 1 (by rfl) ⟨4285745, by rfl⟩ : syracuseStep 5714327 = 8571491) B8571491
theorem B3809551 : Blo 2257435 3809551 := bstep (se 1 (by rfl) ⟨2857163, by rfl⟩ : syracuseStep 3809551 = 5714327) B5714327
theorem B5079401 : Blo 2257435 5079401 := bstep (se 2 (by rfl) ⟨1904775, by rfl⟩ : syracuseStep 5079401 = 3809551) B3809551
theorem B3386267 : Blo 2257435 3386267 := bstep (se 1 (by rfl) ⟨2539700, by rfl⟩ : syracuseStep 3386267 = 5079401) B5079401
theorem B2257511 : Blo 2257435 2257511 := bstep (se 1 (by rfl) ⟨1693133, by rfl⟩ : syracuseStep 2257511 = 3386267) B3386267
theorem B2539705 : Blo 2257435 2539705 := bbase (se 2 (by rfl) ⟨952389, by rfl⟩ : syracuseStep 2539705 = 1904779) (by norm_num)
theorem B3386273 : Blo 2257435 3386273 := bstep (se 2 (by rfl) ⟨1269852, by rfl⟩ : syracuseStep 3386273 = 2539705) B2539705
theorem B2257515 : Blo 2257435 2257515 := bstep (se 1 (by rfl) ⟨1693136, by rfl⟩ : syracuseStep 2257515 = 3386273) B3386273
theorem B2574361 : Blo 2257435 2574361 := bbase (se 2 (by rfl) ⟨965385, by rfl⟩ : syracuseStep 2574361 = 1930771) (by norm_num)
theorem B13729925 : Blo 2257435 13729925 := bstep (se 4 (by rfl) ⟨1287180, by rfl⟩ : syracuseStep 13729925 = 2574361) B2574361
theorem B9153283 : Blo 2257435 9153283 := bstep (se 1 (by rfl) ⟨6864962, by rfl⟩ : syracuseStep 9153283 = 13729925) B13729925
theorem B12204377 : Blo 2257435 12204377 := bstep (se 2 (by rfl) ⟨4576641, by rfl⟩ : syracuseStep 12204377 = 9153283) B9153283
theorem B8136251 : Blo 2257435 8136251 := bstep (se 1 (by rfl) ⟨6102188, by rfl⟩ : syracuseStep 8136251 = 12204377) B12204377
theorem B5424167 : Blo 2257435 5424167 := bstep (se 1 (by rfl) ⟨4068125, by rfl⟩ : syracuseStep 5424167 = 8136251) B8136251
theorem B3616111 : Blo 2257435 3616111 := bstep (se 1 (by rfl) ⟨2712083, by rfl⟩ : syracuseStep 3616111 = 5424167) B5424167
theorem B4821481 : Blo 2257435 4821481 := bstep (se 2 (by rfl) ⟨1808055, by rfl⟩ : syracuseStep 4821481 = 3616111) B3616111
theorem B6428641 : Blo 2257435 6428641 := bstep (se 2 (by rfl) ⟨2410740, by rfl⟩ : syracuseStep 6428641 = 4821481) B4821481
theorem B8571521 : Blo 2257435 8571521 := bstep (se 2 (by rfl) ⟨3214320, by rfl⟩ : syracuseStep 8571521 = 6428641) B6428641
theorem B5714347 : Blo 2257435 5714347 := bstep (se 1 (by rfl) ⟨4285760, by rfl⟩ : syracuseStep 5714347 = 8571521) B8571521
theorem B7619129 : Blo 2257435 7619129 := bstep (se 2 (by rfl) ⟨2857173, by rfl⟩ : syracuseStep 7619129 = 5714347) B5714347
theorem B5079419 : Blo 2257435 5079419 := bstep (se 1 (by rfl) ⟨3809564, by rfl⟩ : syracuseStep 5079419 = 7619129) B7619129
theorem B3386279 : Blo 2257435 3386279 := bstep (se 1 (by rfl) ⟨2539709, by rfl⟩ : syracuseStep 3386279 = 5079419) B5079419
theorem B2257519 : Blo 2257435 2257519 := bstep (se 1 (by rfl) ⟨1693139, by rfl⟩ : syracuseStep 2257519 = 3386279) B3386279
theorem B3386285 : Blo 2257435 3386285 := bbase (se 3 (by rfl) ⟨634928, by rfl⟩ : syracuseStep 3386285 = 1269857) (by norm_num)
theorem B2257523 : Blo 2257435 2257523 := bstep (se 1 (by rfl) ⟨1693142, by rfl⟩ : syracuseStep 2257523 = 3386285) B3386285
theorem B5079437 : Blo 2257435 5079437 := bbase (se 3 (by rfl) ⟨952394, by rfl⟩ : syracuseStep 5079437 = 1904789) (by norm_num)
theorem B3386291 : Blo 2257435 3386291 := bstep (se 1 (by rfl) ⟨2539718, by rfl⟩ : syracuseStep 3386291 = 5079437) B5079437
theorem B2257527 : Blo 2257435 2257527 := bstep (se 1 (by rfl) ⟨1693145, by rfl⟩ : syracuseStep 2257527 = 3386291) B3386291
theorem B2857189 : Blo 2257435 2857189 := bbase (se 4 (by rfl) ⟨267861, by rfl⟩ : syracuseStep 2857189 = 535723) (by norm_num)
theorem B3809585 : Blo 2257435 3809585 := bstep (se 2 (by rfl) ⟨1428594, by rfl⟩ : syracuseStep 3809585 = 2857189) B2857189
theorem B2539723 : Blo 2257435 2539723 := bstep (se 1 (by rfl) ⟨1904792, by rfl⟩ : syracuseStep 2539723 = 3809585) B3809585
theorem B3386297 : Blo 2257435 3386297 := bstep (se 2 (by rfl) ⟨1269861, by rfl⟩ : syracuseStep 3386297 = 2539723) B2539723
theorem B2257531 : Blo 2257435 2257531 := bstep (se 1 (by rfl) ⟨1693148, by rfl⟩ : syracuseStep 2257531 = 3386297) B3386297
theorem B2896177 : Blo 2257435 2896177 := bbase (se 2 (by rfl) ⟨1086066, by rfl⟩ : syracuseStep 2896177 = 2172133) (by norm_num)
theorem B3861569 : Blo 2257435 3861569 := bstep (se 2 (by rfl) ⟨1448088, by rfl⟩ : syracuseStep 3861569 = 2896177) B2896177
theorem B2574379 : Blo 2257435 2574379 := bstep (se 1 (by rfl) ⟨1930784, by rfl⟩ : syracuseStep 2574379 = 3861569) B3861569
theorem B3432505 : Blo 2257435 3432505 := bstep (se 2 (by rfl) ⟨1287189, by rfl⟩ : syracuseStep 3432505 = 2574379) B2574379
theorem B4576673 : Blo 2257435 4576673 := bstep (se 2 (by rfl) ⟨1716252, by rfl⟩ : syracuseStep 4576673 = 3432505) B3432505
theorem B3051115 : Blo 2257435 3051115 := bstep (se 1 (by rfl) ⟨2288336, by rfl⟩ : syracuseStep 3051115 = 4576673) B4576673
theorem B16272613 : Blo 2257435 16272613 := bstep (se 4 (by rfl) ⟨1525557, by rfl⟩ : syracuseStep 16272613 = 3051115) B3051115
theorem B21696817 : Blo 2257435 21696817 := bstep (se 2 (by rfl) ⟨8136306, by rfl⟩ : syracuseStep 21696817 = 16272613) B16272613
theorem B28929089 : Blo 2257435 28929089 := bstep (se 2 (by rfl) ⟨10848408, by rfl⟩ : syracuseStep 28929089 = 21696817) B21696817
theorem B19286059 : Blo 2257435 19286059 := bstep (se 1 (by rfl) ⟨14464544, by rfl⟩ : syracuseStep 19286059 = 28929089) B28929089
theorem B25714745 : Blo 2257435 25714745 := bstep (se 2 (by rfl) ⟨9643029, by rfl⟩ : syracuseStep 25714745 = 19286059) B19286059
theorem B17143163 : Blo 2257435 17143163 := bstep (se 1 (by rfl) ⟨12857372, by rfl⟩ : syracuseStep 17143163 = 25714745) B25714745
theorem B11428775 : Blo 2257435 11428775 := bstep (se 1 (by rfl) ⟨8571581, by rfl⟩ : syracuseStep 11428775 = 17143163) B17143163
theorem B7619183 : Blo 2257435 7619183 := bstep (se 1 (by rfl) ⟨5714387, by rfl⟩ : syracuseStep 7619183 = 11428775) B11428775
theorem B5079455 : Blo 2257435 5079455 := bstep (se 1 (by rfl) ⟨3809591, by rfl⟩ : syracuseStep 5079455 = 7619183) B7619183
theorem B3386303 : Blo 2257435 3386303 := bstep (se 1 (by rfl) ⟨2539727, by rfl⟩ : syracuseStep 3386303 = 5079455) B5079455
theorem B2257535 : Blo 2257435 2257535 := bstep (se 1 (by rfl) ⟨1693151, by rfl⟩ : syracuseStep 2257535 = 3386303) B3386303
theorem B3386309 : Blo 2257435 3386309 := bbase (se 4 (by rfl) ⟨317466, by rfl⟩ : syracuseStep 3386309 = 634933) (by norm_num)
theorem B2257539 : Blo 2257435 2257539 := bstep (se 1 (by rfl) ⟨1693154, by rfl⟩ : syracuseStep 2257539 = 3386309) B3386309
theorem B3809605 : Blo 2257435 3809605 := bbase (se 4 (by rfl) ⟨357150, by rfl⟩ : syracuseStep 3809605 = 714301) (by norm_num)
theorem B5079473 : Blo 2257435 5079473 := bstep (se 2 (by rfl) ⟨1904802, by rfl⟩ : syracuseStep 5079473 = 3809605) B3809605
theorem B3386315 : Blo 2257435 3386315 := bstep (se 1 (by rfl) ⟨2539736, by rfl⟩ : syracuseStep 3386315 = 5079473) B5079473
theorem B2257543 : Blo 2257435 2257543 := bstep (se 1 (by rfl) ⟨1693157, by rfl⟩ : syracuseStep 2257543 = 3386315) B3386315
theorem B2539741 : Blo 2257435 2539741 := bbase (se 3 (by rfl) ⟨476201, by rfl⟩ : syracuseStep 2539741 = 952403) (by norm_num)
theorem B3386321 : Blo 2257435 3386321 := bstep (se 2 (by rfl) ⟨1269870, by rfl⟩ : syracuseStep 3386321 = 2539741) B2539741
theorem B2257547 : Blo 2257435 2257547 := bstep (se 1 (by rfl) ⟨1693160, by rfl⟩ : syracuseStep 2257547 = 3386321) B3386321
theorem B7619237 : Blo 2257435 7619237 := bbase (se 4 (by rfl) ⟨714303, by rfl⟩ : syracuseStep 7619237 = 1428607) (by norm_num)
theorem B5079491 : Blo 2257435 5079491 := bstep (se 1 (by rfl) ⟨3809618, by rfl⟩ : syracuseStep 5079491 = 7619237) B7619237
theorem B3386327 : Blo 2257435 3386327 := bstep (se 1 (by rfl) ⟨2539745, by rfl⟩ : syracuseStep 3386327 = 5079491) B5079491
theorem B2257551 : Blo 2257435 2257551 := bstep (se 1 (by rfl) ⟨1693163, by rfl⟩ : syracuseStep 2257551 = 3386327) B3386327
theorem B3386333 : Blo 2257435 3386333 := bbase (se 3 (by rfl) ⟨634937, by rfl⟩ : syracuseStep 3386333 = 1269875) (by norm_num)
theorem B2257555 : Blo 2257435 2257555 := bstep (se 1 (by rfl) ⟨1693166, by rfl⟩ : syracuseStep 2257555 = 3386333) B3386333
theorem B5079509 : Blo 2257435 5079509 := bbase (se 7 (by rfl) ⟨59525, by rfl⟩ : syracuseStep 5079509 = 119051) (by norm_num)
theorem B3386339 : Blo 2257435 3386339 := bstep (se 1 (by rfl) ⟨2539754, by rfl⟩ : syracuseStep 3386339 = 5079509) B5079509
theorem B2257559 : Blo 2257435 2257559 := bstep (se 1 (by rfl) ⟨1693169, by rfl⟩ : syracuseStep 2257559 = 3386339) B3386339
theorem B9153461 : Blo 2257435 9153461 := bbase (se 5 (by rfl) ⟨429068, by rfl⟩ : syracuseStep 9153461 = 858137) (by norm_num)
theorem B6102307 : Blo 2257435 6102307 := bstep (se 1 (by rfl) ⟨4576730, by rfl⟩ : syracuseStep 6102307 = 9153461) B9153461
theorem B32545637 : Blo 2257435 32545637 := bstep (se 4 (by rfl) ⟨3051153, by rfl⟩ : syracuseStep 32545637 = 6102307) B6102307
theorem B21697091 : Blo 2257435 21697091 := bstep (se 1 (by rfl) ⟨16272818, by rfl⟩ : syracuseStep 21697091 = 32545637) B32545637
theorem B14464727 : Blo 2257435 14464727 := bstep (se 1 (by rfl) ⟨10848545, by rfl⟩ : syracuseStep 14464727 = 21697091) B21697091
theorem B9643151 : Blo 2257435 9643151 := bstep (se 1 (by rfl) ⟨7232363, by rfl⟩ : syracuseStep 9643151 = 14464727) B14464727
theorem B6428767 : Blo 2257435 6428767 := bstep (se 1 (by rfl) ⟨4821575, by rfl⟩ : syracuseStep 6428767 = 9643151) B9643151
theorem B8571689 : Blo 2257435 8571689 := bstep (se 2 (by rfl) ⟨3214383, by rfl⟩ : syracuseStep 8571689 = 6428767) B6428767
theorem B5714459 : Blo 2257435 5714459 := bstep (se 1 (by rfl) ⟨4285844, by rfl⟩ : syracuseStep 5714459 = 8571689) B8571689
theorem B3809639 : Blo 2257435 3809639 := bstep (se 1 (by rfl) ⟨2857229, by rfl⟩ : syracuseStep 3809639 = 5714459) B5714459
theorem B2539759 : Blo 2257435 2539759 := bstep (se 1 (by rfl) ⟨1904819, by rfl⟩ : syracuseStep 2539759 = 3809639) B3809639
theorem B3386345 : Blo 2257435 3386345 := bstep (se 2 (by rfl) ⟨1269879, by rfl⟩ : syracuseStep 3386345 = 2539759) B2539759
theorem B2257563 : Blo 2257435 2257563 := bstep (se 1 (by rfl) ⟨1693172, by rfl⟩ : syracuseStep 2257563 = 3386345) B3386345
theorem B2288369 : Blo 2257435 2288369 := bbase (se 2 (by rfl) ⟨858138, by rfl⟩ : syracuseStep 2288369 = 1716277) (by norm_num)
theorem B6102317 : Blo 2257435 6102317 := bstep (se 3 (by rfl) ⟨1144184, by rfl⟩ : syracuseStep 6102317 = 2288369) B2288369
theorem B16272845 : Blo 2257435 16272845 := bstep (se 3 (by rfl) ⟨3051158, by rfl⟩ : syracuseStep 16272845 = 6102317) B6102317
theorem B10848563 : Blo 2257435 10848563 := bstep (se 1 (by rfl) ⟨8136422, by rfl⟩ : syracuseStep 10848563 = 16272845) B16272845
theorem B7232375 : Blo 2257435 7232375 := bstep (se 1 (by rfl) ⟨5424281, by rfl⟩ : syracuseStep 7232375 = 10848563) B10848563
theorem B19286333 : Blo 2257435 19286333 := bstep (se 3 (by rfl) ⟨3616187, by rfl⟩ : syracuseStep 19286333 = 7232375) B7232375
theorem B12857555 : Blo 2257435 12857555 := bstep (se 1 (by rfl) ⟨9643166, by rfl⟩ : syracuseStep 12857555 = 19286333) B19286333
theorem B8571703 : Blo 2257435 8571703 := bstep (se 1 (by rfl) ⟨6428777, by rfl⟩ : syracuseStep 8571703 = 12857555) B12857555
theorem B11428937 : Blo 2257435 11428937 := bstep (se 2 (by rfl) ⟨4285851, by rfl⟩ : syracuseStep 11428937 = 8571703) B8571703
theorem B7619291 : Blo 2257435 7619291 := bstep (se 1 (by rfl) ⟨5714468, by rfl⟩ : syracuseStep 7619291 = 11428937) B11428937
theorem B5079527 : Blo 2257435 5079527 := bstep (se 1 (by rfl) ⟨3809645, by rfl⟩ : syracuseStep 5079527 = 7619291) B7619291
theorem B3386351 : Blo 2257435 3386351 := bstep (se 1 (by rfl) ⟨2539763, by rfl⟩ : syracuseStep 3386351 = 5079527) B5079527
theorem B2257567 : Blo 2257435 2257567 := bstep (se 1 (by rfl) ⟨1693175, by rfl⟩ : syracuseStep 2257567 = 3386351) B3386351
theorem B3386357 : Blo 2257435 3386357 := bbase (se 5 (by rfl) ⟨158735, by rfl⟩ : syracuseStep 3386357 = 317471) (by norm_num)
theorem B2257571 : Blo 2257435 2257571 := bstep (se 1 (by rfl) ⟨1693178, by rfl⟩ : syracuseStep 2257571 = 3386357) B3386357
theorem B6102341 : Blo 2257435 6102341 := bbase (se 4 (by rfl) ⟨572094, by rfl⟩ : syracuseStep 6102341 = 1144189) (by norm_num)
theorem B4068227 : Blo 2257435 4068227 := bstep (se 1 (by rfl) ⟨3051170, by rfl⟩ : syracuseStep 4068227 = 6102341) B6102341
theorem B2712151 : Blo 2257435 2712151 := bstep (se 1 (by rfl) ⟨2034113, by rfl⟩ : syracuseStep 2712151 = 4068227) B4068227
theorem B3616201 : Blo 2257435 3616201 := bstep (se 2 (by rfl) ⟨1356075, by rfl⟩ : syracuseStep 3616201 = 2712151) B2712151
theorem B4821601 : Blo 2257435 4821601 := bstep (se 2 (by rfl) ⟨1808100, by rfl⟩ : syracuseStep 4821601 = 3616201) B3616201
theorem B6428801 : Blo 2257435 6428801 := bstep (se 2 (by rfl) ⟨2410800, by rfl⟩ : syracuseStep 6428801 = 4821601) B4821601
theorem B4285867 : Blo 2257435 4285867 := bstep (se 1 (by rfl) ⟨3214400, by rfl⟩ : syracuseStep 4285867 = 6428801) B6428801
theorem B5714489 : Blo 2257435 5714489 := bstep (se 2 (by rfl) ⟨2142933, by rfl⟩ : syracuseStep 5714489 = 4285867) B4285867
theorem B3809659 : Blo 2257435 3809659 := bstep (se 1 (by rfl) ⟨2857244, by rfl⟩ : syracuseStep 3809659 = 5714489) B5714489
theorem B5079545 : Blo 2257435 5079545 := bstep (se 2 (by rfl) ⟨1904829, by rfl⟩ : syracuseStep 5079545 = 3809659) B3809659
theorem B3386363 : Blo 2257435 3386363 := bstep (se 1 (by rfl) ⟨2539772, by rfl⟩ : syracuseStep 3386363 = 5079545) B5079545
theorem B2257575 : Blo 2257435 2257575 := bstep (se 1 (by rfl) ⟨1693181, by rfl⟩ : syracuseStep 2257575 = 3386363) B3386363
theorem B2539777 : Blo 2257435 2539777 := bbase (se 2 (by rfl) ⟨952416, by rfl⟩ : syracuseStep 2539777 = 1904833) (by norm_num)
theorem B3386369 : Blo 2257435 3386369 := bstep (se 2 (by rfl) ⟨1269888, by rfl⟩ : syracuseStep 3386369 = 2539777) B2539777
theorem B2257579 : Blo 2257435 2257579 := bstep (se 1 (by rfl) ⟨1693184, by rfl⟩ : syracuseStep 2257579 = 3386369) B3386369
theorem B5714509 : Blo 2257435 5714509 := bbase (se 3 (by rfl) ⟨1071470, by rfl⟩ : syracuseStep 5714509 = 2142941) (by norm_num)
theorem B7619345 : Blo 2257435 7619345 := bstep (se 2 (by rfl) ⟨2857254, by rfl⟩ : syracuseStep 7619345 = 5714509) B5714509
theorem B5079563 : Blo 2257435 5079563 := bstep (se 1 (by rfl) ⟨3809672, by rfl⟩ : syracuseStep 5079563 = 7619345) B7619345
theorem B3386375 : Blo 2257435 3386375 := bstep (se 1 (by rfl) ⟨2539781, by rfl⟩ : syracuseStep 3386375 = 5079563) B5079563
theorem B2257583 : Blo 2257435 2257583 := bstep (se 1 (by rfl) ⟨1693187, by rfl⟩ : syracuseStep 2257583 = 3386375) B3386375
theorem B3386381 : Blo 2257435 3386381 := bbase (se 3 (by rfl) ⟨634946, by rfl⟩ : syracuseStep 3386381 = 1269893) (by norm_num)
theorem B2257587 : Blo 2257435 2257587 := bstep (se 1 (by rfl) ⟨1693190, by rfl⟩ : syracuseStep 2257587 = 3386381) B3386381
theorem B5079581 : Blo 2257435 5079581 := bbase (se 3 (by rfl) ⟨952421, by rfl⟩ : syracuseStep 5079581 = 1904843) (by norm_num)
theorem B3386387 : Blo 2257435 3386387 := bstep (se 1 (by rfl) ⟨2539790, by rfl⟩ : syracuseStep 3386387 = 5079581) B5079581
theorem B2257591 : Blo 2257435 2257591 := bstep (se 1 (by rfl) ⟨1693193, by rfl⟩ : syracuseStep 2257591 = 3386387) B3386387
theorem B3809693 : Blo 2257435 3809693 := bbase (se 3 (by rfl) ⟨714317, by rfl⟩ : syracuseStep 3809693 = 1428635) (by norm_num)
theorem B2539795 : Blo 2257435 2539795 := bstep (se 1 (by rfl) ⟨1904846, by rfl⟩ : syracuseStep 2539795 = 3809693) B3809693
theorem B3386393 : Blo 2257435 3386393 := bstep (se 2 (by rfl) ⟨1269897, by rfl⟩ : syracuseStep 3386393 = 2539795) B2539795
theorem B2257595 : Blo 2257435 2257595 := bstep (se 1 (by rfl) ⟨1693196, by rfl⟩ : syracuseStep 2257595 = 3386393) B3386393
theorem B9153605 : Blo 2257435 9153605 := bbase (se 4 (by rfl) ⟨858150, by rfl⟩ : syracuseStep 9153605 = 1716301) (by norm_num)
theorem B24409613 : Blo 2257435 24409613 := bstep (se 3 (by rfl) ⟨4576802, by rfl⟩ : syracuseStep 24409613 = 9153605) B9153605
theorem B16273075 : Blo 2257435 16273075 := bstep (se 1 (by rfl) ⟨12204806, by rfl⟩ : syracuseStep 16273075 = 24409613) B24409613
theorem B21697433 : Blo 2257435 21697433 := bstep (se 2 (by rfl) ⟨8136537, by rfl⟩ : syracuseStep 21697433 = 16273075) B16273075
theorem B14464955 : Blo 2257435 14464955 := bstep (se 1 (by rfl) ⟨10848716, by rfl⟩ : syracuseStep 14464955 = 21697433) B21697433
theorem B9643303 : Blo 2257435 9643303 := bstep (se 1 (by rfl) ⟨7232477, by rfl⟩ : syracuseStep 9643303 = 14464955) B14464955
theorem B12857737 : Blo 2257435 12857737 := bstep (se 2 (by rfl) ⟨4821651, by rfl⟩ : syracuseStep 12857737 = 9643303) B9643303
theorem B17143649 : Blo 2257435 17143649 := bstep (se 2 (by rfl) ⟨6428868, by rfl⟩ : syracuseStep 17143649 = 12857737) B12857737
theorem B11429099 : Blo 2257435 11429099 := bstep (se 1 (by rfl) ⟨8571824, by rfl⟩ : syracuseStep 11429099 = 17143649) B17143649
theorem B7619399 : Blo 2257435 7619399 := bstep (se 1 (by rfl) ⟨5714549, by rfl⟩ : syracuseStep 7619399 = 11429099) B11429099
theorem B5079599 : Blo 2257435 5079599 := bstep (se 1 (by rfl) ⟨3809699, by rfl⟩ : syracuseStep 5079599 = 7619399) B7619399
theorem B3386399 : Blo 2257435 3386399 := bstep (se 1 (by rfl) ⟨2539799, by rfl⟩ : syracuseStep 3386399 = 5079599) B5079599
theorem B2257599 : Blo 2257435 2257599 := bstep (se 1 (by rfl) ⟨1693199, by rfl⟩ : syracuseStep 2257599 = 3386399) B3386399
theorem B3386405 : Blo 2257435 3386405 := bbase (se 4 (by rfl) ⟨317475, by rfl⟩ : syracuseStep 3386405 = 634951) (by norm_num)
theorem B2257603 : Blo 2257435 2257603 := bstep (se 1 (by rfl) ⟨1693202, by rfl⟩ : syracuseStep 2257603 = 3386405) B3386405
theorem B2857285 : Blo 2257435 2857285 := bbase (se 4 (by rfl) ⟨267870, by rfl⟩ : syracuseStep 2857285 = 535741) (by norm_num)
theorem B3809713 : Blo 2257435 3809713 := bstep (se 2 (by rfl) ⟨1428642, by rfl⟩ : syracuseStep 3809713 = 2857285) B2857285
theorem B5079617 : Blo 2257435 5079617 := bstep (se 2 (by rfl) ⟨1904856, by rfl⟩ : syracuseStep 5079617 = 3809713) B3809713
theorem B3386411 : Blo 2257435 3386411 := bstep (se 1 (by rfl) ⟨2539808, by rfl⟩ : syracuseStep 3386411 = 5079617) B5079617
theorem B2257607 : Blo 2257435 2257607 := bstep (se 1 (by rfl) ⟨1693205, by rfl⟩ : syracuseStep 2257607 = 3386411) B3386411
theorem B2539813 : Blo 2257435 2539813 := bbase (se 4 (by rfl) ⟨238107, by rfl⟩ : syracuseStep 2539813 = 476215) (by norm_num)
theorem B3386417 : Blo 2257435 3386417 := bstep (se 2 (by rfl) ⟨1269906, by rfl⟩ : syracuseStep 3386417 = 2539813) B2539813
theorem B2257611 : Blo 2257435 2257611 := bstep (se 1 (by rfl) ⟨1693208, by rfl⟩ : syracuseStep 2257611 = 3386417) B3386417
theorem B4576837 : Blo 2257435 4576837 := bbase (se 4 (by rfl) ⟨429078, by rfl⟩ : syracuseStep 4576837 = 858157) (by norm_num)
theorem B6102449 : Blo 2257435 6102449 := bstep (se 2 (by rfl) ⟨2288418, by rfl⟩ : syracuseStep 6102449 = 4576837) B4576837
theorem B4068299 : Blo 2257435 4068299 := bstep (se 1 (by rfl) ⟨3051224, by rfl⟩ : syracuseStep 4068299 = 6102449) B6102449
theorem B2712199 : Blo 2257435 2712199 := bstep (se 1 (by rfl) ⟨2034149, by rfl⟩ : syracuseStep 2712199 = 4068299) B4068299
theorem B3616265 : Blo 2257435 3616265 := bstep (se 2 (by rfl) ⟨1356099, by rfl⟩ : syracuseStep 3616265 = 2712199) B2712199
theorem B9643373 : Blo 2257435 9643373 := bstep (se 3 (by rfl) ⟨1808132, by rfl⟩ : syracuseStep 9643373 = 3616265) B3616265
theorem B6428915 : Blo 2257435 6428915 := bstep (se 1 (by rfl) ⟨4821686, by rfl⟩ : syracuseStep 6428915 = 9643373) B9643373
theorem B4285943 : Blo 2257435 4285943 := bstep (se 1 (by rfl) ⟨3214457, by rfl⟩ : syracuseStep 4285943 = 6428915) B6428915
theorem B2857295 : Blo 2257435 2857295 := bstep (se 1 (by rfl) ⟨2142971, by rfl⟩ : syracuseStep 2857295 = 4285943) B4285943
theorem B7619453 : Blo 2257435 7619453 := bstep (se 3 (by rfl) ⟨1428647, by rfl⟩ : syracuseStep 7619453 = 2857295) B2857295
theorem B5079635 : Blo 2257435 5079635 := bstep (se 1 (by rfl) ⟨3809726, by rfl⟩ : syracuseStep 5079635 = 7619453) B7619453
theorem B3386423 : Blo 2257435 3386423 := bstep (se 1 (by rfl) ⟨2539817, by rfl⟩ : syracuseStep 3386423 = 5079635) B5079635
theorem B2257615 : Blo 2257435 2257615 := bstep (se 1 (by rfl) ⟨1693211, by rfl⟩ : syracuseStep 2257615 = 3386423) B3386423
theorem B3386429 : Blo 2257435 3386429 := bbase (se 3 (by rfl) ⟨634955, by rfl⟩ : syracuseStep 3386429 = 1269911) (by norm_num)
theorem B2257619 : Blo 2257435 2257619 := bstep (se 1 (by rfl) ⟨1693214, by rfl⟩ : syracuseStep 2257619 = 3386429) B3386429
theorem B5079653 : Blo 2257435 5079653 := bbase (se 4 (by rfl) ⟨476217, by rfl⟩ : syracuseStep 5079653 = 952435) (by norm_num)
theorem B3386435 : Blo 2257435 3386435 := bstep (se 1 (by rfl) ⟨2539826, by rfl⟩ : syracuseStep 3386435 = 5079653) B5079653
theorem B2257623 : Blo 2257435 2257623 := bstep (se 1 (by rfl) ⟨1693217, by rfl⟩ : syracuseStep 2257623 = 3386435) B3386435
theorem B5714621 : Blo 2257435 5714621 := bbase (se 3 (by rfl) ⟨1071491, by rfl⟩ : syracuseStep 5714621 = 2142983) (by norm_num)
theorem B3809747 : Blo 2257435 3809747 := bstep (se 1 (by rfl) ⟨2857310, by rfl⟩ : syracuseStep 3809747 = 5714621) B5714621
theorem B2539831 : Blo 2257435 2539831 := bstep (se 1 (by rfl) ⟨1904873, by rfl⟩ : syracuseStep 2539831 = 3809747) B3809747
theorem B3386441 : Blo 2257435 3386441 := bstep (se 2 (by rfl) ⟨1269915, by rfl⟩ : syracuseStep 3386441 = 2539831) B2539831
theorem B2257627 : Blo 2257435 2257627 := bstep (se 1 (by rfl) ⟨1693220, by rfl⟩ : syracuseStep 2257627 = 3386441) B3386441
theorem B4285973 : Blo 2257435 4285973 := bbase (se 6 (by rfl) ⟨100452, by rfl⟩ : syracuseStep 4285973 = 200905) (by norm_num)
theorem B11429261 : Blo 2257435 11429261 := bstep (se 3 (by rfl) ⟨2142986, by rfl⟩ : syracuseStep 11429261 = 4285973) B4285973
theorem B7619507 : Blo 2257435 7619507 := bstep (se 1 (by rfl) ⟨5714630, by rfl⟩ : syracuseStep 7619507 = 11429261) B11429261
theorem B5079671 : Blo 2257435 5079671 := bstep (se 1 (by rfl) ⟨3809753, by rfl⟩ : syracuseStep 5079671 = 7619507) B7619507
theorem B3386447 : Blo 2257435 3386447 := bstep (se 1 (by rfl) ⟨2539835, by rfl⟩ : syracuseStep 3386447 = 5079671) B5079671
theorem B2257631 : Blo 2257435 2257631 := bstep (se 1 (by rfl) ⟨1693223, by rfl⟩ : syracuseStep 2257631 = 3386447) B3386447
theorem B3386453 : Blo 2257435 3386453 := bbase (se 8 (by rfl) ⟨19842, by rfl⟩ : syracuseStep 3386453 = 39685) (by norm_num)
theorem B2257635 : Blo 2257435 2257635 := bstep (se 1 (by rfl) ⟨1693226, by rfl⟩ : syracuseStep 2257635 = 3386453) B3386453
theorem B3258349 : Blo 2257435 3258349 := bbase (se 3 (by rfl) ⟨610940, by rfl⟩ : syracuseStep 3258349 = 1221881) (by norm_num)
theorem B17377861 : Blo 2257435 17377861 := bstep (se 4 (by rfl) ⟨1629174, by rfl⟩ : syracuseStep 17377861 = 3258349) B3258349
theorem B23170481 : Blo 2257435 23170481 := bstep (se 2 (by rfl) ⟨8688930, by rfl⟩ : syracuseStep 23170481 = 17377861) B17377861
theorem B15446987 : Blo 2257435 15446987 := bstep (se 1 (by rfl) ⟨11585240, by rfl⟩ : syracuseStep 15446987 = 23170481) B23170481
theorem B10297991 : Blo 2257435 10297991 := bstep (se 1 (by rfl) ⟨7723493, by rfl⟩ : syracuseStep 10297991 = 15446987) B15446987
theorem B6865327 : Blo 2257435 6865327 := bstep (se 1 (by rfl) ⟨5148995, by rfl⟩ : syracuseStep 6865327 = 10297991) B10297991
theorem B9153769 : Blo 2257435 9153769 := bstep (se 2 (by rfl) ⟨3432663, by rfl⟩ : syracuseStep 9153769 = 6865327) B6865327
theorem B12205025 : Blo 2257435 12205025 := bstep (se 2 (by rfl) ⟨4576884, by rfl⟩ : syracuseStep 12205025 = 9153769) B9153769
theorem B8136683 : Blo 2257435 8136683 := bstep (se 1 (by rfl) ⟨6102512, by rfl⟩ : syracuseStep 8136683 = 12205025) B12205025
theorem B5424455 : Blo 2257435 5424455 := bstep (se 1 (by rfl) ⟨4068341, by rfl⟩ : syracuseStep 5424455 = 8136683) B8136683
theorem B14465213 : Blo 2257435 14465213 := bstep (se 3 (by rfl) ⟨2712227, by rfl⟩ : syracuseStep 14465213 = 5424455) B5424455
theorem B9643475 : Blo 2257435 9643475 := bstep (se 1 (by rfl) ⟨7232606, by rfl⟩ : syracuseStep 9643475 = 14465213) B14465213
theorem B6428983 : Blo 2257435 6428983 := bstep (se 1 (by rfl) ⟨4821737, by rfl⟩ : syracuseStep 6428983 = 9643475) B9643475
theorem B8571977 : Blo 2257435 8571977 := bstep (se 2 (by rfl) ⟨3214491, by rfl⟩ : syracuseStep 8571977 = 6428983) B6428983
theorem B5714651 : Blo 2257435 5714651 := bstep (se 1 (by rfl) ⟨4285988, by rfl⟩ : syracuseStep 5714651 = 8571977) B8571977
theorem B3809767 : Blo 2257435 3809767 := bstep (se 1 (by rfl) ⟨2857325, by rfl⟩ : syracuseStep 3809767 = 5714651) B5714651
theorem B5079689 : Blo 2257435 5079689 := bstep (se 2 (by rfl) ⟨1904883, by rfl⟩ : syracuseStep 5079689 = 3809767) B3809767
theorem B3386459 : Blo 2257435 3386459 := bstep (se 1 (by rfl) ⟨2539844, by rfl⟩ : syracuseStep 3386459 = 5079689) B5079689
theorem B2257639 : Blo 2257435 2257639 := bstep (se 1 (by rfl) ⟨1693229, by rfl⟩ : syracuseStep 2257639 = 3386459) B3386459
theorem B2539849 : Blo 2257435 2539849 := bbase (se 2 (by rfl) ⟨952443, by rfl⟩ : syracuseStep 2539849 = 1904887) (by norm_num)
theorem B3386465 : Blo 2257435 3386465 := bstep (se 2 (by rfl) ⟨1269924, by rfl⟩ : syracuseStep 3386465 = 2539849) B2539849
theorem B2257643 : Blo 2257435 2257643 := bstep (se 1 (by rfl) ⟨1693232, by rfl⟩ : syracuseStep 2257643 = 3386465) B3386465
theorem B47614229 : Blo 2257435 47614229 := bbase (se 6 (by rfl) ⟨1115958, by rfl⟩ : syracuseStep 47614229 = 2231917) (by norm_num)
theorem B31742819 : Blo 2257435 31742819 := bstep (se 1 (by rfl) ⟨23807114, by rfl⟩ : syracuseStep 31742819 = 47614229) B47614229
theorem B21161879 : Blo 2257435 21161879 := bstep (se 1 (by rfl) ⟨15871409, by rfl⟩ : syracuseStep 21161879 = 31742819) B31742819
theorem B225726709 : Blo 2257435 225726709 := bstep (se 5 (by rfl) ⟨10580939, by rfl⟩ : syracuseStep 225726709 = 21161879) B21161879
theorem B300968945 : Blo 2257435 300968945 := bstep (se 2 (by rfl) ⟨112863354, by rfl⟩ : syracuseStep 300968945 = 225726709) B225726709
theorem B200645963 : Blo 2257435 200645963 := bstep (se 1 (by rfl) ⟨150484472, by rfl⟩ : syracuseStep 200645963 = 300968945) B300968945
theorem B133763975 : Blo 2257435 133763975 := bstep (se 1 (by rfl) ⟨100322981, by rfl⟩ : syracuseStep 133763975 = 200645963) B200645963
theorem B89175983 : Blo 2257435 89175983 := bstep (se 1 (by rfl) ⟨66881987, by rfl⟩ : syracuseStep 89175983 = 133763975) B133763975
theorem B951210485 : Blo 2257435 951210485 := bstep (se 5 (by rfl) ⟨44587991, by rfl⟩ : syracuseStep 951210485 = 89175983) B89175983
theorem B634140323 : Blo 2257435 634140323 := bstep (se 1 (by rfl) ⟨475605242, by rfl⟩ : syracuseStep 634140323 = 951210485) B951210485
theorem B422760215 : Blo 2257435 422760215 := bstep (se 1 (by rfl) ⟨317070161, by rfl⟩ : syracuseStep 422760215 = 634140323) B634140323
theorem B281840143 : Blo 2257435 281840143 := bstep (se 1 (by rfl) ⟨211380107, by rfl⟩ : syracuseStep 281840143 = 422760215) B422760215
theorem B375786857 : Blo 2257435 375786857 := bstep (se 2 (by rfl) ⟨140920071, by rfl⟩ : syracuseStep 375786857 = 281840143) B281840143
theorem B250524571 : Blo 2257435 250524571 := bstep (se 1 (by rfl) ⟨187893428, by rfl⟩ : syracuseStep 250524571 = 375786857) B375786857
theorem B334032761 : Blo 2257435 334032761 := bstep (se 2 (by rfl) ⟨125262285, by rfl⟩ : syracuseStep 334032761 = 250524571) B250524571
theorem B890754029 : Blo 2257435 890754029 := bstep (se 3 (by rfl) ⟨167016380, by rfl⟩ : syracuseStep 890754029 = 334032761) B334032761
theorem B593836019 : Blo 2257435 593836019 := bstep (se 1 (by rfl) ⟨445377014, by rfl⟩ : syracuseStep 593836019 = 890754029) B890754029
theorem B395890679 : Blo 2257435 395890679 := bstep (se 1 (by rfl) ⟨296918009, by rfl⟩ : syracuseStep 395890679 = 593836019) B593836019
theorem B263927119 : Blo 2257435 263927119 := bstep (se 1 (by rfl) ⟨197945339, by rfl⟩ : syracuseStep 263927119 = 395890679) B395890679
theorem B351902825 : Blo 2257435 351902825 := bstep (se 2 (by rfl) ⟨131963559, by rfl⟩ : syracuseStep 351902825 = 263927119) B263927119
theorem B234601883 : Blo 2257435 234601883 := bstep (se 1 (by rfl) ⟨175951412, by rfl⟩ : syracuseStep 234601883 = 351902825) B351902825
theorem B156401255 : Blo 2257435 156401255 := bstep (se 1 (by rfl) ⟨117300941, by rfl⟩ : syracuseStep 156401255 = 234601883) B234601883
theorem B104267503 : Blo 2257435 104267503 := bstep (se 1 (by rfl) ⟨78200627, by rfl⟩ : syracuseStep 104267503 = 156401255) B156401255
theorem B139023337 : Blo 2257435 139023337 := bstep (se 2 (by rfl) ⟨52133751, by rfl⟩ : syracuseStep 139023337 = 104267503) B104267503
theorem B185364449 : Blo 2257435 185364449 := bstep (se 2 (by rfl) ⟨69511668, by rfl⟩ : syracuseStep 185364449 = 139023337) B139023337
theorem B123576299 : Blo 2257435 123576299 := bstep (se 1 (by rfl) ⟨92682224, by rfl⟩ : syracuseStep 123576299 = 185364449) B185364449
theorem B82384199 : Blo 2257435 82384199 := bstep (se 1 (by rfl) ⟨61788149, by rfl⟩ : syracuseStep 82384199 = 123576299) B123576299
theorem B54922799 : Blo 2257435 54922799 := bstep (se 1 (by rfl) ⟨41192099, by rfl⟩ : syracuseStep 54922799 = 82384199) B82384199
theorem B36615199 : Blo 2257435 36615199 := bstep (se 1 (by rfl) ⟨27461399, by rfl⟩ : syracuseStep 36615199 = 54922799) B54922799
theorem B48820265 : Blo 2257435 48820265 := bstep (se 2 (by rfl) ⟨18307599, by rfl⟩ : syracuseStep 48820265 = 36615199) B36615199
theorem B32546843 : Blo 2257435 32546843 := bstep (se 1 (by rfl) ⟨24410132, by rfl⟩ : syracuseStep 32546843 = 48820265) B48820265
theorem B21697895 : Blo 2257435 21697895 := bstep (se 1 (by rfl) ⟨16273421, by rfl⟩ : syracuseStep 21697895 = 32546843) B32546843
theorem B14465263 : Blo 2257435 14465263 := bstep (se 1 (by rfl) ⟨10848947, by rfl⟩ : syracuseStep 14465263 = 21697895) B21697895
theorem B19287017 : Blo 2257435 19287017 := bstep (se 2 (by rfl) ⟨7232631, by rfl⟩ : syracuseStep 19287017 = 14465263) B14465263
theorem B12858011 : Blo 2257435 12858011 := bstep (se 1 (by rfl) ⟨9643508, by rfl⟩ : syracuseStep 12858011 = 19287017) B19287017
theorem B8572007 : Blo 2257435 8572007 := bstep (se 1 (by rfl) ⟨6429005, by rfl⟩ : syracuseStep 8572007 = 12858011) B12858011
theorem B5714671 : Blo 2257435 5714671 := bstep (se 1 (by rfl) ⟨4286003, by rfl⟩ : syracuseStep 5714671 = 8572007) B8572007
theorem B7619561 : Blo 2257435 7619561 := bstep (se 2 (by rfl) ⟨2857335, by rfl⟩ : syracuseStep 7619561 = 5714671) B5714671
theorem B5079707 : Blo 2257435 5079707 := bstep (se 1 (by rfl) ⟨3809780, by rfl⟩ : syracuseStep 5079707 = 7619561) B7619561
theorem B3386471 : Blo 2257435 3386471 := bstep (se 1 (by rfl) ⟨2539853, by rfl⟩ : syracuseStep 3386471 = 5079707) B5079707
theorem B2257647 : Blo 2257435 2257647 := bstep (se 1 (by rfl) ⟨1693235, by rfl⟩ : syracuseStep 2257647 = 3386471) B3386471
theorem B3386477 : Blo 2257435 3386477 := bbase (se 3 (by rfl) ⟨634964, by rfl⟩ : syracuseStep 3386477 = 1269929) (by norm_num)
theorem B2257651 : Blo 2257435 2257651 := bstep (se 1 (by rfl) ⟨1693238, by rfl⟩ : syracuseStep 2257651 = 3386477) B3386477
theorem B5079725 : Blo 2257435 5079725 := bbase (se 3 (by rfl) ⟨952448, by rfl⟩ : syracuseStep 5079725 = 1904897) (by norm_num)
theorem B3386483 : Blo 2257435 3386483 := bstep (se 1 (by rfl) ⟨2539862, by rfl⟩ : syracuseStep 3386483 = 5079725) B5079725
theorem B2257655 : Blo 2257435 2257655 := bstep (se 1 (by rfl) ⟨1693241, by rfl⟩ : syracuseStep 2257655 = 3386483) B3386483
theorem B4821781 : Blo 2257435 4821781 := bbase (se 6 (by rfl) ⟨113010, by rfl⟩ : syracuseStep 4821781 = 226021) (by norm_num)
theorem B6429041 : Blo 2257435 6429041 := bstep (se 2 (by rfl) ⟨2410890, by rfl⟩ : syracuseStep 6429041 = 4821781) B4821781
theorem B4286027 : Blo 2257435 4286027 := bstep (se 1 (by rfl) ⟨3214520, by rfl⟩ : syracuseStep 4286027 = 6429041) B6429041
theorem B2857351 : Blo 2257435 2857351 := bstep (se 1 (by rfl) ⟨2143013, by rfl⟩ : syracuseStep 2857351 = 4286027) B4286027
theorem B3809801 : Blo 2257435 3809801 := bstep (se 2 (by rfl) ⟨1428675, by rfl⟩ : syracuseStep 3809801 = 2857351) B2857351
theorem B2539867 : Blo 2257435 2539867 := bstep (se 1 (by rfl) ⟨1904900, by rfl⟩ : syracuseStep 2539867 = 3809801) B3809801
theorem B3386489 : Blo 2257435 3386489 := bstep (se 2 (by rfl) ⟨1269933, by rfl⟩ : syracuseStep 3386489 = 2539867) B2539867
theorem B2257659 : Blo 2257435 2257659 := bstep (se 1 (by rfl) ⟨1693244, by rfl⟩ : syracuseStep 2257659 = 3386489) B3386489
theorem B8247781 : Blo 2257435 8247781 := bbase (se 4 (by rfl) ⟨773229, by rfl⟩ : syracuseStep 8247781 = 1546459) (by norm_num)
theorem B10997041 : Blo 2257435 10997041 := bstep (se 2 (by rfl) ⟨4123890, by rfl⟩ : syracuseStep 10997041 = 8247781) B8247781
theorem B14662721 : Blo 2257435 14662721 := bstep (se 2 (by rfl) ⟨5498520, by rfl⟩ : syracuseStep 14662721 = 10997041) B10997041
theorem B9775147 : Blo 2257435 9775147 := bstep (se 1 (by rfl) ⟨7331360, by rfl⟩ : syracuseStep 9775147 = 14662721) B14662721
theorem B13033529 : Blo 2257435 13033529 := bstep (se 2 (by rfl) ⟨4887573, by rfl⟩ : syracuseStep 13033529 = 9775147) B9775147
theorem B556097237 : Blo 2257435 556097237 := bstep (se 7 (by rfl) ⟨6516764, by rfl⟩ : syracuseStep 556097237 = 13033529) B13033529
theorem B370731491 : Blo 2257435 370731491 := bstep (se 1 (by rfl) ⟨278048618, by rfl⟩ : syracuseStep 370731491 = 556097237) B556097237
theorem B247154327 : Blo 2257435 247154327 := bstep (se 1 (by rfl) ⟨185365745, by rfl⟩ : syracuseStep 247154327 = 370731491) B370731491
theorem B164769551 : Blo 2257435 164769551 := bstep (se 1 (by rfl) ⟨123577163, by rfl⟩ : syracuseStep 164769551 = 247154327) B247154327
theorem B109846367 : Blo 2257435 109846367 := bstep (se 1 (by rfl) ⟨82384775, by rfl⟩ : syracuseStep 109846367 = 164769551) B164769551
theorem B73230911 : Blo 2257435 73230911 := bstep (se 1 (by rfl) ⟨54923183, by rfl⟩ : syracuseStep 73230911 = 109846367) B109846367
theorem B48820607 : Blo 2257435 48820607 := bstep (se 1 (by rfl) ⟨36615455, by rfl⟩ : syracuseStep 48820607 = 73230911) B73230911
theorem B32547071 : Blo 2257435 32547071 := bstep (se 1 (by rfl) ⟨24410303, by rfl⟩ : syracuseStep 32547071 = 48820607) B48820607
theorem B21698047 : Blo 2257435 21698047 := bstep (se 1 (by rfl) ⟨16273535, by rfl⟩ : syracuseStep 21698047 = 32547071) B32547071
theorem B28930729 : Blo 2257435 28930729 := bstep (se 2 (by rfl) ⟨10849023, by rfl⟩ : syracuseStep 28930729 = 21698047) B21698047
theorem B38574305 : Blo 2257435 38574305 := bstep (se 2 (by rfl) ⟨14465364, by rfl⟩ : syracuseStep 38574305 = 28930729) B28930729
theorem B25716203 : Blo 2257435 25716203 := bstep (se 1 (by rfl) ⟨19287152, by rfl⟩ : syracuseStep 25716203 = 38574305) B38574305
theorem B17144135 : Blo 2257435 17144135 := bstep (se 1 (by rfl) ⟨12858101, by rfl⟩ : syracuseStep 17144135 = 25716203) B25716203
theorem B11429423 : Blo 2257435 11429423 := bstep (se 1 (by rfl) ⟨8572067, by rfl⟩ : syracuseStep 11429423 = 17144135) B17144135
theorem B7619615 : Blo 2257435 7619615 := bstep (se 1 (by rfl) ⟨5714711, by rfl⟩ : syracuseStep 7619615 = 11429423) B11429423
theorem B5079743 : Blo 2257435 5079743 := bstep (se 1 (by rfl) ⟨3809807, by rfl⟩ : syracuseStep 5079743 = 7619615) B7619615
theorem B3386495 : Blo 2257435 3386495 := bstep (se 1 (by rfl) ⟨2539871, by rfl⟩ : syracuseStep 3386495 = 5079743) B5079743
theorem B2257663 : Blo 2257435 2257663 := bstep (se 1 (by rfl) ⟨1693247, by rfl⟩ : syracuseStep 2257663 = 3386495) B3386495
theorem B3386501 : Blo 2257435 3386501 := bbase (se 4 (by rfl) ⟨317484, by rfl⟩ : syracuseStep 3386501 = 634969) (by norm_num)
theorem B2257667 : Blo 2257435 2257667 := bstep (se 1 (by rfl) ⟨1693250, by rfl⟩ : syracuseStep 2257667 = 3386501) B3386501
theorem B3809821 : Blo 2257435 3809821 := bbase (se 3 (by rfl) ⟨714341, by rfl⟩ : syracuseStep 3809821 = 1428683) (by norm_num)
theorem B5079761 : Blo 2257435 5079761 := bstep (se 2 (by rfl) ⟨1904910, by rfl⟩ : syracuseStep 5079761 = 3809821) B3809821
theorem B3386507 : Blo 2257435 3386507 := bstep (se 1 (by rfl) ⟨2539880, by rfl⟩ : syracuseStep 3386507 = 5079761) B5079761
theorem B2257671 : Blo 2257435 2257671 := bstep (se 1 (by rfl) ⟨1693253, by rfl⟩ : syracuseStep 2257671 = 3386507) B3386507
theorem B2539885 : Blo 2257435 2539885 := bbase (se 3 (by rfl) ⟨476228, by rfl⟩ : syracuseStep 2539885 = 952457) (by norm_num)
theorem B3386513 : Blo 2257435 3386513 := bstep (se 2 (by rfl) ⟨1269942, by rfl⟩ : syracuseStep 3386513 = 2539885) B2539885
theorem B2257675 : Blo 2257435 2257675 := bstep (se 1 (by rfl) ⟨1693256, by rfl⟩ : syracuseStep 2257675 = 3386513) B3386513
theorem B7619669 : Blo 2257435 7619669 := bbase (se 8 (by rfl) ⟨44646, by rfl⟩ : syracuseStep 7619669 = 89293) (by norm_num)
theorem B5079779 : Blo 2257435 5079779 := bstep (se 1 (by rfl) ⟨3809834, by rfl⟩ : syracuseStep 5079779 = 7619669) B7619669
theorem B3386519 : Blo 2257435 3386519 := bstep (se 1 (by rfl) ⟨2539889, by rfl⟩ : syracuseStep 3386519 = 5079779) B5079779
theorem B2257679 : Blo 2257435 2257679 := bstep (se 1 (by rfl) ⟨1693259, by rfl⟩ : syracuseStep 2257679 = 3386519) B3386519
theorem B3386525 : Blo 2257435 3386525 := bbase (se 3 (by rfl) ⟨634973, by rfl⟩ : syracuseStep 3386525 = 1269947) (by norm_num)
theorem B2257683 : Blo 2257435 2257683 := bstep (se 1 (by rfl) ⟨1693262, by rfl⟩ : syracuseStep 2257683 = 3386525) B3386525
theorem B5079797 : Blo 2257435 5079797 := bbase (se 5 (by rfl) ⟨238115, by rfl⟩ : syracuseStep 5079797 = 476231) (by norm_num)
theorem B3386531 : Blo 2257435 3386531 := bstep (se 1 (by rfl) ⟨2539898, by rfl⟩ : syracuseStep 3386531 = 5079797) B5079797
theorem B2257687 : Blo 2257435 2257687 := bstep (se 1 (by rfl) ⟨1693265, by rfl⟩ : syracuseStep 2257687 = 3386531) B3386531
theorem B28931093 : Blo 2257435 28931093 := bbase (se 6 (by rfl) ⟨678072, by rfl⟩ : syracuseStep 28931093 = 1356145) (by norm_num)
theorem B19287395 : Blo 2257435 19287395 := bstep (se 1 (by rfl) ⟨14465546, by rfl⟩ : syracuseStep 19287395 = 28931093) B28931093
theorem B12858263 : Blo 2257435 12858263 := bstep (se 1 (by rfl) ⟨9643697, by rfl⟩ : syracuseStep 12858263 = 19287395) B19287395
theorem B8572175 : Blo 2257435 8572175 := bstep (se 1 (by rfl) ⟨6429131, by rfl⟩ : syracuseStep 8572175 = 12858263) B12858263
theorem B5714783 : Blo 2257435 5714783 := bstep (se 1 (by rfl) ⟨4286087, by rfl⟩ : syracuseStep 5714783 = 8572175) B8572175
theorem B3809855 : Blo 2257435 3809855 := bstep (se 1 (by rfl) ⟨2857391, by rfl⟩ : syracuseStep 3809855 = 5714783) B5714783
theorem B2539903 : Blo 2257435 2539903 := bstep (se 1 (by rfl) ⟨1904927, by rfl⟩ : syracuseStep 2539903 = 3809855) B3809855
theorem B3386537 : Blo 2257435 3386537 := bstep (se 2 (by rfl) ⟨1269951, by rfl⟩ : syracuseStep 3386537 = 2539903) B2539903
theorem B2257691 : Blo 2257435 2257691 := bstep (se 1 (by rfl) ⟨1693268, by rfl⟩ : syracuseStep 2257691 = 3386537) B3386537
theorem B2383453 : Blo 2257435 2383453 := bbase (se 3 (by rfl) ⟨446897, by rfl⟩ : syracuseStep 2383453 = 893795) (by norm_num)
theorem B3177937 : Blo 2257435 3177937 := bstep (se 2 (by rfl) ⟨1191726, by rfl⟩ : syracuseStep 3177937 = 2383453) B2383453
theorem B16948997 : Blo 2257435 16948997 := bstep (se 4 (by rfl) ⟨1588968, by rfl⟩ : syracuseStep 16948997 = 3177937) B3177937
theorem B11299331 : Blo 2257435 11299331 := bstep (se 1 (by rfl) ⟨8474498, by rfl⟩ : syracuseStep 11299331 = 16948997) B16948997
theorem B7532887 : Blo 2257435 7532887 := bstep (se 1 (by rfl) ⟨5649665, by rfl⟩ : syracuseStep 7532887 = 11299331) B11299331
theorem B10043849 : Blo 2257435 10043849 := bstep (se 2 (by rfl) ⟨3766443, by rfl⟩ : syracuseStep 10043849 = 7532887) B7532887
theorem B26783597 : Blo 2257435 26783597 := bstep (se 3 (by rfl) ⟨5021924, by rfl⟩ : syracuseStep 26783597 = 10043849) B10043849
theorem B17855731 : Blo 2257435 17855731 := bstep (se 1 (by rfl) ⟨13391798, by rfl⟩ : syracuseStep 17855731 = 26783597) B26783597
theorem B23807641 : Blo 2257435 23807641 := bstep (se 2 (by rfl) ⟨8927865, by rfl⟩ : syracuseStep 23807641 = 17855731) B17855731
theorem B31743521 : Blo 2257435 31743521 := bstep (se 2 (by rfl) ⟨11903820, by rfl⟩ : syracuseStep 31743521 = 23807641) B23807641
theorem B21162347 : Blo 2257435 21162347 := bstep (se 1 (by rfl) ⟨15871760, by rfl⟩ : syracuseStep 21162347 = 31743521) B31743521
theorem B14108231 : Blo 2257435 14108231 := bstep (se 1 (by rfl) ⟨10581173, by rfl⟩ : syracuseStep 14108231 = 21162347) B21162347
theorem B9405487 : Blo 2257435 9405487 := bstep (se 1 (by rfl) ⟨7054115, by rfl⟩ : syracuseStep 9405487 = 14108231) B14108231
theorem B50162597 : Blo 2257435 50162597 := bstep (se 4 (by rfl) ⟨4702743, by rfl⟩ : syracuseStep 50162597 = 9405487) B9405487
theorem B33441731 : Blo 2257435 33441731 := bstep (se 1 (by rfl) ⟨25081298, by rfl⟩ : syracuseStep 33441731 = 50162597) B50162597
theorem B22294487 : Blo 2257435 22294487 := bstep (se 1 (by rfl) ⟨16720865, by rfl⟩ : syracuseStep 22294487 = 33441731) B33441731
theorem B59451965 : Blo 2257435 59451965 := bstep (se 3 (by rfl) ⟨11147243, by rfl⟩ : syracuseStep 59451965 = 22294487) B22294487
theorem B39634643 : Blo 2257435 39634643 := bstep (se 1 (by rfl) ⟨29725982, by rfl⟩ : syracuseStep 39634643 = 59451965) B59451965
theorem B26423095 : Blo 2257435 26423095 := bstep (se 1 (by rfl) ⟨19817321, by rfl⟩ : syracuseStep 26423095 = 39634643) B39634643
theorem B35230793 : Blo 2257435 35230793 := bstep (se 2 (by rfl) ⟨13211547, by rfl⟩ : syracuseStep 35230793 = 26423095) B26423095
theorem B93948781 : Blo 2257435 93948781 := bstep (se 3 (by rfl) ⟨17615396, by rfl⟩ : syracuseStep 93948781 = 35230793) B35230793
theorem B125265041 : Blo 2257435 125265041 := bstep (se 2 (by rfl) ⟨46974390, by rfl⟩ : syracuseStep 125265041 = 93948781) B93948781
theorem B83510027 : Blo 2257435 83510027 := bstep (se 1 (by rfl) ⟨62632520, by rfl⟩ : syracuseStep 83510027 = 125265041) B125265041
theorem B55673351 : Blo 2257435 55673351 := bstep (se 1 (by rfl) ⟨41755013, by rfl⟩ : syracuseStep 55673351 = 83510027) B83510027
theorem B37115567 : Blo 2257435 37115567 := bstep (se 1 (by rfl) ⟨27836675, by rfl⟩ : syracuseStep 37115567 = 55673351) B55673351
theorem B24743711 : Blo 2257435 24743711 := bstep (se 1 (by rfl) ⟨18557783, by rfl⟩ : syracuseStep 24743711 = 37115567) B37115567
theorem B16495807 : Blo 2257435 16495807 := bstep (se 1 (by rfl) ⟨12371855, by rfl⟩ : syracuseStep 16495807 = 24743711) B24743711
theorem B21994409 : Blo 2257435 21994409 := bstep (se 2 (by rfl) ⟨8247903, by rfl⟩ : syracuseStep 21994409 = 16495807) B16495807
theorem B14662939 : Blo 2257435 14662939 := bstep (se 1 (by rfl) ⟨10997204, by rfl⟩ : syracuseStep 14662939 = 21994409) B21994409
theorem B19550585 : Blo 2257435 19550585 := bstep (se 2 (by rfl) ⟨7331469, by rfl⟩ : syracuseStep 19550585 = 14662939) B14662939
theorem B13033723 : Blo 2257435 13033723 := bstep (se 1 (by rfl) ⟨9775292, by rfl⟩ : syracuseStep 13033723 = 19550585) B19550585
theorem B17378297 : Blo 2257435 17378297 := bstep (se 2 (by rfl) ⟨6516861, by rfl⟩ : syracuseStep 17378297 = 13033723) B13033723
theorem B11585531 : Blo 2257435 11585531 := bstep (se 1 (by rfl) ⟨8689148, by rfl⟩ : syracuseStep 11585531 = 17378297) B17378297
theorem B7723687 : Blo 2257435 7723687 := bstep (se 1 (by rfl) ⟨5792765, by rfl⟩ : syracuseStep 7723687 = 11585531) B11585531
theorem B10298249 : Blo 2257435 10298249 := bstep (se 2 (by rfl) ⟨3861843, by rfl⟩ : syracuseStep 10298249 = 7723687) B7723687
theorem B6865499 : Blo 2257435 6865499 := bstep (se 1 (by rfl) ⟨5149124, by rfl⟩ : syracuseStep 6865499 = 10298249) B10298249
theorem B4576999 : Blo 2257435 4576999 := bstep (se 1 (by rfl) ⟨3432749, by rfl⟩ : syracuseStep 4576999 = 6865499) B6865499
theorem B6102665 : Blo 2257435 6102665 := bstep (se 2 (by rfl) ⟨2288499, by rfl⟩ : syracuseStep 6102665 = 4576999) B4576999
theorem B4068443 : Blo 2257435 4068443 := bstep (se 1 (by rfl) ⟨3051332, by rfl⟩ : syracuseStep 4068443 = 6102665) B6102665
theorem B2712295 : Blo 2257435 2712295 := bstep (se 1 (by rfl) ⟨2034221, by rfl⟩ : syracuseStep 2712295 = 4068443) B4068443
theorem B3616393 : Blo 2257435 3616393 := bstep (se 2 (by rfl) ⟨1356147, by rfl⟩ : syracuseStep 3616393 = 2712295) B2712295
theorem B4821857 : Blo 2257435 4821857 := bstep (se 2 (by rfl) ⟨1808196, by rfl⟩ : syracuseStep 4821857 = 3616393) B3616393
theorem B3214571 : Blo 2257435 3214571 := bstep (se 1 (by rfl) ⟨2410928, by rfl⟩ : syracuseStep 3214571 = 4821857) B4821857
theorem B8572189 : Blo 2257435 8572189 := bstep (se 3 (by rfl) ⟨1607285, by rfl⟩ : syracuseStep 8572189 = 3214571) B3214571
theorem B11429585 : Blo 2257435 11429585 := bstep (se 2 (by rfl) ⟨4286094, by rfl⟩ : syracuseStep 11429585 = 8572189) B8572189
theorem B7619723 : Blo 2257435 7619723 := bstep (se 1 (by rfl) ⟨5714792, by rfl⟩ : syracuseStep 7619723 = 11429585) B11429585
theorem B5079815 : Blo 2257435 5079815 := bstep (se 1 (by rfl) ⟨3809861, by rfl⟩ : syracuseStep 5079815 = 7619723) B7619723
theorem B3386543 : Blo 2257435 3386543 := bstep (se 1 (by rfl) ⟨2539907, by rfl⟩ : syracuseStep 3386543 = 5079815) B5079815
theorem B2257695 : Blo 2257435 2257695 := bstep (se 1 (by rfl) ⟨1693271, by rfl⟩ : syracuseStep 2257695 = 3386543) B3386543
theorem B3386549 : Blo 2257435 3386549 := bbase (se 5 (by rfl) ⟨158744, by rfl⟩ : syracuseStep 3386549 = 317489) (by norm_num)
theorem B2257699 : Blo 2257435 2257699 := bstep (se 1 (by rfl) ⟨1693274, by rfl⟩ : syracuseStep 2257699 = 3386549) B3386549
theorem B5714813 : Blo 2257435 5714813 := bbase (se 3 (by rfl) ⟨1071527, by rfl⟩ : syracuseStep 5714813 = 2143055) (by norm_num)
theorem B3809875 : Blo 2257435 3809875 := bstep (se 1 (by rfl) ⟨2857406, by rfl⟩ : syracuseStep 3809875 = 5714813) B5714813
theorem B5079833 : Blo 2257435 5079833 := bstep (se 2 (by rfl) ⟨1904937, by rfl⟩ : syracuseStep 5079833 = 3809875) B3809875
theorem B3386555 : Blo 2257435 3386555 := bstep (se 1 (by rfl) ⟨2539916, by rfl⟩ : syracuseStep 3386555 = 5079833) B5079833
theorem B2257703 : Blo 2257435 2257703 := bstep (se 1 (by rfl) ⟨1693277, by rfl⟩ : syracuseStep 2257703 = 3386555) B3386555
theorem B2539921 : Blo 2257435 2539921 := bbase (se 2 (by rfl) ⟨952470, by rfl⟩ : syracuseStep 2539921 = 1904941) (by norm_num)
theorem B3386561 : Blo 2257435 3386561 := bstep (se 2 (by rfl) ⟨1269960, by rfl⟩ : syracuseStep 3386561 = 2539921) B2539921
theorem B2257707 : Blo 2257435 2257707 := bstep (se 1 (by rfl) ⟨1693280, by rfl⟩ : syracuseStep 2257707 = 3386561) B3386561
theorem B4286125 : Blo 2257435 4286125 := bbase (se 3 (by rfl) ⟨803648, by rfl⟩ : syracuseStep 4286125 = 1607297) (by norm_num)
theorem B5714833 : Blo 2257435 5714833 := bstep (se 2 (by rfl) ⟨2143062, by rfl⟩ : syracuseStep 5714833 = 4286125) B4286125
theorem B7619777 : Blo 2257435 7619777 := bstep (se 2 (by rfl) ⟨2857416, by rfl⟩ : syracuseStep 7619777 = 5714833) B5714833
theorem B5079851 : Blo 2257435 5079851 := bstep (se 1 (by rfl) ⟨3809888, by rfl⟩ : syracuseStep 5079851 = 7619777) B7619777
theorem B3386567 : Blo 2257435 3386567 := bstep (se 1 (by rfl) ⟨2539925, by rfl⟩ : syracuseStep 3386567 = 5079851) B5079851
theorem B2257711 : Blo 2257435 2257711 := bstep (se 1 (by rfl) ⟨1693283, by rfl⟩ : syracuseStep 2257711 = 3386567) B3386567
theorem B3386573 : Blo 2257435 3386573 := bbase (se 3 (by rfl) ⟨634982, by rfl⟩ : syracuseStep 3386573 = 1269965) (by norm_num)
theorem B2257715 : Blo 2257435 2257715 := bstep (se 1 (by rfl) ⟨1693286, by rfl⟩ : syracuseStep 2257715 = 3386573) B3386573
theorem B5079869 : Blo 2257435 5079869 := bbase (se 3 (by rfl) ⟨952475, by rfl⟩ : syracuseStep 5079869 = 1904951) (by norm_num)
theorem B3386579 : Blo 2257435 3386579 := bstep (se 1 (by rfl) ⟨2539934, by rfl⟩ : syracuseStep 3386579 = 5079869) B5079869
theorem B2257719 : Blo 2257435 2257719 := bstep (se 1 (by rfl) ⟨1693289, by rfl⟩ : syracuseStep 2257719 = 3386579) B3386579
theorem B3809909 : Blo 2257435 3809909 := bbase (se 5 (by rfl) ⟨178589, by rfl⟩ : syracuseStep 3809909 = 357179) (by norm_num)
theorem B2539939 : Blo 2257435 2539939 := bstep (se 1 (by rfl) ⟨1904954, by rfl⟩ : syracuseStep 2539939 = 3809909) B3809909
theorem B3386585 : Blo 2257435 3386585 := bstep (se 2 (by rfl) ⟨1269969, by rfl⟩ : syracuseStep 3386585 = 2539939) B2539939
theorem B2257723 : Blo 2257435 2257723 := bstep (se 1 (by rfl) ⟨1693292, by rfl⟩ : syracuseStep 2257723 = 3386585) B3386585
theorem B4821925 : Blo 2257435 4821925 := bbase (se 4 (by rfl) ⟨452055, by rfl⟩ : syracuseStep 4821925 = 904111) (by norm_num)
theorem B6429233 : Blo 2257435 6429233 := bstep (se 2 (by rfl) ⟨2410962, by rfl⟩ : syracuseStep 6429233 = 4821925) B4821925
theorem B17144621 : Blo 2257435 17144621 := bstep (se 3 (by rfl) ⟨3214616, by rfl⟩ : syracuseStep 17144621 = 6429233) B6429233
theorem B11429747 : Blo 2257435 11429747 := bstep (se 1 (by rfl) ⟨8572310, by rfl⟩ : syracuseStep 11429747 = 17144621) B17144621
theorem B7619831 : Blo 2257435 7619831 := bstep (se 1 (by rfl) ⟨5714873, by rfl⟩ : syracuseStep 7619831 = 11429747) B11429747
theorem B5079887 : Blo 2257435 5079887 := bstep (se 1 (by rfl) ⟨3809915, by rfl⟩ : syracuseStep 5079887 = 7619831) B7619831
theorem B3386591 : Blo 2257435 3386591 := bstep (se 1 (by rfl) ⟨2539943, by rfl⟩ : syracuseStep 3386591 = 5079887) B5079887
theorem B2257727 : Blo 2257435 2257727 := bstep (se 1 (by rfl) ⟨1693295, by rfl⟩ : syracuseStep 2257727 = 3386591) B3386591
theorem B3386597 : Blo 2257435 3386597 := bbase (se 4 (by rfl) ⟨317493, by rfl⟩ : syracuseStep 3386597 = 634987) (by norm_num)
theorem B2257731 : Blo 2257435 2257731 := bstep (se 1 (by rfl) ⟨1693298, by rfl⟩ : syracuseStep 2257731 = 3386597) B3386597
theorem B6102773 : Blo 2257435 6102773 := bbase (se 5 (by rfl) ⟨286067, by rfl⟩ : syracuseStep 6102773 = 572135) (by norm_num)
theorem B4068515 : Blo 2257435 4068515 := bstep (se 1 (by rfl) ⟨3051386, by rfl⟩ : syracuseStep 4068515 = 6102773) B6102773
theorem B10849373 : Blo 2257435 10849373 := bstep (se 3 (by rfl) ⟨2034257, by rfl⟩ : syracuseStep 10849373 = 4068515) B4068515
theorem B7232915 : Blo 2257435 7232915 := bstep (se 1 (by rfl) ⟨5424686, by rfl⟩ : syracuseStep 7232915 = 10849373) B10849373
theorem B4821943 : Blo 2257435 4821943 := bstep (se 1 (by rfl) ⟨3616457, by rfl⟩ : syracuseStep 4821943 = 7232915) B7232915
theorem B6429257 : Blo 2257435 6429257 := bstep (se 2 (by rfl) ⟨2410971, by rfl⟩ : syracuseStep 6429257 = 4821943) B4821943
theorem B4286171 : Blo 2257435 4286171 := bstep (se 1 (by rfl) ⟨3214628, by rfl⟩ : syracuseStep 4286171 = 6429257) B6429257
theorem B2857447 : Blo 2257435 2857447 := bstep (se 1 (by rfl) ⟨2143085, by rfl⟩ : syracuseStep 2857447 = 4286171) B4286171
theorem B3809929 : Blo 2257435 3809929 := bstep (se 2 (by rfl) ⟨1428723, by rfl⟩ : syracuseStep 3809929 = 2857447) B2857447
theorem B5079905 : Blo 2257435 5079905 := bstep (se 2 (by rfl) ⟨1904964, by rfl⟩ : syracuseStep 5079905 = 3809929) B3809929
theorem B3386603 : Blo 2257435 3386603 := bstep (se 1 (by rfl) ⟨2539952, by rfl⟩ : syracuseStep 3386603 = 5079905) B5079905
theorem B2257735 : Blo 2257435 2257735 := bstep (se 1 (by rfl) ⟨1693301, by rfl⟩ : syracuseStep 2257735 = 3386603) B3386603
theorem B2539957 : Blo 2257435 2539957 := bbase (se 5 (by rfl) ⟨119060, by rfl⟩ : syracuseStep 2539957 = 238121) (by norm_num)
theorem B3386609 : Blo 2257435 3386609 := bstep (se 2 (by rfl) ⟨1269978, by rfl⟩ : syracuseStep 3386609 = 2539957) B2539957
theorem B2257739 : Blo 2257435 2257739 := bstep (se 1 (by rfl) ⟨1693304, by rfl⟩ : syracuseStep 2257739 = 3386609) B3386609
theorem B2857457 : Blo 2257435 2857457 := bbase (se 2 (by rfl) ⟨1071546, by rfl⟩ : syracuseStep 2857457 = 2143093) (by norm_num)
theorem B7619885 : Blo 2257435 7619885 := bstep (se 3 (by rfl) ⟨1428728, by rfl⟩ : syracuseStep 7619885 = 2857457) B2857457
theorem B5079923 : Blo 2257435 5079923 := bstep (se 1 (by rfl) ⟨3809942, by rfl⟩ : syracuseStep 5079923 = 7619885) B7619885
theorem B3386615 : Blo 2257435 3386615 := bstep (se 1 (by rfl) ⟨2539961, by rfl⟩ : syracuseStep 3386615 = 5079923) B5079923
theorem B2257743 : Blo 2257435 2257743 := bstep (se 1 (by rfl) ⟨1693307, by rfl⟩ : syracuseStep 2257743 = 3386615) B3386615
theorem B3386621 : Blo 2257435 3386621 := bbase (se 3 (by rfl) ⟨634991, by rfl⟩ : syracuseStep 3386621 = 1269983) (by norm_num)
theorem B2257747 : Blo 2257435 2257747 := bstep (se 1 (by rfl) ⟨1693310, by rfl⟩ : syracuseStep 2257747 = 3386621) B3386621
theorem B5079941 : Blo 2257435 5079941 := bbase (se 4 (by rfl) ⟨476244, by rfl⟩ : syracuseStep 5079941 = 952489) (by norm_num)
theorem B3386627 : Blo 2257435 3386627 := bstep (se 1 (by rfl) ⟨2539970, by rfl⟩ : syracuseStep 3386627 = 5079941) B5079941
theorem B2257751 : Blo 2257435 2257751 := bstep (se 1 (by rfl) ⟨1693313, by rfl⟩ : syracuseStep 2257751 = 3386627) B3386627
theorem B2410993 : Blo 2257435 2410993 := bbase (se 2 (by rfl) ⟨904122, by rfl⟩ : syracuseStep 2410993 = 1808245) (by norm_num)
theorem B3214657 : Blo 2257435 3214657 := bstep (se 2 (by rfl) ⟨1205496, by rfl⟩ : syracuseStep 3214657 = 2410993) B2410993
theorem B4286209 : Blo 2257435 4286209 := bstep (se 2 (by rfl) ⟨1607328, by rfl⟩ : syracuseStep 4286209 = 3214657) B3214657
theorem B5714945 : Blo 2257435 5714945 := bstep (se 2 (by rfl) ⟨2143104, by rfl⟩ : syracuseStep 5714945 = 4286209) B4286209
theorem B3809963 : Blo 2257435 3809963 := bstep (se 1 (by rfl) ⟨2857472, by rfl⟩ : syracuseStep 3809963 = 5714945) B5714945
theorem B2539975 : Blo 2257435 2539975 := bstep (se 1 (by rfl) ⟨1904981, by rfl⟩ : syracuseStep 2539975 = 3809963) B3809963
theorem B3386633 : Blo 2257435 3386633 := bstep (se 2 (by rfl) ⟨1269987, by rfl⟩ : syracuseStep 3386633 = 2539975) B2539975
theorem B2257755 : Blo 2257435 2257755 := bstep (se 1 (by rfl) ⟨1693316, by rfl⟩ : syracuseStep 2257755 = 3386633) B3386633
theorem B11429909 : Blo 2257435 11429909 := bbase (se 6 (by rfl) ⟨267888, by rfl⟩ : syracuseStep 11429909 = 535777) (by norm_num)
theorem B7619939 : Blo 2257435 7619939 := bstep (se 1 (by rfl) ⟨5714954, by rfl⟩ : syracuseStep 7619939 = 11429909) B11429909
theorem B5079959 : Blo 2257435 5079959 := bstep (se 1 (by rfl) ⟨3809969, by rfl⟩ : syracuseStep 5079959 = 7619939) B7619939
theorem B3386639 : Blo 2257435 3386639 := bstep (se 1 (by rfl) ⟨2539979, by rfl⟩ : syracuseStep 3386639 = 5079959) B5079959
theorem B2257759 : Blo 2257435 2257759 := bstep (se 1 (by rfl) ⟨1693319, by rfl⟩ : syracuseStep 2257759 = 3386639) B3386639
theorem B3386645 : Blo 2257435 3386645 := bbase (se 6 (by rfl) ⟨79374, by rfl⟩ : syracuseStep 3386645 = 158749) (by norm_num)
theorem B2257763 : Blo 2257435 2257763 := bstep (se 1 (by rfl) ⟨1693322, by rfl⟩ : syracuseStep 2257763 = 3386645) B3386645
theorem B3258533 : Blo 2257435 3258533 := bbase (se 4 (by rfl) ⟨305487, by rfl⟩ : syracuseStep 3258533 = 610975) (by norm_num)
theorem B8689421 : Blo 2257435 8689421 := bstep (se 3 (by rfl) ⟨1629266, by rfl⟩ : syracuseStep 8689421 = 3258533) B3258533
theorem B23171789 : Blo 2257435 23171789 := bstep (se 3 (by rfl) ⟨4344710, by rfl⟩ : syracuseStep 23171789 = 8689421) B8689421
theorem B61791437 : Blo 2257435 61791437 := bstep (se 3 (by rfl) ⟨11585894, by rfl⟩ : syracuseStep 61791437 = 23171789) B23171789
theorem B41194291 : Blo 2257435 41194291 := bstep (se 1 (by rfl) ⟨30895718, by rfl⟩ : syracuseStep 41194291 = 61791437) B61791437
theorem B54925721 : Blo 2257435 54925721 := bstep (se 2 (by rfl) ⟨20597145, by rfl⟩ : syracuseStep 54925721 = 41194291) B41194291
theorem B36617147 : Blo 2257435 36617147 := bstep (se 1 (by rfl) ⟨27462860, by rfl⟩ : syracuseStep 36617147 = 54925721) B54925721
theorem B24411431 : Blo 2257435 24411431 := bstep (se 1 (by rfl) ⟨18308573, by rfl⟩ : syracuseStep 24411431 = 36617147) B36617147
theorem B16274287 : Blo 2257435 16274287 := bstep (se 1 (by rfl) ⟨12205715, by rfl⟩ : syracuseStep 16274287 = 24411431) B24411431
theorem B21699049 : Blo 2257435 21699049 := bstep (se 2 (by rfl) ⟨8137143, by rfl⟩ : syracuseStep 21699049 = 16274287) B16274287
theorem B28932065 : Blo 2257435 28932065 := bstep (se 2 (by rfl) ⟨10849524, by rfl⟩ : syracuseStep 28932065 = 21699049) B21699049
theorem B19288043 : Blo 2257435 19288043 := bstep (se 1 (by rfl) ⟨14466032, by rfl⟩ : syracuseStep 19288043 = 28932065) B28932065
theorem B12858695 : Blo 2257435 12858695 := bstep (se 1 (by rfl) ⟨9644021, by rfl⟩ : syracuseStep 12858695 = 19288043) B19288043
theorem B8572463 : Blo 2257435 8572463 := bstep (se 1 (by rfl) ⟨6429347, by rfl⟩ : syracuseStep 8572463 = 12858695) B12858695
theorem B5714975 : Blo 2257435 5714975 := bstep (se 1 (by rfl) ⟨4286231, by rfl⟩ : syracuseStep 5714975 = 8572463) B8572463
theorem B3809983 : Blo 2257435 3809983 := bstep (se 1 (by rfl) ⟨2857487, by rfl⟩ : syracuseStep 3809983 = 5714975) B5714975
theorem B5079977 : Blo 2257435 5079977 := bstep (se 2 (by rfl) ⟨1904991, by rfl⟩ : syracuseStep 5079977 = 3809983) B3809983
theorem B3386651 : Blo 2257435 3386651 := bstep (se 1 (by rfl) ⟨2539988, by rfl⟩ : syracuseStep 3386651 = 5079977) B5079977
theorem B2257767 : Blo 2257435 2257767 := bstep (se 1 (by rfl) ⟨1693325, by rfl⟩ : syracuseStep 2257767 = 3386651) B3386651
theorem B2539993 : Blo 2257435 2539993 := bbase (se 2 (by rfl) ⟨952497, by rfl⟩ : syracuseStep 2539993 = 1904995) (by norm_num)
theorem B3386657 : Blo 2257435 3386657 := bstep (se 2 (by rfl) ⟨1269996, by rfl⟩ : syracuseStep 3386657 = 2539993) B2539993
theorem B2257771 : Blo 2257435 2257771 := bstep (se 1 (by rfl) ⟨1693328, by rfl⟩ : syracuseStep 2257771 = 3386657) B3386657
theorem B3214685 : Blo 2257435 3214685 := bbase (se 3 (by rfl) ⟨602753, by rfl⟩ : syracuseStep 3214685 = 1205507) (by norm_num)
theorem B8572493 : Blo 2257435 8572493 := bstep (se 3 (by rfl) ⟨1607342, by rfl⟩ : syracuseStep 8572493 = 3214685) B3214685
theorem B5714995 : Blo 2257435 5714995 := bstep (se 1 (by rfl) ⟨4286246, by rfl⟩ : syracuseStep 5714995 = 8572493) B8572493
theorem B7619993 : Blo 2257435 7619993 := bstep (se 2 (by rfl) ⟨2857497, by rfl⟩ : syracuseStep 7619993 = 5714995) B5714995
theorem B5079995 : Blo 2257435 5079995 := bstep (se 1 (by rfl) ⟨3809996, by rfl⟩ : syracuseStep 5079995 = 7619993) B7619993
theorem B3386663 : Blo 2257435 3386663 := bstep (se 1 (by rfl) ⟨2539997, by rfl⟩ : syracuseStep 3386663 = 5079995) B5079995
theorem B2257775 : Blo 2257435 2257775 := bstep (se 1 (by rfl) ⟨1693331, by rfl⟩ : syracuseStep 2257775 = 3386663) B3386663
theorem B3386669 : Blo 2257435 3386669 := bbase (se 3 (by rfl) ⟨635000, by rfl⟩ : syracuseStep 3386669 = 1270001) (by norm_num)
theorem B2257779 : Blo 2257435 2257779 := bstep (se 1 (by rfl) ⟨1693334, by rfl⟩ : syracuseStep 2257779 = 3386669) B3386669
theorem B5080013 : Blo 2257435 5080013 := bbase (se 3 (by rfl) ⟨952502, by rfl⟩ : syracuseStep 5080013 = 1905005) (by norm_num)
theorem B3386675 : Blo 2257435 3386675 := bstep (se 1 (by rfl) ⟨2540006, by rfl⟩ : syracuseStep 3386675 = 5080013) B5080013
theorem B2257783 : Blo 2257435 2257783 := bstep (se 1 (by rfl) ⟨1693337, by rfl⟩ : syracuseStep 2257783 = 3386675) B3386675
theorem B2857513 : Blo 2257435 2857513 := bbase (se 2 (by rfl) ⟨1071567, by rfl⟩ : syracuseStep 2857513 = 2143135) (by norm_num)
theorem B3810017 : Blo 2257435 3810017 := bstep (se 2 (by rfl) ⟨1428756, by rfl⟩ : syracuseStep 3810017 = 2857513) B2857513
theorem B2540011 : Blo 2257435 2540011 := bstep (se 1 (by rfl) ⟨1905008, by rfl⟩ : syracuseStep 2540011 = 3810017) B3810017
theorem B3386681 : Blo 2257435 3386681 := bstep (se 2 (by rfl) ⟨1270005, by rfl⟩ : syracuseStep 3386681 = 2540011) B2540011
theorem B2257787 : Blo 2257435 2257787 := bstep (se 1 (by rfl) ⟨1693340, by rfl⟩ : syracuseStep 2257787 = 3386681) B3386681
theorem B7936213 : Blo 2257435 7936213 := bbase (se 7 (by rfl) ⟨93002, by rfl⟩ : syracuseStep 7936213 = 186005) (by norm_num)
theorem B10581617 : Blo 2257435 10581617 := bstep (se 2 (by rfl) ⟨3968106, by rfl⟩ : syracuseStep 10581617 = 7936213) B7936213
theorem B7054411 : Blo 2257435 7054411 := bstep (se 1 (by rfl) ⟨5290808, by rfl⟩ : syracuseStep 7054411 = 10581617) B10581617
theorem B9405881 : Blo 2257435 9405881 := bstep (se 2 (by rfl) ⟨3527205, by rfl⟩ : syracuseStep 9405881 = 7054411) B7054411
theorem B6270587 : Blo 2257435 6270587 := bstep (se 1 (by rfl) ⟨4702940, by rfl⟩ : syracuseStep 6270587 = 9405881) B9405881
theorem B4180391 : Blo 2257435 4180391 := bstep (se 1 (by rfl) ⟨3135293, by rfl⟩ : syracuseStep 4180391 = 6270587) B6270587
theorem B178363349 : Blo 2257435 178363349 := bstep (se 7 (by rfl) ⟨2090195, by rfl⟩ : syracuseStep 178363349 = 4180391) B4180391
theorem B118908899 : Blo 2257435 118908899 := bstep (se 1 (by rfl) ⟨89181674, by rfl⟩ : syracuseStep 118908899 = 178363349) B178363349
theorem B79272599 : Blo 2257435 79272599 := bstep (se 1 (by rfl) ⟨59454449, by rfl⟩ : syracuseStep 79272599 = 118908899) B118908899
theorem B211393597 : Blo 2257435 211393597 := bstep (se 3 (by rfl) ⟨39636299, by rfl⟩ : syracuseStep 211393597 = 79272599) B79272599
theorem B281858129 : Blo 2257435 281858129 := bstep (se 2 (by rfl) ⟨105696798, by rfl⟩ : syracuseStep 281858129 = 211393597) B211393597
theorem B187905419 : Blo 2257435 187905419 := bstep (se 1 (by rfl) ⟨140929064, by rfl⟩ : syracuseStep 187905419 = 281858129) B281858129
theorem B125270279 : Blo 2257435 125270279 := bstep (se 1 (by rfl) ⟨93952709, by rfl⟩ : syracuseStep 125270279 = 187905419) B187905419
theorem B83513519 : Blo 2257435 83513519 := bstep (se 1 (by rfl) ⟨62635139, by rfl⟩ : syracuseStep 83513519 = 125270279) B125270279
theorem B55675679 : Blo 2257435 55675679 := bstep (se 1 (by rfl) ⟨41756759, by rfl⟩ : syracuseStep 55675679 = 83513519) B83513519
theorem B148468477 : Blo 2257435 148468477 := bstep (se 3 (by rfl) ⟨27837839, by rfl⟩ : syracuseStep 148468477 = 55675679) B55675679
theorem B197957969 : Blo 2257435 197957969 := bstep (se 2 (by rfl) ⟨74234238, by rfl⟩ : syracuseStep 197957969 = 148468477) B148468477
theorem B131971979 : Blo 2257435 131971979 := bstep (se 1 (by rfl) ⟨98978984, by rfl⟩ : syracuseStep 131971979 = 197957969) B197957969
theorem B87981319 : Blo 2257435 87981319 := bstep (se 1 (by rfl) ⟨65985989, by rfl⟩ : syracuseStep 87981319 = 131971979) B131971979
theorem B117308425 : Blo 2257435 117308425 := bstep (se 2 (by rfl) ⟨43990659, by rfl⟩ : syracuseStep 117308425 = 87981319) B87981319
theorem B156411233 : Blo 2257435 156411233 := bstep (se 2 (by rfl) ⟨58654212, by rfl⟩ : syracuseStep 156411233 = 117308425) B117308425
theorem B104274155 : Blo 2257435 104274155 := bstep (se 1 (by rfl) ⟨78205616, by rfl⟩ : syracuseStep 104274155 = 156411233) B156411233
theorem B69516103 : Blo 2257435 69516103 := bstep (se 1 (by rfl) ⟨52137077, by rfl⟩ : syracuseStep 69516103 = 104274155) B104274155
theorem B92688137 : Blo 2257435 92688137 := bstep (se 2 (by rfl) ⟨34758051, by rfl⟩ : syracuseStep 92688137 = 69516103) B69516103
theorem B61792091 : Blo 2257435 61792091 := bstep (se 1 (by rfl) ⟨46344068, by rfl⟩ : syracuseStep 61792091 = 92688137) B92688137
theorem B41194727 : Blo 2257435 41194727 := bstep (se 1 (by rfl) ⟨30896045, by rfl⟩ : syracuseStep 41194727 = 61792091) B61792091
theorem B27463151 : Blo 2257435 27463151 := bstep (se 1 (by rfl) ⟨20597363, by rfl⟩ : syracuseStep 27463151 = 41194727) B41194727
theorem B18308767 : Blo 2257435 18308767 := bstep (se 1 (by rfl) ⟨13731575, by rfl⟩ : syracuseStep 18308767 = 27463151) B27463151
theorem B24411689 : Blo 2257435 24411689 := bstep (se 2 (by rfl) ⟨9154383, by rfl⟩ : syracuseStep 24411689 = 18308767) B18308767
theorem B16274459 : Blo 2257435 16274459 := bstep (se 1 (by rfl) ⟨12205844, by rfl⟩ : syracuseStep 16274459 = 24411689) B24411689
theorem B10849639 : Blo 2257435 10849639 := bstep (se 1 (by rfl) ⟨8137229, by rfl⟩ : syracuseStep 10849639 = 16274459) B16274459
theorem B14466185 : Blo 2257435 14466185 := bstep (se 2 (by rfl) ⟨5424819, by rfl⟩ : syracuseStep 14466185 = 10849639) B10849639
theorem B9644123 : Blo 2257435 9644123 := bstep (se 1 (by rfl) ⟨7233092, by rfl⟩ : syracuseStep 9644123 = 14466185) B14466185
theorem B25717661 : Blo 2257435 25717661 := bstep (se 3 (by rfl) ⟨4822061, by rfl⟩ : syracuseStep 25717661 = 9644123) B9644123
theorem B17145107 : Blo 2257435 17145107 := bstep (se 1 (by rfl) ⟨12858830, by rfl⟩ : syracuseStep 17145107 = 25717661) B25717661
theorem B11430071 : Blo 2257435 11430071 := bstep (se 1 (by rfl) ⟨8572553, by rfl⟩ : syracuseStep 11430071 = 17145107) B17145107
theorem B7620047 : Blo 2257435 7620047 := bstep (se 1 (by rfl) ⟨5715035, by rfl⟩ : syracuseStep 7620047 = 11430071) B11430071
theorem B5080031 : Blo 2257435 5080031 := bstep (se 1 (by rfl) ⟨3810023, by rfl⟩ : syracuseStep 5080031 = 7620047) B7620047
theorem B3386687 : Blo 2257435 3386687 := bstep (se 1 (by rfl) ⟨2540015, by rfl⟩ : syracuseStep 3386687 = 5080031) B5080031
theorem B2257791 : Blo 2257435 2257791 := bstep (se 1 (by rfl) ⟨1693343, by rfl⟩ : syracuseStep 2257791 = 3386687) B3386687
theorem B3386693 : Blo 2257435 3386693 := bbase (se 4 (by rfl) ⟨317502, by rfl⟩ : syracuseStep 3386693 = 635005) (by norm_num)
theorem B2257795 : Blo 2257435 2257795 := bstep (se 1 (by rfl) ⟨1693346, by rfl⟩ : syracuseStep 2257795 = 3386693) B3386693
theorem B3810037 : Blo 2257435 3810037 := bbase (se 5 (by rfl) ⟨178595, by rfl⟩ : syracuseStep 3810037 = 357191) (by norm_num)
theorem B5080049 : Blo 2257435 5080049 := bstep (se 2 (by rfl) ⟨1905018, by rfl⟩ : syracuseStep 5080049 = 3810037) B3810037
theorem B3386699 : Blo 2257435 3386699 := bstep (se 1 (by rfl) ⟨2540024, by rfl⟩ : syracuseStep 3386699 = 5080049) B5080049
theorem B2257799 : Blo 2257435 2257799 := bstep (se 1 (by rfl) ⟨1693349, by rfl⟩ : syracuseStep 2257799 = 3386699) B3386699
theorem B2540029 : Blo 2257435 2540029 := bbase (se 3 (by rfl) ⟨476255, by rfl⟩ : syracuseStep 2540029 = 952511) (by norm_num)
theorem B3386705 : Blo 2257435 3386705 := bstep (se 2 (by rfl) ⟨1270014, by rfl⟩ : syracuseStep 3386705 = 2540029) B2540029
theorem B2257803 : Blo 2257435 2257803 := bstep (se 1 (by rfl) ⟨1693352, by rfl⟩ : syracuseStep 2257803 = 3386705) B3386705
theorem B7620101 : Blo 2257435 7620101 := bbase (se 4 (by rfl) ⟨714384, by rfl⟩ : syracuseStep 7620101 = 1428769) (by norm_num)
theorem B5080067 : Blo 2257435 5080067 := bstep (se 1 (by rfl) ⟨3810050, by rfl⟩ : syracuseStep 5080067 = 7620101) B7620101
theorem B3386711 : Blo 2257435 3386711 := bstep (se 1 (by rfl) ⟨2540033, by rfl⟩ : syracuseStep 3386711 = 5080067) B5080067
theorem B2257807 : Blo 2257435 2257807 := bstep (se 1 (by rfl) ⟨1693355, by rfl⟩ : syracuseStep 2257807 = 3386711) B3386711
theorem B3386717 : Blo 2257435 3386717 := bbase (se 3 (by rfl) ⟨635009, by rfl⟩ : syracuseStep 3386717 = 1270019) (by norm_num)
theorem B2257811 : Blo 2257435 2257811 := bstep (se 1 (by rfl) ⟨1693358, by rfl⟩ : syracuseStep 2257811 = 3386717) B3386717
theorem B5080085 : Blo 2257435 5080085 := bbase (se 6 (by rfl) ⟨119064, by rfl⟩ : syracuseStep 5080085 = 238129) (by norm_num)
theorem B3386723 : Blo 2257435 3386723 := bstep (se 1 (by rfl) ⟨2540042, by rfl⟩ : syracuseStep 3386723 = 5080085) B5080085
theorem B2257815 : Blo 2257435 2257815 := bstep (se 1 (by rfl) ⟨1693361, by rfl⟩ : syracuseStep 2257815 = 3386723) B3386723
theorem B8572661 : Blo 2257435 8572661 := bbase (se 5 (by rfl) ⟨401843, by rfl⟩ : syracuseStep 8572661 = 803687) (by norm_num)
theorem B5715107 : Blo 2257435 5715107 := bstep (se 1 (by rfl) ⟨4286330, by rfl⟩ : syracuseStep 5715107 = 8572661) B8572661
theorem B3810071 : Blo 2257435 3810071 := bstep (se 1 (by rfl) ⟨2857553, by rfl⟩ : syracuseStep 3810071 = 5715107) B5715107
theorem B2540047 : Blo 2257435 2540047 := bstep (se 1 (by rfl) ⟨1905035, by rfl⟩ : syracuseStep 2540047 = 3810071) B3810071
theorem B3386729 : Blo 2257435 3386729 := bstep (se 2 (by rfl) ⟨1270023, by rfl⟩ : syracuseStep 3386729 = 2540047) B2540047
theorem B2257819 : Blo 2257435 2257819 := bstep (se 1 (by rfl) ⟨1693364, by rfl⟩ : syracuseStep 2257819 = 3386729) B3386729
theorem B2411065 : Blo 2257435 2411065 := bbase (se 2 (by rfl) ⟨904149, by rfl⟩ : syracuseStep 2411065 = 1808299) (by norm_num)
theorem B12859013 : Blo 2257435 12859013 := bstep (se 4 (by rfl) ⟨1205532, by rfl⟩ : syracuseStep 12859013 = 2411065) B2411065
theorem B8572675 : Blo 2257435 8572675 := bstep (se 1 (by rfl) ⟨6429506, by rfl⟩ : syracuseStep 8572675 = 12859013) B12859013
theorem B11430233 : Blo 2257435 11430233 := bstep (se 2 (by rfl) ⟨4286337, by rfl⟩ : syracuseStep 11430233 = 8572675) B8572675
theorem B7620155 : Blo 2257435 7620155 := bstep (se 1 (by rfl) ⟨5715116, by rfl⟩ : syracuseStep 7620155 = 11430233) B11430233
theorem B5080103 : Blo 2257435 5080103 := bstep (se 1 (by rfl) ⟨3810077, by rfl⟩ : syracuseStep 5080103 = 7620155) B7620155
theorem B3386735 : Blo 2257435 3386735 := bstep (se 1 (by rfl) ⟨2540051, by rfl⟩ : syracuseStep 3386735 = 5080103) B5080103
theorem B2257823 : Blo 2257435 2257823 := bstep (se 1 (by rfl) ⟨1693367, by rfl⟩ : syracuseStep 2257823 = 3386735) B3386735
theorem B3386741 : Blo 2257435 3386741 := bbase (se 5 (by rfl) ⟨158753, by rfl⟩ : syracuseStep 3386741 = 317507) (by norm_num)
theorem B2257827 : Blo 2257435 2257827 := bstep (se 1 (by rfl) ⟨1693370, by rfl⟩ : syracuseStep 2257827 = 3386741) B3386741
theorem B3214765 : Blo 2257435 3214765 := bbase (se 3 (by rfl) ⟨602768, by rfl⟩ : syracuseStep 3214765 = 1205537) (by norm_num)
theorem B4286353 : Blo 2257435 4286353 := bstep (se 2 (by rfl) ⟨1607382, by rfl⟩ : syracuseStep 4286353 = 3214765) B3214765
theorem B5715137 : Blo 2257435 5715137 := bstep (se 2 (by rfl) ⟨2143176, by rfl⟩ : syracuseStep 5715137 = 4286353) B4286353
theorem B3810091 : Blo 2257435 3810091 := bstep (se 1 (by rfl) ⟨2857568, by rfl⟩ : syracuseStep 3810091 = 5715137) B5715137
theorem B5080121 : Blo 2257435 5080121 := bstep (se 2 (by rfl) ⟨1905045, by rfl⟩ : syracuseStep 5080121 = 3810091) B3810091
theorem B3386747 : Blo 2257435 3386747 := bstep (se 1 (by rfl) ⟨2540060, by rfl⟩ : syracuseStep 3386747 = 5080121) B5080121
theorem B2257831 : Blo 2257435 2257831 := bstep (se 1 (by rfl) ⟨1693373, by rfl⟩ : syracuseStep 2257831 = 3386747) B3386747
theorem B2540065 : Blo 2257435 2540065 := bbase (se 2 (by rfl) ⟨952524, by rfl⟩ : syracuseStep 2540065 = 1905049) (by norm_num)
theorem B3386753 : Blo 2257435 3386753 := bstep (se 2 (by rfl) ⟨1270032, by rfl⟩ : syracuseStep 3386753 = 2540065) B2540065
theorem B2257835 : Blo 2257435 2257835 := bstep (se 1 (by rfl) ⟨1693376, by rfl⟩ : syracuseStep 2257835 = 3386753) B3386753
theorem B5715157 : Blo 2257435 5715157 := bbase (se 7 (by rfl) ⟨66974, by rfl⟩ : syracuseStep 5715157 = 133949) (by norm_num)
theorem B7620209 : Blo 2257435 7620209 := bstep (se 2 (by rfl) ⟨2857578, by rfl⟩ : syracuseStep 7620209 = 5715157) B5715157
theorem B5080139 : Blo 2257435 5080139 := bstep (se 1 (by rfl) ⟨3810104, by rfl⟩ : syracuseStep 5080139 = 7620209) B7620209
theorem B3386759 : Blo 2257435 3386759 := bstep (se 1 (by rfl) ⟨2540069, by rfl⟩ : syracuseStep 3386759 = 5080139) B5080139
theorem B2257839 : Blo 2257435 2257839 := bstep (se 1 (by rfl) ⟨1693379, by rfl⟩ : syracuseStep 2257839 = 3386759) B3386759
theorem B3386765 : Blo 2257435 3386765 := bbase (se 3 (by rfl) ⟨635018, by rfl⟩ : syracuseStep 3386765 = 1270037) (by norm_num)
theorem B2257843 : Blo 2257435 2257843 := bstep (se 1 (by rfl) ⟨1693382, by rfl⟩ : syracuseStep 2257843 = 3386765) B3386765
theorem B5080157 : Blo 2257435 5080157 := bbase (se 3 (by rfl) ⟨952529, by rfl⟩ : syracuseStep 5080157 = 1905059) (by norm_num)
theorem B3386771 : Blo 2257435 3386771 := bstep (se 1 (by rfl) ⟨2540078, by rfl⟩ : syracuseStep 3386771 = 5080157) B5080157
theorem B2257847 : Blo 2257435 2257847 := bstep (se 1 (by rfl) ⟨1693385, by rfl⟩ : syracuseStep 2257847 = 3386771) B3386771
theorem B3810125 : Blo 2257435 3810125 := bbase (se 3 (by rfl) ⟨714398, by rfl⟩ : syracuseStep 3810125 = 1428797) (by norm_num)
theorem B2540083 : Blo 2257435 2540083 := bstep (se 1 (by rfl) ⟨1905062, by rfl⟩ : syracuseStep 2540083 = 3810125) B3810125
theorem B3386777 : Blo 2257435 3386777 := bstep (se 2 (by rfl) ⟨1270041, by rfl⟩ : syracuseStep 3386777 = 2540083) B2540083
theorem B2257851 : Blo 2257435 2257851 := bstep (se 1 (by rfl) ⟨1693388, by rfl⟩ : syracuseStep 2257851 = 3386777) B3386777
theorem B21699893 : Blo 2257435 21699893 := bbase (se 5 (by rfl) ⟨1017182, by rfl⟩ : syracuseStep 21699893 = 2034365) (by norm_num)
theorem B14466595 : Blo 2257435 14466595 := bstep (se 1 (by rfl) ⟨10849946, by rfl⟩ : syracuseStep 14466595 = 21699893) B21699893
theorem B19288793 : Blo 2257435 19288793 := bstep (se 2 (by rfl) ⟨7233297, by rfl⟩ : syracuseStep 19288793 = 14466595) B14466595
theorem B12859195 : Blo 2257435 12859195 := bstep (se 1 (by rfl) ⟨9644396, by rfl⟩ : syracuseStep 12859195 = 19288793) B19288793
theorem B17145593 : Blo 2257435 17145593 := bstep (se 2 (by rfl) ⟨6429597, by rfl⟩ : syracuseStep 17145593 = 12859195) B12859195
theorem B11430395 : Blo 2257435 11430395 := bstep (se 1 (by rfl) ⟨8572796, by rfl⟩ : syracuseStep 11430395 = 17145593) B17145593
theorem B7620263 : Blo 2257435 7620263 := bstep (se 1 (by rfl) ⟨5715197, by rfl⟩ : syracuseStep 7620263 = 11430395) B11430395
theorem B5080175 : Blo 2257435 5080175 := bstep (se 1 (by rfl) ⟨3810131, by rfl⟩ : syracuseStep 5080175 = 7620263) B7620263
theorem B3386783 : Blo 2257435 3386783 := bstep (se 1 (by rfl) ⟨2540087, by rfl⟩ : syracuseStep 3386783 = 5080175) B5080175
theorem B2257855 : Blo 2257435 2257855 := bstep (se 1 (by rfl) ⟨1693391, by rfl⟩ : syracuseStep 2257855 = 3386783) B3386783
theorem B3386789 : Blo 2257435 3386789 := bbase (se 4 (by rfl) ⟨317511, by rfl⟩ : syracuseStep 3386789 = 635023) (by norm_num)
theorem B2257859 : Blo 2257435 2257859 := bstep (se 1 (by rfl) ⟨1693394, by rfl⟩ : syracuseStep 2257859 = 3386789) B3386789
theorem B2857609 : Blo 2257435 2857609 := bbase (se 2 (by rfl) ⟨1071603, by rfl⟩ : syracuseStep 2857609 = 2143207) (by norm_num)
theorem B3810145 : Blo 2257435 3810145 := bstep (se 2 (by rfl) ⟨1428804, by rfl⟩ : syracuseStep 3810145 = 2857609) B2857609
theorem B5080193 : Blo 2257435 5080193 := bstep (se 2 (by rfl) ⟨1905072, by rfl⟩ : syracuseStep 5080193 = 3810145) B3810145
theorem B3386795 : Blo 2257435 3386795 := bstep (se 1 (by rfl) ⟨2540096, by rfl⟩ : syracuseStep 3386795 = 5080193) B5080193
theorem B2257863 : Blo 2257435 2257863 := bstep (se 1 (by rfl) ⟨1693397, by rfl⟩ : syracuseStep 2257863 = 3386795) B3386795
theorem B2540101 : Blo 2257435 2540101 := bbase (se 4 (by rfl) ⟨238134, by rfl⟩ : syracuseStep 2540101 = 476269) (by norm_num)
theorem B3386801 : Blo 2257435 3386801 := bstep (se 2 (by rfl) ⟨1270050, by rfl⟩ : syracuseStep 3386801 = 2540101) B2540101
theorem B2257867 : Blo 2257435 2257867 := bstep (se 1 (by rfl) ⟨1693400, by rfl⟩ : syracuseStep 2257867 = 3386801) B3386801
theorem B4286429 : Blo 2257435 4286429 := bbase (se 3 (by rfl) ⟨803705, by rfl⟩ : syracuseStep 4286429 = 1607411) (by norm_num)
theorem B2857619 : Blo 2257435 2857619 := bstep (se 1 (by rfl) ⟨2143214, by rfl⟩ : syracuseStep 2857619 = 4286429) B4286429
theorem B7620317 : Blo 2257435 7620317 := bstep (se 3 (by rfl) ⟨1428809, by rfl⟩ : syracuseStep 7620317 = 2857619) B2857619
theorem B5080211 : Blo 2257435 5080211 := bstep (se 1 (by rfl) ⟨3810158, by rfl⟩ : syracuseStep 5080211 = 7620317) B7620317
theorem B3386807 : Blo 2257435 3386807 := bstep (se 1 (by rfl) ⟨2540105, by rfl⟩ : syracuseStep 3386807 = 5080211) B5080211
theorem B2257871 : Blo 2257435 2257871 := bstep (se 1 (by rfl) ⟨1693403, by rfl⟩ : syracuseStep 2257871 = 3386807) B3386807
theorem B3386813 : Blo 2257435 3386813 := bbase (se 3 (by rfl) ⟨635027, by rfl⟩ : syracuseStep 3386813 = 1270055) (by norm_num)
theorem B2257875 : Blo 2257435 2257875 := bstep (se 1 (by rfl) ⟨1693406, by rfl⟩ : syracuseStep 2257875 = 3386813) B3386813
theorem B5080229 : Blo 2257435 5080229 := bbase (se 4 (by rfl) ⟨476271, by rfl⟩ : syracuseStep 5080229 = 952543) (by norm_num)
theorem B3386819 : Blo 2257435 3386819 := bstep (se 1 (by rfl) ⟨2540114, by rfl⟩ : syracuseStep 3386819 = 5080229) B5080229
theorem B2257879 : Blo 2257435 2257879 := bstep (se 1 (by rfl) ⟨1693409, by rfl⟩ : syracuseStep 2257879 = 3386819) B3386819
theorem B5715269 : Blo 2257435 5715269 := bbase (se 4 (by rfl) ⟨535806, by rfl⟩ : syracuseStep 5715269 = 1071613) (by norm_num)
theorem B3810179 : Blo 2257435 3810179 := bstep (se 1 (by rfl) ⟨2857634, by rfl⟩ : syracuseStep 3810179 = 5715269) B5715269
theorem B2540119 : Blo 2257435 2540119 := bstep (se 1 (by rfl) ⟨1905089, by rfl⟩ : syracuseStep 2540119 = 3810179) B3810179
theorem B3386825 : Blo 2257435 3386825 := bstep (se 2 (by rfl) ⟨1270059, by rfl⟩ : syracuseStep 3386825 = 2540119) B2540119
theorem B2257883 : Blo 2257435 2257883 := bstep (se 1 (by rfl) ⟨1693412, by rfl⟩ : syracuseStep 2257883 = 3386825) B3386825
theorem B11744597 : Blo 2257435 11744597 := bbase (se 13 (by rfl) ⟨2150, by rfl⟩ : syracuseStep 11744597 = 4301) (by norm_num)
theorem B7829731 : Blo 2257435 7829731 := bstep (se 1 (by rfl) ⟨5872298, by rfl⟩ : syracuseStep 7829731 = 11744597) B11744597
theorem B10439641 : Blo 2257435 10439641 := bstep (se 2 (by rfl) ⟨3914865, by rfl⟩ : syracuseStep 10439641 = 7829731) B7829731
theorem B13919521 : Blo 2257435 13919521 := bstep (se 2 (by rfl) ⟨5219820, by rfl⟩ : syracuseStep 13919521 = 10439641) B10439641
theorem B18559361 : Blo 2257435 18559361 := bstep (se 2 (by rfl) ⟨6959760, by rfl⟩ : syracuseStep 18559361 = 13919521) B13919521
theorem B12372907 : Blo 2257435 12372907 := bstep (se 1 (by rfl) ⟨9279680, by rfl⟩ : syracuseStep 12372907 = 18559361) B18559361
theorem B16497209 : Blo 2257435 16497209 := bstep (se 2 (by rfl) ⟨6186453, by rfl⟩ : syracuseStep 16497209 = 12372907) B12372907
theorem B10998139 : Blo 2257435 10998139 := bstep (se 1 (by rfl) ⟨8248604, by rfl⟩ : syracuseStep 10998139 = 16497209) B16497209
theorem B14664185 : Blo 2257435 14664185 := bstep (se 2 (by rfl) ⟨5499069, by rfl⟩ : syracuseStep 14664185 = 10998139) B10998139
theorem B9776123 : Blo 2257435 9776123 := bstep (se 1 (by rfl) ⟨7332092, by rfl⟩ : syracuseStep 9776123 = 14664185) B14664185
theorem B6517415 : Blo 2257435 6517415 := bstep (se 1 (by rfl) ⟨4888061, by rfl⟩ : syracuseStep 6517415 = 9776123) B9776123
theorem B4344943 : Blo 2257435 4344943 := bstep (se 1 (by rfl) ⟨3258707, by rfl⟩ : syracuseStep 4344943 = 6517415) B6517415
theorem B5793257 : Blo 2257435 5793257 := bstep (se 2 (by rfl) ⟨2172471, by rfl⟩ : syracuseStep 5793257 = 4344943) B4344943
theorem B3862171 : Blo 2257435 3862171 := bstep (se 1 (by rfl) ⟨2896628, by rfl⟩ : syracuseStep 3862171 = 5793257) B5793257
theorem B20598245 : Blo 2257435 20598245 := bstep (se 4 (by rfl) ⟨1931085, by rfl⟩ : syracuseStep 20598245 = 3862171) B3862171
theorem B13732163 : Blo 2257435 13732163 := bstep (se 1 (by rfl) ⟨10299122, by rfl⟩ : syracuseStep 13732163 = 20598245) B20598245
theorem B9154775 : Blo 2257435 9154775 := bstep (se 1 (by rfl) ⟨6866081, by rfl⟩ : syracuseStep 9154775 = 13732163) B13732163
theorem B6103183 : Blo 2257435 6103183 := bstep (se 1 (by rfl) ⟨4577387, by rfl⟩ : syracuseStep 6103183 = 9154775) B9154775
theorem B8137577 : Blo 2257435 8137577 := bstep (se 2 (by rfl) ⟨3051591, by rfl⟩ : syracuseStep 8137577 = 6103183) B6103183
theorem B5425051 : Blo 2257435 5425051 := bstep (se 1 (by rfl) ⟨4068788, by rfl⟩ : syracuseStep 5425051 = 8137577) B8137577
theorem B7233401 : Blo 2257435 7233401 := bstep (se 2 (by rfl) ⟨2712525, by rfl⟩ : syracuseStep 7233401 = 5425051) B5425051
theorem B4822267 : Blo 2257435 4822267 := bstep (se 1 (by rfl) ⟨3616700, by rfl⟩ : syracuseStep 4822267 = 7233401) B7233401
theorem B6429689 : Blo 2257435 6429689 := bstep (se 2 (by rfl) ⟨2411133, by rfl⟩ : syracuseStep 6429689 = 4822267) B4822267
theorem B4286459 : Blo 2257435 4286459 := bstep (se 1 (by rfl) ⟨3214844, by rfl⟩ : syracuseStep 4286459 = 6429689) B6429689
theorem B11430557 : Blo 2257435 11430557 := bstep (se 3 (by rfl) ⟨2143229, by rfl⟩ : syracuseStep 11430557 = 4286459) B4286459
theorem B7620371 : Blo 2257435 7620371 := bstep (se 1 (by rfl) ⟨5715278, by rfl⟩ : syracuseStep 7620371 = 11430557) B11430557
theorem B5080247 : Blo 2257435 5080247 := bstep (se 1 (by rfl) ⟨3810185, by rfl⟩ : syracuseStep 5080247 = 7620371) B7620371
theorem B3386831 : Blo 2257435 3386831 := bstep (se 1 (by rfl) ⟨2540123, by rfl⟩ : syracuseStep 3386831 = 5080247) B5080247
theorem B2257887 : Blo 2257435 2257887 := bstep (se 1 (by rfl) ⟨1693415, by rfl⟩ : syracuseStep 2257887 = 3386831) B3386831
theorem B3386837 : Blo 2257435 3386837 := bbase (se 7 (by rfl) ⟨39689, by rfl⟩ : syracuseStep 3386837 = 79379) (by norm_num)
theorem B2257891 : Blo 2257435 2257891 := bstep (se 1 (by rfl) ⟨1693418, by rfl⟩ : syracuseStep 2257891 = 3386837) B3386837
theorem B8572949 : Blo 2257435 8572949 := bbase (se 6 (by rfl) ⟨200928, by rfl⟩ : syracuseStep 8572949 = 401857) (by norm_num)
theorem B5715299 : Blo 2257435 5715299 := bstep (se 1 (by rfl) ⟨4286474, by rfl⟩ : syracuseStep 5715299 = 8572949) B8572949
theorem B3810199 : Blo 2257435 3810199 := bstep (se 1 (by rfl) ⟨2857649, by rfl⟩ : syracuseStep 3810199 = 5715299) B5715299
theorem B5080265 : Blo 2257435 5080265 := bstep (se 2 (by rfl) ⟨1905099, by rfl⟩ : syracuseStep 5080265 = 3810199) B3810199
theorem B3386843 : Blo 2257435 3386843 := bstep (se 1 (by rfl) ⟨2540132, by rfl⟩ : syracuseStep 3386843 = 5080265) B5080265
theorem B2257895 : Blo 2257435 2257895 := bstep (se 1 (by rfl) ⟨1693421, by rfl⟩ : syracuseStep 2257895 = 3386843) B3386843
theorem B2540137 : Blo 2257435 2540137 := bbase (se 2 (by rfl) ⟨952551, by rfl⟩ : syracuseStep 2540137 = 1905103) (by norm_num)
theorem B3386849 : Blo 2257435 3386849 := bstep (se 2 (by rfl) ⟨1270068, by rfl⟩ : syracuseStep 3386849 = 2540137) B2540137
theorem B2257899 : Blo 2257435 2257899 := bstep (se 1 (by rfl) ⟨1693424, by rfl⟩ : syracuseStep 2257899 = 3386849) B3386849
theorem B4822301 : Blo 2257435 4822301 := bbase (se 3 (by rfl) ⟨904181, by rfl⟩ : syracuseStep 4822301 = 1808363) (by norm_num)
theorem B12859469 : Blo 2257435 12859469 := bstep (se 3 (by rfl) ⟨2411150, by rfl⟩ : syracuseStep 12859469 = 4822301) B4822301
theorem B8572979 : Blo 2257435 8572979 := bstep (se 1 (by rfl) ⟨6429734, by rfl⟩ : syracuseStep 8572979 = 12859469) B12859469
theorem B5715319 : Blo 2257435 5715319 := bstep (se 1 (by rfl) ⟨4286489, by rfl⟩ : syracuseStep 5715319 = 8572979) B8572979
theorem B7620425 : Blo 2257435 7620425 := bstep (se 2 (by rfl) ⟨2857659, by rfl⟩ : syracuseStep 7620425 = 5715319) B5715319
theorem B5080283 : Blo 2257435 5080283 := bstep (se 1 (by rfl) ⟨3810212, by rfl⟩ : syracuseStep 5080283 = 7620425) B7620425
theorem B3386855 : Blo 2257435 3386855 := bstep (se 1 (by rfl) ⟨2540141, by rfl⟩ : syracuseStep 3386855 = 5080283) B5080283
theorem B2257903 : Blo 2257435 2257903 := bstep (se 1 (by rfl) ⟨1693427, by rfl⟩ : syracuseStep 2257903 = 3386855) B3386855
theorem B3386861 : Blo 2257435 3386861 := bbase (se 3 (by rfl) ⟨635036, by rfl⟩ : syracuseStep 3386861 = 1270073) (by norm_num)
theorem B2257907 : Blo 2257435 2257907 := bstep (se 1 (by rfl) ⟨1693430, by rfl⟩ : syracuseStep 2257907 = 3386861) B3386861
theorem B5080301 : Blo 2257435 5080301 := bbase (se 3 (by rfl) ⟨952556, by rfl⟩ : syracuseStep 5080301 = 1905113) (by norm_num)
theorem B3386867 : Blo 2257435 3386867 := bstep (se 1 (by rfl) ⟨2540150, by rfl⟩ : syracuseStep 3386867 = 5080301) B5080301
theorem B2257911 : Blo 2257435 2257911 := bstep (se 1 (by rfl) ⟨1693433, by rfl⟩ : syracuseStep 2257911 = 3386867) B3386867
theorem B3214885 : Blo 2257435 3214885 := bbase (se 4 (by rfl) ⟨301395, by rfl⟩ : syracuseStep 3214885 = 602791) (by norm_num)
theorem B4286513 : Blo 2257435 4286513 := bstep (se 2 (by rfl) ⟨1607442, by rfl⟩ : syracuseStep 4286513 = 3214885) B3214885
theorem B2857675 : Blo 2257435 2857675 := bstep (se 1 (by rfl) ⟨2143256, by rfl⟩ : syracuseStep 2857675 = 4286513) B4286513
theorem B3810233 : Blo 2257435 3810233 := bstep (se 2 (by rfl) ⟨1428837, by rfl⟩ : syracuseStep 3810233 = 2857675) B2857675
theorem B2540155 : Blo 2257435 2540155 := bstep (se 1 (by rfl) ⟨1905116, by rfl⟩ : syracuseStep 2540155 = 3810233) B3810233
theorem B3386873 : Blo 2257435 3386873 := bstep (se 2 (by rfl) ⟨1270077, by rfl⟩ : syracuseStep 3386873 = 2540155) B2540155
theorem B2257915 : Blo 2257435 2257915 := bstep (se 1 (by rfl) ⟨1693436, by rfl⟩ : syracuseStep 2257915 = 3386873) B3386873
theorem B8690005 : Blo 2257435 8690005 := bbase (se 10 (by rfl) ⟨12729, by rfl⟩ : syracuseStep 8690005 = 25459) (by norm_num)
theorem B11586673 : Blo 2257435 11586673 := bstep (se 2 (by rfl) ⟨4345002, by rfl⟩ : syracuseStep 11586673 = 8690005) B8690005
theorem B15448897 : Blo 2257435 15448897 := bstep (se 2 (by rfl) ⟨5793336, by rfl⟩ : syracuseStep 15448897 = 11586673) B11586673
theorem B82394117 : Blo 2257435 82394117 := bstep (se 4 (by rfl) ⟨7724448, by rfl⟩ : syracuseStep 82394117 = 15448897) B15448897
theorem B54929411 : Blo 2257435 54929411 := bstep (se 1 (by rfl) ⟨41197058, by rfl⟩ : syracuseStep 54929411 = 82394117) B82394117
theorem B36619607 : Blo 2257435 36619607 := bstep (se 1 (by rfl) ⟨27464705, by rfl⟩ : syracuseStep 36619607 = 54929411) B54929411
theorem B24413071 : Blo 2257435 24413071 := bstep (se 1 (by rfl) ⟨18309803, by rfl⟩ : syracuseStep 24413071 = 36619607) B36619607
theorem B32550761 : Blo 2257435 32550761 := bstep (se 2 (by rfl) ⟨12206535, by rfl⟩ : syracuseStep 32550761 = 24413071) B24413071
theorem B86802029 : Blo 2257435 86802029 := bstep (se 3 (by rfl) ⟨16275380, by rfl⟩ : syracuseStep 86802029 = 32550761) B32550761
theorem B57868019 : Blo 2257435 57868019 := bstep (se 1 (by rfl) ⟨43401014, by rfl⟩ : syracuseStep 57868019 = 86802029) B86802029
theorem B38578679 : Blo 2257435 38578679 := bstep (se 1 (by rfl) ⟨28934009, by rfl⟩ : syracuseStep 38578679 = 57868019) B57868019
theorem B25719119 : Blo 2257435 25719119 := bstep (se 1 (by rfl) ⟨19289339, by rfl⟩ : syracuseStep 25719119 = 38578679) B38578679
theorem B17146079 : Blo 2257435 17146079 := bstep (se 1 (by rfl) ⟨12859559, by rfl⟩ : syracuseStep 17146079 = 25719119) B25719119
theorem B11430719 : Blo 2257435 11430719 := bstep (se 1 (by rfl) ⟨8573039, by rfl⟩ : syracuseStep 11430719 = 17146079) B17146079
theorem B7620479 : Blo 2257435 7620479 := bstep (se 1 (by rfl) ⟨5715359, by rfl⟩ : syracuseStep 7620479 = 11430719) B11430719
theorem B5080319 : Blo 2257435 5080319 := bstep (se 1 (by rfl) ⟨3810239, by rfl⟩ : syracuseStep 5080319 = 7620479) B7620479
theorem B3386879 : Blo 2257435 3386879 := bstep (se 1 (by rfl) ⟨2540159, by rfl⟩ : syracuseStep 3386879 = 5080319) B5080319
theorem B2257919 : Blo 2257435 2257919 := bstep (se 1 (by rfl) ⟨1693439, by rfl⟩ : syracuseStep 2257919 = 3386879) B3386879
theorem B3386885 : Blo 2257435 3386885 := bbase (se 4 (by rfl) ⟨317520, by rfl⟩ : syracuseStep 3386885 = 635041) (by norm_num)
theorem B2257923 : Blo 2257435 2257923 := bstep (se 1 (by rfl) ⟨1693442, by rfl⟩ : syracuseStep 2257923 = 3386885) B3386885
theorem B3810253 : Blo 2257435 3810253 := bbase (se 3 (by rfl) ⟨714422, by rfl⟩ : syracuseStep 3810253 = 1428845) (by norm_num)
theorem B5080337 : Blo 2257435 5080337 := bstep (se 2 (by rfl) ⟨1905126, by rfl⟩ : syracuseStep 5080337 = 3810253) B3810253
theorem B3386891 : Blo 2257435 3386891 := bstep (se 1 (by rfl) ⟨2540168, by rfl⟩ : syracuseStep 3386891 = 5080337) B5080337
theorem B2257927 : Blo 2257435 2257927 := bstep (se 1 (by rfl) ⟨1693445, by rfl⟩ : syracuseStep 2257927 = 3386891) B3386891
theorem B2540173 : Blo 2257435 2540173 := bbase (se 3 (by rfl) ⟨476282, by rfl⟩ : syracuseStep 2540173 = 952565) (by norm_num)
theorem B3386897 : Blo 2257435 3386897 := bstep (se 2 (by rfl) ⟨1270086, by rfl⟩ : syracuseStep 3386897 = 2540173) B2540173
theorem B2257931 : Blo 2257435 2257931 := bstep (se 1 (by rfl) ⟨1693448, by rfl⟩ : syracuseStep 2257931 = 3386897) B3386897
theorem B7620533 : Blo 2257435 7620533 := bbase (se 5 (by rfl) ⟨357212, by rfl⟩ : syracuseStep 7620533 = 714425) (by norm_num)
theorem B5080355 : Blo 2257435 5080355 := bstep (se 1 (by rfl) ⟨3810266, by rfl⟩ : syracuseStep 5080355 = 7620533) B7620533
theorem B3386903 : Blo 2257435 3386903 := bstep (se 1 (by rfl) ⟨2540177, by rfl⟩ : syracuseStep 3386903 = 5080355) B5080355
theorem B2257935 : Blo 2257435 2257935 := bstep (se 1 (by rfl) ⟨1693451, by rfl⟩ : syracuseStep 2257935 = 3386903) B3386903
theorem B3386909 : Blo 2257435 3386909 := bbase (se 3 (by rfl) ⟨635045, by rfl⟩ : syracuseStep 3386909 = 1270091) (by norm_num)
theorem B2257939 : Blo 2257435 2257939 := bstep (se 1 (by rfl) ⟨1693454, by rfl⟩ : syracuseStep 2257939 = 3386909) B3386909
theorem B5080373 : Blo 2257435 5080373 := bbase (se 5 (by rfl) ⟨238142, by rfl⟩ : syracuseStep 5080373 = 476285) (by norm_num)
theorem B3386915 : Blo 2257435 3386915 := bstep (se 1 (by rfl) ⟨2540186, by rfl⟩ : syracuseStep 3386915 = 5080373) B5080373
theorem B2257943 : Blo 2257435 2257943 := bstep (se 1 (by rfl) ⟨1693457, by rfl⟩ : syracuseStep 2257943 = 3386915) B3386915
theorem B4577509 : Blo 2257435 4577509 := bbase (se 4 (by rfl) ⟨429141, by rfl⟩ : syracuseStep 4577509 = 858283) (by norm_num)
theorem B6103345 : Blo 2257435 6103345 := bstep (se 2 (by rfl) ⟨2288754, by rfl⟩ : syracuseStep 6103345 = 4577509) B4577509
theorem B8137793 : Blo 2257435 8137793 := bstep (se 2 (by rfl) ⟨3051672, by rfl⟩ : syracuseStep 8137793 = 6103345) B6103345
theorem B21700781 : Blo 2257435 21700781 := bstep (se 3 (by rfl) ⟨4068896, by rfl⟩ : syracuseStep 21700781 = 8137793) B8137793
theorem B14467187 : Blo 2257435 14467187 := bstep (se 1 (by rfl) ⟨10850390, by rfl⟩ : syracuseStep 14467187 = 21700781) B21700781
theorem B9644791 : Blo 2257435 9644791 := bstep (se 1 (by rfl) ⟨7233593, by rfl⟩ : syracuseStep 9644791 = 14467187) B14467187
theorem B12859721 : Blo 2257435 12859721 := bstep (se 2 (by rfl) ⟨4822395, by rfl⟩ : syracuseStep 12859721 = 9644791) B9644791
theorem B8573147 : Blo 2257435 8573147 := bstep (se 1 (by rfl) ⟨6429860, by rfl⟩ : syracuseStep 8573147 = 12859721) B12859721
theorem B5715431 : Blo 2257435 5715431 := bstep (se 1 (by rfl) ⟨4286573, by rfl⟩ : syracuseStep 5715431 = 8573147) B8573147
theorem B3810287 : Blo 2257435 3810287 := bstep (se 1 (by rfl) ⟨2857715, by rfl⟩ : syracuseStep 3810287 = 5715431) B5715431
theorem B2540191 : Blo 2257435 2540191 := bstep (se 1 (by rfl) ⟨1905143, by rfl⟩ : syracuseStep 2540191 = 3810287) B3810287
theorem B3386921 : Blo 2257435 3386921 := bstep (se 2 (by rfl) ⟨1270095, by rfl⟩ : syracuseStep 3386921 = 2540191) B2540191
theorem B2257947 : Blo 2257435 2257947 := bstep (se 1 (by rfl) ⟨1693460, by rfl⟩ : syracuseStep 2257947 = 3386921) B3386921
theorem B10299413 : Blo 2257435 10299413 := bbase (se 6 (by rfl) ⟨241392, by rfl⟩ : syracuseStep 10299413 = 482785) (by norm_num)
theorem B6866275 : Blo 2257435 6866275 := bstep (se 1 (by rfl) ⟨5149706, by rfl⟩ : syracuseStep 6866275 = 10299413) B10299413
theorem B9155033 : Blo 2257435 9155033 := bstep (se 2 (by rfl) ⟨3433137, by rfl⟩ : syracuseStep 9155033 = 6866275) B6866275
theorem B6103355 : Blo 2257435 6103355 := bstep (se 1 (by rfl) ⟨4577516, by rfl⟩ : syracuseStep 6103355 = 9155033) B9155033
theorem B16275613 : Blo 2257435 16275613 := bstep (se 3 (by rfl) ⟨3051677, by rfl⟩ : syracuseStep 16275613 = 6103355) B6103355
theorem B21700817 : Blo 2257435 21700817 := bstep (se 2 (by rfl) ⟨8137806, by rfl⟩ : syracuseStep 21700817 = 16275613) B16275613
theorem B14467211 : Blo 2257435 14467211 := bstep (se 1 (by rfl) ⟨10850408, by rfl⟩ : syracuseStep 14467211 = 21700817) B21700817
theorem B9644807 : Blo 2257435 9644807 := bstep (se 1 (by rfl) ⟨7233605, by rfl⟩ : syracuseStep 9644807 = 14467211) B14467211
theorem B6429871 : Blo 2257435 6429871 := bstep (se 1 (by rfl) ⟨4822403, by rfl⟩ : syracuseStep 6429871 = 9644807) B9644807
theorem B8573161 : Blo 2257435 8573161 := bstep (se 2 (by rfl) ⟨3214935, by rfl⟩ : syracuseStep 8573161 = 6429871) B6429871
theorem B11430881 : Blo 2257435 11430881 := bstep (se 2 (by rfl) ⟨4286580, by rfl⟩ : syracuseStep 11430881 = 8573161) B8573161
theorem B7620587 : Blo 2257435 7620587 := bstep (se 1 (by rfl) ⟨5715440, by rfl⟩ : syracuseStep 7620587 = 11430881) B11430881
theorem B5080391 : Blo 2257435 5080391 := bstep (se 1 (by rfl) ⟨3810293, by rfl⟩ : syracuseStep 5080391 = 7620587) B7620587
theorem B3386927 : Blo 2257435 3386927 := bstep (se 1 (by rfl) ⟨2540195, by rfl⟩ : syracuseStep 3386927 = 5080391) B5080391
theorem B2257951 : Blo 2257435 2257951 := bstep (se 1 (by rfl) ⟨1693463, by rfl⟩ : syracuseStep 2257951 = 3386927) B3386927
theorem B3386933 : Blo 2257435 3386933 := bbase (se 5 (by rfl) ⟨158762, by rfl⟩ : syracuseStep 3386933 = 317525) (by norm_num)
theorem B2257955 : Blo 2257435 2257955 := bstep (se 1 (by rfl) ⟨1693466, by rfl⟩ : syracuseStep 2257955 = 3386933) B3386933
theorem B5715461 : Blo 2257435 5715461 := bbase (se 4 (by rfl) ⟨535824, by rfl⟩ : syracuseStep 5715461 = 1071649) (by norm_num)
theorem B3810307 : Blo 2257435 3810307 := bstep (se 1 (by rfl) ⟨2857730, by rfl⟩ : syracuseStep 3810307 = 5715461) B5715461
theorem B5080409 : Blo 2257435 5080409 := bstep (se 2 (by rfl) ⟨1905153, by rfl⟩ : syracuseStep 5080409 = 3810307) B3810307
theorem B3386939 : Blo 2257435 3386939 := bstep (se 1 (by rfl) ⟨2540204, by rfl⟩ : syracuseStep 3386939 = 5080409) B5080409
theorem B2257959 : Blo 2257435 2257959 := bstep (se 1 (by rfl) ⟨1693469, by rfl⟩ : syracuseStep 2257959 = 3386939) B3386939
theorem B2540209 : Blo 2257435 2540209 := bbase (se 2 (by rfl) ⟨952578, by rfl⟩ : syracuseStep 2540209 = 1905157) (by norm_num)
theorem B3386945 : Blo 2257435 3386945 := bstep (se 2 (by rfl) ⟨1270104, by rfl⟩ : syracuseStep 3386945 = 2540209) B2540209
theorem B2257963 : Blo 2257435 2257963 := bstep (se 1 (by rfl) ⟨1693472, by rfl⟩ : syracuseStep 2257963 = 3386945) B3386945
theorem B3616829 : Blo 2257435 3616829 := bbase (se 3 (by rfl) ⟨678155, by rfl⟩ : syracuseStep 3616829 = 1356311) (by norm_num)
theorem B2411219 : Blo 2257435 2411219 := bstep (se 1 (by rfl) ⟨1808414, by rfl⟩ : syracuseStep 2411219 = 3616829) B3616829
theorem B6429917 : Blo 2257435 6429917 := bstep (se 3 (by rfl) ⟨1205609, by rfl⟩ : syracuseStep 6429917 = 2411219) B2411219
theorem B4286611 : Blo 2257435 4286611 := bstep (se 1 (by rfl) ⟨3214958, by rfl⟩ : syracuseStep 4286611 = 6429917) B6429917
theorem B5715481 : Blo 2257435 5715481 := bstep (se 2 (by rfl) ⟨2143305, by rfl⟩ : syracuseStep 5715481 = 4286611) B4286611
theorem B7620641 : Blo 2257435 7620641 := bstep (se 2 (by rfl) ⟨2857740, by rfl⟩ : syracuseStep 7620641 = 5715481) B5715481
theorem B5080427 : Blo 2257435 5080427 := bstep (se 1 (by rfl) ⟨3810320, by rfl⟩ : syracuseStep 5080427 = 7620641) B7620641
theorem B3386951 : Blo 2257435 3386951 := bstep (se 1 (by rfl) ⟨2540213, by rfl⟩ : syracuseStep 3386951 = 5080427) B5080427
theorem B2257967 : Blo 2257435 2257967 := bstep (se 1 (by rfl) ⟨1693475, by rfl⟩ : syracuseStep 2257967 = 3386951) B3386951
theorem B3386957 : Blo 2257435 3386957 := bbase (se 3 (by rfl) ⟨635054, by rfl⟩ : syracuseStep 3386957 = 1270109) (by norm_num)
theorem B2257971 : Blo 2257435 2257971 := bstep (se 1 (by rfl) ⟨1693478, by rfl⟩ : syracuseStep 2257971 = 3386957) B3386957
theorem B5080445 : Blo 2257435 5080445 := bbase (se 3 (by rfl) ⟨952583, by rfl⟩ : syracuseStep 5080445 = 1905167) (by norm_num)
theorem B3386963 : Blo 2257435 3386963 := bstep (se 1 (by rfl) ⟨2540222, by rfl⟩ : syracuseStep 3386963 = 5080445) B5080445
theorem B2257975 : Blo 2257435 2257975 := bstep (se 1 (by rfl) ⟨1693481, by rfl⟩ : syracuseStep 2257975 = 3386963) B3386963
theorem B3810341 : Blo 2257435 3810341 := bbase (se 4 (by rfl) ⟨357219, by rfl⟩ : syracuseStep 3810341 = 714439) (by norm_num)
theorem B2540227 : Blo 2257435 2540227 := bstep (se 1 (by rfl) ⟨1905170, by rfl⟩ : syracuseStep 2540227 = 3810341) B3810341
theorem B3386969 : Blo 2257435 3386969 := bstep (se 2 (by rfl) ⟨1270113, by rfl⟩ : syracuseStep 3386969 = 2540227) B2540227
theorem B2257979 : Blo 2257435 2257979 := bstep (se 1 (by rfl) ⟨1693484, by rfl⟩ : syracuseStep 2257979 = 3386969) B3386969
theorem B3214981 : Blo 2257435 3214981 := bbase (se 4 (by rfl) ⟨301404, by rfl⟩ : syracuseStep 3214981 = 602809) (by norm_num)
theorem B17146565 : Blo 2257435 17146565 := bstep (se 4 (by rfl) ⟨1607490, by rfl⟩ : syracuseStep 17146565 = 3214981) B3214981
theorem B11431043 : Blo 2257435 11431043 := bstep (se 1 (by rfl) ⟨8573282, by rfl⟩ : syracuseStep 11431043 = 17146565) B17146565
theorem B7620695 : Blo 2257435 7620695 := bstep (se 1 (by rfl) ⟨5715521, by rfl⟩ : syracuseStep 7620695 = 11431043) B11431043
theorem B5080463 : Blo 2257435 5080463 := bstep (se 1 (by rfl) ⟨3810347, by rfl⟩ : syracuseStep 5080463 = 7620695) B7620695
theorem B3386975 : Blo 2257435 3386975 := bstep (se 1 (by rfl) ⟨2540231, by rfl⟩ : syracuseStep 3386975 = 5080463) B5080463
theorem B2257983 : Blo 2257435 2257983 := bstep (se 1 (by rfl) ⟨1693487, by rfl⟩ : syracuseStep 2257983 = 3386975) B3386975
theorem B3386981 : Blo 2257435 3386981 := bbase (se 4 (by rfl) ⟨317529, by rfl⟩ : syracuseStep 3386981 = 635059) (by norm_num)
theorem B2257987 : Blo 2257435 2257987 := bstep (se 1 (by rfl) ⟨1693490, by rfl⟩ : syracuseStep 2257987 = 3386981) B3386981
theorem B2411245 : Blo 2257435 2411245 := bbase (se 3 (by rfl) ⟨452108, by rfl⟩ : syracuseStep 2411245 = 904217) (by norm_num)
theorem B3214993 : Blo 2257435 3214993 := bstep (se 2 (by rfl) ⟨1205622, by rfl⟩ : syracuseStep 3214993 = 2411245) B2411245
theorem B4286657 : Blo 2257435 4286657 := bstep (se 2 (by rfl) ⟨1607496, by rfl⟩ : syracuseStep 4286657 = 3214993) B3214993
theorem B2857771 : Blo 2257435 2857771 := bstep (se 1 (by rfl) ⟨2143328, by rfl⟩ : syracuseStep 2857771 = 4286657) B4286657
theorem B3810361 : Blo 2257435 3810361 := bstep (se 2 (by rfl) ⟨1428885, by rfl⟩ : syracuseStep 3810361 = 2857771) B2857771
theorem B5080481 : Blo 2257435 5080481 := bstep (se 2 (by rfl) ⟨1905180, by rfl⟩ : syracuseStep 5080481 = 3810361) B3810361
theorem B3386987 : Blo 2257435 3386987 := bstep (se 1 (by rfl) ⟨2540240, by rfl⟩ : syracuseStep 3386987 = 5080481) B5080481
theorem B2257991 : Blo 2257435 2257991 := bstep (se 1 (by rfl) ⟨1693493, by rfl⟩ : syracuseStep 2257991 = 3386987) B3386987
theorem B2540245 : Blo 2257435 2540245 := bbase (se 7 (by rfl) ⟨29768, by rfl⟩ : syracuseStep 2540245 = 59537) (by norm_num)
theorem B3386993 : Blo 2257435 3386993 := bstep (se 2 (by rfl) ⟨1270122, by rfl⟩ : syracuseStep 3386993 = 2540245) B2540245
theorem B2257995 : Blo 2257435 2257995 := bstep (se 1 (by rfl) ⟨1693496, by rfl⟩ : syracuseStep 2257995 = 3386993) B3386993
theorem B2857781 : Blo 2257435 2857781 := bbase (se 5 (by rfl) ⟨133958, by rfl⟩ : syracuseStep 2857781 = 267917) (by norm_num)
theorem B7620749 : Blo 2257435 7620749 := bstep (se 3 (by rfl) ⟨1428890, by rfl⟩ : syracuseStep 7620749 = 2857781) B2857781
theorem B5080499 : Blo 2257435 5080499 := bstep (se 1 (by rfl) ⟨3810374, by rfl⟩ : syracuseStep 5080499 = 7620749) B7620749
theorem B3386999 : Blo 2257435 3386999 := bstep (se 1 (by rfl) ⟨2540249, by rfl⟩ : syracuseStep 3386999 = 5080499) B5080499
theorem B2257999 : Blo 2257435 2257999 := bstep (se 1 (by rfl) ⟨1693499, by rfl⟩ : syracuseStep 2257999 = 3386999) B3386999
theorem B3387005 : Blo 2257435 3387005 := bbase (se 3 (by rfl) ⟨635063, by rfl⟩ : syracuseStep 3387005 = 1270127) (by norm_num)
theorem B2258003 : Blo 2257435 2258003 := bstep (se 1 (by rfl) ⟨1693502, by rfl⟩ : syracuseStep 2258003 = 3387005) B3387005
theorem B5080517 : Blo 2257435 5080517 := bbase (se 4 (by rfl) ⟨476298, by rfl⟩ : syracuseStep 5080517 = 952597) (by norm_num)
theorem B3387011 : Blo 2257435 3387011 := bstep (se 1 (by rfl) ⟨2540258, by rfl⟩ : syracuseStep 3387011 = 5080517) B5080517
theorem B2258007 : Blo 2257435 2258007 := bstep (se 1 (by rfl) ⟨1693505, by rfl⟩ : syracuseStep 2258007 = 3387011) B3387011
theorem B23490485 : Blo 2257435 23490485 := bbase (se 5 (by rfl) ⟨1101116, by rfl⟩ : syracuseStep 23490485 = 2202233) (by norm_num)
theorem B15660323 : Blo 2257435 15660323 := bstep (se 1 (by rfl) ⟨11745242, by rfl⟩ : syracuseStep 15660323 = 23490485) B23490485
theorem B10440215 : Blo 2257435 10440215 := bstep (se 1 (by rfl) ⟨7830161, by rfl⟩ : syracuseStep 10440215 = 15660323) B15660323
theorem B6960143 : Blo 2257435 6960143 := bstep (se 1 (by rfl) ⟨5220107, by rfl⟩ : syracuseStep 6960143 = 10440215) B10440215
theorem B4640095 : Blo 2257435 4640095 := bstep (se 1 (by rfl) ⟨3480071, by rfl⟩ : syracuseStep 4640095 = 6960143) B6960143
theorem B6186793 : Blo 2257435 6186793 := bstep (se 2 (by rfl) ⟨2320047, by rfl⟩ : syracuseStep 6186793 = 4640095) B4640095
theorem B8249057 : Blo 2257435 8249057 := bstep (se 2 (by rfl) ⟨3093396, by rfl⟩ : syracuseStep 8249057 = 6186793) B6186793
theorem B5499371 : Blo 2257435 5499371 := bstep (se 1 (by rfl) ⟨4124528, by rfl⟩ : syracuseStep 5499371 = 8249057) B8249057
theorem B14664989 : Blo 2257435 14664989 := bstep (se 3 (by rfl) ⟨2749685, by rfl⟩ : syracuseStep 14664989 = 5499371) B5499371
theorem B39106637 : Blo 2257435 39106637 := bstep (se 3 (by rfl) ⟨7332494, by rfl⟩ : syracuseStep 39106637 = 14664989) B14664989
theorem B26071091 : Blo 2257435 26071091 := bstep (se 1 (by rfl) ⟨19553318, by rfl⟩ : syracuseStep 26071091 = 39106637) B39106637
theorem B17380727 : Blo 2257435 17380727 := bstep (se 1 (by rfl) ⟨13035545, by rfl⟩ : syracuseStep 17380727 = 26071091) B26071091
theorem B11587151 : Blo 2257435 11587151 := bstep (se 1 (by rfl) ⟨8690363, by rfl⟩ : syracuseStep 11587151 = 17380727) B17380727
theorem B7724767 : Blo 2257435 7724767 := bstep (se 1 (by rfl) ⟨5793575, by rfl⟩ : syracuseStep 7724767 = 11587151) B11587151
theorem B10299689 : Blo 2257435 10299689 := bstep (se 2 (by rfl) ⟨3862383, by rfl⟩ : syracuseStep 10299689 = 7724767) B7724767
theorem B6866459 : Blo 2257435 6866459 := bstep (se 1 (by rfl) ⟨5149844, by rfl⟩ : syracuseStep 6866459 = 10299689) B10299689
theorem B4577639 : Blo 2257435 4577639 := bstep (se 1 (by rfl) ⟨3433229, by rfl⟩ : syracuseStep 4577639 = 6866459) B6866459
theorem B12207037 : Blo 2257435 12207037 := bstep (se 3 (by rfl) ⟨2288819, by rfl⟩ : syracuseStep 12207037 = 4577639) B4577639
theorem B16276049 : Blo 2257435 16276049 := bstep (se 2 (by rfl) ⟨6103518, by rfl⟩ : syracuseStep 16276049 = 12207037) B12207037
theorem B10850699 : Blo 2257435 10850699 := bstep (se 1 (by rfl) ⟨8138024, by rfl⟩ : syracuseStep 10850699 = 16276049) B16276049
theorem B7233799 : Blo 2257435 7233799 := bstep (se 1 (by rfl) ⟨5425349, by rfl⟩ : syracuseStep 7233799 = 10850699) B10850699
theorem B9645065 : Blo 2257435 9645065 := bstep (se 2 (by rfl) ⟨3616899, by rfl⟩ : syracuseStep 9645065 = 7233799) B7233799
theorem B6430043 : Blo 2257435 6430043 := bstep (se 1 (by rfl) ⟨4822532, by rfl⟩ : syracuseStep 6430043 = 9645065) B9645065
theorem B4286695 : Blo 2257435 4286695 := bstep (se 1 (by rfl) ⟨3215021, by rfl⟩ : syracuseStep 4286695 = 6430043) B6430043
theorem B5715593 : Blo 2257435 5715593 := bstep (se 2 (by rfl) ⟨2143347, by rfl⟩ : syracuseStep 5715593 = 4286695) B4286695
theorem B3810395 : Blo 2257435 3810395 := bstep (se 1 (by rfl) ⟨2857796, by rfl⟩ : syracuseStep 3810395 = 5715593) B5715593
theorem B2540263 : Blo 2257435 2540263 := bstep (se 1 (by rfl) ⟨1905197, by rfl⟩ : syracuseStep 2540263 = 3810395) B3810395
theorem B3387017 : Blo 2257435 3387017 := bstep (se 2 (by rfl) ⟨1270131, by rfl⟩ : syracuseStep 3387017 = 2540263) B2540263
theorem B2258011 : Blo 2257435 2258011 := bstep (se 1 (by rfl) ⟨1693508, by rfl⟩ : syracuseStep 2258011 = 3387017) B3387017
theorem B11431205 : Blo 2257435 11431205 := bbase (se 4 (by rfl) ⟨1071675, by rfl⟩ : syracuseStep 11431205 = 2143351) (by norm_num)
theorem B7620803 : Blo 2257435 7620803 := bstep (se 1 (by rfl) ⟨5715602, by rfl⟩ : syracuseStep 7620803 = 11431205) B11431205
theorem B5080535 : Blo 2257435 5080535 := bstep (se 1 (by rfl) ⟨3810401, by rfl⟩ : syracuseStep 5080535 = 7620803) B7620803
theorem B3387023 : Blo 2257435 3387023 := bstep (se 1 (by rfl) ⟨2540267, by rfl⟩ : syracuseStep 3387023 = 5080535) B5080535
theorem B2258015 : Blo 2257435 2258015 := bstep (se 1 (by rfl) ⟨1693511, by rfl⟩ : syracuseStep 2258015 = 3387023) B3387023
theorem B3387029 : Blo 2257435 3387029 := bbase (se 6 (by rfl) ⟨79383, by rfl⟩ : syracuseStep 3387029 = 158767) (by norm_num)
theorem B2258019 : Blo 2257435 2258019 := bstep (se 1 (by rfl) ⟨1693514, by rfl⟩ : syracuseStep 2258019 = 3387029) B3387029
theorem B7332533 : Blo 2257435 7332533 := bbase (se 5 (by rfl) ⟨343712, by rfl⟩ : syracuseStep 7332533 = 687425) (by norm_num)
theorem B4888355 : Blo 2257435 4888355 := bstep (se 1 (by rfl) ⟨3666266, by rfl⟩ : syracuseStep 4888355 = 7332533) B7332533
theorem B52142453 : Blo 2257435 52142453 := bstep (se 5 (by rfl) ⟨2444177, by rfl⟩ : syracuseStep 52142453 = 4888355) B4888355
theorem B34761635 : Blo 2257435 34761635 := bstep (se 1 (by rfl) ⟨26071226, by rfl⟩ : syracuseStep 34761635 = 52142453) B52142453
theorem B23174423 : Blo 2257435 23174423 := bstep (se 1 (by rfl) ⟨17380817, by rfl⟩ : syracuseStep 23174423 = 34761635) B34761635
theorem B15449615 : Blo 2257435 15449615 := bstep (se 1 (by rfl) ⟨11587211, by rfl⟩ : syracuseStep 15449615 = 23174423) B23174423
theorem B10299743 : Blo 2257435 10299743 := bstep (se 1 (by rfl) ⟨7724807, by rfl⟩ : syracuseStep 10299743 = 15449615) B15449615
theorem B6866495 : Blo 2257435 6866495 := bstep (se 1 (by rfl) ⟨5149871, by rfl⟩ : syracuseStep 6866495 = 10299743) B10299743
theorem B4577663 : Blo 2257435 4577663 := bstep (se 1 (by rfl) ⟨3433247, by rfl⟩ : syracuseStep 4577663 = 6866495) B6866495
theorem B3051775 : Blo 2257435 3051775 := bstep (se 1 (by rfl) ⟨2288831, by rfl⟩ : syracuseStep 3051775 = 4577663) B4577663
theorem B16276133 : Blo 2257435 16276133 := bstep (se 4 (by rfl) ⟨1525887, by rfl⟩ : syracuseStep 16276133 = 3051775) B3051775
theorem B10850755 : Blo 2257435 10850755 := bstep (se 1 (by rfl) ⟨8138066, by rfl⟩ : syracuseStep 10850755 = 16276133) B16276133
theorem B14467673 : Blo 2257435 14467673 := bstep (se 2 (by rfl) ⟨5425377, by rfl⟩ : syracuseStep 14467673 = 10850755) B10850755
theorem B9645115 : Blo 2257435 9645115 := bstep (se 1 (by rfl) ⟨7233836, by rfl⟩ : syracuseStep 9645115 = 14467673) B14467673
theorem B12860153 : Blo 2257435 12860153 := bstep (se 2 (by rfl) ⟨4822557, by rfl⟩ : syracuseStep 12860153 = 9645115) B9645115
theorem B8573435 : Blo 2257435 8573435 := bstep (se 1 (by rfl) ⟨6430076, by rfl⟩ : syracuseStep 8573435 = 12860153) B12860153
theorem B5715623 : Blo 2257435 5715623 := bstep (se 1 (by rfl) ⟨4286717, by rfl⟩ : syracuseStep 5715623 = 8573435) B8573435
theorem B3810415 : Blo 2257435 3810415 := bstep (se 1 (by rfl) ⟨2857811, by rfl⟩ : syracuseStep 3810415 = 5715623) B5715623
theorem B5080553 : Blo 2257435 5080553 := bstep (se 2 (by rfl) ⟨1905207, by rfl⟩ : syracuseStep 5080553 = 3810415) B3810415
theorem B3387035 : Blo 2257435 3387035 := bstep (se 1 (by rfl) ⟨2540276, by rfl⟩ : syracuseStep 3387035 = 5080553) B5080553
theorem B2258023 : Blo 2257435 2258023 := bstep (se 1 (by rfl) ⟨1693517, by rfl⟩ : syracuseStep 2258023 = 3387035) B3387035
theorem B2540281 : Blo 2257435 2540281 := bbase (se 2 (by rfl) ⟨952605, by rfl⟩ : syracuseStep 2540281 = 1905211) (by norm_num)
theorem B3387041 : Blo 2257435 3387041 := bstep (se 2 (by rfl) ⟨1270140, by rfl⟩ : syracuseStep 3387041 = 2540281) B2540281
theorem B2258027 : Blo 2257435 2258027 := bstep (se 1 (by rfl) ⟨1693520, by rfl⟩ : syracuseStep 2258027 = 3387041) B3387041
theorem B5425397 : Blo 2257435 5425397 := bbase (se 5 (by rfl) ⟨254315, by rfl⟩ : syracuseStep 5425397 = 508631) (by norm_num)
theorem B3616931 : Blo 2257435 3616931 := bstep (se 1 (by rfl) ⟨2712698, by rfl⟩ : syracuseStep 3616931 = 5425397) B5425397
theorem B9645149 : Blo 2257435 9645149 := bstep (se 3 (by rfl) ⟨1808465, by rfl⟩ : syracuseStep 9645149 = 3616931) B3616931
theorem B6430099 : Blo 2257435 6430099 := bstep (se 1 (by rfl) ⟨4822574, by rfl⟩ : syracuseStep 6430099 = 9645149) B9645149
theorem B8573465 : Blo 2257435 8573465 := bstep (se 2 (by rfl) ⟨3215049, by rfl⟩ : syracuseStep 8573465 = 6430099) B6430099
theorem B5715643 : Blo 2257435 5715643 := bstep (se 1 (by rfl) ⟨4286732, by rfl⟩ : syracuseStep 5715643 = 8573465) B8573465
theorem B7620857 : Blo 2257435 7620857 := bstep (se 2 (by rfl) ⟨2857821, by rfl⟩ : syracuseStep 7620857 = 5715643) B5715643
theorem B5080571 : Blo 2257435 5080571 := bstep (se 1 (by rfl) ⟨3810428, by rfl⟩ : syracuseStep 5080571 = 7620857) B7620857
theorem B3387047 : Blo 2257435 3387047 := bstep (se 1 (by rfl) ⟨2540285, by rfl⟩ : syracuseStep 3387047 = 5080571) B5080571
theorem B2258031 : Blo 2257435 2258031 := bstep (se 1 (by rfl) ⟨1693523, by rfl⟩ : syracuseStep 2258031 = 3387047) B3387047
theorem B3387053 : Blo 2257435 3387053 := bbase (se 3 (by rfl) ⟨635072, by rfl⟩ : syracuseStep 3387053 = 1270145) (by norm_num)
theorem B2258035 : Blo 2257435 2258035 := bstep (se 1 (by rfl) ⟨1693526, by rfl⟩ : syracuseStep 2258035 = 3387053) B3387053
theorem B5080589 : Blo 2257435 5080589 := bbase (se 3 (by rfl) ⟨952610, by rfl⟩ : syracuseStep 5080589 = 1905221) (by norm_num)
theorem B3387059 : Blo 2257435 3387059 := bstep (se 1 (by rfl) ⟨2540294, by rfl⟩ : syracuseStep 3387059 = 5080589) B5080589
theorem B2258039 : Blo 2257435 2258039 := bstep (se 1 (by rfl) ⟨1693529, by rfl⟩ : syracuseStep 2258039 = 3387059) B3387059
theorem B2857837 : Blo 2257435 2857837 := bbase (se 3 (by rfl) ⟨535844, by rfl⟩ : syracuseStep 2857837 = 1071689) (by norm_num)
theorem B3810449 : Blo 2257435 3810449 := bstep (se 2 (by rfl) ⟨1428918, by rfl⟩ : syracuseStep 3810449 = 2857837) B2857837
theorem B2540299 : Blo 2257435 2540299 := bstep (se 1 (by rfl) ⟨1905224, by rfl⟩ : syracuseStep 2540299 = 3810449) B3810449
theorem B3387065 : Blo 2257435 3387065 := bstep (se 2 (by rfl) ⟨1270149, by rfl⟩ : syracuseStep 3387065 = 2540299) B2540299
theorem B2258043 : Blo 2257435 2258043 := bstep (se 1 (by rfl) ⟨1693532, by rfl⟩ : syracuseStep 2258043 = 3387065) B3387065
theorem B10850869 : Blo 2257435 10850869 := bbase (se 5 (by rfl) ⟨508634, by rfl⟩ : syracuseStep 10850869 = 1017269) (by norm_num)
theorem B14467825 : Blo 2257435 14467825 := bstep (se 2 (by rfl) ⟨5425434, by rfl⟩ : syracuseStep 14467825 = 10850869) B10850869
theorem B19290433 : Blo 2257435 19290433 := bstep (se 2 (by rfl) ⟨7233912, by rfl⟩ : syracuseStep 19290433 = 14467825) B14467825
theorem B25720577 : Blo 2257435 25720577 := bstep (se 2 (by rfl) ⟨9645216, by rfl⟩ : syracuseStep 25720577 = 19290433) B19290433
theorem B17147051 : Blo 2257435 17147051 := bstep (se 1 (by rfl) ⟨12860288, by rfl⟩ : syracuseStep 17147051 = 25720577) B25720577
theorem B11431367 : Blo 2257435 11431367 := bstep (se 1 (by rfl) ⟨8573525, by rfl⟩ : syracuseStep 11431367 = 17147051) B17147051
theorem B7620911 : Blo 2257435 7620911 := bstep (se 1 (by rfl) ⟨5715683, by rfl⟩ : syracuseStep 7620911 = 11431367) B11431367
theorem B5080607 : Blo 2257435 5080607 := bstep (se 1 (by rfl) ⟨3810455, by rfl⟩ : syracuseStep 5080607 = 7620911) B7620911
theorem B3387071 : Blo 2257435 3387071 := bstep (se 1 (by rfl) ⟨2540303, by rfl⟩ : syracuseStep 3387071 = 5080607) B5080607
theorem B2258047 : Blo 2257435 2258047 := bstep (se 1 (by rfl) ⟨1693535, by rfl⟩ : syracuseStep 2258047 = 3387071) B3387071
theorem B3387077 : Blo 2257435 3387077 := bbase (se 4 (by rfl) ⟨317538, by rfl⟩ : syracuseStep 3387077 = 635077) (by norm_num)
theorem B2258051 : Blo 2257435 2258051 := bstep (se 1 (by rfl) ⟨1693538, by rfl⟩ : syracuseStep 2258051 = 3387077) B3387077
theorem B3810469 : Blo 2257435 3810469 := bbase (se 4 (by rfl) ⟨357231, by rfl⟩ : syracuseStep 3810469 = 714463) (by norm_num)
theorem B5080625 : Blo 2257435 5080625 := bstep (se 2 (by rfl) ⟨1905234, by rfl⟩ : syracuseStep 5080625 = 3810469) B3810469
theorem B3387083 : Blo 2257435 3387083 := bstep (se 1 (by rfl) ⟨2540312, by rfl⟩ : syracuseStep 3387083 = 5080625) B5080625
theorem B2258055 : Blo 2257435 2258055 := bstep (se 1 (by rfl) ⟨1693541, by rfl⟩ : syracuseStep 2258055 = 3387083) B3387083
theorem B2540317 : Blo 2257435 2540317 := bbase (se 3 (by rfl) ⟨476309, by rfl⟩ : syracuseStep 2540317 = 952619) (by norm_num)
theorem B3387089 : Blo 2257435 3387089 := bstep (se 2 (by rfl) ⟨1270158, by rfl⟩ : syracuseStep 3387089 = 2540317) B2540317
theorem B2258059 : Blo 2257435 2258059 := bstep (se 1 (by rfl) ⟨1693544, by rfl⟩ : syracuseStep 2258059 = 3387089) B3387089
theorem B7620965 : Blo 2257435 7620965 := bbase (se 4 (by rfl) ⟨714465, by rfl⟩ : syracuseStep 7620965 = 1428931) (by norm_num)
theorem B5080643 : Blo 2257435 5080643 := bstep (se 1 (by rfl) ⟨3810482, by rfl⟩ : syracuseStep 5080643 = 7620965) B7620965
theorem B3387095 : Blo 2257435 3387095 := bstep (se 1 (by rfl) ⟨2540321, by rfl⟩ : syracuseStep 3387095 = 5080643) B5080643
theorem B2258063 : Blo 2257435 2258063 := bstep (se 1 (by rfl) ⟨1693547, by rfl⟩ : syracuseStep 2258063 = 3387095) B3387095
theorem B3387101 : Blo 2257435 3387101 := bbase (se 3 (by rfl) ⟨635081, by rfl⟩ : syracuseStep 3387101 = 1270163) (by norm_num)
theorem B2258067 : Blo 2257435 2258067 := bstep (se 1 (by rfl) ⟨1693550, by rfl⟩ : syracuseStep 2258067 = 3387101) B3387101
theorem B5080661 : Blo 2257435 5080661 := bbase (se 8 (by rfl) ⟨29769, by rfl⟩ : syracuseStep 5080661 = 59539) (by norm_num)
theorem B3387107 : Blo 2257435 3387107 := bstep (se 1 (by rfl) ⟨2540330, by rfl⟩ : syracuseStep 3387107 = 5080661) B5080661
theorem B2258071 : Blo 2257435 2258071 := bstep (se 1 (by rfl) ⟨1693553, by rfl⟩ : syracuseStep 2258071 = 3387107) B3387107
theorem B4822669 : Blo 2257435 4822669 := bbase (se 3 (by rfl) ⟨904250, by rfl⟩ : syracuseStep 4822669 = 1808501) (by norm_num)
theorem B6430225 : Blo 2257435 6430225 := bstep (se 2 (by rfl) ⟨2411334, by rfl⟩ : syracuseStep 6430225 = 4822669) B4822669
theorem B8573633 : Blo 2257435 8573633 := bstep (se 2 (by rfl) ⟨3215112, by rfl⟩ : syracuseStep 8573633 = 6430225) B6430225
theorem B5715755 : Blo 2257435 5715755 := bstep (se 1 (by rfl) ⟨4286816, by rfl⟩ : syracuseStep 5715755 = 8573633) B8573633
theorem B3810503 : Blo 2257435 3810503 := bstep (se 1 (by rfl) ⟨2857877, by rfl⟩ : syracuseStep 3810503 = 5715755) B5715755
theorem B2540335 : Blo 2257435 2540335 := bstep (se 1 (by rfl) ⟨1905251, by rfl⟩ : syracuseStep 2540335 = 3810503) B3810503
theorem B3387113 : Blo 2257435 3387113 := bstep (se 2 (by rfl) ⟨1270167, by rfl⟩ : syracuseStep 3387113 = 2540335) B2540335
theorem B2258075 : Blo 2257435 2258075 := bstep (se 1 (by rfl) ⟨1693556, by rfl⟩ : syracuseStep 2258075 = 3387113) B3387113
theorem B11745589 : Blo 2257435 11745589 := bbase (se 5 (by rfl) ⟨550574, by rfl⟩ : syracuseStep 11745589 = 1101149) (by norm_num)
theorem B15660785 : Blo 2257435 15660785 := bstep (se 2 (by rfl) ⟨5872794, by rfl⟩ : syracuseStep 15660785 = 11745589) B11745589
theorem B10440523 : Blo 2257435 10440523 := bstep (se 1 (by rfl) ⟨7830392, by rfl⟩ : syracuseStep 10440523 = 15660785) B15660785
theorem B13920697 : Blo 2257435 13920697 := bstep (se 2 (by rfl) ⟨5220261, by rfl⟩ : syracuseStep 13920697 = 10440523) B10440523
theorem B18560929 : Blo 2257435 18560929 := bstep (se 2 (by rfl) ⟨6960348, by rfl⟩ : syracuseStep 18560929 = 13920697) B13920697
theorem B24747905 : Blo 2257435 24747905 := bstep (se 2 (by rfl) ⟨9280464, by rfl⟩ : syracuseStep 24747905 = 18560929) B18560929
theorem B16498603 : Blo 2257435 16498603 := bstep (se 1 (by rfl) ⟨12373952, by rfl⟩ : syracuseStep 16498603 = 24747905) B24747905
theorem B21998137 : Blo 2257435 21998137 := bstep (se 2 (by rfl) ⟨8249301, by rfl⟩ : syracuseStep 21998137 = 16498603) B16498603
theorem B29330849 : Blo 2257435 29330849 := bstep (se 2 (by rfl) ⟨10999068, by rfl⟩ : syracuseStep 29330849 = 21998137) B21998137
theorem B19553899 : Blo 2257435 19553899 := bstep (se 1 (by rfl) ⟨14665424, by rfl⟩ : syracuseStep 19553899 = 29330849) B29330849
theorem B26071865 : Blo 2257435 26071865 := bstep (se 2 (by rfl) ⟨9776949, by rfl⟩ : syracuseStep 26071865 = 19553899) B19553899
theorem B17381243 : Blo 2257435 17381243 := bstep (se 1 (by rfl) ⟨13035932, by rfl⟩ : syracuseStep 17381243 = 26071865) B26071865
theorem B46349981 : Blo 2257435 46349981 := bstep (se 3 (by rfl) ⟨8690621, by rfl⟩ : syracuseStep 46349981 = 17381243) B17381243
theorem B30899987 : Blo 2257435 30899987 := bstep (se 1 (by rfl) ⟨23174990, by rfl⟩ : syracuseStep 30899987 = 46349981) B46349981
theorem B20599991 : Blo 2257435 20599991 := bstep (se 1 (by rfl) ⟨15449993, by rfl⟩ : syracuseStep 20599991 = 30899987) B30899987
theorem B13733327 : Blo 2257435 13733327 := bstep (se 1 (by rfl) ⟨10299995, by rfl⟩ : syracuseStep 13733327 = 20599991) B20599991
theorem B36622205 : Blo 2257435 36622205 := bstep (se 3 (by rfl) ⟨6866663, by rfl⟩ : syracuseStep 36622205 = 13733327) B13733327
theorem B24414803 : Blo 2257435 24414803 := bstep (se 1 (by rfl) ⟨18311102, by rfl⟩ : syracuseStep 24414803 = 36622205) B36622205
theorem B16276535 : Blo 2257435 16276535 := bstep (se 1 (by rfl) ⟨12207401, by rfl⟩ : syracuseStep 16276535 = 24414803) B24414803
theorem B10851023 : Blo 2257435 10851023 := bstep (se 1 (by rfl) ⟨8138267, by rfl⟩ : syracuseStep 10851023 = 16276535) B16276535
theorem B28936061 : Blo 2257435 28936061 := bstep (se 3 (by rfl) ⟨5425511, by rfl⟩ : syracuseStep 28936061 = 10851023) B10851023
theorem B19290707 : Blo 2257435 19290707 := bstep (se 1 (by rfl) ⟨14468030, by rfl⟩ : syracuseStep 19290707 = 28936061) B28936061
theorem B12860471 : Blo 2257435 12860471 := bstep (se 1 (by rfl) ⟨9645353, by rfl⟩ : syracuseStep 12860471 = 19290707) B19290707
theorem B8573647 : Blo 2257435 8573647 := bstep (se 1 (by rfl) ⟨6430235, by rfl⟩ : syracuseStep 8573647 = 12860471) B12860471
theorem B11431529 : Blo 2257435 11431529 := bstep (se 2 (by rfl) ⟨4286823, by rfl⟩ : syracuseStep 11431529 = 8573647) B8573647
theorem B7621019 : Blo 2257435 7621019 := bstep (se 1 (by rfl) ⟨5715764, by rfl⟩ : syracuseStep 7621019 = 11431529) B11431529
theorem B5080679 : Blo 2257435 5080679 := bstep (se 1 (by rfl) ⟨3810509, by rfl⟩ : syracuseStep 5080679 = 7621019) B7621019
theorem B3387119 : Blo 2257435 3387119 := bstep (se 1 (by rfl) ⟨2540339, by rfl⟩ : syracuseStep 3387119 = 5080679) B5080679
theorem B2258079 : Blo 2257435 2258079 := bstep (se 1 (by rfl) ⟨1693559, by rfl⟩ : syracuseStep 2258079 = 3387119) B3387119
theorem B3387125 : Blo 2257435 3387125 := bbase (se 5 (by rfl) ⟨158771, by rfl⟩ : syracuseStep 3387125 = 317543) (by norm_num)
theorem B2258083 : Blo 2257435 2258083 := bstep (se 1 (by rfl) ⟨1693562, by rfl⟩ : syracuseStep 2258083 = 3387125) B3387125
theorem B3617021 : Blo 2257435 3617021 := bbase (se 3 (by rfl) ⟨678191, by rfl⟩ : syracuseStep 3617021 = 1356383) (by norm_num)
theorem B9645389 : Blo 2257435 9645389 := bstep (se 3 (by rfl) ⟨1808510, by rfl⟩ : syracuseStep 9645389 = 3617021) B3617021
theorem B6430259 : Blo 2257435 6430259 := bstep (se 1 (by rfl) ⟨4822694, by rfl⟩ : syracuseStep 6430259 = 9645389) B9645389
theorem B4286839 : Blo 2257435 4286839 := bstep (se 1 (by rfl) ⟨3215129, by rfl⟩ : syracuseStep 4286839 = 6430259) B6430259
theorem B5715785 : Blo 2257435 5715785 := bstep (se 2 (by rfl) ⟨2143419, by rfl⟩ : syracuseStep 5715785 = 4286839) B4286839
theorem B3810523 : Blo 2257435 3810523 := bstep (se 1 (by rfl) ⟨2857892, by rfl⟩ : syracuseStep 3810523 = 5715785) B5715785
theorem B5080697 : Blo 2257435 5080697 := bstep (se 2 (by rfl) ⟨1905261, by rfl⟩ : syracuseStep 5080697 = 3810523) B3810523
theorem B3387131 : Blo 2257435 3387131 := bstep (se 1 (by rfl) ⟨2540348, by rfl⟩ : syracuseStep 3387131 = 5080697) B5080697
theorem B2258087 : Blo 2257435 2258087 := bstep (se 1 (by rfl) ⟨1693565, by rfl⟩ : syracuseStep 2258087 = 3387131) B3387131
theorem B2540353 : Blo 2257435 2540353 := bbase (se 2 (by rfl) ⟨952632, by rfl⟩ : syracuseStep 2540353 = 1905265) (by norm_num)
theorem B3387137 : Blo 2257435 3387137 := bstep (se 2 (by rfl) ⟨1270176, by rfl⟩ : syracuseStep 3387137 = 2540353) B2540353
theorem B2258091 : Blo 2257435 2258091 := bstep (se 1 (by rfl) ⟨1693568, by rfl⟩ : syracuseStep 2258091 = 3387137) B3387137
theorem B5715805 : Blo 2257435 5715805 := bbase (se 3 (by rfl) ⟨1071713, by rfl⟩ : syracuseStep 5715805 = 2143427) (by norm_num)
theorem B7621073 : Blo 2257435 7621073 := bstep (se 2 (by rfl) ⟨2857902, by rfl⟩ : syracuseStep 7621073 = 5715805) B5715805
theorem B5080715 : Blo 2257435 5080715 := bstep (se 1 (by rfl) ⟨3810536, by rfl⟩ : syracuseStep 5080715 = 7621073) B7621073
theorem B3387143 : Blo 2257435 3387143 := bstep (se 1 (by rfl) ⟨2540357, by rfl⟩ : syracuseStep 3387143 = 5080715) B5080715
theorem B2258095 : Blo 2257435 2258095 := bstep (se 1 (by rfl) ⟨1693571, by rfl⟩ : syracuseStep 2258095 = 3387143) B3387143
theorem B3387149 : Blo 2257435 3387149 := bbase (se 3 (by rfl) ⟨635090, by rfl⟩ : syracuseStep 3387149 = 1270181) (by norm_num)
theorem B2258099 : Blo 2257435 2258099 := bstep (se 1 (by rfl) ⟨1693574, by rfl⟩ : syracuseStep 2258099 = 3387149) B3387149
theorem B5080733 : Blo 2257435 5080733 := bbase (se 3 (by rfl) ⟨952637, by rfl⟩ : syracuseStep 5080733 = 1905275) (by norm_num)
theorem B3387155 : Blo 2257435 3387155 := bstep (se 1 (by rfl) ⟨2540366, by rfl⟩ : syracuseStep 3387155 = 5080733) B5080733
theorem B2258103 : Blo 2257435 2258103 := bstep (se 1 (by rfl) ⟨1693577, by rfl⟩ : syracuseStep 2258103 = 3387155) B3387155
theorem B3810557 : Blo 2257435 3810557 := bbase (se 3 (by rfl) ⟨714479, by rfl⟩ : syracuseStep 3810557 = 1428959) (by norm_num)
theorem B2540371 : Blo 2257435 2540371 := bstep (se 1 (by rfl) ⟨1905278, by rfl⟩ : syracuseStep 2540371 = 3810557) B3810557
theorem B3387161 : Blo 2257435 3387161 := bstep (se 2 (by rfl) ⟨1270185, by rfl⟩ : syracuseStep 3387161 = 2540371) B2540371
theorem B2258107 : Blo 2257435 2258107 := bstep (se 1 (by rfl) ⟨1693580, by rfl⟩ : syracuseStep 2258107 = 3387161) B3387161
theorem B5425589 : Blo 2257435 5425589 := bbase (se 5 (by rfl) ⟨254324, by rfl⟩ : syracuseStep 5425589 = 508649) (by norm_num)
theorem B3617059 : Blo 2257435 3617059 := bstep (se 1 (by rfl) ⟨2712794, by rfl⟩ : syracuseStep 3617059 = 5425589) B5425589
theorem B4822745 : Blo 2257435 4822745 := bstep (se 2 (by rfl) ⟨1808529, by rfl⟩ : syracuseStep 4822745 = 3617059) B3617059
theorem B12860653 : Blo 2257435 12860653 := bstep (se 3 (by rfl) ⟨2411372, by rfl⟩ : syracuseStep 12860653 = 4822745) B4822745
theorem B17147537 : Blo 2257435 17147537 := bstep (se 2 (by rfl) ⟨6430326, by rfl⟩ : syracuseStep 17147537 = 12860653) B12860653
theorem B11431691 : Blo 2257435 11431691 := bstep (se 1 (by rfl) ⟨8573768, by rfl⟩ : syracuseStep 11431691 = 17147537) B17147537
theorem B7621127 : Blo 2257435 7621127 := bstep (se 1 (by rfl) ⟨5715845, by rfl⟩ : syracuseStep 7621127 = 11431691) B11431691
theorem B5080751 : Blo 2257435 5080751 := bstep (se 1 (by rfl) ⟨3810563, by rfl⟩ : syracuseStep 5080751 = 7621127) B7621127
theorem B3387167 : Blo 2257435 3387167 := bstep (se 1 (by rfl) ⟨2540375, by rfl⟩ : syracuseStep 3387167 = 5080751) B5080751
theorem B2258111 : Blo 2257435 2258111 := bstep (se 1 (by rfl) ⟨1693583, by rfl⟩ : syracuseStep 2258111 = 3387167) B3387167
theorem B3387173 : Blo 2257435 3387173 := bbase (se 4 (by rfl) ⟨317547, by rfl⟩ : syracuseStep 3387173 = 635095) (by norm_num)
theorem B2258115 : Blo 2257435 2258115 := bstep (se 1 (by rfl) ⟨1693586, by rfl⟩ : syracuseStep 2258115 = 3387173) B3387173
theorem B2857933 : Blo 2257435 2857933 := bbase (se 3 (by rfl) ⟨535862, by rfl⟩ : syracuseStep 2857933 = 1071725) (by norm_num)
theorem B3810577 : Blo 2257435 3810577 := bstep (se 2 (by rfl) ⟨1428966, by rfl⟩ : syracuseStep 3810577 = 2857933) B2857933
theorem B5080769 : Blo 2257435 5080769 := bstep (se 2 (by rfl) ⟨1905288, by rfl⟩ : syracuseStep 5080769 = 3810577) B3810577
theorem B3387179 : Blo 2257435 3387179 := bstep (se 1 (by rfl) ⟨2540384, by rfl⟩ : syracuseStep 3387179 = 5080769) B5080769
theorem B2258119 : Blo 2257435 2258119 := bstep (se 1 (by rfl) ⟨1693589, by rfl⟩ : syracuseStep 2258119 = 3387179) B3387179
theorem B2540389 : Blo 2257435 2540389 := bbase (se 4 (by rfl) ⟨238161, by rfl⟩ : syracuseStep 2540389 = 476323) (by norm_num)
theorem B3387185 : Blo 2257435 3387185 := bstep (se 2 (by rfl) ⟨1270194, by rfl⟩ : syracuseStep 3387185 = 2540389) B2540389
theorem B2258123 : Blo 2257435 2258123 := bstep (se 1 (by rfl) ⟨1693592, by rfl⟩ : syracuseStep 2258123 = 3387185) B3387185
theorem B6430373 : Blo 2257435 6430373 := bbase (se 4 (by rfl) ⟨602847, by rfl⟩ : syracuseStep 6430373 = 1205695) (by norm_num)
theorem B4286915 : Blo 2257435 4286915 := bstep (se 1 (by rfl) ⟨3215186, by rfl⟩ : syracuseStep 4286915 = 6430373) B6430373
theorem B2857943 : Blo 2257435 2857943 := bstep (se 1 (by rfl) ⟨2143457, by rfl⟩ : syracuseStep 2857943 = 4286915) B4286915
theorem B7621181 : Blo 2257435 7621181 := bstep (se 3 (by rfl) ⟨1428971, by rfl⟩ : syracuseStep 7621181 = 2857943) B2857943
theorem B5080787 : Blo 2257435 5080787 := bstep (se 1 (by rfl) ⟨3810590, by rfl⟩ : syracuseStep 5080787 = 7621181) B7621181
theorem B3387191 : Blo 2257435 3387191 := bstep (se 1 (by rfl) ⟨2540393, by rfl⟩ : syracuseStep 3387191 = 5080787) B5080787
theorem B2258127 : Blo 2257435 2258127 := bstep (se 1 (by rfl) ⟨1693595, by rfl⟩ : syracuseStep 2258127 = 3387191) B3387191
theorem B3387197 : Blo 2257435 3387197 := bbase (se 3 (by rfl) ⟨635099, by rfl⟩ : syracuseStep 3387197 = 1270199) (by norm_num)
theorem B2258131 : Blo 2257435 2258131 := bstep (se 1 (by rfl) ⟨1693598, by rfl⟩ : syracuseStep 2258131 = 3387197) B3387197
theorem B5080805 : Blo 2257435 5080805 := bbase (se 4 (by rfl) ⟨476325, by rfl⟩ : syracuseStep 5080805 = 952651) (by norm_num)
theorem B3387203 : Blo 2257435 3387203 := bstep (se 1 (by rfl) ⟨2540402, by rfl⟩ : syracuseStep 3387203 = 5080805) B5080805
theorem B2258135 : Blo 2257435 2258135 := bstep (se 1 (by rfl) ⟨1693601, by rfl⟩ : syracuseStep 2258135 = 3387203) B3387203
theorem B5715917 : Blo 2257435 5715917 := bbase (se 3 (by rfl) ⟨1071734, by rfl⟩ : syracuseStep 5715917 = 2143469) (by norm_num)
theorem B3810611 : Blo 2257435 3810611 := bstep (se 1 (by rfl) ⟨2857958, by rfl⟩ : syracuseStep 3810611 = 5715917) B5715917
theorem B2540407 : Blo 2257435 2540407 := bstep (se 1 (by rfl) ⟨1905305, by rfl⟩ : syracuseStep 2540407 = 3810611) B3810611
theorem B3387209 : Blo 2257435 3387209 := bstep (se 2 (by rfl) ⟨1270203, by rfl⟩ : syracuseStep 3387209 = 2540407) B2540407
theorem B2258139 : Blo 2257435 2258139 := bstep (se 1 (by rfl) ⟨1693604, by rfl⟩ : syracuseStep 2258139 = 3387209) B3387209
theorem B8138501 : Blo 2257435 8138501 := bbase (se 4 (by rfl) ⟨762984, by rfl⟩ : syracuseStep 8138501 = 1525969) (by norm_num)
theorem B5425667 : Blo 2257435 5425667 := bstep (se 1 (by rfl) ⟨4069250, by rfl⟩ : syracuseStep 5425667 = 8138501) B8138501
theorem B3617111 : Blo 2257435 3617111 := bstep (se 1 (by rfl) ⟨2712833, by rfl⟩ : syracuseStep 3617111 = 5425667) B5425667
theorem B2411407 : Blo 2257435 2411407 := bstep (se 1 (by rfl) ⟨1808555, by rfl⟩ : syracuseStep 2411407 = 3617111) B3617111
theorem B3215209 : Blo 2257435 3215209 := bstep (se 2 (by rfl) ⟨1205703, by rfl⟩ : syracuseStep 3215209 = 2411407) B2411407
theorem B4286945 : Blo 2257435 4286945 := bstep (se 2 (by rfl) ⟨1607604, by rfl⟩ : syracuseStep 4286945 = 3215209) B3215209
theorem B11431853 : Blo 2257435 11431853 := bstep (se 3 (by rfl) ⟨2143472, by rfl⟩ : syracuseStep 11431853 = 4286945) B4286945
theorem B7621235 : Blo 2257435 7621235 := bstep (se 1 (by rfl) ⟨5715926, by rfl⟩ : syracuseStep 7621235 = 11431853) B11431853
theorem B5080823 : Blo 2257435 5080823 := bstep (se 1 (by rfl) ⟨3810617, by rfl⟩ : syracuseStep 5080823 = 7621235) B7621235
theorem B3387215 : Blo 2257435 3387215 := bstep (se 1 (by rfl) ⟨2540411, by rfl⟩ : syracuseStep 3387215 = 5080823) B5080823
theorem B2258143 : Blo 2257435 2258143 := bstep (se 1 (by rfl) ⟨1693607, by rfl⟩ : syracuseStep 2258143 = 3387215) B3387215
theorem B3387221 : Blo 2257435 3387221 := bbase (se 9 (by rfl) ⟨9923, by rfl⟩ : syracuseStep 3387221 = 19847) (by norm_num)
theorem B2258147 : Blo 2257435 2258147 := bstep (se 1 (by rfl) ⟨1693610, by rfl⟩ : syracuseStep 2258147 = 3387221) B3387221
theorem B9155845 : Blo 2257435 9155845 := bbase (se 4 (by rfl) ⟨858360, by rfl⟩ : syracuseStep 9155845 = 1716721) (by norm_num)
theorem B12207793 : Blo 2257435 12207793 := bstep (se 2 (by rfl) ⟨4577922, by rfl⟩ : syracuseStep 12207793 = 9155845) B9155845
theorem B16277057 : Blo 2257435 16277057 := bstep (se 2 (by rfl) ⟨6103896, by rfl⟩ : syracuseStep 16277057 = 12207793) B12207793
theorem B10851371 : Blo 2257435 10851371 := bstep (se 1 (by rfl) ⟨8138528, by rfl⟩ : syracuseStep 10851371 = 16277057) B16277057
theorem B7234247 : Blo 2257435 7234247 := bstep (se 1 (by rfl) ⟨5425685, by rfl⟩ : syracuseStep 7234247 = 10851371) B10851371
theorem B4822831 : Blo 2257435 4822831 := bstep (se 1 (by rfl) ⟨3617123, by rfl⟩ : syracuseStep 4822831 = 7234247) B7234247
theorem B6430441 : Blo 2257435 6430441 := bstep (se 2 (by rfl) ⟨2411415, by rfl⟩ : syracuseStep 6430441 = 4822831) B4822831
theorem B8573921 : Blo 2257435 8573921 := bstep (se 2 (by rfl) ⟨3215220, by rfl⟩ : syracuseStep 8573921 = 6430441) B6430441
theorem B5715947 : Blo 2257435 5715947 := bstep (se 1 (by rfl) ⟨4286960, by rfl⟩ : syracuseStep 5715947 = 8573921) B8573921
theorem B3810631 : Blo 2257435 3810631 := bstep (se 1 (by rfl) ⟨2857973, by rfl⟩ : syracuseStep 3810631 = 5715947) B5715947
theorem B5080841 : Blo 2257435 5080841 := bstep (se 2 (by rfl) ⟨1905315, by rfl⟩ : syracuseStep 5080841 = 3810631) B3810631
theorem B3387227 : Blo 2257435 3387227 := bstep (se 1 (by rfl) ⟨2540420, by rfl⟩ : syracuseStep 3387227 = 5080841) B5080841
theorem B2258151 : Blo 2257435 2258151 := bstep (se 1 (by rfl) ⟨1693613, by rfl⟩ : syracuseStep 2258151 = 3387227) B3387227
theorem B2540425 : Blo 2257435 2540425 := bbase (se 2 (by rfl) ⟨952659, by rfl⟩ : syracuseStep 2540425 = 1905319) (by norm_num)
theorem B3387233 : Blo 2257435 3387233 := bstep (se 2 (by rfl) ⟨1270212, by rfl⟩ : syracuseStep 3387233 = 2540425) B2540425
theorem B2258155 : Blo 2257435 2258155 := bstep (se 1 (by rfl) ⟨1693616, by rfl⟩ : syracuseStep 2258155 = 3387233) B3387233
theorem B12374389 : Blo 2257435 12374389 := bbase (se 5 (by rfl) ⟨580049, by rfl⟩ : syracuseStep 12374389 = 1160099) (by norm_num)
theorem B65996741 : Blo 2257435 65996741 := bstep (se 4 (by rfl) ⟨6187194, by rfl⟩ : syracuseStep 65996741 = 12374389) B12374389
theorem B43997827 : Blo 2257435 43997827 := bstep (se 1 (by rfl) ⟨32998370, by rfl⟩ : syracuseStep 43997827 = 65996741) B65996741
theorem B58663769 : Blo 2257435 58663769 := bstep (se 2 (by rfl) ⟨21998913, by rfl⟩ : syracuseStep 58663769 = 43997827) B43997827
theorem B625746869 : Blo 2257435 625746869 := bstep (se 5 (by rfl) ⟨29331884, by rfl⟩ : syracuseStep 625746869 = 58663769) B58663769
theorem B417164579 : Blo 2257435 417164579 := bstep (se 1 (by rfl) ⟨312873434, by rfl⟩ : syracuseStep 417164579 = 625746869) B625746869
theorem B278109719 : Blo 2257435 278109719 := bstep (se 1 (by rfl) ⟨208582289, by rfl⟩ : syracuseStep 278109719 = 417164579) B417164579
theorem B185406479 : Blo 2257435 185406479 := bstep (se 1 (by rfl) ⟨139054859, by rfl⟩ : syracuseStep 185406479 = 278109719) B278109719
theorem B123604319 : Blo 2257435 123604319 := bstep (se 1 (by rfl) ⟨92703239, by rfl⟩ : syracuseStep 123604319 = 185406479) B185406479
theorem B329611517 : Blo 2257435 329611517 := bstep (se 3 (by rfl) ⟨61802159, by rfl⟩ : syracuseStep 329611517 = 123604319) B123604319
theorem B219741011 : Blo 2257435 219741011 := bstep (se 1 (by rfl) ⟨164805758, by rfl⟩ : syracuseStep 219741011 = 329611517) B329611517
theorem B146494007 : Blo 2257435 146494007 := bstep (se 1 (by rfl) ⟨109870505, by rfl⟩ : syracuseStep 146494007 = 219741011) B219741011
theorem B97662671 : Blo 2257435 97662671 := bstep (se 1 (by rfl) ⟨73247003, by rfl⟩ : syracuseStep 97662671 = 146494007) B146494007
theorem B65108447 : Blo 2257435 65108447 := bstep (se 1 (by rfl) ⟨48831335, by rfl⟩ : syracuseStep 65108447 = 97662671) B97662671
theorem B43405631 : Blo 2257435 43405631 := bstep (se 1 (by rfl) ⟨32554223, by rfl⟩ : syracuseStep 43405631 = 65108447) B65108447
theorem B28937087 : Blo 2257435 28937087 := bstep (se 1 (by rfl) ⟨21702815, by rfl⟩ : syracuseStep 28937087 = 43405631) B43405631
theorem B19291391 : Blo 2257435 19291391 := bstep (se 1 (by rfl) ⟨14468543, by rfl⟩ : syracuseStep 19291391 = 28937087) B28937087
theorem B12860927 : Blo 2257435 12860927 := bstep (se 1 (by rfl) ⟨9645695, by rfl⟩ : syracuseStep 12860927 = 19291391) B19291391
theorem B8573951 : Blo 2257435 8573951 := bstep (se 1 (by rfl) ⟨6430463, by rfl⟩ : syracuseStep 8573951 = 12860927) B12860927
theorem B5715967 : Blo 2257435 5715967 := bstep (se 1 (by rfl) ⟨4286975, by rfl⟩ : syracuseStep 5715967 = 8573951) B8573951
theorem B7621289 : Blo 2257435 7621289 := bstep (se 2 (by rfl) ⟨2857983, by rfl⟩ : syracuseStep 7621289 = 5715967) B5715967
theorem B5080859 : Blo 2257435 5080859 := bstep (se 1 (by rfl) ⟨3810644, by rfl⟩ : syracuseStep 5080859 = 7621289) B7621289
theorem B3387239 : Blo 2257435 3387239 := bstep (se 1 (by rfl) ⟨2540429, by rfl⟩ : syracuseStep 3387239 = 5080859) B5080859
theorem B2258159 : Blo 2257435 2258159 := bstep (se 1 (by rfl) ⟨1693619, by rfl⟩ : syracuseStep 2258159 = 3387239) B3387239
theorem B3387245 : Blo 2257435 3387245 := bbase (se 3 (by rfl) ⟨635108, by rfl⟩ : syracuseStep 3387245 = 1270217) (by norm_num)
theorem B2258163 : Blo 2257435 2258163 := bstep (se 1 (by rfl) ⟨1693622, by rfl⟩ : syracuseStep 2258163 = 3387245) B3387245
theorem B5080877 : Blo 2257435 5080877 := bbase (se 3 (by rfl) ⟨952664, by rfl⟩ : syracuseStep 5080877 = 1905329) (by norm_num)
theorem B3387251 : Blo 2257435 3387251 := bstep (se 1 (by rfl) ⟨2540438, by rfl⟩ : syracuseStep 3387251 = 5080877) B5080877
theorem B2258167 : Blo 2257435 2258167 := bstep (se 1 (by rfl) ⟨1693625, by rfl⟩ : syracuseStep 2258167 = 3387251) B3387251
theorem B9645749 : Blo 2257435 9645749 := bbase (se 5 (by rfl) ⟨452144, by rfl⟩ : syracuseStep 9645749 = 904289) (by norm_num)
theorem B6430499 : Blo 2257435 6430499 := bstep (se 1 (by rfl) ⟨4822874, by rfl⟩ : syracuseStep 6430499 = 9645749) B9645749
theorem B4286999 : Blo 2257435 4286999 := bstep (se 1 (by rfl) ⟨3215249, by rfl⟩ : syracuseStep 4286999 = 6430499) B6430499
theorem B2857999 : Blo 2257435 2857999 := bstep (se 1 (by rfl) ⟨2143499, by rfl⟩ : syracuseStep 2857999 = 4286999) B4286999
theorem B3810665 : Blo 2257435 3810665 := bstep (se 2 (by rfl) ⟨1428999, by rfl⟩ : syracuseStep 3810665 = 2857999) B2857999
theorem B2540443 : Blo 2257435 2540443 := bstep (se 1 (by rfl) ⟨1905332, by rfl⟩ : syracuseStep 2540443 = 3810665) B3810665
theorem B3387257 : Blo 2257435 3387257 := bstep (se 2 (by rfl) ⟨1270221, by rfl⟩ : syracuseStep 3387257 = 2540443) B2540443
theorem B2258171 : Blo 2257435 2258171 := bstep (se 1 (by rfl) ⟨1693628, by rfl⟩ : syracuseStep 2258171 = 3387257) B3387257
theorem B2575109 : Blo 2257435 2575109 := bbase (se 4 (by rfl) ⟨241416, by rfl⟩ : syracuseStep 2575109 = 482833) (by norm_num)
theorem B6866957 : Blo 2257435 6866957 := bstep (se 3 (by rfl) ⟨1287554, by rfl⟩ : syracuseStep 6866957 = 2575109) B2575109
theorem B4577971 : Blo 2257435 4577971 := bstep (se 1 (by rfl) ⟨3433478, by rfl⟩ : syracuseStep 4577971 = 6866957) B6866957
theorem B6103961 : Blo 2257435 6103961 := bstep (se 2 (by rfl) ⟨2288985, by rfl⟩ : syracuseStep 6103961 = 4577971) B4577971
theorem B4069307 : Blo 2257435 4069307 := bstep (se 1 (by rfl) ⟨3051980, by rfl⟩ : syracuseStep 4069307 = 6103961) B6103961
theorem B2712871 : Blo 2257435 2712871 := bstep (se 1 (by rfl) ⟨2034653, by rfl⟩ : syracuseStep 2712871 = 4069307) B4069307
theorem B14468645 : Blo 2257435 14468645 := bstep (se 4 (by rfl) ⟨1356435, by rfl⟩ : syracuseStep 14468645 = 2712871) B2712871
theorem B38583053 : Blo 2257435 38583053 := bstep (se 3 (by rfl) ⟨7234322, by rfl⟩ : syracuseStep 38583053 = 14468645) B14468645
theorem B25722035 : Blo 2257435 25722035 := bstep (se 1 (by rfl) ⟨19291526, by rfl⟩ : syracuseStep 25722035 = 38583053) B38583053
theorem B17148023 : Blo 2257435 17148023 := bstep (se 1 (by rfl) ⟨12861017, by rfl⟩ : syracuseStep 17148023 = 25722035) B25722035
theorem B11432015 : Blo 2257435 11432015 := bstep (se 1 (by rfl) ⟨8574011, by rfl⟩ : syracuseStep 11432015 = 17148023) B17148023
theorem B7621343 : Blo 2257435 7621343 := bstep (se 1 (by rfl) ⟨5716007, by rfl⟩ : syracuseStep 7621343 = 11432015) B11432015
theorem B5080895 : Blo 2257435 5080895 := bstep (se 1 (by rfl) ⟨3810671, by rfl⟩ : syracuseStep 5080895 = 7621343) B7621343
theorem B3387263 : Blo 2257435 3387263 := bstep (se 1 (by rfl) ⟨2540447, by rfl⟩ : syracuseStep 3387263 = 5080895) B5080895
theorem B2258175 : Blo 2257435 2258175 := bstep (se 1 (by rfl) ⟨1693631, by rfl⟩ : syracuseStep 2258175 = 3387263) B3387263
theorem B3387269 : Blo 2257435 3387269 := bbase (se 4 (by rfl) ⟨317556, by rfl⟩ : syracuseStep 3387269 = 635113) (by norm_num)
theorem B2258179 : Blo 2257435 2258179 := bstep (se 1 (by rfl) ⟨1693634, by rfl⟩ : syracuseStep 2258179 = 3387269) B3387269
theorem B3810685 : Blo 2257435 3810685 := bbase (se 3 (by rfl) ⟨714503, by rfl⟩ : syracuseStep 3810685 = 1429007) (by norm_num)
theorem B5080913 : Blo 2257435 5080913 := bstep (se 2 (by rfl) ⟨1905342, by rfl⟩ : syracuseStep 5080913 = 3810685) B3810685
theorem B3387275 : Blo 2257435 3387275 := bstep (se 1 (by rfl) ⟨2540456, by rfl⟩ : syracuseStep 3387275 = 5080913) B5080913
theorem B2258183 : Blo 2257435 2258183 := bstep (se 1 (by rfl) ⟨1693637, by rfl⟩ : syracuseStep 2258183 = 3387275) B3387275
theorem B2540461 : Blo 2257435 2540461 := bbase (se 3 (by rfl) ⟨476336, by rfl⟩ : syracuseStep 2540461 = 952673) (by norm_num)
theorem B3387281 : Blo 2257435 3387281 := bstep (se 2 (by rfl) ⟨1270230, by rfl⟩ : syracuseStep 3387281 = 2540461) B2540461
theorem B2258187 : Blo 2257435 2258187 := bstep (se 1 (by rfl) ⟨1693640, by rfl⟩ : syracuseStep 2258187 = 3387281) B3387281
theorem B7621397 : Blo 2257435 7621397 := bbase (se 6 (by rfl) ⟨178626, by rfl⟩ : syracuseStep 7621397 = 357253) (by norm_num)
theorem B5080931 : Blo 2257435 5080931 := bstep (se 1 (by rfl) ⟨3810698, by rfl⟩ : syracuseStep 5080931 = 7621397) B7621397
theorem B3387287 : Blo 2257435 3387287 := bstep (se 1 (by rfl) ⟨2540465, by rfl⟩ : syracuseStep 3387287 = 5080931) B5080931
theorem B2258191 : Blo 2257435 2258191 := bstep (se 1 (by rfl) ⟨1693643, by rfl⟩ : syracuseStep 2258191 = 3387287) B3387287
theorem B3387293 : Blo 2257435 3387293 := bbase (se 3 (by rfl) ⟨635117, by rfl⟩ : syracuseStep 3387293 = 1270235) (by norm_num)
theorem B2258195 : Blo 2257435 2258195 := bstep (se 1 (by rfl) ⟨1693646, by rfl⟩ : syracuseStep 2258195 = 3387293) B3387293
theorem B5080949 : Blo 2257435 5080949 := bbase (se 5 (by rfl) ⟨238169, by rfl⟩ : syracuseStep 5080949 = 476339) (by norm_num)
theorem B3387299 : Blo 2257435 3387299 := bstep (se 1 (by rfl) ⟨2540474, by rfl⟩ : syracuseStep 3387299 = 5080949) B5080949
theorem B2258199 : Blo 2257435 2258199 := bstep (se 1 (by rfl) ⟨1693649, by rfl⟩ : syracuseStep 2258199 = 3387299) B3387299
theorem B19821781 : Blo 2257435 19821781 := bbase (se 7 (by rfl) ⟨232286, by rfl⟩ : syracuseStep 19821781 = 464573) (by norm_num)
theorem B26429041 : Blo 2257435 26429041 := bstep (se 2 (by rfl) ⟨9910890, by rfl⟩ : syracuseStep 26429041 = 19821781) B19821781
theorem B35238721 : Blo 2257435 35238721 := bstep (se 2 (by rfl) ⟨13214520, by rfl⟩ : syracuseStep 35238721 = 26429041) B26429041
theorem B46984961 : Blo 2257435 46984961 := bstep (se 2 (by rfl) ⟨17619360, by rfl⟩ : syracuseStep 46984961 = 35238721) B35238721
theorem B31323307 : Blo 2257435 31323307 := bstep (se 1 (by rfl) ⟨23492480, by rfl⟩ : syracuseStep 31323307 = 46984961) B46984961
theorem B41764409 : Blo 2257435 41764409 := bstep (se 2 (by rfl) ⟨15661653, by rfl⟩ : syracuseStep 41764409 = 31323307) B31323307
theorem B27842939 : Blo 2257435 27842939 := bstep (se 1 (by rfl) ⟨20882204, by rfl⟩ : syracuseStep 27842939 = 41764409) B41764409
theorem B18561959 : Blo 2257435 18561959 := bstep (se 1 (by rfl) ⟨13921469, by rfl⟩ : syracuseStep 18561959 = 27842939) B27842939
theorem B12374639 : Blo 2257435 12374639 := bstep (se 1 (by rfl) ⟨9280979, by rfl⟩ : syracuseStep 12374639 = 18561959) B18561959
theorem B8249759 : Blo 2257435 8249759 := bstep (se 1 (by rfl) ⟨6187319, by rfl⟩ : syracuseStep 8249759 = 12374639) B12374639
theorem B5499839 : Blo 2257435 5499839 := bstep (se 1 (by rfl) ⟨4124879, by rfl⟩ : syracuseStep 5499839 = 8249759) B8249759
theorem B3666559 : Blo 2257435 3666559 := bstep (se 1 (by rfl) ⟨2749919, by rfl⟩ : syracuseStep 3666559 = 5499839) B5499839
theorem B4888745 : Blo 2257435 4888745 := bstep (se 2 (by rfl) ⟨1833279, by rfl⟩ : syracuseStep 4888745 = 3666559) B3666559
theorem B3259163 : Blo 2257435 3259163 := bstep (se 1 (by rfl) ⟨2444372, by rfl⟩ : syracuseStep 3259163 = 4888745) B4888745
theorem B8691101 : Blo 2257435 8691101 := bstep (se 3 (by rfl) ⟨1629581, by rfl⟩ : syracuseStep 8691101 = 3259163) B3259163
theorem B5794067 : Blo 2257435 5794067 := bstep (se 1 (by rfl) ⟨4345550, by rfl⟩ : syracuseStep 5794067 = 8691101) B8691101
theorem B3862711 : Blo 2257435 3862711 := bstep (se 1 (by rfl) ⟨2897033, by rfl⟩ : syracuseStep 3862711 = 5794067) B5794067
theorem B20601125 : Blo 2257435 20601125 := bstep (se 4 (by rfl) ⟨1931355, by rfl⟩ : syracuseStep 20601125 = 3862711) B3862711
theorem B13734083 : Blo 2257435 13734083 := bstep (se 1 (by rfl) ⟨10300562, by rfl⟩ : syracuseStep 13734083 = 20601125) B20601125
theorem B36624221 : Blo 2257435 36624221 := bstep (se 3 (by rfl) ⟨6867041, by rfl⟩ : syracuseStep 36624221 = 13734083) B13734083
theorem B24416147 : Blo 2257435 24416147 := bstep (se 1 (by rfl) ⟨18312110, by rfl⟩ : syracuseStep 24416147 = 36624221) B36624221
theorem B16277431 : Blo 2257435 16277431 := bstep (se 1 (by rfl) ⟨12208073, by rfl⟩ : syracuseStep 16277431 = 24416147) B24416147
theorem B21703241 : Blo 2257435 21703241 := bstep (se 2 (by rfl) ⟨8138715, by rfl⟩ : syracuseStep 21703241 = 16277431) B16277431
theorem B14468827 : Blo 2257435 14468827 := bstep (se 1 (by rfl) ⟨10851620, by rfl⟩ : syracuseStep 14468827 = 21703241) B21703241
theorem B19291769 : Blo 2257435 19291769 := bstep (se 2 (by rfl) ⟨7234413, by rfl⟩ : syracuseStep 19291769 = 14468827) B14468827
theorem B12861179 : Blo 2257435 12861179 := bstep (se 1 (by rfl) ⟨9645884, by rfl⟩ : syracuseStep 12861179 = 19291769) B19291769
theorem B8574119 : Blo 2257435 8574119 := bstep (se 1 (by rfl) ⟨6430589, by rfl⟩ : syracuseStep 8574119 = 12861179) B12861179
theorem B5716079 : Blo 2257435 5716079 := bstep (se 1 (by rfl) ⟨4287059, by rfl⟩ : syracuseStep 5716079 = 8574119) B8574119
theorem B3810719 : Blo 2257435 3810719 := bstep (se 1 (by rfl) ⟨2858039, by rfl⟩ : syracuseStep 3810719 = 5716079) B5716079
theorem B2540479 : Blo 2257435 2540479 := bstep (se 1 (by rfl) ⟨1905359, by rfl⟩ : syracuseStep 2540479 = 3810719) B3810719
theorem B3387305 : Blo 2257435 3387305 := bstep (se 2 (by rfl) ⟨1270239, by rfl⟩ : syracuseStep 3387305 = 2540479) B2540479
theorem B2258203 : Blo 2257435 2258203 := bstep (se 1 (by rfl) ⟨1693652, by rfl⟩ : syracuseStep 2258203 = 3387305) B3387305
theorem B8574133 : Blo 2257435 8574133 := bbase (se 5 (by rfl) ⟨401912, by rfl⟩ : syracuseStep 8574133 = 803825) (by norm_num)
theorem B11432177 : Blo 2257435 11432177 := bstep (se 2 (by rfl) ⟨4287066, by rfl⟩ : syracuseStep 11432177 = 8574133) B8574133
theorem B7621451 : Blo 2257435 7621451 := bstep (se 1 (by rfl) ⟨5716088, by rfl⟩ : syracuseStep 7621451 = 11432177) B11432177
theorem B5080967 : Blo 2257435 5080967 := bstep (se 1 (by rfl) ⟨3810725, by rfl⟩ : syracuseStep 5080967 = 7621451) B7621451
theorem B3387311 : Blo 2257435 3387311 := bstep (se 1 (by rfl) ⟨2540483, by rfl⟩ : syracuseStep 3387311 = 5080967) B5080967
theorem B2258207 : Blo 2257435 2258207 := bstep (se 1 (by rfl) ⟨1693655, by rfl⟩ : syracuseStep 2258207 = 3387311) B3387311
theorem B3387317 : Blo 2257435 3387317 := bbase (se 5 (by rfl) ⟨158780, by rfl⟩ : syracuseStep 3387317 = 317561) (by norm_num)
theorem B2258211 : Blo 2257435 2258211 := bstep (se 1 (by rfl) ⟨1693658, by rfl⟩ : syracuseStep 2258211 = 3387317) B3387317
theorem B5716109 : Blo 2257435 5716109 := bbase (se 3 (by rfl) ⟨1071770, by rfl⟩ : syracuseStep 5716109 = 2143541) (by norm_num)
theorem B3810739 : Blo 2257435 3810739 := bstep (se 1 (by rfl) ⟨2858054, by rfl⟩ : syracuseStep 3810739 = 5716109) B5716109
theorem B5080985 : Blo 2257435 5080985 := bstep (se 2 (by rfl) ⟨1905369, by rfl⟩ : syracuseStep 5080985 = 3810739) B3810739
theorem B3387323 : Blo 2257435 3387323 := bstep (se 1 (by rfl) ⟨2540492, by rfl⟩ : syracuseStep 3387323 = 5080985) B5080985
theorem B2258215 : Blo 2257435 2258215 := bstep (se 1 (by rfl) ⟨1693661, by rfl⟩ : syracuseStep 2258215 = 3387323) B3387323
theorem B2540497 : Blo 2257435 2540497 := bbase (se 2 (by rfl) ⟨952686, by rfl⟩ : syracuseStep 2540497 = 1905373) (by norm_num)
theorem B3387329 : Blo 2257435 3387329 := bstep (se 2 (by rfl) ⟨1270248, by rfl⟩ : syracuseStep 3387329 = 2540497) B2540497
theorem B2258219 : Blo 2257435 2258219 := bstep (se 1 (by rfl) ⟨1693664, by rfl⟩ : syracuseStep 2258219 = 3387329) B3387329
theorem B8138789 : Blo 2257435 8138789 := bbase (se 4 (by rfl) ⟨763011, by rfl⟩ : syracuseStep 8138789 = 1526023) (by norm_num)
theorem B5425859 : Blo 2257435 5425859 := bstep (se 1 (by rfl) ⟨4069394, by rfl⟩ : syracuseStep 5425859 = 8138789) B8138789
theorem B3617239 : Blo 2257435 3617239 := bstep (se 1 (by rfl) ⟨2712929, by rfl⟩ : syracuseStep 3617239 = 5425859) B5425859
theorem B4822985 : Blo 2257435 4822985 := bstep (se 2 (by rfl) ⟨1808619, by rfl⟩ : syracuseStep 4822985 = 3617239) B3617239
theorem B3215323 : Blo 2257435 3215323 := bstep (se 1 (by rfl) ⟨2411492, by rfl⟩ : syracuseStep 3215323 = 4822985) B4822985
theorem B4287097 : Blo 2257435 4287097 := bstep (se 2 (by rfl) ⟨1607661, by rfl⟩ : syracuseStep 4287097 = 3215323) B3215323
theorem B5716129 : Blo 2257435 5716129 := bstep (se 2 (by rfl) ⟨2143548, by rfl⟩ : syracuseStep 5716129 = 4287097) B4287097
theorem B7621505 : Blo 2257435 7621505 := bstep (se 2 (by rfl) ⟨2858064, by rfl⟩ : syracuseStep 7621505 = 5716129) B5716129
theorem B5081003 : Blo 2257435 5081003 := bstep (se 1 (by rfl) ⟨3810752, by rfl⟩ : syracuseStep 5081003 = 7621505) B7621505
theorem B3387335 : Blo 2257435 3387335 := bstep (se 1 (by rfl) ⟨2540501, by rfl⟩ : syracuseStep 3387335 = 5081003) B5081003
theorem B2258223 : Blo 2257435 2258223 := bstep (se 1 (by rfl) ⟨1693667, by rfl⟩ : syracuseStep 2258223 = 3387335) B3387335
theorem B3387341 : Blo 2257435 3387341 := bbase (se 3 (by rfl) ⟨635126, by rfl⟩ : syracuseStep 3387341 = 1270253) (by norm_num)
theorem B2258227 : Blo 2257435 2258227 := bstep (se 1 (by rfl) ⟨1693670, by rfl⟩ : syracuseStep 2258227 = 3387341) B3387341
theorem B5081021 : Blo 2257435 5081021 := bbase (se 3 (by rfl) ⟨952691, by rfl⟩ : syracuseStep 5081021 = 1905383) (by norm_num)
theorem B3387347 : Blo 2257435 3387347 := bstep (se 1 (by rfl) ⟨2540510, by rfl⟩ : syracuseStep 3387347 = 5081021) B5081021
theorem B2258231 : Blo 2257435 2258231 := bstep (se 1 (by rfl) ⟨1693673, by rfl⟩ : syracuseStep 2258231 = 3387347) B3387347
theorem B3810773 : Blo 2257435 3810773 := bbase (se 7 (by rfl) ⟨44657, by rfl⟩ : syracuseStep 3810773 = 89315) (by norm_num)
theorem B2540515 : Blo 2257435 2540515 := bstep (se 1 (by rfl) ⟨1905386, by rfl⟩ : syracuseStep 2540515 = 3810773) B3810773
theorem B3387353 : Blo 2257435 3387353 := bstep (se 2 (by rfl) ⟨1270257, by rfl⟩ : syracuseStep 3387353 = 2540515) B2540515
theorem B2258235 : Blo 2257435 2258235 := bstep (se 1 (by rfl) ⟨1693676, by rfl⟩ : syracuseStep 2258235 = 3387353) B3387353
theorem B9646037 : Blo 2257435 9646037 := bbase (se 7 (by rfl) ⟨113039, by rfl⟩ : syracuseStep 9646037 = 226079) (by norm_num)
theorem B6430691 : Blo 2257435 6430691 := bstep (se 1 (by rfl) ⟨4823018, by rfl⟩ : syracuseStep 6430691 = 9646037) B9646037
theorem B17148509 : Blo 2257435 17148509 := bstep (se 3 (by rfl) ⟨3215345, by rfl⟩ : syracuseStep 17148509 = 6430691) B6430691
theorem B11432339 : Blo 2257435 11432339 := bstep (se 1 (by rfl) ⟨8574254, by rfl⟩ : syracuseStep 11432339 = 17148509) B17148509
theorem B7621559 : Blo 2257435 7621559 := bstep (se 1 (by rfl) ⟨5716169, by rfl⟩ : syracuseStep 7621559 = 11432339) B11432339
theorem B5081039 : Blo 2257435 5081039 := bstep (se 1 (by rfl) ⟨3810779, by rfl⟩ : syracuseStep 5081039 = 7621559) B7621559
theorem B3387359 : Blo 2257435 3387359 := bstep (se 1 (by rfl) ⟨2540519, by rfl⟩ : syracuseStep 3387359 = 5081039) B5081039
theorem B2258239 : Blo 2257435 2258239 := bstep (se 1 (by rfl) ⟨1693679, by rfl⟩ : syracuseStep 2258239 = 3387359) B3387359
theorem B3387365 : Blo 2257435 3387365 := bbase (se 4 (by rfl) ⟨317565, by rfl⟩ : syracuseStep 3387365 = 635131) (by norm_num)
theorem B2258243 : Blo 2257435 2258243 := bstep (se 1 (by rfl) ⟨1693682, by rfl⟩ : syracuseStep 2258243 = 3387365) B3387365
theorem B5794181 : Blo 2257435 5794181 := bbase (se 4 (by rfl) ⟨543204, by rfl⟩ : syracuseStep 5794181 = 1086409) (by norm_num)
theorem B3862787 : Blo 2257435 3862787 := bstep (se 1 (by rfl) ⟨2897090, by rfl⟩ : syracuseStep 3862787 = 5794181) B5794181
theorem B10300765 : Blo 2257435 10300765 := bstep (se 3 (by rfl) ⟨1931393, by rfl⟩ : syracuseStep 10300765 = 3862787) B3862787
theorem B13734353 : Blo 2257435 13734353 := bstep (se 2 (by rfl) ⟨5150382, by rfl⟩ : syracuseStep 13734353 = 10300765) B10300765
theorem B9156235 : Blo 2257435 9156235 := bstep (se 1 (by rfl) ⟨6867176, by rfl⟩ : syracuseStep 9156235 = 13734353) B13734353
theorem B12208313 : Blo 2257435 12208313 := bstep (se 2 (by rfl) ⟨4578117, by rfl⟩ : syracuseStep 12208313 = 9156235) B9156235
theorem B8138875 : Blo 2257435 8138875 := bstep (se 1 (by rfl) ⟨6104156, by rfl⟩ : syracuseStep 8138875 = 12208313) B12208313
theorem B10851833 : Blo 2257435 10851833 := bstep (se 2 (by rfl) ⟨4069437, by rfl⟩ : syracuseStep 10851833 = 8138875) B8138875
theorem B7234555 : Blo 2257435 7234555 := bstep (se 1 (by rfl) ⟨5425916, by rfl⟩ : syracuseStep 7234555 = 10851833) B10851833
theorem B9646073 : Blo 2257435 9646073 := bstep (se 2 (by rfl) ⟨3617277, by rfl⟩ : syracuseStep 9646073 = 7234555) B7234555
theorem B6430715 : Blo 2257435 6430715 := bstep (se 1 (by rfl) ⟨4823036, by rfl⟩ : syracuseStep 6430715 = 9646073) B9646073
theorem B4287143 : Blo 2257435 4287143 := bstep (se 1 (by rfl) ⟨3215357, by rfl⟩ : syracuseStep 4287143 = 6430715) B6430715
theorem B2858095 : Blo 2257435 2858095 := bstep (se 1 (by rfl) ⟨2143571, by rfl⟩ : syracuseStep 2858095 = 4287143) B4287143
theorem B3810793 : Blo 2257435 3810793 := bstep (se 2 (by rfl) ⟨1429047, by rfl⟩ : syracuseStep 3810793 = 2858095) B2858095
theorem B5081057 : Blo 2257435 5081057 := bstep (se 2 (by rfl) ⟨1905396, by rfl⟩ : syracuseStep 5081057 = 3810793) B3810793
theorem B3387371 : Blo 2257435 3387371 := bstep (se 1 (by rfl) ⟨2540528, by rfl⟩ : syracuseStep 3387371 = 5081057) B5081057
theorem B2258247 : Blo 2257435 2258247 := bstep (se 1 (by rfl) ⟨1693685, by rfl⟩ : syracuseStep 2258247 = 3387371) B3387371
theorem B2540533 : Blo 2257435 2540533 := bbase (se 5 (by rfl) ⟨119087, by rfl⟩ : syracuseStep 2540533 = 238175) (by norm_num)
theorem B3387377 : Blo 2257435 3387377 := bstep (se 2 (by rfl) ⟨1270266, by rfl⟩ : syracuseStep 3387377 = 2540533) B2540533
theorem B2258251 : Blo 2257435 2258251 := bstep (se 1 (by rfl) ⟨1693688, by rfl⟩ : syracuseStep 2258251 = 3387377) B3387377
theorem B2858105 : Blo 2257435 2858105 := bbase (se 2 (by rfl) ⟨1071789, by rfl⟩ : syracuseStep 2858105 = 2143579) (by norm_num)
theorem B7621613 : Blo 2257435 7621613 := bstep (se 3 (by rfl) ⟨1429052, by rfl⟩ : syracuseStep 7621613 = 2858105) B2858105
theorem B5081075 : Blo 2257435 5081075 := bstep (se 1 (by rfl) ⟨3810806, by rfl⟩ : syracuseStep 5081075 = 7621613) B7621613
theorem B3387383 : Blo 2257435 3387383 := bstep (se 1 (by rfl) ⟨2540537, by rfl⟩ : syracuseStep 3387383 = 5081075) B5081075
theorem B2258255 : Blo 2257435 2258255 := bstep (se 1 (by rfl) ⟨1693691, by rfl⟩ : syracuseStep 2258255 = 3387383) B3387383
theorem B3387389 : Blo 2257435 3387389 := bbase (se 3 (by rfl) ⟨635135, by rfl⟩ : syracuseStep 3387389 = 1270271) (by norm_num)
theorem B2258259 : Blo 2257435 2258259 := bstep (se 1 (by rfl) ⟨1693694, by rfl⟩ : syracuseStep 2258259 = 3387389) B3387389
theorem B5081093 : Blo 2257435 5081093 := bbase (se 4 (by rfl) ⟨476352, by rfl⟩ : syracuseStep 5081093 = 952705) (by norm_num)
theorem B3387395 : Blo 2257435 3387395 := bstep (se 1 (by rfl) ⟨2540546, by rfl⟩ : syracuseStep 3387395 = 5081093) B5081093
theorem B2258263 : Blo 2257435 2258263 := bstep (se 1 (by rfl) ⟨1693697, by rfl⟩ : syracuseStep 2258263 = 3387395) B3387395
theorem B4287181 : Blo 2257435 4287181 := bbase (se 3 (by rfl) ⟨803846, by rfl⟩ : syracuseStep 4287181 = 1607693) (by norm_num)
theorem B5716241 : Blo 2257435 5716241 := bstep (se 2 (by rfl) ⟨2143590, by rfl⟩ : syracuseStep 5716241 = 4287181) B4287181
theorem B3810827 : Blo 2257435 3810827 := bstep (se 1 (by rfl) ⟨2858120, by rfl⟩ : syracuseStep 3810827 = 5716241) B5716241
theorem B2540551 : Blo 2257435 2540551 := bstep (se 1 (by rfl) ⟨1905413, by rfl⟩ : syracuseStep 2540551 = 3810827) B3810827
theorem B3387401 : Blo 2257435 3387401 := bstep (se 2 (by rfl) ⟨1270275, by rfl⟩ : syracuseStep 3387401 = 2540551) B2540551
theorem B2258267 : Blo 2257435 2258267 := bstep (se 1 (by rfl) ⟨1693700, by rfl⟩ : syracuseStep 2258267 = 3387401) B3387401
theorem B11432501 : Blo 2257435 11432501 := bbase (se 5 (by rfl) ⟨535898, by rfl⟩ : syracuseStep 11432501 = 1071797) (by norm_num)
theorem B7621667 : Blo 2257435 7621667 := bstep (se 1 (by rfl) ⟨5716250, by rfl⟩ : syracuseStep 7621667 = 11432501) B11432501
theorem B5081111 : Blo 2257435 5081111 := bstep (se 1 (by rfl) ⟨3810833, by rfl⟩ : syracuseStep 5081111 = 7621667) B7621667
theorem B3387407 : Blo 2257435 3387407 := bstep (se 1 (by rfl) ⟨2540555, by rfl⟩ : syracuseStep 3387407 = 5081111) B5081111
theorem B2258271 : Blo 2257435 2258271 := bstep (se 1 (by rfl) ⟨1693703, by rfl⟩ : syracuseStep 2258271 = 3387407) B3387407
theorem B3387413 : Blo 2257435 3387413 := bbase (se 6 (by rfl) ⟨79392, by rfl⟩ : syracuseStep 3387413 = 158785) (by norm_num)
theorem B2258275 : Blo 2257435 2258275 := bstep (se 1 (by rfl) ⟨1693706, by rfl⟩ : syracuseStep 2258275 = 3387413) B3387413
theorem B3433637 : Blo 2257435 3433637 := bbase (se 4 (by rfl) ⟨321903, by rfl⟩ : syracuseStep 3433637 = 643807) (by norm_num)
theorem B2289091 : Blo 2257435 2289091 := bstep (se 1 (by rfl) ⟨1716818, by rfl⟩ : syracuseStep 2289091 = 3433637) B3433637
theorem B3052121 : Blo 2257435 3052121 := bstep (se 2 (by rfl) ⟨1144545, by rfl⟩ : syracuseStep 3052121 = 2289091) B2289091
theorem B8138989 : Blo 2257435 8138989 := bstep (se 3 (by rfl) ⟨1526060, by rfl⟩ : syracuseStep 8138989 = 3052121) B3052121
theorem B10851985 : Blo 2257435 10851985 := bstep (se 2 (by rfl) ⟨4069494, by rfl⟩ : syracuseStep 10851985 = 8138989) B8138989
theorem B14469313 : Blo 2257435 14469313 := bstep (se 2 (by rfl) ⟨5425992, by rfl⟩ : syracuseStep 14469313 = 10851985) B10851985
theorem B19292417 : Blo 2257435 19292417 := bstep (se 2 (by rfl) ⟨7234656, by rfl⟩ : syracuseStep 19292417 = 14469313) B14469313
theorem B12861611 : Blo 2257435 12861611 := bstep (se 1 (by rfl) ⟨9646208, by rfl⟩ : syracuseStep 12861611 = 19292417) B19292417
theorem B8574407 : Blo 2257435 8574407 := bstep (se 1 (by rfl) ⟨6430805, by rfl⟩ : syracuseStep 8574407 = 12861611) B12861611
theorem B5716271 : Blo 2257435 5716271 := bstep (se 1 (by rfl) ⟨4287203, by rfl⟩ : syracuseStep 5716271 = 8574407) B8574407
theorem B3810847 : Blo 2257435 3810847 := bstep (se 1 (by rfl) ⟨2858135, by rfl⟩ : syracuseStep 3810847 = 5716271) B5716271
theorem B5081129 : Blo 2257435 5081129 := bstep (se 2 (by rfl) ⟨1905423, by rfl⟩ : syracuseStep 5081129 = 3810847) B3810847
theorem B3387419 : Blo 2257435 3387419 := bstep (se 1 (by rfl) ⟨2540564, by rfl⟩ : syracuseStep 3387419 = 5081129) B5081129
theorem B2258279 : Blo 2257435 2258279 := bstep (se 1 (by rfl) ⟨1693709, by rfl⟩ : syracuseStep 2258279 = 3387419) B3387419
theorem B2540569 : Blo 2257435 2540569 := bbase (se 2 (by rfl) ⟨952713, by rfl⟩ : syracuseStep 2540569 = 1905427) (by norm_num)
theorem B3387425 : Blo 2257435 3387425 := bstep (se 2 (by rfl) ⟨1270284, by rfl⟩ : syracuseStep 3387425 = 2540569) B2540569
theorem B2258283 : Blo 2257435 2258283 := bstep (se 1 (by rfl) ⟨1693712, by rfl⟩ : syracuseStep 2258283 = 3387425) B3387425
theorem B8574437 : Blo 2257435 8574437 := bbase (se 4 (by rfl) ⟨803853, by rfl⟩ : syracuseStep 8574437 = 1607707) (by norm_num)
theorem B5716291 : Blo 2257435 5716291 := bstep (se 1 (by rfl) ⟨4287218, by rfl⟩ : syracuseStep 5716291 = 8574437) B8574437
theorem B7621721 : Blo 2257435 7621721 := bstep (se 2 (by rfl) ⟨2858145, by rfl⟩ : syracuseStep 7621721 = 5716291) B5716291
theorem B5081147 : Blo 2257435 5081147 := bstep (se 1 (by rfl) ⟨3810860, by rfl⟩ : syracuseStep 5081147 = 7621721) B7621721
theorem B3387431 : Blo 2257435 3387431 := bstep (se 1 (by rfl) ⟨2540573, by rfl⟩ : syracuseStep 3387431 = 5081147) B5081147
theorem B2258287 : Blo 2257435 2258287 := bstep (se 1 (by rfl) ⟨1693715, by rfl⟩ : syracuseStep 2258287 = 3387431) B3387431
theorem B3387437 : Blo 2257435 3387437 := bbase (se 3 (by rfl) ⟨635144, by rfl⟩ : syracuseStep 3387437 = 1270289) (by norm_num)
theorem B2258291 : Blo 2257435 2258291 := bstep (se 1 (by rfl) ⟨1693718, by rfl⟩ : syracuseStep 2258291 = 3387437) B3387437
theorem B5081165 : Blo 2257435 5081165 := bbase (se 3 (by rfl) ⟨952718, by rfl⟩ : syracuseStep 5081165 = 1905437) (by norm_num)
theorem B3387443 : Blo 2257435 3387443 := bstep (se 1 (by rfl) ⟨2540582, by rfl⟩ : syracuseStep 3387443 = 5081165) B5081165
theorem B2258295 : Blo 2257435 2258295 := bstep (se 1 (by rfl) ⟨1693721, by rfl⟩ : syracuseStep 2258295 = 3387443) B3387443
theorem B2858161 : Blo 2257435 2858161 := bbase (se 2 (by rfl) ⟨1071810, by rfl⟩ : syracuseStep 2858161 = 2143621) (by norm_num)
theorem B3810881 : Blo 2257435 3810881 := bstep (se 2 (by rfl) ⟨1429080, by rfl⟩ : syracuseStep 3810881 = 2858161) B2858161
theorem B2540587 : Blo 2257435 2540587 := bstep (se 1 (by rfl) ⟨1905440, by rfl⟩ : syracuseStep 2540587 = 3810881) B3810881
theorem B3387449 : Blo 2257435 3387449 := bstep (se 2 (by rfl) ⟨1270293, by rfl⟩ : syracuseStep 3387449 = 2540587) B2540587
theorem B2258299 : Blo 2257435 2258299 := bstep (se 1 (by rfl) ⟨1693724, by rfl⟩ : syracuseStep 2258299 = 3387449) B3387449
theorem B2713025 : Blo 2257435 2713025 := bbase (se 2 (by rfl) ⟨1017384, by rfl⟩ : syracuseStep 2713025 = 2034769) (by norm_num)
theorem B7234733 : Blo 2257435 7234733 := bstep (se 3 (by rfl) ⟨1356512, by rfl⟩ : syracuseStep 7234733 = 2713025) B2713025
theorem B4823155 : Blo 2257435 4823155 := bstep (se 1 (by rfl) ⟨3617366, by rfl⟩ : syracuseStep 4823155 = 7234733) B7234733
theorem B25723493 : Blo 2257435 25723493 := bstep (se 4 (by rfl) ⟨2411577, by rfl⟩ : syracuseStep 25723493 = 4823155) B4823155
theorem B17148995 : Blo 2257435 17148995 := bstep (se 1 (by rfl) ⟨12861746, by rfl⟩ : syracuseStep 17148995 = 25723493) B25723493
theorem B11432663 : Blo 2257435 11432663 := bstep (se 1 (by rfl) ⟨8574497, by rfl⟩ : syracuseStep 11432663 = 17148995) B17148995
theorem B7621775 : Blo 2257435 7621775 := bstep (se 1 (by rfl) ⟨5716331, by rfl⟩ : syracuseStep 7621775 = 11432663) B11432663
theorem B5081183 : Blo 2257435 5081183 := bstep (se 1 (by rfl) ⟨3810887, by rfl⟩ : syracuseStep 5081183 = 7621775) B7621775
theorem B3387455 : Blo 2257435 3387455 := bstep (se 1 (by rfl) ⟨2540591, by rfl⟩ : syracuseStep 3387455 = 5081183) B5081183
theorem B2258303 : Blo 2257435 2258303 := bstep (se 1 (by rfl) ⟨1693727, by rfl⟩ : syracuseStep 2258303 = 3387455) B3387455
theorem B3387461 : Blo 2257435 3387461 := bbase (se 4 (by rfl) ⟨317574, by rfl⟩ : syracuseStep 3387461 = 635149) (by norm_num)
theorem B2258307 : Blo 2257435 2258307 := bstep (se 1 (by rfl) ⟨1693730, by rfl⟩ : syracuseStep 2258307 = 3387461) B3387461
theorem B3810901 : Blo 2257435 3810901 := bbase (se 8 (by rfl) ⟨22329, by rfl⟩ : syracuseStep 3810901 = 44659) (by norm_num)
theorem B5081201 : Blo 2257435 5081201 := bstep (se 2 (by rfl) ⟨1905450, by rfl⟩ : syracuseStep 5081201 = 3810901) B3810901
theorem B3387467 : Blo 2257435 3387467 := bstep (se 1 (by rfl) ⟨2540600, by rfl⟩ : syracuseStep 3387467 = 5081201) B5081201
theorem B2258311 : Blo 2257435 2258311 := bstep (se 1 (by rfl) ⟨1693733, by rfl⟩ : syracuseStep 2258311 = 3387467) B3387467
theorem B2540605 : Blo 2257435 2540605 := bbase (se 3 (by rfl) ⟨476363, by rfl⟩ : syracuseStep 2540605 = 952727) (by norm_num)
theorem B3387473 : Blo 2257435 3387473 := bstep (se 2 (by rfl) ⟨1270302, by rfl⟩ : syracuseStep 3387473 = 2540605) B2540605
theorem B2258315 : Blo 2257435 2258315 := bstep (se 1 (by rfl) ⟨1693736, by rfl⟩ : syracuseStep 2258315 = 3387473) B3387473
theorem B7621829 : Blo 2257435 7621829 := bbase (se 4 (by rfl) ⟨714546, by rfl⟩ : syracuseStep 7621829 = 1429093) (by norm_num)
theorem B5081219 : Blo 2257435 5081219 := bstep (se 1 (by rfl) ⟨3810914, by rfl⟩ : syracuseStep 5081219 = 7621829) B7621829
theorem B3387479 : Blo 2257435 3387479 := bstep (se 1 (by rfl) ⟨2540609, by rfl⟩ : syracuseStep 3387479 = 5081219) B5081219
theorem B2258319 : Blo 2257435 2258319 := bstep (se 1 (by rfl) ⟨1693739, by rfl⟩ : syracuseStep 2258319 = 3387479) B3387479
theorem B3387485 : Blo 2257435 3387485 := bbase (se 3 (by rfl) ⟨635153, by rfl⟩ : syracuseStep 3387485 = 1270307) (by norm_num)
theorem B2258323 : Blo 2257435 2258323 := bstep (se 1 (by rfl) ⟨1693742, by rfl⟩ : syracuseStep 2258323 = 3387485) B3387485
theorem B5081237 : Blo 2257435 5081237 := bbase (se 6 (by rfl) ⟨119091, by rfl⟩ : syracuseStep 5081237 = 238183) (by norm_num)
theorem B3387491 : Blo 2257435 3387491 := bstep (se 1 (by rfl) ⟨2540618, by rfl⟩ : syracuseStep 3387491 = 5081237) B5081237
theorem B2258327 : Blo 2257435 2258327 := bstep (se 1 (by rfl) ⟨1693745, by rfl⟩ : syracuseStep 2258327 = 3387491) B3387491
theorem B3215477 : Blo 2257435 3215477 := bbase (se 5 (by rfl) ⟨150725, by rfl⟩ : syracuseStep 3215477 = 301451) (by norm_num)
theorem B8574605 : Blo 2257435 8574605 := bstep (se 3 (by rfl) ⟨1607738, by rfl⟩ : syracuseStep 8574605 = 3215477) B3215477
theorem B5716403 : Blo 2257435 5716403 := bstep (se 1 (by rfl) ⟨4287302, by rfl⟩ : syracuseStep 5716403 = 8574605) B8574605
theorem B3810935 : Blo 2257435 3810935 := bstep (se 1 (by rfl) ⟨2858201, by rfl⟩ : syracuseStep 3810935 = 5716403) B5716403
theorem B2540623 : Blo 2257435 2540623 := bstep (se 1 (by rfl) ⟨1905467, by rfl⟩ : syracuseStep 2540623 = 3810935) B3810935
theorem B3387497 : Blo 2257435 3387497 := bstep (se 2 (by rfl) ⟨1270311, by rfl⟩ : syracuseStep 3387497 = 2540623) B2540623
theorem B2258331 : Blo 2257435 2258331 := bstep (se 1 (by rfl) ⟨1693748, by rfl⟩ : syracuseStep 2258331 = 3387497) B3387497
theorem B4345805 : Blo 2257435 4345805 := bbase (se 3 (by rfl) ⟨814838, by rfl⟩ : syracuseStep 4345805 = 1629677) (by norm_num)
theorem B2897203 : Blo 2257435 2897203 := bstep (se 1 (by rfl) ⟨2172902, by rfl⟩ : syracuseStep 2897203 = 4345805) B4345805
theorem B3862937 : Blo 2257435 3862937 := bstep (se 2 (by rfl) ⟨1448601, by rfl⟩ : syracuseStep 3862937 = 2897203) B2897203
theorem B2575291 : Blo 2257435 2575291 := bstep (se 1 (by rfl) ⟨1931468, by rfl⟩ : syracuseStep 2575291 = 3862937) B3862937
theorem B3433721 : Blo 2257435 3433721 := bstep (se 2 (by rfl) ⟨1287645, by rfl⟩ : syracuseStep 3433721 = 2575291) B2575291
theorem B36626357 : Blo 2257435 36626357 := bstep (se 5 (by rfl) ⟨1716860, by rfl⟩ : syracuseStep 36626357 = 3433721) B3433721
theorem B24417571 : Blo 2257435 24417571 := bstep (se 1 (by rfl) ⟨18313178, by rfl⟩ : syracuseStep 24417571 = 36626357) B36626357
theorem B32556761 : Blo 2257435 32556761 := bstep (se 2 (by rfl) ⟨12208785, by rfl⟩ : syracuseStep 32556761 = 24417571) B24417571
theorem B21704507 : Blo 2257435 21704507 := bstep (se 1 (by rfl) ⟨16278380, by rfl⟩ : syracuseStep 21704507 = 32556761) B32556761
theorem B14469671 : Blo 2257435 14469671 := bstep (se 1 (by rfl) ⟨10852253, by rfl⟩ : syracuseStep 14469671 = 21704507) B21704507
theorem B9646447 : Blo 2257435 9646447 := bstep (se 1 (by rfl) ⟨7234835, by rfl⟩ : syracuseStep 9646447 = 14469671) B14469671
theorem B12861929 : Blo 2257435 12861929 := bstep (se 2 (by rfl) ⟨4823223, by rfl⟩ : syracuseStep 12861929 = 9646447) B9646447
theorem B8574619 : Blo 2257435 8574619 := bstep (se 1 (by rfl) ⟨6430964, by rfl⟩ : syracuseStep 8574619 = 12861929) B12861929
theorem B11432825 : Blo 2257435 11432825 := bstep (se 2 (by rfl) ⟨4287309, by rfl⟩ : syracuseStep 11432825 = 8574619) B8574619
theorem B7621883 : Blo 2257435 7621883 := bstep (se 1 (by rfl) ⟨5716412, by rfl⟩ : syracuseStep 7621883 = 11432825) B11432825
theorem B5081255 : Blo 2257435 5081255 := bstep (se 1 (by rfl) ⟨3810941, by rfl⟩ : syracuseStep 5081255 = 7621883) B7621883
theorem B3387503 : Blo 2257435 3387503 := bstep (se 1 (by rfl) ⟨2540627, by rfl⟩ : syracuseStep 3387503 = 5081255) B5081255
theorem B2258335 : Blo 2257435 2258335 := bstep (se 1 (by rfl) ⟨1693751, by rfl⟩ : syracuseStep 2258335 = 3387503) B3387503
theorem B3387509 : Blo 2257435 3387509 := bbase (se 5 (by rfl) ⟨158789, by rfl⟩ : syracuseStep 3387509 = 317579) (by norm_num)
theorem B2258339 : Blo 2257435 2258339 := bstep (se 1 (by rfl) ⟨1693754, by rfl⟩ : syracuseStep 2258339 = 3387509) B3387509
theorem B4287325 : Blo 2257435 4287325 := bbase (se 3 (by rfl) ⟨803873, by rfl⟩ : syracuseStep 4287325 = 1607747) (by norm_num)
theorem B5716433 : Blo 2257435 5716433 := bstep (se 2 (by rfl) ⟨2143662, by rfl⟩ : syracuseStep 5716433 = 4287325) B4287325
theorem B3810955 : Blo 2257435 3810955 := bstep (se 1 (by rfl) ⟨2858216, by rfl⟩ : syracuseStep 3810955 = 5716433) B5716433
theorem B5081273 : Blo 2257435 5081273 := bstep (se 2 (by rfl) ⟨1905477, by rfl⟩ : syracuseStep 5081273 = 3810955) B3810955
theorem B3387515 : Blo 2257435 3387515 := bstep (se 1 (by rfl) ⟨2540636, by rfl⟩ : syracuseStep 3387515 = 5081273) B5081273
theorem B2258343 : Blo 2257435 2258343 := bstep (se 1 (by rfl) ⟨1693757, by rfl⟩ : syracuseStep 2258343 = 3387515) B3387515
theorem B2540641 : Blo 2257435 2540641 := bbase (se 2 (by rfl) ⟨952740, by rfl⟩ : syracuseStep 2540641 = 1905481) (by norm_num)
theorem B3387521 : Blo 2257435 3387521 := bstep (se 2 (by rfl) ⟨1270320, by rfl⟩ : syracuseStep 3387521 = 2540641) B2540641
theorem B2258347 : Blo 2257435 2258347 := bstep (se 1 (by rfl) ⟨1693760, by rfl⟩ : syracuseStep 2258347 = 3387521) B3387521
theorem B5716453 : Blo 2257435 5716453 := bbase (se 4 (by rfl) ⟨535917, by rfl⟩ : syracuseStep 5716453 = 1071835) (by norm_num)
theorem B7621937 : Blo 2257435 7621937 := bstep (se 2 (by rfl) ⟨2858226, by rfl⟩ : syracuseStep 7621937 = 5716453) B5716453
theorem B5081291 : Blo 2257435 5081291 := bstep (se 1 (by rfl) ⟨3810968, by rfl⟩ : syracuseStep 5081291 = 7621937) B7621937
theorem B3387527 : Blo 2257435 3387527 := bstep (se 1 (by rfl) ⟨2540645, by rfl⟩ : syracuseStep 3387527 = 5081291) B5081291
theorem B2258351 : Blo 2257435 2258351 := bstep (se 1 (by rfl) ⟨1693763, by rfl⟩ : syracuseStep 2258351 = 3387527) B3387527
theorem B3387533 : Blo 2257435 3387533 := bbase (se 3 (by rfl) ⟨635162, by rfl⟩ : syracuseStep 3387533 = 1270325) (by norm_num)
theorem B2258355 : Blo 2257435 2258355 := bstep (se 1 (by rfl) ⟨1693766, by rfl⟩ : syracuseStep 2258355 = 3387533) B3387533
theorem B5081309 : Blo 2257435 5081309 := bbase (se 3 (by rfl) ⟨952745, by rfl⟩ : syracuseStep 5081309 = 1905491) (by norm_num)
theorem B3387539 : Blo 2257435 3387539 := bstep (se 1 (by rfl) ⟨2540654, by rfl⟩ : syracuseStep 3387539 = 5081309) B5081309
theorem B2258359 : Blo 2257435 2258359 := bstep (se 1 (by rfl) ⟨1693769, by rfl⟩ : syracuseStep 2258359 = 3387539) B3387539
theorem B3810989 : Blo 2257435 3810989 := bbase (se 3 (by rfl) ⟨714560, by rfl⟩ : syracuseStep 3810989 = 1429121) (by norm_num)
theorem B2540659 : Blo 2257435 2540659 := bstep (se 1 (by rfl) ⟨1905494, by rfl⟩ : syracuseStep 2540659 = 3810989) B3810989
theorem B3387545 : Blo 2257435 3387545 := bstep (se 2 (by rfl) ⟨1270329, by rfl⟩ : syracuseStep 3387545 = 2540659) B2540659
theorem B2258363 : Blo 2257435 2258363 := bstep (se 1 (by rfl) ⟨1693772, by rfl⟩ : syracuseStep 2258363 = 3387545) B3387545
theorem B5500237 : Blo 2257435 5500237 := bbase (se 3 (by rfl) ⟨1031294, by rfl⟩ : syracuseStep 5500237 = 2062589) (by norm_num)
theorem B7333649 : Blo 2257435 7333649 := bstep (se 2 (by rfl) ⟨2750118, by rfl⟩ : syracuseStep 7333649 = 5500237) B5500237
theorem B4889099 : Blo 2257435 4889099 := bstep (se 1 (by rfl) ⟨3666824, by rfl⟩ : syracuseStep 4889099 = 7333649) B7333649
theorem B3259399 : Blo 2257435 3259399 := bstep (se 1 (by rfl) ⟨2444549, by rfl⟩ : syracuseStep 3259399 = 4889099) B4889099
theorem B4345865 : Blo 2257435 4345865 := bstep (se 2 (by rfl) ⟨1629699, by rfl⟩ : syracuseStep 4345865 = 3259399) B3259399
theorem B2897243 : Blo 2257435 2897243 := bstep (se 1 (by rfl) ⟨2172932, by rfl⟩ : syracuseStep 2897243 = 4345865) B4345865
theorem B30903925 : Blo 2257435 30903925 := bstep (se 5 (by rfl) ⟨1448621, by rfl⟩ : syracuseStep 30903925 = 2897243) B2897243
theorem B41205233 : Blo 2257435 41205233 := bstep (se 2 (by rfl) ⟨15451962, by rfl⟩ : syracuseStep 41205233 = 30903925) B30903925
theorem B109880621 : Blo 2257435 109880621 := bstep (se 3 (by rfl) ⟨20602616, by rfl⟩ : syracuseStep 109880621 = 41205233) B41205233
theorem B73253747 : Blo 2257435 73253747 := bstep (se 1 (by rfl) ⟨54940310, by rfl⟩ : syracuseStep 73253747 = 109880621) B109880621
theorem B48835831 : Blo 2257435 48835831 := bstep (se 1 (by rfl) ⟨36626873, by rfl⟩ : syracuseStep 48835831 = 73253747) B73253747
theorem B65114441 : Blo 2257435 65114441 := bstep (se 2 (by rfl) ⟨24417915, by rfl⟩ : syracuseStep 65114441 = 48835831) B48835831
theorem B43409627 : Blo 2257435 43409627 := bstep (se 1 (by rfl) ⟨32557220, by rfl⟩ : syracuseStep 43409627 = 65114441) B65114441
theorem B28939751 : Blo 2257435 28939751 := bstep (se 1 (by rfl) ⟨21704813, by rfl⟩ : syracuseStep 28939751 = 43409627) B43409627
theorem B19293167 : Blo 2257435 19293167 := bstep (se 1 (by rfl) ⟨14469875, by rfl⟩ : syracuseStep 19293167 = 28939751) B28939751
theorem B12862111 : Blo 2257435 12862111 := bstep (se 1 (by rfl) ⟨9646583, by rfl⟩ : syracuseStep 12862111 = 19293167) B19293167
theorem B17149481 : Blo 2257435 17149481 := bstep (se 2 (by rfl) ⟨6431055, by rfl⟩ : syracuseStep 17149481 = 12862111) B12862111
theorem B11432987 : Blo 2257435 11432987 := bstep (se 1 (by rfl) ⟨8574740, by rfl⟩ : syracuseStep 11432987 = 17149481) B17149481
theorem B7621991 : Blo 2257435 7621991 := bstep (se 1 (by rfl) ⟨5716493, by rfl⟩ : syracuseStep 7621991 = 11432987) B11432987
theorem B5081327 : Blo 2257435 5081327 := bstep (se 1 (by rfl) ⟨3810995, by rfl⟩ : syracuseStep 5081327 = 7621991) B7621991
theorem B3387551 : Blo 2257435 3387551 := bstep (se 1 (by rfl) ⟨2540663, by rfl⟩ : syracuseStep 3387551 = 5081327) B5081327
theorem B2258367 : Blo 2257435 2258367 := bstep (se 1 (by rfl) ⟨1693775, by rfl⟩ : syracuseStep 2258367 = 3387551) B3387551
theorem B3387557 : Blo 2257435 3387557 := bbase (se 4 (by rfl) ⟨317583, by rfl⟩ : syracuseStep 3387557 = 635167) (by norm_num)
theorem B2258371 : Blo 2257435 2258371 := bstep (se 1 (by rfl) ⟨1693778, by rfl⟩ : syracuseStep 2258371 = 3387557) B3387557
theorem B2858257 : Blo 2257435 2858257 := bbase (se 2 (by rfl) ⟨1071846, by rfl⟩ : syracuseStep 2858257 = 2143693) (by norm_num)
theorem B3811009 : Blo 2257435 3811009 := bstep (se 2 (by rfl) ⟨1429128, by rfl⟩ : syracuseStep 3811009 = 2858257) B2858257
theorem B5081345 : Blo 2257435 5081345 := bstep (se 2 (by rfl) ⟨1905504, by rfl⟩ : syracuseStep 5081345 = 3811009) B3811009
theorem B3387563 : Blo 2257435 3387563 := bstep (se 1 (by rfl) ⟨2540672, by rfl⟩ : syracuseStep 3387563 = 5081345) B5081345
theorem B2258375 : Blo 2257435 2258375 := bstep (se 1 (by rfl) ⟨1693781, by rfl⟩ : syracuseStep 2258375 = 3387563) B3387563
theorem B2540677 : Blo 2257435 2540677 := bbase (se 4 (by rfl) ⟨238188, by rfl⟩ : syracuseStep 2540677 = 476377) (by norm_num)
theorem B3387569 : Blo 2257435 3387569 := bstep (se 2 (by rfl) ⟨1270338, by rfl⟩ : syracuseStep 3387569 = 2540677) B2540677
theorem B2258379 : Blo 2257435 2258379 := bstep (se 1 (by rfl) ⟨1693784, by rfl⟩ : syracuseStep 2258379 = 3387569) B3387569
theorem B5150693 : Blo 2257435 5150693 := bbase (se 4 (by rfl) ⟨482877, by rfl⟩ : syracuseStep 5150693 = 965755) (by norm_num)
theorem B3433795 : Blo 2257435 3433795 := bstep (se 1 (by rfl) ⟨2575346, by rfl⟩ : syracuseStep 3433795 = 5150693) B5150693
theorem B18313573 : Blo 2257435 18313573 := bstep (se 4 (by rfl) ⟨1716897, by rfl⟩ : syracuseStep 18313573 = 3433795) B3433795
theorem B24418097 : Blo 2257435 24418097 := bstep (se 2 (by rfl) ⟨9156786, by rfl⟩ : syracuseStep 24418097 = 18313573) B18313573
theorem B16278731 : Blo 2257435 16278731 := bstep (se 1 (by rfl) ⟨12209048, by rfl⟩ : syracuseStep 16278731 = 24418097) B24418097
theorem B10852487 : Blo 2257435 10852487 := bstep (se 1 (by rfl) ⟨8139365, by rfl⟩ : syracuseStep 10852487 = 16278731) B16278731
theorem B7234991 : Blo 2257435 7234991 := bstep (se 1 (by rfl) ⟨5426243, by rfl⟩ : syracuseStep 7234991 = 10852487) B10852487
theorem B4823327 : Blo 2257435 4823327 := bstep (se 1 (by rfl) ⟨3617495, by rfl⟩ : syracuseStep 4823327 = 7234991) B7234991
theorem B3215551 : Blo 2257435 3215551 := bstep (se 1 (by rfl) ⟨2411663, by rfl⟩ : syracuseStep 3215551 = 4823327) B4823327
theorem B4287401 : Blo 2257435 4287401 := bstep (se 2 (by rfl) ⟨1607775, by rfl⟩ : syracuseStep 4287401 = 3215551) B3215551
theorem B2858267 : Blo 2257435 2858267 := bstep (se 1 (by rfl) ⟨2143700, by rfl⟩ : syracuseStep 2858267 = 4287401) B4287401
theorem B7622045 : Blo 2257435 7622045 := bstep (se 3 (by rfl) ⟨1429133, by rfl⟩ : syracuseStep 7622045 = 2858267) B2858267
theorem B5081363 : Blo 2257435 5081363 := bstep (se 1 (by rfl) ⟨3811022, by rfl⟩ : syracuseStep 5081363 = 7622045) B7622045
theorem B3387575 : Blo 2257435 3387575 := bstep (se 1 (by rfl) ⟨2540681, by rfl⟩ : syracuseStep 3387575 = 5081363) B5081363
theorem B2258383 : Blo 2257435 2258383 := bstep (se 1 (by rfl) ⟨1693787, by rfl⟩ : syracuseStep 2258383 = 3387575) B3387575
theorem B3387581 : Blo 2257435 3387581 := bbase (se 3 (by rfl) ⟨635171, by rfl⟩ : syracuseStep 3387581 = 1270343) (by norm_num)
theorem B2258387 : Blo 2257435 2258387 := bstep (se 1 (by rfl) ⟨1693790, by rfl⟩ : syracuseStep 2258387 = 3387581) B3387581
theorem B5081381 : Blo 2257435 5081381 := bbase (se 4 (by rfl) ⟨476379, by rfl⟩ : syracuseStep 5081381 = 952759) (by norm_num)
theorem B3387587 : Blo 2257435 3387587 := bstep (se 1 (by rfl) ⟨2540690, by rfl⟩ : syracuseStep 3387587 = 5081381) B5081381
theorem B2258391 : Blo 2257435 2258391 := bstep (se 1 (by rfl) ⟨1693793, by rfl⟩ : syracuseStep 2258391 = 3387587) B3387587
theorem B5716565 : Blo 2257435 5716565 := bbase (se 8 (by rfl) ⟨33495, by rfl⟩ : syracuseStep 5716565 = 66991) (by norm_num)
theorem B3811043 : Blo 2257435 3811043 := bstep (se 1 (by rfl) ⟨2858282, by rfl⟩ : syracuseStep 3811043 = 5716565) B5716565
theorem B2540695 : Blo 2257435 2540695 := bstep (se 1 (by rfl) ⟨1905521, by rfl⟩ : syracuseStep 2540695 = 3811043) B3811043
theorem B3387593 : Blo 2257435 3387593 := bstep (se 2 (by rfl) ⟨1270347, by rfl⟩ : syracuseStep 3387593 = 2540695) B2540695
theorem B2258395 : Blo 2257435 2258395 := bstep (se 1 (by rfl) ⟨1693796, by rfl⟩ : syracuseStep 2258395 = 3387593) B3387593
theorem B2444585 : Blo 2257435 2444585 := bbase (se 2 (by rfl) ⟨916719, by rfl⟩ : syracuseStep 2444585 = 1833439) (by norm_num)
theorem B6518893 : Blo 2257435 6518893 := bstep (se 3 (by rfl) ⟨1222292, by rfl⟩ : syracuseStep 6518893 = 2444585) B2444585
theorem B8691857 : Blo 2257435 8691857 := bstep (se 2 (by rfl) ⟨3259446, by rfl⟩ : syracuseStep 8691857 = 6518893) B6518893
theorem B5794571 : Blo 2257435 5794571 := bstep (se 1 (by rfl) ⟨4345928, by rfl⟩ : syracuseStep 5794571 = 8691857) B8691857
theorem B3863047 : Blo 2257435 3863047 := bstep (se 1 (by rfl) ⟨2897285, by rfl⟩ : syracuseStep 3863047 = 5794571) B5794571
theorem B5150729 : Blo 2257435 5150729 := bstep (se 2 (by rfl) ⟨1931523, by rfl⟩ : syracuseStep 5150729 = 3863047) B3863047
theorem B13735277 : Blo 2257435 13735277 := bstep (se 3 (by rfl) ⟨2575364, by rfl⟩ : syracuseStep 13735277 = 5150729) B5150729
theorem B9156851 : Blo 2257435 9156851 := bstep (se 1 (by rfl) ⟨6867638, by rfl⟩ : syracuseStep 9156851 = 13735277) B13735277
theorem B6104567 : Blo 2257435 6104567 := bstep (se 1 (by rfl) ⟨4578425, by rfl⟩ : syracuseStep 6104567 = 9156851) B9156851
theorem B4069711 : Blo 2257435 4069711 := bstep (se 1 (by rfl) ⟨3052283, by rfl⟩ : syracuseStep 4069711 = 6104567) B6104567
theorem B5426281 : Blo 2257435 5426281 := bstep (se 2 (by rfl) ⟨2034855, by rfl⟩ : syracuseStep 5426281 = 4069711) B4069711
theorem B7235041 : Blo 2257435 7235041 := bstep (se 2 (by rfl) ⟨2713140, by rfl⟩ : syracuseStep 7235041 = 5426281) B5426281
theorem B9646721 : Blo 2257435 9646721 := bstep (se 2 (by rfl) ⟨3617520, by rfl⟩ : syracuseStep 9646721 = 7235041) B7235041
theorem B6431147 : Blo 2257435 6431147 := bstep (se 1 (by rfl) ⟨4823360, by rfl⟩ : syracuseStep 6431147 = 9646721) B9646721
theorem B4287431 : Blo 2257435 4287431 := bstep (se 1 (by rfl) ⟨3215573, by rfl⟩ : syracuseStep 4287431 = 6431147) B6431147
theorem B11433149 : Blo 2257435 11433149 := bstep (se 3 (by rfl) ⟨2143715, by rfl⟩ : syracuseStep 11433149 = 4287431) B4287431
theorem B7622099 : Blo 2257435 7622099 := bstep (se 1 (by rfl) ⟨5716574, by rfl⟩ : syracuseStep 7622099 = 11433149) B11433149
theorem B5081399 : Blo 2257435 5081399 := bstep (se 1 (by rfl) ⟨3811049, by rfl⟩ : syracuseStep 5081399 = 7622099) B7622099
theorem B3387599 : Blo 2257435 3387599 := bstep (se 1 (by rfl) ⟨2540699, by rfl⟩ : syracuseStep 3387599 = 5081399) B5081399
theorem B2258399 : Blo 2257435 2258399 := bstep (se 1 (by rfl) ⟨1693799, by rfl⟩ : syracuseStep 2258399 = 3387599) B3387599
theorem B3387605 : Blo 2257435 3387605 := bbase (se 7 (by rfl) ⟨39698, by rfl⟩ : syracuseStep 3387605 = 79397) (by norm_num)
theorem B2258403 : Blo 2257435 2258403 := bstep (se 1 (by rfl) ⟨1693802, by rfl⟩ : syracuseStep 2258403 = 3387605) B3387605
theorem B2411689 : Blo 2257435 2411689 := bbase (se 2 (by rfl) ⟨904383, by rfl⟩ : syracuseStep 2411689 = 1808767) (by norm_num)
theorem B3215585 : Blo 2257435 3215585 := bstep (se 2 (by rfl) ⟨1205844, by rfl⟩ : syracuseStep 3215585 = 2411689) B2411689
theorem B8574893 : Blo 2257435 8574893 := bstep (se 3 (by rfl) ⟨1607792, by rfl⟩ : syracuseStep 8574893 = 3215585) B3215585
theorem B5716595 : Blo 2257435 5716595 := bstep (se 1 (by rfl) ⟨4287446, by rfl⟩ : syracuseStep 5716595 = 8574893) B8574893
theorem B3811063 : Blo 2257435 3811063 := bstep (se 1 (by rfl) ⟨2858297, by rfl⟩ : syracuseStep 3811063 = 5716595) B5716595
theorem B5081417 : Blo 2257435 5081417 := bstep (se 2 (by rfl) ⟨1905531, by rfl⟩ : syracuseStep 5081417 = 3811063) B3811063
theorem B3387611 : Blo 2257435 3387611 := bstep (se 1 (by rfl) ⟨2540708, by rfl⟩ : syracuseStep 3387611 = 5081417) B5081417
theorem B2258407 : Blo 2257435 2258407 := bstep (se 1 (by rfl) ⟨1693805, by rfl⟩ : syracuseStep 2258407 = 3387611) B3387611
theorem B2540713 : Blo 2257435 2540713 := bbase (se 2 (by rfl) ⟨952767, by rfl⟩ : syracuseStep 2540713 = 1905535) (by norm_num)
theorem B3387617 : Blo 2257435 3387617 := bstep (se 2 (by rfl) ⟨1270356, by rfl⟩ : syracuseStep 3387617 = 2540713) B2540713
theorem B2258411 : Blo 2257435 2258411 := bstep (se 1 (by rfl) ⟨1693808, by rfl⟩ : syracuseStep 2258411 = 3387617) B3387617
theorem B9646789 : Blo 2257435 9646789 := bbase (se 4 (by rfl) ⟨904386, by rfl⟩ : syracuseStep 9646789 = 1808773) (by norm_num)
theorem B12862385 : Blo 2257435 12862385 := bstep (se 2 (by rfl) ⟨4823394, by rfl⟩ : syracuseStep 12862385 = 9646789) B9646789
theorem B8574923 : Blo 2257435 8574923 := bstep (se 1 (by rfl) ⟨6431192, by rfl⟩ : syracuseStep 8574923 = 12862385) B12862385
theorem B5716615 : Blo 2257435 5716615 := bstep (se 1 (by rfl) ⟨4287461, by rfl⟩ : syracuseStep 5716615 = 8574923) B8574923
theorem B7622153 : Blo 2257435 7622153 := bstep (se 2 (by rfl) ⟨2858307, by rfl⟩ : syracuseStep 7622153 = 5716615) B5716615
theorem B5081435 : Blo 2257435 5081435 := bstep (se 1 (by rfl) ⟨3811076, by rfl⟩ : syracuseStep 5081435 = 7622153) B7622153
theorem B3387623 : Blo 2257435 3387623 := bstep (se 1 (by rfl) ⟨2540717, by rfl⟩ : syracuseStep 3387623 = 5081435) B5081435
theorem B2258415 : Blo 2257435 2258415 := bstep (se 1 (by rfl) ⟨1693811, by rfl⟩ : syracuseStep 2258415 = 3387623) B3387623
theorem B3387629 : Blo 2257435 3387629 := bbase (se 3 (by rfl) ⟨635180, by rfl⟩ : syracuseStep 3387629 = 1270361) (by norm_num)
theorem B2258419 : Blo 2257435 2258419 := bstep (se 1 (by rfl) ⟨1693814, by rfl⟩ : syracuseStep 2258419 = 3387629) B3387629
theorem B5081453 : Blo 2257435 5081453 := bbase (se 3 (by rfl) ⟨952772, by rfl⟩ : syracuseStep 5081453 = 1905545) (by norm_num)
theorem B3387635 : Blo 2257435 3387635 := bstep (se 1 (by rfl) ⟨2540726, by rfl⟩ : syracuseStep 3387635 = 5081453) B5081453
theorem B2258423 : Blo 2257435 2258423 := bstep (se 1 (by rfl) ⟨1693817, by rfl⟩ : syracuseStep 2258423 = 3387635) B3387635
theorem B4287485 : Blo 2257435 4287485 := bbase (se 3 (by rfl) ⟨803903, by rfl⟩ : syracuseStep 4287485 = 1607807) (by norm_num)
theorem B2858323 : Blo 2257435 2858323 := bstep (se 1 (by rfl) ⟨2143742, by rfl⟩ : syracuseStep 2858323 = 4287485) B4287485
theorem B3811097 : Blo 2257435 3811097 := bstep (se 2 (by rfl) ⟨1429161, by rfl⟩ : syracuseStep 3811097 = 2858323) B2858323
theorem B2540731 : Blo 2257435 2540731 := bstep (se 1 (by rfl) ⟨1905548, by rfl⟩ : syracuseStep 2540731 = 3811097) B3811097
theorem B3387641 : Blo 2257435 3387641 := bstep (se 2 (by rfl) ⟨1270365, by rfl⟩ : syracuseStep 3387641 = 2540731) B2540731
theorem B2258427 : Blo 2257435 2258427 := bstep (se 1 (by rfl) ⟨1693820, by rfl⟩ : syracuseStep 2258427 = 3387641) B3387641
theorem B5426357 : Blo 2257435 5426357 := bbase (se 5 (by rfl) ⟨254360, by rfl⟩ : syracuseStep 5426357 = 508721) (by norm_num)
theorem B57881141 : Blo 2257435 57881141 := bstep (se 5 (by rfl) ⟨2713178, by rfl⟩ : syracuseStep 57881141 = 5426357) B5426357
theorem B38587427 : Blo 2257435 38587427 := bstep (se 1 (by rfl) ⟨28940570, by rfl⟩ : syracuseStep 38587427 = 57881141) B57881141
theorem B25724951 : Blo 2257435 25724951 := bstep (se 1 (by rfl) ⟨19293713, by rfl⟩ : syracuseStep 25724951 = 38587427) B38587427
theorem B17149967 : Blo 2257435 17149967 := bstep (se 1 (by rfl) ⟨12862475, by rfl⟩ : syracuseStep 17149967 = 25724951) B25724951
theorem B11433311 : Blo 2257435 11433311 := bstep (se 1 (by rfl) ⟨8574983, by rfl⟩ : syracuseStep 11433311 = 17149967) B17149967
theorem B7622207 : Blo 2257435 7622207 := bstep (se 1 (by rfl) ⟨5716655, by rfl⟩ : syracuseStep 7622207 = 11433311) B11433311
theorem B5081471 : Blo 2257435 5081471 := bstep (se 1 (by rfl) ⟨3811103, by rfl⟩ : syracuseStep 5081471 = 7622207) B7622207
theorem B3387647 : Blo 2257435 3387647 := bstep (se 1 (by rfl) ⟨2540735, by rfl⟩ : syracuseStep 3387647 = 5081471) B5081471
theorem B2258431 : Blo 2257435 2258431 := bstep (se 1 (by rfl) ⟨1693823, by rfl⟩ : syracuseStep 2258431 = 3387647) B3387647
theorem B3387653 : Blo 2257435 3387653 := bbase (se 4 (by rfl) ⟨317592, by rfl⟩ : syracuseStep 3387653 = 635185) (by norm_num)
theorem B2258435 : Blo 2257435 2258435 := bstep (se 1 (by rfl) ⟨1693826, by rfl⟩ : syracuseStep 2258435 = 3387653) B3387653
theorem B3811117 : Blo 2257435 3811117 := bbase (se 3 (by rfl) ⟨714584, by rfl⟩ : syracuseStep 3811117 = 1429169) (by norm_num)
theorem B5081489 : Blo 2257435 5081489 := bstep (se 2 (by rfl) ⟨1905558, by rfl⟩ : syracuseStep 5081489 = 3811117) B3811117
theorem B3387659 : Blo 2257435 3387659 := bstep (se 1 (by rfl) ⟨2540744, by rfl⟩ : syracuseStep 3387659 = 5081489) B5081489
theorem B2258439 : Blo 2257435 2258439 := bstep (se 1 (by rfl) ⟨1693829, by rfl⟩ : syracuseStep 2258439 = 3387659) B3387659
theorem B2540749 : Blo 2257435 2540749 := bbase (se 3 (by rfl) ⟨476390, by rfl⟩ : syracuseStep 2540749 = 952781) (by norm_num)
theorem B3387665 : Blo 2257435 3387665 := bstep (se 2 (by rfl) ⟨1270374, by rfl⟩ : syracuseStep 3387665 = 2540749) B2540749
theorem B2258443 : Blo 2257435 2258443 := bstep (se 1 (by rfl) ⟨1693832, by rfl⟩ : syracuseStep 2258443 = 3387665) B3387665
theorem B7622261 : Blo 2257435 7622261 := bbase (se 5 (by rfl) ⟨357293, by rfl⟩ : syracuseStep 7622261 = 714587) (by norm_num)
theorem B5081507 : Blo 2257435 5081507 := bstep (se 1 (by rfl) ⟨3811130, by rfl⟩ : syracuseStep 5081507 = 7622261) B7622261
theorem B3387671 : Blo 2257435 3387671 := bstep (se 1 (by rfl) ⟨2540753, by rfl⟩ : syracuseStep 3387671 = 5081507) B5081507
theorem B2258447 : Blo 2257435 2258447 := bstep (se 1 (by rfl) ⟨1693835, by rfl⟩ : syracuseStep 2258447 = 3387671) B3387671
theorem B3387677 : Blo 2257435 3387677 := bbase (se 3 (by rfl) ⟨635189, by rfl⟩ : syracuseStep 3387677 = 1270379) (by norm_num)
theorem B2258451 : Blo 2257435 2258451 := bstep (se 1 (by rfl) ⟨1693838, by rfl⟩ : syracuseStep 2258451 = 3387677) B3387677
theorem B5081525 : Blo 2257435 5081525 := bbase (se 5 (by rfl) ⟨238196, by rfl⟩ : syracuseStep 5081525 = 476393) (by norm_num)
theorem B3387683 : Blo 2257435 3387683 := bstep (se 1 (by rfl) ⟨2540762, by rfl⟩ : syracuseStep 3387683 = 5081525) B5081525
theorem B2258455 : Blo 2257435 2258455 := bstep (se 1 (by rfl) ⟨1693841, by rfl⟩ : syracuseStep 2258455 = 3387683) B3387683
theorem B2713213 : Blo 2257435 2713213 := bbase (se 3 (by rfl) ⟨508727, by rfl⟩ : syracuseStep 2713213 = 1017455) (by norm_num)
theorem B3617617 : Blo 2257435 3617617 := bstep (se 2 (by rfl) ⟨1356606, by rfl⟩ : syracuseStep 3617617 = 2713213) B2713213
theorem B4823489 : Blo 2257435 4823489 := bstep (se 2 (by rfl) ⟨1808808, by rfl⟩ : syracuseStep 4823489 = 3617617) B3617617
theorem B12862637 : Blo 2257435 12862637 := bstep (se 3 (by rfl) ⟨2411744, by rfl⟩ : syracuseStep 12862637 = 4823489) B4823489
theorem B8575091 : Blo 2257435 8575091 := bstep (se 1 (by rfl) ⟨6431318, by rfl⟩ : syracuseStep 8575091 = 12862637) B12862637
theorem B5716727 : Blo 2257435 5716727 := bstep (se 1 (by rfl) ⟨4287545, by rfl⟩ : syracuseStep 5716727 = 8575091) B8575091
theorem B3811151 : Blo 2257435 3811151 := bstep (se 1 (by rfl) ⟨2858363, by rfl⟩ : syracuseStep 3811151 = 5716727) B5716727
theorem B2540767 : Blo 2257435 2540767 := bstep (se 1 (by rfl) ⟨1905575, by rfl⟩ : syracuseStep 2540767 = 3811151) B3811151
theorem B3387689 : Blo 2257435 3387689 := bstep (se 2 (by rfl) ⟨1270383, by rfl⟩ : syracuseStep 3387689 = 2540767) B2540767
theorem B2258459 : Blo 2257435 2258459 := bstep (se 1 (by rfl) ⟨1693844, by rfl⟩ : syracuseStep 2258459 = 3387689) B3387689
theorem B8139653 : Blo 2257435 8139653 := bbase (se 4 (by rfl) ⟨763092, by rfl⟩ : syracuseStep 8139653 = 1526185) (by norm_num)
theorem B5426435 : Blo 2257435 5426435 := bstep (se 1 (by rfl) ⟨4069826, by rfl⟩ : syracuseStep 5426435 = 8139653) B8139653
theorem B3617623 : Blo 2257435 3617623 := bstep (se 1 (by rfl) ⟨2713217, by rfl⟩ : syracuseStep 3617623 = 5426435) B5426435
theorem B4823497 : Blo 2257435 4823497 := bstep (se 2 (by rfl) ⟨1808811, by rfl⟩ : syracuseStep 4823497 = 3617623) B3617623
theorem B6431329 : Blo 2257435 6431329 := bstep (se 2 (by rfl) ⟨2411748, by rfl⟩ : syracuseStep 6431329 = 4823497) B4823497
theorem B8575105 : Blo 2257435 8575105 := bstep (se 2 (by rfl) ⟨3215664, by rfl⟩ : syracuseStep 8575105 = 6431329) B6431329
theorem B11433473 : Blo 2257435 11433473 := bstep (se 2 (by rfl) ⟨4287552, by rfl⟩ : syracuseStep 11433473 = 8575105) B8575105
theorem B7622315 : Blo 2257435 7622315 := bstep (se 1 (by rfl) ⟨5716736, by rfl⟩ : syracuseStep 7622315 = 11433473) B11433473
theorem B5081543 : Blo 2257435 5081543 := bstep (se 1 (by rfl) ⟨3811157, by rfl⟩ : syracuseStep 5081543 = 7622315) B7622315
theorem B3387695 : Blo 2257435 3387695 := bstep (se 1 (by rfl) ⟨2540771, by rfl⟩ : syracuseStep 3387695 = 5081543) B5081543
theorem B2258463 : Blo 2257435 2258463 := bstep (se 1 (by rfl) ⟨1693847, by rfl⟩ : syracuseStep 2258463 = 3387695) B3387695
theorem B3387701 : Blo 2257435 3387701 := bbase (se 5 (by rfl) ⟨158798, by rfl⟩ : syracuseStep 3387701 = 317597) (by norm_num)
theorem B2258467 : Blo 2257435 2258467 := bstep (se 1 (by rfl) ⟨1693850, by rfl⟩ : syracuseStep 2258467 = 3387701) B3387701
theorem B5716757 : Blo 2257435 5716757 := bbase (se 6 (by rfl) ⟨133986, by rfl⟩ : syracuseStep 5716757 = 267973) (by norm_num)
theorem B3811171 : Blo 2257435 3811171 := bstep (se 1 (by rfl) ⟨2858378, by rfl⟩ : syracuseStep 3811171 = 5716757) B5716757
theorem B5081561 : Blo 2257435 5081561 := bstep (se 2 (by rfl) ⟨1905585, by rfl⟩ : syracuseStep 5081561 = 3811171) B3811171
theorem B3387707 : Blo 2257435 3387707 := bstep (se 1 (by rfl) ⟨2540780, by rfl⟩ : syracuseStep 3387707 = 5081561) B5081561
theorem B2258471 : Blo 2257435 2258471 := bstep (se 1 (by rfl) ⟨1693853, by rfl⟩ : syracuseStep 2258471 = 3387707) B3387707
theorem B2540785 : Blo 2257435 2540785 := bbase (se 2 (by rfl) ⟨952794, by rfl⟩ : syracuseStep 2540785 = 1905589) (by norm_num)
theorem B3387713 : Blo 2257435 3387713 := bstep (se 2 (by rfl) ⟨1270392, by rfl⟩ : syracuseStep 3387713 = 2540785) B2540785
theorem B2258475 : Blo 2257435 2258475 := bstep (se 1 (by rfl) ⟨1693856, by rfl⟩ : syracuseStep 2258475 = 3387713) B3387713
theorem B5221189 : Blo 2257435 5221189 := bbase (se 4 (by rfl) ⟨489486, by rfl⟩ : syracuseStep 5221189 = 978973) (by norm_num)
theorem B6961585 : Blo 2257435 6961585 := bstep (se 2 (by rfl) ⟨2610594, by rfl⟩ : syracuseStep 6961585 = 5221189) B5221189
theorem B9282113 : Blo 2257435 9282113 := bstep (se 2 (by rfl) ⟨3480792, by rfl⟩ : syracuseStep 9282113 = 6961585) B6961585
theorem B6188075 : Blo 2257435 6188075 := bstep (se 1 (by rfl) ⟨4641056, by rfl⟩ : syracuseStep 6188075 = 9282113) B9282113
theorem B4125383 : Blo 2257435 4125383 := bstep (se 1 (by rfl) ⟨3094037, by rfl⟩ : syracuseStep 4125383 = 6188075) B6188075
theorem B2750255 : Blo 2257435 2750255 := bstep (se 1 (by rfl) ⟨2062691, by rfl⟩ : syracuseStep 2750255 = 4125383) B4125383
theorem B29336053 : Blo 2257435 29336053 := bstep (se 5 (by rfl) ⟨1375127, by rfl⟩ : syracuseStep 29336053 = 2750255) B2750255
theorem B39114737 : Blo 2257435 39114737 := bstep (se 2 (by rfl) ⟨14668026, by rfl⟩ : syracuseStep 39114737 = 29336053) B29336053
theorem B26076491 : Blo 2257435 26076491 := bstep (se 1 (by rfl) ⟨19557368, by rfl⟩ : syracuseStep 26076491 = 39114737) B39114737
theorem B17384327 : Blo 2257435 17384327 := bstep (se 1 (by rfl) ⟨13038245, by rfl⟩ : syracuseStep 17384327 = 26076491) B26076491
theorem B11589551 : Blo 2257435 11589551 := bstep (se 1 (by rfl) ⟨8692163, by rfl⟩ : syracuseStep 11589551 = 17384327) B17384327
theorem B7726367 : Blo 2257435 7726367 := bstep (se 1 (by rfl) ⟨5794775, by rfl⟩ : syracuseStep 7726367 = 11589551) B11589551
theorem B20603645 : Blo 2257435 20603645 := bstep (se 3 (by rfl) ⟨3863183, by rfl⟩ : syracuseStep 20603645 = 7726367) B7726367
theorem B13735763 : Blo 2257435 13735763 := bstep (se 1 (by rfl) ⟨10301822, by rfl⟩ : syracuseStep 13735763 = 20603645) B20603645
theorem B9157175 : Blo 2257435 9157175 := bstep (se 1 (by rfl) ⟨6867881, by rfl⟩ : syracuseStep 9157175 = 13735763) B13735763
theorem B6104783 : Blo 2257435 6104783 := bstep (se 1 (by rfl) ⟨4578587, by rfl⟩ : syracuseStep 6104783 = 9157175) B9157175
theorem B4069855 : Blo 2257435 4069855 := bstep (se 1 (by rfl) ⟨3052391, by rfl⟩ : syracuseStep 4069855 = 6104783) B6104783
theorem B21705893 : Blo 2257435 21705893 := bstep (se 4 (by rfl) ⟨2034927, by rfl⟩ : syracuseStep 21705893 = 4069855) B4069855
theorem B14470595 : Blo 2257435 14470595 := bstep (se 1 (by rfl) ⟨10852946, by rfl⟩ : syracuseStep 14470595 = 21705893) B21705893
theorem B9647063 : Blo 2257435 9647063 := bstep (se 1 (by rfl) ⟨7235297, by rfl⟩ : syracuseStep 9647063 = 14470595) B14470595
theorem B6431375 : Blo 2257435 6431375 := bstep (se 1 (by rfl) ⟨4823531, by rfl⟩ : syracuseStep 6431375 = 9647063) B9647063
theorem B4287583 : Blo 2257435 4287583 := bstep (se 1 (by rfl) ⟨3215687, by rfl⟩ : syracuseStep 4287583 = 6431375) B6431375
theorem B5716777 : Blo 2257435 5716777 := bstep (se 2 (by rfl) ⟨2143791, by rfl⟩ : syracuseStep 5716777 = 4287583) B4287583
theorem B7622369 : Blo 2257435 7622369 := bstep (se 2 (by rfl) ⟨2858388, by rfl⟩ : syracuseStep 7622369 = 5716777) B5716777
theorem B5081579 : Blo 2257435 5081579 := bstep (se 1 (by rfl) ⟨3811184, by rfl⟩ : syracuseStep 5081579 = 7622369) B7622369
theorem B3387719 : Blo 2257435 3387719 := bstep (se 1 (by rfl) ⟨2540789, by rfl⟩ : syracuseStep 3387719 = 5081579) B5081579
theorem B2258479 : Blo 2257435 2258479 := bstep (se 1 (by rfl) ⟨1693859, by rfl⟩ : syracuseStep 2258479 = 3387719) B3387719
theorem B3387725 : Blo 2257435 3387725 := bbase (se 3 (by rfl) ⟨635198, by rfl⟩ : syracuseStep 3387725 = 1270397) (by norm_num)
theorem B2258483 : Blo 2257435 2258483 := bstep (se 1 (by rfl) ⟨1693862, by rfl⟩ : syracuseStep 2258483 = 3387725) B3387725
theorem B5081597 : Blo 2257435 5081597 := bbase (se 3 (by rfl) ⟨952799, by rfl⟩ : syracuseStep 5081597 = 1905599) (by norm_num)
theorem B3387731 : Blo 2257435 3387731 := bstep (se 1 (by rfl) ⟨2540798, by rfl⟩ : syracuseStep 3387731 = 5081597) B5081597
theorem B2258487 : Blo 2257435 2258487 := bstep (se 1 (by rfl) ⟨1693865, by rfl⟩ : syracuseStep 2258487 = 3387731) B3387731
theorem B3811205 : Blo 2257435 3811205 := bbase (se 4 (by rfl) ⟨357300, by rfl⟩ : syracuseStep 3811205 = 714601) (by norm_num)
theorem B2540803 : Blo 2257435 2540803 := bstep (se 1 (by rfl) ⟨1905602, by rfl⟩ : syracuseStep 2540803 = 3811205) B3811205
theorem B3387737 : Blo 2257435 3387737 := bstep (se 2 (by rfl) ⟨1270401, by rfl⟩ : syracuseStep 3387737 = 2540803) B2540803
theorem B2258491 : Blo 2257435 2258491 := bstep (se 1 (by rfl) ⟨1693868, by rfl⟩ : syracuseStep 2258491 = 3387737) B3387737
theorem B17150453 : Blo 2257435 17150453 := bbase (se 5 (by rfl) ⟨803927, by rfl⟩ : syracuseStep 17150453 = 1607855) (by norm_num)
theorem B11433635 : Blo 2257435 11433635 := bstep (se 1 (by rfl) ⟨8575226, by rfl⟩ : syracuseStep 11433635 = 17150453) B17150453
theorem B7622423 : Blo 2257435 7622423 := bstep (se 1 (by rfl) ⟨5716817, by rfl⟩ : syracuseStep 7622423 = 11433635) B11433635
theorem B5081615 : Blo 2257435 5081615 := bstep (se 1 (by rfl) ⟨3811211, by rfl⟩ : syracuseStep 5081615 = 7622423) B7622423
theorem B3387743 : Blo 2257435 3387743 := bstep (se 1 (by rfl) ⟨2540807, by rfl⟩ : syracuseStep 3387743 = 5081615) B5081615
theorem B2258495 : Blo 2257435 2258495 := bstep (se 1 (by rfl) ⟨1693871, by rfl⟩ : syracuseStep 2258495 = 3387743) B3387743
theorem B3387749 : Blo 2257435 3387749 := bbase (se 4 (by rfl) ⟨317601, by rfl⟩ : syracuseStep 3387749 = 635203) (by norm_num)
theorem B2258499 : Blo 2257435 2258499 := bstep (se 1 (by rfl) ⟨1693874, by rfl⟩ : syracuseStep 2258499 = 3387749) B3387749
theorem B4287629 : Blo 2257435 4287629 := bbase (se 3 (by rfl) ⟨803930, by rfl⟩ : syracuseStep 4287629 = 1607861) (by norm_num)
theorem B2858419 : Blo 2257435 2858419 := bstep (se 1 (by rfl) ⟨2143814, by rfl⟩ : syracuseStep 2858419 = 4287629) B4287629
theorem B3811225 : Blo 2257435 3811225 := bstep (se 2 (by rfl) ⟨1429209, by rfl⟩ : syracuseStep 3811225 = 2858419) B2858419
theorem B5081633 : Blo 2257435 5081633 := bstep (se 2 (by rfl) ⟨1905612, by rfl⟩ : syracuseStep 5081633 = 3811225) B3811225
theorem B3387755 : Blo 2257435 3387755 := bstep (se 1 (by rfl) ⟨2540816, by rfl⟩ : syracuseStep 3387755 = 5081633) B5081633
theorem B2258503 : Blo 2257435 2258503 := bstep (se 1 (by rfl) ⟨1693877, by rfl⟩ : syracuseStep 2258503 = 3387755) B3387755
theorem B2540821 : Blo 2257435 2540821 := bbase (se 6 (by rfl) ⟨59550, by rfl⟩ : syracuseStep 2540821 = 119101) (by norm_num)
theorem B3387761 : Blo 2257435 3387761 := bstep (se 2 (by rfl) ⟨1270410, by rfl⟩ : syracuseStep 3387761 = 2540821) B2540821
theorem B2258507 : Blo 2257435 2258507 := bstep (se 1 (by rfl) ⟨1693880, by rfl⟩ : syracuseStep 2258507 = 3387761) B3387761
theorem B2858429 : Blo 2257435 2858429 := bbase (se 3 (by rfl) ⟨535955, by rfl⟩ : syracuseStep 2858429 = 1071911) (by norm_num)
theorem B7622477 : Blo 2257435 7622477 := bstep (se 3 (by rfl) ⟨1429214, by rfl⟩ : syracuseStep 7622477 = 2858429) B2858429
theorem B5081651 : Blo 2257435 5081651 := bstep (se 1 (by rfl) ⟨3811238, by rfl⟩ : syracuseStep 5081651 = 7622477) B7622477
theorem B3387767 : Blo 2257435 3387767 := bstep (se 1 (by rfl) ⟨2540825, by rfl⟩ : syracuseStep 3387767 = 5081651) B5081651
theorem B2258511 : Blo 2257435 2258511 := bstep (se 1 (by rfl) ⟨1693883, by rfl⟩ : syracuseStep 2258511 = 3387767) B3387767
theorem B3387773 : Blo 2257435 3387773 := bbase (se 3 (by rfl) ⟨635207, by rfl⟩ : syracuseStep 3387773 = 1270415) (by norm_num)
theorem B2258515 : Blo 2257435 2258515 := bstep (se 1 (by rfl) ⟨1693886, by rfl⟩ : syracuseStep 2258515 = 3387773) B3387773
theorem B5081669 : Blo 2257435 5081669 := bbase (se 4 (by rfl) ⟨476406, by rfl⟩ : syracuseStep 5081669 = 952813) (by norm_num)
theorem B3387779 : Blo 2257435 3387779 := bstep (se 1 (by rfl) ⟨2540834, by rfl⟩ : syracuseStep 3387779 = 5081669) B5081669
theorem B2258519 : Blo 2257435 2258519 := bstep (se 1 (by rfl) ⟨1693889, by rfl⟩ : syracuseStep 2258519 = 3387779) B3387779
theorem B2411813 : Blo 2257435 2411813 := bbase (se 4 (by rfl) ⟨226107, by rfl⟩ : syracuseStep 2411813 = 452215) (by norm_num)
theorem B6431501 : Blo 2257435 6431501 := bstep (se 3 (by rfl) ⟨1205906, by rfl⟩ : syracuseStep 6431501 = 2411813) B2411813
theorem B4287667 : Blo 2257435 4287667 := bstep (se 1 (by rfl) ⟨3215750, by rfl⟩ : syracuseStep 4287667 = 6431501) B6431501
theorem B5716889 : Blo 2257435 5716889 := bstep (se 2 (by rfl) ⟨2143833, by rfl⟩ : syracuseStep 5716889 = 4287667) B4287667
theorem B3811259 : Blo 2257435 3811259 := bstep (se 1 (by rfl) ⟨2858444, by rfl⟩ : syracuseStep 3811259 = 5716889) B5716889
theorem B2540839 : Blo 2257435 2540839 := bstep (se 1 (by rfl) ⟨1905629, by rfl⟩ : syracuseStep 2540839 = 3811259) B3811259
theorem B3387785 : Blo 2257435 3387785 := bstep (se 2 (by rfl) ⟨1270419, by rfl⟩ : syracuseStep 3387785 = 2540839) B2540839
theorem B2258523 : Blo 2257435 2258523 := bstep (se 1 (by rfl) ⟨1693892, by rfl⟩ : syracuseStep 2258523 = 3387785) B3387785
theorem B11433797 : Blo 2257435 11433797 := bbase (se 4 (by rfl) ⟨1071918, by rfl⟩ : syracuseStep 11433797 = 2143837) (by norm_num)
theorem B7622531 : Blo 2257435 7622531 := bstep (se 1 (by rfl) ⟨5716898, by rfl⟩ : syracuseStep 7622531 = 11433797) B11433797
theorem B5081687 : Blo 2257435 5081687 := bstep (se 1 (by rfl) ⟨3811265, by rfl⟩ : syracuseStep 5081687 = 7622531) B7622531
theorem B3387791 : Blo 2257435 3387791 := bstep (se 1 (by rfl) ⟨2540843, by rfl⟩ : syracuseStep 3387791 = 5081687) B5081687
theorem B2258527 : Blo 2257435 2258527 := bstep (se 1 (by rfl) ⟨1693895, by rfl⟩ : syracuseStep 2258527 = 3387791) B3387791
theorem B3387797 : Blo 2257435 3387797 := bbase (se 6 (by rfl) ⟨79401, by rfl⟩ : syracuseStep 3387797 = 158803) (by norm_num)
theorem B2258531 : Blo 2257435 2258531 := bstep (se 1 (by rfl) ⟨1693898, by rfl⟩ : syracuseStep 2258531 = 3387797) B3387797
theorem B7235477 : Blo 2257435 7235477 := bbase (se 6 (by rfl) ⟨169581, by rfl⟩ : syracuseStep 7235477 = 339163) (by norm_num)
theorem B4823651 : Blo 2257435 4823651 := bstep (se 1 (by rfl) ⟨3617738, by rfl⟩ : syracuseStep 4823651 = 7235477) B7235477
theorem B12863069 : Blo 2257435 12863069 := bstep (se 3 (by rfl) ⟨2411825, by rfl⟩ : syracuseStep 12863069 = 4823651) B4823651
theorem B8575379 : Blo 2257435 8575379 := bstep (se 1 (by rfl) ⟨6431534, by rfl⟩ : syracuseStep 8575379 = 12863069) B12863069
theorem B5716919 : Blo 2257435 5716919 := bstep (se 1 (by rfl) ⟨4287689, by rfl⟩ : syracuseStep 5716919 = 8575379) B8575379
theorem B3811279 : Blo 2257435 3811279 := bstep (se 1 (by rfl) ⟨2858459, by rfl⟩ : syracuseStep 3811279 = 5716919) B5716919
theorem B5081705 : Blo 2257435 5081705 := bstep (se 2 (by rfl) ⟨1905639, by rfl⟩ : syracuseStep 5081705 = 3811279) B3811279
theorem B3387803 : Blo 2257435 3387803 := bstep (se 1 (by rfl) ⟨2540852, by rfl⟩ : syracuseStep 3387803 = 5081705) B5081705
theorem B2258535 : Blo 2257435 2258535 := bstep (se 1 (by rfl) ⟨1693901, by rfl⟩ : syracuseStep 2258535 = 3387803) B3387803
theorem B2540857 : Blo 2257435 2540857 := bbase (se 2 (by rfl) ⟨952821, by rfl⟩ : syracuseStep 2540857 = 1905643) (by norm_num)
theorem B3387809 : Blo 2257435 3387809 := bstep (se 2 (by rfl) ⟨1270428, by rfl⟩ : syracuseStep 3387809 = 2540857) B2540857
theorem B2258539 : Blo 2257435 2258539 := bstep (se 1 (by rfl) ⟨1693904, by rfl⟩ : syracuseStep 2258539 = 3387809) B3387809
theorem B6431557 : Blo 2257435 6431557 := bbase (se 4 (by rfl) ⟨602958, by rfl⟩ : syracuseStep 6431557 = 1205917) (by norm_num)
theorem B8575409 : Blo 2257435 8575409 := bstep (se 2 (by rfl) ⟨3215778, by rfl⟩ : syracuseStep 8575409 = 6431557) B6431557
theorem B5716939 : Blo 2257435 5716939 := bstep (se 1 (by rfl) ⟨4287704, by rfl⟩ : syracuseStep 5716939 = 8575409) B8575409
theorem B7622585 : Blo 2257435 7622585 := bstep (se 2 (by rfl) ⟨2858469, by rfl⟩ : syracuseStep 7622585 = 5716939) B5716939
theorem B5081723 : Blo 2257435 5081723 := bstep (se 1 (by rfl) ⟨3811292, by rfl⟩ : syracuseStep 5081723 = 7622585) B7622585
theorem B3387815 : Blo 2257435 3387815 := bstep (se 1 (by rfl) ⟨2540861, by rfl⟩ : syracuseStep 3387815 = 5081723) B5081723
theorem B2258543 : Blo 2257435 2258543 := bstep (se 1 (by rfl) ⟨1693907, by rfl⟩ : syracuseStep 2258543 = 3387815) B3387815
theorem B3387821 : Blo 2257435 3387821 := bbase (se 3 (by rfl) ⟨635216, by rfl⟩ : syracuseStep 3387821 = 1270433) (by norm_num)
theorem B2258547 : Blo 2257435 2258547 := bstep (se 1 (by rfl) ⟨1693910, by rfl⟩ : syracuseStep 2258547 = 3387821) B3387821
theorem B5081741 : Blo 2257435 5081741 := bbase (se 3 (by rfl) ⟨952826, by rfl⟩ : syracuseStep 5081741 = 1905653) (by norm_num)
theorem B3387827 : Blo 2257435 3387827 := bstep (se 1 (by rfl) ⟨2540870, by rfl⟩ : syracuseStep 3387827 = 5081741) B5081741
theorem B2258551 : Blo 2257435 2258551 := bstep (se 1 (by rfl) ⟨1693913, by rfl⟩ : syracuseStep 2258551 = 3387827) B3387827
theorem B2858485 : Blo 2257435 2858485 := bbase (se 5 (by rfl) ⟨133991, by rfl⟩ : syracuseStep 2858485 = 267983) (by norm_num)
theorem B3811313 : Blo 2257435 3811313 := bstep (se 2 (by rfl) ⟨1429242, by rfl⟩ : syracuseStep 3811313 = 2858485) B2858485
theorem B2540875 : Blo 2257435 2540875 := bstep (se 1 (by rfl) ⟨1905656, by rfl⟩ : syracuseStep 2540875 = 3811313) B3811313
theorem B3387833 : Blo 2257435 3387833 := bstep (se 2 (by rfl) ⟨1270437, by rfl⟩ : syracuseStep 3387833 = 2540875) B2540875
theorem B2258555 : Blo 2257435 2258555 := bstep (se 1 (by rfl) ⟨1693916, by rfl⟩ : syracuseStep 2258555 = 3387833) B3387833
theorem B4578749 : Blo 2257435 4578749 := bbase (se 3 (by rfl) ⟨858515, by rfl⟩ : syracuseStep 4578749 = 1717031) (by norm_num)
theorem B3052499 : Blo 2257435 3052499 := bstep (se 1 (by rfl) ⟨2289374, by rfl⟩ : syracuseStep 3052499 = 4578749) B4578749
theorem B8139997 : Blo 2257435 8139997 := bstep (se 3 (by rfl) ⟨1526249, by rfl⟩ : syracuseStep 8139997 = 3052499) B3052499
theorem B43413317 : Blo 2257435 43413317 := bstep (se 4 (by rfl) ⟨4069998, by rfl⟩ : syracuseStep 43413317 = 8139997) B8139997
theorem B28942211 : Blo 2257435 28942211 := bstep (se 1 (by rfl) ⟨21706658, by rfl⟩ : syracuseStep 28942211 = 43413317) B43413317
theorem B19294807 : Blo 2257435 19294807 := bstep (se 1 (by rfl) ⟨14471105, by rfl⟩ : syracuseStep 19294807 = 28942211) B28942211
theorem B25726409 : Blo 2257435 25726409 := bstep (se 2 (by rfl) ⟨9647403, by rfl⟩ : syracuseStep 25726409 = 19294807) B19294807
theorem B17150939 : Blo 2257435 17150939 := bstep (se 1 (by rfl) ⟨12863204, by rfl⟩ : syracuseStep 17150939 = 25726409) B25726409
theorem B11433959 : Blo 2257435 11433959 := bstep (se 1 (by rfl) ⟨8575469, by rfl⟩ : syracuseStep 11433959 = 17150939) B17150939
theorem B7622639 : Blo 2257435 7622639 := bstep (se 1 (by rfl) ⟨5716979, by rfl⟩ : syracuseStep 7622639 = 11433959) B11433959
theorem B5081759 : Blo 2257435 5081759 := bstep (se 1 (by rfl) ⟨3811319, by rfl⟩ : syracuseStep 5081759 = 7622639) B7622639
theorem B3387839 : Blo 2257435 3387839 := bstep (se 1 (by rfl) ⟨2540879, by rfl⟩ : syracuseStep 3387839 = 5081759) B5081759
theorem B2258559 : Blo 2257435 2258559 := bstep (se 1 (by rfl) ⟨1693919, by rfl⟩ : syracuseStep 2258559 = 3387839) B3387839
theorem B3387845 : Blo 2257435 3387845 := bbase (se 4 (by rfl) ⟨317610, by rfl⟩ : syracuseStep 3387845 = 635221) (by norm_num)
theorem B2258563 : Blo 2257435 2258563 := bstep (se 1 (by rfl) ⟨1693922, by rfl⟩ : syracuseStep 2258563 = 3387845) B3387845
theorem B3811333 : Blo 2257435 3811333 := bbase (se 4 (by rfl) ⟨357312, by rfl⟩ : syracuseStep 3811333 = 714625) (by norm_num)
theorem B5081777 : Blo 2257435 5081777 := bstep (se 2 (by rfl) ⟨1905666, by rfl⟩ : syracuseStep 5081777 = 3811333) B3811333
theorem B3387851 : Blo 2257435 3387851 := bstep (se 1 (by rfl) ⟨2540888, by rfl⟩ : syracuseStep 3387851 = 5081777) B5081777
theorem B2258567 : Blo 2257435 2258567 := bstep (se 1 (by rfl) ⟨1693925, by rfl⟩ : syracuseStep 2258567 = 3387851) B3387851
theorem B2540893 : Blo 2257435 2540893 := bbase (se 3 (by rfl) ⟨476417, by rfl⟩ : syracuseStep 2540893 = 952835) (by norm_num)
theorem B3387857 : Blo 2257435 3387857 := bstep (se 2 (by rfl) ⟨1270446, by rfl⟩ : syracuseStep 3387857 = 2540893) B2540893
theorem B2258571 : Blo 2257435 2258571 := bstep (se 1 (by rfl) ⟨1693928, by rfl⟩ : syracuseStep 2258571 = 3387857) B3387857
theorem B7622693 : Blo 2257435 7622693 := bbase (se 4 (by rfl) ⟨714627, by rfl⟩ : syracuseStep 7622693 = 1429255) (by norm_num)
theorem B5081795 : Blo 2257435 5081795 := bstep (se 1 (by rfl) ⟨3811346, by rfl⟩ : syracuseStep 5081795 = 7622693) B7622693
theorem B3387863 : Blo 2257435 3387863 := bstep (se 1 (by rfl) ⟨2540897, by rfl⟩ : syracuseStep 3387863 = 5081795) B5081795
theorem B2258575 : Blo 2257435 2258575 := bstep (se 1 (by rfl) ⟨1693931, by rfl⟩ : syracuseStep 2258575 = 3387863) B3387863
theorem B3387869 : Blo 2257435 3387869 := bbase (se 3 (by rfl) ⟨635225, by rfl⟩ : syracuseStep 3387869 = 1270451) (by norm_num)
theorem B2258579 : Blo 2257435 2258579 := bstep (se 1 (by rfl) ⟨1693934, by rfl⟩ : syracuseStep 2258579 = 3387869) B3387869
theorem B5081813 : Blo 2257435 5081813 := bbase (se 7 (by rfl) ⟨59552, by rfl⟩ : syracuseStep 5081813 = 119105) (by norm_num)
theorem B3387875 : Blo 2257435 3387875 := bstep (se 1 (by rfl) ⟨2540906, by rfl⟩ : syracuseStep 3387875 = 5081813) B5081813
theorem B2258583 : Blo 2257435 2258583 := bstep (se 1 (by rfl) ⟨1693937, by rfl⟩ : syracuseStep 2258583 = 3387875) B3387875
theorem B9647525 : Blo 2257435 9647525 := bbase (se 4 (by rfl) ⟨904455, by rfl⟩ : syracuseStep 9647525 = 1808911) (by norm_num)
theorem B6431683 : Blo 2257435 6431683 := bstep (se 1 (by rfl) ⟨4823762, by rfl⟩ : syracuseStep 6431683 = 9647525) B9647525
theorem B8575577 : Blo 2257435 8575577 := bstep (se 2 (by rfl) ⟨3215841, by rfl⟩ : syracuseStep 8575577 = 6431683) B6431683
theorem B5717051 : Blo 2257435 5717051 := bstep (se 1 (by rfl) ⟨4287788, by rfl⟩ : syracuseStep 5717051 = 8575577) B8575577
theorem B3811367 : Blo 2257435 3811367 := bstep (se 1 (by rfl) ⟨2858525, by rfl⟩ : syracuseStep 3811367 = 5717051) B5717051
theorem B2540911 : Blo 2257435 2540911 := bstep (se 1 (by rfl) ⟨1905683, by rfl⟩ : syracuseStep 2540911 = 3811367) B3811367
theorem B3387881 : Blo 2257435 3387881 := bstep (se 2 (by rfl) ⟨1270455, by rfl⟩ : syracuseStep 3387881 = 2540911) B2540911
theorem B2258587 : Blo 2257435 2258587 := bstep (se 1 (by rfl) ⟨1693940, by rfl⟩ : syracuseStep 2258587 = 3387881) B3387881
theorem B8363749 : Blo 2257435 8363749 := bbase (se 4 (by rfl) ⟨784101, by rfl⟩ : syracuseStep 8363749 = 1568203) (by norm_num)
theorem B11151665 : Blo 2257435 11151665 := bstep (se 2 (by rfl) ⟨4181874, by rfl⟩ : syracuseStep 11151665 = 8363749) B8363749
theorem B7434443 : Blo 2257435 7434443 := bstep (se 1 (by rfl) ⟨5575832, by rfl⟩ : syracuseStep 7434443 = 11151665) B11151665
theorem B4956295 : Blo 2257435 4956295 := bstep (se 1 (by rfl) ⟨3717221, by rfl⟩ : syracuseStep 4956295 = 7434443) B7434443
theorem B6608393 : Blo 2257435 6608393 := bstep (se 2 (by rfl) ⟨2478147, by rfl⟩ : syracuseStep 6608393 = 4956295) B4956295
theorem B4405595 : Blo 2257435 4405595 := bstep (se 1 (by rfl) ⟨3304196, by rfl⟩ : syracuseStep 4405595 = 6608393) B6608393
theorem B11748253 : Blo 2257435 11748253 := bstep (se 3 (by rfl) ⟨2202797, by rfl⟩ : syracuseStep 11748253 = 4405595) B4405595
theorem B15664337 : Blo 2257435 15664337 := bstep (se 2 (by rfl) ⟨5874126, by rfl⟩ : syracuseStep 15664337 = 11748253) B11748253
theorem B10442891 : Blo 2257435 10442891 := bstep (se 1 (by rfl) ⟨7832168, by rfl⟩ : syracuseStep 10442891 = 15664337) B15664337
theorem B27847709 : Blo 2257435 27847709 := bstep (se 3 (by rfl) ⟨5221445, by rfl⟩ : syracuseStep 27847709 = 10442891) B10442891
theorem B18565139 : Blo 2257435 18565139 := bstep (se 1 (by rfl) ⟨13923854, by rfl⟩ : syracuseStep 18565139 = 27847709) B27847709
theorem B49507037 : Blo 2257435 49507037 := bstep (se 3 (by rfl) ⟨9282569, by rfl⟩ : syracuseStep 49507037 = 18565139) B18565139
theorem B33004691 : Blo 2257435 33004691 := bstep (se 1 (by rfl) ⟨24753518, by rfl⟩ : syracuseStep 33004691 = 49507037) B49507037
theorem B22003127 : Blo 2257435 22003127 := bstep (se 1 (by rfl) ⟨16502345, by rfl⟩ : syracuseStep 22003127 = 33004691) B33004691
theorem B14668751 : Blo 2257435 14668751 := bstep (se 1 (by rfl) ⟨11001563, by rfl⟩ : syracuseStep 14668751 = 22003127) B22003127
theorem B9779167 : Blo 2257435 9779167 := bstep (se 1 (by rfl) ⟨7334375, by rfl⟩ : syracuseStep 9779167 = 14668751) B14668751
theorem B13038889 : Blo 2257435 13038889 := bstep (se 2 (by rfl) ⟨4889583, by rfl⟩ : syracuseStep 13038889 = 9779167) B9779167
theorem B17385185 : Blo 2257435 17385185 := bstep (se 2 (by rfl) ⟨6519444, by rfl⟩ : syracuseStep 17385185 = 13038889) B13038889
theorem B11590123 : Blo 2257435 11590123 := bstep (se 1 (by rfl) ⟨8692592, by rfl⟩ : syracuseStep 11590123 = 17385185) B17385185
theorem B15453497 : Blo 2257435 15453497 := bstep (se 2 (by rfl) ⟨5795061, by rfl⟩ : syracuseStep 15453497 = 11590123) B11590123
theorem B10302331 : Blo 2257435 10302331 := bstep (se 1 (by rfl) ⟨7726748, by rfl⟩ : syracuseStep 10302331 = 15453497) B15453497
theorem B13736441 : Blo 2257435 13736441 := bstep (se 2 (by rfl) ⟨5151165, by rfl⟩ : syracuseStep 13736441 = 10302331) B10302331
theorem B9157627 : Blo 2257435 9157627 := bstep (se 1 (by rfl) ⟨6868220, by rfl⟩ : syracuseStep 9157627 = 13736441) B13736441
theorem B48840677 : Blo 2257435 48840677 := bstep (se 4 (by rfl) ⟨4578813, by rfl⟩ : syracuseStep 48840677 = 9157627) B9157627
theorem B32560451 : Blo 2257435 32560451 := bstep (se 1 (by rfl) ⟨24420338, by rfl⟩ : syracuseStep 32560451 = 48840677) B48840677
theorem B21706967 : Blo 2257435 21706967 := bstep (se 1 (by rfl) ⟨16280225, by rfl⟩ : syracuseStep 21706967 = 32560451) B32560451
theorem B14471311 : Blo 2257435 14471311 := bstep (se 1 (by rfl) ⟨10853483, by rfl⟩ : syracuseStep 14471311 = 21706967) B21706967
theorem B19295081 : Blo 2257435 19295081 := bstep (se 2 (by rfl) ⟨7235655, by rfl⟩ : syracuseStep 19295081 = 14471311) B14471311
theorem B12863387 : Blo 2257435 12863387 := bstep (se 1 (by rfl) ⟨9647540, by rfl⟩ : syracuseStep 12863387 = 19295081) B19295081
theorem B8575591 : Blo 2257435 8575591 := bstep (se 1 (by rfl) ⟨6431693, by rfl⟩ : syracuseStep 8575591 = 12863387) B12863387
theorem B11434121 : Blo 2257435 11434121 := bstep (se 2 (by rfl) ⟨4287795, by rfl⟩ : syracuseStep 11434121 = 8575591) B8575591
theorem B7622747 : Blo 2257435 7622747 := bstep (se 1 (by rfl) ⟨5717060, by rfl⟩ : syracuseStep 7622747 = 11434121) B11434121
theorem B5081831 : Blo 2257435 5081831 := bstep (se 1 (by rfl) ⟨3811373, by rfl⟩ : syracuseStep 5081831 = 7622747) B7622747
theorem B3387887 : Blo 2257435 3387887 := bstep (se 1 (by rfl) ⟨2540915, by rfl⟩ : syracuseStep 3387887 = 5081831) B5081831
theorem B2258591 : Blo 2257435 2258591 := bstep (se 1 (by rfl) ⟨1693943, by rfl⟩ : syracuseStep 2258591 = 3387887) B3387887
theorem B3387893 : Blo 2257435 3387893 := bbase (se 5 (by rfl) ⟨158807, by rfl⟩ : syracuseStep 3387893 = 317615) (by norm_num)
theorem B2258595 : Blo 2257435 2258595 := bstep (se 1 (by rfl) ⟨1693946, by rfl⟩ : syracuseStep 2258595 = 3387893) B3387893
theorem B6431717 : Blo 2257435 6431717 := bbase (se 4 (by rfl) ⟨602973, by rfl⟩ : syracuseStep 6431717 = 1205947) (by norm_num)
theorem B4287811 : Blo 2257435 4287811 := bstep (se 1 (by rfl) ⟨3215858, by rfl⟩ : syracuseStep 4287811 = 6431717) B6431717
theorem B5717081 : Blo 2257435 5717081 := bstep (se 2 (by rfl) ⟨2143905, by rfl⟩ : syracuseStep 5717081 = 4287811) B4287811
theorem B3811387 : Blo 2257435 3811387 := bstep (se 1 (by rfl) ⟨2858540, by rfl⟩ : syracuseStep 3811387 = 5717081) B5717081
theorem B5081849 : Blo 2257435 5081849 := bstep (se 2 (by rfl) ⟨1905693, by rfl⟩ : syracuseStep 5081849 = 3811387) B3811387
theorem B3387899 : Blo 2257435 3387899 := bstep (se 1 (by rfl) ⟨2540924, by rfl⟩ : syracuseStep 3387899 = 5081849) B5081849
theorem B2258599 : Blo 2257435 2258599 := bstep (se 1 (by rfl) ⟨1693949, by rfl⟩ : syracuseStep 2258599 = 3387899) B3387899
theorem B2540929 : Blo 2257435 2540929 := bbase (se 2 (by rfl) ⟨952848, by rfl⟩ : syracuseStep 2540929 = 1905697) (by norm_num)
theorem B3387905 : Blo 2257435 3387905 := bstep (se 2 (by rfl) ⟨1270464, by rfl⟩ : syracuseStep 3387905 = 2540929) B2540929
theorem B2258603 : Blo 2257435 2258603 := bstep (se 1 (by rfl) ⟨1693952, by rfl⟩ : syracuseStep 2258603 = 3387905) B3387905
theorem B5717101 : Blo 2257435 5717101 := bbase (se 3 (by rfl) ⟨1071956, by rfl⟩ : syracuseStep 5717101 = 2143913) (by norm_num)
theorem B7622801 : Blo 2257435 7622801 := bstep (se 2 (by rfl) ⟨2858550, by rfl⟩ : syracuseStep 7622801 = 5717101) B5717101
theorem B5081867 : Blo 2257435 5081867 := bstep (se 1 (by rfl) ⟨3811400, by rfl⟩ : syracuseStep 5081867 = 7622801) B7622801
theorem B3387911 : Blo 2257435 3387911 := bstep (se 1 (by rfl) ⟨2540933, by rfl⟩ : syracuseStep 3387911 = 5081867) B5081867
theorem B2258607 : Blo 2257435 2258607 := bstep (se 1 (by rfl) ⟨1693955, by rfl⟩ : syracuseStep 2258607 = 3387911) B3387911
theorem B3387917 : Blo 2257435 3387917 := bbase (se 3 (by rfl) ⟨635234, by rfl⟩ : syracuseStep 3387917 = 1270469) (by norm_num)
theorem B2258611 : Blo 2257435 2258611 := bstep (se 1 (by rfl) ⟨1693958, by rfl⟩ : syracuseStep 2258611 = 3387917) B3387917
theorem B5081885 : Blo 2257435 5081885 := bbase (se 3 (by rfl) ⟨952853, by rfl⟩ : syracuseStep 5081885 = 1905707) (by norm_num)
theorem B3387923 : Blo 2257435 3387923 := bstep (se 1 (by rfl) ⟨2540942, by rfl⟩ : syracuseStep 3387923 = 5081885) B5081885
theorem B2258615 : Blo 2257435 2258615 := bstep (se 1 (by rfl) ⟨1693961, by rfl⟩ : syracuseStep 2258615 = 3387923) B3387923
theorem B3811421 : Blo 2257435 3811421 := bbase (se 3 (by rfl) ⟨714641, by rfl⟩ : syracuseStep 3811421 = 1429283) (by norm_num)
theorem B2540947 : Blo 2257435 2540947 := bstep (se 1 (by rfl) ⟨1905710, by rfl⟩ : syracuseStep 2540947 = 3811421) B3811421
theorem B3387929 : Blo 2257435 3387929 := bstep (se 2 (by rfl) ⟨1270473, by rfl⟩ : syracuseStep 3387929 = 2540947) B2540947
theorem B2258619 : Blo 2257435 2258619 := bstep (se 1 (by rfl) ⟨1693964, by rfl⟩ : syracuseStep 2258619 = 3387929) B3387929
theorem B8140229 : Blo 2257435 8140229 := bbase (se 4 (by rfl) ⟨763146, by rfl⟩ : syracuseStep 8140229 = 1526293) (by norm_num)
theorem B5426819 : Blo 2257435 5426819 := bstep (se 1 (by rfl) ⟨4070114, by rfl⟩ : syracuseStep 5426819 = 8140229) B8140229
theorem B3617879 : Blo 2257435 3617879 := bstep (se 1 (by rfl) ⟨2713409, by rfl⟩ : syracuseStep 3617879 = 5426819) B5426819
theorem B9647677 : Blo 2257435 9647677 := bstep (se 3 (by rfl) ⟨1808939, by rfl⟩ : syracuseStep 9647677 = 3617879) B3617879
theorem B12863569 : Blo 2257435 12863569 := bstep (se 2 (by rfl) ⟨4823838, by rfl⟩ : syracuseStep 12863569 = 9647677) B9647677
theorem B17151425 : Blo 2257435 17151425 := bstep (se 2 (by rfl) ⟨6431784, by rfl⟩ : syracuseStep 17151425 = 12863569) B12863569
theorem B11434283 : Blo 2257435 11434283 := bstep (se 1 (by rfl) ⟨8575712, by rfl⟩ : syracuseStep 11434283 = 17151425) B17151425
theorem B7622855 : Blo 2257435 7622855 := bstep (se 1 (by rfl) ⟨5717141, by rfl⟩ : syracuseStep 7622855 = 11434283) B11434283
theorem B5081903 : Blo 2257435 5081903 := bstep (se 1 (by rfl) ⟨3811427, by rfl⟩ : syracuseStep 5081903 = 7622855) B7622855
theorem B3387935 : Blo 2257435 3387935 := bstep (se 1 (by rfl) ⟨2540951, by rfl⟩ : syracuseStep 3387935 = 5081903) B5081903
theorem B2258623 : Blo 2257435 2258623 := bstep (se 1 (by rfl) ⟨1693967, by rfl⟩ : syracuseStep 2258623 = 3387935) B3387935
theorem B3387941 : Blo 2257435 3387941 := bbase (se 4 (by rfl) ⟨317619, by rfl⟩ : syracuseStep 3387941 = 635239) (by norm_num)
theorem B2258627 : Blo 2257435 2258627 := bstep (se 1 (by rfl) ⟨1693970, by rfl⟩ : syracuseStep 2258627 = 3387941) B3387941
theorem B2858581 : Blo 2257435 2858581 := bbase (se 8 (by rfl) ⟨16749, by rfl⟩ : syracuseStep 2858581 = 33499) (by norm_num)
theorem B3811441 : Blo 2257435 3811441 := bstep (se 2 (by rfl) ⟨1429290, by rfl⟩ : syracuseStep 3811441 = 2858581) B2858581
theorem B5081921 : Blo 2257435 5081921 := bstep (se 2 (by rfl) ⟨1905720, by rfl⟩ : syracuseStep 5081921 = 3811441) B3811441
theorem B3387947 : Blo 2257435 3387947 := bstep (se 1 (by rfl) ⟨2540960, by rfl⟩ : syracuseStep 3387947 = 5081921) B5081921
theorem B2258631 : Blo 2257435 2258631 := bstep (se 1 (by rfl) ⟨1693973, by rfl⟩ : syracuseStep 2258631 = 3387947) B3387947
theorem B2540965 : Blo 2257435 2540965 := bbase (se 4 (by rfl) ⟨238215, by rfl⟩ : syracuseStep 2540965 = 476431) (by norm_num)
theorem B3387953 : Blo 2257435 3387953 := bstep (se 2 (by rfl) ⟨1270482, by rfl⟩ : syracuseStep 3387953 = 2540965) B2540965
theorem B2258635 : Blo 2257435 2258635 := bstep (se 1 (by rfl) ⟨1693976, by rfl⟩ : syracuseStep 2258635 = 3387953) B3387953
theorem B2713429 : Blo 2257435 2713429 := bbase (se 9 (by rfl) ⟨7949, by rfl⟩ : syracuseStep 2713429 = 15899) (by norm_num)
theorem B14471621 : Blo 2257435 14471621 := bstep (se 4 (by rfl) ⟨1356714, by rfl⟩ : syracuseStep 14471621 = 2713429) B2713429
theorem B9647747 : Blo 2257435 9647747 := bstep (se 1 (by rfl) ⟨7235810, by rfl⟩ : syracuseStep 9647747 = 14471621) B14471621
theorem B6431831 : Blo 2257435 6431831 := bstep (se 1 (by rfl) ⟨4823873, by rfl⟩ : syracuseStep 6431831 = 9647747) B9647747
theorem B4287887 : Blo 2257435 4287887 := bstep (se 1 (by rfl) ⟨3215915, by rfl⟩ : syracuseStep 4287887 = 6431831) B6431831
theorem B2858591 : Blo 2257435 2858591 := bstep (se 1 (by rfl) ⟨2143943, by rfl⟩ : syracuseStep 2858591 = 4287887) B4287887
theorem B7622909 : Blo 2257435 7622909 := bstep (se 3 (by rfl) ⟨1429295, by rfl⟩ : syracuseStep 7622909 = 2858591) B2858591
theorem B5081939 : Blo 2257435 5081939 := bstep (se 1 (by rfl) ⟨3811454, by rfl⟩ : syracuseStep 5081939 = 7622909) B7622909
theorem B3387959 : Blo 2257435 3387959 := bstep (se 1 (by rfl) ⟨2540969, by rfl⟩ : syracuseStep 3387959 = 5081939) B5081939
theorem B2258639 : Blo 2257435 2258639 := bstep (se 1 (by rfl) ⟨1693979, by rfl⟩ : syracuseStep 2258639 = 3387959) B3387959
theorem B3387965 : Blo 2257435 3387965 := bbase (se 3 (by rfl) ⟨635243, by rfl⟩ : syracuseStep 3387965 = 1270487) (by norm_num)
theorem B2258643 : Blo 2257435 2258643 := bstep (se 1 (by rfl) ⟨1693982, by rfl⟩ : syracuseStep 2258643 = 3387965) B3387965
theorem B5081957 : Blo 2257435 5081957 := bbase (se 4 (by rfl) ⟨476433, by rfl⟩ : syracuseStep 5081957 = 952867) (by norm_num)
theorem B3387971 : Blo 2257435 3387971 := bstep (se 1 (by rfl) ⟨2540978, by rfl⟩ : syracuseStep 3387971 = 5081957) B5081957
theorem B2258647 : Blo 2257435 2258647 := bstep (se 1 (by rfl) ⟨1693985, by rfl⟩ : syracuseStep 2258647 = 3387971) B3387971
theorem B5717213 : Blo 2257435 5717213 := bbase (se 3 (by rfl) ⟨1071977, by rfl⟩ : syracuseStep 5717213 = 2143955) (by norm_num)
theorem B3811475 : Blo 2257435 3811475 := bstep (se 1 (by rfl) ⟨2858606, by rfl⟩ : syracuseStep 3811475 = 5717213) B5717213
theorem B2540983 : Blo 2257435 2540983 := bstep (se 1 (by rfl) ⟨1905737, by rfl⟩ : syracuseStep 2540983 = 3811475) B3811475
theorem B3387977 : Blo 2257435 3387977 := bstep (se 2 (by rfl) ⟨1270491, by rfl⟩ : syracuseStep 3387977 = 2540983) B2540983
theorem B2258651 : Blo 2257435 2258651 := bstep (se 1 (by rfl) ⟨1693988, by rfl⟩ : syracuseStep 2258651 = 3387977) B3387977
theorem B4287917 : Blo 2257435 4287917 := bbase (se 3 (by rfl) ⟨803984, by rfl⟩ : syracuseStep 4287917 = 1607969) (by norm_num)
theorem B11434445 : Blo 2257435 11434445 := bstep (se 3 (by rfl) ⟨2143958, by rfl⟩ : syracuseStep 11434445 = 4287917) B4287917
theorem B7622963 : Blo 2257435 7622963 := bstep (se 1 (by rfl) ⟨5717222, by rfl⟩ : syracuseStep 7622963 = 11434445) B11434445
theorem B5081975 : Blo 2257435 5081975 := bstep (se 1 (by rfl) ⟨3811481, by rfl⟩ : syracuseStep 5081975 = 7622963) B7622963
theorem B3387983 : Blo 2257435 3387983 := bstep (se 1 (by rfl) ⟨2540987, by rfl⟩ : syracuseStep 3387983 = 5081975) B5081975
theorem B2258655 : Blo 2257435 2258655 := bstep (se 1 (by rfl) ⟨1693991, by rfl⟩ : syracuseStep 2258655 = 3387983) B3387983
theorem B3387989 : Blo 2257435 3387989 := bbase (se 8 (by rfl) ⟨19851, by rfl⟩ : syracuseStep 3387989 = 39703) (by norm_num)
theorem B2258659 : Blo 2257435 2258659 := bstep (se 1 (by rfl) ⟨1693994, by rfl⟩ : syracuseStep 2258659 = 3387989) B3387989
theorem B10302661 : Blo 2257435 10302661 := bbase (se 4 (by rfl) ⟨965874, by rfl⟩ : syracuseStep 10302661 = 1931749) (by norm_num)
theorem B13736881 : Blo 2257435 13736881 := bstep (se 2 (by rfl) ⟨5151330, by rfl⟩ : syracuseStep 13736881 = 10302661) B10302661
theorem B18315841 : Blo 2257435 18315841 := bstep (se 2 (by rfl) ⟨6868440, by rfl⟩ : syracuseStep 18315841 = 13736881) B13736881
theorem B24421121 : Blo 2257435 24421121 := bstep (se 2 (by rfl) ⟨9157920, by rfl⟩ : syracuseStep 24421121 = 18315841) B18315841
theorem B16280747 : Blo 2257435 16280747 := bstep (se 1 (by rfl) ⟨12210560, by rfl⟩ : syracuseStep 16280747 = 24421121) B24421121
theorem B10853831 : Blo 2257435 10853831 := bstep (se 1 (by rfl) ⟨8140373, by rfl⟩ : syracuseStep 10853831 = 16280747) B16280747
theorem B7235887 : Blo 2257435 7235887 := bstep (se 1 (by rfl) ⟨5426915, by rfl⟩ : syracuseStep 7235887 = 10853831) B10853831
theorem B9647849 : Blo 2257435 9647849 := bstep (se 2 (by rfl) ⟨3617943, by rfl⟩ : syracuseStep 9647849 = 7235887) B7235887
theorem B6431899 : Blo 2257435 6431899 := bstep (se 1 (by rfl) ⟨4823924, by rfl⟩ : syracuseStep 6431899 = 9647849) B9647849
theorem B8575865 : Blo 2257435 8575865 := bstep (se 2 (by rfl) ⟨3215949, by rfl⟩ : syracuseStep 8575865 = 6431899) B6431899
theorem B5717243 : Blo 2257435 5717243 := bstep (se 1 (by rfl) ⟨4287932, by rfl⟩ : syracuseStep 5717243 = 8575865) B8575865
theorem B3811495 : Blo 2257435 3811495 := bstep (se 1 (by rfl) ⟨2858621, by rfl⟩ : syracuseStep 3811495 = 5717243) B5717243
theorem B5081993 : Blo 2257435 5081993 := bstep (se 2 (by rfl) ⟨1905747, by rfl⟩ : syracuseStep 5081993 = 3811495) B3811495
theorem B3387995 : Blo 2257435 3387995 := bstep (se 1 (by rfl) ⟨2540996, by rfl⟩ : syracuseStep 3387995 = 5081993) B5081993
theorem B2258663 : Blo 2257435 2258663 := bstep (se 1 (by rfl) ⟨1693997, by rfl⟩ : syracuseStep 2258663 = 3387995) B3387995
theorem B2541001 : Blo 2257435 2541001 := bbase (se 2 (by rfl) ⟨952875, by rfl⟩ : syracuseStep 2541001 = 1905751) (by norm_num)
theorem B3388001 : Blo 2257435 3388001 := bstep (se 2 (by rfl) ⟨1270500, by rfl⟩ : syracuseStep 3388001 = 2541001) B2541001
theorem B2258667 : Blo 2257435 2258667 := bstep (se 1 (by rfl) ⟨1694000, by rfl⟩ : syracuseStep 2258667 = 3388001) B3388001
theorem B19295765 : Blo 2257435 19295765 := bbase (se 6 (by rfl) ⟨452244, by rfl⟩ : syracuseStep 19295765 = 904489) (by norm_num)
theorem B12863843 : Blo 2257435 12863843 := bstep (se 1 (by rfl) ⟨9647882, by rfl⟩ : syracuseStep 12863843 = 19295765) B19295765
theorem B8575895 : Blo 2257435 8575895 := bstep (se 1 (by rfl) ⟨6431921, by rfl⟩ : syracuseStep 8575895 = 12863843) B12863843
theorem B5717263 : Blo 2257435 5717263 := bstep (se 1 (by rfl) ⟨4287947, by rfl⟩ : syracuseStep 5717263 = 8575895) B8575895
theorem B7623017 : Blo 2257435 7623017 := bstep (se 2 (by rfl) ⟨2858631, by rfl⟩ : syracuseStep 7623017 = 5717263) B5717263
theorem B5082011 : Blo 2257435 5082011 := bstep (se 1 (by rfl) ⟨3811508, by rfl⟩ : syracuseStep 5082011 = 7623017) B7623017
theorem B3388007 : Blo 2257435 3388007 := bstep (se 1 (by rfl) ⟨2541005, by rfl⟩ : syracuseStep 3388007 = 5082011) B5082011
theorem B2258671 : Blo 2257435 2258671 := bstep (se 1 (by rfl) ⟨1694003, by rfl⟩ : syracuseStep 2258671 = 3388007) B3388007
theorem B3388013 : Blo 2257435 3388013 := bbase (se 3 (by rfl) ⟨635252, by rfl⟩ : syracuseStep 3388013 = 1270505) (by norm_num)
theorem B2258675 : Blo 2257435 2258675 := bstep (se 1 (by rfl) ⟨1694006, by rfl⟩ : syracuseStep 2258675 = 3388013) B3388013
theorem B5082029 : Blo 2257435 5082029 := bbase (se 3 (by rfl) ⟨952880, by rfl⟩ : syracuseStep 5082029 = 1905761) (by norm_num)
theorem B3388019 : Blo 2257435 3388019 := bstep (se 1 (by rfl) ⟨2541014, by rfl⟩ : syracuseStep 3388019 = 5082029) B5082029
theorem B2258679 : Blo 2257435 2258679 := bstep (se 1 (by rfl) ⟨1694009, by rfl⟩ : syracuseStep 2258679 = 3388019) B3388019
theorem B6431957 : Blo 2257435 6431957 := bbase (se 7 (by rfl) ⟨75374, by rfl⟩ : syracuseStep 6431957 = 150749) (by norm_num)
theorem B4287971 : Blo 2257435 4287971 := bstep (se 1 (by rfl) ⟨3215978, by rfl⟩ : syracuseStep 4287971 = 6431957) B6431957
theorem B2858647 : Blo 2257435 2858647 := bstep (se 1 (by rfl) ⟨2143985, by rfl⟩ : syracuseStep 2858647 = 4287971) B4287971
theorem B3811529 : Blo 2257435 3811529 := bstep (se 2 (by rfl) ⟨1429323, by rfl⟩ : syracuseStep 3811529 = 2858647) B2858647
theorem B2541019 : Blo 2257435 2541019 := bstep (se 1 (by rfl) ⟨1905764, by rfl⟩ : syracuseStep 2541019 = 3811529) B3811529
theorem B3388025 : Blo 2257435 3388025 := bstep (se 2 (by rfl) ⟨1270509, by rfl⟩ : syracuseStep 3388025 = 2541019) B2541019
theorem B2258683 : Blo 2257435 2258683 := bstep (se 1 (by rfl) ⟨1694012, by rfl⟩ : syracuseStep 2258683 = 3388025) B3388025
theorem B3528605 : Blo 2257435 3528605 := bbase (se 3 (by rfl) ⟨661613, by rfl⟩ : syracuseStep 3528605 = 1323227) (by norm_num)
theorem B9409613 : Blo 2257435 9409613 := bstep (se 3 (by rfl) ⟨1764302, by rfl⟩ : syracuseStep 9409613 = 3528605) B3528605
theorem B25092301 : Blo 2257435 25092301 := bstep (se 3 (by rfl) ⟨4704806, by rfl⟩ : syracuseStep 25092301 = 9409613) B9409613
theorem B33456401 : Blo 2257435 33456401 := bstep (se 2 (by rfl) ⟨12546150, by rfl⟩ : syracuseStep 33456401 = 25092301) B25092301
theorem B22304267 : Blo 2257435 22304267 := bstep (se 1 (by rfl) ⟨16728200, by rfl⟩ : syracuseStep 22304267 = 33456401) B33456401
theorem B14869511 : Blo 2257435 14869511 := bstep (se 1 (by rfl) ⟨11152133, by rfl⟩ : syracuseStep 14869511 = 22304267) B22304267
theorem B9913007 : Blo 2257435 9913007 := bstep (se 1 (by rfl) ⟨7434755, by rfl⟩ : syracuseStep 9913007 = 14869511) B14869511
theorem B6608671 : Blo 2257435 6608671 := bstep (se 1 (by rfl) ⟨4956503, by rfl⟩ : syracuseStep 6608671 = 9913007) B9913007
theorem B35246245 : Blo 2257435 35246245 := bstep (se 4 (by rfl) ⟨3304335, by rfl⟩ : syracuseStep 35246245 = 6608671) B6608671
theorem B46994993 : Blo 2257435 46994993 := bstep (se 2 (by rfl) ⟨17623122, by rfl⟩ : syracuseStep 46994993 = 35246245) B35246245
theorem B31329995 : Blo 2257435 31329995 := bstep (se 1 (by rfl) ⟨23497496, by rfl⟩ : syracuseStep 31329995 = 46994993) B46994993
theorem B83546653 : Blo 2257435 83546653 := bstep (se 3 (by rfl) ⟨15664997, by rfl⟩ : syracuseStep 83546653 = 31329995) B31329995
theorem B111395537 : Blo 2257435 111395537 := bstep (se 2 (by rfl) ⟨41773326, by rfl⟩ : syracuseStep 111395537 = 83546653) B83546653
theorem B74263691 : Blo 2257435 74263691 := bstep (se 1 (by rfl) ⟨55697768, by rfl⟩ : syracuseStep 74263691 = 111395537) B111395537
theorem B49509127 : Blo 2257435 49509127 := bstep (se 1 (by rfl) ⟨37131845, by rfl⟩ : syracuseStep 49509127 = 74263691) B74263691
theorem B66012169 : Blo 2257435 66012169 := bstep (se 2 (by rfl) ⟨24754563, by rfl⟩ : syracuseStep 66012169 = 49509127) B49509127
theorem B88016225 : Blo 2257435 88016225 := bstep (se 2 (by rfl) ⟨33006084, by rfl⟩ : syracuseStep 88016225 = 66012169) B66012169
theorem B938839733 : Blo 2257435 938839733 := bstep (se 5 (by rfl) ⟨44008112, by rfl⟩ : syracuseStep 938839733 = 88016225) B88016225
theorem B625893155 : Blo 2257435 625893155 := bstep (se 1 (by rfl) ⟨469419866, by rfl⟩ : syracuseStep 625893155 = 938839733) B938839733
theorem B417262103 : Blo 2257435 417262103 := bstep (se 1 (by rfl) ⟨312946577, by rfl⟩ : syracuseStep 417262103 = 625893155) B625893155
theorem B278174735 : Blo 2257435 278174735 := bstep (se 1 (by rfl) ⟨208631051, by rfl⟩ : syracuseStep 278174735 = 417262103) B417262103
theorem B185449823 : Blo 2257435 185449823 := bstep (se 1 (by rfl) ⟨139087367, by rfl⟩ : syracuseStep 185449823 = 278174735) B278174735
theorem B123633215 : Blo 2257435 123633215 := bstep (se 1 (by rfl) ⟨92724911, by rfl⟩ : syracuseStep 123633215 = 185449823) B185449823
theorem B82422143 : Blo 2257435 82422143 := bstep (se 1 (by rfl) ⟨61816607, by rfl⟩ : syracuseStep 82422143 = 123633215) B123633215
theorem B54948095 : Blo 2257435 54948095 := bstep (se 1 (by rfl) ⟨41211071, by rfl⟩ : syracuseStep 54948095 = 82422143) B82422143
theorem B36632063 : Blo 2257435 36632063 := bstep (se 1 (by rfl) ⟨27474047, by rfl⟩ : syracuseStep 36632063 = 54948095) B54948095
theorem B24421375 : Blo 2257435 24421375 := bstep (se 1 (by rfl) ⟨18316031, by rfl⟩ : syracuseStep 24421375 = 36632063) B36632063
theorem B32561833 : Blo 2257435 32561833 := bstep (se 2 (by rfl) ⟨12210687, by rfl⟩ : syracuseStep 32561833 = 24421375) B24421375
theorem B43415777 : Blo 2257435 43415777 := bstep (se 2 (by rfl) ⟨16280916, by rfl⟩ : syracuseStep 43415777 = 32561833) B32561833
theorem B28943851 : Blo 2257435 28943851 := bstep (se 1 (by rfl) ⟨21707888, by rfl⟩ : syracuseStep 28943851 = 43415777) B43415777
theorem B38591801 : Blo 2257435 38591801 := bstep (se 2 (by rfl) ⟨14471925, by rfl⟩ : syracuseStep 38591801 = 28943851) B28943851
theorem B25727867 : Blo 2257435 25727867 := bstep (se 1 (by rfl) ⟨19295900, by rfl⟩ : syracuseStep 25727867 = 38591801) B38591801
theorem B17151911 : Blo 2257435 17151911 := bstep (se 1 (by rfl) ⟨12863933, by rfl⟩ : syracuseStep 17151911 = 25727867) B25727867
theorem B11434607 : Blo 2257435 11434607 := bstep (se 1 (by rfl) ⟨8575955, by rfl⟩ : syracuseStep 11434607 = 17151911) B17151911
theorem B7623071 : Blo 2257435 7623071 := bstep (se 1 (by rfl) ⟨5717303, by rfl⟩ : syracuseStep 7623071 = 11434607) B11434607
theorem B5082047 : Blo 2257435 5082047 := bstep (se 1 (by rfl) ⟨3811535, by rfl⟩ : syracuseStep 5082047 = 7623071) B7623071
theorem B3388031 : Blo 2257435 3388031 := bstep (se 1 (by rfl) ⟨2541023, by rfl⟩ : syracuseStep 3388031 = 5082047) B5082047
theorem B2258687 : Blo 2257435 2258687 := bstep (se 1 (by rfl) ⟨1694015, by rfl⟩ : syracuseStep 2258687 = 3388031) B3388031
theorem B3388037 : Blo 2257435 3388037 := bbase (se 4 (by rfl) ⟨317628, by rfl⟩ : syracuseStep 3388037 = 635257) (by norm_num)
theorem B2258691 : Blo 2257435 2258691 := bstep (se 1 (by rfl) ⟨1694018, by rfl⟩ : syracuseStep 2258691 = 3388037) B3388037
theorem B3811549 : Blo 2257435 3811549 := bbase (se 3 (by rfl) ⟨714665, by rfl⟩ : syracuseStep 3811549 = 1429331) (by norm_num)
theorem B5082065 : Blo 2257435 5082065 := bstep (se 2 (by rfl) ⟨1905774, by rfl⟩ : syracuseStep 5082065 = 3811549) B3811549
theorem B3388043 : Blo 2257435 3388043 := bstep (se 1 (by rfl) ⟨2541032, by rfl⟩ : syracuseStep 3388043 = 5082065) B5082065
theorem B2258695 : Blo 2257435 2258695 := bstep (se 1 (by rfl) ⟨1694021, by rfl⟩ : syracuseStep 2258695 = 3388043) B3388043
theorem B2541037 : Blo 2257435 2541037 := bbase (se 3 (by rfl) ⟨476444, by rfl⟩ : syracuseStep 2541037 = 952889) (by norm_num)
theorem B3388049 : Blo 2257435 3388049 := bstep (se 2 (by rfl) ⟨1270518, by rfl⟩ : syracuseStep 3388049 = 2541037) B2541037
theorem B2258699 : Blo 2257435 2258699 := bstep (se 1 (by rfl) ⟨1694024, by rfl⟩ : syracuseStep 2258699 = 3388049) B3388049
theorem B7623125 : Blo 2257435 7623125 := bbase (se 7 (by rfl) ⟨89333, by rfl⟩ : syracuseStep 7623125 = 178667) (by norm_num)
theorem B5082083 : Blo 2257435 5082083 := bstep (se 1 (by rfl) ⟨3811562, by rfl⟩ : syracuseStep 5082083 = 7623125) B7623125
theorem B3388055 : Blo 2257435 3388055 := bstep (se 1 (by rfl) ⟨2541041, by rfl⟩ : syracuseStep 3388055 = 5082083) B5082083
theorem B2258703 : Blo 2257435 2258703 := bstep (se 1 (by rfl) ⟨1694027, by rfl⟩ : syracuseStep 2258703 = 3388055) B3388055
theorem B3388061 : Blo 2257435 3388061 := bbase (se 3 (by rfl) ⟨635261, by rfl⟩ : syracuseStep 3388061 = 1270523) (by norm_num)
theorem B2258707 : Blo 2257435 2258707 := bstep (se 1 (by rfl) ⟨1694030, by rfl⟩ : syracuseStep 2258707 = 3388061) B3388061
theorem B5082101 : Blo 2257435 5082101 := bbase (se 5 (by rfl) ⟨238223, by rfl⟩ : syracuseStep 5082101 = 476447) (by norm_num)
theorem B3388067 : Blo 2257435 3388067 := bstep (se 1 (by rfl) ⟨2541050, by rfl⟩ : syracuseStep 3388067 = 5082101) B5082101
theorem B2258711 : Blo 2257435 2258711 := bstep (se 1 (by rfl) ⟨1694033, by rfl⟩ : syracuseStep 2258711 = 3388067) B3388067
theorem B5795381 : Blo 2257435 5795381 := bbase (se 5 (by rfl) ⟨271658, by rfl⟩ : syracuseStep 5795381 = 543317) (by norm_num)
theorem B3863587 : Blo 2257435 3863587 := bstep (se 1 (by rfl) ⟨2897690, by rfl⟩ : syracuseStep 3863587 = 5795381) B5795381
theorem B5151449 : Blo 2257435 5151449 := bstep (se 2 (by rfl) ⟨1931793, by rfl⟩ : syracuseStep 5151449 = 3863587) B3863587
theorem B13737197 : Blo 2257435 13737197 := bstep (se 3 (by rfl) ⟨2575724, by rfl⟩ : syracuseStep 13737197 = 5151449) B5151449
theorem B9158131 : Blo 2257435 9158131 := bstep (se 1 (by rfl) ⟨6868598, by rfl⟩ : syracuseStep 9158131 = 13737197) B13737197
theorem B12210841 : Blo 2257435 12210841 := bstep (se 2 (by rfl) ⟨4579065, by rfl⟩ : syracuseStep 12210841 = 9158131) B9158131
theorem B65124485 : Blo 2257435 65124485 := bstep (se 4 (by rfl) ⟨6105420, by rfl⟩ : syracuseStep 65124485 = 12210841) B12210841
theorem B43416323 : Blo 2257435 43416323 := bstep (se 1 (by rfl) ⟨32562242, by rfl⟩ : syracuseStep 43416323 = 65124485) B65124485
theorem B28944215 : Blo 2257435 28944215 := bstep (se 1 (by rfl) ⟨21708161, by rfl⟩ : syracuseStep 28944215 = 43416323) B43416323
theorem B19296143 : Blo 2257435 19296143 := bstep (se 1 (by rfl) ⟨14472107, by rfl⟩ : syracuseStep 19296143 = 28944215) B28944215
theorem B12864095 : Blo 2257435 12864095 := bstep (se 1 (by rfl) ⟨9648071, by rfl⟩ : syracuseStep 12864095 = 19296143) B19296143
theorem B8576063 : Blo 2257435 8576063 := bstep (se 1 (by rfl) ⟨6432047, by rfl⟩ : syracuseStep 8576063 = 12864095) B12864095
theorem B5717375 : Blo 2257435 5717375 := bstep (se 1 (by rfl) ⟨4288031, by rfl⟩ : syracuseStep 5717375 = 8576063) B8576063
theorem B3811583 : Blo 2257435 3811583 := bstep (se 1 (by rfl) ⟨2858687, by rfl⟩ : syracuseStep 3811583 = 5717375) B5717375
theorem B2541055 : Blo 2257435 2541055 := bstep (se 1 (by rfl) ⟨1905791, by rfl⟩ : syracuseStep 2541055 = 3811583) B3811583
theorem B3388073 : Blo 2257435 3388073 := bstep (se 2 (by rfl) ⟨1270527, by rfl⟩ : syracuseStep 3388073 = 2541055) B2541055
theorem B2258715 : Blo 2257435 2258715 := bstep (se 1 (by rfl) ⟨1694036, by rfl⟩ : syracuseStep 2258715 = 3388073) B3388073
theorem B3216029 : Blo 2257435 3216029 := bbase (se 3 (by rfl) ⟨603005, by rfl⟩ : syracuseStep 3216029 = 1206011) (by norm_num)
theorem B8576077 : Blo 2257435 8576077 := bstep (se 3 (by rfl) ⟨1608014, by rfl⟩ : syracuseStep 8576077 = 3216029) B3216029
theorem B11434769 : Blo 2257435 11434769 := bstep (se 2 (by rfl) ⟨4288038, by rfl⟩ : syracuseStep 11434769 = 8576077) B8576077
theorem B7623179 : Blo 2257435 7623179 := bstep (se 1 (by rfl) ⟨5717384, by rfl⟩ : syracuseStep 7623179 = 11434769) B11434769
theorem B5082119 : Blo 2257435 5082119 := bstep (se 1 (by rfl) ⟨3811589, by rfl⟩ : syracuseStep 5082119 = 7623179) B7623179
theorem B3388079 : Blo 2257435 3388079 := bstep (se 1 (by rfl) ⟨2541059, by rfl⟩ : syracuseStep 3388079 = 5082119) B5082119
theorem B2258719 : Blo 2257435 2258719 := bstep (se 1 (by rfl) ⟨1694039, by rfl⟩ : syracuseStep 2258719 = 3388079) B3388079
theorem B3388085 : Blo 2257435 3388085 := bbase (se 5 (by rfl) ⟨158816, by rfl⟩ : syracuseStep 3388085 = 317633) (by norm_num)
theorem B2258723 : Blo 2257435 2258723 := bstep (se 1 (by rfl) ⟨1694042, by rfl⟩ : syracuseStep 2258723 = 3388085) B3388085
theorem B5717405 : Blo 2257435 5717405 := bbase (se 3 (by rfl) ⟨1072013, by rfl⟩ : syracuseStep 5717405 = 2144027) (by norm_num)
theorem B3811603 : Blo 2257435 3811603 := bstep (se 1 (by rfl) ⟨2858702, by rfl⟩ : syracuseStep 3811603 = 5717405) B5717405
theorem B5082137 : Blo 2257435 5082137 := bstep (se 2 (by rfl) ⟨1905801, by rfl⟩ : syracuseStep 5082137 = 3811603) B3811603
theorem B3388091 : Blo 2257435 3388091 := bstep (se 1 (by rfl) ⟨2541068, by rfl⟩ : syracuseStep 3388091 = 5082137) B5082137
theorem B2258727 : Blo 2257435 2258727 := bstep (se 1 (by rfl) ⟨1694045, by rfl⟩ : syracuseStep 2258727 = 3388091) B3388091
theorem B2541073 : Blo 2257435 2541073 := bbase (se 2 (by rfl) ⟨952902, by rfl⟩ : syracuseStep 2541073 = 1905805) (by norm_num)
theorem B3388097 : Blo 2257435 3388097 := bstep (se 2 (by rfl) ⟨1270536, by rfl⟩ : syracuseStep 3388097 = 2541073) B2541073
theorem B2258731 : Blo 2257435 2258731 := bstep (se 1 (by rfl) ⟨1694048, by rfl⟩ : syracuseStep 2258731 = 3388097) B3388097
theorem B4288069 : Blo 2257435 4288069 := bbase (se 4 (by rfl) ⟨402006, by rfl⟩ : syracuseStep 4288069 = 804013) (by norm_num)
theorem B5717425 : Blo 2257435 5717425 := bstep (se 2 (by rfl) ⟨2144034, by rfl⟩ : syracuseStep 5717425 = 4288069) B4288069
theorem B7623233 : Blo 2257435 7623233 := bstep (se 2 (by rfl) ⟨2858712, by rfl⟩ : syracuseStep 7623233 = 5717425) B5717425
theorem B5082155 : Blo 2257435 5082155 := bstep (se 1 (by rfl) ⟨3811616, by rfl⟩ : syracuseStep 5082155 = 7623233) B7623233
theorem B3388103 : Blo 2257435 3388103 := bstep (se 1 (by rfl) ⟨2541077, by rfl⟩ : syracuseStep 3388103 = 5082155) B5082155
theorem B2258735 : Blo 2257435 2258735 := bstep (se 1 (by rfl) ⟨1694051, by rfl⟩ : syracuseStep 2258735 = 3388103) B3388103
theorem B3388109 : Blo 2257435 3388109 := bbase (se 3 (by rfl) ⟨635270, by rfl⟩ : syracuseStep 3388109 = 1270541) (by norm_num)
theorem B2258739 : Blo 2257435 2258739 := bstep (se 1 (by rfl) ⟨1694054, by rfl⟩ : syracuseStep 2258739 = 3388109) B3388109
theorem B5082173 : Blo 2257435 5082173 := bbase (se 3 (by rfl) ⟨952907, by rfl⟩ : syracuseStep 5082173 = 1905815) (by norm_num)
theorem B3388115 : Blo 2257435 3388115 := bstep (se 1 (by rfl) ⟨2541086, by rfl⟩ : syracuseStep 3388115 = 5082173) B5082173
theorem B2258743 : Blo 2257435 2258743 := bstep (se 1 (by rfl) ⟨1694057, by rfl⟩ : syracuseStep 2258743 = 3388115) B3388115
theorem B3811637 : Blo 2257435 3811637 := bbase (se 5 (by rfl) ⟨178670, by rfl⟩ : syracuseStep 3811637 = 357341) (by norm_num)
theorem B2541091 : Blo 2257435 2541091 := bstep (se 1 (by rfl) ⟨1905818, by rfl⟩ : syracuseStep 2541091 = 3811637) B3811637
theorem B3388121 : Blo 2257435 3388121 := bstep (se 2 (by rfl) ⟨1270545, by rfl⟩ : syracuseStep 3388121 = 2541091) B2541091
theorem B2258747 : Blo 2257435 2258747 := bstep (se 1 (by rfl) ⟨1694060, by rfl⟩ : syracuseStep 2258747 = 3388121) B3388121
theorem B6432149 : Blo 2257435 6432149 := bbase (se 6 (by rfl) ⟨150753, by rfl⟩ : syracuseStep 6432149 = 301507) (by norm_num)
theorem B17152397 : Blo 2257435 17152397 := bstep (se 3 (by rfl) ⟨3216074, by rfl⟩ : syracuseStep 17152397 = 6432149) B6432149
theorem B11434931 : Blo 2257435 11434931 := bstep (se 1 (by rfl) ⟨8576198, by rfl⟩ : syracuseStep 11434931 = 17152397) B17152397
theorem B7623287 : Blo 2257435 7623287 := bstep (se 1 (by rfl) ⟨5717465, by rfl⟩ : syracuseStep 7623287 = 11434931) B11434931
theorem B5082191 : Blo 2257435 5082191 := bstep (se 1 (by rfl) ⟨3811643, by rfl⟩ : syracuseStep 5082191 = 7623287) B7623287
theorem B3388127 : Blo 2257435 3388127 := bstep (se 1 (by rfl) ⟨2541095, by rfl⟩ : syracuseStep 3388127 = 5082191) B5082191
theorem B2258751 : Blo 2257435 2258751 := bstep (se 1 (by rfl) ⟨1694063, by rfl⟩ : syracuseStep 2258751 = 3388127) B3388127
theorem B3388133 : Blo 2257435 3388133 := bbase (se 4 (by rfl) ⟨317637, by rfl⟩ : syracuseStep 3388133 = 635275) (by norm_num)
theorem B2258755 : Blo 2257435 2258755 := bstep (se 1 (by rfl) ⟨1694066, by rfl⟩ : syracuseStep 2258755 = 3388133) B3388133
theorem B2412065 : Blo 2257435 2412065 := bbase (se 2 (by rfl) ⟨904524, by rfl⟩ : syracuseStep 2412065 = 1809049) (by norm_num)
theorem B6432173 : Blo 2257435 6432173 := bstep (se 3 (by rfl) ⟨1206032, by rfl⟩ : syracuseStep 6432173 = 2412065) B2412065
theorem B4288115 : Blo 2257435 4288115 := bstep (se 1 (by rfl) ⟨3216086, by rfl⟩ : syracuseStep 4288115 = 6432173) B6432173
theorem B2858743 : Blo 2257435 2858743 := bstep (se 1 (by rfl) ⟨2144057, by rfl⟩ : syracuseStep 2858743 = 4288115) B4288115
theorem B3811657 : Blo 2257435 3811657 := bstep (se 2 (by rfl) ⟨1429371, by rfl⟩ : syracuseStep 3811657 = 2858743) B2858743
theorem B5082209 : Blo 2257435 5082209 := bstep (se 2 (by rfl) ⟨1905828, by rfl⟩ : syracuseStep 5082209 = 3811657) B3811657
theorem B3388139 : Blo 2257435 3388139 := bstep (se 1 (by rfl) ⟨2541104, by rfl⟩ : syracuseStep 3388139 = 5082209) B5082209
theorem B2258759 : Blo 2257435 2258759 := bstep (se 1 (by rfl) ⟨1694069, by rfl⟩ : syracuseStep 2258759 = 3388139) B3388139
theorem B2541109 : Blo 2257435 2541109 := bbase (se 5 (by rfl) ⟨119114, by rfl⟩ : syracuseStep 2541109 = 238229) (by norm_num)
theorem B3388145 : Blo 2257435 3388145 := bstep (se 2 (by rfl) ⟨1270554, by rfl⟩ : syracuseStep 3388145 = 2541109) B2541109
theorem B2258763 : Blo 2257435 2258763 := bstep (se 1 (by rfl) ⟨1694072, by rfl⟩ : syracuseStep 2258763 = 3388145) B3388145
theorem B2858753 : Blo 2257435 2858753 := bbase (se 2 (by rfl) ⟨1072032, by rfl⟩ : syracuseStep 2858753 = 2144065) (by norm_num)
theorem B7623341 : Blo 2257435 7623341 := bstep (se 3 (by rfl) ⟨1429376, by rfl⟩ : syracuseStep 7623341 = 2858753) B2858753
theorem B5082227 : Blo 2257435 5082227 := bstep (se 1 (by rfl) ⟨3811670, by rfl⟩ : syracuseStep 5082227 = 7623341) B7623341
theorem B3388151 : Blo 2257435 3388151 := bstep (se 1 (by rfl) ⟨2541113, by rfl⟩ : syracuseStep 3388151 = 5082227) B5082227
theorem B2258767 : Blo 2257435 2258767 := bstep (se 1 (by rfl) ⟨1694075, by rfl⟩ : syracuseStep 2258767 = 3388151) B3388151
theorem B3388157 : Blo 2257435 3388157 := bbase (se 3 (by rfl) ⟨635279, by rfl⟩ : syracuseStep 3388157 = 1270559) (by norm_num)
theorem B2258771 : Blo 2257435 2258771 := bstep (se 1 (by rfl) ⟨1694078, by rfl⟩ : syracuseStep 2258771 = 3388157) B3388157
theorem B5082245 : Blo 2257435 5082245 := bbase (se 4 (by rfl) ⟨476460, by rfl⟩ : syracuseStep 5082245 = 952921) (by norm_num)
theorem B3388163 : Blo 2257435 3388163 := bstep (se 1 (by rfl) ⟨2541122, by rfl⟩ : syracuseStep 3388163 = 5082245) B5082245
theorem B2258775 : Blo 2257435 2258775 := bstep (se 1 (by rfl) ⟨1694081, by rfl⟩ : syracuseStep 2258775 = 3388163) B3388163
theorem B4824173 : Blo 2257435 4824173 := bbase (se 3 (by rfl) ⟨904532, by rfl⟩ : syracuseStep 4824173 = 1809065) (by norm_num)
theorem B3216115 : Blo 2257435 3216115 := bstep (se 1 (by rfl) ⟨2412086, by rfl⟩ : syracuseStep 3216115 = 4824173) B4824173
theorem B4288153 : Blo 2257435 4288153 := bstep (se 2 (by rfl) ⟨1608057, by rfl⟩ : syracuseStep 4288153 = 3216115) B3216115
theorem B5717537 : Blo 2257435 5717537 := bstep (se 2 (by rfl) ⟨2144076, by rfl⟩ : syracuseStep 5717537 = 4288153) B4288153
theorem B3811691 : Blo 2257435 3811691 := bstep (se 1 (by rfl) ⟨2858768, by rfl⟩ : syracuseStep 3811691 = 5717537) B5717537
theorem B2541127 : Blo 2257435 2541127 := bstep (se 1 (by rfl) ⟨1905845, by rfl⟩ : syracuseStep 2541127 = 3811691) B3811691
theorem B3388169 : Blo 2257435 3388169 := bstep (se 2 (by rfl) ⟨1270563, by rfl⟩ : syracuseStep 3388169 = 2541127) B2541127
theorem B2258779 : Blo 2257435 2258779 := bstep (se 1 (by rfl) ⟨1694084, by rfl⟩ : syracuseStep 2258779 = 3388169) B3388169
theorem B11435093 : Blo 2257435 11435093 := bbase (se 8 (by rfl) ⟨67002, by rfl⟩ : syracuseStep 11435093 = 134005) (by norm_num)
theorem B7623395 : Blo 2257435 7623395 := bstep (se 1 (by rfl) ⟨5717546, by rfl⟩ : syracuseStep 7623395 = 11435093) B11435093
theorem B5082263 : Blo 2257435 5082263 := bstep (se 1 (by rfl) ⟨3811697, by rfl⟩ : syracuseStep 5082263 = 7623395) B7623395
theorem B3388175 : Blo 2257435 3388175 := bstep (se 1 (by rfl) ⟨2541131, by rfl⟩ : syracuseStep 3388175 = 5082263) B5082263
theorem B2258783 : Blo 2257435 2258783 := bstep (se 1 (by rfl) ⟨1694087, by rfl⟩ : syracuseStep 2258783 = 3388175) B3388175
theorem B3388181 : Blo 2257435 3388181 := bbase (se 6 (by rfl) ⟨79410, by rfl⟩ : syracuseStep 3388181 = 158821) (by norm_num)
theorem B2258787 : Blo 2257435 2258787 := bstep (se 1 (by rfl) ⟨1694090, by rfl⟩ : syracuseStep 2258787 = 3388181) B3388181
theorem B3052813 : Blo 2257435 3052813 := bbase (se 3 (by rfl) ⟨572402, by rfl⟩ : syracuseStep 3052813 = 1144805) (by norm_num)
theorem B4070417 : Blo 2257435 4070417 := bstep (se 2 (by rfl) ⟨1526406, by rfl⟩ : syracuseStep 4070417 = 3052813) B3052813
theorem B43417781 : Blo 2257435 43417781 := bstep (se 5 (by rfl) ⟨2035208, by rfl⟩ : syracuseStep 43417781 = 4070417) B4070417
theorem B28945187 : Blo 2257435 28945187 := bstep (se 1 (by rfl) ⟨21708890, by rfl⟩ : syracuseStep 28945187 = 43417781) B43417781
theorem B19296791 : Blo 2257435 19296791 := bstep (se 1 (by rfl) ⟨14472593, by rfl⟩ : syracuseStep 19296791 = 28945187) B28945187
theorem B12864527 : Blo 2257435 12864527 := bstep (se 1 (by rfl) ⟨9648395, by rfl⟩ : syracuseStep 12864527 = 19296791) B19296791
theorem B8576351 : Blo 2257435 8576351 := bstep (se 1 (by rfl) ⟨6432263, by rfl⟩ : syracuseStep 8576351 = 12864527) B12864527
theorem B5717567 : Blo 2257435 5717567 := bstep (se 1 (by rfl) ⟨4288175, by rfl⟩ : syracuseStep 5717567 = 8576351) B8576351
theorem B3811711 : Blo 2257435 3811711 := bstep (se 1 (by rfl) ⟨2858783, by rfl⟩ : syracuseStep 3811711 = 5717567) B5717567
theorem B5082281 : Blo 2257435 5082281 := bstep (se 2 (by rfl) ⟨1905855, by rfl⟩ : syracuseStep 5082281 = 3811711) B3811711
theorem B3388187 : Blo 2257435 3388187 := bstep (se 1 (by rfl) ⟨2541140, by rfl⟩ : syracuseStep 3388187 = 5082281) B5082281
theorem B2258791 : Blo 2257435 2258791 := bstep (se 1 (by rfl) ⟨1694093, by rfl⟩ : syracuseStep 2258791 = 3388187) B3388187
theorem B2541145 : Blo 2257435 2541145 := bbase (se 2 (by rfl) ⟨952929, by rfl⟩ : syracuseStep 2541145 = 1905859) (by norm_num)
theorem B3388193 : Blo 2257435 3388193 := bstep (se 2 (by rfl) ⟨1270572, by rfl⟩ : syracuseStep 3388193 = 2541145) B2541145
theorem B2258795 : Blo 2257435 2258795 := bstep (se 1 (by rfl) ⟨1694096, by rfl⟩ : syracuseStep 2258795 = 3388193) B3388193
theorem B10854485 : Blo 2257435 10854485 := bbase (se 8 (by rfl) ⟨63600, by rfl⟩ : syracuseStep 10854485 = 127201) (by norm_num)
theorem B7236323 : Blo 2257435 7236323 := bstep (se 1 (by rfl) ⟨5427242, by rfl⟩ : syracuseStep 7236323 = 10854485) B10854485
theorem B4824215 : Blo 2257435 4824215 := bstep (se 1 (by rfl) ⟨3618161, by rfl⟩ : syracuseStep 4824215 = 7236323) B7236323
theorem B3216143 : Blo 2257435 3216143 := bstep (se 1 (by rfl) ⟨2412107, by rfl⟩ : syracuseStep 3216143 = 4824215) B4824215
theorem B8576381 : Blo 2257435 8576381 := bstep (se 3 (by rfl) ⟨1608071, by rfl⟩ : syracuseStep 8576381 = 3216143) B3216143
theorem B5717587 : Blo 2257435 5717587 := bstep (se 1 (by rfl) ⟨4288190, by rfl⟩ : syracuseStep 5717587 = 8576381) B8576381
theorem B7623449 : Blo 2257435 7623449 := bstep (se 2 (by rfl) ⟨2858793, by rfl⟩ : syracuseStep 7623449 = 5717587) B5717587
theorem B5082299 : Blo 2257435 5082299 := bstep (se 1 (by rfl) ⟨3811724, by rfl⟩ : syracuseStep 5082299 = 7623449) B7623449
theorem B3388199 : Blo 2257435 3388199 := bstep (se 1 (by rfl) ⟨2541149, by rfl⟩ : syracuseStep 3388199 = 5082299) B5082299
theorem B2258799 : Blo 2257435 2258799 := bstep (se 1 (by rfl) ⟨1694099, by rfl⟩ : syracuseStep 2258799 = 3388199) B3388199
theorem B3388205 : Blo 2257435 3388205 := bbase (se 3 (by rfl) ⟨635288, by rfl⟩ : syracuseStep 3388205 = 1270577) (by norm_num)
theorem B2258803 : Blo 2257435 2258803 := bstep (se 1 (by rfl) ⟨1694102, by rfl⟩ : syracuseStep 2258803 = 3388205) B3388205
theorem B5082317 : Blo 2257435 5082317 := bbase (se 3 (by rfl) ⟨952934, by rfl⟩ : syracuseStep 5082317 = 1905869) (by norm_num)
theorem B3388211 : Blo 2257435 3388211 := bstep (se 1 (by rfl) ⟨2541158, by rfl⟩ : syracuseStep 3388211 = 5082317) B5082317
theorem B2258807 : Blo 2257435 2258807 := bstep (se 1 (by rfl) ⟨1694105, by rfl⟩ : syracuseStep 2258807 = 3388211) B3388211
theorem B2858809 : Blo 2257435 2858809 := bbase (se 2 (by rfl) ⟨1072053, by rfl⟩ : syracuseStep 2858809 = 2144107) (by norm_num)
theorem B3811745 : Blo 2257435 3811745 := bstep (se 2 (by rfl) ⟨1429404, by rfl⟩ : syracuseStep 3811745 = 2858809) B2858809
theorem B2541163 : Blo 2257435 2541163 := bstep (se 1 (by rfl) ⟨1905872, by rfl⟩ : syracuseStep 2541163 = 3811745) B3811745
theorem B3388217 : Blo 2257435 3388217 := bstep (se 2 (by rfl) ⟨1270581, by rfl⟩ : syracuseStep 3388217 = 2541163) B2541163
theorem B2258811 : Blo 2257435 2258811 := bstep (se 1 (by rfl) ⟨1694108, by rfl⟩ : syracuseStep 2258811 = 3388217) B3388217
theorem B7236373 : Blo 2257435 7236373 := bbase (se 6 (by rfl) ⟨169602, by rfl⟩ : syracuseStep 7236373 = 339205) (by norm_num)
theorem B9648497 : Blo 2257435 9648497 := bstep (se 2 (by rfl) ⟨3618186, by rfl⟩ : syracuseStep 9648497 = 7236373) B7236373
theorem B25729325 : Blo 2257435 25729325 := bstep (se 3 (by rfl) ⟨4824248, by rfl⟩ : syracuseStep 25729325 = 9648497) B9648497
theorem B17152883 : Blo 2257435 17152883 := bstep (se 1 (by rfl) ⟨12864662, by rfl⟩ : syracuseStep 17152883 = 25729325) B25729325
theorem B11435255 : Blo 2257435 11435255 := bstep (se 1 (by rfl) ⟨8576441, by rfl⟩ : syracuseStep 11435255 = 17152883) B17152883
theorem B7623503 : Blo 2257435 7623503 := bstep (se 1 (by rfl) ⟨5717627, by rfl⟩ : syracuseStep 7623503 = 11435255) B11435255
theorem B5082335 : Blo 2257435 5082335 := bstep (se 1 (by rfl) ⟨3811751, by rfl⟩ : syracuseStep 5082335 = 7623503) B7623503
theorem B3388223 : Blo 2257435 3388223 := bstep (se 1 (by rfl) ⟨2541167, by rfl⟩ : syracuseStep 3388223 = 5082335) B5082335
theorem B2258815 : Blo 2257435 2258815 := bstep (se 1 (by rfl) ⟨1694111, by rfl⟩ : syracuseStep 2258815 = 3388223) B3388223
theorem B3388229 : Blo 2257435 3388229 := bbase (se 4 (by rfl) ⟨317646, by rfl⟩ : syracuseStep 3388229 = 635293) (by norm_num)
theorem B2258819 : Blo 2257435 2258819 := bstep (se 1 (by rfl) ⟨1694114, by rfl⟩ : syracuseStep 2258819 = 3388229) B3388229
theorem B3811765 : Blo 2257435 3811765 := bbase (se 5 (by rfl) ⟨178676, by rfl⟩ : syracuseStep 3811765 = 357353) (by norm_num)
theorem B5082353 : Blo 2257435 5082353 := bstep (se 2 (by rfl) ⟨1905882, by rfl⟩ : syracuseStep 5082353 = 3811765) B3811765
theorem B3388235 : Blo 2257435 3388235 := bstep (se 1 (by rfl) ⟨2541176, by rfl⟩ : syracuseStep 3388235 = 5082353) B5082353
theorem B2258823 : Blo 2257435 2258823 := bstep (se 1 (by rfl) ⟨1694117, by rfl⟩ : syracuseStep 2258823 = 3388235) B3388235
theorem B2541181 : Blo 2257435 2541181 := bbase (se 3 (by rfl) ⟨476471, by rfl⟩ : syracuseStep 2541181 = 952943) (by norm_num)
theorem B3388241 : Blo 2257435 3388241 := bstep (se 2 (by rfl) ⟨1270590, by rfl⟩ : syracuseStep 3388241 = 2541181) B2541181
theorem B2258827 : Blo 2257435 2258827 := bstep (se 1 (by rfl) ⟨1694120, by rfl⟩ : syracuseStep 2258827 = 3388241) B3388241
theorem B7623557 : Blo 2257435 7623557 := bbase (se 4 (by rfl) ⟨714708, by rfl⟩ : syracuseStep 7623557 = 1429417) (by norm_num)
theorem B5082371 : Blo 2257435 5082371 := bstep (se 1 (by rfl) ⟨3811778, by rfl⟩ : syracuseStep 5082371 = 7623557) B7623557
theorem B3388247 : Blo 2257435 3388247 := bstep (se 1 (by rfl) ⟨2541185, by rfl⟩ : syracuseStep 3388247 = 5082371) B5082371
theorem B2258831 : Blo 2257435 2258831 := bstep (se 1 (by rfl) ⟨1694123, by rfl⟩ : syracuseStep 2258831 = 3388247) B3388247
theorem B3388253 : Blo 2257435 3388253 := bbase (se 3 (by rfl) ⟨635297, by rfl⟩ : syracuseStep 3388253 = 1270595) (by norm_num)
theorem B2258835 : Blo 2257435 2258835 := bstep (se 1 (by rfl) ⟨1694126, by rfl⟩ : syracuseStep 2258835 = 3388253) B3388253
theorem B5082389 : Blo 2257435 5082389 := bbase (se 6 (by rfl) ⟨119118, by rfl⟩ : syracuseStep 5082389 = 238237) (by norm_num)
theorem B3388259 : Blo 2257435 3388259 := bstep (se 1 (by rfl) ⟨2541194, by rfl⟩ : syracuseStep 3388259 = 5082389) B5082389
theorem B2258839 : Blo 2257435 2258839 := bstep (se 1 (by rfl) ⟨1694129, by rfl⟩ : syracuseStep 2258839 = 3388259) B3388259
theorem B8576549 : Blo 2257435 8576549 := bbase (se 4 (by rfl) ⟨804051, by rfl⟩ : syracuseStep 8576549 = 1608103) (by norm_num)
theorem B5717699 : Blo 2257435 5717699 := bstep (se 1 (by rfl) ⟨4288274, by rfl⟩ : syracuseStep 5717699 = 8576549) B8576549
theorem B3811799 : Blo 2257435 3811799 := bstep (se 1 (by rfl) ⟨2858849, by rfl⟩ : syracuseStep 3811799 = 5717699) B5717699
theorem B2541199 : Blo 2257435 2541199 := bstep (se 1 (by rfl) ⟨1905899, by rfl⟩ : syracuseStep 2541199 = 3811799) B3811799
theorem B3388265 : Blo 2257435 3388265 := bstep (se 2 (by rfl) ⟨1270599, by rfl⟩ : syracuseStep 3388265 = 2541199) B2541199
theorem B2258843 : Blo 2257435 2258843 := bstep (se 1 (by rfl) ⟨1694132, by rfl⟩ : syracuseStep 2258843 = 3388265) B3388265
theorem B4824317 : Blo 2257435 4824317 := bbase (se 3 (by rfl) ⟨904559, by rfl⟩ : syracuseStep 4824317 = 1809119) (by norm_num)
theorem B12864845 : Blo 2257435 12864845 := bstep (se 3 (by rfl) ⟨2412158, by rfl⟩ : syracuseStep 12864845 = 4824317) B4824317
theorem B8576563 : Blo 2257435 8576563 := bstep (se 1 (by rfl) ⟨6432422, by rfl⟩ : syracuseStep 8576563 = 12864845) B12864845
theorem B11435417 : Blo 2257435 11435417 := bstep (se 2 (by rfl) ⟨4288281, by rfl⟩ : syracuseStep 11435417 = 8576563) B8576563
theorem B7623611 : Blo 2257435 7623611 := bstep (se 1 (by rfl) ⟨5717708, by rfl⟩ : syracuseStep 7623611 = 11435417) B11435417
theorem B5082407 : Blo 2257435 5082407 := bstep (se 1 (by rfl) ⟨3811805, by rfl⟩ : syracuseStep 5082407 = 7623611) B7623611
theorem B3388271 : Blo 2257435 3388271 := bstep (se 1 (by rfl) ⟨2541203, by rfl⟩ : syracuseStep 3388271 = 5082407) B5082407
theorem B2258847 : Blo 2257435 2258847 := bstep (se 1 (by rfl) ⟨1694135, by rfl⟩ : syracuseStep 2258847 = 3388271) B3388271
theorem B3388277 : Blo 2257435 3388277 := bbase (se 5 (by rfl) ⟨158825, by rfl⟩ : syracuseStep 3388277 = 317651) (by norm_num)
theorem B2258851 : Blo 2257435 2258851 := bstep (se 1 (by rfl) ⟨1694138, by rfl⟩ : syracuseStep 2258851 = 3388277) B3388277
theorem B16282133 : Blo 2257435 16282133 := bbase (se 6 (by rfl) ⟨381612, by rfl⟩ : syracuseStep 16282133 = 763225) (by norm_num)
theorem B10854755 : Blo 2257435 10854755 := bstep (se 1 (by rfl) ⟨8141066, by rfl⟩ : syracuseStep 10854755 = 16282133) B16282133
theorem B7236503 : Blo 2257435 7236503 := bstep (se 1 (by rfl) ⟨5427377, by rfl⟩ : syracuseStep 7236503 = 10854755) B10854755
theorem B4824335 : Blo 2257435 4824335 := bstep (se 1 (by rfl) ⟨3618251, by rfl⟩ : syracuseStep 4824335 = 7236503) B7236503
theorem B3216223 : Blo 2257435 3216223 := bstep (se 1 (by rfl) ⟨2412167, by rfl⟩ : syracuseStep 3216223 = 4824335) B4824335
theorem B4288297 : Blo 2257435 4288297 := bstep (se 2 (by rfl) ⟨1608111, by rfl⟩ : syracuseStep 4288297 = 3216223) B3216223
theorem B5717729 : Blo 2257435 5717729 := bstep (se 2 (by rfl) ⟨2144148, by rfl⟩ : syracuseStep 5717729 = 4288297) B4288297
theorem B3811819 : Blo 2257435 3811819 := bstep (se 1 (by rfl) ⟨2858864, by rfl⟩ : syracuseStep 3811819 = 5717729) B5717729
theorem B5082425 : Blo 2257435 5082425 := bstep (se 2 (by rfl) ⟨1905909, by rfl⟩ : syracuseStep 5082425 = 3811819) B3811819
theorem B3388283 : Blo 2257435 3388283 := bstep (se 1 (by rfl) ⟨2541212, by rfl⟩ : syracuseStep 3388283 = 5082425) B5082425
theorem B2258855 : Blo 2257435 2258855 := bstep (se 1 (by rfl) ⟨1694141, by rfl⟩ : syracuseStep 2258855 = 3388283) B3388283
theorem B2541217 : Blo 2257435 2541217 := bbase (se 2 (by rfl) ⟨952956, by rfl⟩ : syracuseStep 2541217 = 1905913) (by norm_num)
theorem B3388289 : Blo 2257435 3388289 := bstep (se 2 (by rfl) ⟨1270608, by rfl⟩ : syracuseStep 3388289 = 2541217) B2541217
theorem B2258859 : Blo 2257435 2258859 := bstep (se 1 (by rfl) ⟨1694144, by rfl⟩ : syracuseStep 2258859 = 3388289) B3388289
theorem B5717749 : Blo 2257435 5717749 := bbase (se 5 (by rfl) ⟨268019, by rfl⟩ : syracuseStep 5717749 = 536039) (by norm_num)
theorem B7623665 : Blo 2257435 7623665 := bstep (se 2 (by rfl) ⟨2858874, by rfl⟩ : syracuseStep 7623665 = 5717749) B5717749
theorem B5082443 : Blo 2257435 5082443 := bstep (se 1 (by rfl) ⟨3811832, by rfl⟩ : syracuseStep 5082443 = 7623665) B7623665
theorem B3388295 : Blo 2257435 3388295 := bstep (se 1 (by rfl) ⟨2541221, by rfl⟩ : syracuseStep 3388295 = 5082443) B5082443
theorem B2258863 : Blo 2257435 2258863 := bstep (se 1 (by rfl) ⟨1694147, by rfl⟩ : syracuseStep 2258863 = 3388295) B3388295
theorem B3388301 : Blo 2257435 3388301 := bbase (se 3 (by rfl) ⟨635306, by rfl⟩ : syracuseStep 3388301 = 1270613) (by norm_num)
theorem B2258867 : Blo 2257435 2258867 := bstep (se 1 (by rfl) ⟨1694150, by rfl⟩ : syracuseStep 2258867 = 3388301) B3388301
theorem B5082461 : Blo 2257435 5082461 := bbase (se 3 (by rfl) ⟨952961, by rfl⟩ : syracuseStep 5082461 = 1905923) (by norm_num)
theorem B3388307 : Blo 2257435 3388307 := bstep (se 1 (by rfl) ⟨2541230, by rfl⟩ : syracuseStep 3388307 = 5082461) B5082461
theorem B2258871 : Blo 2257435 2258871 := bstep (se 1 (by rfl) ⟨1694153, by rfl⟩ : syracuseStep 2258871 = 3388307) B3388307
theorem B3811853 : Blo 2257435 3811853 := bbase (se 3 (by rfl) ⟨714722, by rfl⟩ : syracuseStep 3811853 = 1429445) (by norm_num)
theorem B2541235 : Blo 2257435 2541235 := bstep (se 1 (by rfl) ⟨1905926, by rfl⟩ : syracuseStep 2541235 = 3811853) B3811853
theorem B3388313 : Blo 2257435 3388313 := bstep (se 2 (by rfl) ⟨1270617, by rfl⟩ : syracuseStep 3388313 = 2541235) B2541235
theorem B2258875 : Blo 2257435 2258875 := bstep (se 1 (by rfl) ⟨1694156, by rfl⟩ : syracuseStep 2258875 = 3388313) B3388313
theorem B2713717 : Blo 2257435 2713717 := bbase (se 5 (by rfl) ⟨127205, by rfl⟩ : syracuseStep 2713717 = 254411) (by norm_num)
theorem B3618289 : Blo 2257435 3618289 := bstep (se 2 (by rfl) ⟨1356858, by rfl⟩ : syracuseStep 3618289 = 2713717) B2713717
theorem B19297541 : Blo 2257435 19297541 := bstep (se 4 (by rfl) ⟨1809144, by rfl⟩ : syracuseStep 19297541 = 3618289) B3618289
theorem B12865027 : Blo 2257435 12865027 := bstep (se 1 (by rfl) ⟨9648770, by rfl⟩ : syracuseStep 12865027 = 19297541) B19297541
theorem B17153369 : Blo 2257435 17153369 := bstep (se 2 (by rfl) ⟨6432513, by rfl⟩ : syracuseStep 17153369 = 12865027) B12865027
theorem B11435579 : Blo 2257435 11435579 := bstep (se 1 (by rfl) ⟨8576684, by rfl⟩ : syracuseStep 11435579 = 17153369) B17153369
theorem B7623719 : Blo 2257435 7623719 := bstep (se 1 (by rfl) ⟨5717789, by rfl⟩ : syracuseStep 7623719 = 11435579) B11435579
theorem B5082479 : Blo 2257435 5082479 := bstep (se 1 (by rfl) ⟨3811859, by rfl⟩ : syracuseStep 5082479 = 7623719) B7623719
theorem B3388319 : Blo 2257435 3388319 := bstep (se 1 (by rfl) ⟨2541239, by rfl⟩ : syracuseStep 3388319 = 5082479) B5082479
theorem B2258879 : Blo 2257435 2258879 := bstep (se 1 (by rfl) ⟨1694159, by rfl⟩ : syracuseStep 2258879 = 3388319) B3388319
theorem B3388325 : Blo 2257435 3388325 := bbase (se 4 (by rfl) ⟨317655, by rfl⟩ : syracuseStep 3388325 = 635311) (by norm_num)
theorem B2258883 : Blo 2257435 2258883 := bstep (se 1 (by rfl) ⟨1694162, by rfl⟩ : syracuseStep 2258883 = 3388325) B3388325
theorem B2858905 : Blo 2257435 2858905 := bbase (se 2 (by rfl) ⟨1072089, by rfl⟩ : syracuseStep 2858905 = 2144179) (by norm_num)
theorem B3811873 : Blo 2257435 3811873 := bstep (se 2 (by rfl) ⟨1429452, by rfl⟩ : syracuseStep 3811873 = 2858905) B2858905
theorem B5082497 : Blo 2257435 5082497 := bstep (se 2 (by rfl) ⟨1905936, by rfl⟩ : syracuseStep 5082497 = 3811873) B3811873
theorem B3388331 : Blo 2257435 3388331 := bstep (se 1 (by rfl) ⟨2541248, by rfl⟩ : syracuseStep 3388331 = 5082497) B5082497
theorem B2258887 : Blo 2257435 2258887 := bstep (se 1 (by rfl) ⟨1694165, by rfl⟩ : syracuseStep 2258887 = 3388331) B3388331
theorem B2541253 : Blo 2257435 2541253 := bbase (se 4 (by rfl) ⟨238242, by rfl⟩ : syracuseStep 2541253 = 476485) (by norm_num)
theorem B3388337 : Blo 2257435 3388337 := bstep (se 2 (by rfl) ⟨1270626, by rfl⟩ : syracuseStep 3388337 = 2541253) B2541253
theorem B2258891 : Blo 2257435 2258891 := bstep (se 1 (by rfl) ⟨1694168, by rfl⟩ : syracuseStep 2258891 = 3388337) B3388337
theorem B4288373 : Blo 2257435 4288373 := bbase (se 5 (by rfl) ⟨201017, by rfl⟩ : syracuseStep 4288373 = 402035) (by norm_num)
theorem B2858915 : Blo 2257435 2858915 := bstep (se 1 (by rfl) ⟨2144186, by rfl⟩ : syracuseStep 2858915 = 4288373) B4288373
theorem B7623773 : Blo 2257435 7623773 := bstep (se 3 (by rfl) ⟨1429457, by rfl⟩ : syracuseStep 7623773 = 2858915) B2858915
theorem B5082515 : Blo 2257435 5082515 := bstep (se 1 (by rfl) ⟨3811886, by rfl⟩ : syracuseStep 5082515 = 7623773) B7623773
theorem B3388343 : Blo 2257435 3388343 := bstep (se 1 (by rfl) ⟨2541257, by rfl⟩ : syracuseStep 3388343 = 5082515) B5082515
theorem B2258895 : Blo 2257435 2258895 := bstep (se 1 (by rfl) ⟨1694171, by rfl⟩ : syracuseStep 2258895 = 3388343) B3388343
theorem B3388349 : Blo 2257435 3388349 := bbase (se 3 (by rfl) ⟨635315, by rfl⟩ : syracuseStep 3388349 = 1270631) (by norm_num)
theorem B2258899 : Blo 2257435 2258899 := bstep (se 1 (by rfl) ⟨1694174, by rfl⟩ : syracuseStep 2258899 = 3388349) B3388349
theorem B5082533 : Blo 2257435 5082533 := bbase (se 4 (by rfl) ⟨476487, by rfl⟩ : syracuseStep 5082533 = 952975) (by norm_num)
theorem B3388355 : Blo 2257435 3388355 := bstep (se 1 (by rfl) ⟨2541266, by rfl⟩ : syracuseStep 3388355 = 5082533) B5082533
theorem B2258903 : Blo 2257435 2258903 := bstep (se 1 (by rfl) ⟨1694177, by rfl⟩ : syracuseStep 2258903 = 3388355) B3388355
theorem B5717861 : Blo 2257435 5717861 := bbase (se 4 (by rfl) ⟨536049, by rfl⟩ : syracuseStep 5717861 = 1072099) (by norm_num)
theorem B3811907 : Blo 2257435 3811907 := bstep (se 1 (by rfl) ⟨2858930, by rfl⟩ : syracuseStep 3811907 = 5717861) B5717861
theorem B2541271 : Blo 2257435 2541271 := bstep (se 1 (by rfl) ⟨1905953, by rfl⟩ : syracuseStep 2541271 = 3811907) B3811907
theorem B3388361 : Blo 2257435 3388361 := bstep (se 2 (by rfl) ⟨1270635, by rfl⟩ : syracuseStep 3388361 = 2541271) B2541271
theorem B2258907 : Blo 2257435 2258907 := bstep (se 1 (by rfl) ⟨1694180, by rfl⟩ : syracuseStep 2258907 = 3388361) B3388361
theorem B3618341 : Blo 2257435 3618341 := bbase (se 4 (by rfl) ⟨339219, by rfl⟩ : syracuseStep 3618341 = 678439) (by norm_num)
theorem B2412227 : Blo 2257435 2412227 := bstep (se 1 (by rfl) ⟨1809170, by rfl⟩ : syracuseStep 2412227 = 3618341) B3618341
theorem B6432605 : Blo 2257435 6432605 := bstep (se 3 (by rfl) ⟨1206113, by rfl⟩ : syracuseStep 6432605 = 2412227) B2412227
theorem B4288403 : Blo 2257435 4288403 := bstep (se 1 (by rfl) ⟨3216302, by rfl⟩ : syracuseStep 4288403 = 6432605) B6432605
theorem B11435741 : Blo 2257435 11435741 := bstep (se 3 (by rfl) ⟨2144201, by rfl⟩ : syracuseStep 11435741 = 4288403) B4288403
theorem B7623827 : Blo 2257435 7623827 := bstep (se 1 (by rfl) ⟨5717870, by rfl⟩ : syracuseStep 7623827 = 11435741) B11435741
theorem B5082551 : Blo 2257435 5082551 := bstep (se 1 (by rfl) ⟨3811913, by rfl⟩ : syracuseStep 5082551 = 7623827) B7623827
theorem B3388367 : Blo 2257435 3388367 := bstep (se 1 (by rfl) ⟨2541275, by rfl⟩ : syracuseStep 3388367 = 5082551) B5082551
theorem B2258911 : Blo 2257435 2258911 := bstep (se 1 (by rfl) ⟨1694183, by rfl⟩ : syracuseStep 2258911 = 3388367) B3388367
theorem B3388373 : Blo 2257435 3388373 := bbase (se 7 (by rfl) ⟨39707, by rfl⟩ : syracuseStep 3388373 = 79415) (by norm_num)
theorem B2258915 : Blo 2257435 2258915 := bstep (se 1 (by rfl) ⟨1694186, by rfl⟩ : syracuseStep 2258915 = 3388373) B3388373
theorem B8576837 : Blo 2257435 8576837 := bbase (se 4 (by rfl) ⟨804078, by rfl⟩ : syracuseStep 8576837 = 1608157) (by norm_num)
theorem B5717891 : Blo 2257435 5717891 := bstep (se 1 (by rfl) ⟨4288418, by rfl⟩ : syracuseStep 5717891 = 8576837) B8576837
theorem B3811927 : Blo 2257435 3811927 := bstep (se 1 (by rfl) ⟨2858945, by rfl⟩ : syracuseStep 3811927 = 5717891) B5717891
theorem B5082569 : Blo 2257435 5082569 := bstep (se 2 (by rfl) ⟨1905963, by rfl⟩ : syracuseStep 5082569 = 3811927) B3811927
theorem B3388379 : Blo 2257435 3388379 := bstep (se 1 (by rfl) ⟨2541284, by rfl⟩ : syracuseStep 3388379 = 5082569) B5082569
theorem B2258919 : Blo 2257435 2258919 := bstep (se 1 (by rfl) ⟨1694189, by rfl⟩ : syracuseStep 2258919 = 3388379) B3388379
theorem B2541289 : Blo 2257435 2541289 := bbase (se 2 (by rfl) ⟨952983, by rfl⟩ : syracuseStep 2541289 = 1905967) (by norm_num)
theorem B3388385 : Blo 2257435 3388385 := bstep (se 2 (by rfl) ⟨1270644, by rfl⟩ : syracuseStep 3388385 = 2541289) B2541289
theorem B2258923 : Blo 2257435 2258923 := bstep (se 1 (by rfl) ⟨1694192, by rfl⟩ : syracuseStep 2258923 = 3388385) B3388385
theorem B12865301 : Blo 2257435 12865301 := bbase (se 6 (by rfl) ⟨301530, by rfl⟩ : syracuseStep 12865301 = 603061) (by norm_num)
theorem B8576867 : Blo 2257435 8576867 := bstep (se 1 (by rfl) ⟨6432650, by rfl⟩ : syracuseStep 8576867 = 12865301) B12865301
theorem B5717911 : Blo 2257435 5717911 := bstep (se 1 (by rfl) ⟨4288433, by rfl⟩ : syracuseStep 5717911 = 8576867) B8576867
theorem B7623881 : Blo 2257435 7623881 := bstep (se 2 (by rfl) ⟨2858955, by rfl⟩ : syracuseStep 7623881 = 5717911) B5717911
theorem B5082587 : Blo 2257435 5082587 := bstep (se 1 (by rfl) ⟨3811940, by rfl⟩ : syracuseStep 5082587 = 7623881) B7623881
theorem B3388391 : Blo 2257435 3388391 := bstep (se 1 (by rfl) ⟨2541293, by rfl⟩ : syracuseStep 3388391 = 5082587) B5082587
theorem B2258927 : Blo 2257435 2258927 := bstep (se 1 (by rfl) ⟨1694195, by rfl⟩ : syracuseStep 2258927 = 3388391) B3388391
theorem B3388397 : Blo 2257435 3388397 := bbase (se 3 (by rfl) ⟨635324, by rfl⟩ : syracuseStep 3388397 = 1270649) (by norm_num)
theorem B2258931 : Blo 2257435 2258931 := bstep (se 1 (by rfl) ⟨1694198, by rfl⟩ : syracuseStep 2258931 = 3388397) B3388397
theorem B5082605 : Blo 2257435 5082605 := bbase (se 3 (by rfl) ⟨952988, by rfl⟩ : syracuseStep 5082605 = 1905977) (by norm_num)
theorem B3388403 : Blo 2257435 3388403 := bstep (se 1 (by rfl) ⟨2541302, by rfl⟩ : syracuseStep 3388403 = 5082605) B5082605
theorem B2258935 : Blo 2257435 2258935 := bstep (se 1 (by rfl) ⟨1694201, by rfl⟩ : syracuseStep 2258935 = 3388403) B3388403
theorem B7236773 : Blo 2257435 7236773 := bbase (se 4 (by rfl) ⟨678447, by rfl⟩ : syracuseStep 7236773 = 1356895) (by norm_num)
theorem B4824515 : Blo 2257435 4824515 := bstep (se 1 (by rfl) ⟨3618386, by rfl⟩ : syracuseStep 4824515 = 7236773) B7236773
theorem B3216343 : Blo 2257435 3216343 := bstep (se 1 (by rfl) ⟨2412257, by rfl⟩ : syracuseStep 3216343 = 4824515) B4824515
theorem B4288457 : Blo 2257435 4288457 := bstep (se 2 (by rfl) ⟨1608171, by rfl⟩ : syracuseStep 4288457 = 3216343) B3216343
theorem B2858971 : Blo 2257435 2858971 := bstep (se 1 (by rfl) ⟨2144228, by rfl⟩ : syracuseStep 2858971 = 4288457) B4288457
theorem B3811961 : Blo 2257435 3811961 := bstep (se 2 (by rfl) ⟨1429485, by rfl⟩ : syracuseStep 3811961 = 2858971) B2858971
theorem B2541307 : Blo 2257435 2541307 := bstep (se 1 (by rfl) ⟨1905980, by rfl⟩ : syracuseStep 2541307 = 3811961) B3811961
theorem B3388409 : Blo 2257435 3388409 := bstep (se 2 (by rfl) ⟨1270653, by rfl⟩ : syracuseStep 3388409 = 2541307) B2541307
theorem B2258939 : Blo 2257435 2258939 := bstep (se 1 (by rfl) ⟨1694204, by rfl⟩ : syracuseStep 2258939 = 3388409) B3388409
theorem B4589101 : Blo 2257435 4589101 := bbase (se 3 (by rfl) ⟨860456, by rfl⟩ : syracuseStep 4589101 = 1720913) (by norm_num)
theorem B24475205 : Blo 2257435 24475205 := bstep (se 4 (by rfl) ⟨2294550, by rfl⟩ : syracuseStep 24475205 = 4589101) B4589101
theorem B16316803 : Blo 2257435 16316803 := bstep (se 1 (by rfl) ⟨12237602, by rfl⟩ : syracuseStep 16316803 = 24475205) B24475205
theorem B21755737 : Blo 2257435 21755737 := bstep (se 2 (by rfl) ⟨8158401, by rfl⟩ : syracuseStep 21755737 = 16316803) B16316803
theorem B29007649 : Blo 2257435 29007649 := bstep (se 2 (by rfl) ⟨10877868, by rfl⟩ : syracuseStep 29007649 = 21755737) B21755737
theorem B38676865 : Blo 2257435 38676865 := bstep (se 2 (by rfl) ⟨14503824, by rfl⟩ : syracuseStep 38676865 = 29007649) B29007649
theorem B51569153 : Blo 2257435 51569153 := bstep (se 2 (by rfl) ⟨19338432, by rfl⟩ : syracuseStep 51569153 = 38676865) B38676865
theorem B34379435 : Blo 2257435 34379435 := bstep (se 1 (by rfl) ⟨25784576, by rfl⟩ : syracuseStep 34379435 = 51569153) B51569153
theorem B91678493 : Blo 2257435 91678493 := bstep (se 3 (by rfl) ⟨17189717, by rfl⟩ : syracuseStep 91678493 = 34379435) B34379435
theorem B244475981 : Blo 2257435 244475981 := bstep (se 3 (by rfl) ⟨45839246, by rfl⟩ : syracuseStep 244475981 = 91678493) B91678493
theorem B162983987 : Blo 2257435 162983987 := bstep (se 1 (by rfl) ⟨122237990, by rfl⟩ : syracuseStep 162983987 = 244475981) B244475981
theorem B108655991 : Blo 2257435 108655991 := bstep (se 1 (by rfl) ⟨81491993, by rfl⟩ : syracuseStep 108655991 = 162983987) B162983987
theorem B72437327 : Blo 2257435 72437327 := bstep (se 1 (by rfl) ⟨54327995, by rfl⟩ : syracuseStep 72437327 = 108655991) B108655991
theorem B48291551 : Blo 2257435 48291551 := bstep (se 1 (by rfl) ⟨36218663, by rfl⟩ : syracuseStep 48291551 = 72437327) B72437327
theorem B32194367 : Blo 2257435 32194367 := bstep (se 1 (by rfl) ⟨24145775, by rfl⟩ : syracuseStep 32194367 = 48291551) B48291551
theorem B21462911 : Blo 2257435 21462911 := bstep (se 1 (by rfl) ⟨16097183, by rfl⟩ : syracuseStep 21462911 = 32194367) B32194367
theorem B14308607 : Blo 2257435 14308607 := bstep (se 1 (by rfl) ⟨10731455, by rfl⟩ : syracuseStep 14308607 = 21462911) B21462911
theorem B38156285 : Blo 2257435 38156285 := bstep (se 3 (by rfl) ⟨7154303, by rfl⟩ : syracuseStep 38156285 = 14308607) B14308607
theorem B25437523 : Blo 2257435 25437523 := bstep (se 1 (by rfl) ⟨19078142, by rfl⟩ : syracuseStep 25437523 = 38156285) B38156285
theorem B33916697 : Blo 2257435 33916697 := bstep (se 2 (by rfl) ⟨12718761, by rfl⟩ : syracuseStep 33916697 = 25437523) B25437523
theorem B22611131 : Blo 2257435 22611131 := bstep (se 1 (by rfl) ⟨16958348, by rfl⟩ : syracuseStep 22611131 = 33916697) B33916697
theorem B15074087 : Blo 2257435 15074087 := bstep (se 1 (by rfl) ⟨11305565, by rfl⟩ : syracuseStep 15074087 = 22611131) B22611131
theorem B40197565 : Blo 2257435 40197565 := bstep (se 3 (by rfl) ⟨7537043, by rfl⟩ : syracuseStep 40197565 = 15074087) B15074087
theorem B214387013 : Blo 2257435 214387013 := bstep (se 4 (by rfl) ⟨20098782, by rfl⟩ : syracuseStep 214387013 = 40197565) B40197565
theorem B142924675 : Blo 2257435 142924675 := bstep (se 1 (by rfl) ⟨107193506, by rfl⟩ : syracuseStep 142924675 = 214387013) B214387013
theorem B190566233 : Blo 2257435 190566233 := bstep (se 2 (by rfl) ⟨71462337, by rfl⟩ : syracuseStep 190566233 = 142924675) B142924675
theorem B127044155 : Blo 2257435 127044155 := bstep (se 1 (by rfl) ⟨95283116, by rfl⟩ : syracuseStep 127044155 = 190566233) B190566233
theorem B84696103 : Blo 2257435 84696103 := bstep (se 1 (by rfl) ⟨63522077, by rfl⟩ : syracuseStep 84696103 = 127044155) B127044155
theorem B112928137 : Blo 2257435 112928137 := bstep (se 2 (by rfl) ⟨42348051, by rfl⟩ : syracuseStep 112928137 = 84696103) B84696103
theorem B2409133589 : Blo 2257435 2409133589 := bstep (se 6 (by rfl) ⟨56464068, by rfl⟩ : syracuseStep 2409133589 = 112928137) B112928137
theorem B1606089059 : Blo 2257435 1606089059 := bstep (se 1 (by rfl) ⟨1204566794, by rfl⟩ : syracuseStep 1606089059 = 2409133589) B2409133589
theorem B1070726039 : Blo 2257435 1070726039 := bstep (se 1 (by rfl) ⟨803044529, by rfl⟩ : syracuseStep 1070726039 = 1606089059) B1606089059
theorem B713817359 : Blo 2257435 713817359 := bstep (se 1 (by rfl) ⟨535363019, by rfl⟩ : syracuseStep 713817359 = 1070726039) B1070726039
theorem B475878239 : Blo 2257435 475878239 := bstep (se 1 (by rfl) ⟨356908679, by rfl⟩ : syracuseStep 475878239 = 713817359) B713817359
theorem B317252159 : Blo 2257435 317252159 := bstep (se 1 (by rfl) ⟨237939119, by rfl⟩ : syracuseStep 317252159 = 475878239) B475878239
theorem B211501439 : Blo 2257435 211501439 := bstep (se 1 (by rfl) ⟨158626079, by rfl⟩ : syracuseStep 211501439 = 317252159) B317252159
theorem B141000959 : Blo 2257435 141000959 := bstep (se 1 (by rfl) ⟨105750719, by rfl⟩ : syracuseStep 141000959 = 211501439) B211501439
theorem B376002557 : Blo 2257435 376002557 := bstep (se 3 (by rfl) ⟨70500479, by rfl⟩ : syracuseStep 376002557 = 141000959) B141000959
theorem B250668371 : Blo 2257435 250668371 := bstep (se 1 (by rfl) ⟨188001278, by rfl⟩ : syracuseStep 250668371 = 376002557) B376002557
theorem B167112247 : Blo 2257435 167112247 := bstep (se 1 (by rfl) ⟨125334185, by rfl⟩ : syracuseStep 167112247 = 250668371) B250668371
theorem B222816329 : Blo 2257435 222816329 := bstep (se 2 (by rfl) ⟨83556123, by rfl⟩ : syracuseStep 222816329 = 167112247) B167112247
theorem B148544219 : Blo 2257435 148544219 := bstep (se 1 (by rfl) ⟨111408164, by rfl⟩ : syracuseStep 148544219 = 222816329) B222816329
theorem B99029479 : Blo 2257435 99029479 := bstep (se 1 (by rfl) ⟨74272109, by rfl⟩ : syracuseStep 99029479 = 148544219) B148544219
theorem B132039305 : Blo 2257435 132039305 := bstep (se 2 (by rfl) ⟨49514739, by rfl⟩ : syracuseStep 132039305 = 99029479) B99029479
theorem B88026203 : Blo 2257435 88026203 := bstep (se 1 (by rfl) ⟨66019652, by rfl⟩ : syracuseStep 88026203 = 132039305) B132039305
theorem B234736541 : Blo 2257435 234736541 := bstep (se 3 (by rfl) ⟨44013101, by rfl⟩ : syracuseStep 234736541 = 88026203) B88026203
theorem B156491027 : Blo 2257435 156491027 := bstep (se 1 (by rfl) ⟨117368270, by rfl⟩ : syracuseStep 156491027 = 234736541) B234736541
theorem B104327351 : Blo 2257435 104327351 := bstep (se 1 (by rfl) ⟨78245513, by rfl⟩ : syracuseStep 104327351 = 156491027) B156491027
theorem B69551567 : Blo 2257435 69551567 := bstep (se 1 (by rfl) ⟨52163675, by rfl⟩ : syracuseStep 69551567 = 104327351) B104327351
theorem B46367711 : Blo 2257435 46367711 := bstep (se 1 (by rfl) ⟨34775783, by rfl⟩ : syracuseStep 46367711 = 69551567) B69551567
theorem B30911807 : Blo 2257435 30911807 := bstep (se 1 (by rfl) ⟨23183855, by rfl⟩ : syracuseStep 30911807 = 46367711) B46367711
theorem B20607871 : Blo 2257435 20607871 := bstep (se 1 (by rfl) ⟨15455903, by rfl⟩ : syracuseStep 20607871 = 30911807) B30911807
theorem B27477161 : Blo 2257435 27477161 := bstep (se 2 (by rfl) ⟨10303935, by rfl⟩ : syracuseStep 27477161 = 20607871) B20607871
theorem B18318107 : Blo 2257435 18318107 := bstep (se 1 (by rfl) ⟨13738580, by rfl⟩ : syracuseStep 18318107 = 27477161) B27477161
theorem B48848285 : Blo 2257435 48848285 := bstep (se 3 (by rfl) ⟨9159053, by rfl⟩ : syracuseStep 48848285 = 18318107) B18318107
theorem B130262093 : Blo 2257435 130262093 := bstep (se 3 (by rfl) ⟨24424142, by rfl⟩ : syracuseStep 130262093 = 48848285) B48848285
theorem B86841395 : Blo 2257435 86841395 := bstep (se 1 (by rfl) ⟨65131046, by rfl⟩ : syracuseStep 86841395 = 130262093) B130262093
theorem B57894263 : Blo 2257435 57894263 := bstep (se 1 (by rfl) ⟨43420697, by rfl⟩ : syracuseStep 57894263 = 86841395) B86841395
theorem B38596175 : Blo 2257435 38596175 := bstep (se 1 (by rfl) ⟨28947131, by rfl⟩ : syracuseStep 38596175 = 57894263) B57894263
theorem B25730783 : Blo 2257435 25730783 := bstep (se 1 (by rfl) ⟨19298087, by rfl⟩ : syracuseStep 25730783 = 38596175) B38596175
theorem B17153855 : Blo 2257435 17153855 := bstep (se 1 (by rfl) ⟨12865391, by rfl⟩ : syracuseStep 17153855 = 25730783) B25730783
theorem B11435903 : Blo 2257435 11435903 := bstep (se 1 (by rfl) ⟨8576927, by rfl⟩ : syracuseStep 11435903 = 17153855) B17153855
theorem B7623935 : Blo 2257435 7623935 := bstep (se 1 (by rfl) ⟨5717951, by rfl⟩ : syracuseStep 7623935 = 11435903) B11435903
theorem B5082623 : Blo 2257435 5082623 := bstep (se 1 (by rfl) ⟨3811967, by rfl⟩ : syracuseStep 5082623 = 7623935) B7623935
theorem B3388415 : Blo 2257435 3388415 := bstep (se 1 (by rfl) ⟨2541311, by rfl⟩ : syracuseStep 3388415 = 5082623) B5082623
theorem B2258943 : Blo 2257435 2258943 := bstep (se 1 (by rfl) ⟨1694207, by rfl⟩ : syracuseStep 2258943 = 3388415) B3388415
theorem B3388421 : Blo 2257435 3388421 := bbase (se 4 (by rfl) ⟨317664, by rfl⟩ : syracuseStep 3388421 = 635329) (by norm_num)
theorem B2258947 : Blo 2257435 2258947 := bstep (se 1 (by rfl) ⟨1694210, by rfl⟩ : syracuseStep 2258947 = 3388421) B3388421
theorem B3811981 : Blo 2257435 3811981 := bbase (se 3 (by rfl) ⟨714746, by rfl⟩ : syracuseStep 3811981 = 1429493) (by norm_num)
theorem B5082641 : Blo 2257435 5082641 := bstep (se 2 (by rfl) ⟨1905990, by rfl⟩ : syracuseStep 5082641 = 3811981) B3811981
theorem B3388427 : Blo 2257435 3388427 := bstep (se 1 (by rfl) ⟨2541320, by rfl⟩ : syracuseStep 3388427 = 5082641) B5082641
theorem B2258951 : Blo 2257435 2258951 := bstep (se 1 (by rfl) ⟨1694213, by rfl⟩ : syracuseStep 2258951 = 3388427) B3388427
theorem B2541325 : Blo 2257435 2541325 := bbase (se 3 (by rfl) ⟨476498, by rfl⟩ : syracuseStep 2541325 = 952997) (by norm_num)
theorem B3388433 : Blo 2257435 3388433 := bstep (se 2 (by rfl) ⟨1270662, by rfl⟩ : syracuseStep 3388433 = 2541325) B2541325
theorem B2258955 : Blo 2257435 2258955 := bstep (se 1 (by rfl) ⟨1694216, by rfl⟩ : syracuseStep 2258955 = 3388433) B3388433
theorem B7623989 : Blo 2257435 7623989 := bbase (se 5 (by rfl) ⟨357374, by rfl⟩ : syracuseStep 7623989 = 714749) (by norm_num)
theorem B5082659 : Blo 2257435 5082659 := bstep (se 1 (by rfl) ⟨3811994, by rfl⟩ : syracuseStep 5082659 = 7623989) B7623989
theorem B3388439 : Blo 2257435 3388439 := bstep (se 1 (by rfl) ⟨2541329, by rfl⟩ : syracuseStep 3388439 = 5082659) B5082659
theorem B2258959 : Blo 2257435 2258959 := bstep (se 1 (by rfl) ⟨1694219, by rfl⟩ : syracuseStep 2258959 = 3388439) B3388439
theorem B3388445 : Blo 2257435 3388445 := bbase (se 3 (by rfl) ⟨635333, by rfl⟩ : syracuseStep 3388445 = 1270667) (by norm_num)
theorem B2258963 : Blo 2257435 2258963 := bstep (se 1 (by rfl) ⟨1694222, by rfl⟩ : syracuseStep 2258963 = 3388445) B3388445
theorem B5082677 : Blo 2257435 5082677 := bbase (se 5 (by rfl) ⟨238250, by rfl⟩ : syracuseStep 5082677 = 476501) (by norm_num)
theorem B3388451 : Blo 2257435 3388451 := bstep (se 1 (by rfl) ⟨2541338, by rfl⟩ : syracuseStep 3388451 = 5082677) B5082677
theorem B2258967 : Blo 2257435 2258967 := bstep (se 1 (by rfl) ⟨1694225, by rfl⟩ : syracuseStep 2258967 = 3388451) B3388451
theorem B3618437 : Blo 2257435 3618437 := bbase (se 4 (by rfl) ⟨339228, by rfl⟩ : syracuseStep 3618437 = 678457) (by norm_num)
theorem B9649165 : Blo 2257435 9649165 := bstep (se 3 (by rfl) ⟨1809218, by rfl⟩ : syracuseStep 9649165 = 3618437) B3618437
theorem B12865553 : Blo 2257435 12865553 := bstep (se 2 (by rfl) ⟨4824582, by rfl⟩ : syracuseStep 12865553 = 9649165) B9649165
theorem B8577035 : Blo 2257435 8577035 := bstep (se 1 (by rfl) ⟨6432776, by rfl⟩ : syracuseStep 8577035 = 12865553) B12865553
theorem B5718023 : Blo 2257435 5718023 := bstep (se 1 (by rfl) ⟨4288517, by rfl⟩ : syracuseStep 5718023 = 8577035) B8577035
theorem B3812015 : Blo 2257435 3812015 := bstep (se 1 (by rfl) ⟨2859011, by rfl⟩ : syracuseStep 3812015 = 5718023) B5718023
theorem B2541343 : Blo 2257435 2541343 := bstep (se 1 (by rfl) ⟨1906007, by rfl⟩ : syracuseStep 2541343 = 3812015) B3812015
theorem B3388457 : Blo 2257435 3388457 := bstep (se 2 (by rfl) ⟨1270671, by rfl⟩ : syracuseStep 3388457 = 2541343) B2541343
theorem B2258971 : Blo 2257435 2258971 := bstep (se 1 (by rfl) ⟨1694228, by rfl⟩ : syracuseStep 2258971 = 3388457) B3388457
theorem B4070749 : Blo 2257435 4070749 := bbase (se 3 (by rfl) ⟨763265, by rfl⟩ : syracuseStep 4070749 = 1526531) (by norm_num)
theorem B5427665 : Blo 2257435 5427665 := bstep (se 2 (by rfl) ⟨2035374, by rfl⟩ : syracuseStep 5427665 = 4070749) B4070749
theorem B3618443 : Blo 2257435 3618443 := bstep (se 1 (by rfl) ⟨2713832, by rfl⟩ : syracuseStep 3618443 = 5427665) B5427665
theorem B9649181 : Blo 2257435 9649181 := bstep (se 3 (by rfl) ⟨1809221, by rfl⟩ : syracuseStep 9649181 = 3618443) B3618443
theorem B6432787 : Blo 2257435 6432787 := bstep (se 1 (by rfl) ⟨4824590, by rfl⟩ : syracuseStep 6432787 = 9649181) B9649181
theorem B8577049 : Blo 2257435 8577049 := bstep (se 2 (by rfl) ⟨3216393, by rfl⟩ : syracuseStep 8577049 = 6432787) B6432787
theorem B11436065 : Blo 2257435 11436065 := bstep (se 2 (by rfl) ⟨4288524, by rfl⟩ : syracuseStep 11436065 = 8577049) B8577049
theorem B7624043 : Blo 2257435 7624043 := bstep (se 1 (by rfl) ⟨5718032, by rfl⟩ : syracuseStep 7624043 = 11436065) B11436065
theorem B5082695 : Blo 2257435 5082695 := bstep (se 1 (by rfl) ⟨3812021, by rfl⟩ : syracuseStep 5082695 = 7624043) B7624043
theorem B3388463 : Blo 2257435 3388463 := bstep (se 1 (by rfl) ⟨2541347, by rfl⟩ : syracuseStep 3388463 = 5082695) B5082695
theorem B2258975 : Blo 2257435 2258975 := bstep (se 1 (by rfl) ⟨1694231, by rfl⟩ : syracuseStep 2258975 = 3388463) B3388463
theorem B3388469 : Blo 2257435 3388469 := bbase (se 5 (by rfl) ⟨158834, by rfl⟩ : syracuseStep 3388469 = 317669) (by norm_num)
theorem B2258979 : Blo 2257435 2258979 := bstep (se 1 (by rfl) ⟨1694234, by rfl⟩ : syracuseStep 2258979 = 3388469) B3388469
theorem B5718053 : Blo 2257435 5718053 := bbase (se 4 (by rfl) ⟨536067, by rfl⟩ : syracuseStep 5718053 = 1072135) (by norm_num)
theorem B3812035 : Blo 2257435 3812035 := bstep (se 1 (by rfl) ⟨2859026, by rfl⟩ : syracuseStep 3812035 = 5718053) B5718053
theorem B5082713 : Blo 2257435 5082713 := bstep (se 2 (by rfl) ⟨1906017, by rfl⟩ : syracuseStep 5082713 = 3812035) B3812035
theorem B3388475 : Blo 2257435 3388475 := bstep (se 1 (by rfl) ⟨2541356, by rfl⟩ : syracuseStep 3388475 = 5082713) B5082713
theorem B2258983 : Blo 2257435 2258983 := bstep (se 1 (by rfl) ⟨1694237, by rfl⟩ : syracuseStep 2258983 = 3388475) B3388475
theorem B2541361 : Blo 2257435 2541361 := bbase (se 2 (by rfl) ⟨953010, by rfl⟩ : syracuseStep 2541361 = 1906021) (by norm_num)
theorem B3388481 : Blo 2257435 3388481 := bstep (se 2 (by rfl) ⟨1270680, by rfl⟩ : syracuseStep 3388481 = 2541361) B2541361
theorem B2258987 : Blo 2257435 2258987 := bstep (se 1 (by rfl) ⟨1694240, by rfl⟩ : syracuseStep 2258987 = 3388481) B3388481
theorem B3618469 : Blo 2257435 3618469 := bbase (se 4 (by rfl) ⟨339231, by rfl⟩ : syracuseStep 3618469 = 678463) (by norm_num)
theorem B4824625 : Blo 2257435 4824625 := bstep (se 2 (by rfl) ⟨1809234, by rfl⟩ : syracuseStep 4824625 = 3618469) B3618469
theorem B6432833 : Blo 2257435 6432833 := bstep (se 2 (by rfl) ⟨2412312, by rfl⟩ : syracuseStep 6432833 = 4824625) B4824625
theorem B4288555 : Blo 2257435 4288555 := bstep (se 1 (by rfl) ⟨3216416, by rfl⟩ : syracuseStep 4288555 = 6432833) B6432833
theorem B5718073 : Blo 2257435 5718073 := bstep (se 2 (by rfl) ⟨2144277, by rfl⟩ : syracuseStep 5718073 = 4288555) B4288555
theorem B7624097 : Blo 2257435 7624097 := bstep (se 2 (by rfl) ⟨2859036, by rfl⟩ : syracuseStep 7624097 = 5718073) B5718073
theorem B5082731 : Blo 2257435 5082731 := bstep (se 1 (by rfl) ⟨3812048, by rfl⟩ : syracuseStep 5082731 = 7624097) B7624097
theorem B3388487 : Blo 2257435 3388487 := bstep (se 1 (by rfl) ⟨2541365, by rfl⟩ : syracuseStep 3388487 = 5082731) B5082731
theorem B2258991 : Blo 2257435 2258991 := bstep (se 1 (by rfl) ⟨1694243, by rfl⟩ : syracuseStep 2258991 = 3388487) B3388487
theorem B3388493 : Blo 2257435 3388493 := bbase (se 3 (by rfl) ⟨635342, by rfl⟩ : syracuseStep 3388493 = 1270685) (by norm_num)
theorem B2258995 : Blo 2257435 2258995 := bstep (se 1 (by rfl) ⟨1694246, by rfl⟩ : syracuseStep 2258995 = 3388493) B3388493
theorem B5082749 : Blo 2257435 5082749 := bbase (se 3 (by rfl) ⟨953015, by rfl⟩ : syracuseStep 5082749 = 1906031) (by norm_num)
theorem B3388499 : Blo 2257435 3388499 := bstep (se 1 (by rfl) ⟨2541374, by rfl⟩ : syracuseStep 3388499 = 5082749) B5082749
theorem B2258999 : Blo 2257435 2258999 := bstep (se 1 (by rfl) ⟨1694249, by rfl⟩ : syracuseStep 2258999 = 3388499) B3388499
theorem B3812069 : Blo 2257435 3812069 := bbase (se 4 (by rfl) ⟨357381, by rfl⟩ : syracuseStep 3812069 = 714763) (by norm_num)
theorem B2541379 : Blo 2257435 2541379 := bstep (se 1 (by rfl) ⟨1906034, by rfl⟩ : syracuseStep 2541379 = 3812069) B3812069
theorem B3388505 : Blo 2257435 3388505 := bstep (se 2 (by rfl) ⟨1270689, by rfl⟩ : syracuseStep 3388505 = 2541379) B2541379
theorem B2259003 : Blo 2257435 2259003 := bstep (se 1 (by rfl) ⟨1694252, by rfl⟩ : syracuseStep 2259003 = 3388505) B3388505
theorem B9159317 : Blo 2257435 9159317 := bbase (se 6 (by rfl) ⟨214671, by rfl⟩ : syracuseStep 9159317 = 429343) (by norm_num)
theorem B6106211 : Blo 2257435 6106211 := bstep (se 1 (by rfl) ⟨4579658, by rfl⟩ : syracuseStep 6106211 = 9159317) B9159317
theorem B4070807 : Blo 2257435 4070807 := bstep (se 1 (by rfl) ⟨3053105, by rfl⟩ : syracuseStep 4070807 = 6106211) B6106211
theorem B2713871 : Blo 2257435 2713871 := bstep (se 1 (by rfl) ⟨2035403, by rfl⟩ : syracuseStep 2713871 = 4070807) B4070807
theorem B7236989 : Blo 2257435 7236989 := bstep (se 3 (by rfl) ⟨1356935, by rfl⟩ : syracuseStep 7236989 = 2713871) B2713871
theorem B4824659 : Blo 2257435 4824659 := bstep (se 1 (by rfl) ⟨3618494, by rfl⟩ : syracuseStep 4824659 = 7236989) B7236989
theorem B3216439 : Blo 2257435 3216439 := bstep (se 1 (by rfl) ⟨2412329, by rfl⟩ : syracuseStep 3216439 = 4824659) B4824659
theorem B17154341 : Blo 2257435 17154341 := bstep (se 4 (by rfl) ⟨1608219, by rfl⟩ : syracuseStep 17154341 = 3216439) B3216439
theorem B11436227 : Blo 2257435 11436227 := bstep (se 1 (by rfl) ⟨8577170, by rfl⟩ : syracuseStep 11436227 = 17154341) B17154341
theorem B7624151 : Blo 2257435 7624151 := bstep (se 1 (by rfl) ⟨5718113, by rfl⟩ : syracuseStep 7624151 = 11436227) B11436227
theorem B5082767 : Blo 2257435 5082767 := bstep (se 1 (by rfl) ⟨3812075, by rfl⟩ : syracuseStep 5082767 = 7624151) B7624151
theorem B3388511 : Blo 2257435 3388511 := bstep (se 1 (by rfl) ⟨2541383, by rfl⟩ : syracuseStep 3388511 = 5082767) B5082767
theorem B2259007 : Blo 2257435 2259007 := bstep (se 1 (by rfl) ⟨1694255, by rfl⟩ : syracuseStep 2259007 = 3388511) B3388511
theorem B3388517 : Blo 2257435 3388517 := bbase (se 4 (by rfl) ⟨317673, by rfl⟩ : syracuseStep 3388517 = 635347) (by norm_num)
theorem B2259011 : Blo 2257435 2259011 := bstep (se 1 (by rfl) ⟨1694258, by rfl⟩ : syracuseStep 2259011 = 3388517) B3388517
theorem B4824677 : Blo 2257435 4824677 := bbase (se 4 (by rfl) ⟨452313, by rfl⟩ : syracuseStep 4824677 = 904627) (by norm_num)
theorem B3216451 : Blo 2257435 3216451 := bstep (se 1 (by rfl) ⟨2412338, by rfl⟩ : syracuseStep 3216451 = 4824677) B4824677
theorem B4288601 : Blo 2257435 4288601 := bstep (se 2 (by rfl) ⟨1608225, by rfl⟩ : syracuseStep 4288601 = 3216451) B3216451
theorem B2859067 : Blo 2257435 2859067 := bstep (se 1 (by rfl) ⟨2144300, by rfl⟩ : syracuseStep 2859067 = 4288601) B4288601
theorem B3812089 : Blo 2257435 3812089 := bstep (se 2 (by rfl) ⟨1429533, by rfl⟩ : syracuseStep 3812089 = 2859067) B2859067
theorem B5082785 : Blo 2257435 5082785 := bstep (se 2 (by rfl) ⟨1906044, by rfl⟩ : syracuseStep 5082785 = 3812089) B3812089
theorem B3388523 : Blo 2257435 3388523 := bstep (se 1 (by rfl) ⟨2541392, by rfl⟩ : syracuseStep 3388523 = 5082785) B5082785
theorem B2259015 : Blo 2257435 2259015 := bstep (se 1 (by rfl) ⟨1694261, by rfl⟩ : syracuseStep 2259015 = 3388523) B3388523
theorem B2541397 : Blo 2257435 2541397 := bbase (se 9 (by rfl) ⟨7445, by rfl⟩ : syracuseStep 2541397 = 14891) (by norm_num)
theorem B3388529 : Blo 2257435 3388529 := bstep (se 2 (by rfl) ⟨1270698, by rfl⟩ : syracuseStep 3388529 = 2541397) B2541397
theorem B2259019 : Blo 2257435 2259019 := bstep (se 1 (by rfl) ⟨1694264, by rfl⟩ : syracuseStep 2259019 = 3388529) B3388529
theorem B2859077 : Blo 2257435 2859077 := bbase (se 4 (by rfl) ⟨268038, by rfl⟩ : syracuseStep 2859077 = 536077) (by norm_num)
theorem B7624205 : Blo 2257435 7624205 := bstep (se 3 (by rfl) ⟨1429538, by rfl⟩ : syracuseStep 7624205 = 2859077) B2859077
theorem B5082803 : Blo 2257435 5082803 := bstep (se 1 (by rfl) ⟨3812102, by rfl⟩ : syracuseStep 5082803 = 7624205) B7624205
theorem B3388535 : Blo 2257435 3388535 := bstep (se 1 (by rfl) ⟨2541401, by rfl⟩ : syracuseStep 3388535 = 5082803) B5082803
theorem B2259023 : Blo 2257435 2259023 := bstep (se 1 (by rfl) ⟨1694267, by rfl⟩ : syracuseStep 2259023 = 3388535) B3388535
theorem B3388541 : Blo 2257435 3388541 := bbase (se 3 (by rfl) ⟨635351, by rfl⟩ : syracuseStep 3388541 = 1270703) (by norm_num)
theorem B2259027 : Blo 2257435 2259027 := bstep (se 1 (by rfl) ⟨1694270, by rfl⟩ : syracuseStep 2259027 = 3388541) B3388541
theorem B5082821 : Blo 2257435 5082821 := bbase (se 4 (by rfl) ⟨476514, by rfl⟩ : syracuseStep 5082821 = 953029) (by norm_num)
theorem B3388547 : Blo 2257435 3388547 := bstep (se 1 (by rfl) ⟨2541410, by rfl⟩ : syracuseStep 3388547 = 5082821) B5082821
theorem B2259031 : Blo 2257435 2259031 := bstep (se 1 (by rfl) ⟨1694273, by rfl⟩ : syracuseStep 2259031 = 3388547) B3388547
theorem B36637717 : Blo 2257435 36637717 := bbase (se 6 (by rfl) ⟨858696, by rfl⟩ : syracuseStep 36637717 = 1717393) (by norm_num)
theorem B48850289 : Blo 2257435 48850289 := bstep (se 2 (by rfl) ⟨18318858, by rfl⟩ : syracuseStep 48850289 = 36637717) B36637717
theorem B32566859 : Blo 2257435 32566859 := bstep (se 1 (by rfl) ⟨24425144, by rfl⟩ : syracuseStep 32566859 = 48850289) B48850289
theorem B21711239 : Blo 2257435 21711239 := bstep (se 1 (by rfl) ⟨16283429, by rfl⟩ : syracuseStep 21711239 = 32566859) B32566859
theorem B14474159 : Blo 2257435 14474159 := bstep (se 1 (by rfl) ⟨10855619, by rfl⟩ : syracuseStep 14474159 = 21711239) B21711239
theorem B9649439 : Blo 2257435 9649439 := bstep (se 1 (by rfl) ⟨7237079, by rfl⟩ : syracuseStep 9649439 = 14474159) B14474159
theorem B6432959 : Blo 2257435 6432959 := bstep (se 1 (by rfl) ⟨4824719, by rfl⟩ : syracuseStep 6432959 = 9649439) B9649439
theorem B4288639 : Blo 2257435 4288639 := bstep (se 1 (by rfl) ⟨3216479, by rfl⟩ : syracuseStep 4288639 = 6432959) B6432959
theorem B5718185 : Blo 2257435 5718185 := bstep (se 2 (by rfl) ⟨2144319, by rfl⟩ : syracuseStep 5718185 = 4288639) B4288639
theorem B3812123 : Blo 2257435 3812123 := bstep (se 1 (by rfl) ⟨2859092, by rfl⟩ : syracuseStep 3812123 = 5718185) B5718185
theorem B2541415 : Blo 2257435 2541415 := bstep (se 1 (by rfl) ⟨1906061, by rfl⟩ : syracuseStep 2541415 = 3812123) B3812123
theorem B3388553 : Blo 2257435 3388553 := bstep (se 2 (by rfl) ⟨1270707, by rfl⟩ : syracuseStep 3388553 = 2541415) B2541415
theorem B2259035 : Blo 2257435 2259035 := bstep (se 1 (by rfl) ⟨1694276, by rfl⟩ : syracuseStep 2259035 = 3388553) B3388553
theorem B11436389 : Blo 2257435 11436389 := bbase (se 4 (by rfl) ⟨1072161, by rfl⟩ : syracuseStep 11436389 = 2144323) (by norm_num)
theorem B7624259 : Blo 2257435 7624259 := bstep (se 1 (by rfl) ⟨5718194, by rfl⟩ : syracuseStep 7624259 = 11436389) B11436389
theorem B5082839 : Blo 2257435 5082839 := bstep (se 1 (by rfl) ⟨3812129, by rfl⟩ : syracuseStep 5082839 = 7624259) B7624259
theorem B3388559 : Blo 2257435 3388559 := bstep (se 1 (by rfl) ⟨2541419, by rfl⟩ : syracuseStep 3388559 = 5082839) B5082839
theorem B2259039 : Blo 2257435 2259039 := bstep (se 1 (by rfl) ⟨1694279, by rfl⟩ : syracuseStep 2259039 = 3388559) B3388559
theorem B3388565 : Blo 2257435 3388565 := bbase (se 6 (by rfl) ⟨79419, by rfl⟩ : syracuseStep 3388565 = 158839) (by norm_num)
theorem B2259043 : Blo 2257435 2259043 := bstep (se 1 (by rfl) ⟨1694282, by rfl⟩ : syracuseStep 2259043 = 3388565) B3388565
theorem B4126421 : Blo 2257435 4126421 := bbase (se 7 (by rfl) ⟨48356, by rfl⟩ : syracuseStep 4126421 = 96713) (by norm_num)
theorem B11003789 : Blo 2257435 11003789 := bstep (se 3 (by rfl) ⟨2063210, by rfl⟩ : syracuseStep 11003789 = 4126421) B4126421
theorem B7335859 : Blo 2257435 7335859 := bstep (se 1 (by rfl) ⟨5501894, by rfl⟩ : syracuseStep 7335859 = 11003789) B11003789
theorem B9781145 : Blo 2257435 9781145 := bstep (se 2 (by rfl) ⟨3667929, by rfl⟩ : syracuseStep 9781145 = 7335859) B7335859
theorem B6520763 : Blo 2257435 6520763 := bstep (se 1 (by rfl) ⟨4890572, by rfl⟩ : syracuseStep 6520763 = 9781145) B9781145
theorem B17388701 : Blo 2257435 17388701 := bstep (se 3 (by rfl) ⟨3260381, by rfl⟩ : syracuseStep 17388701 = 6520763) B6520763
theorem B11592467 : Blo 2257435 11592467 := bstep (se 1 (by rfl) ⟨8694350, by rfl⟩ : syracuseStep 11592467 = 17388701) B17388701
theorem B7728311 : Blo 2257435 7728311 := bstep (se 1 (by rfl) ⟨5796233, by rfl⟩ : syracuseStep 7728311 = 11592467) B11592467
theorem B20608829 : Blo 2257435 20608829 := bstep (se 3 (by rfl) ⟨3864155, by rfl⟩ : syracuseStep 20608829 = 7728311) B7728311
theorem B13739219 : Blo 2257435 13739219 := bstep (se 1 (by rfl) ⟨10304414, by rfl⟩ : syracuseStep 13739219 = 20608829) B20608829
theorem B9159479 : Blo 2257435 9159479 := bstep (se 1 (by rfl) ⟨6869609, by rfl⟩ : syracuseStep 9159479 = 13739219) B13739219
theorem B6106319 : Blo 2257435 6106319 := bstep (se 1 (by rfl) ⟨4579739, by rfl⟩ : syracuseStep 6106319 = 9159479) B9159479
theorem B4070879 : Blo 2257435 4070879 := bstep (se 1 (by rfl) ⟨3053159, by rfl⟩ : syracuseStep 4070879 = 6106319) B6106319
theorem B2713919 : Blo 2257435 2713919 := bstep (se 1 (by rfl) ⟨2035439, by rfl⟩ : syracuseStep 2713919 = 4070879) B4070879
theorem B7237117 : Blo 2257435 7237117 := bstep (se 3 (by rfl) ⟨1356959, by rfl⟩ : syracuseStep 7237117 = 2713919) B2713919
theorem B9649489 : Blo 2257435 9649489 := bstep (se 2 (by rfl) ⟨3618558, by rfl⟩ : syracuseStep 9649489 = 7237117) B7237117
theorem B12865985 : Blo 2257435 12865985 := bstep (se 2 (by rfl) ⟨4824744, by rfl⟩ : syracuseStep 12865985 = 9649489) B9649489
theorem B8577323 : Blo 2257435 8577323 := bstep (se 1 (by rfl) ⟨6432992, by rfl⟩ : syracuseStep 8577323 = 12865985) B12865985
theorem B5718215 : Blo 2257435 5718215 := bstep (se 1 (by rfl) ⟨4288661, by rfl⟩ : syracuseStep 5718215 = 8577323) B8577323
theorem B3812143 : Blo 2257435 3812143 := bstep (se 1 (by rfl) ⟨2859107, by rfl⟩ : syracuseStep 3812143 = 5718215) B5718215
theorem B5082857 : Blo 2257435 5082857 := bstep (se 2 (by rfl) ⟨1906071, by rfl⟩ : syracuseStep 5082857 = 3812143) B3812143
theorem B3388571 : Blo 2257435 3388571 := bstep (se 1 (by rfl) ⟨2541428, by rfl⟩ : syracuseStep 3388571 = 5082857) B5082857
theorem B2259047 : Blo 2257435 2259047 := bstep (se 1 (by rfl) ⟨1694285, by rfl⟩ : syracuseStep 2259047 = 3388571) B3388571
theorem B2541433 : Blo 2257435 2541433 := bbase (se 2 (by rfl) ⟨953037, by rfl⟩ : syracuseStep 2541433 = 1906075) (by norm_num)
theorem B3388577 : Blo 2257435 3388577 := bstep (se 2 (by rfl) ⟨1270716, by rfl⟩ : syracuseStep 3388577 = 2541433) B2541433
theorem B2259051 : Blo 2257435 2259051 := bstep (se 1 (by rfl) ⟨1694288, by rfl⟩ : syracuseStep 2259051 = 3388577) B3388577
theorem B4070893 : Blo 2257435 4070893 := bbase (se 3 (by rfl) ⟨763292, by rfl⟩ : syracuseStep 4070893 = 1526585) (by norm_num)
theorem B5427857 : Blo 2257435 5427857 := bstep (se 2 (by rfl) ⟨2035446, by rfl⟩ : syracuseStep 5427857 = 4070893) B4070893
theorem B14474285 : Blo 2257435 14474285 := bstep (se 3 (by rfl) ⟨2713928, by rfl⟩ : syracuseStep 14474285 = 5427857) B5427857
theorem B9649523 : Blo 2257435 9649523 := bstep (se 1 (by rfl) ⟨7237142, by rfl⟩ : syracuseStep 9649523 = 14474285) B14474285
theorem B6433015 : Blo 2257435 6433015 := bstep (se 1 (by rfl) ⟨4824761, by rfl⟩ : syracuseStep 6433015 = 9649523) B9649523
theorem B8577353 : Blo 2257435 8577353 := bstep (se 2 (by rfl) ⟨3216507, by rfl⟩ : syracuseStep 8577353 = 6433015) B6433015
theorem B5718235 : Blo 2257435 5718235 := bstep (se 1 (by rfl) ⟨4288676, by rfl⟩ : syracuseStep 5718235 = 8577353) B8577353
theorem B7624313 : Blo 2257435 7624313 := bstep (se 2 (by rfl) ⟨2859117, by rfl⟩ : syracuseStep 7624313 = 5718235) B5718235
theorem B5082875 : Blo 2257435 5082875 := bstep (se 1 (by rfl) ⟨3812156, by rfl⟩ : syracuseStep 5082875 = 7624313) B7624313
theorem B3388583 : Blo 2257435 3388583 := bstep (se 1 (by rfl) ⟨2541437, by rfl⟩ : syracuseStep 3388583 = 5082875) B5082875
theorem B2259055 : Blo 2257435 2259055 := bstep (se 1 (by rfl) ⟨1694291, by rfl⟩ : syracuseStep 2259055 = 3388583) B3388583
theorem B3388589 : Blo 2257435 3388589 := bbase (se 3 (by rfl) ⟨635360, by rfl⟩ : syracuseStep 3388589 = 1270721) (by norm_num)
theorem B2259059 : Blo 2257435 2259059 := bstep (se 1 (by rfl) ⟨1694294, by rfl⟩ : syracuseStep 2259059 = 3388589) B3388589
theorem B5082893 : Blo 2257435 5082893 := bbase (se 3 (by rfl) ⟨953042, by rfl⟩ : syracuseStep 5082893 = 1906085) (by norm_num)
theorem B3388595 : Blo 2257435 3388595 := bstep (se 1 (by rfl) ⟨2541446, by rfl⟩ : syracuseStep 3388595 = 5082893) B5082893
theorem B2259063 : Blo 2257435 2259063 := bstep (se 1 (by rfl) ⟨1694297, by rfl⟩ : syracuseStep 2259063 = 3388595) B3388595
theorem B2859133 : Blo 2257435 2859133 := bbase (se 3 (by rfl) ⟨536087, by rfl⟩ : syracuseStep 2859133 = 1072175) (by norm_num)
theorem B3812177 : Blo 2257435 3812177 := bstep (se 2 (by rfl) ⟨1429566, by rfl⟩ : syracuseStep 3812177 = 2859133) B2859133
theorem B2541451 : Blo 2257435 2541451 := bstep (se 1 (by rfl) ⟨1906088, by rfl⟩ : syracuseStep 2541451 = 3812177) B3812177
theorem B3388601 : Blo 2257435 3388601 := bstep (se 2 (by rfl) ⟨1270725, by rfl⟩ : syracuseStep 3388601 = 2541451) B2541451
theorem B2259067 : Blo 2257435 2259067 := bstep (se 1 (by rfl) ⟨1694300, by rfl⟩ : syracuseStep 2259067 = 3388601) B3388601
theorem B5152261 : Blo 2257435 5152261 := bbase (se 4 (by rfl) ⟨483024, by rfl⟩ : syracuseStep 5152261 = 966049) (by norm_num)
theorem B6869681 : Blo 2257435 6869681 := bstep (se 2 (by rfl) ⟨2576130, by rfl⟩ : syracuseStep 6869681 = 5152261) B5152261
theorem B4579787 : Blo 2257435 4579787 := bstep (se 1 (by rfl) ⟨3434840, by rfl⟩ : syracuseStep 4579787 = 6869681) B6869681
theorem B12212765 : Blo 2257435 12212765 := bstep (se 3 (by rfl) ⟨2289893, by rfl⟩ : syracuseStep 12212765 = 4579787) B4579787
theorem B8141843 : Blo 2257435 8141843 := bstep (se 1 (by rfl) ⟨6106382, by rfl⟩ : syracuseStep 8141843 = 12212765) B12212765
theorem B5427895 : Blo 2257435 5427895 := bstep (se 1 (by rfl) ⟨4070921, by rfl⟩ : syracuseStep 5427895 = 8141843) B8141843
theorem B7237193 : Blo 2257435 7237193 := bstep (se 2 (by rfl) ⟨2713947, by rfl⟩ : syracuseStep 7237193 = 5427895) B5427895
theorem B19299181 : Blo 2257435 19299181 := bstep (se 3 (by rfl) ⟨3618596, by rfl⟩ : syracuseStep 19299181 = 7237193) B7237193
theorem B25732241 : Blo 2257435 25732241 := bstep (se 2 (by rfl) ⟨9649590, by rfl⟩ : syracuseStep 25732241 = 19299181) B19299181
theorem B17154827 : Blo 2257435 17154827 := bstep (se 1 (by rfl) ⟨12866120, by rfl⟩ : syracuseStep 17154827 = 25732241) B25732241
theorem B11436551 : Blo 2257435 11436551 := bstep (se 1 (by rfl) ⟨8577413, by rfl⟩ : syracuseStep 11436551 = 17154827) B17154827
theorem B7624367 : Blo 2257435 7624367 := bstep (se 1 (by rfl) ⟨5718275, by rfl⟩ : syracuseStep 7624367 = 11436551) B11436551
theorem B5082911 : Blo 2257435 5082911 := bstep (se 1 (by rfl) ⟨3812183, by rfl⟩ : syracuseStep 5082911 = 7624367) B7624367
theorem B3388607 : Blo 2257435 3388607 := bstep (se 1 (by rfl) ⟨2541455, by rfl⟩ : syracuseStep 3388607 = 5082911) B5082911
theorem B2259071 : Blo 2257435 2259071 := bstep (se 1 (by rfl) ⟨1694303, by rfl⟩ : syracuseStep 2259071 = 3388607) B3388607
theorem B3388613 : Blo 2257435 3388613 := bbase (se 4 (by rfl) ⟨317682, by rfl⟩ : syracuseStep 3388613 = 635365) (by norm_num)
theorem B2259075 : Blo 2257435 2259075 := bstep (se 1 (by rfl) ⟨1694306, by rfl⟩ : syracuseStep 2259075 = 3388613) B3388613
theorem B3812197 : Blo 2257435 3812197 := bbase (se 4 (by rfl) ⟨357393, by rfl⟩ : syracuseStep 3812197 = 714787) (by norm_num)
theorem B5082929 : Blo 2257435 5082929 := bstep (se 2 (by rfl) ⟨1906098, by rfl⟩ : syracuseStep 5082929 = 3812197) B3812197
theorem B3388619 : Blo 2257435 3388619 := bstep (se 1 (by rfl) ⟨2541464, by rfl⟩ : syracuseStep 3388619 = 5082929) B5082929
theorem B2259079 : Blo 2257435 2259079 := bstep (se 1 (by rfl) ⟨1694309, by rfl⟩ : syracuseStep 2259079 = 3388619) B3388619
theorem B2541469 : Blo 2257435 2541469 := bbase (se 3 (by rfl) ⟨476525, by rfl⟩ : syracuseStep 2541469 = 953051) (by norm_num)
theorem B3388625 : Blo 2257435 3388625 := bstep (se 2 (by rfl) ⟨1270734, by rfl⟩ : syracuseStep 3388625 = 2541469) B2541469
theorem B2259083 : Blo 2257435 2259083 := bstep (se 1 (by rfl) ⟨1694312, by rfl⟩ : syracuseStep 2259083 = 3388625) B3388625
theorem B7624421 : Blo 2257435 7624421 := bbase (se 4 (by rfl) ⟨714789, by rfl⟩ : syracuseStep 7624421 = 1429579) (by norm_num)
theorem B5082947 : Blo 2257435 5082947 := bstep (se 1 (by rfl) ⟨3812210, by rfl⟩ : syracuseStep 5082947 = 7624421) B7624421
theorem B3388631 : Blo 2257435 3388631 := bstep (se 1 (by rfl) ⟨2541473, by rfl⟩ : syracuseStep 3388631 = 5082947) B5082947
theorem B2259087 : Blo 2257435 2259087 := bstep (se 1 (by rfl) ⟨1694315, by rfl⟩ : syracuseStep 2259087 = 3388631) B3388631
theorem B3388637 : Blo 2257435 3388637 := bbase (se 3 (by rfl) ⟨635369, by rfl⟩ : syracuseStep 3388637 = 1270739) (by norm_num)
theorem B2259091 : Blo 2257435 2259091 := bstep (se 1 (by rfl) ⟨1694318, by rfl⟩ : syracuseStep 2259091 = 3388637) B3388637
theorem B5082965 : Blo 2257435 5082965 := bbase (se 9 (by rfl) ⟨14891, by rfl⟩ : syracuseStep 5082965 = 29783) (by norm_num)
theorem B3388643 : Blo 2257435 3388643 := bstep (se 1 (by rfl) ⟨2541482, by rfl⟩ : syracuseStep 3388643 = 5082965) B5082965
theorem B2259095 : Blo 2257435 2259095 := bstep (se 1 (by rfl) ⟨1694321, by rfl⟩ : syracuseStep 2259095 = 3388643) B3388643
theorem B6433141 : Blo 2257435 6433141 := bbase (se 5 (by rfl) ⟨301553, by rfl⟩ : syracuseStep 6433141 = 603107) (by norm_num)
theorem B8577521 : Blo 2257435 8577521 := bstep (se 2 (by rfl) ⟨3216570, by rfl⟩ : syracuseStep 8577521 = 6433141) B6433141
theorem B5718347 : Blo 2257435 5718347 := bstep (se 1 (by rfl) ⟨4288760, by rfl⟩ : syracuseStep 5718347 = 8577521) B8577521
theorem B3812231 : Blo 2257435 3812231 := bstep (se 1 (by rfl) ⟨2859173, by rfl⟩ : syracuseStep 3812231 = 5718347) B5718347
theorem B2541487 : Blo 2257435 2541487 := bstep (se 1 (by rfl) ⟨1906115, by rfl⟩ : syracuseStep 2541487 = 3812231) B3812231
theorem B3388649 : Blo 2257435 3388649 := bstep (se 2 (by rfl) ⟨1270743, by rfl⟩ : syracuseStep 3388649 = 2541487) B2541487
theorem B2259099 : Blo 2257435 2259099 := bstep (se 1 (by rfl) ⟨1694324, by rfl⟩ : syracuseStep 2259099 = 3388649) B3388649
theorem B7336037 : Blo 2257435 7336037 := bbase (se 4 (by rfl) ⟨687753, by rfl⟩ : syracuseStep 7336037 = 1375507) (by norm_num)
theorem B4890691 : Blo 2257435 4890691 := bstep (se 1 (by rfl) ⟨3668018, by rfl⟩ : syracuseStep 4890691 = 7336037) B7336037
theorem B26083685 : Blo 2257435 26083685 := bstep (se 4 (by rfl) ⟨2445345, by rfl⟩ : syracuseStep 26083685 = 4890691) B4890691
theorem B69556493 : Blo 2257435 69556493 := bstep (se 3 (by rfl) ⟨13041842, by rfl⟩ : syracuseStep 69556493 = 26083685) B26083685
theorem B185483981 : Blo 2257435 185483981 := bstep (se 3 (by rfl) ⟨34778246, by rfl⟩ : syracuseStep 185483981 = 69556493) B69556493
theorem B123655987 : Blo 2257435 123655987 := bstep (se 1 (by rfl) ⟨92741990, by rfl⟩ : syracuseStep 123655987 = 185483981) B185483981
theorem B164874649 : Blo 2257435 164874649 := bstep (se 2 (by rfl) ⟨61827993, by rfl⟩ : syracuseStep 164874649 = 123655987) B123655987
theorem B219832865 : Blo 2257435 219832865 := bstep (se 2 (by rfl) ⟨82437324, by rfl⟩ : syracuseStep 219832865 = 164874649) B164874649
theorem B146555243 : Blo 2257435 146555243 := bstep (se 1 (by rfl) ⟨109916432, by rfl⟩ : syracuseStep 146555243 = 219832865) B219832865
theorem B97703495 : Blo 2257435 97703495 := bstep (se 1 (by rfl) ⟨73277621, by rfl⟩ : syracuseStep 97703495 = 146555243) B146555243
theorem B65135663 : Blo 2257435 65135663 := bstep (se 1 (by rfl) ⟨48851747, by rfl⟩ : syracuseStep 65135663 = 97703495) B97703495
theorem B43423775 : Blo 2257435 43423775 := bstep (se 1 (by rfl) ⟨32567831, by rfl⟩ : syracuseStep 43423775 = 65135663) B65135663
theorem B28949183 : Blo 2257435 28949183 := bstep (se 1 (by rfl) ⟨21711887, by rfl⟩ : syracuseStep 28949183 = 43423775) B43423775
theorem B19299455 : Blo 2257435 19299455 := bstep (se 1 (by rfl) ⟨14474591, by rfl⟩ : syracuseStep 19299455 = 28949183) B28949183
theorem B12866303 : Blo 2257435 12866303 := bstep (se 1 (by rfl) ⟨9649727, by rfl⟩ : syracuseStep 12866303 = 19299455) B19299455
theorem B8577535 : Blo 2257435 8577535 := bstep (se 1 (by rfl) ⟨6433151, by rfl⟩ : syracuseStep 8577535 = 12866303) B12866303
theorem B11436713 : Blo 2257435 11436713 := bstep (se 2 (by rfl) ⟨4288767, by rfl⟩ : syracuseStep 11436713 = 8577535) B8577535
theorem B7624475 : Blo 2257435 7624475 := bstep (se 1 (by rfl) ⟨5718356, by rfl⟩ : syracuseStep 7624475 = 11436713) B11436713
theorem B5082983 : Blo 2257435 5082983 := bstep (se 1 (by rfl) ⟨3812237, by rfl⟩ : syracuseStep 5082983 = 7624475) B7624475
theorem B3388655 : Blo 2257435 3388655 := bstep (se 1 (by rfl) ⟨2541491, by rfl⟩ : syracuseStep 3388655 = 5082983) B5082983
theorem B2259103 : Blo 2257435 2259103 := bstep (se 1 (by rfl) ⟨1694327, by rfl⟩ : syracuseStep 2259103 = 3388655) B3388655
theorem B3388661 : Blo 2257435 3388661 := bbase (se 5 (by rfl) ⟨158843, by rfl⟩ : syracuseStep 3388661 = 317687) (by norm_num)
theorem B2259107 : Blo 2257435 2259107 := bstep (se 1 (by rfl) ⟨1694330, by rfl⟩ : syracuseStep 2259107 = 3388661) B3388661
theorem B14474645 : Blo 2257435 14474645 := bbase (se 6 (by rfl) ⟨339249, by rfl⟩ : syracuseStep 14474645 = 678499) (by norm_num)
theorem B9649763 : Blo 2257435 9649763 := bstep (se 1 (by rfl) ⟨7237322, by rfl⟩ : syracuseStep 9649763 = 14474645) B14474645
theorem B6433175 : Blo 2257435 6433175 := bstep (se 1 (by rfl) ⟨4824881, by rfl⟩ : syracuseStep 6433175 = 9649763) B9649763
theorem B4288783 : Blo 2257435 4288783 := bstep (se 1 (by rfl) ⟨3216587, by rfl⟩ : syracuseStep 4288783 = 6433175) B6433175
theorem B5718377 : Blo 2257435 5718377 := bstep (se 2 (by rfl) ⟨2144391, by rfl⟩ : syracuseStep 5718377 = 4288783) B4288783
theorem B3812251 : Blo 2257435 3812251 := bstep (se 1 (by rfl) ⟨2859188, by rfl⟩ : syracuseStep 3812251 = 5718377) B5718377
theorem B5083001 : Blo 2257435 5083001 := bstep (se 2 (by rfl) ⟨1906125, by rfl⟩ : syracuseStep 5083001 = 3812251) B3812251
theorem B3388667 : Blo 2257435 3388667 := bstep (se 1 (by rfl) ⟨2541500, by rfl⟩ : syracuseStep 3388667 = 5083001) B5083001
theorem B2259111 : Blo 2257435 2259111 := bstep (se 1 (by rfl) ⟨1694333, by rfl⟩ : syracuseStep 2259111 = 3388667) B3388667
theorem B2541505 : Blo 2257435 2541505 := bbase (se 2 (by rfl) ⟨953064, by rfl⟩ : syracuseStep 2541505 = 1906129) (by norm_num)
theorem B3388673 : Blo 2257435 3388673 := bstep (se 2 (by rfl) ⟨1270752, by rfl⟩ : syracuseStep 3388673 = 2541505) B2541505
theorem B2259115 : Blo 2257435 2259115 := bstep (se 1 (by rfl) ⟨1694336, by rfl⟩ : syracuseStep 2259115 = 3388673) B3388673
theorem B5718397 : Blo 2257435 5718397 := bbase (se 3 (by rfl) ⟨1072199, by rfl⟩ : syracuseStep 5718397 = 2144399) (by norm_num)
theorem B7624529 : Blo 2257435 7624529 := bstep (se 2 (by rfl) ⟨2859198, by rfl⟩ : syracuseStep 7624529 = 5718397) B5718397
theorem B5083019 : Blo 2257435 5083019 := bstep (se 1 (by rfl) ⟨3812264, by rfl⟩ : syracuseStep 5083019 = 7624529) B7624529
theorem B3388679 : Blo 2257435 3388679 := bstep (se 1 (by rfl) ⟨2541509, by rfl⟩ : syracuseStep 3388679 = 5083019) B5083019
theorem B2259119 : Blo 2257435 2259119 := bstep (se 1 (by rfl) ⟨1694339, by rfl⟩ : syracuseStep 2259119 = 3388679) B3388679
theorem B3388685 : Blo 2257435 3388685 := bbase (se 3 (by rfl) ⟨635378, by rfl⟩ : syracuseStep 3388685 = 1270757) (by norm_num)
theorem B2259123 : Blo 2257435 2259123 := bstep (se 1 (by rfl) ⟨1694342, by rfl⟩ : syracuseStep 2259123 = 3388685) B3388685
theorem B5083037 : Blo 2257435 5083037 := bbase (se 3 (by rfl) ⟨953069, by rfl⟩ : syracuseStep 5083037 = 1906139) (by norm_num)
theorem B3388691 : Blo 2257435 3388691 := bstep (se 1 (by rfl) ⟨2541518, by rfl⟩ : syracuseStep 3388691 = 5083037) B5083037
theorem B2259127 : Blo 2257435 2259127 := bstep (se 1 (by rfl) ⟨1694345, by rfl⟩ : syracuseStep 2259127 = 3388691) B3388691
theorem B3812285 : Blo 2257435 3812285 := bbase (se 3 (by rfl) ⟨714803, by rfl⟩ : syracuseStep 3812285 = 1429607) (by norm_num)
theorem B2541523 : Blo 2257435 2541523 := bstep (se 1 (by rfl) ⟨1906142, by rfl⟩ : syracuseStep 2541523 = 3812285) B3812285
theorem B3388697 : Blo 2257435 3388697 := bstep (se 2 (by rfl) ⟨1270761, by rfl⟩ : syracuseStep 3388697 = 2541523) B2541523
theorem B2259131 : Blo 2257435 2259131 := bstep (se 1 (by rfl) ⟨1694348, by rfl⟩ : syracuseStep 2259131 = 3388697) B3388697
theorem B12866485 : Blo 2257435 12866485 := bbase (se 5 (by rfl) ⟨603116, by rfl⟩ : syracuseStep 12866485 = 1206233) (by norm_num)
theorem B17155313 : Blo 2257435 17155313 := bstep (se 2 (by rfl) ⟨6433242, by rfl⟩ : syracuseStep 17155313 = 12866485) B12866485
theorem B11436875 : Blo 2257435 11436875 := bstep (se 1 (by rfl) ⟨8577656, by rfl⟩ : syracuseStep 11436875 = 17155313) B17155313
theorem B7624583 : Blo 2257435 7624583 := bstep (se 1 (by rfl) ⟨5718437, by rfl⟩ : syracuseStep 7624583 = 11436875) B11436875
theorem B5083055 : Blo 2257435 5083055 := bstep (se 1 (by rfl) ⟨3812291, by rfl⟩ : syracuseStep 5083055 = 7624583) B7624583
theorem B3388703 : Blo 2257435 3388703 := bstep (se 1 (by rfl) ⟨2541527, by rfl⟩ : syracuseStep 3388703 = 5083055) B5083055
theorem B2259135 : Blo 2257435 2259135 := bstep (se 1 (by rfl) ⟨1694351, by rfl⟩ : syracuseStep 2259135 = 3388703) B3388703
theorem B3388709 : Blo 2257435 3388709 := bbase (se 4 (by rfl) ⟨317691, by rfl⟩ : syracuseStep 3388709 = 635383) (by norm_num)
theorem B2259139 : Blo 2257435 2259139 := bstep (se 1 (by rfl) ⟨1694354, by rfl⟩ : syracuseStep 2259139 = 3388709) B3388709
theorem B2859229 : Blo 2257435 2859229 := bbase (se 3 (by rfl) ⟨536105, by rfl⟩ : syracuseStep 2859229 = 1072211) (by norm_num)
theorem B3812305 : Blo 2257435 3812305 := bstep (se 2 (by rfl) ⟨1429614, by rfl⟩ : syracuseStep 3812305 = 2859229) B2859229
theorem B5083073 : Blo 2257435 5083073 := bstep (se 2 (by rfl) ⟨1906152, by rfl⟩ : syracuseStep 5083073 = 3812305) B3812305
theorem B3388715 : Blo 2257435 3388715 := bstep (se 1 (by rfl) ⟨2541536, by rfl⟩ : syracuseStep 3388715 = 5083073) B5083073
theorem B2259143 : Blo 2257435 2259143 := bstep (se 1 (by rfl) ⟨1694357, by rfl⟩ : syracuseStep 2259143 = 3388715) B3388715
theorem B2541541 : Blo 2257435 2541541 := bbase (se 4 (by rfl) ⟨238269, by rfl⟩ : syracuseStep 2541541 = 476539) (by norm_num)
theorem B3388721 : Blo 2257435 3388721 := bstep (se 2 (by rfl) ⟨1270770, by rfl⟩ : syracuseStep 3388721 = 2541541) B2541541
theorem B2259147 : Blo 2257435 2259147 := bstep (se 1 (by rfl) ⟨1694360, by rfl⟩ : syracuseStep 2259147 = 3388721) B3388721
theorem B8142133 : Blo 2257435 8142133 := bbase (se 5 (by rfl) ⟨381662, by rfl⟩ : syracuseStep 8142133 = 763325) (by norm_num)
theorem B10856177 : Blo 2257435 10856177 := bstep (se 2 (by rfl) ⟨4071066, by rfl⟩ : syracuseStep 10856177 = 8142133) B8142133
theorem B7237451 : Blo 2257435 7237451 := bstep (se 1 (by rfl) ⟨5428088, by rfl⟩ : syracuseStep 7237451 = 10856177) B10856177
theorem B4824967 : Blo 2257435 4824967 := bstep (se 1 (by rfl) ⟨3618725, by rfl⟩ : syracuseStep 4824967 = 7237451) B7237451
theorem B6433289 : Blo 2257435 6433289 := bstep (se 2 (by rfl) ⟨2412483, by rfl⟩ : syracuseStep 6433289 = 4824967) B4824967
theorem B4288859 : Blo 2257435 4288859 := bstep (se 1 (by rfl) ⟨3216644, by rfl⟩ : syracuseStep 4288859 = 6433289) B6433289
theorem B2859239 : Blo 2257435 2859239 := bstep (se 1 (by rfl) ⟨2144429, by rfl⟩ : syracuseStep 2859239 = 4288859) B4288859
theorem B7624637 : Blo 2257435 7624637 := bstep (se 3 (by rfl) ⟨1429619, by rfl⟩ : syracuseStep 7624637 = 2859239) B2859239
theorem B5083091 : Blo 2257435 5083091 := bstep (se 1 (by rfl) ⟨3812318, by rfl⟩ : syracuseStep 5083091 = 7624637) B7624637
theorem B3388727 : Blo 2257435 3388727 := bstep (se 1 (by rfl) ⟨2541545, by rfl⟩ : syracuseStep 3388727 = 5083091) B5083091
theorem B2259151 : Blo 2257435 2259151 := bstep (se 1 (by rfl) ⟨1694363, by rfl⟩ : syracuseStep 2259151 = 3388727) B3388727
theorem B3388733 : Blo 2257435 3388733 := bbase (se 3 (by rfl) ⟨635387, by rfl⟩ : syracuseStep 3388733 = 1270775) (by norm_num)
theorem B2259155 : Blo 2257435 2259155 := bstep (se 1 (by rfl) ⟨1694366, by rfl⟩ : syracuseStep 2259155 = 3388733) B3388733
theorem B5083109 : Blo 2257435 5083109 := bbase (se 4 (by rfl) ⟨476541, by rfl⟩ : syracuseStep 5083109 = 953083) (by norm_num)
theorem B3388739 : Blo 2257435 3388739 := bstep (se 1 (by rfl) ⟨2541554, by rfl⟩ : syracuseStep 3388739 = 5083109) B5083109
theorem B2259159 : Blo 2257435 2259159 := bstep (se 1 (by rfl) ⟨1694369, by rfl⟩ : syracuseStep 2259159 = 3388739) B3388739
theorem B5718509 : Blo 2257435 5718509 := bbase (se 3 (by rfl) ⟨1072220, by rfl⟩ : syracuseStep 5718509 = 2144441) (by norm_num)
theorem B3812339 : Blo 2257435 3812339 := bstep (se 1 (by rfl) ⟨2859254, by rfl⟩ : syracuseStep 3812339 = 5718509) B5718509
theorem B2541559 : Blo 2257435 2541559 := bstep (se 1 (by rfl) ⟨1906169, by rfl⟩ : syracuseStep 2541559 = 3812339) B3812339
theorem B3388745 : Blo 2257435 3388745 := bstep (se 2 (by rfl) ⟨1270779, by rfl⟩ : syracuseStep 3388745 = 2541559) B2541559
theorem B2259163 : Blo 2257435 2259163 := bstep (se 1 (by rfl) ⟨1694372, by rfl⟩ : syracuseStep 2259163 = 3388745) B3388745
theorem B5796541 : Blo 2257435 5796541 := bbase (se 3 (by rfl) ⟨1086851, by rfl⟩ : syracuseStep 5796541 = 2173703) (by norm_num)
theorem B30914885 : Blo 2257435 30914885 := bstep (se 4 (by rfl) ⟨2898270, by rfl⟩ : syracuseStep 30914885 = 5796541) B5796541
theorem B20609923 : Blo 2257435 20609923 := bstep (se 1 (by rfl) ⟨15457442, by rfl⟩ : syracuseStep 20609923 = 30914885) B30914885
theorem B27479897 : Blo 2257435 27479897 := bstep (se 2 (by rfl) ⟨10304961, by rfl⟩ : syracuseStep 27479897 = 20609923) B20609923
theorem B18319931 : Blo 2257435 18319931 := bstep (se 1 (by rfl) ⟨13739948, by rfl⟩ : syracuseStep 18319931 = 27479897) B27479897
theorem B12213287 : Blo 2257435 12213287 := bstep (se 1 (by rfl) ⟨9159965, by rfl⟩ : syracuseStep 12213287 = 18319931) B18319931
theorem B8142191 : Blo 2257435 8142191 := bstep (se 1 (by rfl) ⟨6106643, by rfl⟩ : syracuseStep 8142191 = 12213287) B12213287
theorem B5428127 : Blo 2257435 5428127 := bstep (se 1 (by rfl) ⟨4071095, by rfl⟩ : syracuseStep 5428127 = 8142191) B8142191
theorem B3618751 : Blo 2257435 3618751 := bstep (se 1 (by rfl) ⟨2714063, by rfl⟩ : syracuseStep 3618751 = 5428127) B5428127
theorem B4825001 : Blo 2257435 4825001 := bstep (se 2 (by rfl) ⟨1809375, by rfl⟩ : syracuseStep 4825001 = 3618751) B3618751
theorem B3216667 : Blo 2257435 3216667 := bstep (se 1 (by rfl) ⟨2412500, by rfl⟩ : syracuseStep 3216667 = 4825001) B4825001
theorem B4288889 : Blo 2257435 4288889 := bstep (se 2 (by rfl) ⟨1608333, by rfl⟩ : syracuseStep 4288889 = 3216667) B3216667
theorem B11437037 : Blo 2257435 11437037 := bstep (se 3 (by rfl) ⟨2144444, by rfl⟩ : syracuseStep 11437037 = 4288889) B4288889
theorem B7624691 : Blo 2257435 7624691 := bstep (se 1 (by rfl) ⟨5718518, by rfl⟩ : syracuseStep 7624691 = 11437037) B11437037
theorem B5083127 : Blo 2257435 5083127 := bstep (se 1 (by rfl) ⟨3812345, by rfl⟩ : syracuseStep 5083127 = 7624691) B7624691
theorem B3388751 : Blo 2257435 3388751 := bstep (se 1 (by rfl) ⟨2541563, by rfl⟩ : syracuseStep 3388751 = 5083127) B5083127
theorem B2259167 : Blo 2257435 2259167 := bstep (se 1 (by rfl) ⟨1694375, by rfl⟩ : syracuseStep 2259167 = 3388751) B3388751
theorem B3388757 : Blo 2257435 3388757 := bbase (se 13 (by rfl) ⟨620, by rfl⟩ : syracuseStep 3388757 = 1241) (by norm_num)
theorem B2259171 : Blo 2257435 2259171 := bstep (se 1 (by rfl) ⟨1694378, by rfl⟩ : syracuseStep 2259171 = 3388757) B3388757
theorem B2412509 : Blo 2257435 2412509 := bbase (se 3 (by rfl) ⟨452345, by rfl⟩ : syracuseStep 2412509 = 904691) (by norm_num)
theorem B6433357 : Blo 2257435 6433357 := bstep (se 3 (by rfl) ⟨1206254, by rfl⟩ : syracuseStep 6433357 = 2412509) B2412509
theorem B8577809 : Blo 2257435 8577809 := bstep (se 2 (by rfl) ⟨3216678, by rfl⟩ : syracuseStep 8577809 = 6433357) B6433357
theorem B5718539 : Blo 2257435 5718539 := bstep (se 1 (by rfl) ⟨4288904, by rfl⟩ : syracuseStep 5718539 = 8577809) B8577809
theorem B3812359 : Blo 2257435 3812359 := bstep (se 1 (by rfl) ⟨2859269, by rfl⟩ : syracuseStep 3812359 = 5718539) B5718539
theorem B5083145 : Blo 2257435 5083145 := bstep (se 2 (by rfl) ⟨1906179, by rfl⟩ : syracuseStep 5083145 = 3812359) B3812359
theorem B3388763 : Blo 2257435 3388763 := bstep (se 1 (by rfl) ⟨2541572, by rfl⟩ : syracuseStep 3388763 = 5083145) B5083145
theorem B2259175 : Blo 2257435 2259175 := bstep (se 1 (by rfl) ⟨1694381, by rfl⟩ : syracuseStep 2259175 = 3388763) B3388763
theorem B2541577 : Blo 2257435 2541577 := bbase (se 2 (by rfl) ⟨953091, by rfl⟩ : syracuseStep 2541577 = 1906183) (by norm_num)
theorem B3388769 : Blo 2257435 3388769 := bstep (se 2 (by rfl) ⟨1270788, by rfl⟩ : syracuseStep 3388769 = 2541577) B2541577
theorem B2259179 : Blo 2257435 2259179 := bstep (se 1 (by rfl) ⟨1694384, by rfl⟩ : syracuseStep 2259179 = 3388769) B3388769
theorem B5152517 : Blo 2257435 5152517 := bbase (se 4 (by rfl) ⟨483048, by rfl⟩ : syracuseStep 5152517 = 966097) (by norm_num)
theorem B3435011 : Blo 2257435 3435011 := bstep (se 1 (by rfl) ⟨2576258, by rfl⟩ : syracuseStep 3435011 = 5152517) B5152517
theorem B2290007 : Blo 2257435 2290007 := bstep (se 1 (by rfl) ⟨1717505, by rfl⟩ : syracuseStep 2290007 = 3435011) B3435011
theorem B6106685 : Blo 2257435 6106685 := bstep (se 3 (by rfl) ⟨1145003, by rfl⟩ : syracuseStep 6106685 = 2290007) B2290007
theorem B16284493 : Blo 2257435 16284493 := bstep (se 3 (by rfl) ⟨3053342, by rfl⟩ : syracuseStep 16284493 = 6106685) B6106685
theorem B21712657 : Blo 2257435 21712657 := bstep (se 2 (by rfl) ⟨8142246, by rfl⟩ : syracuseStep 21712657 = 16284493) B16284493
theorem B28950209 : Blo 2257435 28950209 := bstep (se 2 (by rfl) ⟨10856328, by rfl⟩ : syracuseStep 28950209 = 21712657) B21712657
theorem B19300139 : Blo 2257435 19300139 := bstep (se 1 (by rfl) ⟨14475104, by rfl⟩ : syracuseStep 19300139 = 28950209) B28950209
theorem B12866759 : Blo 2257435 12866759 := bstep (se 1 (by rfl) ⟨9650069, by rfl⟩ : syracuseStep 12866759 = 19300139) B19300139
theorem B8577839 : Blo 2257435 8577839 := bstep (se 1 (by rfl) ⟨6433379, by rfl⟩ : syracuseStep 8577839 = 12866759) B12866759
theorem B5718559 : Blo 2257435 5718559 := bstep (se 1 (by rfl) ⟨4288919, by rfl⟩ : syracuseStep 5718559 = 8577839) B8577839
theorem B7624745 : Blo 2257435 7624745 := bstep (se 2 (by rfl) ⟨2859279, by rfl⟩ : syracuseStep 7624745 = 5718559) B5718559
theorem B5083163 : Blo 2257435 5083163 := bstep (se 1 (by rfl) ⟨3812372, by rfl⟩ : syracuseStep 5083163 = 7624745) B7624745
theorem B3388775 : Blo 2257435 3388775 := bstep (se 1 (by rfl) ⟨2541581, by rfl⟩ : syracuseStep 3388775 = 5083163) B5083163
theorem B2259183 : Blo 2257435 2259183 := bstep (se 1 (by rfl) ⟨1694387, by rfl⟩ : syracuseStep 2259183 = 3388775) B3388775
theorem B3388781 : Blo 2257435 3388781 := bbase (se 3 (by rfl) ⟨635396, by rfl⟩ : syracuseStep 3388781 = 1270793) (by norm_num)
theorem B2259187 : Blo 2257435 2259187 := bstep (se 1 (by rfl) ⟨1694390, by rfl⟩ : syracuseStep 2259187 = 3388781) B3388781
theorem B5083181 : Blo 2257435 5083181 := bbase (se 3 (by rfl) ⟨953096, by rfl⟩ : syracuseStep 5083181 = 1906193) (by norm_num)
theorem B3388787 : Blo 2257435 3388787 := bstep (se 1 (by rfl) ⟨2541590, by rfl⟩ : syracuseStep 3388787 = 5083181) B5083181
theorem B2259191 : Blo 2257435 2259191 := bstep (se 1 (by rfl) ⟨1694393, by rfl⟩ : syracuseStep 2259191 = 3388787) B3388787
theorem B10856389 : Blo 2257435 10856389 := bbase (se 4 (by rfl) ⟨1017786, by rfl⟩ : syracuseStep 10856389 = 2035573) (by norm_num)
theorem B14475185 : Blo 2257435 14475185 := bstep (se 2 (by rfl) ⟨5428194, by rfl⟩ : syracuseStep 14475185 = 10856389) B10856389
theorem B9650123 : Blo 2257435 9650123 := bstep (se 1 (by rfl) ⟨7237592, by rfl⟩ : syracuseStep 9650123 = 14475185) B14475185
theorem B6433415 : Blo 2257435 6433415 := bstep (se 1 (by rfl) ⟨4825061, by rfl⟩ : syracuseStep 6433415 = 9650123) B9650123
theorem B4288943 : Blo 2257435 4288943 := bstep (se 1 (by rfl) ⟨3216707, by rfl⟩ : syracuseStep 4288943 = 6433415) B6433415
theorem B2859295 : Blo 2257435 2859295 := bstep (se 1 (by rfl) ⟨2144471, by rfl⟩ : syracuseStep 2859295 = 4288943) B4288943
theorem B3812393 : Blo 2257435 3812393 := bstep (se 2 (by rfl) ⟨1429647, by rfl⟩ : syracuseStep 3812393 = 2859295) B2859295
theorem B2541595 : Blo 2257435 2541595 := bstep (se 1 (by rfl) ⟨1906196, by rfl⟩ : syracuseStep 2541595 = 3812393) B3812393
theorem B3388793 : Blo 2257435 3388793 := bstep (se 2 (by rfl) ⟨1270797, by rfl⟩ : syracuseStep 3388793 = 2541595) B2541595
theorem B2259195 : Blo 2257435 2259195 := bstep (se 1 (by rfl) ⟨1694396, by rfl⟩ : syracuseStep 2259195 = 3388793) B3388793
theorem B10856405 : Blo 2257435 10856405 := bbase (se 7 (by rfl) ⟨127223, by rfl⟩ : syracuseStep 10856405 = 254447) (by norm_num)
theorem B7237603 : Blo 2257435 7237603 := bstep (se 1 (by rfl) ⟨5428202, by rfl⟩ : syracuseStep 7237603 = 10856405) B10856405
theorem B38600549 : Blo 2257435 38600549 := bstep (se 4 (by rfl) ⟨3618801, by rfl⟩ : syracuseStep 38600549 = 7237603) B7237603
theorem B25733699 : Blo 2257435 25733699 := bstep (se 1 (by rfl) ⟨19300274, by rfl⟩ : syracuseStep 25733699 = 38600549) B38600549
theorem B17155799 : Blo 2257435 17155799 := bstep (se 1 (by rfl) ⟨12866849, by rfl⟩ : syracuseStep 17155799 = 25733699) B25733699
theorem B11437199 : Blo 2257435 11437199 := bstep (se 1 (by rfl) ⟨8577899, by rfl⟩ : syracuseStep 11437199 = 17155799) B17155799
theorem B7624799 : Blo 2257435 7624799 := bstep (se 1 (by rfl) ⟨5718599, by rfl⟩ : syracuseStep 7624799 = 11437199) B11437199
theorem B5083199 : Blo 2257435 5083199 := bstep (se 1 (by rfl) ⟨3812399, by rfl⟩ : syracuseStep 5083199 = 7624799) B7624799
theorem B3388799 : Blo 2257435 3388799 := bstep (se 1 (by rfl) ⟨2541599, by rfl⟩ : syracuseStep 3388799 = 5083199) B5083199
theorem B2259199 : Blo 2257435 2259199 := bstep (se 1 (by rfl) ⟨1694399, by rfl⟩ : syracuseStep 2259199 = 3388799) B3388799
theorem B3388805 : Blo 2257435 3388805 := bbase (se 4 (by rfl) ⟨317700, by rfl⟩ : syracuseStep 3388805 = 635401) (by norm_num)
theorem B2259203 : Blo 2257435 2259203 := bstep (se 1 (by rfl) ⟨1694402, by rfl⟩ : syracuseStep 2259203 = 3388805) B3388805
theorem B3812413 : Blo 2257435 3812413 := bbase (se 3 (by rfl) ⟨714827, by rfl⟩ : syracuseStep 3812413 = 1429655) (by norm_num)
theorem B5083217 : Blo 2257435 5083217 := bstep (se 2 (by rfl) ⟨1906206, by rfl⟩ : syracuseStep 5083217 = 3812413) B3812413
theorem B3388811 : Blo 2257435 3388811 := bstep (se 1 (by rfl) ⟨2541608, by rfl⟩ : syracuseStep 3388811 = 5083217) B5083217
theorem B2259207 : Blo 2257435 2259207 := bstep (se 1 (by rfl) ⟨1694405, by rfl⟩ : syracuseStep 2259207 = 3388811) B3388811
theorem B2541613 : Blo 2257435 2541613 := bbase (se 3 (by rfl) ⟨476552, by rfl⟩ : syracuseStep 2541613 = 953105) (by norm_num)
theorem B3388817 : Blo 2257435 3388817 := bstep (se 2 (by rfl) ⟨1270806, by rfl⟩ : syracuseStep 3388817 = 2541613) B2541613
theorem B2259211 : Blo 2257435 2259211 := bstep (se 1 (by rfl) ⟨1694408, by rfl⟩ : syracuseStep 2259211 = 3388817) B3388817
theorem B7624853 : Blo 2257435 7624853 := bbase (se 6 (by rfl) ⟨178707, by rfl⟩ : syracuseStep 7624853 = 357415) (by norm_num)
theorem B5083235 : Blo 2257435 5083235 := bstep (se 1 (by rfl) ⟨3812426, by rfl⟩ : syracuseStep 5083235 = 7624853) B7624853
theorem B3388823 : Blo 2257435 3388823 := bstep (se 1 (by rfl) ⟨2541617, by rfl⟩ : syracuseStep 3388823 = 5083235) B5083235
theorem B2259215 : Blo 2257435 2259215 := bstep (se 1 (by rfl) ⟨1694411, by rfl⟩ : syracuseStep 2259215 = 3388823) B3388823
theorem B3388829 : Blo 2257435 3388829 := bbase (se 3 (by rfl) ⟨635405, by rfl⟩ : syracuseStep 3388829 = 1270811) (by norm_num)
theorem B2259219 : Blo 2257435 2259219 := bstep (se 1 (by rfl) ⟨1694414, by rfl⟩ : syracuseStep 2259219 = 3388829) B3388829
theorem B5083253 : Blo 2257435 5083253 := bbase (se 5 (by rfl) ⟨238277, by rfl⟩ : syracuseStep 5083253 = 476555) (by norm_num)
theorem B3388835 : Blo 2257435 3388835 := bstep (se 1 (by rfl) ⟨2541626, by rfl⟩ : syracuseStep 3388835 = 5083253) B5083253
theorem B2259223 : Blo 2257435 2259223 := bstep (se 1 (by rfl) ⟨1694417, by rfl⟩ : syracuseStep 2259223 = 3388835) B3388835
theorem B2445481 : Blo 2257435 2445481 := bbase (se 2 (by rfl) ⟨917055, by rfl⟩ : syracuseStep 2445481 = 1834111) (by norm_num)
theorem B13042565 : Blo 2257435 13042565 := bstep (se 4 (by rfl) ⟨1222740, by rfl⟩ : syracuseStep 13042565 = 2445481) B2445481
theorem B8695043 : Blo 2257435 8695043 := bstep (se 1 (by rfl) ⟨6521282, by rfl⟩ : syracuseStep 8695043 = 13042565) B13042565
theorem B5796695 : Blo 2257435 5796695 := bstep (se 1 (by rfl) ⟨4347521, by rfl⟩ : syracuseStep 5796695 = 8695043) B8695043
theorem B15457853 : Blo 2257435 15457853 := bstep (se 3 (by rfl) ⟨2898347, by rfl⟩ : syracuseStep 15457853 = 5796695) B5796695
theorem B10305235 : Blo 2257435 10305235 := bstep (se 1 (by rfl) ⟨7728926, by rfl⟩ : syracuseStep 10305235 = 15457853) B15457853
theorem B13740313 : Blo 2257435 13740313 := bstep (se 2 (by rfl) ⟨5152617, by rfl⟩ : syracuseStep 13740313 = 10305235) B10305235
theorem B18320417 : Blo 2257435 18320417 := bstep (se 2 (by rfl) ⟨6870156, by rfl⟩ : syracuseStep 18320417 = 13740313) B13740313
theorem B12213611 : Blo 2257435 12213611 := bstep (se 1 (by rfl) ⟨9160208, by rfl⟩ : syracuseStep 12213611 = 18320417) B18320417
theorem B8142407 : Blo 2257435 8142407 := bstep (se 1 (by rfl) ⟨6106805, by rfl⟩ : syracuseStep 8142407 = 12213611) B12213611
theorem B5428271 : Blo 2257435 5428271 := bstep (se 1 (by rfl) ⟨4071203, by rfl⟩ : syracuseStep 5428271 = 8142407) B8142407
theorem B3618847 : Blo 2257435 3618847 := bstep (se 1 (by rfl) ⟨2714135, by rfl⟩ : syracuseStep 3618847 = 5428271) B5428271
theorem B19300517 : Blo 2257435 19300517 := bstep (se 4 (by rfl) ⟨1809423, by rfl⟩ : syracuseStep 19300517 = 3618847) B3618847
theorem B12867011 : Blo 2257435 12867011 := bstep (se 1 (by rfl) ⟨9650258, by rfl⟩ : syracuseStep 12867011 = 19300517) B19300517
theorem B8578007 : Blo 2257435 8578007 := bstep (se 1 (by rfl) ⟨6433505, by rfl⟩ : syracuseStep 8578007 = 12867011) B12867011
theorem B5718671 : Blo 2257435 5718671 := bstep (se 1 (by rfl) ⟨4289003, by rfl⟩ : syracuseStep 5718671 = 8578007) B8578007
theorem B3812447 : Blo 2257435 3812447 := bstep (se 1 (by rfl) ⟨2859335, by rfl⟩ : syracuseStep 3812447 = 5718671) B5718671
theorem B2541631 : Blo 2257435 2541631 := bstep (se 1 (by rfl) ⟨1906223, by rfl⟩ : syracuseStep 2541631 = 3812447) B3812447
theorem B3388841 : Blo 2257435 3388841 := bstep (se 2 (by rfl) ⟨1270815, by rfl⟩ : syracuseStep 3388841 = 2541631) B2541631
theorem B2259227 : Blo 2257435 2259227 := bstep (se 1 (by rfl) ⟨1694420, by rfl⟩ : syracuseStep 2259227 = 3388841) B3388841
theorem B8578021 : Blo 2257435 8578021 := bbase (se 4 (by rfl) ⟨804189, by rfl⟩ : syracuseStep 8578021 = 1608379) (by norm_num)
theorem B11437361 : Blo 2257435 11437361 := bstep (se 2 (by rfl) ⟨4289010, by rfl⟩ : syracuseStep 11437361 = 8578021) B8578021
theorem B7624907 : Blo 2257435 7624907 := bstep (se 1 (by rfl) ⟨5718680, by rfl⟩ : syracuseStep 7624907 = 11437361) B11437361
theorem B5083271 : Blo 2257435 5083271 := bstep (se 1 (by rfl) ⟨3812453, by rfl⟩ : syracuseStep 5083271 = 7624907) B7624907
theorem B3388847 : Blo 2257435 3388847 := bstep (se 1 (by rfl) ⟨2541635, by rfl⟩ : syracuseStep 3388847 = 5083271) B5083271
theorem B2259231 : Blo 2257435 2259231 := bstep (se 1 (by rfl) ⟨1694423, by rfl⟩ : syracuseStep 2259231 = 3388847) B3388847
theorem B3388853 : Blo 2257435 3388853 := bbase (se 5 (by rfl) ⟨158852, by rfl⟩ : syracuseStep 3388853 = 317705) (by norm_num)
theorem B2259235 : Blo 2257435 2259235 := bstep (se 1 (by rfl) ⟨1694426, by rfl⟩ : syracuseStep 2259235 = 3388853) B3388853
theorem B5718701 : Blo 2257435 5718701 := bbase (se 3 (by rfl) ⟨1072256, by rfl⟩ : syracuseStep 5718701 = 2144513) (by norm_num)
theorem B3812467 : Blo 2257435 3812467 := bstep (se 1 (by rfl) ⟨2859350, by rfl⟩ : syracuseStep 3812467 = 5718701) B5718701
theorem B5083289 : Blo 2257435 5083289 := bstep (se 2 (by rfl) ⟨1906233, by rfl⟩ : syracuseStep 5083289 = 3812467) B3812467
theorem B3388859 : Blo 2257435 3388859 := bstep (se 1 (by rfl) ⟨2541644, by rfl⟩ : syracuseStep 3388859 = 5083289) B5083289
theorem B2259239 : Blo 2257435 2259239 := bstep (se 1 (by rfl) ⟨1694429, by rfl⟩ : syracuseStep 2259239 = 3388859) B3388859
theorem B2541649 : Blo 2257435 2541649 := bbase (se 2 (by rfl) ⟨953118, by rfl⟩ : syracuseStep 2541649 = 1906237) (by norm_num)
theorem B3388865 : Blo 2257435 3388865 := bstep (se 2 (by rfl) ⟨1270824, by rfl⟩ : syracuseStep 3388865 = 2541649) B2541649
theorem B2259243 : Blo 2257435 2259243 := bstep (se 1 (by rfl) ⟨1694432, by rfl⟩ : syracuseStep 2259243 = 3388865) B3388865
theorem B3216781 : Blo 2257435 3216781 := bbase (se 3 (by rfl) ⟨603146, by rfl⟩ : syracuseStep 3216781 = 1206293) (by norm_num)
theorem B4289041 : Blo 2257435 4289041 := bstep (se 2 (by rfl) ⟨1608390, by rfl⟩ : syracuseStep 4289041 = 3216781) B3216781
theorem B5718721 : Blo 2257435 5718721 := bstep (se 2 (by rfl) ⟨2144520, by rfl⟩ : syracuseStep 5718721 = 4289041) B4289041
theorem B7624961 : Blo 2257435 7624961 := bstep (se 2 (by rfl) ⟨2859360, by rfl⟩ : syracuseStep 7624961 = 5718721) B5718721
theorem B5083307 : Blo 2257435 5083307 := bstep (se 1 (by rfl) ⟨3812480, by rfl⟩ : syracuseStep 5083307 = 7624961) B7624961
theorem B3388871 : Blo 2257435 3388871 := bstep (se 1 (by rfl) ⟨2541653, by rfl⟩ : syracuseStep 3388871 = 5083307) B5083307
theorem B2259247 : Blo 2257435 2259247 := bstep (se 1 (by rfl) ⟨1694435, by rfl⟩ : syracuseStep 2259247 = 3388871) B3388871
theorem B3388877 : Blo 2257435 3388877 := bbase (se 3 (by rfl) ⟨635414, by rfl⟩ : syracuseStep 3388877 = 1270829) (by norm_num)
theorem B2259251 : Blo 2257435 2259251 := bstep (se 1 (by rfl) ⟨1694438, by rfl⟩ : syracuseStep 2259251 = 3388877) B3388877
theorem B5083325 : Blo 2257435 5083325 := bbase (se 3 (by rfl) ⟨953123, by rfl⟩ : syracuseStep 5083325 = 1906247) (by norm_num)
theorem B3388883 : Blo 2257435 3388883 := bstep (se 1 (by rfl) ⟨2541662, by rfl⟩ : syracuseStep 3388883 = 5083325) B5083325
theorem B2259255 : Blo 2257435 2259255 := bstep (se 1 (by rfl) ⟨1694441, by rfl⟩ : syracuseStep 2259255 = 3388883) B3388883
theorem B3812501 : Blo 2257435 3812501 := bbase (se 6 (by rfl) ⟨89355, by rfl⟩ : syracuseStep 3812501 = 178711) (by norm_num)
theorem B2541667 : Blo 2257435 2541667 := bstep (se 1 (by rfl) ⟨1906250, by rfl⟩ : syracuseStep 2541667 = 3812501) B3812501
theorem B3388889 : Blo 2257435 3388889 := bstep (se 2 (by rfl) ⟨1270833, by rfl⟩ : syracuseStep 3388889 = 2541667) B2541667
theorem B2259259 : Blo 2257435 2259259 := bstep (se 1 (by rfl) ⟨1694444, by rfl⟩ : syracuseStep 2259259 = 3388889) B3388889
theorem B10305397 : Blo 2257435 10305397 := bbase (se 5 (by rfl) ⟨483065, by rfl⟩ : syracuseStep 10305397 = 966131) (by norm_num)
theorem B13740529 : Blo 2257435 13740529 := bstep (se 2 (by rfl) ⟨5152698, by rfl⟩ : syracuseStep 13740529 = 10305397) B10305397
theorem B18320705 : Blo 2257435 18320705 := bstep (se 2 (by rfl) ⟨6870264, by rfl⟩ : syracuseStep 18320705 = 13740529) B13740529
theorem B12213803 : Blo 2257435 12213803 := bstep (se 1 (by rfl) ⟨9160352, by rfl⟩ : syracuseStep 12213803 = 18320705) B18320705
theorem B8142535 : Blo 2257435 8142535 := bstep (se 1 (by rfl) ⟨6106901, by rfl⟩ : syracuseStep 8142535 = 12213803) B12213803
theorem B10856713 : Blo 2257435 10856713 := bstep (se 2 (by rfl) ⟨4071267, by rfl⟩ : syracuseStep 10856713 = 8142535) B8142535
theorem B14475617 : Blo 2257435 14475617 := bstep (se 2 (by rfl) ⟨5428356, by rfl⟩ : syracuseStep 14475617 = 10856713) B10856713
theorem B9650411 : Blo 2257435 9650411 := bstep (se 1 (by rfl) ⟨7237808, by rfl⟩ : syracuseStep 9650411 = 14475617) B14475617
theorem B6433607 : Blo 2257435 6433607 := bstep (se 1 (by rfl) ⟨4825205, by rfl⟩ : syracuseStep 6433607 = 9650411) B9650411
theorem B17156285 : Blo 2257435 17156285 := bstep (se 3 (by rfl) ⟨3216803, by rfl⟩ : syracuseStep 17156285 = 6433607) B6433607
theorem B11437523 : Blo 2257435 11437523 := bstep (se 1 (by rfl) ⟨8578142, by rfl⟩ : syracuseStep 11437523 = 17156285) B17156285
theorem B7625015 : Blo 2257435 7625015 := bstep (se 1 (by rfl) ⟨5718761, by rfl⟩ : syracuseStep 7625015 = 11437523) B11437523
theorem B5083343 : Blo 2257435 5083343 := bstep (se 1 (by rfl) ⟨3812507, by rfl⟩ : syracuseStep 5083343 = 7625015) B7625015
theorem B3388895 : Blo 2257435 3388895 := bstep (se 1 (by rfl) ⟨2541671, by rfl⟩ : syracuseStep 3388895 = 5083343) B5083343
theorem B2259263 : Blo 2257435 2259263 := bstep (se 1 (by rfl) ⟨1694447, by rfl⟩ : syracuseStep 2259263 = 3388895) B3388895
theorem B3388901 : Blo 2257435 3388901 := bbase (se 4 (by rfl) ⟨317709, by rfl⟩ : syracuseStep 3388901 = 635419) (by norm_num)
theorem B2259267 : Blo 2257435 2259267 := bstep (se 1 (by rfl) ⟨1694450, by rfl⟩ : syracuseStep 2259267 = 3388901) B3388901
theorem B32570261 : Blo 2257435 32570261 := bbase (se 6 (by rfl) ⟨763365, by rfl⟩ : syracuseStep 32570261 = 1526731) (by norm_num)
theorem B21713507 : Blo 2257435 21713507 := bstep (se 1 (by rfl) ⟨16285130, by rfl⟩ : syracuseStep 21713507 = 32570261) B32570261
theorem B14475671 : Blo 2257435 14475671 := bstep (se 1 (by rfl) ⟨10856753, by rfl⟩ : syracuseStep 14475671 = 21713507) B21713507
theorem B9650447 : Blo 2257435 9650447 := bstep (se 1 (by rfl) ⟨7237835, by rfl⟩ : syracuseStep 9650447 = 14475671) B14475671
theorem B6433631 : Blo 2257435 6433631 := bstep (se 1 (by rfl) ⟨4825223, by rfl⟩ : syracuseStep 6433631 = 9650447) B9650447
theorem B4289087 : Blo 2257435 4289087 := bstep (se 1 (by rfl) ⟨3216815, by rfl⟩ : syracuseStep 4289087 = 6433631) B6433631
theorem B2859391 : Blo 2257435 2859391 := bstep (se 1 (by rfl) ⟨2144543, by rfl⟩ : syracuseStep 2859391 = 4289087) B4289087
theorem B3812521 : Blo 2257435 3812521 := bstep (se 2 (by rfl) ⟨1429695, by rfl⟩ : syracuseStep 3812521 = 2859391) B2859391
theorem B5083361 : Blo 2257435 5083361 := bstep (se 2 (by rfl) ⟨1906260, by rfl⟩ : syracuseStep 5083361 = 3812521) B3812521
theorem B3388907 : Blo 2257435 3388907 := bstep (se 1 (by rfl) ⟨2541680, by rfl⟩ : syracuseStep 3388907 = 5083361) B5083361
theorem B2259271 : Blo 2257435 2259271 := bstep (se 1 (by rfl) ⟨1694453, by rfl⟩ : syracuseStep 2259271 = 3388907) B3388907
theorem B2541685 : Blo 2257435 2541685 := bbase (se 5 (by rfl) ⟨119141, by rfl⟩ : syracuseStep 2541685 = 238283) (by norm_num)
theorem B3388913 : Blo 2257435 3388913 := bstep (se 2 (by rfl) ⟨1270842, by rfl⟩ : syracuseStep 3388913 = 2541685) B2541685
theorem B2259275 : Blo 2257435 2259275 := bstep (se 1 (by rfl) ⟨1694456, by rfl⟩ : syracuseStep 2259275 = 3388913) B3388913
theorem B2859401 : Blo 2257435 2859401 := bbase (se 2 (by rfl) ⟨1072275, by rfl⟩ : syracuseStep 2859401 = 2144551) (by norm_num)
theorem B7625069 : Blo 2257435 7625069 := bstep (se 3 (by rfl) ⟨1429700, by rfl⟩ : syracuseStep 7625069 = 2859401) B2859401
theorem B5083379 : Blo 2257435 5083379 := bstep (se 1 (by rfl) ⟨3812534, by rfl⟩ : syracuseStep 5083379 = 7625069) B7625069
theorem B3388919 : Blo 2257435 3388919 := bstep (se 1 (by rfl) ⟨2541689, by rfl⟩ : syracuseStep 3388919 = 5083379) B5083379
theorem B2259279 : Blo 2257435 2259279 := bstep (se 1 (by rfl) ⟨1694459, by rfl⟩ : syracuseStep 2259279 = 3388919) B3388919
theorem B3388925 : Blo 2257435 3388925 := bbase (se 3 (by rfl) ⟨635423, by rfl⟩ : syracuseStep 3388925 = 1270847) (by norm_num)
theorem B2259283 : Blo 2257435 2259283 := bstep (se 1 (by rfl) ⟨1694462, by rfl⟩ : syracuseStep 2259283 = 3388925) B3388925
theorem B5083397 : Blo 2257435 5083397 := bbase (se 4 (by rfl) ⟨476568, by rfl⟩ : syracuseStep 5083397 = 953137) (by norm_num)
theorem B3388931 : Blo 2257435 3388931 := bstep (se 1 (by rfl) ⟨2541698, by rfl⟩ : syracuseStep 3388931 = 5083397) B5083397
theorem B2259287 : Blo 2257435 2259287 := bstep (se 1 (by rfl) ⟨1694465, by rfl⟩ : syracuseStep 2259287 = 3388931) B3388931
theorem B4289125 : Blo 2257435 4289125 := bbase (se 4 (by rfl) ⟨402105, by rfl⟩ : syracuseStep 4289125 = 804211) (by norm_num)
theorem B5718833 : Blo 2257435 5718833 := bstep (se 2 (by rfl) ⟨2144562, by rfl⟩ : syracuseStep 5718833 = 4289125) B4289125
theorem B3812555 : Blo 2257435 3812555 := bstep (se 1 (by rfl) ⟨2859416, by rfl⟩ : syracuseStep 3812555 = 5718833) B5718833
theorem B2541703 : Blo 2257435 2541703 := bstep (se 1 (by rfl) ⟨1906277, by rfl⟩ : syracuseStep 2541703 = 3812555) B3812555
theorem B3388937 : Blo 2257435 3388937 := bstep (se 2 (by rfl) ⟨1270851, by rfl⟩ : syracuseStep 3388937 = 2541703) B2541703
theorem B2259291 : Blo 2257435 2259291 := bstep (se 1 (by rfl) ⟨1694468, by rfl⟩ : syracuseStep 2259291 = 3388937) B3388937
theorem B11437685 : Blo 2257435 11437685 := bbase (se 5 (by rfl) ⟨536141, by rfl⟩ : syracuseStep 11437685 = 1072283) (by norm_num)
theorem B7625123 : Blo 2257435 7625123 := bstep (se 1 (by rfl) ⟨5718842, by rfl⟩ : syracuseStep 7625123 = 11437685) B11437685
theorem B5083415 : Blo 2257435 5083415 := bstep (se 1 (by rfl) ⟨3812561, by rfl⟩ : syracuseStep 5083415 = 7625123) B7625123
theorem B3388943 : Blo 2257435 3388943 := bstep (se 1 (by rfl) ⟨2541707, by rfl⟩ : syracuseStep 3388943 = 5083415) B5083415
theorem B2259295 : Blo 2257435 2259295 := bstep (se 1 (by rfl) ⟨1694471, by rfl⟩ : syracuseStep 2259295 = 3388943) B3388943
theorem B3388949 : Blo 2257435 3388949 := bbase (se 6 (by rfl) ⟨79428, by rfl⟩ : syracuseStep 3388949 = 158857) (by norm_num)
theorem B2259299 : Blo 2257435 2259299 := bstep (se 1 (by rfl) ⟨1694474, by rfl⟩ : syracuseStep 2259299 = 3388949) B3388949
theorem B5428453 : Blo 2257435 5428453 := bbase (se 4 (by rfl) ⟨508917, by rfl⟩ : syracuseStep 5428453 = 1017835) (by norm_num)
theorem B7237937 : Blo 2257435 7237937 := bstep (se 2 (by rfl) ⟨2714226, by rfl⟩ : syracuseStep 7237937 = 5428453) B5428453
theorem B19301165 : Blo 2257435 19301165 := bstep (se 3 (by rfl) ⟨3618968, by rfl⟩ : syracuseStep 19301165 = 7237937) B7237937
theorem B12867443 : Blo 2257435 12867443 := bstep (se 1 (by rfl) ⟨9650582, by rfl⟩ : syracuseStep 12867443 = 19301165) B19301165
theorem B8578295 : Blo 2257435 8578295 := bstep (se 1 (by rfl) ⟨6433721, by rfl⟩ : syracuseStep 8578295 = 12867443) B12867443
theorem B5718863 : Blo 2257435 5718863 := bstep (se 1 (by rfl) ⟨4289147, by rfl⟩ : syracuseStep 5718863 = 8578295) B8578295
theorem B3812575 : Blo 2257435 3812575 := bstep (se 1 (by rfl) ⟨2859431, by rfl⟩ : syracuseStep 3812575 = 5718863) B5718863
theorem B5083433 : Blo 2257435 5083433 := bstep (se 2 (by rfl) ⟨1906287, by rfl⟩ : syracuseStep 5083433 = 3812575) B3812575
theorem B3388955 : Blo 2257435 3388955 := bstep (se 1 (by rfl) ⟨2541716, by rfl⟩ : syracuseStep 3388955 = 5083433) B5083433
theorem B2259303 : Blo 2257435 2259303 := bstep (se 1 (by rfl) ⟨1694477, by rfl⟩ : syracuseStep 2259303 = 3388955) B3388955
theorem B2541721 : Blo 2257435 2541721 := bbase (se 2 (by rfl) ⟨953145, by rfl⟩ : syracuseStep 2541721 = 1906291) (by norm_num)
theorem B3388961 : Blo 2257435 3388961 := bstep (se 2 (by rfl) ⟨1270860, by rfl⟩ : syracuseStep 3388961 = 2541721) B2541721
theorem B2259307 : Blo 2257435 2259307 := bstep (se 1 (by rfl) ⟨1694480, by rfl⟩ : syracuseStep 2259307 = 3388961) B3388961
theorem B8578325 : Blo 2257435 8578325 := bbase (se 6 (by rfl) ⟨201054, by rfl⟩ : syracuseStep 8578325 = 402109) (by norm_num)
theorem B5718883 : Blo 2257435 5718883 := bstep (se 1 (by rfl) ⟨4289162, by rfl⟩ : syracuseStep 5718883 = 8578325) B8578325
theorem B7625177 : Blo 2257435 7625177 := bstep (se 2 (by rfl) ⟨2859441, by rfl⟩ : syracuseStep 7625177 = 5718883) B5718883
theorem B5083451 : Blo 2257435 5083451 := bstep (se 1 (by rfl) ⟨3812588, by rfl⟩ : syracuseStep 5083451 = 7625177) B7625177
theorem B3388967 : Blo 2257435 3388967 := bstep (se 1 (by rfl) ⟨2541725, by rfl⟩ : syracuseStep 3388967 = 5083451) B5083451
theorem B2259311 : Blo 2257435 2259311 := bstep (se 1 (by rfl) ⟨1694483, by rfl⟩ : syracuseStep 2259311 = 3388967) B3388967
theorem B3388973 : Blo 2257435 3388973 := bbase (se 3 (by rfl) ⟨635432, by rfl⟩ : syracuseStep 3388973 = 1270865) (by norm_num)
theorem B2259315 : Blo 2257435 2259315 := bstep (se 1 (by rfl) ⟨1694486, by rfl⟩ : syracuseStep 2259315 = 3388973) B3388973
theorem B5083469 : Blo 2257435 5083469 := bbase (se 3 (by rfl) ⟨953150, by rfl⟩ : syracuseStep 5083469 = 1906301) (by norm_num)
theorem B3388979 : Blo 2257435 3388979 := bstep (se 1 (by rfl) ⟨2541734, by rfl⟩ : syracuseStep 3388979 = 5083469) B5083469
theorem B2259319 : Blo 2257435 2259319 := bstep (se 1 (by rfl) ⟨1694489, by rfl⟩ : syracuseStep 2259319 = 3388979) B3388979
theorem B2859457 : Blo 2257435 2859457 := bbase (se 2 (by rfl) ⟨1072296, by rfl⟩ : syracuseStep 2859457 = 2144593) (by norm_num)
theorem B3812609 : Blo 2257435 3812609 := bstep (se 2 (by rfl) ⟨1429728, by rfl⟩ : syracuseStep 3812609 = 2859457) B2859457
theorem B2541739 : Blo 2257435 2541739 := bstep (se 1 (by rfl) ⟨1906304, by rfl⟩ : syracuseStep 2541739 = 3812609) B3812609
theorem B3388985 : Blo 2257435 3388985 := bstep (se 2 (by rfl) ⟨1270869, by rfl⟩ : syracuseStep 3388985 = 2541739) B2541739
theorem B2259323 : Blo 2257435 2259323 := bstep (se 1 (by rfl) ⟨1694492, by rfl⟩ : syracuseStep 2259323 = 3388985) B3388985
theorem B20611381 : Blo 2257435 20611381 := bbase (se 5 (by rfl) ⟨966158, by rfl⟩ : syracuseStep 20611381 = 1932317) (by norm_num)
theorem B27481841 : Blo 2257435 27481841 := bstep (se 2 (by rfl) ⟨10305690, by rfl⟩ : syracuseStep 27481841 = 20611381) B20611381
theorem B18321227 : Blo 2257435 18321227 := bstep (se 1 (by rfl) ⟨13740920, by rfl⟩ : syracuseStep 18321227 = 27481841) B27481841
theorem B12214151 : Blo 2257435 12214151 := bstep (se 1 (by rfl) ⟨9160613, by rfl⟩ : syracuseStep 12214151 = 18321227) B18321227
theorem B8142767 : Blo 2257435 8142767 := bstep (se 1 (by rfl) ⟨6107075, by rfl⟩ : syracuseStep 8142767 = 12214151) B12214151
theorem B5428511 : Blo 2257435 5428511 := bstep (se 1 (by rfl) ⟨4071383, by rfl⟩ : syracuseStep 5428511 = 8142767) B8142767
theorem B3619007 : Blo 2257435 3619007 := bstep (se 1 (by rfl) ⟨2714255, by rfl⟩ : syracuseStep 3619007 = 5428511) B5428511
theorem B2412671 : Blo 2257435 2412671 := bstep (se 1 (by rfl) ⟨1809503, by rfl⟩ : syracuseStep 2412671 = 3619007) B3619007
theorem B25735157 : Blo 2257435 25735157 := bstep (se 5 (by rfl) ⟨1206335, by rfl⟩ : syracuseStep 25735157 = 2412671) B2412671
theorem B17156771 : Blo 2257435 17156771 := bstep (se 1 (by rfl) ⟨12867578, by rfl⟩ : syracuseStep 17156771 = 25735157) B25735157
theorem B11437847 : Blo 2257435 11437847 := bstep (se 1 (by rfl) ⟨8578385, by rfl⟩ : syracuseStep 11437847 = 17156771) B17156771
theorem B7625231 : Blo 2257435 7625231 := bstep (se 1 (by rfl) ⟨5718923, by rfl⟩ : syracuseStep 7625231 = 11437847) B11437847
theorem B5083487 : Blo 2257435 5083487 := bstep (se 1 (by rfl) ⟨3812615, by rfl⟩ : syracuseStep 5083487 = 7625231) B7625231
theorem B3388991 : Blo 2257435 3388991 := bstep (se 1 (by rfl) ⟨2541743, by rfl⟩ : syracuseStep 3388991 = 5083487) B5083487
theorem B2259327 : Blo 2257435 2259327 := bstep (se 1 (by rfl) ⟨1694495, by rfl⟩ : syracuseStep 2259327 = 3388991) B3388991
theorem B3388997 : Blo 2257435 3388997 := bbase (se 4 (by rfl) ⟨317718, by rfl⟩ : syracuseStep 3388997 = 635437) (by norm_num)
theorem B2259331 : Blo 2257435 2259331 := bstep (se 1 (by rfl) ⟨1694498, by rfl⟩ : syracuseStep 2259331 = 3388997) B3388997
theorem B3812629 : Blo 2257435 3812629 := bbase (se 6 (by rfl) ⟨89358, by rfl⟩ : syracuseStep 3812629 = 178717) (by norm_num)
theorem B5083505 : Blo 2257435 5083505 := bstep (se 2 (by rfl) ⟨1906314, by rfl⟩ : syracuseStep 5083505 = 3812629) B3812629
theorem B3389003 : Blo 2257435 3389003 := bstep (se 1 (by rfl) ⟨2541752, by rfl⟩ : syracuseStep 3389003 = 5083505) B5083505
theorem B2259335 : Blo 2257435 2259335 := bstep (se 1 (by rfl) ⟨1694501, by rfl⟩ : syracuseStep 2259335 = 3389003) B3389003
theorem B2541757 : Blo 2257435 2541757 := bbase (se 3 (by rfl) ⟨476579, by rfl⟩ : syracuseStep 2541757 = 953159) (by norm_num)
theorem B3389009 : Blo 2257435 3389009 := bstep (se 2 (by rfl) ⟨1270878, by rfl⟩ : syracuseStep 3389009 = 2541757) B2541757
theorem B2259339 : Blo 2257435 2259339 := bstep (se 1 (by rfl) ⟨1694504, by rfl⟩ : syracuseStep 2259339 = 3389009) B3389009
theorem B7625285 : Blo 2257435 7625285 := bbase (se 4 (by rfl) ⟨714870, by rfl⟩ : syracuseStep 7625285 = 1429741) (by norm_num)
theorem B5083523 : Blo 2257435 5083523 := bstep (se 1 (by rfl) ⟨3812642, by rfl⟩ : syracuseStep 5083523 = 7625285) B7625285
theorem B3389015 : Blo 2257435 3389015 := bstep (se 1 (by rfl) ⟨2541761, by rfl⟩ : syracuseStep 3389015 = 5083523) B5083523
theorem B2259343 : Blo 2257435 2259343 := bstep (se 1 (by rfl) ⟨1694507, by rfl⟩ : syracuseStep 2259343 = 3389015) B3389015
theorem B3389021 : Blo 2257435 3389021 := bbase (se 3 (by rfl) ⟨635441, by rfl⟩ : syracuseStep 3389021 = 1270883) (by norm_num)
theorem B2259347 : Blo 2257435 2259347 := bstep (se 1 (by rfl) ⟨1694510, by rfl⟩ : syracuseStep 2259347 = 3389021) B3389021
theorem B5083541 : Blo 2257435 5083541 := bbase (se 6 (by rfl) ⟨119145, by rfl⟩ : syracuseStep 5083541 = 238291) (by norm_num)
theorem B3389027 : Blo 2257435 3389027 := bstep (se 1 (by rfl) ⟨2541770, by rfl⟩ : syracuseStep 3389027 = 5083541) B5083541
theorem B2259351 : Blo 2257435 2259351 := bstep (se 1 (by rfl) ⟨1694513, by rfl⟩ : syracuseStep 2259351 = 3389027) B3389027
theorem B8142869 : Blo 2257435 8142869 := bbase (se 6 (by rfl) ⟨190848, by rfl⟩ : syracuseStep 8142869 = 381697) (by norm_num)
theorem B5428579 : Blo 2257435 5428579 := bstep (se 1 (by rfl) ⟨4071434, by rfl⟩ : syracuseStep 5428579 = 8142869) B8142869
theorem B7238105 : Blo 2257435 7238105 := bstep (se 2 (by rfl) ⟨2714289, by rfl⟩ : syracuseStep 7238105 = 5428579) B5428579
theorem B4825403 : Blo 2257435 4825403 := bstep (se 1 (by rfl) ⟨3619052, by rfl⟩ : syracuseStep 4825403 = 7238105) B7238105
theorem B3216935 : Blo 2257435 3216935 := bstep (se 1 (by rfl) ⟨2412701, by rfl⟩ : syracuseStep 3216935 = 4825403) B4825403
theorem B8578493 : Blo 2257435 8578493 := bstep (se 3 (by rfl) ⟨1608467, by rfl⟩ : syracuseStep 8578493 = 3216935) B3216935
theorem B5718995 : Blo 2257435 5718995 := bstep (se 1 (by rfl) ⟨4289246, by rfl⟩ : syracuseStep 5718995 = 8578493) B8578493
theorem B3812663 : Blo 2257435 3812663 := bstep (se 1 (by rfl) ⟨2859497, by rfl⟩ : syracuseStep 3812663 = 5718995) B5718995
theorem B2541775 : Blo 2257435 2541775 := bstep (se 1 (by rfl) ⟨1906331, by rfl⟩ : syracuseStep 2541775 = 3812663) B3812663
theorem B3389033 : Blo 2257435 3389033 := bstep (se 2 (by rfl) ⟨1270887, by rfl⟩ : syracuseStep 3389033 = 2541775) B2541775
theorem B2259355 : Blo 2257435 2259355 := bstep (se 1 (by rfl) ⟨1694516, by rfl⟩ : syracuseStep 2259355 = 3389033) B3389033
theorem B9650821 : Blo 2257435 9650821 := bbase (se 4 (by rfl) ⟨904764, by rfl⟩ : syracuseStep 9650821 = 1809529) (by norm_num)
theorem B12867761 : Blo 2257435 12867761 := bstep (se 2 (by rfl) ⟨4825410, by rfl⟩ : syracuseStep 12867761 = 9650821) B9650821
theorem B8578507 : Blo 2257435 8578507 := bstep (se 1 (by rfl) ⟨6433880, by rfl⟩ : syracuseStep 8578507 = 12867761) B12867761
theorem B11438009 : Blo 2257435 11438009 := bstep (se 2 (by rfl) ⟨4289253, by rfl⟩ : syracuseStep 11438009 = 8578507) B8578507
theorem B7625339 : Blo 2257435 7625339 := bstep (se 1 (by rfl) ⟨5719004, by rfl⟩ : syracuseStep 7625339 = 11438009) B11438009
theorem B5083559 : Blo 2257435 5083559 := bstep (se 1 (by rfl) ⟨3812669, by rfl⟩ : syracuseStep 5083559 = 7625339) B7625339
theorem B3389039 : Blo 2257435 3389039 := bstep (se 1 (by rfl) ⟨2541779, by rfl⟩ : syracuseStep 3389039 = 5083559) B5083559
theorem B2259359 : Blo 2257435 2259359 := bstep (se 1 (by rfl) ⟨1694519, by rfl⟩ : syracuseStep 2259359 = 3389039) B3389039
theorem B3389045 : Blo 2257435 3389045 := bbase (se 5 (by rfl) ⟨158861, by rfl⟩ : syracuseStep 3389045 = 317723) (by norm_num)
theorem B2259363 : Blo 2257435 2259363 := bstep (se 1 (by rfl) ⟨1694522, by rfl⟩ : syracuseStep 2259363 = 3389045) B3389045
theorem B4289269 : Blo 2257435 4289269 := bbase (se 5 (by rfl) ⟨201059, by rfl⟩ : syracuseStep 4289269 = 402119) (by norm_num)
theorem B5719025 : Blo 2257435 5719025 := bstep (se 2 (by rfl) ⟨2144634, by rfl⟩ : syracuseStep 5719025 = 4289269) B4289269
theorem B3812683 : Blo 2257435 3812683 := bstep (se 1 (by rfl) ⟨2859512, by rfl⟩ : syracuseStep 3812683 = 5719025) B5719025
theorem B5083577 : Blo 2257435 5083577 := bstep (se 2 (by rfl) ⟨1906341, by rfl⟩ : syracuseStep 5083577 = 3812683) B3812683
theorem B3389051 : Blo 2257435 3389051 := bstep (se 1 (by rfl) ⟨2541788, by rfl⟩ : syracuseStep 3389051 = 5083577) B5083577
theorem B2259367 : Blo 2257435 2259367 := bstep (se 1 (by rfl) ⟨1694525, by rfl⟩ : syracuseStep 2259367 = 3389051) B3389051
theorem B2541793 : Blo 2257435 2541793 := bbase (se 2 (by rfl) ⟨953172, by rfl⟩ : syracuseStep 2541793 = 1906345) (by norm_num)
theorem B3389057 : Blo 2257435 3389057 := bstep (se 2 (by rfl) ⟨1270896, by rfl⟩ : syracuseStep 3389057 = 2541793) B2541793
theorem B2259371 : Blo 2257435 2259371 := bstep (se 1 (by rfl) ⟨1694528, by rfl⟩ : syracuseStep 2259371 = 3389057) B3389057
theorem B5719045 : Blo 2257435 5719045 := bbase (se 4 (by rfl) ⟨536160, by rfl⟩ : syracuseStep 5719045 = 1072321) (by norm_num)
theorem B7625393 : Blo 2257435 7625393 := bstep (se 2 (by rfl) ⟨2859522, by rfl⟩ : syracuseStep 7625393 = 5719045) B5719045
theorem B5083595 : Blo 2257435 5083595 := bstep (se 1 (by rfl) ⟨3812696, by rfl⟩ : syracuseStep 5083595 = 7625393) B7625393
theorem B3389063 : Blo 2257435 3389063 := bstep (se 1 (by rfl) ⟨2541797, by rfl⟩ : syracuseStep 3389063 = 5083595) B5083595
theorem B2259375 : Blo 2257435 2259375 := bstep (se 1 (by rfl) ⟨1694531, by rfl⟩ : syracuseStep 2259375 = 3389063) B3389063
theorem B3389069 : Blo 2257435 3389069 := bbase (se 3 (by rfl) ⟨635450, by rfl⟩ : syracuseStep 3389069 = 1270901) (by norm_num)
theorem B2259379 : Blo 2257435 2259379 := bstep (se 1 (by rfl) ⟨1694534, by rfl⟩ : syracuseStep 2259379 = 3389069) B3389069
theorem B5083613 : Blo 2257435 5083613 := bbase (se 3 (by rfl) ⟨953177, by rfl⟩ : syracuseStep 5083613 = 1906355) (by norm_num)
theorem B3389075 : Blo 2257435 3389075 := bstep (se 1 (by rfl) ⟨2541806, by rfl⟩ : syracuseStep 3389075 = 5083613) B5083613
theorem B2259383 : Blo 2257435 2259383 := bstep (se 1 (by rfl) ⟨1694537, by rfl⟩ : syracuseStep 2259383 = 3389075) B3389075
theorem B3812717 : Blo 2257435 3812717 := bbase (se 3 (by rfl) ⟨714884, by rfl⟩ : syracuseStep 3812717 = 1429769) (by norm_num)
theorem B2541811 : Blo 2257435 2541811 := bstep (se 1 (by rfl) ⟨1906358, by rfl⟩ : syracuseStep 2541811 = 3812717) B3812717
theorem B3389081 : Blo 2257435 3389081 := bstep (se 2 (by rfl) ⟨1270905, by rfl⟩ : syracuseStep 3389081 = 2541811) B2541811
theorem B2259387 : Blo 2257435 2259387 := bstep (se 1 (by rfl) ⟨1694540, by rfl⟩ : syracuseStep 2259387 = 3389081) B3389081
theorem B2751365 : Blo 2257435 2751365 := bbase (se 4 (by rfl) ⟨257940, by rfl⟩ : syracuseStep 2751365 = 515881) (by norm_num)
theorem B7336973 : Blo 2257435 7336973 := bstep (se 3 (by rfl) ⟨1375682, by rfl⟩ : syracuseStep 7336973 = 2751365) B2751365
theorem B4891315 : Blo 2257435 4891315 := bstep (se 1 (by rfl) ⟨3668486, by rfl⟩ : syracuseStep 4891315 = 7336973) B7336973
theorem B6521753 : Blo 2257435 6521753 := bstep (se 2 (by rfl) ⟨2445657, by rfl⟩ : syracuseStep 6521753 = 4891315) B4891315
theorem B17391341 : Blo 2257435 17391341 := bstep (se 3 (by rfl) ⟨3260876, by rfl⟩ : syracuseStep 17391341 = 6521753) B6521753
theorem B11594227 : Blo 2257435 11594227 := bstep (se 1 (by rfl) ⟨8695670, by rfl⟩ : syracuseStep 11594227 = 17391341) B17391341
theorem B15458969 : Blo 2257435 15458969 := bstep (se 2 (by rfl) ⟨5797113, by rfl⟩ : syracuseStep 15458969 = 11594227) B11594227
theorem B41223917 : Blo 2257435 41223917 := bstep (se 3 (by rfl) ⟨7729484, by rfl⟩ : syracuseStep 41223917 = 15458969) B15458969
theorem B109930445 : Blo 2257435 109930445 := bstep (se 3 (by rfl) ⟨20611958, by rfl⟩ : syracuseStep 109930445 = 41223917) B41223917
theorem B73286963 : Blo 2257435 73286963 := bstep (se 1 (by rfl) ⟨54965222, by rfl⟩ : syracuseStep 73286963 = 109930445) B109930445
theorem B48857975 : Blo 2257435 48857975 := bstep (se 1 (by rfl) ⟨36643481, by rfl⟩ : syracuseStep 48857975 = 73286963) B73286963
theorem B32571983 : Blo 2257435 32571983 := bstep (se 1 (by rfl) ⟨24428987, by rfl⟩ : syracuseStep 32571983 = 48857975) B48857975
theorem B21714655 : Blo 2257435 21714655 := bstep (se 1 (by rfl) ⟨16285991, by rfl⟩ : syracuseStep 21714655 = 32571983) B32571983
theorem B28952873 : Blo 2257435 28952873 := bstep (se 2 (by rfl) ⟨10857327, by rfl⟩ : syracuseStep 28952873 = 21714655) B21714655
theorem B19301915 : Blo 2257435 19301915 := bstep (se 1 (by rfl) ⟨14476436, by rfl⟩ : syracuseStep 19301915 = 28952873) B28952873
theorem B12867943 : Blo 2257435 12867943 := bstep (se 1 (by rfl) ⟨9650957, by rfl⟩ : syracuseStep 12867943 = 19301915) B19301915
theorem B17157257 : Blo 2257435 17157257 := bstep (se 2 (by rfl) ⟨6433971, by rfl⟩ : syracuseStep 17157257 = 12867943) B12867943
theorem B11438171 : Blo 2257435 11438171 := bstep (se 1 (by rfl) ⟨8578628, by rfl⟩ : syracuseStep 11438171 = 17157257) B17157257
theorem B7625447 : Blo 2257435 7625447 := bstep (se 1 (by rfl) ⟨5719085, by rfl⟩ : syracuseStep 7625447 = 11438171) B11438171
theorem B5083631 : Blo 2257435 5083631 := bstep (se 1 (by rfl) ⟨3812723, by rfl⟩ : syracuseStep 5083631 = 7625447) B7625447
theorem B3389087 : Blo 2257435 3389087 := bstep (se 1 (by rfl) ⟨2541815, by rfl⟩ : syracuseStep 3389087 = 5083631) B5083631
theorem B2259391 : Blo 2257435 2259391 := bstep (se 1 (by rfl) ⟨1694543, by rfl⟩ : syracuseStep 2259391 = 3389087) B3389087
theorem B3389093 : Blo 2257435 3389093 := bbase (se 4 (by rfl) ⟨317727, by rfl⟩ : syracuseStep 3389093 = 635455) (by norm_num)
theorem B2259395 : Blo 2257435 2259395 := bstep (se 1 (by rfl) ⟨1694546, by rfl⟩ : syracuseStep 2259395 = 3389093) B3389093
theorem B2859553 : Blo 2257435 2859553 := bbase (se 2 (by rfl) ⟨1072332, by rfl⟩ : syracuseStep 2859553 = 2144665) (by norm_num)
theorem B3812737 : Blo 2257435 3812737 := bstep (se 2 (by rfl) ⟨1429776, by rfl⟩ : syracuseStep 3812737 = 2859553) B2859553
theorem B5083649 : Blo 2257435 5083649 := bstep (se 2 (by rfl) ⟨1906368, by rfl⟩ : syracuseStep 5083649 = 3812737) B3812737
theorem B3389099 : Blo 2257435 3389099 := bstep (se 1 (by rfl) ⟨2541824, by rfl⟩ : syracuseStep 3389099 = 5083649) B5083649
theorem B2259399 : Blo 2257435 2259399 := bstep (se 1 (by rfl) ⟨1694549, by rfl⟩ : syracuseStep 2259399 = 3389099) B3389099
theorem B2541829 : Blo 2257435 2541829 := bbase (se 4 (by rfl) ⟨238296, by rfl⟩ : syracuseStep 2541829 = 476593) (by norm_num)
theorem B3389105 : Blo 2257435 3389105 := bstep (se 2 (by rfl) ⟨1270914, by rfl⟩ : syracuseStep 3389105 = 2541829) B2541829
theorem B2259403 : Blo 2257435 2259403 := bstep (se 1 (by rfl) ⟨1694552, by rfl⟩ : syracuseStep 2259403 = 3389105) B3389105
theorem B2412757 : Blo 2257435 2412757 := bbase (se 7 (by rfl) ⟨28274, by rfl⟩ : syracuseStep 2412757 = 56549) (by norm_num)
theorem B3217009 : Blo 2257435 3217009 := bstep (se 2 (by rfl) ⟨1206378, by rfl⟩ : syracuseStep 3217009 = 2412757) B2412757
theorem B4289345 : Blo 2257435 4289345 := bstep (se 2 (by rfl) ⟨1608504, by rfl⟩ : syracuseStep 4289345 = 3217009) B3217009
theorem B2859563 : Blo 2257435 2859563 := bstep (se 1 (by rfl) ⟨2144672, by rfl⟩ : syracuseStep 2859563 = 4289345) B4289345
theorem B7625501 : Blo 2257435 7625501 := bstep (se 3 (by rfl) ⟨1429781, by rfl⟩ : syracuseStep 7625501 = 2859563) B2859563
theorem B5083667 : Blo 2257435 5083667 := bstep (se 1 (by rfl) ⟨3812750, by rfl⟩ : syracuseStep 5083667 = 7625501) B7625501
theorem B3389111 : Blo 2257435 3389111 := bstep (se 1 (by rfl) ⟨2541833, by rfl⟩ : syracuseStep 3389111 = 5083667) B5083667
theorem B2259407 : Blo 2257435 2259407 := bstep (se 1 (by rfl) ⟨1694555, by rfl⟩ : syracuseStep 2259407 = 3389111) B3389111
theorem B3389117 : Blo 2257435 3389117 := bbase (se 3 (by rfl) ⟨635459, by rfl⟩ : syracuseStep 3389117 = 1270919) (by norm_num)
theorem B2259411 : Blo 2257435 2259411 := bstep (se 1 (by rfl) ⟨1694558, by rfl⟩ : syracuseStep 2259411 = 3389117) B3389117
theorem B5083685 : Blo 2257435 5083685 := bbase (se 4 (by rfl) ⟨476595, by rfl⟩ : syracuseStep 5083685 = 953191) (by norm_num)
theorem B3389123 : Blo 2257435 3389123 := bstep (se 1 (by rfl) ⟨2541842, by rfl⟩ : syracuseStep 3389123 = 5083685) B5083685
theorem B2259415 : Blo 2257435 2259415 := bstep (se 1 (by rfl) ⟨1694561, by rfl⟩ : syracuseStep 2259415 = 3389123) B3389123
theorem B5719157 : Blo 2257435 5719157 := bbase (se 5 (by rfl) ⟨268085, by rfl⟩ : syracuseStep 5719157 = 536171) (by norm_num)
theorem B3812771 : Blo 2257435 3812771 := bstep (se 1 (by rfl) ⟨2859578, by rfl⟩ : syracuseStep 3812771 = 5719157) B5719157
theorem B2541847 : Blo 2257435 2541847 := bstep (se 1 (by rfl) ⟨1906385, by rfl⟩ : syracuseStep 2541847 = 3812771) B3812771
theorem B3389129 : Blo 2257435 3389129 := bstep (se 2 (by rfl) ⟨1270923, by rfl⟩ : syracuseStep 3389129 = 2541847) B2541847
theorem B2259419 : Blo 2257435 2259419 := bstep (se 1 (by rfl) ⟨1694564, by rfl⟩ : syracuseStep 2259419 = 3389129) B3389129
theorem B21714965 : Blo 2257435 21714965 := bbase (se 6 (by rfl) ⟨508944, by rfl⟩ : syracuseStep 21714965 = 1017889) (by norm_num)
theorem B14476643 : Blo 2257435 14476643 := bstep (se 1 (by rfl) ⟨10857482, by rfl⟩ : syracuseStep 14476643 = 21714965) B21714965
theorem B9651095 : Blo 2257435 9651095 := bstep (se 1 (by rfl) ⟨7238321, by rfl⟩ : syracuseStep 9651095 = 14476643) B14476643
theorem B6434063 : Blo 2257435 6434063 := bstep (se 1 (by rfl) ⟨4825547, by rfl⟩ : syracuseStep 6434063 = 9651095) B9651095
theorem B4289375 : Blo 2257435 4289375 := bstep (se 1 (by rfl) ⟨3217031, by rfl⟩ : syracuseStep 4289375 = 6434063) B6434063
theorem B11438333 : Blo 2257435 11438333 := bstep (se 3 (by rfl) ⟨2144687, by rfl⟩ : syracuseStep 11438333 = 4289375) B4289375
theorem B7625555 : Blo 2257435 7625555 := bstep (se 1 (by rfl) ⟨5719166, by rfl⟩ : syracuseStep 7625555 = 11438333) B11438333
theorem B5083703 : Blo 2257435 5083703 := bstep (se 1 (by rfl) ⟨3812777, by rfl⟩ : syracuseStep 5083703 = 7625555) B7625555
theorem B3389135 : Blo 2257435 3389135 := bstep (se 1 (by rfl) ⟨2541851, by rfl⟩ : syracuseStep 3389135 = 5083703) B5083703
theorem B2259423 : Blo 2257435 2259423 := bstep (se 1 (by rfl) ⟨1694567, by rfl⟩ : syracuseStep 2259423 = 3389135) B3389135
theorem B3389141 : Blo 2257435 3389141 := bbase (se 7 (by rfl) ⟨39716, by rfl⟩ : syracuseStep 3389141 = 79433) (by norm_num)
theorem B2259427 : Blo 2257435 2259427 := bstep (se 1 (by rfl) ⟨1694570, by rfl⟩ : syracuseStep 2259427 = 3389141) B3389141
theorem B4825565 : Blo 2257435 4825565 := bbase (se 3 (by rfl) ⟨904793, by rfl⟩ : syracuseStep 4825565 = 1809587) (by norm_num)
theorem B3217043 : Blo 2257435 3217043 := bstep (se 1 (by rfl) ⟨2412782, by rfl⟩ : syracuseStep 3217043 = 4825565) B4825565
theorem B8578781 : Blo 2257435 8578781 := bstep (se 3 (by rfl) ⟨1608521, by rfl⟩ : syracuseStep 8578781 = 3217043) B3217043
theorem B5719187 : Blo 2257435 5719187 := bstep (se 1 (by rfl) ⟨4289390, by rfl⟩ : syracuseStep 5719187 = 8578781) B8578781
theorem B3812791 : Blo 2257435 3812791 := bstep (se 1 (by rfl) ⟨2859593, by rfl⟩ : syracuseStep 3812791 = 5719187) B5719187
theorem B5083721 : Blo 2257435 5083721 := bstep (se 2 (by rfl) ⟨1906395, by rfl⟩ : syracuseStep 5083721 = 3812791) B3812791
theorem B3389147 : Blo 2257435 3389147 := bstep (se 1 (by rfl) ⟨2541860, by rfl⟩ : syracuseStep 3389147 = 5083721) B5083721
theorem B2259431 : Blo 2257435 2259431 := bstep (se 1 (by rfl) ⟨1694573, by rfl⟩ : syracuseStep 2259431 = 3389147) B3389147
theorem B2541865 : Blo 2257435 2541865 := bbase (se 2 (by rfl) ⟨953199, by rfl⟩ : syracuseStep 2541865 = 1906399) (by norm_num)
theorem B3389153 : Blo 2257435 3389153 := bstep (se 2 (by rfl) ⟨1270932, by rfl⟩ : syracuseStep 3389153 = 2541865) B2541865
theorem B2259435 : Blo 2257435 2259435 := bstep (se 1 (by rfl) ⟨1694576, by rfl⟩ : syracuseStep 2259435 = 3389153) B3389153
theorem C0 (j : ℕ) (h1 : 564358 ≤ j) (h2 : j ≤ 564858) : Blo 2257435 (4 * j + 3) := by
  interval_cases j
  · exact B2257435
  · exact B2257439
  · exact B2257443
  · exact B2257447
  · exact B2257451
  · exact B2257455
  · exact B2257459
  · exact B2257463
  · exact B2257467
  · exact B2257471
  · exact B2257475
  · exact B2257479
  · exact B2257483
  · exact B2257487
  · exact B2257491
  · exact B2257495
  · exact B2257499
  · exact B2257503
  · exact B2257507
  · exact B2257511
  · exact B2257515
  · exact B2257519
  · exact B2257523
  · exact B2257527
  · exact B2257531
  · exact B2257535
  · exact B2257539
  · exact B2257543
  · exact B2257547
  · exact B2257551
  · exact B2257555
  · exact B2257559
  · exact B2257563
  · exact B2257567
  · exact B2257571
  · exact B2257575
  · exact B2257579
  · exact B2257583
  · exact B2257587
  · exact B2257591
  · exact B2257595
  · exact B2257599
  · exact B2257603
  · exact B2257607
  · exact B2257611
  · exact B2257615
  · exact B2257619
  · exact B2257623
  · exact B2257627
  · exact B2257631
  · exact B2257635
  · exact B2257639
  · exact B2257643
  · exact B2257647
  · exact B2257651
  · exact B2257655
  · exact B2257659
  · exact B2257663
  · exact B2257667
  · exact B2257671
  · exact B2257675
  · exact B2257679
  · exact B2257683
  · exact B2257687
  · exact B2257691
  · exact B2257695
  · exact B2257699
  · exact B2257703
  · exact B2257707
  · exact B2257711
  · exact B2257715
  · exact B2257719
  · exact B2257723
  · exact B2257727
  · exact B2257731
  · exact B2257735
  · exact B2257739
  · exact B2257743
  · exact B2257747
  · exact B2257751
  · exact B2257755
  · exact B2257759
  · exact B2257763
  · exact B2257767
  · exact B2257771
  · exact B2257775
  · exact B2257779
  · exact B2257783
  · exact B2257787
  · exact B2257791
  · exact B2257795
  · exact B2257799
  · exact B2257803
  · exact B2257807
  · exact B2257811
  · exact B2257815
  · exact B2257819
  · exact B2257823
  · exact B2257827
  · exact B2257831
  · exact B2257835
  · exact B2257839
  · exact B2257843
  · exact B2257847
  · exact B2257851
  · exact B2257855
  · exact B2257859
  · exact B2257863
  · exact B2257867
  · exact B2257871
  · exact B2257875
  · exact B2257879
  · exact B2257883
  · exact B2257887
  · exact B2257891
  · exact B2257895
  · exact B2257899
  · exact B2257903
  · exact B2257907
  · exact B2257911
  · exact B2257915
  · exact B2257919
  · exact B2257923
  · exact B2257927
  · exact B2257931
  · exact B2257935
  · exact B2257939
  · exact B2257943
  · exact B2257947
  · exact B2257951
  · exact B2257955
  · exact B2257959
  · exact B2257963
  · exact B2257967
  · exact B2257971
  · exact B2257975
  · exact B2257979
  · exact B2257983
  · exact B2257987
  · exact B2257991
  · exact B2257995
  · exact B2257999
  · exact B2258003
  · exact B2258007
  · exact B2258011
  · exact B2258015
  · exact B2258019
  · exact B2258023
  · exact B2258027
  · exact B2258031
  · exact B2258035
  · exact B2258039
  · exact B2258043
  · exact B2258047
  · exact B2258051
  · exact B2258055
  · exact B2258059
  · exact B2258063
  · exact B2258067
  · exact B2258071
  · exact B2258075
  · exact B2258079
  · exact B2258083
  · exact B2258087
  · exact B2258091
  · exact B2258095
  · exact B2258099
  · exact B2258103
  · exact B2258107
  · exact B2258111
  · exact B2258115
  · exact B2258119
  · exact B2258123
  · exact B2258127
  · exact B2258131
  · exact B2258135
  · exact B2258139
  · exact B2258143
  · exact B2258147
  · exact B2258151
  · exact B2258155
  · exact B2258159
  · exact B2258163
  · exact B2258167
  · exact B2258171
  · exact B2258175
  · exact B2258179
  · exact B2258183
  · exact B2258187
  · exact B2258191
  · exact B2258195
  · exact B2258199
  · exact B2258203
  · exact B2258207
  · exact B2258211
  · exact B2258215
  · exact B2258219
  · exact B2258223
  · exact B2258227
  · exact B2258231
  · exact B2258235
  · exact B2258239
  · exact B2258243
  · exact B2258247
  · exact B2258251
  · exact B2258255
  · exact B2258259
  · exact B2258263
  · exact B2258267
  · exact B2258271
  · exact B2258275
  · exact B2258279
  · exact B2258283
  · exact B2258287
  · exact B2258291
  · exact B2258295
  · exact B2258299
  · exact B2258303
  · exact B2258307
  · exact B2258311
  · exact B2258315
  · exact B2258319
  · exact B2258323
  · exact B2258327
  · exact B2258331
  · exact B2258335
  · exact B2258339
  · exact B2258343
  · exact B2258347
  · exact B2258351
  · exact B2258355
  · exact B2258359
  · exact B2258363
  · exact B2258367
  · exact B2258371
  · exact B2258375
  · exact B2258379
  · exact B2258383
  · exact B2258387
  · exact B2258391
  · exact B2258395
  · exact B2258399
  · exact B2258403
  · exact B2258407
  · exact B2258411
  · exact B2258415
  · exact B2258419
  · exact B2258423
  · exact B2258427
  · exact B2258431
  · exact B2258435
  · exact B2258439
  · exact B2258443
  · exact B2258447
  · exact B2258451
  · exact B2258455
  · exact B2258459
  · exact B2258463
  · exact B2258467
  · exact B2258471
  · exact B2258475
  · exact B2258479
  · exact B2258483
  · exact B2258487
  · exact B2258491
  · exact B2258495
  · exact B2258499
  · exact B2258503
  · exact B2258507
  · exact B2258511
  · exact B2258515
  · exact B2258519
  · exact B2258523
  · exact B2258527
  · exact B2258531
  · exact B2258535
  · exact B2258539
  · exact B2258543
  · exact B2258547
  · exact B2258551
  · exact B2258555
  · exact B2258559
  · exact B2258563
  · exact B2258567
  · exact B2258571
  · exact B2258575
  · exact B2258579
  · exact B2258583
  · exact B2258587
  · exact B2258591
  · exact B2258595
  · exact B2258599
  · exact B2258603
  · exact B2258607
  · exact B2258611
  · exact B2258615
  · exact B2258619
  · exact B2258623
  · exact B2258627
  · exact B2258631
  · exact B2258635
  · exact B2258639
  · exact B2258643
  · exact B2258647
  · exact B2258651
  · exact B2258655
  · exact B2258659
  · exact B2258663
  · exact B2258667
  · exact B2258671
  · exact B2258675
  · exact B2258679
  · exact B2258683
  · exact B2258687
  · exact B2258691
  · exact B2258695
  · exact B2258699
  · exact B2258703
  · exact B2258707
  · exact B2258711
  · exact B2258715
  · exact B2258719
  · exact B2258723
  · exact B2258727
  · exact B2258731
  · exact B2258735
  · exact B2258739
  · exact B2258743
  · exact B2258747
  · exact B2258751
  · exact B2258755
  · exact B2258759
  · exact B2258763
  · exact B2258767
  · exact B2258771
  · exact B2258775
  · exact B2258779
  · exact B2258783
  · exact B2258787
  · exact B2258791
  · exact B2258795
  · exact B2258799
  · exact B2258803
  · exact B2258807
  · exact B2258811
  · exact B2258815
  · exact B2258819
  · exact B2258823
  · exact B2258827
  · exact B2258831
  · exact B2258835
  · exact B2258839
  · exact B2258843
  · exact B2258847
  · exact B2258851
  · exact B2258855
  · exact B2258859
  · exact B2258863
  · exact B2258867
  · exact B2258871
  · exact B2258875
  · exact B2258879
  · exact B2258883
  · exact B2258887
  · exact B2258891
  · exact B2258895
  · exact B2258899
  · exact B2258903
  · exact B2258907
  · exact B2258911
  · exact B2258915
  · exact B2258919
  · exact B2258923
  · exact B2258927
  · exact B2258931
  · exact B2258935
  · exact B2258939
  · exact B2258943
  · exact B2258947
  · exact B2258951
  · exact B2258955
  · exact B2258959
  · exact B2258963
  · exact B2258967
  · exact B2258971
  · exact B2258975
  · exact B2258979
  · exact B2258983
  · exact B2258987
  · exact B2258991
  · exact B2258995
  · exact B2258999
  · exact B2259003
  · exact B2259007
  · exact B2259011
  · exact B2259015
  · exact B2259019
  · exact B2259023
  · exact B2259027
  · exact B2259031
  · exact B2259035
  · exact B2259039
  · exact B2259043
  · exact B2259047
  · exact B2259051
  · exact B2259055
  · exact B2259059
  · exact B2259063
  · exact B2259067
  · exact B2259071
  · exact B2259075
  · exact B2259079
  · exact B2259083
  · exact B2259087
  · exact B2259091
  · exact B2259095
  · exact B2259099
  · exact B2259103
  · exact B2259107
  · exact B2259111
  · exact B2259115
  · exact B2259119
  · exact B2259123
  · exact B2259127
  · exact B2259131
  · exact B2259135
  · exact B2259139
  · exact B2259143
  · exact B2259147
  · exact B2259151
  · exact B2259155
  · exact B2259159
  · exact B2259163
  · exact B2259167
  · exact B2259171
  · exact B2259175
  · exact B2259179
  · exact B2259183
  · exact B2259187
  · exact B2259191
  · exact B2259195
  · exact B2259199
  · exact B2259203
  · exact B2259207
  · exact B2259211
  · exact B2259215
  · exact B2259219
  · exact B2259223
  · exact B2259227
  · exact B2259231
  · exact B2259235
  · exact B2259239
  · exact B2259243
  · exact B2259247
  · exact B2259251
  · exact B2259255
  · exact B2259259
  · exact B2259263
  · exact B2259267
  · exact B2259271
  · exact B2259275
  · exact B2259279
  · exact B2259283
  · exact B2259287
  · exact B2259291
  · exact B2259295
  · exact B2259299
  · exact B2259303
  · exact B2259307
  · exact B2259311
  · exact B2259315
  · exact B2259319
  · exact B2259323
  · exact B2259327
  · exact B2259331
  · exact B2259335
  · exact B2259339
  · exact B2259343
  · exact B2259347
  · exact B2259351
  · exact B2259355
  · exact B2259359
  · exact B2259363
  · exact B2259367
  · exact B2259371
  · exact B2259375
  · exact B2259379
  · exact B2259383
  · exact B2259387
  · exact B2259391
  · exact B2259395
  · exact B2259399
  · exact B2259403
  · exact B2259407
  · exact B2259411
  · exact B2259415
  · exact B2259419
  · exact B2259423
  · exact B2259427
  · exact B2259431
  · exact B2259435
theorem solution (m : ℕ) (hlo : 2257435 ≤ m) (hhi : m ≤ 2259435) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 564358 ≤ j := by omega
    have hj2 : j ≤ 564858 := by omega
    have hb : Blo 2257435 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
