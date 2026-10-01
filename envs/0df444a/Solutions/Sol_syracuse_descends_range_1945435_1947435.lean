-- Prove2me | solution 1 for syracuse_descends_range_1945435_1947435
-- status  : ACCEPTED   (prove)
-- author  : @chstdu
-- created : 2026-09-23T16:47:36.419885+00:00
-- url     : https://prove2.me/submissions/1ae79b6d-d525-45eb-9034-8cde84de627c

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

theorem B2218477 : Blo 1945435 2218477 := bbase (se 3 (by rfl) ⟨415964, by rfl⟩ : syracuseStep 2218477 = 831929) (by norm_num)
theorem B2957969 : Blo 1945435 2957969 := bstep (se 2 (by rfl) ⟨1109238, by rfl⟩ : syracuseStep 2957969 = 2218477) B2218477
theorem B7887917 : Blo 1945435 7887917 := bstep (se 3 (by rfl) ⟨1478984, by rfl⟩ : syracuseStep 7887917 = 2957969) B2957969
theorem B5258611 : Blo 1945435 5258611 := bstep (se 1 (by rfl) ⟨3943958, by rfl⟩ : syracuseStep 5258611 = 7887917) B7887917
theorem B7011481 : Blo 1945435 7011481 := bstep (se 2 (by rfl) ⟨2629305, by rfl⟩ : syracuseStep 7011481 = 5258611) B5258611
theorem B9348641 : Blo 1945435 9348641 := bstep (se 2 (by rfl) ⟨3505740, by rfl⟩ : syracuseStep 9348641 = 7011481) B7011481
theorem B6232427 : Blo 1945435 6232427 := bstep (se 1 (by rfl) ⟨4674320, by rfl⟩ : syracuseStep 6232427 = 9348641) B9348641
theorem B4154951 : Blo 1945435 4154951 := bstep (se 1 (by rfl) ⟨3116213, by rfl⟩ : syracuseStep 4154951 = 6232427) B6232427
theorem B2769967 : Blo 1945435 2769967 := bstep (se 1 (by rfl) ⟨2077475, by rfl⟩ : syracuseStep 2769967 = 4154951) B4154951
theorem B3693289 : Blo 1945435 3693289 := bstep (se 2 (by rfl) ⟨1384983, by rfl⟩ : syracuseStep 3693289 = 2769967) B2769967
theorem B4924385 : Blo 1945435 4924385 := bstep (se 2 (by rfl) ⟨1846644, by rfl⟩ : syracuseStep 4924385 = 3693289) B3693289
theorem B3282923 : Blo 1945435 3282923 := bstep (se 1 (by rfl) ⟨2462192, by rfl⟩ : syracuseStep 3282923 = 4924385) B4924385
theorem B2188615 : Blo 1945435 2188615 := bstep (se 1 (by rfl) ⟨1641461, by rfl⟩ : syracuseStep 2188615 = 3282923) B3282923
theorem B2918153 : Blo 1945435 2918153 := bstep (se 2 (by rfl) ⟨1094307, by rfl⟩ : syracuseStep 2918153 = 2188615) B2188615
theorem B1945435 : Blo 1945435 1945435 := bstep (se 1 (by rfl) ⟨1459076, by rfl⟩ : syracuseStep 1945435 = 2918153) B2918153
theorem B9848789 : Blo 1945435 9848789 := bbase (se 7 (by rfl) ⟨115415, by rfl⟩ : syracuseStep 9848789 = 230831) (by norm_num)
theorem B6565859 : Blo 1945435 6565859 := bstep (se 1 (by rfl) ⟨4924394, by rfl⟩ : syracuseStep 6565859 = 9848789) B9848789
theorem B4377239 : Blo 1945435 4377239 := bstep (se 1 (by rfl) ⟨3282929, by rfl⟩ : syracuseStep 4377239 = 6565859) B6565859
theorem B2918159 : Blo 1945435 2918159 := bstep (se 1 (by rfl) ⟨2188619, by rfl⟩ : syracuseStep 2918159 = 4377239) B4377239
theorem B1945439 : Blo 1945435 1945439 := bstep (se 1 (by rfl) ⟨1459079, by rfl⟩ : syracuseStep 1945439 = 2918159) B2918159
theorem B2918165 : Blo 1945435 2918165 := bbase (se 6 (by rfl) ⟨68394, by rfl⟩ : syracuseStep 2918165 = 136789) (by norm_num)
theorem B1945443 : Blo 1945435 1945443 := bstep (se 1 (by rfl) ⟨1459082, by rfl⟩ : syracuseStep 1945443 = 2918165) B2918165
theorem B3743701 : Blo 1945435 3743701 := bbase (se 7 (by rfl) ⟨43871, by rfl⟩ : syracuseStep 3743701 = 87743) (by norm_num)
theorem B19966405 : Blo 1945435 19966405 := bstep (se 4 (by rfl) ⟨1871850, by rfl⟩ : syracuseStep 19966405 = 3743701) B3743701
theorem B26621873 : Blo 1945435 26621873 := bstep (se 2 (by rfl) ⟨9983202, by rfl⟩ : syracuseStep 26621873 = 19966405) B19966405
theorem B17747915 : Blo 1945435 17747915 := bstep (se 1 (by rfl) ⟨13310936, by rfl⟩ : syracuseStep 17747915 = 26621873) B26621873
theorem B189311093 : Blo 1945435 189311093 := bstep (se 5 (by rfl) ⟨8873957, by rfl⟩ : syracuseStep 189311093 = 17747915) B17747915
theorem B126207395 : Blo 1945435 126207395 := bstep (se 1 (by rfl) ⟨94655546, by rfl⟩ : syracuseStep 126207395 = 189311093) B189311093
theorem B84138263 : Blo 1945435 84138263 := bstep (se 1 (by rfl) ⟨63103697, by rfl⟩ : syracuseStep 84138263 = 126207395) B126207395
theorem B56092175 : Blo 1945435 56092175 := bstep (se 1 (by rfl) ⟨42069131, by rfl⟩ : syracuseStep 56092175 = 84138263) B84138263
theorem B37394783 : Blo 1945435 37394783 := bstep (se 1 (by rfl) ⟨28046087, by rfl⟩ : syracuseStep 37394783 = 56092175) B56092175
theorem B24929855 : Blo 1945435 24929855 := bstep (se 1 (by rfl) ⟨18697391, by rfl⟩ : syracuseStep 24929855 = 37394783) B37394783
theorem B16619903 : Blo 1945435 16619903 := bstep (se 1 (by rfl) ⟨12464927, by rfl⟩ : syracuseStep 16619903 = 24929855) B24929855
theorem B11079935 : Blo 1945435 11079935 := bstep (se 1 (by rfl) ⟨8309951, by rfl⟩ : syracuseStep 11079935 = 16619903) B16619903
theorem B7386623 : Blo 1945435 7386623 := bstep (se 1 (by rfl) ⟨5539967, by rfl⟩ : syracuseStep 7386623 = 11079935) B11079935
theorem B4924415 : Blo 1945435 4924415 := bstep (se 1 (by rfl) ⟨3693311, by rfl⟩ : syracuseStep 4924415 = 7386623) B7386623
theorem B3282943 : Blo 1945435 3282943 := bstep (se 1 (by rfl) ⟨2462207, by rfl⟩ : syracuseStep 3282943 = 4924415) B4924415
theorem B4377257 : Blo 1945435 4377257 := bstep (se 2 (by rfl) ⟨1641471, by rfl⟩ : syracuseStep 4377257 = 3282943) B3282943
theorem B2918171 : Blo 1945435 2918171 := bstep (se 1 (by rfl) ⟨2188628, by rfl⟩ : syracuseStep 2918171 = 4377257) B4377257
theorem B1945447 : Blo 1945435 1945447 := bstep (se 1 (by rfl) ⟨1459085, by rfl⟩ : syracuseStep 1945447 = 2918171) B2918171
theorem B2188633 : Blo 1945435 2188633 := bbase (se 2 (by rfl) ⟨820737, by rfl⟩ : syracuseStep 2188633 = 1641475) (by norm_num)
theorem B2918177 : Blo 1945435 2918177 := bstep (se 2 (by rfl) ⟨1094316, by rfl⟩ : syracuseStep 2918177 = 2188633) B2188633
theorem B1945451 : Blo 1945435 1945451 := bstep (se 1 (by rfl) ⟨1459088, by rfl⟩ : syracuseStep 1945451 = 2918177) B2918177
theorem B3116245 : Blo 1945435 3116245 := bbase (se 7 (by rfl) ⟨36518, by rfl⟩ : syracuseStep 3116245 = 73037) (by norm_num)
theorem B4154993 : Blo 1945435 4154993 := bstep (se 2 (by rfl) ⟨1558122, by rfl⟩ : syracuseStep 4154993 = 3116245) B3116245
theorem B2769995 : Blo 1945435 2769995 := bstep (se 1 (by rfl) ⟨2077496, by rfl⟩ : syracuseStep 2769995 = 4154993) B4154993
theorem B7386653 : Blo 1945435 7386653 := bstep (se 3 (by rfl) ⟨1384997, by rfl⟩ : syracuseStep 7386653 = 2769995) B2769995
theorem B4924435 : Blo 1945435 4924435 := bstep (se 1 (by rfl) ⟨3693326, by rfl⟩ : syracuseStep 4924435 = 7386653) B7386653
theorem B6565913 : Blo 1945435 6565913 := bstep (se 2 (by rfl) ⟨2462217, by rfl⟩ : syracuseStep 6565913 = 4924435) B4924435
theorem B4377275 : Blo 1945435 4377275 := bstep (se 1 (by rfl) ⟨3282956, by rfl⟩ : syracuseStep 4377275 = 6565913) B6565913
theorem B2918183 : Blo 1945435 2918183 := bstep (se 1 (by rfl) ⟨2188637, by rfl⟩ : syracuseStep 2918183 = 4377275) B4377275
theorem B1945455 : Blo 1945435 1945455 := bstep (se 1 (by rfl) ⟨1459091, by rfl⟩ : syracuseStep 1945455 = 2918183) B2918183
theorem B2918189 : Blo 1945435 2918189 := bbase (se 3 (by rfl) ⟨547160, by rfl⟩ : syracuseStep 2918189 = 1094321) (by norm_num)
theorem B1945459 : Blo 1945435 1945459 := bstep (se 1 (by rfl) ⟨1459094, by rfl⟩ : syracuseStep 1945459 = 2918189) B2918189
theorem B4377293 : Blo 1945435 4377293 := bbase (se 3 (by rfl) ⟨820742, by rfl⟩ : syracuseStep 4377293 = 1641485) (by norm_num)
theorem B2918195 : Blo 1945435 2918195 := bstep (se 1 (by rfl) ⟨2188646, by rfl⟩ : syracuseStep 2918195 = 4377293) B4377293
theorem B1945463 : Blo 1945435 1945463 := bstep (se 1 (by rfl) ⟨1459097, by rfl⟩ : syracuseStep 1945463 = 2918195) B2918195
theorem B2462233 : Blo 1945435 2462233 := bbase (se 2 (by rfl) ⟨923337, by rfl⟩ : syracuseStep 2462233 = 1846675) (by norm_num)
theorem B3282977 : Blo 1945435 3282977 := bstep (se 2 (by rfl) ⟨1231116, by rfl⟩ : syracuseStep 3282977 = 2462233) B2462233
theorem B2188651 : Blo 1945435 2188651 := bstep (se 1 (by rfl) ⟨1641488, by rfl⟩ : syracuseStep 2188651 = 3282977) B3282977
theorem B2918201 : Blo 1945435 2918201 := bstep (se 2 (by rfl) ⟨1094325, by rfl⟩ : syracuseStep 2918201 = 2188651) B2188651
theorem B1945467 : Blo 1945435 1945467 := bstep (se 1 (by rfl) ⟨1459100, by rfl⟩ : syracuseStep 1945467 = 2918201) B2918201
theorem B8310053 : Blo 1945435 8310053 := bbase (se 4 (by rfl) ⟨779067, by rfl⟩ : syracuseStep 8310053 = 1558135) (by norm_num)
theorem B22160141 : Blo 1945435 22160141 := bstep (se 3 (by rfl) ⟨4155026, by rfl⟩ : syracuseStep 22160141 = 8310053) B8310053
theorem B14773427 : Blo 1945435 14773427 := bstep (se 1 (by rfl) ⟨11080070, by rfl⟩ : syracuseStep 14773427 = 22160141) B22160141
theorem B9848951 : Blo 1945435 9848951 := bstep (se 1 (by rfl) ⟨7386713, by rfl⟩ : syracuseStep 9848951 = 14773427) B14773427
theorem B6565967 : Blo 1945435 6565967 := bstep (se 1 (by rfl) ⟨4924475, by rfl⟩ : syracuseStep 6565967 = 9848951) B9848951
theorem B4377311 : Blo 1945435 4377311 := bstep (se 1 (by rfl) ⟨3282983, by rfl⟩ : syracuseStep 4377311 = 6565967) B6565967
theorem B2918207 : Blo 1945435 2918207 := bstep (se 1 (by rfl) ⟨2188655, by rfl⟩ : syracuseStep 2918207 = 4377311) B4377311
theorem B1945471 : Blo 1945435 1945471 := bstep (se 1 (by rfl) ⟨1459103, by rfl⟩ : syracuseStep 1945471 = 2918207) B2918207
theorem B2918213 : Blo 1945435 2918213 := bbase (se 4 (by rfl) ⟨273582, by rfl⟩ : syracuseStep 2918213 = 547165) (by norm_num)
theorem B1945475 : Blo 1945435 1945475 := bstep (se 1 (by rfl) ⟨1459106, by rfl⟩ : syracuseStep 1945475 = 2918213) B2918213
theorem B3282997 : Blo 1945435 3282997 := bbase (se 5 (by rfl) ⟨153890, by rfl⟩ : syracuseStep 3282997 = 307781) (by norm_num)
theorem B4377329 : Blo 1945435 4377329 := bstep (se 2 (by rfl) ⟨1641498, by rfl⟩ : syracuseStep 4377329 = 3282997) B3282997
theorem B2918219 : Blo 1945435 2918219 := bstep (se 1 (by rfl) ⟨2188664, by rfl⟩ : syracuseStep 2918219 = 4377329) B4377329
theorem B1945479 : Blo 1945435 1945479 := bstep (se 1 (by rfl) ⟨1459109, by rfl⟩ : syracuseStep 1945479 = 2918219) B2918219
theorem B2188669 : Blo 1945435 2188669 := bbase (se 3 (by rfl) ⟨410375, by rfl⟩ : syracuseStep 2188669 = 820751) (by norm_num)
theorem B2918225 : Blo 1945435 2918225 := bstep (se 2 (by rfl) ⟨1094334, by rfl⟩ : syracuseStep 2918225 = 2188669) B2188669
theorem B1945483 : Blo 1945435 1945483 := bstep (se 1 (by rfl) ⟨1459112, by rfl⟩ : syracuseStep 1945483 = 2918225) B2918225
theorem B6566021 : Blo 1945435 6566021 := bbase (se 4 (by rfl) ⟨615564, by rfl⟩ : syracuseStep 6566021 = 1231129) (by norm_num)
theorem B4377347 : Blo 1945435 4377347 := bstep (se 1 (by rfl) ⟨3283010, by rfl⟩ : syracuseStep 4377347 = 6566021) B6566021
theorem B2918231 : Blo 1945435 2918231 := bstep (se 1 (by rfl) ⟨2188673, by rfl⟩ : syracuseStep 2918231 = 4377347) B4377347
theorem B1945487 : Blo 1945435 1945487 := bstep (se 1 (by rfl) ⟨1459115, by rfl⟩ : syracuseStep 1945487 = 2918231) B2918231
theorem B2918237 : Blo 1945435 2918237 := bbase (se 3 (by rfl) ⟨547169, by rfl⟩ : syracuseStep 2918237 = 1094339) (by norm_num)
theorem B1945491 : Blo 1945435 1945491 := bstep (se 1 (by rfl) ⟨1459118, by rfl⟩ : syracuseStep 1945491 = 2918237) B2918237
theorem B4377365 : Blo 1945435 4377365 := bbase (se 6 (by rfl) ⟨102594, by rfl⟩ : syracuseStep 4377365 = 205189) (by norm_num)
theorem B2918243 : Blo 1945435 2918243 := bstep (se 1 (by rfl) ⟨2188682, by rfl⟩ : syracuseStep 2918243 = 4377365) B4377365
theorem B1945495 : Blo 1945435 1945495 := bstep (se 1 (by rfl) ⟨1459121, by rfl⟩ : syracuseStep 1945495 = 2918243) B2918243
theorem B7386821 : Blo 1945435 7386821 := bbase (se 4 (by rfl) ⟨692514, by rfl⟩ : syracuseStep 7386821 = 1385029) (by norm_num)
theorem B4924547 : Blo 1945435 4924547 := bstep (se 1 (by rfl) ⟨3693410, by rfl⟩ : syracuseStep 4924547 = 7386821) B7386821
theorem B3283031 : Blo 1945435 3283031 := bstep (se 1 (by rfl) ⟨2462273, by rfl⟩ : syracuseStep 3283031 = 4924547) B4924547
theorem B2188687 : Blo 1945435 2188687 := bstep (se 1 (by rfl) ⟨1641515, by rfl⟩ : syracuseStep 2188687 = 3283031) B3283031
theorem B2918249 : Blo 1945435 2918249 := bstep (se 2 (by rfl) ⟨1094343, by rfl⟩ : syracuseStep 2918249 = 2188687) B2188687
theorem B1945499 : Blo 1945435 1945499 := bstep (se 1 (by rfl) ⟨1459124, by rfl⟩ : syracuseStep 1945499 = 2918249) B2918249
theorem B9348965 : Blo 1945435 9348965 := bbase (se 4 (by rfl) ⟨876465, by rfl⟩ : syracuseStep 9348965 = 1752931) (by norm_num)
theorem B6232643 : Blo 1945435 6232643 := bstep (se 1 (by rfl) ⟨4674482, by rfl⟩ : syracuseStep 6232643 = 9348965) B9348965
theorem B4155095 : Blo 1945435 4155095 := bstep (se 1 (by rfl) ⟨3116321, by rfl⟩ : syracuseStep 4155095 = 6232643) B6232643
theorem B11080253 : Blo 1945435 11080253 := bstep (se 3 (by rfl) ⟨2077547, by rfl⟩ : syracuseStep 11080253 = 4155095) B4155095
theorem B7386835 : Blo 1945435 7386835 := bstep (se 1 (by rfl) ⟨5540126, by rfl⟩ : syracuseStep 7386835 = 11080253) B11080253
theorem B9849113 : Blo 1945435 9849113 := bstep (se 2 (by rfl) ⟨3693417, by rfl⟩ : syracuseStep 9849113 = 7386835) B7386835
theorem B6566075 : Blo 1945435 6566075 := bstep (se 1 (by rfl) ⟨4924556, by rfl⟩ : syracuseStep 6566075 = 9849113) B9849113
theorem B4377383 : Blo 1945435 4377383 := bstep (se 1 (by rfl) ⟨3283037, by rfl⟩ : syracuseStep 4377383 = 6566075) B6566075
theorem B2918255 : Blo 1945435 2918255 := bstep (se 1 (by rfl) ⟨2188691, by rfl⟩ : syracuseStep 2918255 = 4377383) B4377383
theorem B1945503 : Blo 1945435 1945503 := bstep (se 1 (by rfl) ⟨1459127, by rfl⟩ : syracuseStep 1945503 = 2918255) B2918255
theorem B2918261 : Blo 1945435 2918261 := bbase (se 5 (by rfl) ⟨136793, by rfl⟩ : syracuseStep 2918261 = 273587) (by norm_num)
theorem B1945507 : Blo 1945435 1945507 := bstep (se 1 (by rfl) ⟨1459130, by rfl⟩ : syracuseStep 1945507 = 2918261) B2918261
theorem B7487653 : Blo 1945435 7487653 := bbase (se 4 (by rfl) ⟨701967, by rfl⟩ : syracuseStep 7487653 = 1403935) (by norm_num)
theorem B9983537 : Blo 1945435 9983537 := bstep (se 2 (by rfl) ⟨3743826, by rfl⟩ : syracuseStep 9983537 = 7487653) B7487653
theorem B6655691 : Blo 1945435 6655691 := bstep (se 1 (by rfl) ⟨4991768, by rfl⟩ : syracuseStep 6655691 = 9983537) B9983537
theorem B4437127 : Blo 1945435 4437127 := bstep (se 1 (by rfl) ⟨3327845, by rfl⟩ : syracuseStep 4437127 = 6655691) B6655691
theorem B5916169 : Blo 1945435 5916169 := bstep (se 2 (by rfl) ⟨2218563, by rfl⟩ : syracuseStep 5916169 = 4437127) B4437127
theorem B7888225 : Blo 1945435 7888225 := bstep (se 2 (by rfl) ⟨2958084, by rfl⟩ : syracuseStep 7888225 = 5916169) B5916169
theorem B10517633 : Blo 1945435 10517633 := bstep (se 2 (by rfl) ⟨3944112, by rfl⟩ : syracuseStep 10517633 = 7888225) B7888225
theorem B7011755 : Blo 1945435 7011755 := bstep (se 1 (by rfl) ⟨5258816, by rfl⟩ : syracuseStep 7011755 = 10517633) B10517633
theorem B4674503 : Blo 1945435 4674503 := bstep (se 1 (by rfl) ⟨3505877, by rfl⟩ : syracuseStep 4674503 = 7011755) B7011755
theorem B3116335 : Blo 1945435 3116335 := bstep (se 1 (by rfl) ⟨2337251, by rfl⟩ : syracuseStep 3116335 = 4674503) B4674503
theorem B4155113 : Blo 1945435 4155113 := bstep (se 2 (by rfl) ⟨1558167, by rfl⟩ : syracuseStep 4155113 = 3116335) B3116335
theorem B2770075 : Blo 1945435 2770075 := bstep (se 1 (by rfl) ⟨2077556, by rfl⟩ : syracuseStep 2770075 = 4155113) B4155113
theorem B3693433 : Blo 1945435 3693433 := bstep (se 2 (by rfl) ⟨1385037, by rfl⟩ : syracuseStep 3693433 = 2770075) B2770075
theorem B4924577 : Blo 1945435 4924577 := bstep (se 2 (by rfl) ⟨1846716, by rfl⟩ : syracuseStep 4924577 = 3693433) B3693433
theorem B3283051 : Blo 1945435 3283051 := bstep (se 1 (by rfl) ⟨2462288, by rfl⟩ : syracuseStep 3283051 = 4924577) B4924577
theorem B4377401 : Blo 1945435 4377401 := bstep (se 2 (by rfl) ⟨1641525, by rfl⟩ : syracuseStep 4377401 = 3283051) B3283051
theorem B2918267 : Blo 1945435 2918267 := bstep (se 1 (by rfl) ⟨2188700, by rfl⟩ : syracuseStep 2918267 = 4377401) B4377401
theorem B1945511 : Blo 1945435 1945511 := bstep (se 1 (by rfl) ⟨1459133, by rfl⟩ : syracuseStep 1945511 = 2918267) B2918267
theorem B2188705 : Blo 1945435 2188705 := bbase (se 2 (by rfl) ⟨820764, by rfl⟩ : syracuseStep 2188705 = 1641529) (by norm_num)
theorem B2918273 : Blo 1945435 2918273 := bstep (se 2 (by rfl) ⟨1094352, by rfl⟩ : syracuseStep 2918273 = 2188705) B2188705
theorem B1945515 : Blo 1945435 1945515 := bstep (se 1 (by rfl) ⟨1459136, by rfl⟩ : syracuseStep 1945515 = 2918273) B2918273
theorem B4924597 : Blo 1945435 4924597 := bbase (se 5 (by rfl) ⟨230840, by rfl⟩ : syracuseStep 4924597 = 461681) (by norm_num)
theorem B6566129 : Blo 1945435 6566129 := bstep (se 2 (by rfl) ⟨2462298, by rfl⟩ : syracuseStep 6566129 = 4924597) B4924597
theorem B4377419 : Blo 1945435 4377419 := bstep (se 1 (by rfl) ⟨3283064, by rfl⟩ : syracuseStep 4377419 = 6566129) B6566129
theorem B2918279 : Blo 1945435 2918279 := bstep (se 1 (by rfl) ⟨2188709, by rfl⟩ : syracuseStep 2918279 = 4377419) B4377419
theorem B1945519 : Blo 1945435 1945519 := bstep (se 1 (by rfl) ⟨1459139, by rfl⟩ : syracuseStep 1945519 = 2918279) B2918279
theorem B2918285 : Blo 1945435 2918285 := bbase (se 3 (by rfl) ⟨547178, by rfl⟩ : syracuseStep 2918285 = 1094357) (by norm_num)
theorem B1945523 : Blo 1945435 1945523 := bstep (se 1 (by rfl) ⟨1459142, by rfl⟩ : syracuseStep 1945523 = 2918285) B2918285
theorem B4377437 : Blo 1945435 4377437 := bbase (se 3 (by rfl) ⟨820769, by rfl⟩ : syracuseStep 4377437 = 1641539) (by norm_num)
theorem B2918291 : Blo 1945435 2918291 := bstep (se 1 (by rfl) ⟨2188718, by rfl⟩ : syracuseStep 2918291 = 4377437) B4377437
theorem B1945527 : Blo 1945435 1945527 := bstep (se 1 (by rfl) ⟨1459145, by rfl⟩ : syracuseStep 1945527 = 2918291) B2918291
theorem B3283085 : Blo 1945435 3283085 := bbase (se 3 (by rfl) ⟨615578, by rfl⟩ : syracuseStep 3283085 = 1231157) (by norm_num)
theorem B2188723 : Blo 1945435 2188723 := bstep (se 1 (by rfl) ⟨1641542, by rfl⟩ : syracuseStep 2188723 = 3283085) B3283085
theorem B2918297 : Blo 1945435 2918297 := bstep (se 2 (by rfl) ⟨1094361, by rfl⟩ : syracuseStep 2918297 = 2188723) B2188723
theorem B1945531 : Blo 1945435 1945531 := bstep (se 1 (by rfl) ⟨1459148, by rfl⟩ : syracuseStep 1945531 = 2918297) B2918297
theorem B147881045 : Blo 1945435 147881045 := bbase (se 8 (by rfl) ⟨866490, by rfl⟩ : syracuseStep 147881045 = 1732981) (by norm_num)
theorem B98587363 : Blo 1945435 98587363 := bstep (se 1 (by rfl) ⟨73940522, by rfl⟩ : syracuseStep 98587363 = 147881045) B147881045
theorem B131449817 : Blo 1945435 131449817 := bstep (se 2 (by rfl) ⟨49293681, by rfl⟩ : syracuseStep 131449817 = 98587363) B98587363
theorem B87633211 : Blo 1945435 87633211 := bstep (se 1 (by rfl) ⟨65724908, by rfl⟩ : syracuseStep 87633211 = 131449817) B131449817
theorem B116844281 : Blo 1945435 116844281 := bstep (se 2 (by rfl) ⟨43816605, by rfl⟩ : syracuseStep 116844281 = 87633211) B87633211
theorem B77896187 : Blo 1945435 77896187 := bstep (se 1 (by rfl) ⟨58422140, by rfl⟩ : syracuseStep 77896187 = 116844281) B116844281
theorem B51930791 : Blo 1945435 51930791 := bstep (se 1 (by rfl) ⟨38948093, by rfl⟩ : syracuseStep 51930791 = 77896187) B77896187
theorem B34620527 : Blo 1945435 34620527 := bstep (se 1 (by rfl) ⟨25965395, by rfl⟩ : syracuseStep 34620527 = 51930791) B51930791
theorem B23080351 : Blo 1945435 23080351 := bstep (se 1 (by rfl) ⟨17310263, by rfl⟩ : syracuseStep 23080351 = 34620527) B34620527
theorem B30773801 : Blo 1945435 30773801 := bstep (se 2 (by rfl) ⟨11540175, by rfl⟩ : syracuseStep 30773801 = 23080351) B23080351
theorem B82063469 : Blo 1945435 82063469 := bstep (se 3 (by rfl) ⟨15386900, by rfl⟩ : syracuseStep 82063469 = 30773801) B30773801
theorem B54708979 : Blo 1945435 54708979 := bstep (se 1 (by rfl) ⟨41031734, by rfl⟩ : syracuseStep 54708979 = 82063469) B82063469
theorem B72945305 : Blo 1945435 72945305 := bstep (se 2 (by rfl) ⟨27354489, by rfl⟩ : syracuseStep 72945305 = 54708979) B54708979
theorem B48630203 : Blo 1945435 48630203 := bstep (se 1 (by rfl) ⟨36472652, by rfl⟩ : syracuseStep 48630203 = 72945305) B72945305
theorem B32420135 : Blo 1945435 32420135 := bstep (se 1 (by rfl) ⟨24315101, by rfl⟩ : syracuseStep 32420135 = 48630203) B48630203
theorem B21613423 : Blo 1945435 21613423 := bstep (se 1 (by rfl) ⟨16210067, by rfl⟩ : syracuseStep 21613423 = 32420135) B32420135
theorem B28817897 : Blo 1945435 28817897 := bstep (se 2 (by rfl) ⟨10806711, by rfl⟩ : syracuseStep 28817897 = 21613423) B21613423
theorem B76847725 : Blo 1945435 76847725 := bstep (se 3 (by rfl) ⟨14408948, by rfl⟩ : syracuseStep 76847725 = 28817897) B28817897
theorem B102463633 : Blo 1945435 102463633 := bstep (se 2 (by rfl) ⟨38423862, by rfl⟩ : syracuseStep 102463633 = 76847725) B76847725
theorem B136618177 : Blo 1945435 136618177 := bstep (se 2 (by rfl) ⟨51231816, by rfl⟩ : syracuseStep 136618177 = 102463633) B102463633
theorem B182157569 : Blo 1945435 182157569 := bstep (se 2 (by rfl) ⟨68309088, by rfl⟩ : syracuseStep 182157569 = 136618177) B136618177
theorem B121438379 : Blo 1945435 121438379 := bstep (se 1 (by rfl) ⟨91078784, by rfl⟩ : syracuseStep 121438379 = 182157569) B182157569
theorem B80958919 : Blo 1945435 80958919 := bstep (se 1 (by rfl) ⟨60719189, by rfl⟩ : syracuseStep 80958919 = 121438379) B121438379
theorem B107945225 : Blo 1945435 107945225 := bstep (se 2 (by rfl) ⟨40479459, by rfl⟩ : syracuseStep 107945225 = 80958919) B80958919
theorem B71963483 : Blo 1945435 71963483 := bstep (se 1 (by rfl) ⟨53972612, by rfl⟩ : syracuseStep 71963483 = 107945225) B107945225
theorem B191902621 : Blo 1945435 191902621 := bstep (se 3 (by rfl) ⟨35981741, by rfl⟩ : syracuseStep 191902621 = 71963483) B71963483
theorem B255870161 : Blo 1945435 255870161 := bstep (se 2 (by rfl) ⟨95951310, by rfl⟩ : syracuseStep 255870161 = 191902621) B191902621
theorem B170580107 : Blo 1945435 170580107 := bstep (se 1 (by rfl) ⟨127935080, by rfl⟩ : syracuseStep 170580107 = 255870161) B255870161
theorem B113720071 : Blo 1945435 113720071 := bstep (se 1 (by rfl) ⟨85290053, by rfl⟩ : syracuseStep 113720071 = 170580107) B170580107
theorem B151626761 : Blo 1945435 151626761 := bstep (se 2 (by rfl) ⟨56860035, by rfl⟩ : syracuseStep 151626761 = 113720071) B113720071
theorem B101084507 : Blo 1945435 101084507 := bstep (se 1 (by rfl) ⟨75813380, by rfl⟩ : syracuseStep 101084507 = 151626761) B151626761
theorem B67389671 : Blo 1945435 67389671 := bstep (se 1 (by rfl) ⟨50542253, by rfl⟩ : syracuseStep 67389671 = 101084507) B101084507
theorem B179705789 : Blo 1945435 179705789 := bstep (se 3 (by rfl) ⟨33694835, by rfl⟩ : syracuseStep 179705789 = 67389671) B67389671
theorem B119803859 : Blo 1945435 119803859 := bstep (se 1 (by rfl) ⟨89852894, by rfl⟩ : syracuseStep 119803859 = 179705789) B179705789
theorem B79869239 : Blo 1945435 79869239 := bstep (se 1 (by rfl) ⟨59901929, by rfl⟩ : syracuseStep 79869239 = 119803859) B119803859
theorem B53246159 : Blo 1945435 53246159 := bstep (se 1 (by rfl) ⟨39934619, by rfl⟩ : syracuseStep 53246159 = 79869239) B79869239
theorem B35497439 : Blo 1945435 35497439 := bstep (se 1 (by rfl) ⟨26623079, by rfl⟩ : syracuseStep 35497439 = 53246159) B53246159
theorem B23664959 : Blo 1945435 23664959 := bstep (se 1 (by rfl) ⟨17748719, by rfl⟩ : syracuseStep 23664959 = 35497439) B35497439
theorem B15776639 : Blo 1945435 15776639 := bstep (se 1 (by rfl) ⟨11832479, by rfl⟩ : syracuseStep 15776639 = 23664959) B23664959
theorem B10517759 : Blo 1945435 10517759 := bstep (se 1 (by rfl) ⟨7888319, by rfl⟩ : syracuseStep 10517759 = 15776639) B15776639
theorem B7011839 : Blo 1945435 7011839 := bstep (se 1 (by rfl) ⟨5258879, by rfl⟩ : syracuseStep 7011839 = 10517759) B10517759
theorem B4674559 : Blo 1945435 4674559 := bstep (se 1 (by rfl) ⟨3505919, by rfl⟩ : syracuseStep 4674559 = 7011839) B7011839
theorem B6232745 : Blo 1945435 6232745 := bstep (se 2 (by rfl) ⟨2337279, by rfl⟩ : syracuseStep 6232745 = 4674559) B4674559
theorem B16620653 : Blo 1945435 16620653 := bstep (se 3 (by rfl) ⟨3116372, by rfl⟩ : syracuseStep 16620653 = 6232745) B6232745
theorem B11080435 : Blo 1945435 11080435 := bstep (se 1 (by rfl) ⟨8310326, by rfl⟩ : syracuseStep 11080435 = 16620653) B16620653
theorem B14773913 : Blo 1945435 14773913 := bstep (se 2 (by rfl) ⟨5540217, by rfl⟩ : syracuseStep 14773913 = 11080435) B11080435
theorem B9849275 : Blo 1945435 9849275 := bstep (se 1 (by rfl) ⟨7386956, by rfl⟩ : syracuseStep 9849275 = 14773913) B14773913
theorem B6566183 : Blo 1945435 6566183 := bstep (se 1 (by rfl) ⟨4924637, by rfl⟩ : syracuseStep 6566183 = 9849275) B9849275
theorem B4377455 : Blo 1945435 4377455 := bstep (se 1 (by rfl) ⟨3283091, by rfl⟩ : syracuseStep 4377455 = 6566183) B6566183
theorem B2918303 : Blo 1945435 2918303 := bstep (se 1 (by rfl) ⟨2188727, by rfl⟩ : syracuseStep 2918303 = 4377455) B4377455
theorem B1945535 : Blo 1945435 1945535 := bstep (se 1 (by rfl) ⟨1459151, by rfl⟩ : syracuseStep 1945535 = 2918303) B2918303
theorem B2918309 : Blo 1945435 2918309 := bbase (se 4 (by rfl) ⟨273591, by rfl⟩ : syracuseStep 2918309 = 547183) (by norm_num)
theorem B1945539 : Blo 1945435 1945539 := bstep (se 1 (by rfl) ⟨1459154, by rfl⟩ : syracuseStep 1945539 = 2918309) B2918309
theorem B2462329 : Blo 1945435 2462329 := bbase (se 2 (by rfl) ⟨923373, by rfl⟩ : syracuseStep 2462329 = 1846747) (by norm_num)
theorem B3283105 : Blo 1945435 3283105 := bstep (se 2 (by rfl) ⟨1231164, by rfl⟩ : syracuseStep 3283105 = 2462329) B2462329
theorem B4377473 : Blo 1945435 4377473 := bstep (se 2 (by rfl) ⟨1641552, by rfl⟩ : syracuseStep 4377473 = 3283105) B3283105
theorem B2918315 : Blo 1945435 2918315 := bstep (se 1 (by rfl) ⟨2188736, by rfl⟩ : syracuseStep 2918315 = 4377473) B4377473
theorem B1945543 : Blo 1945435 1945543 := bstep (se 1 (by rfl) ⟨1459157, by rfl⟩ : syracuseStep 1945543 = 2918315) B2918315
theorem B2188741 : Blo 1945435 2188741 := bbase (se 4 (by rfl) ⟨205194, by rfl⟩ : syracuseStep 2188741 = 410389) (by norm_num)
theorem B2918321 : Blo 1945435 2918321 := bstep (se 2 (by rfl) ⟨1094370, by rfl⟩ : syracuseStep 2918321 = 2188741) B2188741
theorem B1945547 : Blo 1945435 1945547 := bstep (se 1 (by rfl) ⟨1459160, by rfl⟩ : syracuseStep 1945547 = 2918321) B2918321
theorem B3693509 : Blo 1945435 3693509 := bbase (se 4 (by rfl) ⟨346266, by rfl⟩ : syracuseStep 3693509 = 692533) (by norm_num)
theorem B2462339 : Blo 1945435 2462339 := bstep (se 1 (by rfl) ⟨1846754, by rfl⟩ : syracuseStep 2462339 = 3693509) B3693509
theorem B6566237 : Blo 1945435 6566237 := bstep (se 3 (by rfl) ⟨1231169, by rfl⟩ : syracuseStep 6566237 = 2462339) B2462339
theorem B4377491 : Blo 1945435 4377491 := bstep (se 1 (by rfl) ⟨3283118, by rfl⟩ : syracuseStep 4377491 = 6566237) B6566237
theorem B2918327 : Blo 1945435 2918327 := bstep (se 1 (by rfl) ⟨2188745, by rfl⟩ : syracuseStep 2918327 = 4377491) B4377491
theorem B1945551 : Blo 1945435 1945551 := bstep (se 1 (by rfl) ⟨1459163, by rfl⟩ : syracuseStep 1945551 = 2918327) B2918327
theorem B2918333 : Blo 1945435 2918333 := bbase (se 3 (by rfl) ⟨547187, by rfl⟩ : syracuseStep 2918333 = 1094375) (by norm_num)
theorem B1945555 : Blo 1945435 1945555 := bstep (se 1 (by rfl) ⟨1459166, by rfl⟩ : syracuseStep 1945555 = 2918333) B2918333
theorem B4377509 : Blo 1945435 4377509 := bbase (se 4 (by rfl) ⟨410391, by rfl⟩ : syracuseStep 4377509 = 820783) (by norm_num)
theorem B2918339 : Blo 1945435 2918339 := bstep (se 1 (by rfl) ⟨2188754, by rfl⟩ : syracuseStep 2918339 = 4377509) B4377509
theorem B1945559 : Blo 1945435 1945559 := bstep (se 1 (by rfl) ⟨1459169, by rfl⟩ : syracuseStep 1945559 = 2918339) B2918339
theorem B4924709 : Blo 1945435 4924709 := bbase (se 4 (by rfl) ⟨461691, by rfl⟩ : syracuseStep 4924709 = 923383) (by norm_num)
theorem B3283139 : Blo 1945435 3283139 := bstep (se 1 (by rfl) ⟨2462354, by rfl⟩ : syracuseStep 3283139 = 4924709) B4924709
theorem B2188759 : Blo 1945435 2188759 := bstep (se 1 (by rfl) ⟨1641569, by rfl⟩ : syracuseStep 2188759 = 3283139) B3283139
theorem B2918345 : Blo 1945435 2918345 := bstep (se 2 (by rfl) ⟨1094379, by rfl⟩ : syracuseStep 2918345 = 2188759) B2188759
theorem B1945563 : Blo 1945435 1945563 := bstep (se 1 (by rfl) ⟨1459172, by rfl⟩ : syracuseStep 1945563 = 2918345) B2918345
theorem B5540309 : Blo 1945435 5540309 := bbase (se 7 (by rfl) ⟨64925, by rfl⟩ : syracuseStep 5540309 = 129851) (by norm_num)
theorem B3693539 : Blo 1945435 3693539 := bstep (se 1 (by rfl) ⟨2770154, by rfl⟩ : syracuseStep 3693539 = 5540309) B5540309
theorem B9849437 : Blo 1945435 9849437 := bstep (se 3 (by rfl) ⟨1846769, by rfl⟩ : syracuseStep 9849437 = 3693539) B3693539
theorem B6566291 : Blo 1945435 6566291 := bstep (se 1 (by rfl) ⟨4924718, by rfl⟩ : syracuseStep 6566291 = 9849437) B9849437
theorem B4377527 : Blo 1945435 4377527 := bstep (se 1 (by rfl) ⟨3283145, by rfl⟩ : syracuseStep 4377527 = 6566291) B6566291
theorem B2918351 : Blo 1945435 2918351 := bstep (se 1 (by rfl) ⟨2188763, by rfl⟩ : syracuseStep 2918351 = 4377527) B4377527
theorem B1945567 : Blo 1945435 1945567 := bstep (se 1 (by rfl) ⟨1459175, by rfl⟩ : syracuseStep 1945567 = 2918351) B2918351
theorem B2918357 : Blo 1945435 2918357 := bbase (se 7 (by rfl) ⟨34199, by rfl⟩ : syracuseStep 2918357 = 68399) (by norm_num)
theorem B1945571 : Blo 1945435 1945571 := bstep (se 1 (by rfl) ⟨1459178, by rfl⟩ : syracuseStep 1945571 = 2918357) B2918357
theorem B7387109 : Blo 1945435 7387109 := bbase (se 4 (by rfl) ⟨692541, by rfl⟩ : syracuseStep 7387109 = 1385083) (by norm_num)
theorem B4924739 : Blo 1945435 4924739 := bstep (se 1 (by rfl) ⟨3693554, by rfl⟩ : syracuseStep 4924739 = 7387109) B7387109
theorem B3283159 : Blo 1945435 3283159 := bstep (se 1 (by rfl) ⟨2462369, by rfl⟩ : syracuseStep 3283159 = 4924739) B4924739
theorem B4377545 : Blo 1945435 4377545 := bstep (se 2 (by rfl) ⟨1641579, by rfl⟩ : syracuseStep 4377545 = 3283159) B3283159
theorem B2918363 : Blo 1945435 2918363 := bstep (se 1 (by rfl) ⟨2188772, by rfl⟩ : syracuseStep 2918363 = 4377545) B4377545
theorem B1945575 : Blo 1945435 1945575 := bstep (se 1 (by rfl) ⟨1459181, by rfl⟩ : syracuseStep 1945575 = 2918363) B2918363
theorem B2188777 : Blo 1945435 2188777 := bbase (se 2 (by rfl) ⟨820791, by rfl⟩ : syracuseStep 2188777 = 1641583) (by norm_num)
theorem B2918369 : Blo 1945435 2918369 := bstep (se 2 (by rfl) ⟨1094388, by rfl⟩ : syracuseStep 2918369 = 2188777) B2188777
theorem B1945579 : Blo 1945435 1945579 := bstep (se 1 (by rfl) ⟨1459184, by rfl⟩ : syracuseStep 1945579 = 2918369) B2918369
theorem B2077633 : Blo 1945435 2077633 := bbase (se 2 (by rfl) ⟨779112, by rfl⟩ : syracuseStep 2077633 = 1558225) (by norm_num)
theorem B11080709 : Blo 1945435 11080709 := bstep (se 4 (by rfl) ⟨1038816, by rfl⟩ : syracuseStep 11080709 = 2077633) B2077633
theorem B7387139 : Blo 1945435 7387139 := bstep (se 1 (by rfl) ⟨5540354, by rfl⟩ : syracuseStep 7387139 = 11080709) B11080709
theorem B4924759 : Blo 1945435 4924759 := bstep (se 1 (by rfl) ⟨3693569, by rfl⟩ : syracuseStep 4924759 = 7387139) B7387139
theorem B6566345 : Blo 1945435 6566345 := bstep (se 2 (by rfl) ⟨2462379, by rfl⟩ : syracuseStep 6566345 = 4924759) B4924759
theorem B4377563 : Blo 1945435 4377563 := bstep (se 1 (by rfl) ⟨3283172, by rfl⟩ : syracuseStep 4377563 = 6566345) B6566345
theorem B2918375 : Blo 1945435 2918375 := bstep (se 1 (by rfl) ⟨2188781, by rfl⟩ : syracuseStep 2918375 = 4377563) B4377563
theorem B1945583 : Blo 1945435 1945583 := bstep (se 1 (by rfl) ⟨1459187, by rfl⟩ : syracuseStep 1945583 = 2918375) B2918375
theorem B2918381 : Blo 1945435 2918381 := bbase (se 3 (by rfl) ⟨547196, by rfl⟩ : syracuseStep 2918381 = 1094393) (by norm_num)
theorem B1945587 : Blo 1945435 1945587 := bstep (se 1 (by rfl) ⟨1459190, by rfl⟩ : syracuseStep 1945587 = 2918381) B2918381
theorem B4377581 : Blo 1945435 4377581 := bbase (se 3 (by rfl) ⟨820796, by rfl⟩ : syracuseStep 4377581 = 1641593) (by norm_num)
theorem B2918387 : Blo 1945435 2918387 := bstep (se 1 (by rfl) ⟨2188790, by rfl⟩ : syracuseStep 2918387 = 4377581) B4377581
theorem B1945591 : Blo 1945435 1945591 := bstep (se 1 (by rfl) ⟨1459193, by rfl⟩ : syracuseStep 1945591 = 2918387) B2918387
theorem B4155293 : Blo 1945435 4155293 := bbase (se 3 (by rfl) ⟨779117, by rfl⟩ : syracuseStep 4155293 = 1558235) (by norm_num)
theorem B2770195 : Blo 1945435 2770195 := bstep (se 1 (by rfl) ⟨2077646, by rfl⟩ : syracuseStep 2770195 = 4155293) B4155293
theorem B3693593 : Blo 1945435 3693593 := bstep (se 2 (by rfl) ⟨1385097, by rfl⟩ : syracuseStep 3693593 = 2770195) B2770195
theorem B2462395 : Blo 1945435 2462395 := bstep (se 1 (by rfl) ⟨1846796, by rfl⟩ : syracuseStep 2462395 = 3693593) B3693593
theorem B3283193 : Blo 1945435 3283193 := bstep (se 2 (by rfl) ⟨1231197, by rfl⟩ : syracuseStep 3283193 = 2462395) B2462395
theorem B2188795 : Blo 1945435 2188795 := bstep (se 1 (by rfl) ⟨1641596, by rfl⟩ : syracuseStep 2188795 = 3283193) B3283193
theorem B2918393 : Blo 1945435 2918393 := bstep (se 2 (by rfl) ⟨1094397, by rfl⟩ : syracuseStep 2918393 = 2188795) B2188795
theorem B1945595 : Blo 1945435 1945595 := bstep (se 1 (by rfl) ⟨1459196, by rfl⟩ : syracuseStep 1945595 = 2918393) B2918393
theorem B4437325 : Blo 1945435 4437325 := bbase (se 3 (by rfl) ⟨831998, by rfl⟩ : syracuseStep 4437325 = 1663997) (by norm_num)
theorem B5916433 : Blo 1945435 5916433 := bstep (se 2 (by rfl) ⟨2218662, by rfl⟩ : syracuseStep 5916433 = 4437325) B4437325
theorem B126217237 : Blo 1945435 126217237 := bstep (se 6 (by rfl) ⟨2958216, by rfl⟩ : syracuseStep 126217237 = 5916433) B5916433
theorem B168289649 : Blo 1945435 168289649 := bstep (se 2 (by rfl) ⟨63108618, by rfl⟩ : syracuseStep 168289649 = 126217237) B126217237
theorem B112193099 : Blo 1945435 112193099 := bstep (se 1 (by rfl) ⟨84144824, by rfl⟩ : syracuseStep 112193099 = 168289649) B168289649
theorem B74795399 : Blo 1945435 74795399 := bstep (se 1 (by rfl) ⟨56096549, by rfl⟩ : syracuseStep 74795399 = 112193099) B112193099
theorem B49863599 : Blo 1945435 49863599 := bstep (se 1 (by rfl) ⟨37397699, by rfl⟩ : syracuseStep 49863599 = 74795399) B74795399
theorem B33242399 : Blo 1945435 33242399 := bstep (se 1 (by rfl) ⟨24931799, by rfl⟩ : syracuseStep 33242399 = 49863599) B49863599
theorem B22161599 : Blo 1945435 22161599 := bstep (se 1 (by rfl) ⟨16621199, by rfl⟩ : syracuseStep 22161599 = 33242399) B33242399
theorem B14774399 : Blo 1945435 14774399 := bstep (se 1 (by rfl) ⟨11080799, by rfl⟩ : syracuseStep 14774399 = 22161599) B22161599
theorem B9849599 : Blo 1945435 9849599 := bstep (se 1 (by rfl) ⟨7387199, by rfl⟩ : syracuseStep 9849599 = 14774399) B14774399
theorem B6566399 : Blo 1945435 6566399 := bstep (se 1 (by rfl) ⟨4924799, by rfl⟩ : syracuseStep 6566399 = 9849599) B9849599
theorem B4377599 : Blo 1945435 4377599 := bstep (se 1 (by rfl) ⟨3283199, by rfl⟩ : syracuseStep 4377599 = 6566399) B6566399
theorem B2918399 : Blo 1945435 2918399 := bstep (se 1 (by rfl) ⟨2188799, by rfl⟩ : syracuseStep 2918399 = 4377599) B4377599
theorem B1945599 : Blo 1945435 1945599 := bstep (se 1 (by rfl) ⟨1459199, by rfl⟩ : syracuseStep 1945599 = 2918399) B2918399
theorem B2918405 : Blo 1945435 2918405 := bbase (se 4 (by rfl) ⟨273600, by rfl⟩ : syracuseStep 2918405 = 547201) (by norm_num)
theorem B1945603 : Blo 1945435 1945603 := bstep (se 1 (by rfl) ⟨1459202, by rfl⟩ : syracuseStep 1945603 = 2918405) B2918405
theorem B3283213 : Blo 1945435 3283213 := bbase (se 3 (by rfl) ⟨615602, by rfl⟩ : syracuseStep 3283213 = 1231205) (by norm_num)
theorem B4377617 : Blo 1945435 4377617 := bstep (se 2 (by rfl) ⟨1641606, by rfl⟩ : syracuseStep 4377617 = 3283213) B3283213
theorem B2918411 : Blo 1945435 2918411 := bstep (se 1 (by rfl) ⟨2188808, by rfl⟩ : syracuseStep 2918411 = 4377617) B4377617
theorem B1945607 : Blo 1945435 1945607 := bstep (se 1 (by rfl) ⟨1459205, by rfl⟩ : syracuseStep 1945607 = 2918411) B2918411
theorem B2188813 : Blo 1945435 2188813 := bbase (se 3 (by rfl) ⟨410402, by rfl⟩ : syracuseStep 2188813 = 820805) (by norm_num)
theorem B2918417 : Blo 1945435 2918417 := bstep (se 2 (by rfl) ⟨1094406, by rfl⟩ : syracuseStep 2918417 = 2188813) B2188813
theorem B1945611 : Blo 1945435 1945611 := bstep (se 1 (by rfl) ⟨1459208, by rfl⟩ : syracuseStep 1945611 = 2918417) B2918417
theorem B6566453 : Blo 1945435 6566453 := bbase (se 5 (by rfl) ⟨307802, by rfl⟩ : syracuseStep 6566453 = 615605) (by norm_num)
theorem B4377635 : Blo 1945435 4377635 := bstep (se 1 (by rfl) ⟨3283226, by rfl⟩ : syracuseStep 4377635 = 6566453) B6566453
theorem B2918423 : Blo 1945435 2918423 := bstep (se 1 (by rfl) ⟨2188817, by rfl⟩ : syracuseStep 2918423 = 4377635) B4377635
theorem B1945615 : Blo 1945435 1945615 := bstep (se 1 (by rfl) ⟨1459211, by rfl⟩ : syracuseStep 1945615 = 2918423) B2918423
theorem B2918429 : Blo 1945435 2918429 := bbase (se 3 (by rfl) ⟨547205, by rfl⟩ : syracuseStep 2918429 = 1094411) (by norm_num)
theorem B1945619 : Blo 1945435 1945619 := bstep (se 1 (by rfl) ⟨1459214, by rfl⟩ : syracuseStep 1945619 = 2918429) B2918429
theorem B4377653 : Blo 1945435 4377653 := bbase (se 5 (by rfl) ⟨205202, by rfl⟩ : syracuseStep 4377653 = 410405) (by norm_num)
theorem B2918435 : Blo 1945435 2918435 := bstep (se 1 (by rfl) ⟨2188826, by rfl⟩ : syracuseStep 2918435 = 4377653) B4377653
theorem B1945623 : Blo 1945435 1945623 := bstep (se 1 (by rfl) ⟨1459217, by rfl⟩ : syracuseStep 1945623 = 2918435) B2918435
theorem B4674781 : Blo 1945435 4674781 := bbase (se 3 (by rfl) ⟨876521, by rfl⟩ : syracuseStep 4674781 = 1753043) (by norm_num)
theorem B6233041 : Blo 1945435 6233041 := bstep (se 2 (by rfl) ⟨2337390, by rfl⟩ : syracuseStep 6233041 = 4674781) B4674781
theorem B8310721 : Blo 1945435 8310721 := bstep (se 2 (by rfl) ⟨3116520, by rfl⟩ : syracuseStep 8310721 = 6233041) B6233041
theorem B11080961 : Blo 1945435 11080961 := bstep (se 2 (by rfl) ⟨4155360, by rfl⟩ : syracuseStep 11080961 = 8310721) B8310721
theorem B7387307 : Blo 1945435 7387307 := bstep (se 1 (by rfl) ⟨5540480, by rfl⟩ : syracuseStep 7387307 = 11080961) B11080961
theorem B4924871 : Blo 1945435 4924871 := bstep (se 1 (by rfl) ⟨3693653, by rfl⟩ : syracuseStep 4924871 = 7387307) B7387307
theorem B3283247 : Blo 1945435 3283247 := bstep (se 1 (by rfl) ⟨2462435, by rfl⟩ : syracuseStep 3283247 = 4924871) B4924871
theorem B2188831 : Blo 1945435 2188831 := bstep (se 1 (by rfl) ⟨1641623, by rfl⟩ : syracuseStep 2188831 = 3283247) B3283247
theorem B2918441 : Blo 1945435 2918441 := bstep (se 2 (by rfl) ⟨1094415, by rfl⟩ : syracuseStep 2918441 = 2188831) B2188831
theorem B1945627 : Blo 1945435 1945627 := bstep (se 1 (by rfl) ⟨1459220, by rfl⟩ : syracuseStep 1945627 = 2918441) B2918441
theorem B3506093 : Blo 1945435 3506093 := bbase (se 3 (by rfl) ⟨657392, by rfl⟩ : syracuseStep 3506093 = 1314785) (by norm_num)
theorem B2337395 : Blo 1945435 2337395 := bstep (se 1 (by rfl) ⟨1753046, by rfl⟩ : syracuseStep 2337395 = 3506093) B3506093
theorem B6233053 : Blo 1945435 6233053 := bstep (se 3 (by rfl) ⟨1168697, by rfl⟩ : syracuseStep 6233053 = 2337395) B2337395
theorem B8310737 : Blo 1945435 8310737 := bstep (se 2 (by rfl) ⟨3116526, by rfl⟩ : syracuseStep 8310737 = 6233053) B6233053
theorem B5540491 : Blo 1945435 5540491 := bstep (se 1 (by rfl) ⟨4155368, by rfl⟩ : syracuseStep 5540491 = 8310737) B8310737
theorem B7387321 : Blo 1945435 7387321 := bstep (se 2 (by rfl) ⟨2770245, by rfl⟩ : syracuseStep 7387321 = 5540491) B5540491
theorem B9849761 : Blo 1945435 9849761 := bstep (se 2 (by rfl) ⟨3693660, by rfl⟩ : syracuseStep 9849761 = 7387321) B7387321
theorem B6566507 : Blo 1945435 6566507 := bstep (se 1 (by rfl) ⟨4924880, by rfl⟩ : syracuseStep 6566507 = 9849761) B9849761
theorem B4377671 : Blo 1945435 4377671 := bstep (se 1 (by rfl) ⟨3283253, by rfl⟩ : syracuseStep 4377671 = 6566507) B6566507
theorem B2918447 : Blo 1945435 2918447 := bstep (se 1 (by rfl) ⟨2188835, by rfl⟩ : syracuseStep 2918447 = 4377671) B4377671
theorem B1945631 : Blo 1945435 1945631 := bstep (se 1 (by rfl) ⟨1459223, by rfl⟩ : syracuseStep 1945631 = 2918447) B2918447
theorem B2918453 : Blo 1945435 2918453 := bbase (se 5 (by rfl) ⟨136802, by rfl⟩ : syracuseStep 2918453 = 273605) (by norm_num)
theorem B1945635 : Blo 1945435 1945635 := bstep (se 1 (by rfl) ⟨1459226, by rfl⟩ : syracuseStep 1945635 = 2918453) B2918453
theorem B4924901 : Blo 1945435 4924901 := bbase (se 4 (by rfl) ⟨461709, by rfl⟩ : syracuseStep 4924901 = 923419) (by norm_num)
theorem B3283267 : Blo 1945435 3283267 := bstep (se 1 (by rfl) ⟨2462450, by rfl⟩ : syracuseStep 3283267 = 4924901) B4924901
theorem B4377689 : Blo 1945435 4377689 := bstep (se 2 (by rfl) ⟨1641633, by rfl⟩ : syracuseStep 4377689 = 3283267) B3283267
theorem B2918459 : Blo 1945435 2918459 := bstep (se 1 (by rfl) ⟨2188844, by rfl⟩ : syracuseStep 2918459 = 4377689) B4377689
theorem B1945639 : Blo 1945435 1945639 := bstep (se 1 (by rfl) ⟨1459229, by rfl⟩ : syracuseStep 1945639 = 2918459) B2918459
theorem B2188849 : Blo 1945435 2188849 := bbase (se 2 (by rfl) ⟨820818, by rfl⟩ : syracuseStep 2188849 = 1641637) (by norm_num)
theorem B2918465 : Blo 1945435 2918465 := bstep (se 2 (by rfl) ⟨1094424, by rfl⟩ : syracuseStep 2918465 = 2188849) B2188849
theorem B1945643 : Blo 1945435 1945643 := bstep (se 1 (by rfl) ⟨1459232, by rfl⟩ : syracuseStep 1945643 = 2918465) B2918465
theorem B4674829 : Blo 1945435 4674829 := bbase (se 3 (by rfl) ⟨876530, by rfl⟩ : syracuseStep 4674829 = 1753061) (by norm_num)
theorem B6233105 : Blo 1945435 6233105 := bstep (se 2 (by rfl) ⟨2337414, by rfl⟩ : syracuseStep 6233105 = 4674829) B4674829
theorem B4155403 : Blo 1945435 4155403 := bstep (se 1 (by rfl) ⟨3116552, by rfl⟩ : syracuseStep 4155403 = 6233105) B6233105
theorem B5540537 : Blo 1945435 5540537 := bstep (se 2 (by rfl) ⟨2077701, by rfl⟩ : syracuseStep 5540537 = 4155403) B4155403
theorem B3693691 : Blo 1945435 3693691 := bstep (se 1 (by rfl) ⟨2770268, by rfl⟩ : syracuseStep 3693691 = 5540537) B5540537
theorem B4924921 : Blo 1945435 4924921 := bstep (se 2 (by rfl) ⟨1846845, by rfl⟩ : syracuseStep 4924921 = 3693691) B3693691
theorem B6566561 : Blo 1945435 6566561 := bstep (se 2 (by rfl) ⟨2462460, by rfl⟩ : syracuseStep 6566561 = 4924921) B4924921
theorem B4377707 : Blo 1945435 4377707 := bstep (se 1 (by rfl) ⟨3283280, by rfl⟩ : syracuseStep 4377707 = 6566561) B6566561
theorem B2918471 : Blo 1945435 2918471 := bstep (se 1 (by rfl) ⟨2188853, by rfl⟩ : syracuseStep 2918471 = 4377707) B4377707
theorem B1945647 : Blo 1945435 1945647 := bstep (se 1 (by rfl) ⟨1459235, by rfl⟩ : syracuseStep 1945647 = 2918471) B2918471
theorem B2918477 : Blo 1945435 2918477 := bbase (se 3 (by rfl) ⟨547214, by rfl⟩ : syracuseStep 2918477 = 1094429) (by norm_num)
theorem B1945651 : Blo 1945435 1945651 := bstep (se 1 (by rfl) ⟨1459238, by rfl⟩ : syracuseStep 1945651 = 2918477) B2918477
theorem B4377725 : Blo 1945435 4377725 := bbase (se 3 (by rfl) ⟨820823, by rfl⟩ : syracuseStep 4377725 = 1641647) (by norm_num)
theorem B2918483 : Blo 1945435 2918483 := bstep (se 1 (by rfl) ⟨2188862, by rfl⟩ : syracuseStep 2918483 = 4377725) B4377725
theorem B1945655 : Blo 1945435 1945655 := bstep (se 1 (by rfl) ⟨1459241, by rfl⟩ : syracuseStep 1945655 = 2918483) B2918483
theorem B3283301 : Blo 1945435 3283301 := bbase (se 4 (by rfl) ⟨307809, by rfl⟩ : syracuseStep 3283301 = 615619) (by norm_num)
theorem B2188867 : Blo 1945435 2188867 := bstep (se 1 (by rfl) ⟨1641650, by rfl⟩ : syracuseStep 2188867 = 3283301) B3283301
theorem B2918489 : Blo 1945435 2918489 := bstep (se 2 (by rfl) ⟨1094433, by rfl⟩ : syracuseStep 2918489 = 2188867) B2188867
theorem B1945659 : Blo 1945435 1945659 := bstep (se 1 (by rfl) ⟨1459244, by rfl⟩ : syracuseStep 1945659 = 2918489) B2918489
theorem B4155437 : Blo 1945435 4155437 := bbase (se 3 (by rfl) ⟨779144, by rfl⟩ : syracuseStep 4155437 = 1558289) (by norm_num)
theorem B2770291 : Blo 1945435 2770291 := bstep (se 1 (by rfl) ⟨2077718, by rfl⟩ : syracuseStep 2770291 = 4155437) B4155437
theorem B14774885 : Blo 1945435 14774885 := bstep (se 4 (by rfl) ⟨1385145, by rfl⟩ : syracuseStep 14774885 = 2770291) B2770291
theorem B9849923 : Blo 1945435 9849923 := bstep (se 1 (by rfl) ⟨7387442, by rfl⟩ : syracuseStep 9849923 = 14774885) B14774885
theorem B6566615 : Blo 1945435 6566615 := bstep (se 1 (by rfl) ⟨4924961, by rfl⟩ : syracuseStep 6566615 = 9849923) B9849923
theorem B4377743 : Blo 1945435 4377743 := bstep (se 1 (by rfl) ⟨3283307, by rfl⟩ : syracuseStep 4377743 = 6566615) B6566615
theorem B2918495 : Blo 1945435 2918495 := bstep (se 1 (by rfl) ⟨2188871, by rfl⟩ : syracuseStep 2918495 = 4377743) B4377743
theorem B1945663 : Blo 1945435 1945663 := bstep (se 1 (by rfl) ⟨1459247, by rfl⟩ : syracuseStep 1945663 = 2918495) B2918495
theorem B2918501 : Blo 1945435 2918501 := bbase (se 4 (by rfl) ⟨273609, by rfl⟩ : syracuseStep 2918501 = 547219) (by norm_num)
theorem B1945667 : Blo 1945435 1945667 := bstep (se 1 (by rfl) ⟨1459250, by rfl⟩ : syracuseStep 1945667 = 2918501) B2918501
theorem B4498037 : Blo 1945435 4498037 := bbase (se 5 (by rfl) ⟨210845, by rfl⟩ : syracuseStep 4498037 = 421691) (by norm_num)
theorem B2998691 : Blo 1945435 2998691 := bstep (se 1 (by rfl) ⟨2249018, by rfl⟩ : syracuseStep 2998691 = 4498037) B4498037
theorem B1999127 : Blo 1945435 1999127 := bstep (se 1 (by rfl) ⟨1499345, by rfl⟩ : syracuseStep 1999127 = 2998691) B2998691
theorem B5331005 : Blo 1945435 5331005 := bstep (se 3 (by rfl) ⟨999563, by rfl⟩ : syracuseStep 5331005 = 1999127) B1999127
theorem B3554003 : Blo 1945435 3554003 := bstep (se 1 (by rfl) ⟨2665502, by rfl⟩ : syracuseStep 3554003 = 5331005) B5331005
theorem B2369335 : Blo 1945435 2369335 := bstep (se 1 (by rfl) ⟨1777001, by rfl⟩ : syracuseStep 2369335 = 3554003) B3554003
theorem B3159113 : Blo 1945435 3159113 := bstep (se 2 (by rfl) ⟨1184667, by rfl⟩ : syracuseStep 3159113 = 2369335) B2369335
theorem B33697205 : Blo 1945435 33697205 := bstep (se 5 (by rfl) ⟨1579556, by rfl⟩ : syracuseStep 33697205 = 3159113) B3159113
theorem B22464803 : Blo 1945435 22464803 := bstep (se 1 (by rfl) ⟨16848602, by rfl⟩ : syracuseStep 22464803 = 33697205) B33697205
theorem B14976535 : Blo 1945435 14976535 := bstep (se 1 (by rfl) ⟨11232401, by rfl⟩ : syracuseStep 14976535 = 22464803) B22464803
theorem B19968713 : Blo 1945435 19968713 := bstep (se 2 (by rfl) ⟨7488267, by rfl⟩ : syracuseStep 19968713 = 14976535) B14976535
theorem B13312475 : Blo 1945435 13312475 := bstep (se 1 (by rfl) ⟨9984356, by rfl⟩ : syracuseStep 13312475 = 19968713) B19968713
theorem B8874983 : Blo 1945435 8874983 := bstep (se 1 (by rfl) ⟨6656237, by rfl⟩ : syracuseStep 8874983 = 13312475) B13312475
theorem B5916655 : Blo 1945435 5916655 := bstep (se 1 (by rfl) ⟨4437491, by rfl⟩ : syracuseStep 5916655 = 8874983) B8874983
theorem B31555493 : Blo 1945435 31555493 := bstep (se 4 (by rfl) ⟨2958327, by rfl⟩ : syracuseStep 31555493 = 5916655) B5916655
theorem B21036995 : Blo 1945435 21036995 := bstep (se 1 (by rfl) ⟨15777746, by rfl⟩ : syracuseStep 21036995 = 31555493) B31555493
theorem B14024663 : Blo 1945435 14024663 := bstep (se 1 (by rfl) ⟨10518497, by rfl⟩ : syracuseStep 14024663 = 21036995) B21036995
theorem B9349775 : Blo 1945435 9349775 := bstep (se 1 (by rfl) ⟨7012331, by rfl⟩ : syracuseStep 9349775 = 14024663) B14024663
theorem B6233183 : Blo 1945435 6233183 := bstep (se 1 (by rfl) ⟨4674887, by rfl⟩ : syracuseStep 6233183 = 9349775) B9349775
theorem B4155455 : Blo 1945435 4155455 := bstep (se 1 (by rfl) ⟨3116591, by rfl⟩ : syracuseStep 4155455 = 6233183) B6233183
theorem B2770303 : Blo 1945435 2770303 := bstep (se 1 (by rfl) ⟨2077727, by rfl⟩ : syracuseStep 2770303 = 4155455) B4155455
theorem B3693737 : Blo 1945435 3693737 := bstep (se 2 (by rfl) ⟨1385151, by rfl⟩ : syracuseStep 3693737 = 2770303) B2770303
theorem B2462491 : Blo 1945435 2462491 := bstep (se 1 (by rfl) ⟨1846868, by rfl⟩ : syracuseStep 2462491 = 3693737) B3693737
theorem B3283321 : Blo 1945435 3283321 := bstep (se 2 (by rfl) ⟨1231245, by rfl⟩ : syracuseStep 3283321 = 2462491) B2462491
theorem B4377761 : Blo 1945435 4377761 := bstep (se 2 (by rfl) ⟨1641660, by rfl⟩ : syracuseStep 4377761 = 3283321) B3283321
theorem B2918507 : Blo 1945435 2918507 := bstep (se 1 (by rfl) ⟨2188880, by rfl⟩ : syracuseStep 2918507 = 4377761) B4377761
theorem B1945671 : Blo 1945435 1945671 := bstep (se 1 (by rfl) ⟨1459253, by rfl⟩ : syracuseStep 1945671 = 2918507) B2918507
theorem B2188885 : Blo 1945435 2188885 := bbase (se 8 (by rfl) ⟨12825, by rfl⟩ : syracuseStep 2188885 = 25651) (by norm_num)
theorem B2918513 : Blo 1945435 2918513 := bstep (se 2 (by rfl) ⟨1094442, by rfl⟩ : syracuseStep 2918513 = 2188885) B2188885
theorem B1945675 : Blo 1945435 1945675 := bstep (se 1 (by rfl) ⟨1459256, by rfl⟩ : syracuseStep 1945675 = 2918513) B2918513
theorem B2462501 : Blo 1945435 2462501 := bbase (se 4 (by rfl) ⟨230859, by rfl⟩ : syracuseStep 2462501 = 461719) (by norm_num)
theorem B6566669 : Blo 1945435 6566669 := bstep (se 3 (by rfl) ⟨1231250, by rfl⟩ : syracuseStep 6566669 = 2462501) B2462501
theorem B4377779 : Blo 1945435 4377779 := bstep (se 1 (by rfl) ⟨3283334, by rfl⟩ : syracuseStep 4377779 = 6566669) B6566669
theorem B2918519 : Blo 1945435 2918519 := bstep (se 1 (by rfl) ⟨2188889, by rfl⟩ : syracuseStep 2918519 = 4377779) B4377779
theorem B1945679 : Blo 1945435 1945679 := bstep (se 1 (by rfl) ⟨1459259, by rfl⟩ : syracuseStep 1945679 = 2918519) B2918519
theorem B2918525 : Blo 1945435 2918525 := bbase (se 3 (by rfl) ⟨547223, by rfl⟩ : syracuseStep 2918525 = 1094447) (by norm_num)
theorem B1945683 : Blo 1945435 1945683 := bstep (se 1 (by rfl) ⟨1459262, by rfl⟩ : syracuseStep 1945683 = 2918525) B2918525
theorem B4377797 : Blo 1945435 4377797 := bbase (se 4 (by rfl) ⟨410418, by rfl⟩ : syracuseStep 4377797 = 820837) (by norm_num)
theorem B2918531 : Blo 1945435 2918531 := bstep (se 1 (by rfl) ⟨2188898, by rfl⟩ : syracuseStep 2918531 = 4377797) B4377797
theorem B1945687 : Blo 1945435 1945687 := bstep (se 1 (by rfl) ⟨1459265, by rfl⟩ : syracuseStep 1945687 = 2918531) B2918531
theorem B3944477 : Blo 1945435 3944477 := bbase (se 3 (by rfl) ⟨739589, by rfl⟩ : syracuseStep 3944477 = 1479179) (by norm_num)
theorem B10518605 : Blo 1945435 10518605 := bstep (se 3 (by rfl) ⟨1972238, by rfl⟩ : syracuseStep 10518605 = 3944477) B3944477
theorem B7012403 : Blo 1945435 7012403 := bstep (se 1 (by rfl) ⟨5259302, by rfl⟩ : syracuseStep 7012403 = 10518605) B10518605
theorem B4674935 : Blo 1945435 4674935 := bstep (se 1 (by rfl) ⟨3506201, by rfl⟩ : syracuseStep 4674935 = 7012403) B7012403
theorem B12466493 : Blo 1945435 12466493 := bstep (se 3 (by rfl) ⟨2337467, by rfl⟩ : syracuseStep 12466493 = 4674935) B4674935
theorem B8310995 : Blo 1945435 8310995 := bstep (se 1 (by rfl) ⟨6233246, by rfl⟩ : syracuseStep 8310995 = 12466493) B12466493
theorem B5540663 : Blo 1945435 5540663 := bstep (se 1 (by rfl) ⟨4155497, by rfl⟩ : syracuseStep 5540663 = 8310995) B8310995
theorem B3693775 : Blo 1945435 3693775 := bstep (se 1 (by rfl) ⟨2770331, by rfl⟩ : syracuseStep 3693775 = 5540663) B5540663
theorem B4925033 : Blo 1945435 4925033 := bstep (se 2 (by rfl) ⟨1846887, by rfl⟩ : syracuseStep 4925033 = 3693775) B3693775
theorem B3283355 : Blo 1945435 3283355 := bstep (se 1 (by rfl) ⟨2462516, by rfl⟩ : syracuseStep 3283355 = 4925033) B4925033
theorem B2188903 : Blo 1945435 2188903 := bstep (se 1 (by rfl) ⟨1641677, by rfl⟩ : syracuseStep 2188903 = 3283355) B3283355
theorem B2918537 : Blo 1945435 2918537 := bstep (se 2 (by rfl) ⟨1094451, by rfl⟩ : syracuseStep 2918537 = 2188903) B2188903
theorem B1945691 : Blo 1945435 1945691 := bstep (se 1 (by rfl) ⟨1459268, by rfl⟩ : syracuseStep 1945691 = 2918537) B2918537
theorem B9850085 : Blo 1945435 9850085 := bbase (se 4 (by rfl) ⟨923445, by rfl⟩ : syracuseStep 9850085 = 1846891) (by norm_num)
theorem B6566723 : Blo 1945435 6566723 := bstep (se 1 (by rfl) ⟨4925042, by rfl⟩ : syracuseStep 6566723 = 9850085) B9850085
theorem B4377815 : Blo 1945435 4377815 := bstep (se 1 (by rfl) ⟨3283361, by rfl⟩ : syracuseStep 4377815 = 6566723) B6566723
theorem B2918543 : Blo 1945435 2918543 := bstep (se 1 (by rfl) ⟨2188907, by rfl⟩ : syracuseStep 2918543 = 4377815) B4377815
theorem B1945695 : Blo 1945435 1945695 := bstep (se 1 (by rfl) ⟨1459271, by rfl⟩ : syracuseStep 1945695 = 2918543) B2918543
theorem B2918549 : Blo 1945435 2918549 := bbase (se 6 (by rfl) ⟨68403, by rfl⟩ : syracuseStep 2918549 = 136807) (by norm_num)
theorem B1945699 : Blo 1945435 1945699 := bstep (se 1 (by rfl) ⟨1459274, by rfl⟩ : syracuseStep 1945699 = 2918549) B2918549
theorem B8311045 : Blo 1945435 8311045 := bbase (se 4 (by rfl) ⟨779160, by rfl⟩ : syracuseStep 8311045 = 1558321) (by norm_num)
theorem B11081393 : Blo 1945435 11081393 := bstep (se 2 (by rfl) ⟨4155522, by rfl⟩ : syracuseStep 11081393 = 8311045) B8311045
theorem B7387595 : Blo 1945435 7387595 := bstep (se 1 (by rfl) ⟨5540696, by rfl⟩ : syracuseStep 7387595 = 11081393) B11081393
theorem B4925063 : Blo 1945435 4925063 := bstep (se 1 (by rfl) ⟨3693797, by rfl⟩ : syracuseStep 4925063 = 7387595) B7387595
theorem B3283375 : Blo 1945435 3283375 := bstep (se 1 (by rfl) ⟨2462531, by rfl⟩ : syracuseStep 3283375 = 4925063) B4925063
theorem B4377833 : Blo 1945435 4377833 := bstep (se 2 (by rfl) ⟨1641687, by rfl⟩ : syracuseStep 4377833 = 3283375) B3283375
theorem B2918555 : Blo 1945435 2918555 := bstep (se 1 (by rfl) ⟨2188916, by rfl⟩ : syracuseStep 2918555 = 4377833) B4377833
theorem B1945703 : Blo 1945435 1945703 := bstep (se 1 (by rfl) ⟨1459277, by rfl⟩ : syracuseStep 1945703 = 2918555) B2918555
theorem B2188921 : Blo 1945435 2188921 := bbase (se 2 (by rfl) ⟨820845, by rfl⟩ : syracuseStep 2188921 = 1641691) (by norm_num)
theorem B2918561 : Blo 1945435 2918561 := bstep (se 2 (by rfl) ⟨1094460, by rfl⟩ : syracuseStep 2918561 = 2188921) B2188921
theorem B1945707 : Blo 1945435 1945707 := bstep (se 1 (by rfl) ⟨1459280, by rfl⟩ : syracuseStep 1945707 = 2918561) B2918561
theorem B2564717 : Blo 1945435 2564717 := bbase (se 3 (by rfl) ⟨480884, by rfl⟩ : syracuseStep 2564717 = 961769) (by norm_num)
theorem B6839245 : Blo 1945435 6839245 := bstep (se 3 (by rfl) ⟨1282358, by rfl⟩ : syracuseStep 6839245 = 2564717) B2564717
theorem B9118993 : Blo 1945435 9118993 := bstep (se 2 (by rfl) ⟨3419622, by rfl⟩ : syracuseStep 9118993 = 6839245) B6839245
theorem B12158657 : Blo 1945435 12158657 := bstep (se 2 (by rfl) ⟨4559496, by rfl⟩ : syracuseStep 12158657 = 9118993) B9118993
theorem B8105771 : Blo 1945435 8105771 := bstep (se 1 (by rfl) ⟨6079328, by rfl⟩ : syracuseStep 8105771 = 12158657) B12158657
theorem B5403847 : Blo 1945435 5403847 := bstep (se 1 (by rfl) ⟨4052885, by rfl⟩ : syracuseStep 5403847 = 8105771) B8105771
theorem B7205129 : Blo 1945435 7205129 := bstep (se 2 (by rfl) ⟨2701923, by rfl⟩ : syracuseStep 7205129 = 5403847) B5403847
theorem B4803419 : Blo 1945435 4803419 := bstep (se 1 (by rfl) ⟨3602564, by rfl⟩ : syracuseStep 4803419 = 7205129) B7205129
theorem B12809117 : Blo 1945435 12809117 := bstep (se 3 (by rfl) ⟨2401709, by rfl⟩ : syracuseStep 12809117 = 4803419) B4803419
theorem B34157645 : Blo 1945435 34157645 := bstep (se 3 (by rfl) ⟨6404558, by rfl⟩ : syracuseStep 34157645 = 12809117) B12809117
theorem B22771763 : Blo 1945435 22771763 := bstep (se 1 (by rfl) ⟨17078822, by rfl⟩ : syracuseStep 22771763 = 34157645) B34157645
theorem B15181175 : Blo 1945435 15181175 := bstep (se 1 (by rfl) ⟨11385881, by rfl⟩ : syracuseStep 15181175 = 22771763) B22771763
theorem B10120783 : Blo 1945435 10120783 := bstep (se 1 (by rfl) ⟨7590587, by rfl⟩ : syracuseStep 10120783 = 15181175) B15181175
theorem B13494377 : Blo 1945435 13494377 := bstep (se 2 (by rfl) ⟨5060391, by rfl⟩ : syracuseStep 13494377 = 10120783) B10120783
theorem B35985005 : Blo 1945435 35985005 := bstep (se 3 (by rfl) ⟨6747188, by rfl⟩ : syracuseStep 35985005 = 13494377) B13494377
theorem B23990003 : Blo 1945435 23990003 := bstep (se 1 (by rfl) ⟨17992502, by rfl⟩ : syracuseStep 23990003 = 35985005) B35985005
theorem B15993335 : Blo 1945435 15993335 := bstep (se 1 (by rfl) ⟨11995001, by rfl⟩ : syracuseStep 15993335 = 23990003) B23990003
theorem B42648893 : Blo 1945435 42648893 := bstep (se 3 (by rfl) ⟨7996667, by rfl⟩ : syracuseStep 42648893 = 15993335) B15993335
theorem B28432595 : Blo 1945435 28432595 := bstep (se 1 (by rfl) ⟨21324446, by rfl⟩ : syracuseStep 28432595 = 42648893) B42648893
theorem B18955063 : Blo 1945435 18955063 := bstep (se 1 (by rfl) ⟨14216297, by rfl⟩ : syracuseStep 18955063 = 28432595) B28432595
theorem B25273417 : Blo 1945435 25273417 := bstep (se 2 (by rfl) ⟨9477531, by rfl⟩ : syracuseStep 25273417 = 18955063) B18955063
theorem B33697889 : Blo 1945435 33697889 := bstep (se 2 (by rfl) ⟨12636708, by rfl⟩ : syracuseStep 33697889 = 25273417) B25273417
theorem B22465259 : Blo 1945435 22465259 := bstep (se 1 (by rfl) ⟨16848944, by rfl⟩ : syracuseStep 22465259 = 33697889) B33697889
theorem B14976839 : Blo 1945435 14976839 := bstep (se 1 (by rfl) ⟨11232629, by rfl⟩ : syracuseStep 14976839 = 22465259) B22465259
theorem B9984559 : Blo 1945435 9984559 := bstep (se 1 (by rfl) ⟨7488419, by rfl⟩ : syracuseStep 9984559 = 14976839) B14976839
theorem B13312745 : Blo 1945435 13312745 := bstep (se 2 (by rfl) ⟨4992279, by rfl⟩ : syracuseStep 13312745 = 9984559) B9984559
theorem B8875163 : Blo 1945435 8875163 := bstep (se 1 (by rfl) ⟨6656372, by rfl⟩ : syracuseStep 8875163 = 13312745) B13312745
theorem B5916775 : Blo 1945435 5916775 := bstep (se 1 (by rfl) ⟨4437581, by rfl⟩ : syracuseStep 5916775 = 8875163) B8875163
theorem B7889033 : Blo 1945435 7889033 := bstep (se 2 (by rfl) ⟨2958387, by rfl⟩ : syracuseStep 7889033 = 5916775) B5916775
theorem B21037421 : Blo 1945435 21037421 := bstep (se 3 (by rfl) ⟨3944516, by rfl⟩ : syracuseStep 21037421 = 7889033) B7889033
theorem B14024947 : Blo 1945435 14024947 := bstep (se 1 (by rfl) ⟨10518710, by rfl⟩ : syracuseStep 14024947 = 21037421) B21037421
theorem B18699929 : Blo 1945435 18699929 := bstep (se 2 (by rfl) ⟨7012473, by rfl⟩ : syracuseStep 18699929 = 14024947) B14024947
theorem B12466619 : Blo 1945435 12466619 := bstep (se 1 (by rfl) ⟨9349964, by rfl⟩ : syracuseStep 12466619 = 18699929) B18699929
theorem B8311079 : Blo 1945435 8311079 := bstep (se 1 (by rfl) ⟨6233309, by rfl⟩ : syracuseStep 8311079 = 12466619) B12466619
theorem B5540719 : Blo 1945435 5540719 := bstep (se 1 (by rfl) ⟨4155539, by rfl⟩ : syracuseStep 5540719 = 8311079) B8311079
theorem B7387625 : Blo 1945435 7387625 := bstep (se 2 (by rfl) ⟨2770359, by rfl⟩ : syracuseStep 7387625 = 5540719) B5540719
theorem B4925083 : Blo 1945435 4925083 := bstep (se 1 (by rfl) ⟨3693812, by rfl⟩ : syracuseStep 4925083 = 7387625) B7387625
theorem B6566777 : Blo 1945435 6566777 := bstep (se 2 (by rfl) ⟨2462541, by rfl⟩ : syracuseStep 6566777 = 4925083) B4925083
theorem B4377851 : Blo 1945435 4377851 := bstep (se 1 (by rfl) ⟨3283388, by rfl⟩ : syracuseStep 4377851 = 6566777) B6566777
theorem B2918567 : Blo 1945435 2918567 := bstep (se 1 (by rfl) ⟨2188925, by rfl⟩ : syracuseStep 2918567 = 4377851) B4377851
theorem B1945711 : Blo 1945435 1945711 := bstep (se 1 (by rfl) ⟨1459283, by rfl⟩ : syracuseStep 1945711 = 2918567) B2918567
theorem B2918573 : Blo 1945435 2918573 := bbase (se 3 (by rfl) ⟨547232, by rfl⟩ : syracuseStep 2918573 = 1094465) (by norm_num)
theorem B1945715 : Blo 1945435 1945715 := bstep (se 1 (by rfl) ⟨1459286, by rfl⟩ : syracuseStep 1945715 = 2918573) B2918573
theorem B4377869 : Blo 1945435 4377869 := bbase (se 3 (by rfl) ⟨820850, by rfl⟩ : syracuseStep 4377869 = 1641701) (by norm_num)
theorem B2918579 : Blo 1945435 2918579 := bstep (se 1 (by rfl) ⟨2188934, by rfl⟩ : syracuseStep 2918579 = 4377869) B4377869
theorem B1945719 : Blo 1945435 1945719 := bstep (se 1 (by rfl) ⟨1459289, by rfl⟩ : syracuseStep 1945719 = 2918579) B2918579
theorem B2462557 : Blo 1945435 2462557 := bbase (se 3 (by rfl) ⟨461729, by rfl⟩ : syracuseStep 2462557 = 923459) (by norm_num)
theorem B3283409 : Blo 1945435 3283409 := bstep (se 2 (by rfl) ⟨1231278, by rfl⟩ : syracuseStep 3283409 = 2462557) B2462557
theorem B2188939 : Blo 1945435 2188939 := bstep (se 1 (by rfl) ⟨1641704, by rfl⟩ : syracuseStep 2188939 = 3283409) B3283409
theorem B2918585 : Blo 1945435 2918585 := bstep (se 2 (by rfl) ⟨1094469, by rfl⟩ : syracuseStep 2918585 = 2188939) B2188939
theorem B1945723 : Blo 1945435 1945723 := bstep (se 1 (by rfl) ⟨1459292, by rfl⟩ : syracuseStep 1945723 = 2918585) B2918585
theorem B16622293 : Blo 1945435 16622293 := bbase (se 7 (by rfl) ⟨194792, by rfl⟩ : syracuseStep 16622293 = 389585) (by norm_num)
theorem B22163057 : Blo 1945435 22163057 := bstep (se 2 (by rfl) ⟨8311146, by rfl⟩ : syracuseStep 22163057 = 16622293) B16622293
theorem B14775371 : Blo 1945435 14775371 := bstep (se 1 (by rfl) ⟨11081528, by rfl⟩ : syracuseStep 14775371 = 22163057) B22163057
theorem B9850247 : Blo 1945435 9850247 := bstep (se 1 (by rfl) ⟨7387685, by rfl⟩ : syracuseStep 9850247 = 14775371) B14775371
theorem B6566831 : Blo 1945435 6566831 := bstep (se 1 (by rfl) ⟨4925123, by rfl⟩ : syracuseStep 6566831 = 9850247) B9850247
theorem B4377887 : Blo 1945435 4377887 := bstep (se 1 (by rfl) ⟨3283415, by rfl⟩ : syracuseStep 4377887 = 6566831) B6566831
theorem B2918591 : Blo 1945435 2918591 := bstep (se 1 (by rfl) ⟨2188943, by rfl⟩ : syracuseStep 2918591 = 4377887) B4377887
theorem B1945727 : Blo 1945435 1945727 := bstep (se 1 (by rfl) ⟨1459295, by rfl⟩ : syracuseStep 1945727 = 2918591) B2918591
theorem B2918597 : Blo 1945435 2918597 := bbase (se 4 (by rfl) ⟨273618, by rfl⟩ : syracuseStep 2918597 = 547237) (by norm_num)
theorem B1945731 : Blo 1945435 1945731 := bstep (se 1 (by rfl) ⟨1459298, by rfl⟩ : syracuseStep 1945731 = 2918597) B2918597
theorem B3283429 : Blo 1945435 3283429 := bbase (se 4 (by rfl) ⟨307821, by rfl⟩ : syracuseStep 3283429 = 615643) (by norm_num)
theorem B4377905 : Blo 1945435 4377905 := bstep (se 2 (by rfl) ⟨1641714, by rfl⟩ : syracuseStep 4377905 = 3283429) B3283429
theorem B2918603 : Blo 1945435 2918603 := bstep (se 1 (by rfl) ⟨2188952, by rfl⟩ : syracuseStep 2918603 = 4377905) B4377905
theorem B1945735 : Blo 1945435 1945735 := bstep (se 1 (by rfl) ⟨1459301, by rfl⟩ : syracuseStep 1945735 = 2918603) B2918603
theorem B2188957 : Blo 1945435 2188957 := bbase (se 3 (by rfl) ⟨410429, by rfl⟩ : syracuseStep 2188957 = 820859) (by norm_num)
theorem B2918609 : Blo 1945435 2918609 := bstep (se 2 (by rfl) ⟨1094478, by rfl⟩ : syracuseStep 2918609 = 2188957) B2188957
theorem B1945739 : Blo 1945435 1945739 := bstep (se 1 (by rfl) ⟨1459304, by rfl⟩ : syracuseStep 1945739 = 2918609) B2918609
theorem B6566885 : Blo 1945435 6566885 := bbase (se 4 (by rfl) ⟨615645, by rfl⟩ : syracuseStep 6566885 = 1231291) (by norm_num)
theorem B4377923 : Blo 1945435 4377923 := bstep (se 1 (by rfl) ⟨3283442, by rfl⟩ : syracuseStep 4377923 = 6566885) B6566885
theorem B2918615 : Blo 1945435 2918615 := bstep (se 1 (by rfl) ⟨2188961, by rfl⟩ : syracuseStep 2918615 = 4377923) B4377923
theorem B1945743 : Blo 1945435 1945743 := bstep (se 1 (by rfl) ⟨1459307, by rfl⟩ : syracuseStep 1945743 = 2918615) B2918615
theorem B2918621 : Blo 1945435 2918621 := bbase (se 3 (by rfl) ⟨547241, by rfl⟩ : syracuseStep 2918621 = 1094483) (by norm_num)
theorem B1945747 : Blo 1945435 1945747 := bstep (se 1 (by rfl) ⟨1459310, by rfl⟩ : syracuseStep 1945747 = 2918621) B2918621
theorem B4377941 : Blo 1945435 4377941 := bbase (se 11 (by rfl) ⟨3206, by rfl⟩ : syracuseStep 4377941 = 6413) (by norm_num)
theorem B2918627 : Blo 1945435 2918627 := bstep (se 1 (by rfl) ⟨2188970, by rfl⟩ : syracuseStep 2918627 = 4377941) B4377941
theorem B1945751 : Blo 1945435 1945751 := bstep (se 1 (by rfl) ⟨1459313, by rfl⟩ : syracuseStep 1945751 = 2918627) B2918627
theorem B2077817 : Blo 1945435 2077817 := bbase (se 2 (by rfl) ⟨779181, by rfl⟩ : syracuseStep 2077817 = 1558363) (by norm_num)
theorem B5540845 : Blo 1945435 5540845 := bstep (se 3 (by rfl) ⟨1038908, by rfl⟩ : syracuseStep 5540845 = 2077817) B2077817
theorem B7387793 : Blo 1945435 7387793 := bstep (se 2 (by rfl) ⟨2770422, by rfl⟩ : syracuseStep 7387793 = 5540845) B5540845
theorem B4925195 : Blo 1945435 4925195 := bstep (se 1 (by rfl) ⟨3693896, by rfl⟩ : syracuseStep 4925195 = 7387793) B7387793
theorem B3283463 : Blo 1945435 3283463 := bstep (se 1 (by rfl) ⟨2462597, by rfl⟩ : syracuseStep 3283463 = 4925195) B4925195
theorem B2188975 : Blo 1945435 2188975 := bstep (se 1 (by rfl) ⟨1641731, by rfl⟩ : syracuseStep 2188975 = 3283463) B3283463
theorem B2918633 : Blo 1945435 2918633 := bstep (se 2 (by rfl) ⟨1094487, by rfl⟩ : syracuseStep 2918633 = 2188975) B2188975
theorem B1945755 : Blo 1945435 1945755 := bstep (se 1 (by rfl) ⟨1459316, by rfl⟩ : syracuseStep 1945755 = 2918633) B2918633
theorem B63113813 : Blo 1945435 63113813 := bbase (se 8 (by rfl) ⟨369807, by rfl⟩ : syracuseStep 63113813 = 739615) (by norm_num)
theorem B42075875 : Blo 1945435 42075875 := bstep (se 1 (by rfl) ⟨31556906, by rfl⟩ : syracuseStep 42075875 = 63113813) B63113813
theorem B28050583 : Blo 1945435 28050583 := bstep (se 1 (by rfl) ⟨21037937, by rfl⟩ : syracuseStep 28050583 = 42075875) B42075875
theorem B37400777 : Blo 1945435 37400777 := bstep (se 2 (by rfl) ⟨14025291, by rfl⟩ : syracuseStep 37400777 = 28050583) B28050583
theorem B24933851 : Blo 1945435 24933851 := bstep (se 1 (by rfl) ⟨18700388, by rfl⟩ : syracuseStep 24933851 = 37400777) B37400777
theorem B16622567 : Blo 1945435 16622567 := bstep (se 1 (by rfl) ⟨12466925, by rfl⟩ : syracuseStep 16622567 = 24933851) B24933851
theorem B11081711 : Blo 1945435 11081711 := bstep (se 1 (by rfl) ⟨8311283, by rfl⟩ : syracuseStep 11081711 = 16622567) B16622567
theorem B7387807 : Blo 1945435 7387807 := bstep (se 1 (by rfl) ⟨5540855, by rfl⟩ : syracuseStep 7387807 = 11081711) B11081711
theorem B9850409 : Blo 1945435 9850409 := bstep (se 2 (by rfl) ⟨3693903, by rfl⟩ : syracuseStep 9850409 = 7387807) B7387807
theorem B6566939 : Blo 1945435 6566939 := bstep (se 1 (by rfl) ⟨4925204, by rfl⟩ : syracuseStep 6566939 = 9850409) B9850409
theorem B4377959 : Blo 1945435 4377959 := bstep (se 1 (by rfl) ⟨3283469, by rfl⟩ : syracuseStep 4377959 = 6566939) B6566939
theorem B2918639 : Blo 1945435 2918639 := bstep (se 1 (by rfl) ⟨2188979, by rfl⟩ : syracuseStep 2918639 = 4377959) B4377959
theorem B1945759 : Blo 1945435 1945759 := bstep (se 1 (by rfl) ⟨1459319, by rfl⟩ : syracuseStep 1945759 = 2918639) B2918639
theorem B2918645 : Blo 1945435 2918645 := bbase (se 5 (by rfl) ⟨136811, by rfl⟩ : syracuseStep 2918645 = 273623) (by norm_num)
theorem B1945763 : Blo 1945435 1945763 := bstep (se 1 (by rfl) ⟨1459322, by rfl⟩ : syracuseStep 1945763 = 2918645) B2918645
theorem B18700469 : Blo 1945435 18700469 := bbase (se 5 (by rfl) ⟨876584, by rfl⟩ : syracuseStep 18700469 = 1753169) (by norm_num)
theorem B12466979 : Blo 1945435 12466979 := bstep (se 1 (by rfl) ⟨9350234, by rfl⟩ : syracuseStep 12466979 = 18700469) B18700469
theorem B8311319 : Blo 1945435 8311319 := bstep (se 1 (by rfl) ⟨6233489, by rfl⟩ : syracuseStep 8311319 = 12466979) B12466979
theorem B5540879 : Blo 1945435 5540879 := bstep (se 1 (by rfl) ⟨4155659, by rfl⟩ : syracuseStep 5540879 = 8311319) B8311319
theorem B3693919 : Blo 1945435 3693919 := bstep (se 1 (by rfl) ⟨2770439, by rfl⟩ : syracuseStep 3693919 = 5540879) B5540879
theorem B4925225 : Blo 1945435 4925225 := bstep (se 2 (by rfl) ⟨1846959, by rfl⟩ : syracuseStep 4925225 = 3693919) B3693919
theorem B3283483 : Blo 1945435 3283483 := bstep (se 1 (by rfl) ⟨2462612, by rfl⟩ : syracuseStep 3283483 = 4925225) B4925225
theorem B4377977 : Blo 1945435 4377977 := bstep (se 2 (by rfl) ⟨1641741, by rfl⟩ : syracuseStep 4377977 = 3283483) B3283483
theorem B2918651 : Blo 1945435 2918651 := bstep (se 1 (by rfl) ⟨2188988, by rfl⟩ : syracuseStep 2918651 = 4377977) B4377977
theorem B1945767 : Blo 1945435 1945767 := bstep (se 1 (by rfl) ⟨1459325, by rfl⟩ : syracuseStep 1945767 = 2918651) B2918651
theorem B2188993 : Blo 1945435 2188993 := bbase (se 2 (by rfl) ⟨820872, by rfl⟩ : syracuseStep 2188993 = 1641745) (by norm_num)
theorem B2918657 : Blo 1945435 2918657 := bstep (se 2 (by rfl) ⟨1094496, by rfl⟩ : syracuseStep 2918657 = 2188993) B2188993
theorem B1945771 : Blo 1945435 1945771 := bstep (se 1 (by rfl) ⟨1459328, by rfl⟩ : syracuseStep 1945771 = 2918657) B2918657
theorem B4925245 : Blo 1945435 4925245 := bbase (se 3 (by rfl) ⟨923483, by rfl⟩ : syracuseStep 4925245 = 1846967) (by norm_num)
theorem B6566993 : Blo 1945435 6566993 := bstep (se 2 (by rfl) ⟨2462622, by rfl⟩ : syracuseStep 6566993 = 4925245) B4925245
theorem B4377995 : Blo 1945435 4377995 := bstep (se 1 (by rfl) ⟨3283496, by rfl⟩ : syracuseStep 4377995 = 6566993) B6566993
theorem B2918663 : Blo 1945435 2918663 := bstep (se 1 (by rfl) ⟨2188997, by rfl⟩ : syracuseStep 2918663 = 4377995) B4377995
theorem B1945775 : Blo 1945435 1945775 := bstep (se 1 (by rfl) ⟨1459331, by rfl⟩ : syracuseStep 1945775 = 2918663) B2918663
theorem B2918669 : Blo 1945435 2918669 := bbase (se 3 (by rfl) ⟨547250, by rfl⟩ : syracuseStep 2918669 = 1094501) (by norm_num)
theorem B1945779 : Blo 1945435 1945779 := bstep (se 1 (by rfl) ⟨1459334, by rfl⟩ : syracuseStep 1945779 = 2918669) B2918669
theorem B4378013 : Blo 1945435 4378013 := bbase (se 3 (by rfl) ⟨820877, by rfl⟩ : syracuseStep 4378013 = 1641755) (by norm_num)
theorem B2918675 : Blo 1945435 2918675 := bstep (se 1 (by rfl) ⟨2189006, by rfl⟩ : syracuseStep 2918675 = 4378013) B4378013
theorem B1945783 : Blo 1945435 1945783 := bstep (se 1 (by rfl) ⟨1459337, by rfl⟩ : syracuseStep 1945783 = 2918675) B2918675
theorem B3283517 : Blo 1945435 3283517 := bbase (se 3 (by rfl) ⟨615659, by rfl⟩ : syracuseStep 3283517 = 1231319) (by norm_num)
theorem B2189011 : Blo 1945435 2189011 := bstep (se 1 (by rfl) ⟨1641758, by rfl⟩ : syracuseStep 2189011 = 3283517) B3283517
theorem B2918681 : Blo 1945435 2918681 := bstep (se 2 (by rfl) ⟨1094505, by rfl⟩ : syracuseStep 2918681 = 2189011) B2189011
theorem B1945787 : Blo 1945435 1945787 := bstep (se 1 (by rfl) ⟨1459340, by rfl⟩ : syracuseStep 1945787 = 2918681) B2918681
theorem B2106205 : Blo 1945435 2106205 := bbase (se 3 (by rfl) ⟨394913, by rfl⟩ : syracuseStep 2106205 = 789827) (by norm_num)
theorem B11233093 : Blo 1945435 11233093 := bstep (se 4 (by rfl) ⟨1053102, by rfl⟩ : syracuseStep 11233093 = 2106205) B2106205
theorem B14977457 : Blo 1945435 14977457 := bstep (se 2 (by rfl) ⟨5616546, by rfl⟩ : syracuseStep 14977457 = 11233093) B11233093
theorem B9984971 : Blo 1945435 9984971 := bstep (se 1 (by rfl) ⟨7488728, by rfl⟩ : syracuseStep 9984971 = 14977457) B14977457
theorem B26626589 : Blo 1945435 26626589 := bstep (se 3 (by rfl) ⟨4992485, by rfl⟩ : syracuseStep 26626589 = 9984971) B9984971
theorem B17751059 : Blo 1945435 17751059 := bstep (se 1 (by rfl) ⟨13313294, by rfl⟩ : syracuseStep 17751059 = 26626589) B26626589
theorem B11834039 : Blo 1945435 11834039 := bstep (se 1 (by rfl) ⟨8875529, by rfl⟩ : syracuseStep 11834039 = 17751059) B17751059
theorem B7889359 : Blo 1945435 7889359 := bstep (se 1 (by rfl) ⟨5917019, by rfl⟩ : syracuseStep 7889359 = 11834039) B11834039
theorem B10519145 : Blo 1945435 10519145 := bstep (se 2 (by rfl) ⟨3944679, by rfl⟩ : syracuseStep 10519145 = 7889359) B7889359
theorem B7012763 : Blo 1945435 7012763 := bstep (se 1 (by rfl) ⟨5259572, by rfl⟩ : syracuseStep 7012763 = 10519145) B10519145
theorem B4675175 : Blo 1945435 4675175 := bstep (se 1 (by rfl) ⟨3506381, by rfl⟩ : syracuseStep 4675175 = 7012763) B7012763
theorem B3116783 : Blo 1945435 3116783 := bstep (se 1 (by rfl) ⟨2337587, by rfl⟩ : syracuseStep 3116783 = 4675175) B4675175
theorem B2077855 : Blo 1945435 2077855 := bstep (se 1 (by rfl) ⟨1558391, by rfl⟩ : syracuseStep 2077855 = 3116783) B3116783
theorem B11081893 : Blo 1945435 11081893 := bstep (se 4 (by rfl) ⟨1038927, by rfl⟩ : syracuseStep 11081893 = 2077855) B2077855
theorem B14775857 : Blo 1945435 14775857 := bstep (se 2 (by rfl) ⟨5540946, by rfl⟩ : syracuseStep 14775857 = 11081893) B11081893
theorem B9850571 : Blo 1945435 9850571 := bstep (se 1 (by rfl) ⟨7387928, by rfl⟩ : syracuseStep 9850571 = 14775857) B14775857
theorem B6567047 : Blo 1945435 6567047 := bstep (se 1 (by rfl) ⟨4925285, by rfl⟩ : syracuseStep 6567047 = 9850571) B9850571
theorem B4378031 : Blo 1945435 4378031 := bstep (se 1 (by rfl) ⟨3283523, by rfl⟩ : syracuseStep 4378031 = 6567047) B6567047
theorem B2918687 : Blo 1945435 2918687 := bstep (se 1 (by rfl) ⟨2189015, by rfl⟩ : syracuseStep 2918687 = 4378031) B4378031
theorem B1945791 : Blo 1945435 1945791 := bstep (se 1 (by rfl) ⟨1459343, by rfl⟩ : syracuseStep 1945791 = 2918687) B2918687
theorem B2918693 : Blo 1945435 2918693 := bbase (se 4 (by rfl) ⟨273627, by rfl⟩ : syracuseStep 2918693 = 547255) (by norm_num)
theorem B1945795 : Blo 1945435 1945795 := bstep (se 1 (by rfl) ⟨1459346, by rfl⟩ : syracuseStep 1945795 = 2918693) B2918693
theorem B2462653 : Blo 1945435 2462653 := bbase (se 3 (by rfl) ⟨461747, by rfl⟩ : syracuseStep 2462653 = 923495) (by norm_num)
theorem B3283537 : Blo 1945435 3283537 := bstep (se 2 (by rfl) ⟨1231326, by rfl⟩ : syracuseStep 3283537 = 2462653) B2462653
theorem B4378049 : Blo 1945435 4378049 := bstep (se 2 (by rfl) ⟨1641768, by rfl⟩ : syracuseStep 4378049 = 3283537) B3283537
theorem B2918699 : Blo 1945435 2918699 := bstep (se 1 (by rfl) ⟨2189024, by rfl⟩ : syracuseStep 2918699 = 4378049) B4378049
theorem B1945799 : Blo 1945435 1945799 := bstep (se 1 (by rfl) ⟨1459349, by rfl⟩ : syracuseStep 1945799 = 2918699) B2918699
theorem B2189029 : Blo 1945435 2189029 := bbase (se 4 (by rfl) ⟨205221, by rfl⟩ : syracuseStep 2189029 = 410443) (by norm_num)
theorem B2918705 : Blo 1945435 2918705 := bstep (se 2 (by rfl) ⟨1094514, by rfl⟩ : syracuseStep 2918705 = 2189029) B2189029
theorem B1945803 : Blo 1945435 1945803 := bstep (se 1 (by rfl) ⟨1459352, by rfl⟩ : syracuseStep 1945803 = 2918705) B2918705
theorem B3744397 : Blo 1945435 3744397 := bbase (se 3 (by rfl) ⟨702074, by rfl⟩ : syracuseStep 3744397 = 1404149) (by norm_num)
theorem B4992529 : Blo 1945435 4992529 := bstep (se 2 (by rfl) ⟨1872198, by rfl⟩ : syracuseStep 4992529 = 3744397) B3744397
theorem B6656705 : Blo 1945435 6656705 := bstep (se 2 (by rfl) ⟨2496264, by rfl⟩ : syracuseStep 6656705 = 4992529) B4992529
theorem B4437803 : Blo 1945435 4437803 := bstep (se 1 (by rfl) ⟨3328352, by rfl⟩ : syracuseStep 4437803 = 6656705) B6656705
theorem B2958535 : Blo 1945435 2958535 := bstep (se 1 (by rfl) ⟨2218901, by rfl⟩ : syracuseStep 2958535 = 4437803) B4437803
theorem B3944713 : Blo 1945435 3944713 := bstep (se 2 (by rfl) ⟨1479267, by rfl⟩ : syracuseStep 3944713 = 2958535) B2958535
theorem B5259617 : Blo 1945435 5259617 := bstep (se 2 (by rfl) ⟨1972356, by rfl⟩ : syracuseStep 5259617 = 3944713) B3944713
theorem B3506411 : Blo 1945435 3506411 := bstep (se 1 (by rfl) ⟨2629808, by rfl⟩ : syracuseStep 3506411 = 5259617) B5259617
theorem B2337607 : Blo 1945435 2337607 := bstep (se 1 (by rfl) ⟨1753205, by rfl⟩ : syracuseStep 2337607 = 3506411) B3506411
theorem B3116809 : Blo 1945435 3116809 := bstep (se 2 (by rfl) ⟨1168803, by rfl⟩ : syracuseStep 3116809 = 2337607) B2337607
theorem B4155745 : Blo 1945435 4155745 := bstep (se 2 (by rfl) ⟨1558404, by rfl⟩ : syracuseStep 4155745 = 3116809) B3116809
theorem B5540993 : Blo 1945435 5540993 := bstep (se 2 (by rfl) ⟨2077872, by rfl⟩ : syracuseStep 5540993 = 4155745) B4155745
theorem B3693995 : Blo 1945435 3693995 := bstep (se 1 (by rfl) ⟨2770496, by rfl⟩ : syracuseStep 3693995 = 5540993) B5540993
theorem B2462663 : Blo 1945435 2462663 := bstep (se 1 (by rfl) ⟨1846997, by rfl⟩ : syracuseStep 2462663 = 3693995) B3693995
theorem B6567101 : Blo 1945435 6567101 := bstep (se 3 (by rfl) ⟨1231331, by rfl⟩ : syracuseStep 6567101 = 2462663) B2462663
theorem B4378067 : Blo 1945435 4378067 := bstep (se 1 (by rfl) ⟨3283550, by rfl⟩ : syracuseStep 4378067 = 6567101) B6567101
theorem B2918711 : Blo 1945435 2918711 := bstep (se 1 (by rfl) ⟨2189033, by rfl⟩ : syracuseStep 2918711 = 4378067) B4378067
theorem B1945807 : Blo 1945435 1945807 := bstep (se 1 (by rfl) ⟨1459355, by rfl⟩ : syracuseStep 1945807 = 2918711) B2918711
theorem B2918717 : Blo 1945435 2918717 := bbase (se 3 (by rfl) ⟨547259, by rfl⟩ : syracuseStep 2918717 = 1094519) (by norm_num)
theorem B1945811 : Blo 1945435 1945811 := bstep (se 1 (by rfl) ⟨1459358, by rfl⟩ : syracuseStep 1945811 = 2918717) B2918717
theorem B4378085 : Blo 1945435 4378085 := bbase (se 4 (by rfl) ⟨410445, by rfl⟩ : syracuseStep 4378085 = 820891) (by norm_num)
theorem B2918723 : Blo 1945435 2918723 := bstep (se 1 (by rfl) ⟨2189042, by rfl⟩ : syracuseStep 2918723 = 4378085) B4378085
theorem B1945815 : Blo 1945435 1945815 := bstep (se 1 (by rfl) ⟨1459361, by rfl⟩ : syracuseStep 1945815 = 2918723) B2918723
theorem B4925357 : Blo 1945435 4925357 := bbase (se 3 (by rfl) ⟨923504, by rfl⟩ : syracuseStep 4925357 = 1847009) (by norm_num)
theorem B3283571 : Blo 1945435 3283571 := bstep (se 1 (by rfl) ⟨2462678, by rfl⟩ : syracuseStep 3283571 = 4925357) B4925357
theorem B2189047 : Blo 1945435 2189047 := bstep (se 1 (by rfl) ⟨1641785, by rfl⟩ : syracuseStep 2189047 = 3283571) B3283571
theorem B2918729 : Blo 1945435 2918729 := bstep (se 2 (by rfl) ⟨1094523, by rfl⟩ : syracuseStep 2918729 = 2189047) B2189047
theorem B1945819 : Blo 1945435 1945819 := bstep (se 1 (by rfl) ⟨1459364, by rfl⟩ : syracuseStep 1945819 = 2918729) B2918729
theorem B6233669 : Blo 1945435 6233669 := bbase (se 4 (by rfl) ⟨584406, by rfl⟩ : syracuseStep 6233669 = 1168813) (by norm_num)
theorem B4155779 : Blo 1945435 4155779 := bstep (se 1 (by rfl) ⟨3116834, by rfl⟩ : syracuseStep 4155779 = 6233669) B6233669
theorem B2770519 : Blo 1945435 2770519 := bstep (se 1 (by rfl) ⟨2077889, by rfl⟩ : syracuseStep 2770519 = 4155779) B4155779
theorem B3694025 : Blo 1945435 3694025 := bstep (se 2 (by rfl) ⟨1385259, by rfl⟩ : syracuseStep 3694025 = 2770519) B2770519
theorem B9850733 : Blo 1945435 9850733 := bstep (se 3 (by rfl) ⟨1847012, by rfl⟩ : syracuseStep 9850733 = 3694025) B3694025
theorem B6567155 : Blo 1945435 6567155 := bstep (se 1 (by rfl) ⟨4925366, by rfl⟩ : syracuseStep 6567155 = 9850733) B9850733
theorem B4378103 : Blo 1945435 4378103 := bstep (se 1 (by rfl) ⟨3283577, by rfl⟩ : syracuseStep 4378103 = 6567155) B6567155
theorem B2918735 : Blo 1945435 2918735 := bstep (se 1 (by rfl) ⟨2189051, by rfl⟩ : syracuseStep 2918735 = 4378103) B4378103
theorem B1945823 : Blo 1945435 1945823 := bstep (se 1 (by rfl) ⟨1459367, by rfl⟩ : syracuseStep 1945823 = 2918735) B2918735
theorem B2918741 : Blo 1945435 2918741 := bbase (se 10 (by rfl) ⟨4275, by rfl⟩ : syracuseStep 2918741 = 8551) (by norm_num)
theorem B1945827 : Blo 1945435 1945827 := bstep (se 1 (by rfl) ⟨1459370, by rfl⟩ : syracuseStep 1945827 = 2918741) B2918741
theorem B5541061 : Blo 1945435 5541061 := bbase (se 4 (by rfl) ⟨519474, by rfl⟩ : syracuseStep 5541061 = 1038949) (by norm_num)
theorem B7388081 : Blo 1945435 7388081 := bstep (se 2 (by rfl) ⟨2770530, by rfl⟩ : syracuseStep 7388081 = 5541061) B5541061
theorem B4925387 : Blo 1945435 4925387 := bstep (se 1 (by rfl) ⟨3694040, by rfl⟩ : syracuseStep 4925387 = 7388081) B7388081
theorem B3283591 : Blo 1945435 3283591 := bstep (se 1 (by rfl) ⟨2462693, by rfl⟩ : syracuseStep 3283591 = 4925387) B4925387
theorem B4378121 : Blo 1945435 4378121 := bstep (se 2 (by rfl) ⟨1641795, by rfl⟩ : syracuseStep 4378121 = 3283591) B3283591
theorem B2918747 : Blo 1945435 2918747 := bstep (se 1 (by rfl) ⟨2189060, by rfl⟩ : syracuseStep 2918747 = 4378121) B4378121
theorem B1945831 : Blo 1945435 1945831 := bstep (se 1 (by rfl) ⟨1459373, by rfl⟩ : syracuseStep 1945831 = 2918747) B2918747
theorem B2189065 : Blo 1945435 2189065 := bbase (se 2 (by rfl) ⟨820899, by rfl⟩ : syracuseStep 2189065 = 1641799) (by norm_num)
theorem B2918753 : Blo 1945435 2918753 := bstep (se 2 (by rfl) ⟨1094532, by rfl⟩ : syracuseStep 2918753 = 2189065) B2189065
theorem B1945835 : Blo 1945435 1945835 := bstep (se 1 (by rfl) ⟨1459376, by rfl⟩ : syracuseStep 1945835 = 2918753) B2918753
theorem B5259701 : Blo 1945435 5259701 := bbase (se 5 (by rfl) ⟨246548, by rfl⟩ : syracuseStep 5259701 = 493097) (by norm_num)
theorem B14025869 : Blo 1945435 14025869 := bstep (se 3 (by rfl) ⟨2629850, by rfl⟩ : syracuseStep 14025869 = 5259701) B5259701
theorem B9350579 : Blo 1945435 9350579 := bstep (se 1 (by rfl) ⟨7012934, by rfl⟩ : syracuseStep 9350579 = 14025869) B14025869
theorem B24934877 : Blo 1945435 24934877 := bstep (se 3 (by rfl) ⟨4675289, by rfl⟩ : syracuseStep 24934877 = 9350579) B9350579
theorem B16623251 : Blo 1945435 16623251 := bstep (se 1 (by rfl) ⟨12467438, by rfl⟩ : syracuseStep 16623251 = 24934877) B24934877
theorem B11082167 : Blo 1945435 11082167 := bstep (se 1 (by rfl) ⟨8311625, by rfl⟩ : syracuseStep 11082167 = 16623251) B16623251
theorem B7388111 : Blo 1945435 7388111 := bstep (se 1 (by rfl) ⟨5541083, by rfl⟩ : syracuseStep 7388111 = 11082167) B11082167
theorem B4925407 : Blo 1945435 4925407 := bstep (se 1 (by rfl) ⟨3694055, by rfl⟩ : syracuseStep 4925407 = 7388111) B7388111
theorem B6567209 : Blo 1945435 6567209 := bstep (se 2 (by rfl) ⟨2462703, by rfl⟩ : syracuseStep 6567209 = 4925407) B4925407
theorem B4378139 : Blo 1945435 4378139 := bstep (se 1 (by rfl) ⟨3283604, by rfl⟩ : syracuseStep 4378139 = 6567209) B6567209
theorem B2918759 : Blo 1945435 2918759 := bstep (se 1 (by rfl) ⟨2189069, by rfl⟩ : syracuseStep 2918759 = 4378139) B4378139
theorem B1945839 : Blo 1945435 1945839 := bstep (se 1 (by rfl) ⟨1459379, by rfl⟩ : syracuseStep 1945839 = 2918759) B2918759
theorem B2918765 : Blo 1945435 2918765 := bbase (se 3 (by rfl) ⟨547268, by rfl⟩ : syracuseStep 2918765 = 1094537) (by norm_num)
theorem B1945843 : Blo 1945435 1945843 := bstep (se 1 (by rfl) ⟨1459382, by rfl⟩ : syracuseStep 1945843 = 2918765) B2918765
theorem B4378157 : Blo 1945435 4378157 := bbase (se 3 (by rfl) ⟨820904, by rfl⟩ : syracuseStep 4378157 = 1641809) (by norm_num)
theorem B2918771 : Blo 1945435 2918771 := bstep (se 1 (by rfl) ⟨2189078, by rfl⟩ : syracuseStep 2918771 = 4378157) B4378157
theorem B1945847 : Blo 1945435 1945847 := bstep (se 1 (by rfl) ⟨1459385, by rfl⟩ : syracuseStep 1945847 = 2918771) B2918771
theorem B13495349 : Blo 1945435 13495349 := bbase (se 5 (by rfl) ⟨632594, by rfl⟩ : syracuseStep 13495349 = 1265189) (by norm_num)
theorem B8996899 : Blo 1945435 8996899 := bstep (se 1 (by rfl) ⟨6747674, by rfl⟩ : syracuseStep 8996899 = 13495349) B13495349
theorem B11995865 : Blo 1945435 11995865 := bstep (se 2 (by rfl) ⟨4498449, by rfl⟩ : syracuseStep 11995865 = 8996899) B8996899
theorem B7997243 : Blo 1945435 7997243 := bstep (se 1 (by rfl) ⟨5997932, by rfl⟩ : syracuseStep 7997243 = 11995865) B11995865
theorem B85303925 : Blo 1945435 85303925 := bstep (se 5 (by rfl) ⟨3998621, by rfl⟩ : syracuseStep 85303925 = 7997243) B7997243
theorem B56869283 : Blo 1945435 56869283 := bstep (se 1 (by rfl) ⟨42651962, by rfl⟩ : syracuseStep 56869283 = 85303925) B85303925
theorem B37912855 : Blo 1945435 37912855 := bstep (se 1 (by rfl) ⟨28434641, by rfl⟩ : syracuseStep 37912855 = 56869283) B56869283
theorem B50550473 : Blo 1945435 50550473 := bstep (se 2 (by rfl) ⟨18956427, by rfl⟩ : syracuseStep 50550473 = 37912855) B37912855
theorem B33700315 : Blo 1945435 33700315 := bstep (se 1 (by rfl) ⟨25275236, by rfl⟩ : syracuseStep 33700315 = 50550473) B50550473
theorem B44933753 : Blo 1945435 44933753 := bstep (se 2 (by rfl) ⟨16850157, by rfl⟩ : syracuseStep 44933753 = 33700315) B33700315
theorem B29955835 : Blo 1945435 29955835 := bstep (se 1 (by rfl) ⟨22466876, by rfl⟩ : syracuseStep 29955835 = 44933753) B44933753
theorem B39941113 : Blo 1945435 39941113 := bstep (se 2 (by rfl) ⟨14977917, by rfl⟩ : syracuseStep 39941113 = 29955835) B29955835
theorem B53254817 : Blo 1945435 53254817 := bstep (se 2 (by rfl) ⟨19970556, by rfl⟩ : syracuseStep 53254817 = 39941113) B39941113
theorem B35503211 : Blo 1945435 35503211 := bstep (se 1 (by rfl) ⟨26627408, by rfl⟩ : syracuseStep 35503211 = 53254817) B53254817
theorem B94675229 : Blo 1945435 94675229 := bstep (se 3 (by rfl) ⟨17751605, by rfl⟩ : syracuseStep 94675229 = 35503211) B35503211
theorem B63116819 : Blo 1945435 63116819 := bstep (se 1 (by rfl) ⟨47337614, by rfl⟩ : syracuseStep 63116819 = 94675229) B94675229
theorem B42077879 : Blo 1945435 42077879 := bstep (se 1 (by rfl) ⟨31558409, by rfl⟩ : syracuseStep 42077879 = 63116819) B63116819
theorem B28051919 : Blo 1945435 28051919 := bstep (se 1 (by rfl) ⟨21038939, by rfl⟩ : syracuseStep 28051919 = 42077879) B42077879
theorem B18701279 : Blo 1945435 18701279 := bstep (se 1 (by rfl) ⟨14025959, by rfl⟩ : syracuseStep 18701279 = 28051919) B28051919
theorem B12467519 : Blo 1945435 12467519 := bstep (se 1 (by rfl) ⟨9350639, by rfl⟩ : syracuseStep 12467519 = 18701279) B18701279
theorem B8311679 : Blo 1945435 8311679 := bstep (se 1 (by rfl) ⟨6233759, by rfl⟩ : syracuseStep 8311679 = 12467519) B12467519
theorem B5541119 : Blo 1945435 5541119 := bstep (se 1 (by rfl) ⟨4155839, by rfl⟩ : syracuseStep 5541119 = 8311679) B8311679
theorem B3694079 : Blo 1945435 3694079 := bstep (se 1 (by rfl) ⟨2770559, by rfl⟩ : syracuseStep 3694079 = 5541119) B5541119
theorem B2462719 : Blo 1945435 2462719 := bstep (se 1 (by rfl) ⟨1847039, by rfl⟩ : syracuseStep 2462719 = 3694079) B3694079
theorem B3283625 : Blo 1945435 3283625 := bstep (se 2 (by rfl) ⟨1231359, by rfl⟩ : syracuseStep 3283625 = 2462719) B2462719
theorem B2189083 : Blo 1945435 2189083 := bstep (se 1 (by rfl) ⟨1641812, by rfl⟩ : syracuseStep 2189083 = 3283625) B3283625
theorem B2918777 : Blo 1945435 2918777 := bstep (se 2 (by rfl) ⟨1094541, by rfl⟩ : syracuseStep 2918777 = 2189083) B2189083
theorem B1945851 : Blo 1945435 1945851 := bstep (se 1 (by rfl) ⟨1459388, by rfl⟩ : syracuseStep 1945851 = 2918777) B2918777
theorem B3116885 : Blo 1945435 3116885 := bbase (se 9 (by rfl) ⟨9131, by rfl⟩ : syracuseStep 3116885 = 18263) (by norm_num)
theorem B33246773 : Blo 1945435 33246773 := bstep (se 5 (by rfl) ⟨1558442, by rfl⟩ : syracuseStep 33246773 = 3116885) B3116885
theorem B22164515 : Blo 1945435 22164515 := bstep (se 1 (by rfl) ⟨16623386, by rfl⟩ : syracuseStep 22164515 = 33246773) B33246773
theorem B14776343 : Blo 1945435 14776343 := bstep (se 1 (by rfl) ⟨11082257, by rfl⟩ : syracuseStep 14776343 = 22164515) B22164515
theorem B9850895 : Blo 1945435 9850895 := bstep (se 1 (by rfl) ⟨7388171, by rfl⟩ : syracuseStep 9850895 = 14776343) B14776343
theorem B6567263 : Blo 1945435 6567263 := bstep (se 1 (by rfl) ⟨4925447, by rfl⟩ : syracuseStep 6567263 = 9850895) B9850895
theorem B4378175 : Blo 1945435 4378175 := bstep (se 1 (by rfl) ⟨3283631, by rfl⟩ : syracuseStep 4378175 = 6567263) B6567263
theorem B2918783 : Blo 1945435 2918783 := bstep (se 1 (by rfl) ⟨2189087, by rfl⟩ : syracuseStep 2918783 = 4378175) B4378175
theorem B1945855 : Blo 1945435 1945855 := bstep (se 1 (by rfl) ⟨1459391, by rfl⟩ : syracuseStep 1945855 = 2918783) B2918783
theorem B2918789 : Blo 1945435 2918789 := bbase (se 4 (by rfl) ⟨273636, by rfl⟩ : syracuseStep 2918789 = 547273) (by norm_num)
theorem B1945859 : Blo 1945435 1945859 := bstep (se 1 (by rfl) ⟨1459394, by rfl⟩ : syracuseStep 1945859 = 2918789) B2918789
theorem B3283645 : Blo 1945435 3283645 := bbase (se 3 (by rfl) ⟨615683, by rfl⟩ : syracuseStep 3283645 = 1231367) (by norm_num)
theorem B4378193 : Blo 1945435 4378193 := bstep (se 2 (by rfl) ⟨1641822, by rfl⟩ : syracuseStep 4378193 = 3283645) B3283645
theorem B2918795 : Blo 1945435 2918795 := bstep (se 1 (by rfl) ⟨2189096, by rfl⟩ : syracuseStep 2918795 = 4378193) B4378193
theorem B1945863 : Blo 1945435 1945863 := bstep (se 1 (by rfl) ⟨1459397, by rfl⟩ : syracuseStep 1945863 = 2918795) B2918795
theorem B2189101 : Blo 1945435 2189101 := bbase (se 3 (by rfl) ⟨410456, by rfl⟩ : syracuseStep 2189101 = 820913) (by norm_num)
theorem B2918801 : Blo 1945435 2918801 := bstep (se 2 (by rfl) ⟨1094550, by rfl⟩ : syracuseStep 2918801 = 2189101) B2189101
theorem B1945867 : Blo 1945435 1945867 := bstep (se 1 (by rfl) ⟨1459400, by rfl⟩ : syracuseStep 1945867 = 2918801) B2918801
theorem B6567317 : Blo 1945435 6567317 := bbase (se 6 (by rfl) ⟨153921, by rfl⟩ : syracuseStep 6567317 = 307843) (by norm_num)
theorem B4378211 : Blo 1945435 4378211 := bstep (se 1 (by rfl) ⟨3283658, by rfl⟩ : syracuseStep 4378211 = 6567317) B6567317
theorem B2918807 : Blo 1945435 2918807 := bstep (se 1 (by rfl) ⟨2189105, by rfl⟩ : syracuseStep 2918807 = 4378211) B4378211
theorem B1945871 : Blo 1945435 1945871 := bstep (se 1 (by rfl) ⟨1459403, by rfl⟩ : syracuseStep 1945871 = 2918807) B2918807
theorem B2918813 : Blo 1945435 2918813 := bbase (se 3 (by rfl) ⟨547277, by rfl⟩ : syracuseStep 2918813 = 1094555) (by norm_num)
theorem B1945875 : Blo 1945435 1945875 := bstep (se 1 (by rfl) ⟨1459406, by rfl⟩ : syracuseStep 1945875 = 2918813) B2918813
theorem B4378229 : Blo 1945435 4378229 := bbase (se 5 (by rfl) ⟨205229, by rfl⟩ : syracuseStep 4378229 = 410459) (by norm_num)
theorem B2918819 : Blo 1945435 2918819 := bstep (se 1 (by rfl) ⟨2189114, by rfl⟩ : syracuseStep 2918819 = 4378229) B4378229
theorem B1945879 : Blo 1945435 1945879 := bstep (se 1 (by rfl) ⟨1459409, by rfl⟩ : syracuseStep 1945879 = 2918819) B2918819
theorem B6233861 : Blo 1945435 6233861 := bbase (se 4 (by rfl) ⟨584424, by rfl⟩ : syracuseStep 6233861 = 1168849) (by norm_num)
theorem B16623629 : Blo 1945435 16623629 := bstep (se 3 (by rfl) ⟨3116930, by rfl⟩ : syracuseStep 16623629 = 6233861) B6233861
theorem B11082419 : Blo 1945435 11082419 := bstep (se 1 (by rfl) ⟨8311814, by rfl⟩ : syracuseStep 11082419 = 16623629) B16623629
theorem B7388279 : Blo 1945435 7388279 := bstep (se 1 (by rfl) ⟨5541209, by rfl⟩ : syracuseStep 7388279 = 11082419) B11082419
theorem B4925519 : Blo 1945435 4925519 := bstep (se 1 (by rfl) ⟨3694139, by rfl⟩ : syracuseStep 4925519 = 7388279) B7388279
theorem B3283679 : Blo 1945435 3283679 := bstep (se 1 (by rfl) ⟨2462759, by rfl⟩ : syracuseStep 3283679 = 4925519) B4925519
theorem B2189119 : Blo 1945435 2189119 := bstep (se 1 (by rfl) ⟨1641839, by rfl⟩ : syracuseStep 2189119 = 3283679) B3283679
theorem B2918825 : Blo 1945435 2918825 := bstep (se 2 (by rfl) ⟨1094559, by rfl⟩ : syracuseStep 2918825 = 2189119) B2189119
theorem B1945883 : Blo 1945435 1945883 := bstep (se 1 (by rfl) ⟨1459412, by rfl⟩ : syracuseStep 1945883 = 2918825) B2918825
theorem B7388293 : Blo 1945435 7388293 := bbase (se 4 (by rfl) ⟨692652, by rfl⟩ : syracuseStep 7388293 = 1385305) (by norm_num)
theorem B9851057 : Blo 1945435 9851057 := bstep (se 2 (by rfl) ⟨3694146, by rfl⟩ : syracuseStep 9851057 = 7388293) B7388293
theorem B6567371 : Blo 1945435 6567371 := bstep (se 1 (by rfl) ⟨4925528, by rfl⟩ : syracuseStep 6567371 = 9851057) B9851057
theorem B4378247 : Blo 1945435 4378247 := bstep (se 1 (by rfl) ⟨3283685, by rfl⟩ : syracuseStep 4378247 = 6567371) B6567371
theorem B2918831 : Blo 1945435 2918831 := bstep (se 1 (by rfl) ⟨2189123, by rfl⟩ : syracuseStep 2918831 = 4378247) B4378247
theorem B1945887 : Blo 1945435 1945887 := bstep (se 1 (by rfl) ⟨1459415, by rfl⟩ : syracuseStep 1945887 = 2918831) B2918831
theorem B2918837 : Blo 1945435 2918837 := bbase (se 5 (by rfl) ⟨136820, by rfl⟩ : syracuseStep 2918837 = 273641) (by norm_num)
theorem B1945891 : Blo 1945435 1945891 := bstep (se 1 (by rfl) ⟨1459418, by rfl⟩ : syracuseStep 1945891 = 2918837) B2918837
theorem B4925549 : Blo 1945435 4925549 := bbase (se 3 (by rfl) ⟨923540, by rfl⟩ : syracuseStep 4925549 = 1847081) (by norm_num)
theorem B3283699 : Blo 1945435 3283699 := bstep (se 1 (by rfl) ⟨2462774, by rfl⟩ : syracuseStep 3283699 = 4925549) B4925549
theorem B4378265 : Blo 1945435 4378265 := bstep (se 2 (by rfl) ⟨1641849, by rfl⟩ : syracuseStep 4378265 = 3283699) B3283699
theorem B2918843 : Blo 1945435 2918843 := bstep (se 1 (by rfl) ⟨2189132, by rfl⟩ : syracuseStep 2918843 = 4378265) B4378265
theorem B1945895 : Blo 1945435 1945895 := bstep (se 1 (by rfl) ⟨1459421, by rfl⟩ : syracuseStep 1945895 = 2918843) B2918843
theorem B2189137 : Blo 1945435 2189137 := bbase (se 2 (by rfl) ⟨820926, by rfl⟩ : syracuseStep 2189137 = 1641853) (by norm_num)
theorem B2918849 : Blo 1945435 2918849 := bstep (se 2 (by rfl) ⟨1094568, by rfl⟩ : syracuseStep 2918849 = 2189137) B2189137
theorem B1945899 : Blo 1945435 1945899 := bstep (se 1 (by rfl) ⟨1459424, by rfl⟩ : syracuseStep 1945899 = 2918849) B2918849
theorem B4675445 : Blo 1945435 4675445 := bbase (se 5 (by rfl) ⟨219161, by rfl⟩ : syracuseStep 4675445 = 438323) (by norm_num)
theorem B3116963 : Blo 1945435 3116963 := bstep (se 1 (by rfl) ⟨2337722, by rfl⟩ : syracuseStep 3116963 = 4675445) B4675445
theorem B2077975 : Blo 1945435 2077975 := bstep (se 1 (by rfl) ⟨1558481, by rfl⟩ : syracuseStep 2077975 = 3116963) B3116963
theorem B2770633 : Blo 1945435 2770633 := bstep (se 2 (by rfl) ⟨1038987, by rfl⟩ : syracuseStep 2770633 = 2077975) B2077975
theorem B3694177 : Blo 1945435 3694177 := bstep (se 2 (by rfl) ⟨1385316, by rfl⟩ : syracuseStep 3694177 = 2770633) B2770633
theorem B4925569 : Blo 1945435 4925569 := bstep (se 2 (by rfl) ⟨1847088, by rfl⟩ : syracuseStep 4925569 = 3694177) B3694177
theorem B6567425 : Blo 1945435 6567425 := bstep (se 2 (by rfl) ⟨2462784, by rfl⟩ : syracuseStep 6567425 = 4925569) B4925569
theorem B4378283 : Blo 1945435 4378283 := bstep (se 1 (by rfl) ⟨3283712, by rfl⟩ : syracuseStep 4378283 = 6567425) B6567425
theorem B2918855 : Blo 1945435 2918855 := bstep (se 1 (by rfl) ⟨2189141, by rfl⟩ : syracuseStep 2918855 = 4378283) B4378283
theorem B1945903 : Blo 1945435 1945903 := bstep (se 1 (by rfl) ⟨1459427, by rfl⟩ : syracuseStep 1945903 = 2918855) B2918855
theorem B2918861 : Blo 1945435 2918861 := bbase (se 3 (by rfl) ⟨547286, by rfl⟩ : syracuseStep 2918861 = 1094573) (by norm_num)
theorem B1945907 : Blo 1945435 1945907 := bstep (se 1 (by rfl) ⟨1459430, by rfl⟩ : syracuseStep 1945907 = 2918861) B2918861
theorem B4378301 : Blo 1945435 4378301 := bbase (se 3 (by rfl) ⟨820931, by rfl⟩ : syracuseStep 4378301 = 1641863) (by norm_num)
theorem B2918867 : Blo 1945435 2918867 := bstep (se 1 (by rfl) ⟨2189150, by rfl⟩ : syracuseStep 2918867 = 4378301) B4378301
theorem B1945911 : Blo 1945435 1945911 := bstep (se 1 (by rfl) ⟨1459433, by rfl⟩ : syracuseStep 1945911 = 2918867) B2918867
theorem B3283733 : Blo 1945435 3283733 := bbase (se 6 (by rfl) ⟨76962, by rfl⟩ : syracuseStep 3283733 = 153925) (by norm_num)
theorem B2189155 : Blo 1945435 2189155 := bstep (se 1 (by rfl) ⟨1641866, by rfl⟩ : syracuseStep 2189155 = 3283733) B3283733
theorem B2918873 : Blo 1945435 2918873 := bstep (se 2 (by rfl) ⟨1094577, by rfl⟩ : syracuseStep 2918873 = 2189155) B2189155
theorem B1945915 : Blo 1945435 1945915 := bstep (se 1 (by rfl) ⟨1459436, by rfl⟩ : syracuseStep 1945915 = 2918873) B2918873
theorem B17994421 : Blo 1945435 17994421 := bbase (se 5 (by rfl) ⟨843488, by rfl⟩ : syracuseStep 17994421 = 1686977) (by norm_num)
theorem B23992561 : Blo 1945435 23992561 := bstep (se 2 (by rfl) ⟨8997210, by rfl⟩ : syracuseStep 23992561 = 17994421) B17994421
theorem B31990081 : Blo 1945435 31990081 := bstep (se 2 (by rfl) ⟨11996280, by rfl⟩ : syracuseStep 31990081 = 23992561) B23992561
theorem B42653441 : Blo 1945435 42653441 := bstep (se 2 (by rfl) ⟨15995040, by rfl⟩ : syracuseStep 42653441 = 31990081) B31990081
theorem B28435627 : Blo 1945435 28435627 := bstep (se 1 (by rfl) ⟨21326720, by rfl⟩ : syracuseStep 28435627 = 42653441) B42653441
theorem B37914169 : Blo 1945435 37914169 := bstep (se 2 (by rfl) ⟨14217813, by rfl⟩ : syracuseStep 37914169 = 28435627) B28435627
theorem B50552225 : Blo 1945435 50552225 := bstep (se 2 (by rfl) ⟨18957084, by rfl⟩ : syracuseStep 50552225 = 37914169) B37914169
theorem B33701483 : Blo 1945435 33701483 := bstep (se 1 (by rfl) ⟨25276112, by rfl⟩ : syracuseStep 33701483 = 50552225) B50552225
theorem B22467655 : Blo 1945435 22467655 := bstep (se 1 (by rfl) ⟨16850741, by rfl⟩ : syracuseStep 22467655 = 33701483) B33701483
theorem B29956873 : Blo 1945435 29956873 := bstep (se 2 (by rfl) ⟨11233827, by rfl⟩ : syracuseStep 29956873 = 22467655) B22467655
theorem B39942497 : Blo 1945435 39942497 := bstep (se 2 (by rfl) ⟨14978436, by rfl⟩ : syracuseStep 39942497 = 29956873) B29956873
theorem B106513325 : Blo 1945435 106513325 := bstep (se 3 (by rfl) ⟨19971248, by rfl⟩ : syracuseStep 106513325 = 39942497) B39942497
theorem B71008883 : Blo 1945435 71008883 := bstep (se 1 (by rfl) ⟨53256662, by rfl⟩ : syracuseStep 71008883 = 106513325) B106513325
theorem B47339255 : Blo 1945435 47339255 := bstep (se 1 (by rfl) ⟨35504441, by rfl⟩ : syracuseStep 47339255 = 71008883) B71008883
theorem B31559503 : Blo 1945435 31559503 := bstep (se 1 (by rfl) ⟨23669627, by rfl⟩ : syracuseStep 31559503 = 47339255) B47339255
theorem B42079337 : Blo 1945435 42079337 := bstep (se 2 (by rfl) ⟨15779751, by rfl⟩ : syracuseStep 42079337 = 31559503) B31559503
theorem B28052891 : Blo 1945435 28052891 := bstep (se 1 (by rfl) ⟨21039668, by rfl⟩ : syracuseStep 28052891 = 42079337) B42079337
theorem B18701927 : Blo 1945435 18701927 := bstep (se 1 (by rfl) ⟨14026445, by rfl⟩ : syracuseStep 18701927 = 28052891) B28052891
theorem B12467951 : Blo 1945435 12467951 := bstep (se 1 (by rfl) ⟨9350963, by rfl⟩ : syracuseStep 12467951 = 18701927) B18701927
theorem B8311967 : Blo 1945435 8311967 := bstep (se 1 (by rfl) ⟨6233975, by rfl⟩ : syracuseStep 8311967 = 12467951) B12467951
theorem B5541311 : Blo 1945435 5541311 := bstep (se 1 (by rfl) ⟨4155983, by rfl⟩ : syracuseStep 5541311 = 8311967) B8311967
theorem B14776829 : Blo 1945435 14776829 := bstep (se 3 (by rfl) ⟨2770655, by rfl⟩ : syracuseStep 14776829 = 5541311) B5541311
theorem B9851219 : Blo 1945435 9851219 := bstep (se 1 (by rfl) ⟨7388414, by rfl⟩ : syracuseStep 9851219 = 14776829) B14776829
theorem B6567479 : Blo 1945435 6567479 := bstep (se 1 (by rfl) ⟨4925609, by rfl⟩ : syracuseStep 6567479 = 9851219) B9851219
theorem B4378319 : Blo 1945435 4378319 := bstep (se 1 (by rfl) ⟨3283739, by rfl⟩ : syracuseStep 4378319 = 6567479) B6567479
theorem B2918879 : Blo 1945435 2918879 := bstep (se 1 (by rfl) ⟨2189159, by rfl⟩ : syracuseStep 2918879 = 4378319) B4378319
theorem B1945919 : Blo 1945435 1945919 := bstep (se 1 (by rfl) ⟨1459439, by rfl⟩ : syracuseStep 1945919 = 2918879) B2918879
theorem B2918885 : Blo 1945435 2918885 := bbase (se 4 (by rfl) ⟨273645, by rfl⟩ : syracuseStep 2918885 = 547291) (by norm_num)
theorem B1945923 : Blo 1945435 1945923 := bstep (se 1 (by rfl) ⟨1459442, by rfl⟩ : syracuseStep 1945923 = 2918885) B2918885
theorem B5259941 : Blo 1945435 5259941 := bbase (se 4 (by rfl) ⟨493119, by rfl⟩ : syracuseStep 5259941 = 986239) (by norm_num)
theorem B3506627 : Blo 1945435 3506627 := bstep (se 1 (by rfl) ⟨2629970, by rfl⟩ : syracuseStep 3506627 = 5259941) B5259941
theorem B2337751 : Blo 1945435 2337751 := bstep (se 1 (by rfl) ⟨1753313, by rfl⟩ : syracuseStep 2337751 = 3506627) B3506627
theorem B12468005 : Blo 1945435 12468005 := bstep (se 4 (by rfl) ⟨1168875, by rfl⟩ : syracuseStep 12468005 = 2337751) B2337751
theorem B8312003 : Blo 1945435 8312003 := bstep (se 1 (by rfl) ⟨6234002, by rfl⟩ : syracuseStep 8312003 = 12468005) B12468005
theorem B5541335 : Blo 1945435 5541335 := bstep (se 1 (by rfl) ⟨4156001, by rfl⟩ : syracuseStep 5541335 = 8312003) B8312003
theorem B3694223 : Blo 1945435 3694223 := bstep (se 1 (by rfl) ⟨2770667, by rfl⟩ : syracuseStep 3694223 = 5541335) B5541335
theorem B2462815 : Blo 1945435 2462815 := bstep (se 1 (by rfl) ⟨1847111, by rfl⟩ : syracuseStep 2462815 = 3694223) B3694223
theorem B3283753 : Blo 1945435 3283753 := bstep (se 2 (by rfl) ⟨1231407, by rfl⟩ : syracuseStep 3283753 = 2462815) B2462815
theorem B4378337 : Blo 1945435 4378337 := bstep (se 2 (by rfl) ⟨1641876, by rfl⟩ : syracuseStep 4378337 = 3283753) B3283753
theorem B2918891 : Blo 1945435 2918891 := bstep (se 1 (by rfl) ⟨2189168, by rfl⟩ : syracuseStep 2918891 = 4378337) B4378337
theorem B1945927 : Blo 1945435 1945927 := bstep (se 1 (by rfl) ⟨1459445, by rfl⟩ : syracuseStep 1945927 = 2918891) B2918891
theorem B2189173 : Blo 1945435 2189173 := bbase (se 5 (by rfl) ⟨102617, by rfl⟩ : syracuseStep 2189173 = 205235) (by norm_num)
theorem B2918897 : Blo 1945435 2918897 := bstep (se 2 (by rfl) ⟨1094586, by rfl⟩ : syracuseStep 2918897 = 2189173) B2189173
theorem B1945931 : Blo 1945435 1945931 := bstep (se 1 (by rfl) ⟨1459448, by rfl⟩ : syracuseStep 1945931 = 2918897) B2918897
theorem B2462825 : Blo 1945435 2462825 := bbase (se 2 (by rfl) ⟨923559, by rfl⟩ : syracuseStep 2462825 = 1847119) (by norm_num)
theorem B6567533 : Blo 1945435 6567533 := bstep (se 3 (by rfl) ⟨1231412, by rfl⟩ : syracuseStep 6567533 = 2462825) B2462825
theorem B4378355 : Blo 1945435 4378355 := bstep (se 1 (by rfl) ⟨3283766, by rfl⟩ : syracuseStep 4378355 = 6567533) B6567533
theorem B2918903 : Blo 1945435 2918903 := bstep (se 1 (by rfl) ⟨2189177, by rfl⟩ : syracuseStep 2918903 = 4378355) B4378355
theorem B1945935 : Blo 1945435 1945935 := bstep (se 1 (by rfl) ⟨1459451, by rfl⟩ : syracuseStep 1945935 = 2918903) B2918903
theorem B2918909 : Blo 1945435 2918909 := bbase (se 3 (by rfl) ⟨547295, by rfl⟩ : syracuseStep 2918909 = 1094591) (by norm_num)
theorem B1945939 : Blo 1945435 1945939 := bstep (se 1 (by rfl) ⟨1459454, by rfl⟩ : syracuseStep 1945939 = 2918909) B2918909
theorem B4378373 : Blo 1945435 4378373 := bbase (se 4 (by rfl) ⟨410472, by rfl⟩ : syracuseStep 4378373 = 820945) (by norm_num)
theorem B2918915 : Blo 1945435 2918915 := bstep (se 1 (by rfl) ⟨2189186, by rfl⟩ : syracuseStep 2918915 = 4378373) B4378373
theorem B1945943 : Blo 1945435 1945943 := bstep (se 1 (by rfl) ⟨1459457, by rfl⟩ : syracuseStep 1945943 = 2918915) B2918915
theorem B3694261 : Blo 1945435 3694261 := bbase (se 5 (by rfl) ⟨173168, by rfl⟩ : syracuseStep 3694261 = 346337) (by norm_num)
theorem B4925681 : Blo 1945435 4925681 := bstep (se 2 (by rfl) ⟨1847130, by rfl⟩ : syracuseStep 4925681 = 3694261) B3694261
theorem B3283787 : Blo 1945435 3283787 := bstep (se 1 (by rfl) ⟨2462840, by rfl⟩ : syracuseStep 3283787 = 4925681) B4925681
theorem B2189191 : Blo 1945435 2189191 := bstep (se 1 (by rfl) ⟨1641893, by rfl⟩ : syracuseStep 2189191 = 3283787) B3283787
theorem B2918921 : Blo 1945435 2918921 := bstep (se 2 (by rfl) ⟨1094595, by rfl⟩ : syracuseStep 2918921 = 2189191) B2189191
theorem B1945947 : Blo 1945435 1945947 := bstep (se 1 (by rfl) ⟨1459460, by rfl⟩ : syracuseStep 1945947 = 2918921) B2918921
theorem B9851381 : Blo 1945435 9851381 := bbase (se 5 (by rfl) ⟨461783, by rfl⟩ : syracuseStep 9851381 = 923567) (by norm_num)
theorem B6567587 : Blo 1945435 6567587 := bstep (se 1 (by rfl) ⟨4925690, by rfl⟩ : syracuseStep 6567587 = 9851381) B9851381
theorem B4378391 : Blo 1945435 4378391 := bstep (se 1 (by rfl) ⟨3283793, by rfl⟩ : syracuseStep 4378391 = 6567587) B6567587
theorem B2918927 : Blo 1945435 2918927 := bstep (se 1 (by rfl) ⟨2189195, by rfl⟩ : syracuseStep 2918927 = 4378391) B4378391
theorem B1945951 : Blo 1945435 1945951 := bstep (se 1 (by rfl) ⟨1459463, by rfl⟩ : syracuseStep 1945951 = 2918927) B2918927
theorem B2918933 : Blo 1945435 2918933 := bbase (se 6 (by rfl) ⟨68412, by rfl⟩ : syracuseStep 2918933 = 136825) (by norm_num)
theorem B1945955 : Blo 1945435 1945955 := bstep (se 1 (by rfl) ⟨1459466, by rfl⟩ : syracuseStep 1945955 = 2918933) B2918933
theorem B16624277 : Blo 1945435 16624277 := bbase (se 6 (by rfl) ⟨389631, by rfl⟩ : syracuseStep 16624277 = 779263) (by norm_num)
theorem B11082851 : Blo 1945435 11082851 := bstep (se 1 (by rfl) ⟨8312138, by rfl⟩ : syracuseStep 11082851 = 16624277) B16624277
theorem B7388567 : Blo 1945435 7388567 := bstep (se 1 (by rfl) ⟨5541425, by rfl⟩ : syracuseStep 7388567 = 11082851) B11082851
theorem B4925711 : Blo 1945435 4925711 := bstep (se 1 (by rfl) ⟨3694283, by rfl⟩ : syracuseStep 4925711 = 7388567) B7388567
theorem B3283807 : Blo 1945435 3283807 := bstep (se 1 (by rfl) ⟨2462855, by rfl⟩ : syracuseStep 3283807 = 4925711) B4925711
theorem B4378409 : Blo 1945435 4378409 := bstep (se 2 (by rfl) ⟨1641903, by rfl⟩ : syracuseStep 4378409 = 3283807) B3283807
theorem B2918939 : Blo 1945435 2918939 := bstep (se 1 (by rfl) ⟨2189204, by rfl⟩ : syracuseStep 2918939 = 4378409) B4378409
theorem B1945959 : Blo 1945435 1945959 := bstep (se 1 (by rfl) ⟨1459469, by rfl⟩ : syracuseStep 1945959 = 2918939) B2918939
theorem B2189209 : Blo 1945435 2189209 := bbase (se 2 (by rfl) ⟨820953, by rfl⟩ : syracuseStep 2189209 = 1641907) (by norm_num)
theorem B2918945 : Blo 1945435 2918945 := bstep (se 2 (by rfl) ⟨1094604, by rfl⟩ : syracuseStep 2918945 = 2189209) B2189209
theorem B1945963 : Blo 1945435 1945963 := bstep (se 1 (by rfl) ⟨1459472, by rfl⟩ : syracuseStep 1945963 = 2918945) B2918945
theorem B7388597 : Blo 1945435 7388597 := bbase (se 5 (by rfl) ⟨346340, by rfl⟩ : syracuseStep 7388597 = 692681) (by norm_num)
theorem B4925731 : Blo 1945435 4925731 := bstep (se 1 (by rfl) ⟨3694298, by rfl⟩ : syracuseStep 4925731 = 7388597) B7388597
theorem B6567641 : Blo 1945435 6567641 := bstep (se 2 (by rfl) ⟨2462865, by rfl⟩ : syracuseStep 6567641 = 4925731) B4925731
theorem B4378427 : Blo 1945435 4378427 := bstep (se 1 (by rfl) ⟨3283820, by rfl⟩ : syracuseStep 4378427 = 6567641) B6567641
theorem B2918951 : Blo 1945435 2918951 := bstep (se 1 (by rfl) ⟨2189213, by rfl⟩ : syracuseStep 2918951 = 4378427) B4378427
theorem B1945967 : Blo 1945435 1945967 := bstep (se 1 (by rfl) ⟨1459475, by rfl⟩ : syracuseStep 1945967 = 2918951) B2918951
theorem B2918957 : Blo 1945435 2918957 := bbase (se 3 (by rfl) ⟨547304, by rfl⟩ : syracuseStep 2918957 = 1094609) (by norm_num)
theorem B1945971 : Blo 1945435 1945971 := bstep (se 1 (by rfl) ⟨1459478, by rfl⟩ : syracuseStep 1945971 = 2918957) B2918957
theorem B4378445 : Blo 1945435 4378445 := bbase (se 3 (by rfl) ⟨820958, by rfl⟩ : syracuseStep 4378445 = 1641917) (by norm_num)
theorem B2918963 : Blo 1945435 2918963 := bstep (se 1 (by rfl) ⟨2189222, by rfl⟩ : syracuseStep 2918963 = 4378445) B4378445
theorem B1945975 : Blo 1945435 1945975 := bstep (se 1 (by rfl) ⟨1459481, by rfl⟩ : syracuseStep 1945975 = 2918963) B2918963
theorem B2462881 : Blo 1945435 2462881 := bbase (se 2 (by rfl) ⟨923580, by rfl⟩ : syracuseStep 2462881 = 1847161) (by norm_num)
theorem B3283841 : Blo 1945435 3283841 := bstep (se 2 (by rfl) ⟨1231440, by rfl⟩ : syracuseStep 3283841 = 2462881) B2462881
theorem B2189227 : Blo 1945435 2189227 := bstep (se 1 (by rfl) ⟨1641920, by rfl⟩ : syracuseStep 2189227 = 3283841) B3283841
theorem B2918969 : Blo 1945435 2918969 := bstep (se 2 (by rfl) ⟨1094613, by rfl⟩ : syracuseStep 2918969 = 2189227) B2189227
theorem B1945979 : Blo 1945435 1945979 := bstep (se 1 (by rfl) ⟨1459484, by rfl⟩ : syracuseStep 1945979 = 2918969) B2918969
theorem B22165973 : Blo 1945435 22165973 := bbase (se 7 (by rfl) ⟨259757, by rfl⟩ : syracuseStep 22165973 = 519515) (by norm_num)
theorem B14777315 : Blo 1945435 14777315 := bstep (se 1 (by rfl) ⟨11082986, by rfl⟩ : syracuseStep 14777315 = 22165973) B22165973
theorem B9851543 : Blo 1945435 9851543 := bstep (se 1 (by rfl) ⟨7388657, by rfl⟩ : syracuseStep 9851543 = 14777315) B14777315
theorem B6567695 : Blo 1945435 6567695 := bstep (se 1 (by rfl) ⟨4925771, by rfl⟩ : syracuseStep 6567695 = 9851543) B9851543
theorem B4378463 : Blo 1945435 4378463 := bstep (se 1 (by rfl) ⟨3283847, by rfl⟩ : syracuseStep 4378463 = 6567695) B6567695
theorem B2918975 : Blo 1945435 2918975 := bstep (se 1 (by rfl) ⟨2189231, by rfl⟩ : syracuseStep 2918975 = 4378463) B4378463
theorem B1945983 : Blo 1945435 1945983 := bstep (se 1 (by rfl) ⟨1459487, by rfl⟩ : syracuseStep 1945983 = 2918975) B2918975
theorem B2918981 : Blo 1945435 2918981 := bbase (se 4 (by rfl) ⟨273654, by rfl⟩ : syracuseStep 2918981 = 547309) (by norm_num)
theorem B1945987 : Blo 1945435 1945987 := bstep (se 1 (by rfl) ⟨1459490, by rfl⟩ : syracuseStep 1945987 = 2918981) B2918981
theorem B3283861 : Blo 1945435 3283861 := bbase (se 6 (by rfl) ⟨76965, by rfl⟩ : syracuseStep 3283861 = 153931) (by norm_num)
theorem B4378481 : Blo 1945435 4378481 := bstep (se 2 (by rfl) ⟨1641930, by rfl⟩ : syracuseStep 4378481 = 3283861) B3283861
theorem B2918987 : Blo 1945435 2918987 := bstep (se 1 (by rfl) ⟨2189240, by rfl⟩ : syracuseStep 2918987 = 4378481) B4378481
theorem B1945991 : Blo 1945435 1945991 := bstep (se 1 (by rfl) ⟨1459493, by rfl⟩ : syracuseStep 1945991 = 2918987) B2918987
theorem B2189245 : Blo 1945435 2189245 := bbase (se 3 (by rfl) ⟨410483, by rfl⟩ : syracuseStep 2189245 = 820967) (by norm_num)
theorem B2918993 : Blo 1945435 2918993 := bstep (se 2 (by rfl) ⟨1094622, by rfl⟩ : syracuseStep 2918993 = 2189245) B2189245
theorem B1945995 : Blo 1945435 1945995 := bstep (se 1 (by rfl) ⟨1459496, by rfl⟩ : syracuseStep 1945995 = 2918993) B2918993
theorem B6567749 : Blo 1945435 6567749 := bbase (se 4 (by rfl) ⟨615726, by rfl⟩ : syracuseStep 6567749 = 1231453) (by norm_num)
theorem B4378499 : Blo 1945435 4378499 := bstep (se 1 (by rfl) ⟨3283874, by rfl⟩ : syracuseStep 4378499 = 6567749) B6567749
theorem B2918999 : Blo 1945435 2918999 := bstep (se 1 (by rfl) ⟨2189249, by rfl⟩ : syracuseStep 2918999 = 4378499) B4378499
theorem B1945999 : Blo 1945435 1945999 := bstep (se 1 (by rfl) ⟨1459499, by rfl⟩ : syracuseStep 1945999 = 2918999) B2918999
theorem B2919005 : Blo 1945435 2919005 := bbase (se 3 (by rfl) ⟨547313, by rfl⟩ : syracuseStep 2919005 = 1094627) (by norm_num)
theorem B1946003 : Blo 1945435 1946003 := bstep (se 1 (by rfl) ⟨1459502, by rfl⟩ : syracuseStep 1946003 = 2919005) B2919005
theorem B4378517 : Blo 1945435 4378517 := bbase (se 6 (by rfl) ⟨102621, by rfl⟩ : syracuseStep 4378517 = 205243) (by norm_num)
theorem B2919011 : Blo 1945435 2919011 := bstep (se 1 (by rfl) ⟨2189258, by rfl⟩ : syracuseStep 2919011 = 4378517) B4378517
theorem B1946007 : Blo 1945435 1946007 := bstep (se 1 (by rfl) ⟨1459505, by rfl⟩ : syracuseStep 1946007 = 2919011) B2919011
theorem B4156181 : Blo 1945435 4156181 := bbase (se 6 (by rfl) ⟨97410, by rfl⟩ : syracuseStep 4156181 = 194821) (by norm_num)
theorem B2770787 : Blo 1945435 2770787 := bstep (se 1 (by rfl) ⟨2078090, by rfl⟩ : syracuseStep 2770787 = 4156181) B4156181
theorem B7388765 : Blo 1945435 7388765 := bstep (se 3 (by rfl) ⟨1385393, by rfl⟩ : syracuseStep 7388765 = 2770787) B2770787
theorem B4925843 : Blo 1945435 4925843 := bstep (se 1 (by rfl) ⟨3694382, by rfl⟩ : syracuseStep 4925843 = 7388765) B7388765
theorem B3283895 : Blo 1945435 3283895 := bstep (se 1 (by rfl) ⟨2462921, by rfl⟩ : syracuseStep 3283895 = 4925843) B4925843
theorem B2189263 : Blo 1945435 2189263 := bstep (se 1 (by rfl) ⟨1641947, by rfl⟩ : syracuseStep 2189263 = 3283895) B3283895
theorem B2919017 : Blo 1945435 2919017 := bstep (se 2 (by rfl) ⟨1094631, by rfl⟩ : syracuseStep 2919017 = 2189263) B2189263
theorem B1946011 : Blo 1945435 1946011 := bstep (se 1 (by rfl) ⟨1459508, by rfl⟩ : syracuseStep 1946011 = 2919017) B2919017
theorem B3945133 : Blo 1945435 3945133 := bbase (se 3 (by rfl) ⟨739712, by rfl⟩ : syracuseStep 3945133 = 1479425) (by norm_num)
theorem B5260177 : Blo 1945435 5260177 := bstep (se 2 (by rfl) ⟨1972566, by rfl⟩ : syracuseStep 5260177 = 3945133) B3945133
theorem B7013569 : Blo 1945435 7013569 := bstep (se 2 (by rfl) ⟨2630088, by rfl⟩ : syracuseStep 7013569 = 5260177) B5260177
theorem B9351425 : Blo 1945435 9351425 := bstep (se 2 (by rfl) ⟨3506784, by rfl⟩ : syracuseStep 9351425 = 7013569) B7013569
theorem B6234283 : Blo 1945435 6234283 := bstep (se 1 (by rfl) ⟨4675712, by rfl⟩ : syracuseStep 6234283 = 9351425) B9351425
theorem B8312377 : Blo 1945435 8312377 := bstep (se 2 (by rfl) ⟨3117141, by rfl⟩ : syracuseStep 8312377 = 6234283) B6234283
theorem B11083169 : Blo 1945435 11083169 := bstep (se 2 (by rfl) ⟨4156188, by rfl⟩ : syracuseStep 11083169 = 8312377) B8312377
theorem B7388779 : Blo 1945435 7388779 := bstep (se 1 (by rfl) ⟨5541584, by rfl⟩ : syracuseStep 7388779 = 11083169) B11083169
theorem B9851705 : Blo 1945435 9851705 := bstep (se 2 (by rfl) ⟨3694389, by rfl⟩ : syracuseStep 9851705 = 7388779) B7388779
theorem B6567803 : Blo 1945435 6567803 := bstep (se 1 (by rfl) ⟨4925852, by rfl⟩ : syracuseStep 6567803 = 9851705) B9851705
theorem B4378535 : Blo 1945435 4378535 := bstep (se 1 (by rfl) ⟨3283901, by rfl⟩ : syracuseStep 4378535 = 6567803) B6567803
theorem B2919023 : Blo 1945435 2919023 := bstep (se 1 (by rfl) ⟨2189267, by rfl⟩ : syracuseStep 2919023 = 4378535) B4378535
theorem B1946015 : Blo 1945435 1946015 := bstep (se 1 (by rfl) ⟨1459511, by rfl⟩ : syracuseStep 1946015 = 2919023) B2919023
theorem B2919029 : Blo 1945435 2919029 := bbase (se 5 (by rfl) ⟨136829, by rfl⟩ : syracuseStep 2919029 = 273659) (by norm_num)
theorem B1946019 : Blo 1945435 1946019 := bstep (se 1 (by rfl) ⟨1459514, by rfl⟩ : syracuseStep 1946019 = 2919029) B2919029
theorem B3694405 : Blo 1945435 3694405 := bbase (se 4 (by rfl) ⟨346350, by rfl⟩ : syracuseStep 3694405 = 692701) (by norm_num)
theorem B4925873 : Blo 1945435 4925873 := bstep (se 2 (by rfl) ⟨1847202, by rfl⟩ : syracuseStep 4925873 = 3694405) B3694405
theorem B3283915 : Blo 1945435 3283915 := bstep (se 1 (by rfl) ⟨2462936, by rfl⟩ : syracuseStep 3283915 = 4925873) B4925873
theorem B4378553 : Blo 1945435 4378553 := bstep (se 2 (by rfl) ⟨1641957, by rfl⟩ : syracuseStep 4378553 = 3283915) B3283915
theorem B2919035 : Blo 1945435 2919035 := bstep (se 1 (by rfl) ⟨2189276, by rfl⟩ : syracuseStep 2919035 = 4378553) B4378553
theorem B1946023 : Blo 1945435 1946023 := bstep (se 1 (by rfl) ⟨1459517, by rfl⟩ : syracuseStep 1946023 = 2919035) B2919035
theorem B2189281 : Blo 1945435 2189281 := bbase (se 2 (by rfl) ⟨820980, by rfl⟩ : syracuseStep 2189281 = 1641961) (by norm_num)
theorem B2919041 : Blo 1945435 2919041 := bstep (se 2 (by rfl) ⟨1094640, by rfl⟩ : syracuseStep 2919041 = 2189281) B2189281
theorem B1946027 : Blo 1945435 1946027 := bstep (se 1 (by rfl) ⟨1459520, by rfl⟩ : syracuseStep 1946027 = 2919041) B2919041
theorem B4925893 : Blo 1945435 4925893 := bbase (se 4 (by rfl) ⟨461802, by rfl⟩ : syracuseStep 4925893 = 923605) (by norm_num)
theorem B6567857 : Blo 1945435 6567857 := bstep (se 2 (by rfl) ⟨2462946, by rfl⟩ : syracuseStep 6567857 = 4925893) B4925893
theorem B4378571 : Blo 1945435 4378571 := bstep (se 1 (by rfl) ⟨3283928, by rfl⟩ : syracuseStep 4378571 = 6567857) B6567857
theorem B2919047 : Blo 1945435 2919047 := bstep (se 1 (by rfl) ⟨2189285, by rfl⟩ : syracuseStep 2919047 = 4378571) B4378571
theorem B1946031 : Blo 1945435 1946031 := bstep (se 1 (by rfl) ⟨1459523, by rfl⟩ : syracuseStep 1946031 = 2919047) B2919047
theorem B2919053 : Blo 1945435 2919053 := bbase (se 3 (by rfl) ⟨547322, by rfl⟩ : syracuseStep 2919053 = 1094645) (by norm_num)
theorem B1946035 : Blo 1945435 1946035 := bstep (se 1 (by rfl) ⟨1459526, by rfl⟩ : syracuseStep 1946035 = 2919053) B2919053
theorem B4378589 : Blo 1945435 4378589 := bbase (se 3 (by rfl) ⟨820985, by rfl⟩ : syracuseStep 4378589 = 1641971) (by norm_num)
theorem B2919059 : Blo 1945435 2919059 := bstep (se 1 (by rfl) ⟨2189294, by rfl⟩ : syracuseStep 2919059 = 4378589) B4378589
theorem B1946039 : Blo 1945435 1946039 := bstep (se 1 (by rfl) ⟨1459529, by rfl⟩ : syracuseStep 1946039 = 2919059) B2919059
theorem B3283949 : Blo 1945435 3283949 := bbase (se 3 (by rfl) ⟨615740, by rfl⟩ : syracuseStep 3283949 = 1231481) (by norm_num)
theorem B2189299 : Blo 1945435 2189299 := bstep (se 1 (by rfl) ⟨1641974, by rfl⟩ : syracuseStep 2189299 = 3283949) B3283949
theorem B2919065 : Blo 1945435 2919065 := bstep (se 2 (by rfl) ⟨1094649, by rfl⟩ : syracuseStep 2919065 = 2189299) B2189299
theorem B1946043 : Blo 1945435 1946043 := bstep (se 1 (by rfl) ⟨1459532, by rfl⟩ : syracuseStep 1946043 = 2919065) B2919065
theorem B4675789 : Blo 1945435 4675789 := bbase (se 3 (by rfl) ⟨876710, by rfl⟩ : syracuseStep 4675789 = 1753421) (by norm_num)
theorem B24937541 : Blo 1945435 24937541 := bstep (se 4 (by rfl) ⟨2337894, by rfl⟩ : syracuseStep 24937541 = 4675789) B4675789
theorem B16625027 : Blo 1945435 16625027 := bstep (se 1 (by rfl) ⟨12468770, by rfl⟩ : syracuseStep 16625027 = 24937541) B24937541
theorem B11083351 : Blo 1945435 11083351 := bstep (se 1 (by rfl) ⟨8312513, by rfl⟩ : syracuseStep 11083351 = 16625027) B16625027
theorem B14777801 : Blo 1945435 14777801 := bstep (se 2 (by rfl) ⟨5541675, by rfl⟩ : syracuseStep 14777801 = 11083351) B11083351
theorem B9851867 : Blo 1945435 9851867 := bstep (se 1 (by rfl) ⟨7388900, by rfl⟩ : syracuseStep 9851867 = 14777801) B14777801
theorem B6567911 : Blo 1945435 6567911 := bstep (se 1 (by rfl) ⟨4925933, by rfl⟩ : syracuseStep 6567911 = 9851867) B9851867
theorem B4378607 : Blo 1945435 4378607 := bstep (se 1 (by rfl) ⟨3283955, by rfl⟩ : syracuseStep 4378607 = 6567911) B6567911
theorem B2919071 : Blo 1945435 2919071 := bstep (se 1 (by rfl) ⟨2189303, by rfl⟩ : syracuseStep 2919071 = 4378607) B4378607
theorem B1946047 : Blo 1945435 1946047 := bstep (se 1 (by rfl) ⟨1459535, by rfl⟩ : syracuseStep 1946047 = 2919071) B2919071
theorem B2919077 : Blo 1945435 2919077 := bbase (se 4 (by rfl) ⟨273663, by rfl⟩ : syracuseStep 2919077 = 547327) (by norm_num)
theorem B1946051 : Blo 1945435 1946051 := bstep (se 1 (by rfl) ⟨1459538, by rfl⟩ : syracuseStep 1946051 = 2919077) B2919077
theorem B2462977 : Blo 1945435 2462977 := bbase (se 2 (by rfl) ⟨923616, by rfl⟩ : syracuseStep 2462977 = 1847233) (by norm_num)
theorem B3283969 : Blo 1945435 3283969 := bstep (se 2 (by rfl) ⟨1231488, by rfl⟩ : syracuseStep 3283969 = 2462977) B2462977
theorem B4378625 : Blo 1945435 4378625 := bstep (se 2 (by rfl) ⟨1641984, by rfl⟩ : syracuseStep 4378625 = 3283969) B3283969
theorem B2919083 : Blo 1945435 2919083 := bstep (se 1 (by rfl) ⟨2189312, by rfl⟩ : syracuseStep 2919083 = 4378625) B4378625
theorem B1946055 : Blo 1945435 1946055 := bstep (se 1 (by rfl) ⟨1459541, by rfl⟩ : syracuseStep 1946055 = 2919083) B2919083
theorem B2189317 : Blo 1945435 2189317 := bbase (se 4 (by rfl) ⟨205248, by rfl⟩ : syracuseStep 2189317 = 410497) (by norm_num)
theorem B2919089 : Blo 1945435 2919089 := bstep (se 2 (by rfl) ⟨1094658, by rfl⟩ : syracuseStep 2919089 = 2189317) B2189317
theorem B1946059 : Blo 1945435 1946059 := bstep (se 1 (by rfl) ⟨1459544, by rfl⟩ : syracuseStep 1946059 = 2919089) B2919089
theorem B2770861 : Blo 1945435 2770861 := bbase (se 3 (by rfl) ⟨519536, by rfl⟩ : syracuseStep 2770861 = 1039073) (by norm_num)
theorem B3694481 : Blo 1945435 3694481 := bstep (se 2 (by rfl) ⟨1385430, by rfl⟩ : syracuseStep 3694481 = 2770861) B2770861
theorem B2462987 : Blo 1945435 2462987 := bstep (se 1 (by rfl) ⟨1847240, by rfl⟩ : syracuseStep 2462987 = 3694481) B3694481
theorem B6567965 : Blo 1945435 6567965 := bstep (se 3 (by rfl) ⟨1231493, by rfl⟩ : syracuseStep 6567965 = 2462987) B2462987
theorem B4378643 : Blo 1945435 4378643 := bstep (se 1 (by rfl) ⟨3283982, by rfl⟩ : syracuseStep 4378643 = 6567965) B6567965
theorem B2919095 : Blo 1945435 2919095 := bstep (se 1 (by rfl) ⟨2189321, by rfl⟩ : syracuseStep 2919095 = 4378643) B4378643
theorem B1946063 : Blo 1945435 1946063 := bstep (se 1 (by rfl) ⟨1459547, by rfl⟩ : syracuseStep 1946063 = 2919095) B2919095
theorem B2919101 : Blo 1945435 2919101 := bbase (se 3 (by rfl) ⟨547331, by rfl⟩ : syracuseStep 2919101 = 1094663) (by norm_num)
theorem B1946067 : Blo 1945435 1946067 := bstep (se 1 (by rfl) ⟨1459550, by rfl⟩ : syracuseStep 1946067 = 2919101) B2919101
theorem B4378661 : Blo 1945435 4378661 := bbase (se 4 (by rfl) ⟨410499, by rfl⟩ : syracuseStep 4378661 = 820999) (by norm_num)
theorem B2919107 : Blo 1945435 2919107 := bstep (se 1 (by rfl) ⟨2189330, by rfl⟩ : syracuseStep 2919107 = 4378661) B4378661
theorem B1946071 : Blo 1945435 1946071 := bstep (se 1 (by rfl) ⟨1459553, by rfl⟩ : syracuseStep 1946071 = 2919107) B2919107
theorem B4926005 : Blo 1945435 4926005 := bbase (se 5 (by rfl) ⟨230906, by rfl⟩ : syracuseStep 4926005 = 461813) (by norm_num)
theorem B3284003 : Blo 1945435 3284003 := bstep (se 1 (by rfl) ⟨2463002, by rfl⟩ : syracuseStep 3284003 = 4926005) B4926005
theorem B2189335 : Blo 1945435 2189335 := bstep (se 1 (by rfl) ⟨1642001, by rfl⟩ : syracuseStep 2189335 = 3284003) B3284003
theorem B2919113 : Blo 1945435 2919113 := bstep (se 2 (by rfl) ⟨1094667, by rfl⟩ : syracuseStep 2919113 = 2189335) B2189335
theorem B1946075 : Blo 1945435 1946075 := bstep (se 1 (by rfl) ⟨1459556, by rfl⟩ : syracuseStep 1946075 = 2919113) B2919113
theorem B9351733 : Blo 1945435 9351733 := bbase (se 5 (by rfl) ⟨438362, by rfl⟩ : syracuseStep 9351733 = 876725) (by norm_num)
theorem B12468977 : Blo 1945435 12468977 := bstep (se 2 (by rfl) ⟨4675866, by rfl⟩ : syracuseStep 12468977 = 9351733) B9351733
theorem B8312651 : Blo 1945435 8312651 := bstep (se 1 (by rfl) ⟨6234488, by rfl⟩ : syracuseStep 8312651 = 12468977) B12468977
theorem B5541767 : Blo 1945435 5541767 := bstep (se 1 (by rfl) ⟨4156325, by rfl⟩ : syracuseStep 5541767 = 8312651) B8312651
theorem B3694511 : Blo 1945435 3694511 := bstep (se 1 (by rfl) ⟨2770883, by rfl⟩ : syracuseStep 3694511 = 5541767) B5541767
theorem B9852029 : Blo 1945435 9852029 := bstep (se 3 (by rfl) ⟨1847255, by rfl⟩ : syracuseStep 9852029 = 3694511) B3694511
theorem B6568019 : Blo 1945435 6568019 := bstep (se 1 (by rfl) ⟨4926014, by rfl⟩ : syracuseStep 6568019 = 9852029) B9852029
theorem B4378679 : Blo 1945435 4378679 := bstep (se 1 (by rfl) ⟨3284009, by rfl⟩ : syracuseStep 4378679 = 6568019) B6568019
theorem B2919119 : Blo 1945435 2919119 := bstep (se 1 (by rfl) ⟨2189339, by rfl⟩ : syracuseStep 2919119 = 4378679) B4378679
theorem B1946079 : Blo 1945435 1946079 := bstep (se 1 (by rfl) ⟨1459559, by rfl⟩ : syracuseStep 1946079 = 2919119) B2919119
theorem B2919125 : Blo 1945435 2919125 := bbase (se 7 (by rfl) ⟨34208, by rfl⟩ : syracuseStep 2919125 = 68417) (by norm_num)
theorem B1946083 : Blo 1945435 1946083 := bstep (se 1 (by rfl) ⟨1459562, by rfl⟩ : syracuseStep 1946083 = 2919125) B2919125
theorem B5260373 : Blo 1945435 5260373 := bbase (se 8 (by rfl) ⟨30822, by rfl⟩ : syracuseStep 5260373 = 61645) (by norm_num)
theorem B3506915 : Blo 1945435 3506915 := bstep (se 1 (by rfl) ⟨2630186, by rfl⟩ : syracuseStep 3506915 = 5260373) B5260373
theorem B9351773 : Blo 1945435 9351773 := bstep (se 3 (by rfl) ⟨1753457, by rfl⟩ : syracuseStep 9351773 = 3506915) B3506915
theorem B6234515 : Blo 1945435 6234515 := bstep (se 1 (by rfl) ⟨4675886, by rfl⟩ : syracuseStep 6234515 = 9351773) B9351773
theorem B4156343 : Blo 1945435 4156343 := bstep (se 1 (by rfl) ⟨3117257, by rfl⟩ : syracuseStep 4156343 = 6234515) B6234515
theorem B2770895 : Blo 1945435 2770895 := bstep (se 1 (by rfl) ⟨2078171, by rfl⟩ : syracuseStep 2770895 = 4156343) B4156343
theorem B7389053 : Blo 1945435 7389053 := bstep (se 3 (by rfl) ⟨1385447, by rfl⟩ : syracuseStep 7389053 = 2770895) B2770895
theorem B4926035 : Blo 1945435 4926035 := bstep (se 1 (by rfl) ⟨3694526, by rfl⟩ : syracuseStep 4926035 = 7389053) B7389053
theorem B3284023 : Blo 1945435 3284023 := bstep (se 1 (by rfl) ⟨2463017, by rfl⟩ : syracuseStep 3284023 = 4926035) B4926035
theorem B4378697 : Blo 1945435 4378697 := bstep (se 2 (by rfl) ⟨1642011, by rfl⟩ : syracuseStep 4378697 = 3284023) B3284023
theorem B2919131 : Blo 1945435 2919131 := bstep (se 1 (by rfl) ⟨2189348, by rfl⟩ : syracuseStep 2919131 = 4378697) B4378697
theorem B1946087 : Blo 1945435 1946087 := bstep (se 1 (by rfl) ⟨1459565, by rfl⟩ : syracuseStep 1946087 = 2919131) B2919131
theorem B2189353 : Blo 1945435 2189353 := bbase (se 2 (by rfl) ⟨821007, by rfl⟩ : syracuseStep 2189353 = 1642015) (by norm_num)
theorem B2919137 : Blo 1945435 2919137 := bstep (se 2 (by rfl) ⟨1094676, by rfl⟩ : syracuseStep 2919137 = 2189353) B2189353
theorem B1946091 : Blo 1945435 1946091 := bstep (se 1 (by rfl) ⟨1459568, by rfl⟩ : syracuseStep 1946091 = 2919137) B2919137
theorem B3744949 : Blo 1945435 3744949 := bbase (se 5 (by rfl) ⟨175544, by rfl⟩ : syracuseStep 3744949 = 351089) (by norm_num)
theorem B4993265 : Blo 1945435 4993265 := bstep (se 2 (by rfl) ⟨1872474, by rfl⟩ : syracuseStep 4993265 = 3744949) B3744949
theorem B13315373 : Blo 1945435 13315373 := bstep (se 3 (by rfl) ⟨2496632, by rfl⟩ : syracuseStep 13315373 = 4993265) B4993265
theorem B8876915 : Blo 1945435 8876915 := bstep (se 1 (by rfl) ⟨6657686, by rfl⟩ : syracuseStep 8876915 = 13315373) B13315373
theorem B5917943 : Blo 1945435 5917943 := bstep (se 1 (by rfl) ⟨4438457, by rfl⟩ : syracuseStep 5917943 = 8876915) B8876915
theorem B3945295 : Blo 1945435 3945295 := bstep (se 1 (by rfl) ⟨2958971, by rfl⟩ : syracuseStep 3945295 = 5917943) B5917943
theorem B5260393 : Blo 1945435 5260393 := bstep (se 2 (by rfl) ⟨1972647, by rfl⟩ : syracuseStep 5260393 = 3945295) B3945295
theorem B28055429 : Blo 1945435 28055429 := bstep (se 4 (by rfl) ⟨2630196, by rfl⟩ : syracuseStep 28055429 = 5260393) B5260393
theorem B18703619 : Blo 1945435 18703619 := bstep (se 1 (by rfl) ⟨14027714, by rfl⟩ : syracuseStep 18703619 = 28055429) B28055429
theorem B12469079 : Blo 1945435 12469079 := bstep (se 1 (by rfl) ⟨9351809, by rfl⟩ : syracuseStep 12469079 = 18703619) B18703619
theorem B8312719 : Blo 1945435 8312719 := bstep (se 1 (by rfl) ⟨6234539, by rfl⟩ : syracuseStep 8312719 = 12469079) B12469079
theorem B11083625 : Blo 1945435 11083625 := bstep (se 2 (by rfl) ⟨4156359, by rfl⟩ : syracuseStep 11083625 = 8312719) B8312719
theorem B7389083 : Blo 1945435 7389083 := bstep (se 1 (by rfl) ⟨5541812, by rfl⟩ : syracuseStep 7389083 = 11083625) B11083625
theorem B4926055 : Blo 1945435 4926055 := bstep (se 1 (by rfl) ⟨3694541, by rfl⟩ : syracuseStep 4926055 = 7389083) B7389083
theorem B6568073 : Blo 1945435 6568073 := bstep (se 2 (by rfl) ⟨2463027, by rfl⟩ : syracuseStep 6568073 = 4926055) B4926055
theorem B4378715 : Blo 1945435 4378715 := bstep (se 1 (by rfl) ⟨3284036, by rfl⟩ : syracuseStep 4378715 = 6568073) B6568073
theorem B2919143 : Blo 1945435 2919143 := bstep (se 1 (by rfl) ⟨2189357, by rfl⟩ : syracuseStep 2919143 = 4378715) B4378715
theorem B1946095 : Blo 1945435 1946095 := bstep (se 1 (by rfl) ⟨1459571, by rfl⟩ : syracuseStep 1946095 = 2919143) B2919143
theorem B2919149 : Blo 1945435 2919149 := bbase (se 3 (by rfl) ⟨547340, by rfl⟩ : syracuseStep 2919149 = 1094681) (by norm_num)
theorem B1946099 : Blo 1945435 1946099 := bstep (se 1 (by rfl) ⟨1459574, by rfl⟩ : syracuseStep 1946099 = 2919149) B2919149
theorem B4378733 : Blo 1945435 4378733 := bbase (se 3 (by rfl) ⟨821012, by rfl⟩ : syracuseStep 4378733 = 1642025) (by norm_num)
theorem B2919155 : Blo 1945435 2919155 := bstep (se 1 (by rfl) ⟨2189366, by rfl⟩ : syracuseStep 2919155 = 4378733) B4378733
theorem B1946103 : Blo 1945435 1946103 := bstep (se 1 (by rfl) ⟨1459577, by rfl⟩ : syracuseStep 1946103 = 2919155) B2919155
theorem B3694565 : Blo 1945435 3694565 := bbase (se 4 (by rfl) ⟨346365, by rfl⟩ : syracuseStep 3694565 = 692731) (by norm_num)
theorem B2463043 : Blo 1945435 2463043 := bstep (se 1 (by rfl) ⟨1847282, by rfl⟩ : syracuseStep 2463043 = 3694565) B3694565
theorem B3284057 : Blo 1945435 3284057 := bstep (se 2 (by rfl) ⟨1231521, by rfl⟩ : syracuseStep 3284057 = 2463043) B2463043
theorem B2189371 : Blo 1945435 2189371 := bstep (se 1 (by rfl) ⟨1642028, by rfl⟩ : syracuseStep 2189371 = 3284057) B3284057
theorem B2919161 : Blo 1945435 2919161 := bstep (se 2 (by rfl) ⟨1094685, by rfl⟩ : syracuseStep 2919161 = 2189371) B2189371
theorem B1946107 : Blo 1945435 1946107 := bstep (se 1 (by rfl) ⟨1459580, by rfl⟩ : syracuseStep 1946107 = 2919161) B2919161
theorem B3506957 : Blo 1945435 3506957 := bbase (se 3 (by rfl) ⟨657554, by rfl⟩ : syracuseStep 3506957 = 1315109) (by norm_num)
theorem B37407541 : Blo 1945435 37407541 := bstep (se 5 (by rfl) ⟨1753478, by rfl⟩ : syracuseStep 37407541 = 3506957) B3506957
theorem B49876721 : Blo 1945435 49876721 := bstep (se 2 (by rfl) ⟨18703770, by rfl⟩ : syracuseStep 49876721 = 37407541) B37407541
theorem B33251147 : Blo 1945435 33251147 := bstep (se 1 (by rfl) ⟨24938360, by rfl⟩ : syracuseStep 33251147 = 49876721) B49876721
theorem B22167431 : Blo 1945435 22167431 := bstep (se 1 (by rfl) ⟨16625573, by rfl⟩ : syracuseStep 22167431 = 33251147) B33251147
theorem B14778287 : Blo 1945435 14778287 := bstep (se 1 (by rfl) ⟨11083715, by rfl⟩ : syracuseStep 14778287 = 22167431) B22167431
theorem B9852191 : Blo 1945435 9852191 := bstep (se 1 (by rfl) ⟨7389143, by rfl⟩ : syracuseStep 9852191 = 14778287) B14778287
theorem B6568127 : Blo 1945435 6568127 := bstep (se 1 (by rfl) ⟨4926095, by rfl⟩ : syracuseStep 6568127 = 9852191) B9852191
theorem B4378751 : Blo 1945435 4378751 := bstep (se 1 (by rfl) ⟨3284063, by rfl⟩ : syracuseStep 4378751 = 6568127) B6568127
theorem B2919167 : Blo 1945435 2919167 := bstep (se 1 (by rfl) ⟨2189375, by rfl⟩ : syracuseStep 2919167 = 4378751) B4378751
theorem B1946111 : Blo 1945435 1946111 := bstep (se 1 (by rfl) ⟨1459583, by rfl⟩ : syracuseStep 1946111 = 2919167) B2919167
theorem B2919173 : Blo 1945435 2919173 := bbase (se 4 (by rfl) ⟨273672, by rfl⟩ : syracuseStep 2919173 = 547345) (by norm_num)
theorem B1946115 : Blo 1945435 1946115 := bstep (se 1 (by rfl) ⟨1459586, by rfl⟩ : syracuseStep 1946115 = 2919173) B2919173
theorem B3284077 : Blo 1945435 3284077 := bbase (se 3 (by rfl) ⟨615764, by rfl⟩ : syracuseStep 3284077 = 1231529) (by norm_num)
theorem B4378769 : Blo 1945435 4378769 := bstep (se 2 (by rfl) ⟨1642038, by rfl⟩ : syracuseStep 4378769 = 3284077) B3284077
theorem B2919179 : Blo 1945435 2919179 := bstep (se 1 (by rfl) ⟨2189384, by rfl⟩ : syracuseStep 2919179 = 4378769) B4378769
theorem B1946119 : Blo 1945435 1946119 := bstep (se 1 (by rfl) ⟨1459589, by rfl⟩ : syracuseStep 1946119 = 2919179) B2919179
theorem B2189389 : Blo 1945435 2189389 := bbase (se 3 (by rfl) ⟨410510, by rfl⟩ : syracuseStep 2189389 = 821021) (by norm_num)
theorem B2919185 : Blo 1945435 2919185 := bstep (se 2 (by rfl) ⟨1094694, by rfl⟩ : syracuseStep 2919185 = 2189389) B2189389
theorem B1946123 : Blo 1945435 1946123 := bstep (se 1 (by rfl) ⟨1459592, by rfl⟩ : syracuseStep 1946123 = 2919185) B2919185
theorem B6568181 : Blo 1945435 6568181 := bbase (se 5 (by rfl) ⟨307883, by rfl⟩ : syracuseStep 6568181 = 615767) (by norm_num)
theorem B4378787 : Blo 1945435 4378787 := bstep (se 1 (by rfl) ⟨3284090, by rfl⟩ : syracuseStep 4378787 = 6568181) B6568181
theorem B2919191 : Blo 1945435 2919191 := bstep (se 1 (by rfl) ⟨2189393, by rfl⟩ : syracuseStep 2919191 = 4378787) B4378787
theorem B1946127 : Blo 1945435 1946127 := bstep (se 1 (by rfl) ⟨1459595, by rfl⟩ : syracuseStep 1946127 = 2919191) B2919191
theorem B2919197 : Blo 1945435 2919197 := bbase (se 3 (by rfl) ⟨547349, by rfl⟩ : syracuseStep 2919197 = 1094699) (by norm_num)
theorem B1946131 : Blo 1945435 1946131 := bstep (se 1 (by rfl) ⟨1459598, by rfl⟩ : syracuseStep 1946131 = 2919197) B2919197
theorem B4378805 : Blo 1945435 4378805 := bbase (se 5 (by rfl) ⟨205256, by rfl⟩ : syracuseStep 4378805 = 410513) (by norm_num)
theorem B2919203 : Blo 1945435 2919203 := bstep (se 1 (by rfl) ⟨2189402, by rfl⟩ : syracuseStep 2919203 = 4378805) B4378805
theorem B1946135 : Blo 1945435 1946135 := bstep (se 1 (by rfl) ⟨1459601, by rfl⟩ : syracuseStep 1946135 = 2919203) B2919203
theorem B3117341 : Blo 1945435 3117341 := bbase (se 3 (by rfl) ⟨584501, by rfl⟩ : syracuseStep 3117341 = 1169003) (by norm_num)
theorem B2078227 : Blo 1945435 2078227 := bstep (se 1 (by rfl) ⟨1558670, by rfl⟩ : syracuseStep 2078227 = 3117341) B3117341
theorem B11083877 : Blo 1945435 11083877 := bstep (se 4 (by rfl) ⟨1039113, by rfl⟩ : syracuseStep 11083877 = 2078227) B2078227
theorem B7389251 : Blo 1945435 7389251 := bstep (se 1 (by rfl) ⟨5541938, by rfl⟩ : syracuseStep 7389251 = 11083877) B11083877
theorem B4926167 : Blo 1945435 4926167 := bstep (se 1 (by rfl) ⟨3694625, by rfl⟩ : syracuseStep 4926167 = 7389251) B7389251
theorem B3284111 : Blo 1945435 3284111 := bstep (se 1 (by rfl) ⟨2463083, by rfl⟩ : syracuseStep 3284111 = 4926167) B4926167
theorem B2189407 : Blo 1945435 2189407 := bstep (se 1 (by rfl) ⟨1642055, by rfl⟩ : syracuseStep 2189407 = 3284111) B3284111
theorem B2919209 : Blo 1945435 2919209 := bstep (se 2 (by rfl) ⟨1094703, by rfl⟩ : syracuseStep 2919209 = 2189407) B2189407
theorem B1946139 : Blo 1945435 1946139 := bstep (se 1 (by rfl) ⟨1459604, by rfl⟩ : syracuseStep 1946139 = 2919209) B2919209
theorem B4676021 : Blo 1945435 4676021 := bbase (se 5 (by rfl) ⟨219188, by rfl⟩ : syracuseStep 4676021 = 438377) (by norm_num)
theorem B3117347 : Blo 1945435 3117347 := bstep (se 1 (by rfl) ⟨2338010, by rfl⟩ : syracuseStep 3117347 = 4676021) B4676021
theorem B2078231 : Blo 1945435 2078231 := bstep (se 1 (by rfl) ⟨1558673, by rfl⟩ : syracuseStep 2078231 = 3117347) B3117347
theorem B5541949 : Blo 1945435 5541949 := bstep (se 3 (by rfl) ⟨1039115, by rfl⟩ : syracuseStep 5541949 = 2078231) B2078231
theorem B7389265 : Blo 1945435 7389265 := bstep (se 2 (by rfl) ⟨2770974, by rfl⟩ : syracuseStep 7389265 = 5541949) B5541949
theorem B9852353 : Blo 1945435 9852353 := bstep (se 2 (by rfl) ⟨3694632, by rfl⟩ : syracuseStep 9852353 = 7389265) B7389265
theorem B6568235 : Blo 1945435 6568235 := bstep (se 1 (by rfl) ⟨4926176, by rfl⟩ : syracuseStep 6568235 = 9852353) B9852353
theorem B4378823 : Blo 1945435 4378823 := bstep (se 1 (by rfl) ⟨3284117, by rfl⟩ : syracuseStep 4378823 = 6568235) B6568235
theorem B2919215 : Blo 1945435 2919215 := bstep (se 1 (by rfl) ⟨2189411, by rfl⟩ : syracuseStep 2919215 = 4378823) B4378823
theorem B1946143 : Blo 1945435 1946143 := bstep (se 1 (by rfl) ⟨1459607, by rfl⟩ : syracuseStep 1946143 = 2919215) B2919215
theorem B2919221 : Blo 1945435 2919221 := bbase (se 5 (by rfl) ⟨136838, by rfl⟩ : syracuseStep 2919221 = 273677) (by norm_num)
theorem B1946147 : Blo 1945435 1946147 := bstep (se 1 (by rfl) ⟨1459610, by rfl⟩ : syracuseStep 1946147 = 2919221) B2919221
theorem B4926197 : Blo 1945435 4926197 := bbase (se 5 (by rfl) ⟨230915, by rfl⟩ : syracuseStep 4926197 = 461831) (by norm_num)
theorem B3284131 : Blo 1945435 3284131 := bstep (se 1 (by rfl) ⟨2463098, by rfl⟩ : syracuseStep 3284131 = 4926197) B4926197
theorem B4378841 : Blo 1945435 4378841 := bstep (se 2 (by rfl) ⟨1642065, by rfl⟩ : syracuseStep 4378841 = 3284131) B3284131
theorem B2919227 : Blo 1945435 2919227 := bstep (se 1 (by rfl) ⟨2189420, by rfl⟩ : syracuseStep 2919227 = 4378841) B4378841
theorem B1946151 : Blo 1945435 1946151 := bstep (se 1 (by rfl) ⟨1459613, by rfl⟩ : syracuseStep 1946151 = 2919227) B2919227
theorem B2189425 : Blo 1945435 2189425 := bbase (se 2 (by rfl) ⟨821034, by rfl⟩ : syracuseStep 2189425 = 1642069) (by norm_num)
theorem B2919233 : Blo 1945435 2919233 := bstep (se 2 (by rfl) ⟨1094712, by rfl⟩ : syracuseStep 2919233 = 2189425) B2189425
theorem B1946155 : Blo 1945435 1946155 := bstep (se 1 (by rfl) ⟨1459616, by rfl⟩ : syracuseStep 1946155 = 2919233) B2919233
theorem B11836277 : Blo 1945435 11836277 := bbase (se 5 (by rfl) ⟨554825, by rfl⟩ : syracuseStep 11836277 = 1109651) (by norm_num)
theorem B7890851 : Blo 1945435 7890851 := bstep (se 1 (by rfl) ⟨5918138, by rfl⟩ : syracuseStep 7890851 = 11836277) B11836277
theorem B5260567 : Blo 1945435 5260567 := bstep (se 1 (by rfl) ⟨3945425, by rfl⟩ : syracuseStep 5260567 = 7890851) B7890851
theorem B7014089 : Blo 1945435 7014089 := bstep (se 2 (by rfl) ⟨2630283, by rfl⟩ : syracuseStep 7014089 = 5260567) B5260567
theorem B4676059 : Blo 1945435 4676059 := bstep (se 1 (by rfl) ⟨3507044, by rfl⟩ : syracuseStep 4676059 = 7014089) B7014089
theorem B6234745 : Blo 1945435 6234745 := bstep (se 2 (by rfl) ⟨2338029, by rfl⟩ : syracuseStep 6234745 = 4676059) B4676059
theorem B8312993 : Blo 1945435 8312993 := bstep (se 2 (by rfl) ⟨3117372, by rfl⟩ : syracuseStep 8312993 = 6234745) B6234745
theorem B5541995 : Blo 1945435 5541995 := bstep (se 1 (by rfl) ⟨4156496, by rfl⟩ : syracuseStep 5541995 = 8312993) B8312993
theorem B3694663 : Blo 1945435 3694663 := bstep (se 1 (by rfl) ⟨2770997, by rfl⟩ : syracuseStep 3694663 = 5541995) B5541995
theorem B4926217 : Blo 1945435 4926217 := bstep (se 2 (by rfl) ⟨1847331, by rfl⟩ : syracuseStep 4926217 = 3694663) B3694663
theorem B6568289 : Blo 1945435 6568289 := bstep (se 2 (by rfl) ⟨2463108, by rfl⟩ : syracuseStep 6568289 = 4926217) B4926217
theorem B4378859 : Blo 1945435 4378859 := bstep (se 1 (by rfl) ⟨3284144, by rfl⟩ : syracuseStep 4378859 = 6568289) B6568289
theorem B2919239 : Blo 1945435 2919239 := bstep (se 1 (by rfl) ⟨2189429, by rfl⟩ : syracuseStep 2919239 = 4378859) B4378859
theorem B1946159 : Blo 1945435 1946159 := bstep (se 1 (by rfl) ⟨1459619, by rfl⟩ : syracuseStep 1946159 = 2919239) B2919239
theorem B2919245 : Blo 1945435 2919245 := bbase (se 3 (by rfl) ⟨547358, by rfl⟩ : syracuseStep 2919245 = 1094717) (by norm_num)
theorem B1946163 : Blo 1945435 1946163 := bstep (se 1 (by rfl) ⟨1459622, by rfl⟩ : syracuseStep 1946163 = 2919245) B2919245
theorem B4378877 : Blo 1945435 4378877 := bbase (se 3 (by rfl) ⟨821039, by rfl⟩ : syracuseStep 4378877 = 1642079) (by norm_num)
theorem B2919251 : Blo 1945435 2919251 := bstep (se 1 (by rfl) ⟨2189438, by rfl⟩ : syracuseStep 2919251 = 4378877) B4378877
theorem B1946167 : Blo 1945435 1946167 := bstep (se 1 (by rfl) ⟨1459625, by rfl⟩ : syracuseStep 1946167 = 2919251) B2919251
theorem B3284165 : Blo 1945435 3284165 := bbase (se 4 (by rfl) ⟨307890, by rfl⟩ : syracuseStep 3284165 = 615781) (by norm_num)
theorem B2189443 : Blo 1945435 2189443 := bstep (se 1 (by rfl) ⟨1642082, by rfl⟩ : syracuseStep 2189443 = 3284165) B3284165
theorem B2919257 : Blo 1945435 2919257 := bstep (se 2 (by rfl) ⟨1094721, by rfl⟩ : syracuseStep 2919257 = 2189443) B2189443
theorem B1946171 : Blo 1945435 1946171 := bstep (se 1 (by rfl) ⟨1459628, by rfl⟩ : syracuseStep 1946171 = 2919257) B2919257
theorem B14778773 : Blo 1945435 14778773 := bbase (se 6 (by rfl) ⟨346377, by rfl⟩ : syracuseStep 14778773 = 692755) (by norm_num)
theorem B9852515 : Blo 1945435 9852515 := bstep (se 1 (by rfl) ⟨7389386, by rfl⟩ : syracuseStep 9852515 = 14778773) B14778773
theorem B6568343 : Blo 1945435 6568343 := bstep (se 1 (by rfl) ⟨4926257, by rfl⟩ : syracuseStep 6568343 = 9852515) B9852515
theorem B4378895 : Blo 1945435 4378895 := bstep (se 1 (by rfl) ⟨3284171, by rfl⟩ : syracuseStep 4378895 = 6568343) B6568343
theorem B2919263 : Blo 1945435 2919263 := bstep (se 1 (by rfl) ⟨2189447, by rfl⟩ : syracuseStep 2919263 = 4378895) B4378895
theorem B1946175 : Blo 1945435 1946175 := bstep (se 1 (by rfl) ⟨1459631, by rfl⟩ : syracuseStep 1946175 = 2919263) B2919263
theorem B2919269 : Blo 1945435 2919269 := bbase (se 4 (by rfl) ⟨273681, by rfl⟩ : syracuseStep 2919269 = 547363) (by norm_num)
theorem B1946179 : Blo 1945435 1946179 := bstep (se 1 (by rfl) ⟨1459634, by rfl⟩ : syracuseStep 1946179 = 2919269) B2919269
theorem B3694709 : Blo 1945435 3694709 := bbase (se 5 (by rfl) ⟨173189, by rfl⟩ : syracuseStep 3694709 = 346379) (by norm_num)
theorem B2463139 : Blo 1945435 2463139 := bstep (se 1 (by rfl) ⟨1847354, by rfl⟩ : syracuseStep 2463139 = 3694709) B3694709
theorem B3284185 : Blo 1945435 3284185 := bstep (se 2 (by rfl) ⟨1231569, by rfl⟩ : syracuseStep 3284185 = 2463139) B2463139
theorem B4378913 : Blo 1945435 4378913 := bstep (se 2 (by rfl) ⟨1642092, by rfl⟩ : syracuseStep 4378913 = 3284185) B3284185
theorem B2919275 : Blo 1945435 2919275 := bstep (se 1 (by rfl) ⟨2189456, by rfl⟩ : syracuseStep 2919275 = 4378913) B4378913
theorem B1946183 : Blo 1945435 1946183 := bstep (se 1 (by rfl) ⟨1459637, by rfl⟩ : syracuseStep 1946183 = 2919275) B2919275
theorem B2189461 : Blo 1945435 2189461 := bbase (se 6 (by rfl) ⟨51315, by rfl⟩ : syracuseStep 2189461 = 102631) (by norm_num)
theorem B2919281 : Blo 1945435 2919281 := bstep (se 2 (by rfl) ⟨1094730, by rfl⟩ : syracuseStep 2919281 = 2189461) B2189461
theorem B1946187 : Blo 1945435 1946187 := bstep (se 1 (by rfl) ⟨1459640, by rfl⟩ : syracuseStep 1946187 = 2919281) B2919281
theorem B2463149 : Blo 1945435 2463149 := bbase (se 3 (by rfl) ⟨461840, by rfl⟩ : syracuseStep 2463149 = 923681) (by norm_num)
theorem B6568397 : Blo 1945435 6568397 := bstep (se 3 (by rfl) ⟨1231574, by rfl⟩ : syracuseStep 6568397 = 2463149) B2463149
theorem B4378931 : Blo 1945435 4378931 := bstep (se 1 (by rfl) ⟨3284198, by rfl⟩ : syracuseStep 4378931 = 6568397) B6568397
theorem B2919287 : Blo 1945435 2919287 := bstep (se 1 (by rfl) ⟨2189465, by rfl⟩ : syracuseStep 2919287 = 4378931) B4378931
theorem B1946191 : Blo 1945435 1946191 := bstep (se 1 (by rfl) ⟨1459643, by rfl⟩ : syracuseStep 1946191 = 2919287) B2919287
theorem B2919293 : Blo 1945435 2919293 := bbase (se 3 (by rfl) ⟨547367, by rfl⟩ : syracuseStep 2919293 = 1094735) (by norm_num)
theorem B1946195 : Blo 1945435 1946195 := bstep (se 1 (by rfl) ⟨1459646, by rfl⟩ : syracuseStep 1946195 = 2919293) B2919293
theorem B4378949 : Blo 1945435 4378949 := bbase (se 4 (by rfl) ⟨410526, by rfl⟩ : syracuseStep 4378949 = 821053) (by norm_num)
theorem B2919299 : Blo 1945435 2919299 := bstep (se 1 (by rfl) ⟨2189474, by rfl⟩ : syracuseStep 2919299 = 4378949) B4378949
theorem B1946199 : Blo 1945435 1946199 := bstep (se 1 (by rfl) ⟨1459649, by rfl⟩ : syracuseStep 1946199 = 2919299) B2919299
theorem B3329029 : Blo 1945435 3329029 := bbase (se 4 (by rfl) ⟨312096, by rfl⟩ : syracuseStep 3329029 = 624193) (by norm_num)
theorem B4438705 : Blo 1945435 4438705 := bstep (se 2 (by rfl) ⟨1664514, by rfl⟩ : syracuseStep 4438705 = 3329029) B3329029
theorem B5918273 : Blo 1945435 5918273 := bstep (se 2 (by rfl) ⟨2219352, by rfl⟩ : syracuseStep 5918273 = 4438705) B4438705
theorem B3945515 : Blo 1945435 3945515 := bstep (se 1 (by rfl) ⟨2959136, by rfl⟩ : syracuseStep 3945515 = 5918273) B5918273
theorem B10521373 : Blo 1945435 10521373 := bstep (se 3 (by rfl) ⟨1972757, by rfl⟩ : syracuseStep 10521373 = 3945515) B3945515
theorem B14028497 : Blo 1945435 14028497 := bstep (se 2 (by rfl) ⟨5260686, by rfl⟩ : syracuseStep 14028497 = 10521373) B10521373
theorem B9352331 : Blo 1945435 9352331 := bstep (se 1 (by rfl) ⟨7014248, by rfl⟩ : syracuseStep 9352331 = 14028497) B14028497
theorem B6234887 : Blo 1945435 6234887 := bstep (se 1 (by rfl) ⟨4676165, by rfl⟩ : syracuseStep 6234887 = 9352331) B9352331
theorem B4156591 : Blo 1945435 4156591 := bstep (se 1 (by rfl) ⟨3117443, by rfl⟩ : syracuseStep 4156591 = 6234887) B6234887
theorem B5542121 : Blo 1945435 5542121 := bstep (se 2 (by rfl) ⟨2078295, by rfl⟩ : syracuseStep 5542121 = 4156591) B4156591
theorem B3694747 : Blo 1945435 3694747 := bstep (se 1 (by rfl) ⟨2771060, by rfl⟩ : syracuseStep 3694747 = 5542121) B5542121
theorem B4926329 : Blo 1945435 4926329 := bstep (se 2 (by rfl) ⟨1847373, by rfl⟩ : syracuseStep 4926329 = 3694747) B3694747
theorem B3284219 : Blo 1945435 3284219 := bstep (se 1 (by rfl) ⟨2463164, by rfl⟩ : syracuseStep 3284219 = 4926329) B4926329
theorem B2189479 : Blo 1945435 2189479 := bstep (se 1 (by rfl) ⟨1642109, by rfl⟩ : syracuseStep 2189479 = 3284219) B3284219
theorem B2919305 : Blo 1945435 2919305 := bstep (se 2 (by rfl) ⟨1094739, by rfl⟩ : syracuseStep 2919305 = 2189479) B2189479
theorem B1946203 : Blo 1945435 1946203 := bstep (se 1 (by rfl) ⟨1459652, by rfl⟩ : syracuseStep 1946203 = 2919305) B2919305
theorem B9852677 : Blo 1945435 9852677 := bbase (se 4 (by rfl) ⟨923688, by rfl⟩ : syracuseStep 9852677 = 1847377) (by norm_num)
theorem B6568451 : Blo 1945435 6568451 := bstep (se 1 (by rfl) ⟨4926338, by rfl⟩ : syracuseStep 6568451 = 9852677) B9852677
theorem B4378967 : Blo 1945435 4378967 := bstep (se 1 (by rfl) ⟨3284225, by rfl⟩ : syracuseStep 4378967 = 6568451) B6568451
theorem B2919311 : Blo 1945435 2919311 := bstep (se 1 (by rfl) ⟨2189483, by rfl⟩ : syracuseStep 2919311 = 4378967) B4378967
theorem B1946207 : Blo 1945435 1946207 := bstep (se 1 (by rfl) ⟨1459655, by rfl⟩ : syracuseStep 1946207 = 2919311) B2919311
theorem B2919317 : Blo 1945435 2919317 := bbase (se 6 (by rfl) ⟨68421, by rfl⟩ : syracuseStep 2919317 = 136843) (by norm_num)
theorem B1946211 : Blo 1945435 1946211 := bstep (se 1 (by rfl) ⟨1459658, by rfl⟩ : syracuseStep 1946211 = 2919317) B2919317
theorem B11084309 : Blo 1945435 11084309 := bbase (se 6 (by rfl) ⟨259788, by rfl⟩ : syracuseStep 11084309 = 519577) (by norm_num)
theorem B7389539 : Blo 1945435 7389539 := bstep (se 1 (by rfl) ⟨5542154, by rfl⟩ : syracuseStep 7389539 = 11084309) B11084309
theorem B4926359 : Blo 1945435 4926359 := bstep (se 1 (by rfl) ⟨3694769, by rfl⟩ : syracuseStep 4926359 = 7389539) B7389539
theorem B3284239 : Blo 1945435 3284239 := bstep (se 1 (by rfl) ⟨2463179, by rfl⟩ : syracuseStep 3284239 = 4926359) B4926359
theorem B4378985 : Blo 1945435 4378985 := bstep (se 2 (by rfl) ⟨1642119, by rfl⟩ : syracuseStep 4378985 = 3284239) B3284239
theorem B2919323 : Blo 1945435 2919323 := bstep (se 1 (by rfl) ⟨2189492, by rfl⟩ : syracuseStep 2919323 = 4378985) B4378985
theorem B1946215 : Blo 1945435 1946215 := bstep (se 1 (by rfl) ⟨1459661, by rfl⟩ : syracuseStep 1946215 = 2919323) B2919323
theorem B2189497 : Blo 1945435 2189497 := bbase (se 2 (by rfl) ⟨821061, by rfl⟩ : syracuseStep 2189497 = 1642123) (by norm_num)
theorem B2919329 : Blo 1945435 2919329 := bstep (se 2 (by rfl) ⟨1094748, by rfl⟩ : syracuseStep 2919329 = 2189497) B2189497
theorem B1946219 : Blo 1945435 1946219 := bstep (se 1 (by rfl) ⟨1459664, by rfl⟩ : syracuseStep 1946219 = 2919329) B2919329
theorem B4676213 : Blo 1945435 4676213 := bbase (se 5 (by rfl) ⟨219197, by rfl⟩ : syracuseStep 4676213 = 438395) (by norm_num)
theorem B3117475 : Blo 1945435 3117475 := bstep (se 1 (by rfl) ⟨2338106, by rfl⟩ : syracuseStep 3117475 = 4676213) B4676213
theorem B4156633 : Blo 1945435 4156633 := bstep (se 2 (by rfl) ⟨1558737, by rfl⟩ : syracuseStep 4156633 = 3117475) B3117475
theorem B5542177 : Blo 1945435 5542177 := bstep (se 2 (by rfl) ⟨2078316, by rfl⟩ : syracuseStep 5542177 = 4156633) B4156633
theorem B7389569 : Blo 1945435 7389569 := bstep (se 2 (by rfl) ⟨2771088, by rfl⟩ : syracuseStep 7389569 = 5542177) B5542177
theorem B4926379 : Blo 1945435 4926379 := bstep (se 1 (by rfl) ⟨3694784, by rfl⟩ : syracuseStep 4926379 = 7389569) B7389569
theorem B6568505 : Blo 1945435 6568505 := bstep (se 2 (by rfl) ⟨2463189, by rfl⟩ : syracuseStep 6568505 = 4926379) B4926379
theorem B4379003 : Blo 1945435 4379003 := bstep (se 1 (by rfl) ⟨3284252, by rfl⟩ : syracuseStep 4379003 = 6568505) B6568505
theorem B2919335 : Blo 1945435 2919335 := bstep (se 1 (by rfl) ⟨2189501, by rfl⟩ : syracuseStep 2919335 = 4379003) B4379003
theorem B1946223 : Blo 1945435 1946223 := bstep (se 1 (by rfl) ⟨1459667, by rfl⟩ : syracuseStep 1946223 = 2919335) B2919335
theorem B2919341 : Blo 1945435 2919341 := bbase (se 3 (by rfl) ⟨547376, by rfl⟩ : syracuseStep 2919341 = 1094753) (by norm_num)
theorem B1946227 : Blo 1945435 1946227 := bstep (se 1 (by rfl) ⟨1459670, by rfl⟩ : syracuseStep 1946227 = 2919341) B2919341
theorem B4379021 : Blo 1945435 4379021 := bbase (se 3 (by rfl) ⟨821066, by rfl⟩ : syracuseStep 4379021 = 1642133) (by norm_num)
theorem B2919347 : Blo 1945435 2919347 := bstep (se 1 (by rfl) ⟨2189510, by rfl⟩ : syracuseStep 2919347 = 4379021) B4379021
theorem B1946231 : Blo 1945435 1946231 := bstep (se 1 (by rfl) ⟨1459673, by rfl⟩ : syracuseStep 1946231 = 2919347) B2919347
theorem B2463205 : Blo 1945435 2463205 := bbase (se 4 (by rfl) ⟨230925, by rfl⟩ : syracuseStep 2463205 = 461851) (by norm_num)
theorem B3284273 : Blo 1945435 3284273 := bstep (se 2 (by rfl) ⟨1231602, by rfl⟩ : syracuseStep 3284273 = 2463205) B2463205
theorem B2189515 : Blo 1945435 2189515 := bstep (se 1 (by rfl) ⟨1642136, by rfl⟩ : syracuseStep 2189515 = 3284273) B3284273
theorem B2919353 : Blo 1945435 2919353 := bstep (se 2 (by rfl) ⟨1094757, by rfl⟩ : syracuseStep 2919353 = 2189515) B2189515
theorem B1946235 : Blo 1945435 1946235 := bstep (se 1 (by rfl) ⟨1459676, by rfl⟩ : syracuseStep 1946235 = 2919353) B2919353
theorem B6320069 : Blo 1945435 6320069 := bbase (se 4 (by rfl) ⟨592506, by rfl⟩ : syracuseStep 6320069 = 1185013) (by norm_num)
theorem B4213379 : Blo 1945435 4213379 := bstep (se 1 (by rfl) ⟨3160034, by rfl⟩ : syracuseStep 4213379 = 6320069) B6320069
theorem B2808919 : Blo 1945435 2808919 := bstep (se 1 (by rfl) ⟨2106689, by rfl⟩ : syracuseStep 2808919 = 4213379) B4213379
theorem B3745225 : Blo 1945435 3745225 := bstep (se 2 (by rfl) ⟨1404459, by rfl⟩ : syracuseStep 3745225 = 2808919) B2808919
theorem B4993633 : Blo 1945435 4993633 := bstep (se 2 (by rfl) ⟨1872612, by rfl⟩ : syracuseStep 4993633 = 3745225) B3745225
theorem B26632709 : Blo 1945435 26632709 := bstep (se 4 (by rfl) ⟨2496816, by rfl⟩ : syracuseStep 26632709 = 4993633) B4993633
theorem B17755139 : Blo 1945435 17755139 := bstep (se 1 (by rfl) ⟨13316354, by rfl⟩ : syracuseStep 17755139 = 26632709) B26632709
theorem B47347037 : Blo 1945435 47347037 := bstep (se 3 (by rfl) ⟨8877569, by rfl⟩ : syracuseStep 47347037 = 17755139) B17755139
theorem B31564691 : Blo 1945435 31564691 := bstep (se 1 (by rfl) ⟨23673518, by rfl⟩ : syracuseStep 31564691 = 47347037) B47347037
theorem B21043127 : Blo 1945435 21043127 := bstep (se 1 (by rfl) ⟨15782345, by rfl⟩ : syracuseStep 21043127 = 31564691) B31564691
theorem B14028751 : Blo 1945435 14028751 := bstep (se 1 (by rfl) ⟨10521563, by rfl⟩ : syracuseStep 14028751 = 21043127) B21043127
theorem B18705001 : Blo 1945435 18705001 := bstep (se 2 (by rfl) ⟨7014375, by rfl⟩ : syracuseStep 18705001 = 14028751) B14028751
theorem B24940001 : Blo 1945435 24940001 := bstep (se 2 (by rfl) ⟨9352500, by rfl⟩ : syracuseStep 24940001 = 18705001) B18705001
theorem B16626667 : Blo 1945435 16626667 := bstep (se 1 (by rfl) ⟨12470000, by rfl⟩ : syracuseStep 16626667 = 24940001) B24940001
theorem B22168889 : Blo 1945435 22168889 := bstep (se 2 (by rfl) ⟨8313333, by rfl⟩ : syracuseStep 22168889 = 16626667) B16626667
theorem B14779259 : Blo 1945435 14779259 := bstep (se 1 (by rfl) ⟨11084444, by rfl⟩ : syracuseStep 14779259 = 22168889) B22168889
theorem B9852839 : Blo 1945435 9852839 := bstep (se 1 (by rfl) ⟨7389629, by rfl⟩ : syracuseStep 9852839 = 14779259) B14779259
theorem B6568559 : Blo 1945435 6568559 := bstep (se 1 (by rfl) ⟨4926419, by rfl⟩ : syracuseStep 6568559 = 9852839) B9852839
theorem B4379039 : Blo 1945435 4379039 := bstep (se 1 (by rfl) ⟨3284279, by rfl⟩ : syracuseStep 4379039 = 6568559) B6568559
theorem B2919359 : Blo 1945435 2919359 := bstep (se 1 (by rfl) ⟨2189519, by rfl⟩ : syracuseStep 2919359 = 4379039) B4379039
theorem B1946239 : Blo 1945435 1946239 := bstep (se 1 (by rfl) ⟨1459679, by rfl⟩ : syracuseStep 1946239 = 2919359) B2919359
theorem B2919365 : Blo 1945435 2919365 := bbase (se 4 (by rfl) ⟨273690, by rfl⟩ : syracuseStep 2919365 = 547381) (by norm_num)
theorem B1946243 : Blo 1945435 1946243 := bstep (se 1 (by rfl) ⟨1459682, by rfl⟩ : syracuseStep 1946243 = 2919365) B2919365
theorem B3284293 : Blo 1945435 3284293 := bbase (se 4 (by rfl) ⟨307902, by rfl⟩ : syracuseStep 3284293 = 615805) (by norm_num)
theorem B4379057 : Blo 1945435 4379057 := bstep (se 2 (by rfl) ⟨1642146, by rfl⟩ : syracuseStep 4379057 = 3284293) B3284293
theorem B2919371 : Blo 1945435 2919371 := bstep (se 1 (by rfl) ⟨2189528, by rfl⟩ : syracuseStep 2919371 = 4379057) B4379057
theorem B1946247 : Blo 1945435 1946247 := bstep (se 1 (by rfl) ⟨1459685, by rfl⟩ : syracuseStep 1946247 = 2919371) B2919371
theorem B2189533 : Blo 1945435 2189533 := bbase (se 3 (by rfl) ⟨410537, by rfl⟩ : syracuseStep 2189533 = 821075) (by norm_num)
theorem B2919377 : Blo 1945435 2919377 := bstep (se 2 (by rfl) ⟨1094766, by rfl⟩ : syracuseStep 2919377 = 2189533) B2189533
theorem B1946251 : Blo 1945435 1946251 := bstep (se 1 (by rfl) ⟨1459688, by rfl⟩ : syracuseStep 1946251 = 2919377) B2919377
theorem B6568613 : Blo 1945435 6568613 := bbase (se 4 (by rfl) ⟨615807, by rfl⟩ : syracuseStep 6568613 = 1231615) (by norm_num)
theorem B4379075 : Blo 1945435 4379075 := bstep (se 1 (by rfl) ⟨3284306, by rfl⟩ : syracuseStep 4379075 = 6568613) B6568613
theorem B2919383 : Blo 1945435 2919383 := bstep (se 1 (by rfl) ⟨2189537, by rfl⟩ : syracuseStep 2919383 = 4379075) B4379075
theorem B1946255 : Blo 1945435 1946255 := bstep (se 1 (by rfl) ⟨1459691, by rfl⟩ : syracuseStep 1946255 = 2919383) B2919383
theorem B2919389 : Blo 1945435 2919389 := bbase (se 3 (by rfl) ⟨547385, by rfl⟩ : syracuseStep 2919389 = 1094771) (by norm_num)
theorem B1946259 : Blo 1945435 1946259 := bstep (se 1 (by rfl) ⟨1459694, by rfl⟩ : syracuseStep 1946259 = 2919389) B2919389
theorem B4379093 : Blo 1945435 4379093 := bbase (se 7 (by rfl) ⟨51317, by rfl⟩ : syracuseStep 4379093 = 102635) (by norm_num)
theorem B2919395 : Blo 1945435 2919395 := bstep (se 1 (by rfl) ⟨2189546, by rfl⟩ : syracuseStep 2919395 = 4379093) B4379093
theorem B1946263 : Blo 1945435 1946263 := bstep (se 1 (by rfl) ⟨1459697, by rfl⟩ : syracuseStep 1946263 = 2919395) B2919395
theorem B15392693 : Blo 1945435 15392693 := bbase (se 5 (by rfl) ⟨721532, by rfl⟩ : syracuseStep 15392693 = 1443065) (by norm_num)
theorem B41047181 : Blo 1945435 41047181 := bstep (se 3 (by rfl) ⟨7696346, by rfl⟩ : syracuseStep 41047181 = 15392693) B15392693
theorem B27364787 : Blo 1945435 27364787 := bstep (se 1 (by rfl) ⟨20523590, by rfl⟩ : syracuseStep 27364787 = 41047181) B41047181
theorem B18243191 : Blo 1945435 18243191 := bstep (se 1 (by rfl) ⟨13682393, by rfl⟩ : syracuseStep 18243191 = 27364787) B27364787
theorem B48648509 : Blo 1945435 48648509 := bstep (se 3 (by rfl) ⟨9121595, by rfl⟩ : syracuseStep 48648509 = 18243191) B18243191
theorem B32432339 : Blo 1945435 32432339 := bstep (se 1 (by rfl) ⟨24324254, by rfl⟩ : syracuseStep 32432339 = 48648509) B48648509
theorem B86486237 : Blo 1945435 86486237 := bstep (se 3 (by rfl) ⟨16216169, by rfl⟩ : syracuseStep 86486237 = 32432339) B32432339
theorem B57657491 : Blo 1945435 57657491 := bstep (se 1 (by rfl) ⟨43243118, by rfl⟩ : syracuseStep 57657491 = 86486237) B86486237
theorem B38438327 : Blo 1945435 38438327 := bstep (se 1 (by rfl) ⟨28828745, by rfl⟩ : syracuseStep 38438327 = 57657491) B57657491
theorem B102502205 : Blo 1945435 102502205 := bstep (se 3 (by rfl) ⟨19219163, by rfl⟩ : syracuseStep 102502205 = 38438327) B38438327
theorem B68334803 : Blo 1945435 68334803 := bstep (se 1 (by rfl) ⟨51251102, by rfl⟩ : syracuseStep 68334803 = 102502205) B102502205
theorem B45556535 : Blo 1945435 45556535 := bstep (se 1 (by rfl) ⟨34167401, by rfl⟩ : syracuseStep 45556535 = 68334803) B68334803
theorem B30371023 : Blo 1945435 30371023 := bstep (se 1 (by rfl) ⟨22778267, by rfl⟩ : syracuseStep 30371023 = 45556535) B45556535
theorem B40494697 : Blo 1945435 40494697 := bstep (se 2 (by rfl) ⟨15185511, by rfl⟩ : syracuseStep 40494697 = 30371023) B30371023
theorem B215971717 : Blo 1945435 215971717 := bstep (se 4 (by rfl) ⟨20247348, by rfl⟩ : syracuseStep 215971717 = 40494697) B40494697
theorem B287962289 : Blo 1945435 287962289 := bstep (se 2 (by rfl) ⟨107985858, by rfl⟩ : syracuseStep 287962289 = 215971717) B215971717
theorem B191974859 : Blo 1945435 191974859 := bstep (se 1 (by rfl) ⟨143981144, by rfl⟩ : syracuseStep 191974859 = 287962289) B287962289
theorem B127983239 : Blo 1945435 127983239 := bstep (se 1 (by rfl) ⟨95987429, by rfl⟩ : syracuseStep 127983239 = 191974859) B191974859
theorem B85322159 : Blo 1945435 85322159 := bstep (se 1 (by rfl) ⟨63991619, by rfl⟩ : syracuseStep 85322159 = 127983239) B127983239
theorem B56881439 : Blo 1945435 56881439 := bstep (se 1 (by rfl) ⟨42661079, by rfl⟩ : syracuseStep 56881439 = 85322159) B85322159
theorem B37920959 : Blo 1945435 37920959 := bstep (se 1 (by rfl) ⟨28440719, by rfl⟩ : syracuseStep 37920959 = 56881439) B56881439
theorem B25280639 : Blo 1945435 25280639 := bstep (se 1 (by rfl) ⟨18960479, by rfl⟩ : syracuseStep 25280639 = 37920959) B37920959
theorem B16853759 : Blo 1945435 16853759 := bstep (se 1 (by rfl) ⟨12640319, by rfl⟩ : syracuseStep 16853759 = 25280639) B25280639
theorem B11235839 : Blo 1945435 11235839 := bstep (se 1 (by rfl) ⟨8426879, by rfl⟩ : syracuseStep 11235839 = 16853759) B16853759
theorem B29962237 : Blo 1945435 29962237 := bstep (se 3 (by rfl) ⟨5617919, by rfl⟩ : syracuseStep 29962237 = 11235839) B11235839
theorem B39949649 : Blo 1945435 39949649 := bstep (se 2 (by rfl) ⟨14981118, by rfl⟩ : syracuseStep 39949649 = 29962237) B29962237
theorem B26633099 : Blo 1945435 26633099 := bstep (se 1 (by rfl) ⟨19974824, by rfl⟩ : syracuseStep 26633099 = 39949649) B39949649
theorem B17755399 : Blo 1945435 17755399 := bstep (se 1 (by rfl) ⟨13316549, by rfl⟩ : syracuseStep 17755399 = 26633099) B26633099
theorem B23673865 : Blo 1945435 23673865 := bstep (se 2 (by rfl) ⟨8877699, by rfl⟩ : syracuseStep 23673865 = 17755399) B17755399
theorem B31565153 : Blo 1945435 31565153 := bstep (se 2 (by rfl) ⟨11836932, by rfl⟩ : syracuseStep 31565153 = 23673865) B23673865
theorem B21043435 : Blo 1945435 21043435 := bstep (se 1 (by rfl) ⟨15782576, by rfl⟩ : syracuseStep 21043435 = 31565153) B31565153
theorem B28057913 : Blo 1945435 28057913 := bstep (se 2 (by rfl) ⟨10521717, by rfl⟩ : syracuseStep 28057913 = 21043435) B21043435
theorem B18705275 : Blo 1945435 18705275 := bstep (se 1 (by rfl) ⟨14028956, by rfl⟩ : syracuseStep 18705275 = 28057913) B28057913
theorem B12470183 : Blo 1945435 12470183 := bstep (se 1 (by rfl) ⟨9352637, by rfl⟩ : syracuseStep 12470183 = 18705275) B18705275
theorem B8313455 : Blo 1945435 8313455 := bstep (se 1 (by rfl) ⟨6235091, by rfl⟩ : syracuseStep 8313455 = 12470183) B12470183
theorem B5542303 : Blo 1945435 5542303 := bstep (se 1 (by rfl) ⟨4156727, by rfl⟩ : syracuseStep 5542303 = 8313455) B8313455
theorem B7389737 : Blo 1945435 7389737 := bstep (se 2 (by rfl) ⟨2771151, by rfl⟩ : syracuseStep 7389737 = 5542303) B5542303
theorem B4926491 : Blo 1945435 4926491 := bstep (se 1 (by rfl) ⟨3694868, by rfl⟩ : syracuseStep 4926491 = 7389737) B7389737
theorem B3284327 : Blo 1945435 3284327 := bstep (se 1 (by rfl) ⟨2463245, by rfl⟩ : syracuseStep 3284327 = 4926491) B4926491
theorem B2189551 : Blo 1945435 2189551 := bstep (se 1 (by rfl) ⟨1642163, by rfl⟩ : syracuseStep 2189551 = 3284327) B3284327
theorem B2919401 : Blo 1945435 2919401 := bstep (se 2 (by rfl) ⟨1094775, by rfl⟩ : syracuseStep 2919401 = 2189551) B2189551
theorem B1946267 : Blo 1945435 1946267 := bstep (se 1 (by rfl) ⟨1459700, by rfl⟩ : syracuseStep 1946267 = 2919401) B2919401
theorem B3082021 : Blo 1945435 3082021 := bbase (se 4 (by rfl) ⟨288939, by rfl⟩ : syracuseStep 3082021 = 577879) (by norm_num)
theorem B65749781 : Blo 1945435 65749781 := bstep (se 6 (by rfl) ⟨1541010, by rfl⟩ : syracuseStep 65749781 = 3082021) B3082021
theorem B43833187 : Blo 1945435 43833187 := bstep (se 1 (by rfl) ⟨32874890, by rfl⟩ : syracuseStep 43833187 = 65749781) B65749781
theorem B58444249 : Blo 1945435 58444249 := bstep (se 2 (by rfl) ⟨21916593, by rfl⟩ : syracuseStep 58444249 = 43833187) B43833187
theorem B77925665 : Blo 1945435 77925665 := bstep (se 2 (by rfl) ⟨29222124, by rfl⟩ : syracuseStep 77925665 = 58444249) B58444249
theorem B51950443 : Blo 1945435 51950443 := bstep (se 1 (by rfl) ⟨38962832, by rfl⟩ : syracuseStep 51950443 = 77925665) B77925665
theorem B69267257 : Blo 1945435 69267257 := bstep (se 2 (by rfl) ⟨25975221, by rfl⟩ : syracuseStep 69267257 = 51950443) B51950443
theorem B46178171 : Blo 1945435 46178171 := bstep (se 1 (by rfl) ⟨34633628, by rfl⟩ : syracuseStep 46178171 = 69267257) B69267257
theorem B30785447 : Blo 1945435 30785447 := bstep (se 1 (by rfl) ⟨23089085, by rfl⟩ : syracuseStep 30785447 = 46178171) B46178171
theorem B20523631 : Blo 1945435 20523631 := bstep (se 1 (by rfl) ⟨15392723, by rfl⟩ : syracuseStep 20523631 = 30785447) B30785447
theorem B27364841 : Blo 1945435 27364841 := bstep (se 2 (by rfl) ⟨10261815, by rfl⟩ : syracuseStep 27364841 = 20523631) B20523631
theorem B18243227 : Blo 1945435 18243227 := bstep (se 1 (by rfl) ⟨13682420, by rfl⟩ : syracuseStep 18243227 = 27364841) B27364841
theorem B12162151 : Blo 1945435 12162151 := bstep (se 1 (by rfl) ⟨9121613, by rfl⟩ : syracuseStep 12162151 = 18243227) B18243227
theorem B16216201 : Blo 1945435 16216201 := bstep (se 2 (by rfl) ⟨6081075, by rfl⟩ : syracuseStep 16216201 = 12162151) B12162151
theorem B21621601 : Blo 1945435 21621601 := bstep (se 2 (by rfl) ⟨8108100, by rfl⟩ : syracuseStep 21621601 = 16216201) B16216201
theorem B28828801 : Blo 1945435 28828801 := bstep (se 2 (by rfl) ⟨10810800, by rfl⟩ : syracuseStep 28828801 = 21621601) B21621601
theorem B38438401 : Blo 1945435 38438401 := bstep (se 2 (by rfl) ⟨14414400, by rfl⟩ : syracuseStep 38438401 = 28828801) B28828801
theorem B51251201 : Blo 1945435 51251201 := bstep (se 2 (by rfl) ⟨19219200, by rfl⟩ : syracuseStep 51251201 = 38438401) B38438401
theorem B34167467 : Blo 1945435 34167467 := bstep (se 1 (by rfl) ⟨25625600, by rfl⟩ : syracuseStep 34167467 = 51251201) B51251201
theorem B91113245 : Blo 1945435 91113245 := bstep (se 3 (by rfl) ⟨17083733, by rfl⟩ : syracuseStep 91113245 = 34167467) B34167467
theorem B60742163 : Blo 1945435 60742163 := bstep (se 1 (by rfl) ⟨45556622, by rfl⟩ : syracuseStep 60742163 = 91113245) B91113245
theorem B40494775 : Blo 1945435 40494775 := bstep (se 1 (by rfl) ⟨30371081, by rfl⟩ : syracuseStep 40494775 = 60742163) B60742163
theorem B53993033 : Blo 1945435 53993033 := bstep (se 2 (by rfl) ⟨20247387, by rfl⟩ : syracuseStep 53993033 = 40494775) B40494775
theorem B35995355 : Blo 1945435 35995355 := bstep (se 1 (by rfl) ⟨26996516, by rfl⟩ : syracuseStep 35995355 = 53993033) B53993033
theorem B23996903 : Blo 1945435 23996903 := bstep (se 1 (by rfl) ⟨17997677, by rfl⟩ : syracuseStep 23996903 = 35995355) B35995355
theorem B63991741 : Blo 1945435 63991741 := bstep (se 3 (by rfl) ⟨11998451, by rfl⟩ : syracuseStep 63991741 = 23996903) B23996903
theorem B85322321 : Blo 1945435 85322321 := bstep (se 2 (by rfl) ⟨31995870, by rfl⟩ : syracuseStep 85322321 = 63991741) B63991741
theorem B56881547 : Blo 1945435 56881547 := bstep (se 1 (by rfl) ⟨42661160, by rfl⟩ : syracuseStep 56881547 = 85322321) B85322321
theorem B37921031 : Blo 1945435 37921031 := bstep (se 1 (by rfl) ⟨28440773, by rfl⟩ : syracuseStep 37921031 = 56881547) B56881547
theorem B25280687 : Blo 1945435 25280687 := bstep (se 1 (by rfl) ⟨18960515, by rfl⟩ : syracuseStep 25280687 = 37921031) B37921031
theorem B67415165 : Blo 1945435 67415165 := bstep (se 3 (by rfl) ⟨12640343, by rfl⟩ : syracuseStep 67415165 = 25280687) B25280687
theorem B44943443 : Blo 1945435 44943443 := bstep (se 1 (by rfl) ⟨33707582, by rfl⟩ : syracuseStep 44943443 = 67415165) B67415165
theorem B29962295 : Blo 1945435 29962295 := bstep (se 1 (by rfl) ⟨22471721, by rfl⟩ : syracuseStep 29962295 = 44943443) B44943443
theorem B19974863 : Blo 1945435 19974863 := bstep (se 1 (by rfl) ⟨14981147, by rfl⟩ : syracuseStep 19974863 = 29962295) B29962295
theorem B13316575 : Blo 1945435 13316575 := bstep (se 1 (by rfl) ⟨9987431, by rfl⟩ : syracuseStep 13316575 = 19974863) B19974863
theorem B17755433 : Blo 1945435 17755433 := bstep (se 2 (by rfl) ⟨6658287, by rfl⟩ : syracuseStep 17755433 = 13316575) B13316575
theorem B11836955 : Blo 1945435 11836955 := bstep (se 1 (by rfl) ⟨8877716, by rfl⟩ : syracuseStep 11836955 = 17755433) B17755433
theorem B31565213 : Blo 1945435 31565213 := bstep (se 3 (by rfl) ⟨5918477, by rfl⟩ : syracuseStep 31565213 = 11836955) B11836955
theorem B21043475 : Blo 1945435 21043475 := bstep (se 1 (by rfl) ⟨15782606, by rfl⟩ : syracuseStep 21043475 = 31565213) B31565213
theorem B14028983 : Blo 1945435 14028983 := bstep (se 1 (by rfl) ⟨10521737, by rfl⟩ : syracuseStep 14028983 = 21043475) B21043475
theorem B9352655 : Blo 1945435 9352655 := bstep (se 1 (by rfl) ⟨7014491, by rfl⟩ : syracuseStep 9352655 = 14028983) B14028983
theorem B6235103 : Blo 1945435 6235103 := bstep (se 1 (by rfl) ⟨4676327, by rfl⟩ : syracuseStep 6235103 = 9352655) B9352655
theorem B16626941 : Blo 1945435 16626941 := bstep (se 3 (by rfl) ⟨3117551, by rfl⟩ : syracuseStep 16626941 = 6235103) B6235103
theorem B11084627 : Blo 1945435 11084627 := bstep (se 1 (by rfl) ⟨8313470, by rfl⟩ : syracuseStep 11084627 = 16626941) B16626941
theorem B7389751 : Blo 1945435 7389751 := bstep (se 1 (by rfl) ⟨5542313, by rfl⟩ : syracuseStep 7389751 = 11084627) B11084627
theorem B9853001 : Blo 1945435 9853001 := bstep (se 2 (by rfl) ⟨3694875, by rfl⟩ : syracuseStep 9853001 = 7389751) B7389751
theorem B6568667 : Blo 1945435 6568667 := bstep (se 1 (by rfl) ⟨4926500, by rfl⟩ : syracuseStep 6568667 = 9853001) B9853001
theorem B4379111 : Blo 1945435 4379111 := bstep (se 1 (by rfl) ⟨3284333, by rfl⟩ : syracuseStep 4379111 = 6568667) B6568667
theorem B2919407 : Blo 1945435 2919407 := bstep (se 1 (by rfl) ⟨2189555, by rfl⟩ : syracuseStep 2919407 = 4379111) B4379111
theorem B1946271 : Blo 1945435 1946271 := bstep (se 1 (by rfl) ⟨1459703, by rfl⟩ : syracuseStep 1946271 = 2919407) B2919407
theorem B2919413 : Blo 1945435 2919413 := bbase (se 5 (by rfl) ⟨136847, by rfl⟩ : syracuseStep 2919413 = 273695) (by norm_num)
theorem B1946275 : Blo 1945435 1946275 := bstep (se 1 (by rfl) ⟨1459706, by rfl⟩ : syracuseStep 1946275 = 2919413) B2919413
theorem B3117565 : Blo 1945435 3117565 := bbase (se 3 (by rfl) ⟨584543, by rfl⟩ : syracuseStep 3117565 = 1169087) (by norm_num)
theorem B4156753 : Blo 1945435 4156753 := bstep (se 2 (by rfl) ⟨1558782, by rfl⟩ : syracuseStep 4156753 = 3117565) B3117565
theorem B5542337 : Blo 1945435 5542337 := bstep (se 2 (by rfl) ⟨2078376, by rfl⟩ : syracuseStep 5542337 = 4156753) B4156753
theorem B3694891 : Blo 1945435 3694891 := bstep (se 1 (by rfl) ⟨2771168, by rfl⟩ : syracuseStep 3694891 = 5542337) B5542337
theorem B4926521 : Blo 1945435 4926521 := bstep (se 2 (by rfl) ⟨1847445, by rfl⟩ : syracuseStep 4926521 = 3694891) B3694891
theorem B3284347 : Blo 1945435 3284347 := bstep (se 1 (by rfl) ⟨2463260, by rfl⟩ : syracuseStep 3284347 = 4926521) B4926521
theorem B4379129 : Blo 1945435 4379129 := bstep (se 2 (by rfl) ⟨1642173, by rfl⟩ : syracuseStep 4379129 = 3284347) B3284347
theorem B2919419 : Blo 1945435 2919419 := bstep (se 1 (by rfl) ⟨2189564, by rfl⟩ : syracuseStep 2919419 = 4379129) B4379129
theorem B1946279 : Blo 1945435 1946279 := bstep (se 1 (by rfl) ⟨1459709, by rfl⟩ : syracuseStep 1946279 = 2919419) B2919419
theorem B2189569 : Blo 1945435 2189569 := bbase (se 2 (by rfl) ⟨821088, by rfl⟩ : syracuseStep 2189569 = 1642177) (by norm_num)
theorem B2919425 : Blo 1945435 2919425 := bstep (se 2 (by rfl) ⟨1094784, by rfl⟩ : syracuseStep 2919425 = 2189569) B2189569
theorem B1946283 : Blo 1945435 1946283 := bstep (se 1 (by rfl) ⟨1459712, by rfl⟩ : syracuseStep 1946283 = 2919425) B2919425
theorem B4926541 : Blo 1945435 4926541 := bbase (se 3 (by rfl) ⟨923726, by rfl⟩ : syracuseStep 4926541 = 1847453) (by norm_num)
theorem B6568721 : Blo 1945435 6568721 := bstep (se 2 (by rfl) ⟨2463270, by rfl⟩ : syracuseStep 6568721 = 4926541) B4926541
theorem B4379147 : Blo 1945435 4379147 := bstep (se 1 (by rfl) ⟨3284360, by rfl⟩ : syracuseStep 4379147 = 6568721) B6568721
theorem B2919431 : Blo 1945435 2919431 := bstep (se 1 (by rfl) ⟨2189573, by rfl⟩ : syracuseStep 2919431 = 4379147) B4379147
theorem B1946287 : Blo 1945435 1946287 := bstep (se 1 (by rfl) ⟨1459715, by rfl⟩ : syracuseStep 1946287 = 2919431) B2919431
theorem B2919437 : Blo 1945435 2919437 := bbase (se 3 (by rfl) ⟨547394, by rfl⟩ : syracuseStep 2919437 = 1094789) (by norm_num)
theorem B1946291 : Blo 1945435 1946291 := bstep (se 1 (by rfl) ⟨1459718, by rfl⟩ : syracuseStep 1946291 = 2919437) B2919437
theorem B4379165 : Blo 1945435 4379165 := bbase (se 3 (by rfl) ⟨821093, by rfl⟩ : syracuseStep 4379165 = 1642187) (by norm_num)
theorem B2919443 : Blo 1945435 2919443 := bstep (se 1 (by rfl) ⟨2189582, by rfl⟩ : syracuseStep 2919443 = 4379165) B4379165
theorem B1946295 : Blo 1945435 1946295 := bstep (se 1 (by rfl) ⟨1459721, by rfl⟩ : syracuseStep 1946295 = 2919443) B2919443
theorem B3284381 : Blo 1945435 3284381 := bbase (se 3 (by rfl) ⟨615821, by rfl⟩ : syracuseStep 3284381 = 1231643) (by norm_num)
theorem B2189587 : Blo 1945435 2189587 := bstep (se 1 (by rfl) ⟨1642190, by rfl⟩ : syracuseStep 2189587 = 3284381) B3284381
theorem B2919449 : Blo 1945435 2919449 := bstep (se 2 (by rfl) ⟨1094793, by rfl⟩ : syracuseStep 2919449 = 2189587) B2189587
theorem B1946299 : Blo 1945435 1946299 := bstep (se 1 (by rfl) ⟨1459724, by rfl⟩ : syracuseStep 1946299 = 2919449) B2919449
theorem B4271005 : Blo 1945435 4271005 := bbase (se 3 (by rfl) ⟨800813, by rfl⟩ : syracuseStep 4271005 = 1601627) (by norm_num)
theorem B5694673 : Blo 1945435 5694673 := bstep (se 2 (by rfl) ⟨2135502, by rfl⟩ : syracuseStep 5694673 = 4271005) B4271005
theorem B7592897 : Blo 1945435 7592897 := bstep (se 2 (by rfl) ⟨2847336, by rfl⟩ : syracuseStep 7592897 = 5694673) B5694673
theorem B20247725 : Blo 1945435 20247725 := bstep (se 3 (by rfl) ⟨3796448, by rfl⟩ : syracuseStep 20247725 = 7592897) B7592897
theorem B13498483 : Blo 1945435 13498483 := bstep (se 1 (by rfl) ⟨10123862, by rfl⟩ : syracuseStep 13498483 = 20247725) B20247725
theorem B17997977 : Blo 1945435 17997977 := bstep (se 2 (by rfl) ⟨6749241, by rfl⟩ : syracuseStep 17997977 = 13498483) B13498483
theorem B47994605 : Blo 1945435 47994605 := bstep (se 3 (by rfl) ⟨8998988, by rfl⟩ : syracuseStep 47994605 = 17997977) B17997977
theorem B31996403 : Blo 1945435 31996403 := bstep (se 1 (by rfl) ⟨23997302, by rfl⟩ : syracuseStep 31996403 = 47994605) B47994605
theorem B21330935 : Blo 1945435 21330935 := bstep (se 1 (by rfl) ⟨15998201, by rfl⟩ : syracuseStep 21330935 = 31996403) B31996403
theorem B14220623 : Blo 1945435 14220623 := bstep (se 1 (by rfl) ⟨10665467, by rfl⟩ : syracuseStep 14220623 = 21330935) B21330935
theorem B9480415 : Blo 1945435 9480415 := bstep (se 1 (by rfl) ⟨7110311, by rfl⟩ : syracuseStep 9480415 = 14220623) B14220623
theorem B12640553 : Blo 1945435 12640553 := bstep (se 2 (by rfl) ⟨4740207, by rfl⟩ : syracuseStep 12640553 = 9480415) B9480415
theorem B8427035 : Blo 1945435 8427035 := bstep (se 1 (by rfl) ⟨6320276, by rfl⟩ : syracuseStep 8427035 = 12640553) B12640553
theorem B22472093 : Blo 1945435 22472093 := bstep (se 3 (by rfl) ⟨4213517, by rfl⟩ : syracuseStep 22472093 = 8427035) B8427035
theorem B14981395 : Blo 1945435 14981395 := bstep (se 1 (by rfl) ⟨11236046, by rfl⟩ : syracuseStep 14981395 = 22472093) B22472093
theorem B19975193 : Blo 1945435 19975193 := bstep (se 2 (by rfl) ⟨7490697, by rfl⟩ : syracuseStep 19975193 = 14981395) B14981395
theorem B13316795 : Blo 1945435 13316795 := bstep (se 1 (by rfl) ⟨9987596, by rfl⟩ : syracuseStep 13316795 = 19975193) B19975193
theorem B8877863 : Blo 1945435 8877863 := bstep (se 1 (by rfl) ⟨6658397, by rfl⟩ : syracuseStep 8877863 = 13316795) B13316795
theorem B5918575 : Blo 1945435 5918575 := bstep (se 1 (by rfl) ⟨4438931, by rfl⟩ : syracuseStep 5918575 = 8877863) B8877863
theorem B7891433 : Blo 1945435 7891433 := bstep (se 2 (by rfl) ⟨2959287, by rfl⟩ : syracuseStep 7891433 = 5918575) B5918575
theorem B5260955 : Blo 1945435 5260955 := bstep (se 1 (by rfl) ⟨3945716, by rfl⟩ : syracuseStep 5260955 = 7891433) B7891433
theorem B14029213 : Blo 1945435 14029213 := bstep (se 3 (by rfl) ⟨2630477, by rfl⟩ : syracuseStep 14029213 = 5260955) B5260955
theorem B18705617 : Blo 1945435 18705617 := bstep (se 2 (by rfl) ⟨7014606, by rfl⟩ : syracuseStep 18705617 = 14029213) B14029213
theorem B12470411 : Blo 1945435 12470411 := bstep (se 1 (by rfl) ⟨9352808, by rfl⟩ : syracuseStep 12470411 = 18705617) B18705617
theorem B8313607 : Blo 1945435 8313607 := bstep (se 1 (by rfl) ⟨6235205, by rfl⟩ : syracuseStep 8313607 = 12470411) B12470411
theorem B11084809 : Blo 1945435 11084809 := bstep (se 2 (by rfl) ⟨4156803, by rfl⟩ : syracuseStep 11084809 = 8313607) B8313607
theorem B14779745 : Blo 1945435 14779745 := bstep (se 2 (by rfl) ⟨5542404, by rfl⟩ : syracuseStep 14779745 = 11084809) B11084809
theorem B9853163 : Blo 1945435 9853163 := bstep (se 1 (by rfl) ⟨7389872, by rfl⟩ : syracuseStep 9853163 = 14779745) B14779745
theorem B6568775 : Blo 1945435 6568775 := bstep (se 1 (by rfl) ⟨4926581, by rfl⟩ : syracuseStep 6568775 = 9853163) B9853163
theorem B4379183 : Blo 1945435 4379183 := bstep (se 1 (by rfl) ⟨3284387, by rfl⟩ : syracuseStep 4379183 = 6568775) B6568775
theorem B2919455 : Blo 1945435 2919455 := bstep (se 1 (by rfl) ⟨2189591, by rfl⟩ : syracuseStep 2919455 = 4379183) B4379183
theorem B1946303 : Blo 1945435 1946303 := bstep (se 1 (by rfl) ⟨1459727, by rfl⟩ : syracuseStep 1946303 = 2919455) B2919455
theorem B2919461 : Blo 1945435 2919461 := bbase (se 4 (by rfl) ⟨273699, by rfl⟩ : syracuseStep 2919461 = 547399) (by norm_num)
theorem B1946307 : Blo 1945435 1946307 := bstep (se 1 (by rfl) ⟨1459730, by rfl⟩ : syracuseStep 1946307 = 2919461) B2919461
theorem B2463301 : Blo 1945435 2463301 := bbase (se 4 (by rfl) ⟨230934, by rfl⟩ : syracuseStep 2463301 = 461869) (by norm_num)
theorem B3284401 : Blo 1945435 3284401 := bstep (se 2 (by rfl) ⟨1231650, by rfl⟩ : syracuseStep 3284401 = 2463301) B2463301
theorem B4379201 : Blo 1945435 4379201 := bstep (se 2 (by rfl) ⟨1642200, by rfl⟩ : syracuseStep 4379201 = 3284401) B3284401
theorem B2919467 : Blo 1945435 2919467 := bstep (se 1 (by rfl) ⟨2189600, by rfl⟩ : syracuseStep 2919467 = 4379201) B4379201
theorem B1946311 : Blo 1945435 1946311 := bstep (se 1 (by rfl) ⟨1459733, by rfl⟩ : syracuseStep 1946311 = 2919467) B2919467
theorem B2189605 : Blo 1945435 2189605 := bbase (se 4 (by rfl) ⟨205275, by rfl⟩ : syracuseStep 2189605 = 410551) (by norm_num)
theorem B2919473 : Blo 1945435 2919473 := bstep (se 2 (by rfl) ⟨1094802, by rfl⟩ : syracuseStep 2919473 = 2189605) B2189605
theorem B1946315 : Blo 1945435 1946315 := bstep (se 1 (by rfl) ⟨1459736, by rfl⟩ : syracuseStep 1946315 = 2919473) B2919473
theorem B3117629 : Blo 1945435 3117629 := bbase (se 3 (by rfl) ⟨584555, by rfl⟩ : syracuseStep 3117629 = 1169111) (by norm_num)
theorem B8313677 : Blo 1945435 8313677 := bstep (se 3 (by rfl) ⟨1558814, by rfl⟩ : syracuseStep 8313677 = 3117629) B3117629
theorem B5542451 : Blo 1945435 5542451 := bstep (se 1 (by rfl) ⟨4156838, by rfl⟩ : syracuseStep 5542451 = 8313677) B8313677
theorem B3694967 : Blo 1945435 3694967 := bstep (se 1 (by rfl) ⟨2771225, by rfl⟩ : syracuseStep 3694967 = 5542451) B5542451
theorem B2463311 : Blo 1945435 2463311 := bstep (se 1 (by rfl) ⟨1847483, by rfl⟩ : syracuseStep 2463311 = 3694967) B3694967
theorem B6568829 : Blo 1945435 6568829 := bstep (se 3 (by rfl) ⟨1231655, by rfl⟩ : syracuseStep 6568829 = 2463311) B2463311
theorem B4379219 : Blo 1945435 4379219 := bstep (se 1 (by rfl) ⟨3284414, by rfl⟩ : syracuseStep 4379219 = 6568829) B6568829
theorem B2919479 : Blo 1945435 2919479 := bstep (se 1 (by rfl) ⟨2189609, by rfl⟩ : syracuseStep 2919479 = 4379219) B4379219
theorem B1946319 : Blo 1945435 1946319 := bstep (se 1 (by rfl) ⟨1459739, by rfl⟩ : syracuseStep 1946319 = 2919479) B2919479
theorem B2919485 : Blo 1945435 2919485 := bbase (se 3 (by rfl) ⟨547403, by rfl⟩ : syracuseStep 2919485 = 1094807) (by norm_num)
theorem B1946323 : Blo 1945435 1946323 := bstep (se 1 (by rfl) ⟨1459742, by rfl⟩ : syracuseStep 1946323 = 2919485) B2919485
theorem B4379237 : Blo 1945435 4379237 := bbase (se 4 (by rfl) ⟨410553, by rfl⟩ : syracuseStep 4379237 = 821107) (by norm_num)
theorem B2919491 : Blo 1945435 2919491 := bstep (se 1 (by rfl) ⟨2189618, by rfl⟩ : syracuseStep 2919491 = 4379237) B4379237
theorem B1946327 : Blo 1945435 1946327 := bstep (se 1 (by rfl) ⟨1459745, by rfl⟩ : syracuseStep 1946327 = 2919491) B2919491
theorem B4926653 : Blo 1945435 4926653 := bbase (se 3 (by rfl) ⟨923747, by rfl⟩ : syracuseStep 4926653 = 1847495) (by norm_num)
theorem B3284435 : Blo 1945435 3284435 := bstep (se 1 (by rfl) ⟨2463326, by rfl⟩ : syracuseStep 3284435 = 4926653) B4926653
theorem B2189623 : Blo 1945435 2189623 := bstep (se 1 (by rfl) ⟨1642217, by rfl⟩ : syracuseStep 2189623 = 3284435) B3284435
theorem B2919497 : Blo 1945435 2919497 := bstep (se 2 (by rfl) ⟨1094811, by rfl⟩ : syracuseStep 2919497 = 2189623) B2189623
theorem B1946331 : Blo 1945435 1946331 := bstep (se 1 (by rfl) ⟨1459748, by rfl⟩ : syracuseStep 1946331 = 2919497) B2919497
theorem B3694997 : Blo 1945435 3694997 := bbase (se 6 (by rfl) ⟨86601, by rfl⟩ : syracuseStep 3694997 = 173203) (by norm_num)
theorem B9853325 : Blo 1945435 9853325 := bstep (se 3 (by rfl) ⟨1847498, by rfl⟩ : syracuseStep 9853325 = 3694997) B3694997
theorem B6568883 : Blo 1945435 6568883 := bstep (se 1 (by rfl) ⟨4926662, by rfl⟩ : syracuseStep 6568883 = 9853325) B9853325
theorem B4379255 : Blo 1945435 4379255 := bstep (se 1 (by rfl) ⟨3284441, by rfl⟩ : syracuseStep 4379255 = 6568883) B6568883
theorem B2919503 : Blo 1945435 2919503 := bstep (se 1 (by rfl) ⟨2189627, by rfl⟩ : syracuseStep 2919503 = 4379255) B4379255
theorem B1946335 : Blo 1945435 1946335 := bstep (se 1 (by rfl) ⟨1459751, by rfl⟩ : syracuseStep 1946335 = 2919503) B2919503
theorem B2919509 : Blo 1945435 2919509 := bbase (se 8 (by rfl) ⟨17106, by rfl⟩ : syracuseStep 2919509 = 34213) (by norm_num)
theorem B1946339 : Blo 1945435 1946339 := bstep (se 1 (by rfl) ⟨1459754, by rfl⟩ : syracuseStep 1946339 = 2919509) B2919509
theorem B4676501 : Blo 1945435 4676501 := bbase (se 6 (by rfl) ⟨109605, by rfl⟩ : syracuseStep 4676501 = 219211) (by norm_num)
theorem B12470669 : Blo 1945435 12470669 := bstep (se 3 (by rfl) ⟨2338250, by rfl⟩ : syracuseStep 12470669 = 4676501) B4676501
theorem B8313779 : Blo 1945435 8313779 := bstep (se 1 (by rfl) ⟨6235334, by rfl⟩ : syracuseStep 8313779 = 12470669) B12470669
theorem B5542519 : Blo 1945435 5542519 := bstep (se 1 (by rfl) ⟨4156889, by rfl⟩ : syracuseStep 5542519 = 8313779) B8313779
theorem B7390025 : Blo 1945435 7390025 := bstep (se 2 (by rfl) ⟨2771259, by rfl⟩ : syracuseStep 7390025 = 5542519) B5542519
theorem B4926683 : Blo 1945435 4926683 := bstep (se 1 (by rfl) ⟨3695012, by rfl⟩ : syracuseStep 4926683 = 7390025) B7390025
theorem B3284455 : Blo 1945435 3284455 := bstep (se 1 (by rfl) ⟨2463341, by rfl⟩ : syracuseStep 3284455 = 4926683) B4926683
theorem B4379273 : Blo 1945435 4379273 := bstep (se 2 (by rfl) ⟨1642227, by rfl⟩ : syracuseStep 4379273 = 3284455) B3284455
theorem B2919515 : Blo 1945435 2919515 := bstep (se 1 (by rfl) ⟨2189636, by rfl⟩ : syracuseStep 2919515 = 4379273) B4379273
theorem B1946343 : Blo 1945435 1946343 := bstep (se 1 (by rfl) ⟨1459757, by rfl⟩ : syracuseStep 1946343 = 2919515) B2919515
theorem B2189641 : Blo 1945435 2189641 := bbase (se 2 (by rfl) ⟨821115, by rfl⟩ : syracuseStep 2189641 = 1642231) (by norm_num)
theorem B2919521 : Blo 1945435 2919521 := bstep (se 2 (by rfl) ⟨1094820, by rfl⟩ : syracuseStep 2919521 = 2189641) B2189641
theorem B1946347 : Blo 1945435 1946347 := bstep (se 1 (by rfl) ⟨1459760, by rfl⟩ : syracuseStep 1946347 = 2919521) B2919521
theorem B3603749 : Blo 1945435 3603749 := bbase (se 4 (by rfl) ⟨337851, by rfl⟩ : syracuseStep 3603749 = 675703) (by norm_num)
theorem B9609997 : Blo 1945435 9609997 := bstep (se 3 (by rfl) ⟨1801874, by rfl⟩ : syracuseStep 9609997 = 3603749) B3603749
theorem B12813329 : Blo 1945435 12813329 := bstep (se 2 (by rfl) ⟨4804998, by rfl⟩ : syracuseStep 12813329 = 9609997) B9609997
theorem B34168877 : Blo 1945435 34168877 := bstep (se 3 (by rfl) ⟨6406664, by rfl⟩ : syracuseStep 34168877 = 12813329) B12813329
theorem B22779251 : Blo 1945435 22779251 := bstep (se 1 (by rfl) ⟨17084438, by rfl⟩ : syracuseStep 22779251 = 34168877) B34168877
theorem B15186167 : Blo 1945435 15186167 := bstep (se 1 (by rfl) ⟨11389625, by rfl⟩ : syracuseStep 15186167 = 22779251) B22779251
theorem B10124111 : Blo 1945435 10124111 := bstep (se 1 (by rfl) ⟨7593083, by rfl⟩ : syracuseStep 10124111 = 15186167) B15186167
theorem B6749407 : Blo 1945435 6749407 := bstep (se 1 (by rfl) ⟨5062055, by rfl⟩ : syracuseStep 6749407 = 10124111) B10124111
theorem B8999209 : Blo 1945435 8999209 := bstep (se 2 (by rfl) ⟨3374703, by rfl⟩ : syracuseStep 8999209 = 6749407) B6749407
theorem B11998945 : Blo 1945435 11998945 := bstep (se 2 (by rfl) ⟨4499604, by rfl⟩ : syracuseStep 11998945 = 8999209) B8999209
theorem B15998593 : Blo 1945435 15998593 := bstep (se 2 (by rfl) ⟨5999472, by rfl⟩ : syracuseStep 15998593 = 11998945) B11998945
theorem B21331457 : Blo 1945435 21331457 := bstep (se 2 (by rfl) ⟨7999296, by rfl⟩ : syracuseStep 21331457 = 15998593) B15998593
theorem B14220971 : Blo 1945435 14220971 := bstep (se 1 (by rfl) ⟨10665728, by rfl⟩ : syracuseStep 14220971 = 21331457) B21331457
theorem B9480647 : Blo 1945435 9480647 := bstep (se 1 (by rfl) ⟨7110485, by rfl⟩ : syracuseStep 9480647 = 14220971) B14220971
theorem B6320431 : Blo 1945435 6320431 := bstep (se 1 (by rfl) ⟨4740323, by rfl⟩ : syracuseStep 6320431 = 9480647) B9480647
theorem B8427241 : Blo 1945435 8427241 := bstep (se 2 (by rfl) ⟨3160215, by rfl⟩ : syracuseStep 8427241 = 6320431) B6320431
theorem B44945285 : Blo 1945435 44945285 := bstep (se 4 (by rfl) ⟨4213620, by rfl⟩ : syracuseStep 44945285 = 8427241) B8427241
theorem B119854093 : Blo 1945435 119854093 := bstep (se 3 (by rfl) ⟨22472642, by rfl⟩ : syracuseStep 119854093 = 44945285) B44945285
theorem B159805457 : Blo 1945435 159805457 := bstep (se 2 (by rfl) ⟨59927046, by rfl⟩ : syracuseStep 159805457 = 119854093) B119854093
theorem B106536971 : Blo 1945435 106536971 := bstep (se 1 (by rfl) ⟨79902728, by rfl⟩ : syracuseStep 106536971 = 159805457) B159805457
theorem B71024647 : Blo 1945435 71024647 := bstep (se 1 (by rfl) ⟨53268485, by rfl⟩ : syracuseStep 71024647 = 106536971) B106536971
theorem B94699529 : Blo 1945435 94699529 := bstep (se 2 (by rfl) ⟨35512323, by rfl⟩ : syracuseStep 94699529 = 71024647) B71024647
theorem B63133019 : Blo 1945435 63133019 := bstep (se 1 (by rfl) ⟨47349764, by rfl⟩ : syracuseStep 63133019 = 94699529) B94699529
theorem B42088679 : Blo 1945435 42088679 := bstep (se 1 (by rfl) ⟨31566509, by rfl⟩ : syracuseStep 42088679 = 63133019) B63133019
theorem B28059119 : Blo 1945435 28059119 := bstep (se 1 (by rfl) ⟨21044339, by rfl⟩ : syracuseStep 28059119 = 42088679) B42088679
theorem B18706079 : Blo 1945435 18706079 := bstep (se 1 (by rfl) ⟨14029559, by rfl⟩ : syracuseStep 18706079 = 28059119) B28059119
theorem B12470719 : Blo 1945435 12470719 := bstep (se 1 (by rfl) ⟨9353039, by rfl⟩ : syracuseStep 12470719 = 18706079) B18706079
theorem B16627625 : Blo 1945435 16627625 := bstep (se 2 (by rfl) ⟨6235359, by rfl⟩ : syracuseStep 16627625 = 12470719) B12470719
theorem B11085083 : Blo 1945435 11085083 := bstep (se 1 (by rfl) ⟨8313812, by rfl⟩ : syracuseStep 11085083 = 16627625) B16627625
theorem B7390055 : Blo 1945435 7390055 := bstep (se 1 (by rfl) ⟨5542541, by rfl⟩ : syracuseStep 7390055 = 11085083) B11085083
theorem B4926703 : Blo 1945435 4926703 := bstep (se 1 (by rfl) ⟨3695027, by rfl⟩ : syracuseStep 4926703 = 7390055) B7390055
theorem B6568937 : Blo 1945435 6568937 := bstep (se 2 (by rfl) ⟨2463351, by rfl⟩ : syracuseStep 6568937 = 4926703) B4926703
theorem B4379291 : Blo 1945435 4379291 := bstep (se 1 (by rfl) ⟨3284468, by rfl⟩ : syracuseStep 4379291 = 6568937) B6568937
theorem B2919527 : Blo 1945435 2919527 := bstep (se 1 (by rfl) ⟨2189645, by rfl⟩ : syracuseStep 2919527 = 4379291) B4379291
theorem B1946351 : Blo 1945435 1946351 := bstep (se 1 (by rfl) ⟨1459763, by rfl⟩ : syracuseStep 1946351 = 2919527) B2919527
theorem B2919533 : Blo 1945435 2919533 := bbase (se 3 (by rfl) ⟨547412, by rfl⟩ : syracuseStep 2919533 = 1094825) (by norm_num)
theorem B1946355 : Blo 1945435 1946355 := bstep (se 1 (by rfl) ⟨1459766, by rfl⟩ : syracuseStep 1946355 = 2919533) B2919533
theorem B4379309 : Blo 1945435 4379309 := bbase (se 3 (by rfl) ⟨821120, by rfl⟩ : syracuseStep 4379309 = 1642241) (by norm_num)
theorem B2919539 : Blo 1945435 2919539 := bstep (se 1 (by rfl) ⟨2189654, by rfl⟩ : syracuseStep 2919539 = 4379309) B4379309
theorem B1946359 : Blo 1945435 1946359 := bstep (se 1 (by rfl) ⟨1459769, by rfl⟩ : syracuseStep 1946359 = 2919539) B2919539
theorem B4156933 : Blo 1945435 4156933 := bbase (se 4 (by rfl) ⟨389712, by rfl⟩ : syracuseStep 4156933 = 779425) (by norm_num)
theorem B5542577 : Blo 1945435 5542577 := bstep (se 2 (by rfl) ⟨2078466, by rfl⟩ : syracuseStep 5542577 = 4156933) B4156933
theorem B3695051 : Blo 1945435 3695051 := bstep (se 1 (by rfl) ⟨2771288, by rfl⟩ : syracuseStep 3695051 = 5542577) B5542577
theorem B2463367 : Blo 1945435 2463367 := bstep (se 1 (by rfl) ⟨1847525, by rfl⟩ : syracuseStep 2463367 = 3695051) B3695051
theorem B3284489 : Blo 1945435 3284489 := bstep (se 2 (by rfl) ⟨1231683, by rfl⟩ : syracuseStep 3284489 = 2463367) B2463367
theorem B2189659 : Blo 1945435 2189659 := bstep (se 1 (by rfl) ⟨1642244, by rfl⟩ : syracuseStep 2189659 = 3284489) B3284489
theorem B2919545 : Blo 1945435 2919545 := bstep (se 2 (by rfl) ⟨1094829, by rfl⟩ : syracuseStep 2919545 = 2189659) B2189659
theorem B1946363 : Blo 1945435 1946363 := bstep (se 1 (by rfl) ⟨1459772, by rfl⟩ : syracuseStep 1946363 = 2919545) B2919545
theorem B2249821 : Blo 1945435 2249821 := bbase (se 3 (by rfl) ⟨421841, by rfl⟩ : syracuseStep 2249821 = 843683) (by norm_num)
theorem B2999761 : Blo 1945435 2999761 := bstep (se 2 (by rfl) ⟨1124910, by rfl⟩ : syracuseStep 2999761 = 2249821) B2249821
theorem B15998725 : Blo 1945435 15998725 := bstep (se 4 (by rfl) ⟨1499880, by rfl⟩ : syracuseStep 15998725 = 2999761) B2999761
theorem B21331633 : Blo 1945435 21331633 := bstep (se 2 (by rfl) ⟨7999362, by rfl⟩ : syracuseStep 21331633 = 15998725) B15998725
theorem B28442177 : Blo 1945435 28442177 := bstep (se 2 (by rfl) ⟨10665816, by rfl⟩ : syracuseStep 28442177 = 21331633) B21331633
theorem B18961451 : Blo 1945435 18961451 := bstep (se 1 (by rfl) ⟨14221088, by rfl⟩ : syracuseStep 18961451 = 28442177) B28442177
theorem B12640967 : Blo 1945435 12640967 := bstep (se 1 (by rfl) ⟨9480725, by rfl⟩ : syracuseStep 12640967 = 18961451) B18961451
theorem B8427311 : Blo 1945435 8427311 := bstep (se 1 (by rfl) ⟨6320483, by rfl⟩ : syracuseStep 8427311 = 12640967) B12640967
theorem B5618207 : Blo 1945435 5618207 := bstep (se 1 (by rfl) ⟨4213655, by rfl⟩ : syracuseStep 5618207 = 8427311) B8427311
theorem B14981885 : Blo 1945435 14981885 := bstep (se 3 (by rfl) ⟨2809103, by rfl⟩ : syracuseStep 14981885 = 5618207) B5618207
theorem B9987923 : Blo 1945435 9987923 := bstep (se 1 (by rfl) ⟨7490942, by rfl⟩ : syracuseStep 9987923 = 14981885) B14981885
theorem B6658615 : Blo 1945435 6658615 := bstep (se 1 (by rfl) ⟨4993961, by rfl⟩ : syracuseStep 6658615 = 9987923) B9987923
theorem B35512613 : Blo 1945435 35512613 := bstep (se 4 (by rfl) ⟨3329307, by rfl⟩ : syracuseStep 35512613 = 6658615) B6658615
theorem B23675075 : Blo 1945435 23675075 := bstep (se 1 (by rfl) ⟨17756306, by rfl⟩ : syracuseStep 23675075 = 35512613) B35512613
theorem B15783383 : Blo 1945435 15783383 := bstep (se 1 (by rfl) ⟨11837537, by rfl⟩ : syracuseStep 15783383 = 23675075) B23675075
theorem B42089021 : Blo 1945435 42089021 := bstep (se 3 (by rfl) ⟨7891691, by rfl⟩ : syracuseStep 42089021 = 15783383) B15783383
theorem B28059347 : Blo 1945435 28059347 := bstep (se 1 (by rfl) ⟨21044510, by rfl⟩ : syracuseStep 28059347 = 42089021) B42089021
theorem B18706231 : Blo 1945435 18706231 := bstep (se 1 (by rfl) ⟨14029673, by rfl⟩ : syracuseStep 18706231 = 28059347) B28059347
theorem B24941641 : Blo 1945435 24941641 := bstep (se 2 (by rfl) ⟨9353115, by rfl⟩ : syracuseStep 24941641 = 18706231) B18706231
theorem B33255521 : Blo 1945435 33255521 := bstep (se 2 (by rfl) ⟨12470820, by rfl⟩ : syracuseStep 33255521 = 24941641) B24941641
theorem B22170347 : Blo 1945435 22170347 := bstep (se 1 (by rfl) ⟨16627760, by rfl⟩ : syracuseStep 22170347 = 33255521) B33255521
theorem B14780231 : Blo 1945435 14780231 := bstep (se 1 (by rfl) ⟨11085173, by rfl⟩ : syracuseStep 14780231 = 22170347) B22170347
theorem B9853487 : Blo 1945435 9853487 := bstep (se 1 (by rfl) ⟨7390115, by rfl⟩ : syracuseStep 9853487 = 14780231) B14780231
theorem B6568991 : Blo 1945435 6568991 := bstep (se 1 (by rfl) ⟨4926743, by rfl⟩ : syracuseStep 6568991 = 9853487) B9853487
theorem B4379327 : Blo 1945435 4379327 := bstep (se 1 (by rfl) ⟨3284495, by rfl⟩ : syracuseStep 4379327 = 6568991) B6568991
theorem B2919551 : Blo 1945435 2919551 := bstep (se 1 (by rfl) ⟨2189663, by rfl⟩ : syracuseStep 2919551 = 4379327) B4379327
theorem B1946367 : Blo 1945435 1946367 := bstep (se 1 (by rfl) ⟨1459775, by rfl⟩ : syracuseStep 1946367 = 2919551) B2919551
theorem B2919557 : Blo 1945435 2919557 := bbase (se 4 (by rfl) ⟨273708, by rfl⟩ : syracuseStep 2919557 = 547417) (by norm_num)
theorem B1946371 : Blo 1945435 1946371 := bstep (se 1 (by rfl) ⟨1459778, by rfl⟩ : syracuseStep 1946371 = 2919557) B2919557
theorem B3284509 : Blo 1945435 3284509 := bbase (se 3 (by rfl) ⟨615845, by rfl⟩ : syracuseStep 3284509 = 1231691) (by norm_num)
theorem B4379345 : Blo 1945435 4379345 := bstep (se 2 (by rfl) ⟨1642254, by rfl⟩ : syracuseStep 4379345 = 3284509) B3284509
theorem B2919563 : Blo 1945435 2919563 := bstep (se 1 (by rfl) ⟨2189672, by rfl⟩ : syracuseStep 2919563 = 4379345) B4379345
theorem B1946375 : Blo 1945435 1946375 := bstep (se 1 (by rfl) ⟨1459781, by rfl⟩ : syracuseStep 1946375 = 2919563) B2919563
theorem B2189677 : Blo 1945435 2189677 := bbase (se 3 (by rfl) ⟨410564, by rfl⟩ : syracuseStep 2189677 = 821129) (by norm_num)
theorem B2919569 : Blo 1945435 2919569 := bstep (se 2 (by rfl) ⟨1094838, by rfl⟩ : syracuseStep 2919569 = 2189677) B2189677
theorem B1946379 : Blo 1945435 1946379 := bstep (se 1 (by rfl) ⟨1459784, by rfl⟩ : syracuseStep 1946379 = 2919569) B2919569
theorem B6569045 : Blo 1945435 6569045 := bbase (se 8 (by rfl) ⟨38490, by rfl⟩ : syracuseStep 6569045 = 76981) (by norm_num)
theorem B4379363 : Blo 1945435 4379363 := bstep (se 1 (by rfl) ⟨3284522, by rfl⟩ : syracuseStep 4379363 = 6569045) B6569045
theorem B2919575 : Blo 1945435 2919575 := bstep (se 1 (by rfl) ⟨2189681, by rfl⟩ : syracuseStep 2919575 = 4379363) B4379363
theorem B1946383 : Blo 1945435 1946383 := bstep (se 1 (by rfl) ⟨1459787, by rfl⟩ : syracuseStep 1946383 = 2919575) B2919575
theorem B2919581 : Blo 1945435 2919581 := bbase (se 3 (by rfl) ⟨547421, by rfl⟩ : syracuseStep 2919581 = 1094843) (by norm_num)
theorem B1946387 : Blo 1945435 1946387 := bstep (se 1 (by rfl) ⟨1459790, by rfl⟩ : syracuseStep 1946387 = 2919581) B2919581
theorem B4379381 : Blo 1945435 4379381 := bbase (se 5 (by rfl) ⟨205283, by rfl⟩ : syracuseStep 4379381 = 410567) (by norm_num)
theorem B2919587 : Blo 1945435 2919587 := bstep (se 1 (by rfl) ⟨2189690, by rfl⟩ : syracuseStep 2919587 = 4379381) B4379381
theorem B1946391 : Blo 1945435 1946391 := bstep (se 1 (by rfl) ⟨1459793, by rfl⟩ : syracuseStep 1946391 = 2919587) B2919587
theorem B2338313 : Blo 1945435 2338313 := bbase (se 2 (by rfl) ⟨876867, by rfl⟩ : syracuseStep 2338313 = 1753735) (by norm_num)
theorem B24942005 : Blo 1945435 24942005 := bstep (se 5 (by rfl) ⟨1169156, by rfl⟩ : syracuseStep 24942005 = 2338313) B2338313
theorem B16628003 : Blo 1945435 16628003 := bstep (se 1 (by rfl) ⟨12471002, by rfl⟩ : syracuseStep 16628003 = 24942005) B24942005
theorem B11085335 : Blo 1945435 11085335 := bstep (se 1 (by rfl) ⟨8314001, by rfl⟩ : syracuseStep 11085335 = 16628003) B16628003
theorem B7390223 : Blo 1945435 7390223 := bstep (se 1 (by rfl) ⟨5542667, by rfl⟩ : syracuseStep 7390223 = 11085335) B11085335
theorem B4926815 : Blo 1945435 4926815 := bstep (se 1 (by rfl) ⟨3695111, by rfl⟩ : syracuseStep 4926815 = 7390223) B7390223
theorem B3284543 : Blo 1945435 3284543 := bstep (se 1 (by rfl) ⟨2463407, by rfl⟩ : syracuseStep 3284543 = 4926815) B4926815
theorem B2189695 : Blo 1945435 2189695 := bstep (se 1 (by rfl) ⟨1642271, by rfl⟩ : syracuseStep 2189695 = 3284543) B3284543
theorem B2919593 : Blo 1945435 2919593 := bstep (se 2 (by rfl) ⟨1094847, by rfl⟩ : syracuseStep 2919593 = 2189695) B2189695
theorem B1946395 : Blo 1945435 1946395 := bstep (se 1 (by rfl) ⟨1459796, by rfl⟩ : syracuseStep 1946395 = 2919593) B2919593
theorem B3117757 : Blo 1945435 3117757 := bbase (se 3 (by rfl) ⟨584579, by rfl⟩ : syracuseStep 3117757 = 1169159) (by norm_num)
theorem B4157009 : Blo 1945435 4157009 := bstep (se 2 (by rfl) ⟨1558878, by rfl⟩ : syracuseStep 4157009 = 3117757) B3117757
theorem B2771339 : Blo 1945435 2771339 := bstep (se 1 (by rfl) ⟨2078504, by rfl⟩ : syracuseStep 2771339 = 4157009) B4157009
theorem B7390237 : Blo 1945435 7390237 := bstep (se 3 (by rfl) ⟨1385669, by rfl⟩ : syracuseStep 7390237 = 2771339) B2771339
theorem B9853649 : Blo 1945435 9853649 := bstep (se 2 (by rfl) ⟨3695118, by rfl⟩ : syracuseStep 9853649 = 7390237) B7390237
theorem B6569099 : Blo 1945435 6569099 := bstep (se 1 (by rfl) ⟨4926824, by rfl⟩ : syracuseStep 6569099 = 9853649) B9853649
theorem B4379399 : Blo 1945435 4379399 := bstep (se 1 (by rfl) ⟨3284549, by rfl⟩ : syracuseStep 4379399 = 6569099) B6569099
theorem B2919599 : Blo 1945435 2919599 := bstep (se 1 (by rfl) ⟨2189699, by rfl⟩ : syracuseStep 2919599 = 4379399) B4379399
theorem B1946399 : Blo 1945435 1946399 := bstep (se 1 (by rfl) ⟨1459799, by rfl⟩ : syracuseStep 1946399 = 2919599) B2919599
theorem B2919605 : Blo 1945435 2919605 := bbase (se 5 (by rfl) ⟨136856, by rfl⟩ : syracuseStep 2919605 = 273713) (by norm_num)
theorem B1946403 : Blo 1945435 1946403 := bstep (se 1 (by rfl) ⟨1459802, by rfl⟩ : syracuseStep 1946403 = 2919605) B2919605
theorem B4926845 : Blo 1945435 4926845 := bbase (se 3 (by rfl) ⟨923783, by rfl⟩ : syracuseStep 4926845 = 1847567) (by norm_num)
theorem B3284563 : Blo 1945435 3284563 := bstep (se 1 (by rfl) ⟨2463422, by rfl⟩ : syracuseStep 3284563 = 4926845) B4926845
theorem B4379417 : Blo 1945435 4379417 := bstep (se 2 (by rfl) ⟨1642281, by rfl⟩ : syracuseStep 4379417 = 3284563) B3284563
theorem B2919611 : Blo 1945435 2919611 := bstep (se 1 (by rfl) ⟨2189708, by rfl⟩ : syracuseStep 2919611 = 4379417) B4379417
theorem B1946407 : Blo 1945435 1946407 := bstep (se 1 (by rfl) ⟨1459805, by rfl⟩ : syracuseStep 1946407 = 2919611) B2919611
theorem B2189713 : Blo 1945435 2189713 := bbase (se 2 (by rfl) ⟨821142, by rfl⟩ : syracuseStep 2189713 = 1642285) (by norm_num)
theorem B2919617 : Blo 1945435 2919617 := bstep (se 2 (by rfl) ⟨1094856, by rfl⟩ : syracuseStep 2919617 = 2189713) B2189713
theorem B1946411 : Blo 1945435 1946411 := bstep (se 1 (by rfl) ⟨1459808, by rfl⟩ : syracuseStep 1946411 = 2919617) B2919617
theorem B3695149 : Blo 1945435 3695149 := bbase (se 3 (by rfl) ⟨692840, by rfl⟩ : syracuseStep 3695149 = 1385681) (by norm_num)
theorem B4926865 : Blo 1945435 4926865 := bstep (se 2 (by rfl) ⟨1847574, by rfl⟩ : syracuseStep 4926865 = 3695149) B3695149
theorem B6569153 : Blo 1945435 6569153 := bstep (se 2 (by rfl) ⟨2463432, by rfl⟩ : syracuseStep 6569153 = 4926865) B4926865
theorem B4379435 : Blo 1945435 4379435 := bstep (se 1 (by rfl) ⟨3284576, by rfl⟩ : syracuseStep 4379435 = 6569153) B6569153
theorem B2919623 : Blo 1945435 2919623 := bstep (se 1 (by rfl) ⟨2189717, by rfl⟩ : syracuseStep 2919623 = 4379435) B4379435
theorem B1946415 : Blo 1945435 1946415 := bstep (se 1 (by rfl) ⟨1459811, by rfl⟩ : syracuseStep 1946415 = 2919623) B2919623
theorem B2919629 : Blo 1945435 2919629 := bbase (se 3 (by rfl) ⟨547430, by rfl⟩ : syracuseStep 2919629 = 1094861) (by norm_num)
theorem B1946419 : Blo 1945435 1946419 := bstep (se 1 (by rfl) ⟨1459814, by rfl⟩ : syracuseStep 1946419 = 2919629) B2919629
theorem B4379453 : Blo 1945435 4379453 := bbase (se 3 (by rfl) ⟨821147, by rfl⟩ : syracuseStep 4379453 = 1642295) (by norm_num)
theorem B2919635 : Blo 1945435 2919635 := bstep (se 1 (by rfl) ⟨2189726, by rfl⟩ : syracuseStep 2919635 = 4379453) B4379453
theorem B1946423 : Blo 1945435 1946423 := bstep (se 1 (by rfl) ⟨1459817, by rfl⟩ : syracuseStep 1946423 = 2919635) B2919635
theorem B3284597 : Blo 1945435 3284597 := bbase (se 5 (by rfl) ⟨153965, by rfl⟩ : syracuseStep 3284597 = 307931) (by norm_num)
theorem B2189731 : Blo 1945435 2189731 := bstep (se 1 (by rfl) ⟨1642298, by rfl⟩ : syracuseStep 2189731 = 3284597) B3284597
theorem B2919641 : Blo 1945435 2919641 := bstep (se 2 (by rfl) ⟨1094865, by rfl⟩ : syracuseStep 2919641 = 2189731) B2189731
theorem B1946427 : Blo 1945435 1946427 := bstep (se 1 (by rfl) ⟨1459820, by rfl⟩ : syracuseStep 1946427 = 2919641) B2919641
theorem B4157077 : Blo 1945435 4157077 := bbase (se 6 (by rfl) ⟨97431, by rfl⟩ : syracuseStep 4157077 = 194863) (by norm_num)
theorem B5542769 : Blo 1945435 5542769 := bstep (se 2 (by rfl) ⟨2078538, by rfl⟩ : syracuseStep 5542769 = 4157077) B4157077
theorem B14780717 : Blo 1945435 14780717 := bstep (se 3 (by rfl) ⟨2771384, by rfl⟩ : syracuseStep 14780717 = 5542769) B5542769
theorem B9853811 : Blo 1945435 9853811 := bstep (se 1 (by rfl) ⟨7390358, by rfl⟩ : syracuseStep 9853811 = 14780717) B14780717
theorem B6569207 : Blo 1945435 6569207 := bstep (se 1 (by rfl) ⟨4926905, by rfl⟩ : syracuseStep 6569207 = 9853811) B9853811
theorem B4379471 : Blo 1945435 4379471 := bstep (se 1 (by rfl) ⟨3284603, by rfl⟩ : syracuseStep 4379471 = 6569207) B6569207
theorem B2919647 : Blo 1945435 2919647 := bstep (se 1 (by rfl) ⟨2189735, by rfl⟩ : syracuseStep 2919647 = 4379471) B4379471
theorem B1946431 : Blo 1945435 1946431 := bstep (se 1 (by rfl) ⟨1459823, by rfl⟩ : syracuseStep 1946431 = 2919647) B2919647
theorem B2919653 : Blo 1945435 2919653 := bbase (se 4 (by rfl) ⟨273717, by rfl⟩ : syracuseStep 2919653 = 547435) (by norm_num)
theorem B1946435 : Blo 1945435 1946435 := bstep (se 1 (by rfl) ⟨1459826, by rfl⟩ : syracuseStep 1946435 = 2919653) B2919653
theorem B4994149 : Blo 1945435 4994149 := bbase (se 4 (by rfl) ⟨468201, by rfl⟩ : syracuseStep 4994149 = 936403) (by norm_num)
theorem B6658865 : Blo 1945435 6658865 := bstep (se 2 (by rfl) ⟨2497074, by rfl⟩ : syracuseStep 6658865 = 4994149) B4994149
theorem B4439243 : Blo 1945435 4439243 := bstep (se 1 (by rfl) ⟨3329432, by rfl⟩ : syracuseStep 4439243 = 6658865) B6658865
theorem B11837981 : Blo 1945435 11837981 := bstep (se 3 (by rfl) ⟨2219621, by rfl⟩ : syracuseStep 11837981 = 4439243) B4439243
theorem B7891987 : Blo 1945435 7891987 := bstep (se 1 (by rfl) ⟨5918990, by rfl⟩ : syracuseStep 7891987 = 11837981) B11837981
theorem B10522649 : Blo 1945435 10522649 := bstep (se 2 (by rfl) ⟨3945993, by rfl⟩ : syracuseStep 10522649 = 7891987) B7891987
theorem B7015099 : Blo 1945435 7015099 := bstep (se 1 (by rfl) ⟨5261324, by rfl⟩ : syracuseStep 7015099 = 10522649) B10522649
theorem B9353465 : Blo 1945435 9353465 := bstep (se 2 (by rfl) ⟨3507549, by rfl⟩ : syracuseStep 9353465 = 7015099) B7015099
theorem B6235643 : Blo 1945435 6235643 := bstep (se 1 (by rfl) ⟨4676732, by rfl⟩ : syracuseStep 6235643 = 9353465) B9353465
theorem B4157095 : Blo 1945435 4157095 := bstep (se 1 (by rfl) ⟨3117821, by rfl⟩ : syracuseStep 4157095 = 6235643) B6235643
theorem B5542793 : Blo 1945435 5542793 := bstep (se 2 (by rfl) ⟨2078547, by rfl⟩ : syracuseStep 5542793 = 4157095) B4157095
theorem B3695195 : Blo 1945435 3695195 := bstep (se 1 (by rfl) ⟨2771396, by rfl⟩ : syracuseStep 3695195 = 5542793) B5542793
theorem B2463463 : Blo 1945435 2463463 := bstep (se 1 (by rfl) ⟨1847597, by rfl⟩ : syracuseStep 2463463 = 3695195) B3695195
theorem B3284617 : Blo 1945435 3284617 := bstep (se 2 (by rfl) ⟨1231731, by rfl⟩ : syracuseStep 3284617 = 2463463) B2463463
theorem B4379489 : Blo 1945435 4379489 := bstep (se 2 (by rfl) ⟨1642308, by rfl⟩ : syracuseStep 4379489 = 3284617) B3284617
theorem B2919659 : Blo 1945435 2919659 := bstep (se 1 (by rfl) ⟨2189744, by rfl⟩ : syracuseStep 2919659 = 4379489) B4379489
theorem B1946439 : Blo 1945435 1946439 := bstep (se 1 (by rfl) ⟨1459829, by rfl⟩ : syracuseStep 1946439 = 2919659) B2919659
theorem B2189749 : Blo 1945435 2189749 := bbase (se 5 (by rfl) ⟨102644, by rfl⟩ : syracuseStep 2189749 = 205289) (by norm_num)
theorem B2919665 : Blo 1945435 2919665 := bstep (se 2 (by rfl) ⟨1094874, by rfl⟩ : syracuseStep 2919665 = 2189749) B2189749
theorem B1946443 : Blo 1945435 1946443 := bstep (se 1 (by rfl) ⟨1459832, by rfl⟩ : syracuseStep 1946443 = 2919665) B2919665
theorem B2463473 : Blo 1945435 2463473 := bbase (se 2 (by rfl) ⟨923802, by rfl⟩ : syracuseStep 2463473 = 1847605) (by norm_num)
theorem B6569261 : Blo 1945435 6569261 := bstep (se 3 (by rfl) ⟨1231736, by rfl⟩ : syracuseStep 6569261 = 2463473) B2463473
theorem B4379507 : Blo 1945435 4379507 := bstep (se 1 (by rfl) ⟨3284630, by rfl⟩ : syracuseStep 4379507 = 6569261) B6569261
theorem B2919671 : Blo 1945435 2919671 := bstep (se 1 (by rfl) ⟨2189753, by rfl⟩ : syracuseStep 2919671 = 4379507) B4379507
theorem B1946447 : Blo 1945435 1946447 := bstep (se 1 (by rfl) ⟨1459835, by rfl⟩ : syracuseStep 1946447 = 2919671) B2919671
theorem B2919677 : Blo 1945435 2919677 := bbase (se 3 (by rfl) ⟨547439, by rfl⟩ : syracuseStep 2919677 = 1094879) (by norm_num)
theorem B1946451 : Blo 1945435 1946451 := bstep (se 1 (by rfl) ⟨1459838, by rfl⟩ : syracuseStep 1946451 = 2919677) B2919677
theorem B4379525 : Blo 1945435 4379525 := bbase (se 4 (by rfl) ⟨410580, by rfl⟩ : syracuseStep 4379525 = 821161) (by norm_num)
theorem B2919683 : Blo 1945435 2919683 := bstep (se 1 (by rfl) ⟨2189762, by rfl⟩ : syracuseStep 2919683 = 4379525) B4379525
theorem B1946455 : Blo 1945435 1946455 := bstep (se 1 (by rfl) ⟨1459841, by rfl⟩ : syracuseStep 1946455 = 2919683) B2919683
theorem B2078569 : Blo 1945435 2078569 := bbase (se 2 (by rfl) ⟨779463, by rfl⟩ : syracuseStep 2078569 = 1558927) (by norm_num)
theorem B2771425 : Blo 1945435 2771425 := bstep (se 2 (by rfl) ⟨1039284, by rfl⟩ : syracuseStep 2771425 = 2078569) B2078569
theorem B3695233 : Blo 1945435 3695233 := bstep (se 2 (by rfl) ⟨1385712, by rfl⟩ : syracuseStep 3695233 = 2771425) B2771425
theorem B4926977 : Blo 1945435 4926977 := bstep (se 2 (by rfl) ⟨1847616, by rfl⟩ : syracuseStep 4926977 = 3695233) B3695233
theorem B3284651 : Blo 1945435 3284651 := bstep (se 1 (by rfl) ⟨2463488, by rfl⟩ : syracuseStep 3284651 = 4926977) B4926977
theorem B2189767 : Blo 1945435 2189767 := bstep (se 1 (by rfl) ⟨1642325, by rfl⟩ : syracuseStep 2189767 = 3284651) B3284651
theorem B2919689 : Blo 1945435 2919689 := bstep (se 2 (by rfl) ⟨1094883, by rfl⟩ : syracuseStep 2919689 = 2189767) B2189767
theorem B1946459 : Blo 1945435 1946459 := bstep (se 1 (by rfl) ⟨1459844, by rfl⟩ : syracuseStep 1946459 = 2919689) B2919689
theorem B9853973 : Blo 1945435 9853973 := bbase (se 6 (by rfl) ⟨230952, by rfl⟩ : syracuseStep 9853973 = 461905) (by norm_num)
theorem B6569315 : Blo 1945435 6569315 := bstep (se 1 (by rfl) ⟨4926986, by rfl⟩ : syracuseStep 6569315 = 9853973) B9853973
theorem B4379543 : Blo 1945435 4379543 := bstep (se 1 (by rfl) ⟨3284657, by rfl⟩ : syracuseStep 4379543 = 6569315) B6569315
theorem B2919695 : Blo 1945435 2919695 := bstep (se 1 (by rfl) ⟨2189771, by rfl⟩ : syracuseStep 2919695 = 4379543) B4379543
theorem B1946463 : Blo 1945435 1946463 := bstep (se 1 (by rfl) ⟨1459847, by rfl⟩ : syracuseStep 1946463 = 2919695) B2919695
theorem B2919701 : Blo 1945435 2919701 := bbase (se 6 (by rfl) ⟨68430, by rfl⟩ : syracuseStep 2919701 = 136861) (by norm_num)
theorem B1946467 : Blo 1945435 1946467 := bstep (se 1 (by rfl) ⟨1459850, by rfl⟩ : syracuseStep 1946467 = 2919701) B2919701
theorem B1999949 : Blo 1945435 1999949 := bbase (se 3 (by rfl) ⟨374990, by rfl⟩ : syracuseStep 1999949 = 749981) (by norm_num)
theorem B5333197 : Blo 1945435 5333197 := bstep (se 3 (by rfl) ⟨999974, by rfl⟩ : syracuseStep 5333197 = 1999949) B1999949
theorem B7110929 : Blo 1945435 7110929 := bstep (se 2 (by rfl) ⟨2666598, by rfl⟩ : syracuseStep 7110929 = 5333197) B5333197
theorem B4740619 : Blo 1945435 4740619 := bstep (se 1 (by rfl) ⟨3555464, by rfl⟩ : syracuseStep 4740619 = 7110929) B7110929
theorem B6320825 : Blo 1945435 6320825 := bstep (se 2 (by rfl) ⟨2370309, by rfl⟩ : syracuseStep 6320825 = 4740619) B4740619
theorem B4213883 : Blo 1945435 4213883 := bstep (se 1 (by rfl) ⟨3160412, by rfl⟩ : syracuseStep 4213883 = 6320825) B6320825
theorem B2809255 : Blo 1945435 2809255 := bstep (se 1 (by rfl) ⟨2106941, by rfl⟩ : syracuseStep 2809255 = 4213883) B4213883
theorem B3745673 : Blo 1945435 3745673 := bstep (se 2 (by rfl) ⟨1404627, by rfl⟩ : syracuseStep 3745673 = 2809255) B2809255
theorem B2497115 : Blo 1945435 2497115 := bstep (se 1 (by rfl) ⟨1872836, by rfl⟩ : syracuseStep 2497115 = 3745673) B3745673
theorem B6658973 : Blo 1945435 6658973 := bstep (se 3 (by rfl) ⟨1248557, by rfl⟩ : syracuseStep 6658973 = 2497115) B2497115
theorem B4439315 : Blo 1945435 4439315 := bstep (se 1 (by rfl) ⟨3329486, by rfl⟩ : syracuseStep 4439315 = 6658973) B6658973
theorem B2959543 : Blo 1945435 2959543 := bstep (se 1 (by rfl) ⟨2219657, by rfl⟩ : syracuseStep 2959543 = 4439315) B4439315
theorem B15784229 : Blo 1945435 15784229 := bstep (se 4 (by rfl) ⟨1479771, by rfl⟩ : syracuseStep 15784229 = 2959543) B2959543
theorem B10522819 : Blo 1945435 10522819 := bstep (se 1 (by rfl) ⟨7892114, by rfl⟩ : syracuseStep 10522819 = 15784229) B15784229
theorem B14030425 : Blo 1945435 14030425 := bstep (se 2 (by rfl) ⟨5261409, by rfl⟩ : syracuseStep 14030425 = 10522819) B10522819
theorem B18707233 : Blo 1945435 18707233 := bstep (se 2 (by rfl) ⟨7015212, by rfl⟩ : syracuseStep 18707233 = 14030425) B14030425
theorem B24942977 : Blo 1945435 24942977 := bstep (se 2 (by rfl) ⟨9353616, by rfl⟩ : syracuseStep 24942977 = 18707233) B18707233
theorem B16628651 : Blo 1945435 16628651 := bstep (se 1 (by rfl) ⟨12471488, by rfl⟩ : syracuseStep 16628651 = 24942977) B24942977
theorem B11085767 : Blo 1945435 11085767 := bstep (se 1 (by rfl) ⟨8314325, by rfl⟩ : syracuseStep 11085767 = 16628651) B16628651
theorem B7390511 : Blo 1945435 7390511 := bstep (se 1 (by rfl) ⟨5542883, by rfl⟩ : syracuseStep 7390511 = 11085767) B11085767
theorem B4927007 : Blo 1945435 4927007 := bstep (se 1 (by rfl) ⟨3695255, by rfl⟩ : syracuseStep 4927007 = 7390511) B7390511
theorem B3284671 : Blo 1945435 3284671 := bstep (se 1 (by rfl) ⟨2463503, by rfl⟩ : syracuseStep 3284671 = 4927007) B4927007
theorem B4379561 : Blo 1945435 4379561 := bstep (se 2 (by rfl) ⟨1642335, by rfl⟩ : syracuseStep 4379561 = 3284671) B3284671
theorem B2919707 : Blo 1945435 2919707 := bstep (se 1 (by rfl) ⟨2189780, by rfl⟩ : syracuseStep 2919707 = 4379561) B4379561
theorem B1946471 : Blo 1945435 1946471 := bstep (se 1 (by rfl) ⟨1459853, by rfl⟩ : syracuseStep 1946471 = 2919707) B2919707
theorem B2189785 : Blo 1945435 2189785 := bbase (se 2 (by rfl) ⟨821169, by rfl⟩ : syracuseStep 2189785 = 1642339) (by norm_num)
theorem B2919713 : Blo 1945435 2919713 := bstep (se 2 (by rfl) ⟨1094892, by rfl⟩ : syracuseStep 2919713 = 2189785) B2189785
theorem B1946475 : Blo 1945435 1946475 := bstep (se 1 (by rfl) ⟨1459856, by rfl⟩ : syracuseStep 1946475 = 2919713) B2919713
theorem B2771453 : Blo 1945435 2771453 := bbase (se 3 (by rfl) ⟨519647, by rfl⟩ : syracuseStep 2771453 = 1039295) (by norm_num)
theorem B7390541 : Blo 1945435 7390541 := bstep (se 3 (by rfl) ⟨1385726, by rfl⟩ : syracuseStep 7390541 = 2771453) B2771453
theorem B4927027 : Blo 1945435 4927027 := bstep (se 1 (by rfl) ⟨3695270, by rfl⟩ : syracuseStep 4927027 = 7390541) B7390541
theorem B6569369 : Blo 1945435 6569369 := bstep (se 2 (by rfl) ⟨2463513, by rfl⟩ : syracuseStep 6569369 = 4927027) B4927027
theorem B4379579 : Blo 1945435 4379579 := bstep (se 1 (by rfl) ⟨3284684, by rfl⟩ : syracuseStep 4379579 = 6569369) B6569369
theorem B2919719 : Blo 1945435 2919719 := bstep (se 1 (by rfl) ⟨2189789, by rfl⟩ : syracuseStep 2919719 = 4379579) B4379579
theorem B1946479 : Blo 1945435 1946479 := bstep (se 1 (by rfl) ⟨1459859, by rfl⟩ : syracuseStep 1946479 = 2919719) B2919719
theorem B2919725 : Blo 1945435 2919725 := bbase (se 3 (by rfl) ⟨547448, by rfl⟩ : syracuseStep 2919725 = 1094897) (by norm_num)
theorem B1946483 : Blo 1945435 1946483 := bstep (se 1 (by rfl) ⟨1459862, by rfl⟩ : syracuseStep 1946483 = 2919725) B2919725
theorem B4379597 : Blo 1945435 4379597 := bbase (se 3 (by rfl) ⟨821174, by rfl⟩ : syracuseStep 4379597 = 1642349) (by norm_num)
theorem B2919731 : Blo 1945435 2919731 := bstep (se 1 (by rfl) ⟨2189798, by rfl⟩ : syracuseStep 2919731 = 4379597) B4379597
theorem B1946487 : Blo 1945435 1946487 := bstep (se 1 (by rfl) ⟨1459865, by rfl⟩ : syracuseStep 1946487 = 2919731) B2919731
theorem B2463529 : Blo 1945435 2463529 := bbase (se 2 (by rfl) ⟨923823, by rfl⟩ : syracuseStep 2463529 = 1847647) (by norm_num)
theorem B3284705 : Blo 1945435 3284705 := bstep (se 2 (by rfl) ⟨1231764, by rfl⟩ : syracuseStep 3284705 = 2463529) B2463529
theorem B2189803 : Blo 1945435 2189803 := bstep (se 1 (by rfl) ⟨1642352, by rfl⟩ : syracuseStep 2189803 = 3284705) B3284705
theorem B2919737 : Blo 1945435 2919737 := bstep (se 2 (by rfl) ⟨1094901, by rfl⟩ : syracuseStep 2919737 = 2189803) B2189803
theorem B1946491 : Blo 1945435 1946491 := bstep (se 1 (by rfl) ⟨1459868, by rfl⟩ : syracuseStep 1946491 = 2919737) B2919737
theorem B1973053 : Blo 1945435 1973053 := bbase (se 3 (by rfl) ⟨369947, by rfl⟩ : syracuseStep 1973053 = 739895) (by norm_num)
theorem B2630737 : Blo 1945435 2630737 := bstep (se 2 (by rfl) ⟨986526, by rfl⟩ : syracuseStep 2630737 = 1973053) B1973053
theorem B14030597 : Blo 1945435 14030597 := bstep (se 4 (by rfl) ⟨1315368, by rfl⟩ : syracuseStep 14030597 = 2630737) B2630737
theorem B9353731 : Blo 1945435 9353731 := bstep (se 1 (by rfl) ⟨7015298, by rfl⟩ : syracuseStep 9353731 = 14030597) B14030597
theorem B12471641 : Blo 1945435 12471641 := bstep (se 2 (by rfl) ⟨4676865, by rfl⟩ : syracuseStep 12471641 = 9353731) B9353731
theorem B8314427 : Blo 1945435 8314427 := bstep (se 1 (by rfl) ⟨6235820, by rfl⟩ : syracuseStep 8314427 = 12471641) B12471641
theorem B22171805 : Blo 1945435 22171805 := bstep (se 3 (by rfl) ⟨4157213, by rfl⟩ : syracuseStep 22171805 = 8314427) B8314427
theorem B14781203 : Blo 1945435 14781203 := bstep (se 1 (by rfl) ⟨11085902, by rfl⟩ : syracuseStep 14781203 = 22171805) B22171805
theorem B9854135 : Blo 1945435 9854135 := bstep (se 1 (by rfl) ⟨7390601, by rfl⟩ : syracuseStep 9854135 = 14781203) B14781203
theorem B6569423 : Blo 1945435 6569423 := bstep (se 1 (by rfl) ⟨4927067, by rfl⟩ : syracuseStep 6569423 = 9854135) B9854135
theorem B4379615 : Blo 1945435 4379615 := bstep (se 1 (by rfl) ⟨3284711, by rfl⟩ : syracuseStep 4379615 = 6569423) B6569423
theorem B2919743 : Blo 1945435 2919743 := bstep (se 1 (by rfl) ⟨2189807, by rfl⟩ : syracuseStep 2919743 = 4379615) B4379615
theorem B1946495 : Blo 1945435 1946495 := bstep (se 1 (by rfl) ⟨1459871, by rfl⟩ : syracuseStep 1946495 = 2919743) B2919743
theorem B2919749 : Blo 1945435 2919749 := bbase (se 4 (by rfl) ⟨273726, by rfl⟩ : syracuseStep 2919749 = 547453) (by norm_num)
theorem B1946499 : Blo 1945435 1946499 := bstep (se 1 (by rfl) ⟨1459874, by rfl⟩ : syracuseStep 1946499 = 2919749) B2919749
theorem B3284725 : Blo 1945435 3284725 := bbase (se 5 (by rfl) ⟨153971, by rfl⟩ : syracuseStep 3284725 = 307943) (by norm_num)
theorem B4379633 : Blo 1945435 4379633 := bstep (se 2 (by rfl) ⟨1642362, by rfl⟩ : syracuseStep 4379633 = 3284725) B3284725
theorem B2919755 : Blo 1945435 2919755 := bstep (se 1 (by rfl) ⟨2189816, by rfl⟩ : syracuseStep 2919755 = 4379633) B4379633
theorem B1946503 : Blo 1945435 1946503 := bstep (se 1 (by rfl) ⟨1459877, by rfl⟩ : syracuseStep 1946503 = 2919755) B2919755
theorem B2189821 : Blo 1945435 2189821 := bbase (se 3 (by rfl) ⟨410591, by rfl⟩ : syracuseStep 2189821 = 821183) (by norm_num)
theorem B2919761 : Blo 1945435 2919761 := bstep (se 2 (by rfl) ⟨1094910, by rfl⟩ : syracuseStep 2919761 = 2189821) B2189821
theorem B1946507 : Blo 1945435 1946507 := bstep (se 1 (by rfl) ⟨1459880, by rfl⟩ : syracuseStep 1946507 = 2919761) B2919761
theorem B6569477 : Blo 1945435 6569477 := bbase (se 4 (by rfl) ⟨615888, by rfl⟩ : syracuseStep 6569477 = 1231777) (by norm_num)
theorem B4379651 : Blo 1945435 4379651 := bstep (se 1 (by rfl) ⟨3284738, by rfl⟩ : syracuseStep 4379651 = 6569477) B6569477
theorem B2919767 : Blo 1945435 2919767 := bstep (se 1 (by rfl) ⟨2189825, by rfl⟩ : syracuseStep 2919767 = 4379651) B4379651
theorem B1946511 : Blo 1945435 1946511 := bstep (se 1 (by rfl) ⟨1459883, by rfl⟩ : syracuseStep 1946511 = 2919767) B2919767
theorem B2919773 : Blo 1945435 2919773 := bbase (se 3 (by rfl) ⟨547457, by rfl⟩ : syracuseStep 2919773 = 1094915) (by norm_num)
theorem B1946515 : Blo 1945435 1946515 := bstep (se 1 (by rfl) ⟨1459886, by rfl⟩ : syracuseStep 1946515 = 2919773) B2919773
theorem B4379669 : Blo 1945435 4379669 := bbase (se 6 (by rfl) ⟨102648, by rfl⟩ : syracuseStep 4379669 = 205297) (by norm_num)
theorem B2919779 : Blo 1945435 2919779 := bstep (se 1 (by rfl) ⟨2189834, by rfl⟩ : syracuseStep 2919779 = 4379669) B4379669
theorem B1946519 : Blo 1945435 1946519 := bstep (se 1 (by rfl) ⟨1459889, by rfl⟩ : syracuseStep 1946519 = 2919779) B2919779
theorem B7390709 : Blo 1945435 7390709 := bbase (se 5 (by rfl) ⟨346439, by rfl⟩ : syracuseStep 7390709 = 692879) (by norm_num)
theorem B4927139 : Blo 1945435 4927139 := bstep (se 1 (by rfl) ⟨3695354, by rfl⟩ : syracuseStep 4927139 = 7390709) B7390709
theorem B3284759 : Blo 1945435 3284759 := bstep (se 1 (by rfl) ⟨2463569, by rfl⟩ : syracuseStep 3284759 = 4927139) B4927139
theorem B2189839 : Blo 1945435 2189839 := bstep (se 1 (by rfl) ⟨1642379, by rfl⟩ : syracuseStep 2189839 = 3284759) B3284759
theorem B2919785 : Blo 1945435 2919785 := bstep (se 2 (by rfl) ⟨1094919, by rfl⟩ : syracuseStep 2919785 = 2189839) B2189839
theorem B1946523 : Blo 1945435 1946523 := bstep (se 1 (by rfl) ⟨1459892, by rfl⟩ : syracuseStep 1946523 = 2919785) B2919785
theorem B2078641 : Blo 1945435 2078641 := bbase (se 2 (by rfl) ⟨779490, by rfl⟩ : syracuseStep 2078641 = 1558981) (by norm_num)
theorem B11086085 : Blo 1945435 11086085 := bstep (se 4 (by rfl) ⟨1039320, by rfl⟩ : syracuseStep 11086085 = 2078641) B2078641
theorem B7390723 : Blo 1945435 7390723 := bstep (se 1 (by rfl) ⟨5543042, by rfl⟩ : syracuseStep 7390723 = 11086085) B11086085
theorem B9854297 : Blo 1945435 9854297 := bstep (se 2 (by rfl) ⟨3695361, by rfl⟩ : syracuseStep 9854297 = 7390723) B7390723
theorem B6569531 : Blo 1945435 6569531 := bstep (se 1 (by rfl) ⟨4927148, by rfl⟩ : syracuseStep 6569531 = 9854297) B9854297
theorem B4379687 : Blo 1945435 4379687 := bstep (se 1 (by rfl) ⟨3284765, by rfl⟩ : syracuseStep 4379687 = 6569531) B6569531
theorem B2919791 : Blo 1945435 2919791 := bstep (se 1 (by rfl) ⟨2189843, by rfl⟩ : syracuseStep 2919791 = 4379687) B4379687
theorem B1946527 : Blo 1945435 1946527 := bstep (se 1 (by rfl) ⟨1459895, by rfl⟩ : syracuseStep 1946527 = 2919791) B2919791
theorem B2919797 : Blo 1945435 2919797 := bbase (se 5 (by rfl) ⟨136865, by rfl⟩ : syracuseStep 2919797 = 273731) (by norm_num)
theorem B1946531 : Blo 1945435 1946531 := bstep (se 1 (by rfl) ⟨1459898, by rfl⟩ : syracuseStep 1946531 = 2919797) B2919797
theorem B2771533 : Blo 1945435 2771533 := bbase (se 3 (by rfl) ⟨519662, by rfl⟩ : syracuseStep 2771533 = 1039325) (by norm_num)
theorem B3695377 : Blo 1945435 3695377 := bstep (se 2 (by rfl) ⟨1385766, by rfl⟩ : syracuseStep 3695377 = 2771533) B2771533
theorem B4927169 : Blo 1945435 4927169 := bstep (se 2 (by rfl) ⟨1847688, by rfl⟩ : syracuseStep 4927169 = 3695377) B3695377
theorem B3284779 : Blo 1945435 3284779 := bstep (se 1 (by rfl) ⟨2463584, by rfl⟩ : syracuseStep 3284779 = 4927169) B4927169
theorem B4379705 : Blo 1945435 4379705 := bstep (se 2 (by rfl) ⟨1642389, by rfl⟩ : syracuseStep 4379705 = 3284779) B3284779
theorem B2919803 : Blo 1945435 2919803 := bstep (se 1 (by rfl) ⟨2189852, by rfl⟩ : syracuseStep 2919803 = 4379705) B4379705
theorem B1946535 : Blo 1945435 1946535 := bstep (se 1 (by rfl) ⟨1459901, by rfl⟩ : syracuseStep 1946535 = 2919803) B2919803
theorem B2189857 : Blo 1945435 2189857 := bbase (se 2 (by rfl) ⟨821196, by rfl⟩ : syracuseStep 2189857 = 1642393) (by norm_num)
theorem B2919809 : Blo 1945435 2919809 := bstep (se 2 (by rfl) ⟨1094928, by rfl⟩ : syracuseStep 2919809 = 2189857) B2189857
theorem B1946539 : Blo 1945435 1946539 := bstep (se 1 (by rfl) ⟨1459904, by rfl⟩ : syracuseStep 1946539 = 2919809) B2919809
theorem B4927189 : Blo 1945435 4927189 := bbase (se 7 (by rfl) ⟨57740, by rfl⟩ : syracuseStep 4927189 = 115481) (by norm_num)
theorem B6569585 : Blo 1945435 6569585 := bstep (se 2 (by rfl) ⟨2463594, by rfl⟩ : syracuseStep 6569585 = 4927189) B4927189
theorem B4379723 : Blo 1945435 4379723 := bstep (se 1 (by rfl) ⟨3284792, by rfl⟩ : syracuseStep 4379723 = 6569585) B6569585
theorem B2919815 : Blo 1945435 2919815 := bstep (se 1 (by rfl) ⟨2189861, by rfl⟩ : syracuseStep 2919815 = 4379723) B4379723
theorem B1946543 : Blo 1945435 1946543 := bstep (se 1 (by rfl) ⟨1459907, by rfl⟩ : syracuseStep 1946543 = 2919815) B2919815
theorem B2919821 : Blo 1945435 2919821 := bbase (se 3 (by rfl) ⟨547466, by rfl⟩ : syracuseStep 2919821 = 1094933) (by norm_num)
theorem B1946547 : Blo 1945435 1946547 := bstep (se 1 (by rfl) ⟨1459910, by rfl⟩ : syracuseStep 1946547 = 2919821) B2919821
theorem B4379741 : Blo 1945435 4379741 := bbase (se 3 (by rfl) ⟨821201, by rfl⟩ : syracuseStep 4379741 = 1642403) (by norm_num)
theorem B2919827 : Blo 1945435 2919827 := bstep (se 1 (by rfl) ⟨2189870, by rfl⟩ : syracuseStep 2919827 = 4379741) B4379741
theorem B1946551 : Blo 1945435 1946551 := bstep (se 1 (by rfl) ⟨1459913, by rfl⟩ : syracuseStep 1946551 = 2919827) B2919827
theorem B3284813 : Blo 1945435 3284813 := bbase (se 3 (by rfl) ⟨615902, by rfl⟩ : syracuseStep 3284813 = 1231805) (by norm_num)
theorem B2189875 : Blo 1945435 2189875 := bstep (se 1 (by rfl) ⟨1642406, by rfl⟩ : syracuseStep 2189875 = 3284813) B3284813
theorem B2919833 : Blo 1945435 2919833 := bstep (se 2 (by rfl) ⟨1094937, by rfl⟩ : syracuseStep 2919833 = 2189875) B2189875
theorem B1946555 : Blo 1945435 1946555 := bstep (se 1 (by rfl) ⟨1459916, by rfl⟩ : syracuseStep 1946555 = 2919833) B2919833
theorem B11237525 : Blo 1945435 11237525 := bbase (se 6 (by rfl) ⟨263379, by rfl⟩ : syracuseStep 11237525 = 526759) (by norm_num)
theorem B7491683 : Blo 1945435 7491683 := bstep (se 1 (by rfl) ⟨5618762, by rfl⟩ : syracuseStep 7491683 = 11237525) B11237525
theorem B4994455 : Blo 1945435 4994455 := bstep (se 1 (by rfl) ⟨3745841, by rfl⟩ : syracuseStep 4994455 = 7491683) B7491683
theorem B6659273 : Blo 1945435 6659273 := bstep (se 2 (by rfl) ⟨2497227, by rfl⟩ : syracuseStep 6659273 = 4994455) B4994455
theorem B17758061 : Blo 1945435 17758061 := bstep (se 3 (by rfl) ⟨3329636, by rfl⟩ : syracuseStep 17758061 = 6659273) B6659273
theorem B11838707 : Blo 1945435 11838707 := bstep (se 1 (by rfl) ⟨8879030, by rfl⟩ : syracuseStep 11838707 = 17758061) B17758061
theorem B7892471 : Blo 1945435 7892471 := bstep (se 1 (by rfl) ⟨5919353, by rfl⟩ : syracuseStep 7892471 = 11838707) B11838707
theorem B5261647 : Blo 1945435 5261647 := bstep (se 1 (by rfl) ⟨3946235, by rfl⟩ : syracuseStep 5261647 = 7892471) B7892471
theorem B7015529 : Blo 1945435 7015529 := bstep (se 2 (by rfl) ⟨2630823, by rfl⟩ : syracuseStep 7015529 = 5261647) B5261647
theorem B18708077 : Blo 1945435 18708077 := bstep (se 3 (by rfl) ⟨3507764, by rfl⟩ : syracuseStep 18708077 = 7015529) B7015529
theorem B12472051 : Blo 1945435 12472051 := bstep (se 1 (by rfl) ⟨9354038, by rfl⟩ : syracuseStep 12472051 = 18708077) B18708077
theorem B16629401 : Blo 1945435 16629401 := bstep (se 2 (by rfl) ⟨6236025, by rfl⟩ : syracuseStep 16629401 = 12472051) B12472051
theorem B11086267 : Blo 1945435 11086267 := bstep (se 1 (by rfl) ⟨8314700, by rfl⟩ : syracuseStep 11086267 = 16629401) B16629401
theorem B14781689 : Blo 1945435 14781689 := bstep (se 2 (by rfl) ⟨5543133, by rfl⟩ : syracuseStep 14781689 = 11086267) B11086267
theorem B9854459 : Blo 1945435 9854459 := bstep (se 1 (by rfl) ⟨7390844, by rfl⟩ : syracuseStep 9854459 = 14781689) B14781689
theorem B6569639 : Blo 1945435 6569639 := bstep (se 1 (by rfl) ⟨4927229, by rfl⟩ : syracuseStep 6569639 = 9854459) B9854459
theorem B4379759 : Blo 1945435 4379759 := bstep (se 1 (by rfl) ⟨3284819, by rfl⟩ : syracuseStep 4379759 = 6569639) B6569639
theorem B2919839 : Blo 1945435 2919839 := bstep (se 1 (by rfl) ⟨2189879, by rfl⟩ : syracuseStep 2919839 = 4379759) B4379759
theorem B1946559 : Blo 1945435 1946559 := bstep (se 1 (by rfl) ⟨1459919, by rfl⟩ : syracuseStep 1946559 = 2919839) B2919839
theorem B2919845 : Blo 1945435 2919845 := bbase (se 4 (by rfl) ⟨273735, by rfl⟩ : syracuseStep 2919845 = 547471) (by norm_num)
theorem B1946563 : Blo 1945435 1946563 := bstep (se 1 (by rfl) ⟨1459922, by rfl⟩ : syracuseStep 1946563 = 2919845) B2919845
theorem B2463625 : Blo 1945435 2463625 := bbase (se 2 (by rfl) ⟨923859, by rfl⟩ : syracuseStep 2463625 = 1847719) (by norm_num)
theorem B3284833 : Blo 1945435 3284833 := bstep (se 2 (by rfl) ⟨1231812, by rfl⟩ : syracuseStep 3284833 = 2463625) B2463625
theorem B4379777 : Blo 1945435 4379777 := bstep (se 2 (by rfl) ⟨1642416, by rfl⟩ : syracuseStep 4379777 = 3284833) B3284833
theorem B2919851 : Blo 1945435 2919851 := bstep (se 1 (by rfl) ⟨2189888, by rfl⟩ : syracuseStep 2919851 = 4379777) B4379777
theorem B1946567 : Blo 1945435 1946567 := bstep (se 1 (by rfl) ⟨1459925, by rfl⟩ : syracuseStep 1946567 = 2919851) B2919851
theorem B2189893 : Blo 1945435 2189893 := bbase (se 4 (by rfl) ⟨205302, by rfl⟩ : syracuseStep 2189893 = 410605) (by norm_num)
theorem B2919857 : Blo 1945435 2919857 := bstep (se 2 (by rfl) ⟨1094946, by rfl⟩ : syracuseStep 2919857 = 2189893) B2189893
theorem B1946571 : Blo 1945435 1946571 := bstep (se 1 (by rfl) ⟨1459928, by rfl⟩ : syracuseStep 1946571 = 2919857) B2919857
theorem B3695453 : Blo 1945435 3695453 := bbase (se 3 (by rfl) ⟨692897, by rfl⟩ : syracuseStep 3695453 = 1385795) (by norm_num)
theorem B2463635 : Blo 1945435 2463635 := bstep (se 1 (by rfl) ⟨1847726, by rfl⟩ : syracuseStep 2463635 = 3695453) B3695453
theorem B6569693 : Blo 1945435 6569693 := bstep (se 3 (by rfl) ⟨1231817, by rfl⟩ : syracuseStep 6569693 = 2463635) B2463635
theorem B4379795 : Blo 1945435 4379795 := bstep (se 1 (by rfl) ⟨3284846, by rfl⟩ : syracuseStep 4379795 = 6569693) B6569693
theorem B2919863 : Blo 1945435 2919863 := bstep (se 1 (by rfl) ⟨2189897, by rfl⟩ : syracuseStep 2919863 = 4379795) B4379795
theorem B1946575 : Blo 1945435 1946575 := bstep (se 1 (by rfl) ⟨1459931, by rfl⟩ : syracuseStep 1946575 = 2919863) B2919863
theorem B2919869 : Blo 1945435 2919869 := bbase (se 3 (by rfl) ⟨547475, by rfl⟩ : syracuseStep 2919869 = 1094951) (by norm_num)
theorem B1946579 : Blo 1945435 1946579 := bstep (se 1 (by rfl) ⟨1459934, by rfl⟩ : syracuseStep 1946579 = 2919869) B2919869
theorem B4379813 : Blo 1945435 4379813 := bbase (se 4 (by rfl) ⟨410607, by rfl⟩ : syracuseStep 4379813 = 821215) (by norm_num)
theorem B2919875 : Blo 1945435 2919875 := bstep (se 1 (by rfl) ⟨2189906, by rfl⟩ : syracuseStep 2919875 = 4379813) B4379813
theorem B1946583 : Blo 1945435 1946583 := bstep (se 1 (by rfl) ⟨1459937, by rfl⟩ : syracuseStep 1946583 = 2919875) B2919875
theorem B4927301 : Blo 1945435 4927301 := bbase (se 4 (by rfl) ⟨461934, by rfl⟩ : syracuseStep 4927301 = 923869) (by norm_num)
theorem B3284867 : Blo 1945435 3284867 := bstep (se 1 (by rfl) ⟨2463650, by rfl⟩ : syracuseStep 3284867 = 4927301) B4927301
theorem B2189911 : Blo 1945435 2189911 := bstep (se 1 (by rfl) ⟨1642433, by rfl⟩ : syracuseStep 2189911 = 3284867) B3284867
theorem B2919881 : Blo 1945435 2919881 := bstep (se 2 (by rfl) ⟨1094955, by rfl⟩ : syracuseStep 2919881 = 2189911) B2189911
theorem B1946587 : Blo 1945435 1946587 := bstep (se 1 (by rfl) ⟨1459940, by rfl⟩ : syracuseStep 1946587 = 2919881) B2919881
theorem B9989077 : Blo 1945435 9989077 := bbase (se 7 (by rfl) ⟨117059, by rfl⟩ : syracuseStep 9989077 = 234119) (by norm_num)
theorem B13318769 : Blo 1945435 13318769 := bstep (se 2 (by rfl) ⟨4994538, by rfl⟩ : syracuseStep 13318769 = 9989077) B9989077
theorem B8879179 : Blo 1945435 8879179 := bstep (se 1 (by rfl) ⟨6659384, by rfl⟩ : syracuseStep 8879179 = 13318769) B13318769
theorem B11838905 : Blo 1945435 11838905 := bstep (se 2 (by rfl) ⟨4439589, by rfl⟩ : syracuseStep 11838905 = 8879179) B8879179
theorem B7892603 : Blo 1945435 7892603 := bstep (se 1 (by rfl) ⟨5919452, by rfl⟩ : syracuseStep 7892603 = 11838905) B11838905
theorem B5261735 : Blo 1945435 5261735 := bstep (se 1 (by rfl) ⟨3946301, by rfl⟩ : syracuseStep 5261735 = 7892603) B7892603
theorem B3507823 : Blo 1945435 3507823 := bstep (se 1 (by rfl) ⟨2630867, by rfl⟩ : syracuseStep 3507823 = 5261735) B5261735
theorem B4677097 : Blo 1945435 4677097 := bstep (se 2 (by rfl) ⟨1753911, by rfl⟩ : syracuseStep 4677097 = 3507823) B3507823
theorem B6236129 : Blo 1945435 6236129 := bstep (se 2 (by rfl) ⟨2338548, by rfl⟩ : syracuseStep 6236129 = 4677097) B4677097
theorem B4157419 : Blo 1945435 4157419 := bstep (se 1 (by rfl) ⟨3118064, by rfl⟩ : syracuseStep 4157419 = 6236129) B6236129
theorem B5543225 : Blo 1945435 5543225 := bstep (se 2 (by rfl) ⟨2078709, by rfl⟩ : syracuseStep 5543225 = 4157419) B4157419
theorem B3695483 : Blo 1945435 3695483 := bstep (se 1 (by rfl) ⟨2771612, by rfl⟩ : syracuseStep 3695483 = 5543225) B5543225
theorem B9854621 : Blo 1945435 9854621 := bstep (se 3 (by rfl) ⟨1847741, by rfl⟩ : syracuseStep 9854621 = 3695483) B3695483
theorem B6569747 : Blo 1945435 6569747 := bstep (se 1 (by rfl) ⟨4927310, by rfl⟩ : syracuseStep 6569747 = 9854621) B9854621
theorem B4379831 : Blo 1945435 4379831 := bstep (se 1 (by rfl) ⟨3284873, by rfl⟩ : syracuseStep 4379831 = 6569747) B6569747
theorem B2919887 : Blo 1945435 2919887 := bstep (se 1 (by rfl) ⟨2189915, by rfl⟩ : syracuseStep 2919887 = 4379831) B4379831
theorem B1946591 : Blo 1945435 1946591 := bstep (se 1 (by rfl) ⟨1459943, by rfl⟩ : syracuseStep 1946591 = 2919887) B2919887
theorem B2919893 : Blo 1945435 2919893 := bbase (se 7 (by rfl) ⟨34217, by rfl⟩ : syracuseStep 2919893 = 68435) (by norm_num)
theorem B1946595 : Blo 1945435 1946595 := bstep (se 1 (by rfl) ⟨1459946, by rfl⟩ : syracuseStep 1946595 = 2919893) B2919893
theorem B7390997 : Blo 1945435 7390997 := bbase (se 6 (by rfl) ⟨173226, by rfl⟩ : syracuseStep 7390997 = 346453) (by norm_num)
theorem B4927331 : Blo 1945435 4927331 := bstep (se 1 (by rfl) ⟨3695498, by rfl⟩ : syracuseStep 4927331 = 7390997) B7390997
theorem B3284887 : Blo 1945435 3284887 := bstep (se 1 (by rfl) ⟨2463665, by rfl⟩ : syracuseStep 3284887 = 4927331) B4927331
theorem B4379849 : Blo 1945435 4379849 := bstep (se 2 (by rfl) ⟨1642443, by rfl⟩ : syracuseStep 4379849 = 3284887) B3284887
theorem B2919899 : Blo 1945435 2919899 := bstep (se 1 (by rfl) ⟨2189924, by rfl⟩ : syracuseStep 2919899 = 4379849) B4379849
theorem B1946599 : Blo 1945435 1946599 := bstep (se 1 (by rfl) ⟨1459949, by rfl⟩ : syracuseStep 1946599 = 2919899) B2919899
theorem B2189929 : Blo 1945435 2189929 := bbase (se 2 (by rfl) ⟨821223, by rfl⟩ : syracuseStep 2189929 = 1642447) (by norm_num)
theorem B2919905 : Blo 1945435 2919905 := bstep (se 2 (by rfl) ⟨1094964, by rfl⟩ : syracuseStep 2919905 = 2189929) B2189929
theorem B1946603 : Blo 1945435 1946603 := bstep (se 1 (by rfl) ⟨1459952, by rfl⟩ : syracuseStep 1946603 = 2919905) B2919905
theorem B4157453 : Blo 1945435 4157453 := bbase (se 3 (by rfl) ⟨779522, by rfl⟩ : syracuseStep 4157453 = 1559045) (by norm_num)
theorem B11086541 : Blo 1945435 11086541 := bstep (se 3 (by rfl) ⟨2078726, by rfl⟩ : syracuseStep 11086541 = 4157453) B4157453
theorem B7391027 : Blo 1945435 7391027 := bstep (se 1 (by rfl) ⟨5543270, by rfl⟩ : syracuseStep 7391027 = 11086541) B11086541
theorem B4927351 : Blo 1945435 4927351 := bstep (se 1 (by rfl) ⟨3695513, by rfl⟩ : syracuseStep 4927351 = 7391027) B7391027
theorem B6569801 : Blo 1945435 6569801 := bstep (se 2 (by rfl) ⟨2463675, by rfl⟩ : syracuseStep 6569801 = 4927351) B4927351
theorem B4379867 : Blo 1945435 4379867 := bstep (se 1 (by rfl) ⟨3284900, by rfl⟩ : syracuseStep 4379867 = 6569801) B6569801
theorem B2919911 : Blo 1945435 2919911 := bstep (se 1 (by rfl) ⟨2189933, by rfl⟩ : syracuseStep 2919911 = 4379867) B4379867
theorem B1946607 : Blo 1945435 1946607 := bstep (se 1 (by rfl) ⟨1459955, by rfl⟩ : syracuseStep 1946607 = 2919911) B2919911
theorem B2919917 : Blo 1945435 2919917 := bbase (se 3 (by rfl) ⟨547484, by rfl⟩ : syracuseStep 2919917 = 1094969) (by norm_num)
theorem B1946611 : Blo 1945435 1946611 := bstep (se 1 (by rfl) ⟨1459958, by rfl⟩ : syracuseStep 1946611 = 2919917) B2919917
theorem B4379885 : Blo 1945435 4379885 := bbase (se 3 (by rfl) ⟨821228, by rfl⟩ : syracuseStep 4379885 = 1642457) (by norm_num)
theorem B2919923 : Blo 1945435 2919923 := bstep (se 1 (by rfl) ⟨2189942, by rfl⟩ : syracuseStep 2919923 = 4379885) B4379885
theorem B1946615 : Blo 1945435 1946615 := bstep (se 1 (by rfl) ⟨1459961, by rfl⟩ : syracuseStep 1946615 = 2919923) B2919923
theorem B2771653 : Blo 1945435 2771653 := bbase (se 4 (by rfl) ⟨259842, by rfl⟩ : syracuseStep 2771653 = 519685) (by norm_num)
theorem B3695537 : Blo 1945435 3695537 := bstep (se 2 (by rfl) ⟨1385826, by rfl⟩ : syracuseStep 3695537 = 2771653) B2771653
theorem B2463691 : Blo 1945435 2463691 := bstep (se 1 (by rfl) ⟨1847768, by rfl⟩ : syracuseStep 2463691 = 3695537) B3695537
theorem B3284921 : Blo 1945435 3284921 := bstep (se 2 (by rfl) ⟨1231845, by rfl⟩ : syracuseStep 3284921 = 2463691) B2463691
theorem B2189947 : Blo 1945435 2189947 := bstep (se 1 (by rfl) ⟨1642460, by rfl⟩ : syracuseStep 2189947 = 3284921) B3284921
theorem B2919929 : Blo 1945435 2919929 := bstep (se 2 (by rfl) ⟨1094973, by rfl⟩ : syracuseStep 2919929 = 2189947) B2189947
theorem B1946619 : Blo 1945435 1946619 := bstep (se 1 (by rfl) ⟨1459964, by rfl⟩ : syracuseStep 1946619 = 2919929) B2919929
theorem B9989237 : Blo 1945435 9989237 := bbase (se 5 (by rfl) ⟨468245, by rfl⟩ : syracuseStep 9989237 = 936491) (by norm_num)
theorem B6659491 : Blo 1945435 6659491 := bstep (se 1 (by rfl) ⟨4994618, by rfl⟩ : syracuseStep 6659491 = 9989237) B9989237
theorem B8879321 : Blo 1945435 8879321 := bstep (se 2 (by rfl) ⟨3329745, by rfl⟩ : syracuseStep 8879321 = 6659491) B6659491
theorem B23678189 : Blo 1945435 23678189 := bstep (se 3 (by rfl) ⟨4439660, by rfl⟩ : syracuseStep 23678189 = 8879321) B8879321
theorem B15785459 : Blo 1945435 15785459 := bstep (se 1 (by rfl) ⟨11839094, by rfl⟩ : syracuseStep 15785459 = 23678189) B23678189
theorem B10523639 : Blo 1945435 10523639 := bstep (se 1 (by rfl) ⟨7892729, by rfl⟩ : syracuseStep 10523639 = 15785459) B15785459
theorem B28063037 : Blo 1945435 28063037 := bstep (se 3 (by rfl) ⟨5261819, by rfl⟩ : syracuseStep 28063037 = 10523639) B10523639
theorem B74834765 : Blo 1945435 74834765 := bstep (se 3 (by rfl) ⟨14031518, by rfl⟩ : syracuseStep 74834765 = 28063037) B28063037
theorem B49889843 : Blo 1945435 49889843 := bstep (se 1 (by rfl) ⟨37417382, by rfl⟩ : syracuseStep 49889843 = 74834765) B74834765
theorem B33259895 : Blo 1945435 33259895 := bstep (se 1 (by rfl) ⟨24944921, by rfl⟩ : syracuseStep 33259895 = 49889843) B49889843
theorem B22173263 : Blo 1945435 22173263 := bstep (se 1 (by rfl) ⟨16629947, by rfl⟩ : syracuseStep 22173263 = 33259895) B33259895
theorem B14782175 : Blo 1945435 14782175 := bstep (se 1 (by rfl) ⟨11086631, by rfl⟩ : syracuseStep 14782175 = 22173263) B22173263
theorem B9854783 : Blo 1945435 9854783 := bstep (se 1 (by rfl) ⟨7391087, by rfl⟩ : syracuseStep 9854783 = 14782175) B14782175
theorem B6569855 : Blo 1945435 6569855 := bstep (se 1 (by rfl) ⟨4927391, by rfl⟩ : syracuseStep 6569855 = 9854783) B9854783
theorem B4379903 : Blo 1945435 4379903 := bstep (se 1 (by rfl) ⟨3284927, by rfl⟩ : syracuseStep 4379903 = 6569855) B6569855
theorem B2919935 : Blo 1945435 2919935 := bstep (se 1 (by rfl) ⟨2189951, by rfl⟩ : syracuseStep 2919935 = 4379903) B4379903
theorem B1946623 : Blo 1945435 1946623 := bstep (se 1 (by rfl) ⟨1459967, by rfl⟩ : syracuseStep 1946623 = 2919935) B2919935
theorem B2919941 : Blo 1945435 2919941 := bbase (se 4 (by rfl) ⟨273744, by rfl⟩ : syracuseStep 2919941 = 547489) (by norm_num)
theorem B1946627 : Blo 1945435 1946627 := bstep (se 1 (by rfl) ⟨1459970, by rfl⟩ : syracuseStep 1946627 = 2919941) B2919941
theorem B3284941 : Blo 1945435 3284941 := bbase (se 3 (by rfl) ⟨615926, by rfl⟩ : syracuseStep 3284941 = 1231853) (by norm_num)
theorem B4379921 : Blo 1945435 4379921 := bstep (se 2 (by rfl) ⟨1642470, by rfl⟩ : syracuseStep 4379921 = 3284941) B3284941
theorem B2919947 : Blo 1945435 2919947 := bstep (se 1 (by rfl) ⟨2189960, by rfl⟩ : syracuseStep 2919947 = 4379921) B4379921
theorem B1946631 : Blo 1945435 1946631 := bstep (se 1 (by rfl) ⟨1459973, by rfl⟩ : syracuseStep 1946631 = 2919947) B2919947
theorem B2189965 : Blo 1945435 2189965 := bbase (se 3 (by rfl) ⟨410618, by rfl⟩ : syracuseStep 2189965 = 821237) (by norm_num)
theorem B2919953 : Blo 1945435 2919953 := bstep (se 2 (by rfl) ⟨1094982, by rfl⟩ : syracuseStep 2919953 = 2189965) B2189965
theorem B1946635 : Blo 1945435 1946635 := bstep (se 1 (by rfl) ⟨1459976, by rfl⟩ : syracuseStep 1946635 = 2919953) B2919953
theorem B6569909 : Blo 1945435 6569909 := bbase (se 5 (by rfl) ⟨307964, by rfl⟩ : syracuseStep 6569909 = 615929) (by norm_num)
theorem B4379939 : Blo 1945435 4379939 := bstep (se 1 (by rfl) ⟨3284954, by rfl⟩ : syracuseStep 4379939 = 6569909) B6569909
theorem B2919959 : Blo 1945435 2919959 := bstep (se 1 (by rfl) ⟨2189969, by rfl⟩ : syracuseStep 2919959 = 4379939) B4379939
theorem B1946639 : Blo 1945435 1946639 := bstep (se 1 (by rfl) ⟨1459979, by rfl⟩ : syracuseStep 1946639 = 2919959) B2919959
theorem B2919965 : Blo 1945435 2919965 := bbase (se 3 (by rfl) ⟨547493, by rfl⟩ : syracuseStep 2919965 = 1094987) (by norm_num)
theorem B1946643 : Blo 1945435 1946643 := bstep (se 1 (by rfl) ⟨1459982, by rfl⟩ : syracuseStep 1946643 = 2919965) B2919965
theorem B4379957 : Blo 1945435 4379957 := bbase (se 5 (by rfl) ⟨205310, by rfl⟩ : syracuseStep 4379957 = 410621) (by norm_num)
theorem B2919971 : Blo 1945435 2919971 := bstep (se 1 (by rfl) ⟨2189978, by rfl⟩ : syracuseStep 2919971 = 4379957) B4379957
theorem B1946647 : Blo 1945435 1946647 := bstep (se 1 (by rfl) ⟨1459985, by rfl⟩ : syracuseStep 1946647 = 2919971) B2919971
theorem B4994693 : Blo 1945435 4994693 := bbase (se 4 (by rfl) ⟨468252, by rfl⟩ : syracuseStep 4994693 = 936505) (by norm_num)
theorem B3329795 : Blo 1945435 3329795 := bstep (se 1 (by rfl) ⟨2497346, by rfl⟩ : syracuseStep 3329795 = 4994693) B4994693
theorem B8879453 : Blo 1945435 8879453 := bstep (se 3 (by rfl) ⟨1664897, by rfl⟩ : syracuseStep 8879453 = 3329795) B3329795
theorem B5919635 : Blo 1945435 5919635 := bstep (se 1 (by rfl) ⟨4439726, by rfl⟩ : syracuseStep 5919635 = 8879453) B8879453
theorem B3946423 : Blo 1945435 3946423 := bstep (se 1 (by rfl) ⟨2959817, by rfl⟩ : syracuseStep 3946423 = 5919635) B5919635
theorem B5261897 : Blo 1945435 5261897 := bstep (se 2 (by rfl) ⟨1973211, by rfl⟩ : syracuseStep 5261897 = 3946423) B3946423
theorem B3507931 : Blo 1945435 3507931 := bstep (se 1 (by rfl) ⟨2630948, by rfl⟩ : syracuseStep 3507931 = 5261897) B5261897
theorem B18708965 : Blo 1945435 18708965 := bstep (se 4 (by rfl) ⟨1753965, by rfl⟩ : syracuseStep 18708965 = 3507931) B3507931
theorem B12472643 : Blo 1945435 12472643 := bstep (se 1 (by rfl) ⟨9354482, by rfl⟩ : syracuseStep 12472643 = 18708965) B18708965
theorem B8315095 : Blo 1945435 8315095 := bstep (se 1 (by rfl) ⟨6236321, by rfl⟩ : syracuseStep 8315095 = 12472643) B12472643
theorem B11086793 : Blo 1945435 11086793 := bstep (se 2 (by rfl) ⟨4157547, by rfl⟩ : syracuseStep 11086793 = 8315095) B8315095
theorem B7391195 : Blo 1945435 7391195 := bstep (se 1 (by rfl) ⟨5543396, by rfl⟩ : syracuseStep 7391195 = 11086793) B11086793
theorem B4927463 : Blo 1945435 4927463 := bstep (se 1 (by rfl) ⟨3695597, by rfl⟩ : syracuseStep 4927463 = 7391195) B7391195
theorem B3284975 : Blo 1945435 3284975 := bstep (se 1 (by rfl) ⟨2463731, by rfl⟩ : syracuseStep 3284975 = 4927463) B4927463
theorem B2189983 : Blo 1945435 2189983 := bstep (se 1 (by rfl) ⟨1642487, by rfl⟩ : syracuseStep 2189983 = 3284975) B3284975
theorem B2919977 : Blo 1945435 2919977 := bstep (se 2 (by rfl) ⟨1094991, by rfl⟩ : syracuseStep 2919977 = 2189983) B2189983
theorem B1946651 : Blo 1945435 1946651 := bstep (se 1 (by rfl) ⟨1459988, by rfl⟩ : syracuseStep 1946651 = 2919977) B2919977
theorem B5333701 : Blo 1945435 5333701 := bbase (se 4 (by rfl) ⟨500034, by rfl⟩ : syracuseStep 5333701 = 1000069) (by norm_num)
theorem B7111601 : Blo 1945435 7111601 := bstep (se 2 (by rfl) ⟨2666850, by rfl⟩ : syracuseStep 7111601 = 5333701) B5333701
theorem B4741067 : Blo 1945435 4741067 := bstep (se 1 (by rfl) ⟨3555800, by rfl⟩ : syracuseStep 4741067 = 7111601) B7111601
theorem B3160711 : Blo 1945435 3160711 := bstep (se 1 (by rfl) ⟨2370533, by rfl⟩ : syracuseStep 3160711 = 4741067) B4741067
theorem B4214281 : Blo 1945435 4214281 := bstep (se 2 (by rfl) ⟨1580355, by rfl⟩ : syracuseStep 4214281 = 3160711) B3160711
theorem B5619041 : Blo 1945435 5619041 := bstep (se 2 (by rfl) ⟨2107140, by rfl⟩ : syracuseStep 5619041 = 4214281) B4214281
theorem B3746027 : Blo 1945435 3746027 := bstep (se 1 (by rfl) ⟨2809520, by rfl⟩ : syracuseStep 3746027 = 5619041) B5619041
theorem B2497351 : Blo 1945435 2497351 := bstep (se 1 (by rfl) ⟨1873013, by rfl⟩ : syracuseStep 2497351 = 3746027) B3746027
theorem B3329801 : Blo 1945435 3329801 := bstep (se 2 (by rfl) ⟨1248675, by rfl⟩ : syracuseStep 3329801 = 2497351) B2497351
theorem B2219867 : Blo 1945435 2219867 := bstep (se 1 (by rfl) ⟨1664900, by rfl⟩ : syracuseStep 2219867 = 3329801) B3329801
theorem B23678581 : Blo 1945435 23678581 := bstep (se 5 (by rfl) ⟨1109933, by rfl⟩ : syracuseStep 23678581 = 2219867) B2219867
theorem B31571441 : Blo 1945435 31571441 := bstep (se 2 (by rfl) ⟨11839290, by rfl⟩ : syracuseStep 31571441 = 23678581) B23678581
theorem B21047627 : Blo 1945435 21047627 := bstep (se 1 (by rfl) ⟨15785720, by rfl⟩ : syracuseStep 21047627 = 31571441) B31571441
theorem B14031751 : Blo 1945435 14031751 := bstep (se 1 (by rfl) ⟨10523813, by rfl⟩ : syracuseStep 14031751 = 21047627) B21047627
theorem B18709001 : Blo 1945435 18709001 := bstep (se 2 (by rfl) ⟨7015875, by rfl⟩ : syracuseStep 18709001 = 14031751) B14031751
theorem B12472667 : Blo 1945435 12472667 := bstep (se 1 (by rfl) ⟨9354500, by rfl⟩ : syracuseStep 12472667 = 18709001) B18709001
theorem B8315111 : Blo 1945435 8315111 := bstep (se 1 (by rfl) ⟨6236333, by rfl⟩ : syracuseStep 8315111 = 12472667) B12472667
theorem B5543407 : Blo 1945435 5543407 := bstep (se 1 (by rfl) ⟨4157555, by rfl⟩ : syracuseStep 5543407 = 8315111) B8315111
theorem B7391209 : Blo 1945435 7391209 := bstep (se 2 (by rfl) ⟨2771703, by rfl⟩ : syracuseStep 7391209 = 5543407) B5543407
theorem B9854945 : Blo 1945435 9854945 := bstep (se 2 (by rfl) ⟨3695604, by rfl⟩ : syracuseStep 9854945 = 7391209) B7391209
theorem B6569963 : Blo 1945435 6569963 := bstep (se 1 (by rfl) ⟨4927472, by rfl⟩ : syracuseStep 6569963 = 9854945) B9854945
theorem B4379975 : Blo 1945435 4379975 := bstep (se 1 (by rfl) ⟨3284981, by rfl⟩ : syracuseStep 4379975 = 6569963) B6569963
theorem B2919983 : Blo 1945435 2919983 := bstep (se 1 (by rfl) ⟨2189987, by rfl⟩ : syracuseStep 2919983 = 4379975) B4379975
theorem B1946655 : Blo 1945435 1946655 := bstep (se 1 (by rfl) ⟨1459991, by rfl⟩ : syracuseStep 1946655 = 2919983) B2919983
theorem B2919989 : Blo 1945435 2919989 := bbase (se 5 (by rfl) ⟨136874, by rfl⟩ : syracuseStep 2919989 = 273749) (by norm_num)
theorem B1946659 : Blo 1945435 1946659 := bstep (se 1 (by rfl) ⟨1459994, by rfl⟩ : syracuseStep 1946659 = 2919989) B2919989
theorem B4927493 : Blo 1945435 4927493 := bbase (se 4 (by rfl) ⟨461952, by rfl⟩ : syracuseStep 4927493 = 923905) (by norm_num)
theorem B3284995 : Blo 1945435 3284995 := bstep (se 1 (by rfl) ⟨2463746, by rfl⟩ : syracuseStep 3284995 = 4927493) B4927493
theorem B4379993 : Blo 1945435 4379993 := bstep (se 2 (by rfl) ⟨1642497, by rfl⟩ : syracuseStep 4379993 = 3284995) B3284995
theorem B2919995 : Blo 1945435 2919995 := bstep (se 1 (by rfl) ⟨2189996, by rfl⟩ : syracuseStep 2919995 = 4379993) B4379993
theorem B1946663 : Blo 1945435 1946663 := bstep (se 1 (by rfl) ⟨1459997, by rfl⟩ : syracuseStep 1946663 = 2919995) B2919995
theorem B2190001 : Blo 1945435 2190001 := bbase (se 2 (by rfl) ⟨821250, by rfl⟩ : syracuseStep 2190001 = 1642501) (by norm_num)
theorem B2920001 : Blo 1945435 2920001 := bstep (se 2 (by rfl) ⟨1095000, by rfl⟩ : syracuseStep 2920001 = 2190001) B2190001
theorem B1946667 : Blo 1945435 1946667 := bstep (se 1 (by rfl) ⟨1460000, by rfl⟩ : syracuseStep 1946667 = 2920001) B2920001
theorem B2338645 : Blo 1945435 2338645 := bbase (se 9 (by rfl) ⟨6851, by rfl⟩ : syracuseStep 2338645 = 13703) (by norm_num)
theorem B3118193 : Blo 1945435 3118193 := bstep (se 2 (by rfl) ⟨1169322, by rfl⟩ : syracuseStep 3118193 = 2338645) B2338645
theorem B2078795 : Blo 1945435 2078795 := bstep (se 1 (by rfl) ⟨1559096, by rfl⟩ : syracuseStep 2078795 = 3118193) B3118193
theorem B5543453 : Blo 1945435 5543453 := bstep (se 3 (by rfl) ⟨1039397, by rfl⟩ : syracuseStep 5543453 = 2078795) B2078795
theorem B3695635 : Blo 1945435 3695635 := bstep (se 1 (by rfl) ⟨2771726, by rfl⟩ : syracuseStep 3695635 = 5543453) B5543453
theorem B4927513 : Blo 1945435 4927513 := bstep (se 2 (by rfl) ⟨1847817, by rfl⟩ : syracuseStep 4927513 = 3695635) B3695635
theorem B6570017 : Blo 1945435 6570017 := bstep (se 2 (by rfl) ⟨2463756, by rfl⟩ : syracuseStep 6570017 = 4927513) B4927513
theorem B4380011 : Blo 1945435 4380011 := bstep (se 1 (by rfl) ⟨3285008, by rfl⟩ : syracuseStep 4380011 = 6570017) B6570017
theorem B2920007 : Blo 1945435 2920007 := bstep (se 1 (by rfl) ⟨2190005, by rfl⟩ : syracuseStep 2920007 = 4380011) B4380011
theorem B1946671 : Blo 1945435 1946671 := bstep (se 1 (by rfl) ⟨1460003, by rfl⟩ : syracuseStep 1946671 = 2920007) B2920007
theorem B2920013 : Blo 1945435 2920013 := bbase (se 3 (by rfl) ⟨547502, by rfl⟩ : syracuseStep 2920013 = 1095005) (by norm_num)
theorem B1946675 : Blo 1945435 1946675 := bstep (se 1 (by rfl) ⟨1460006, by rfl⟩ : syracuseStep 1946675 = 2920013) B2920013
theorem B4380029 : Blo 1945435 4380029 := bbase (se 3 (by rfl) ⟨821255, by rfl⟩ : syracuseStep 4380029 = 1642511) (by norm_num)
theorem B2920019 : Blo 1945435 2920019 := bstep (se 1 (by rfl) ⟨2190014, by rfl⟩ : syracuseStep 2920019 = 4380029) B4380029
theorem B1946679 : Blo 1945435 1946679 := bstep (se 1 (by rfl) ⟨1460009, by rfl⟩ : syracuseStep 1946679 = 2920019) B2920019
theorem B3285029 : Blo 1945435 3285029 := bbase (se 4 (by rfl) ⟨307971, by rfl⟩ : syracuseStep 3285029 = 615943) (by norm_num)
theorem B2190019 : Blo 1945435 2190019 := bstep (se 1 (by rfl) ⟨1642514, by rfl⟩ : syracuseStep 2190019 = 3285029) B3285029
theorem B2920025 : Blo 1945435 2920025 := bstep (se 2 (by rfl) ⟨1095009, by rfl⟩ : syracuseStep 2920025 = 2190019) B2190019
theorem B1946683 : Blo 1945435 1946683 := bstep (se 1 (by rfl) ⟨1460012, by rfl⟩ : syracuseStep 1946683 = 2920025) B2920025
theorem B2771749 : Blo 1945435 2771749 := bbase (se 4 (by rfl) ⟨259851, by rfl⟩ : syracuseStep 2771749 = 519703) (by norm_num)
theorem B14782661 : Blo 1945435 14782661 := bstep (se 4 (by rfl) ⟨1385874, by rfl⟩ : syracuseStep 14782661 = 2771749) B2771749
theorem B9855107 : Blo 1945435 9855107 := bstep (se 1 (by rfl) ⟨7391330, by rfl⟩ : syracuseStep 9855107 = 14782661) B14782661
theorem B6570071 : Blo 1945435 6570071 := bstep (se 1 (by rfl) ⟨4927553, by rfl⟩ : syracuseStep 6570071 = 9855107) B9855107
theorem B4380047 : Blo 1945435 4380047 := bstep (se 1 (by rfl) ⟨3285035, by rfl⟩ : syracuseStep 4380047 = 6570071) B6570071
theorem B2920031 : Blo 1945435 2920031 := bstep (se 1 (by rfl) ⟨2190023, by rfl⟩ : syracuseStep 2920031 = 4380047) B4380047
theorem B1946687 : Blo 1945435 1946687 := bstep (se 1 (by rfl) ⟨1460015, by rfl⟩ : syracuseStep 1946687 = 2920031) B2920031
theorem B2920037 : Blo 1945435 2920037 := bbase (se 4 (by rfl) ⟨273753, by rfl⟩ : syracuseStep 2920037 = 547507) (by norm_num)
theorem B1946691 : Blo 1945435 1946691 := bstep (se 1 (by rfl) ⟨1460018, by rfl⟩ : syracuseStep 1946691 = 2920037) B2920037
theorem B2078821 : Blo 1945435 2078821 := bbase (se 4 (by rfl) ⟨194889, by rfl⟩ : syracuseStep 2078821 = 389779) (by norm_num)
theorem B2771761 : Blo 1945435 2771761 := bstep (se 2 (by rfl) ⟨1039410, by rfl⟩ : syracuseStep 2771761 = 2078821) B2078821
theorem B3695681 : Blo 1945435 3695681 := bstep (se 2 (by rfl) ⟨1385880, by rfl⟩ : syracuseStep 3695681 = 2771761) B2771761
theorem B2463787 : Blo 1945435 2463787 := bstep (se 1 (by rfl) ⟨1847840, by rfl⟩ : syracuseStep 2463787 = 3695681) B3695681
theorem B3285049 : Blo 1945435 3285049 := bstep (se 2 (by rfl) ⟨1231893, by rfl⟩ : syracuseStep 3285049 = 2463787) B2463787
theorem B4380065 : Blo 1945435 4380065 := bstep (se 2 (by rfl) ⟨1642524, by rfl⟩ : syracuseStep 4380065 = 3285049) B3285049
theorem B2920043 : Blo 1945435 2920043 := bstep (se 1 (by rfl) ⟨2190032, by rfl⟩ : syracuseStep 2920043 = 4380065) B4380065
theorem B1946695 : Blo 1945435 1946695 := bstep (se 1 (by rfl) ⟨1460021, by rfl⟩ : syracuseStep 1946695 = 2920043) B2920043
theorem B2190037 : Blo 1945435 2190037 := bbase (se 7 (by rfl) ⟨25664, by rfl⟩ : syracuseStep 2190037 = 51329) (by norm_num)
theorem B2920049 : Blo 1945435 2920049 := bstep (se 2 (by rfl) ⟨1095018, by rfl⟩ : syracuseStep 2920049 = 2190037) B2190037
theorem B1946699 : Blo 1945435 1946699 := bstep (se 1 (by rfl) ⟨1460024, by rfl⟩ : syracuseStep 1946699 = 2920049) B2920049
theorem B2463797 : Blo 1945435 2463797 := bbase (se 5 (by rfl) ⟨115490, by rfl⟩ : syracuseStep 2463797 = 230981) (by norm_num)
theorem B6570125 : Blo 1945435 6570125 := bstep (se 3 (by rfl) ⟨1231898, by rfl⟩ : syracuseStep 6570125 = 2463797) B2463797
theorem B4380083 : Blo 1945435 4380083 := bstep (se 1 (by rfl) ⟨3285062, by rfl⟩ : syracuseStep 4380083 = 6570125) B6570125
theorem B2920055 : Blo 1945435 2920055 := bstep (se 1 (by rfl) ⟨2190041, by rfl⟩ : syracuseStep 2920055 = 4380083) B4380083
theorem B1946703 : Blo 1945435 1946703 := bstep (se 1 (by rfl) ⟨1460027, by rfl⟩ : syracuseStep 1946703 = 2920055) B2920055
theorem B2920061 : Blo 1945435 2920061 := bbase (se 3 (by rfl) ⟨547511, by rfl⟩ : syracuseStep 2920061 = 1095023) (by norm_num)
theorem B1946707 : Blo 1945435 1946707 := bstep (se 1 (by rfl) ⟨1460030, by rfl⟩ : syracuseStep 1946707 = 2920061) B2920061
theorem B4380101 : Blo 1945435 4380101 := bbase (se 4 (by rfl) ⟨410634, by rfl⟩ : syracuseStep 4380101 = 821269) (by norm_num)
theorem B2920067 : Blo 1945435 2920067 := bstep (se 1 (by rfl) ⟨2190050, by rfl⟩ : syracuseStep 2920067 = 4380101) B4380101
theorem B1946711 : Blo 1945435 1946711 := bstep (se 1 (by rfl) ⟨1460033, by rfl⟩ : syracuseStep 1946711 = 2920067) B2920067
theorem B23679317 : Blo 1945435 23679317 := bbase (se 10 (by rfl) ⟨34686, by rfl⟩ : syracuseStep 23679317 = 69373) (by norm_num)
theorem B15786211 : Blo 1945435 15786211 := bstep (se 1 (by rfl) ⟨11839658, by rfl⟩ : syracuseStep 15786211 = 23679317) B23679317
theorem B21048281 : Blo 1945435 21048281 := bstep (se 2 (by rfl) ⟨7893105, by rfl⟩ : syracuseStep 21048281 = 15786211) B15786211
theorem B14032187 : Blo 1945435 14032187 := bstep (se 1 (by rfl) ⟨10524140, by rfl⟩ : syracuseStep 14032187 = 21048281) B21048281
theorem B9354791 : Blo 1945435 9354791 := bstep (se 1 (by rfl) ⟨7016093, by rfl⟩ : syracuseStep 9354791 = 14032187) B14032187
theorem B6236527 : Blo 1945435 6236527 := bstep (se 1 (by rfl) ⟨4677395, by rfl⟩ : syracuseStep 6236527 = 9354791) B9354791
theorem B8315369 : Blo 1945435 8315369 := bstep (se 2 (by rfl) ⟨3118263, by rfl⟩ : syracuseStep 8315369 = 6236527) B6236527
theorem B5543579 : Blo 1945435 5543579 := bstep (se 1 (by rfl) ⟨4157684, by rfl⟩ : syracuseStep 5543579 = 8315369) B8315369
theorem B3695719 : Blo 1945435 3695719 := bstep (se 1 (by rfl) ⟨2771789, by rfl⟩ : syracuseStep 3695719 = 5543579) B5543579
theorem B4927625 : Blo 1945435 4927625 := bstep (se 2 (by rfl) ⟨1847859, by rfl⟩ : syracuseStep 4927625 = 3695719) B3695719
theorem B3285083 : Blo 1945435 3285083 := bstep (se 1 (by rfl) ⟨2463812, by rfl⟩ : syracuseStep 3285083 = 4927625) B4927625
theorem B2190055 : Blo 1945435 2190055 := bstep (se 1 (by rfl) ⟨1642541, by rfl⟩ : syracuseStep 2190055 = 3285083) B3285083
theorem B2920073 : Blo 1945435 2920073 := bstep (se 2 (by rfl) ⟨1095027, by rfl⟩ : syracuseStep 2920073 = 2190055) B2190055
theorem B1946715 : Blo 1945435 1946715 := bstep (se 1 (by rfl) ⟨1460036, by rfl⟩ : syracuseStep 1946715 = 2920073) B2920073
theorem B9855269 : Blo 1945435 9855269 := bbase (se 4 (by rfl) ⟨923931, by rfl⟩ : syracuseStep 9855269 = 1847863) (by norm_num)
theorem B6570179 : Blo 1945435 6570179 := bstep (se 1 (by rfl) ⟨4927634, by rfl⟩ : syracuseStep 6570179 = 9855269) B9855269
theorem B4380119 : Blo 1945435 4380119 := bstep (se 1 (by rfl) ⟨3285089, by rfl⟩ : syracuseStep 4380119 = 6570179) B6570179
theorem B2920079 : Blo 1945435 2920079 := bstep (se 1 (by rfl) ⟨2190059, by rfl⟩ : syracuseStep 2920079 = 4380119) B4380119
theorem B1946719 : Blo 1945435 1946719 := bstep (se 1 (by rfl) ⟨1460039, by rfl⟩ : syracuseStep 1946719 = 2920079) B2920079
theorem B2920085 : Blo 1945435 2920085 := bbase (se 6 (by rfl) ⟨68439, by rfl⟩ : syracuseStep 2920085 = 136879) (by norm_num)
theorem B1946723 : Blo 1945435 1946723 := bstep (se 1 (by rfl) ⟨1460042, by rfl⟩ : syracuseStep 1946723 = 2920085) B2920085
theorem B8879797 : Blo 1945435 8879797 := bbase (se 5 (by rfl) ⟨416240, by rfl⟩ : syracuseStep 8879797 = 832481) (by norm_num)
theorem B47358917 : Blo 1945435 47358917 := bstep (se 4 (by rfl) ⟨4439898, by rfl⟩ : syracuseStep 47358917 = 8879797) B8879797
theorem B31572611 : Blo 1945435 31572611 := bstep (se 1 (by rfl) ⟨23679458, by rfl⟩ : syracuseStep 31572611 = 47358917) B47358917
theorem B21048407 : Blo 1945435 21048407 := bstep (se 1 (by rfl) ⟨15786305, by rfl⟩ : syracuseStep 21048407 = 31572611) B31572611
theorem B14032271 : Blo 1945435 14032271 := bstep (se 1 (by rfl) ⟨10524203, by rfl⟩ : syracuseStep 14032271 = 21048407) B21048407
theorem B9354847 : Blo 1945435 9354847 := bstep (se 1 (by rfl) ⟨7016135, by rfl⟩ : syracuseStep 9354847 = 14032271) B14032271
theorem B12473129 : Blo 1945435 12473129 := bstep (se 2 (by rfl) ⟨4677423, by rfl⟩ : syracuseStep 12473129 = 9354847) B9354847
theorem B8315419 : Blo 1945435 8315419 := bstep (se 1 (by rfl) ⟨6236564, by rfl⟩ : syracuseStep 8315419 = 12473129) B12473129
theorem B11087225 : Blo 1945435 11087225 := bstep (se 2 (by rfl) ⟨4157709, by rfl⟩ : syracuseStep 11087225 = 8315419) B8315419
theorem B7391483 : Blo 1945435 7391483 := bstep (se 1 (by rfl) ⟨5543612, by rfl⟩ : syracuseStep 7391483 = 11087225) B11087225
theorem B4927655 : Blo 1945435 4927655 := bstep (se 1 (by rfl) ⟨3695741, by rfl⟩ : syracuseStep 4927655 = 7391483) B7391483
theorem B3285103 : Blo 1945435 3285103 := bstep (se 1 (by rfl) ⟨2463827, by rfl⟩ : syracuseStep 3285103 = 4927655) B4927655
theorem B4380137 : Blo 1945435 4380137 := bstep (se 2 (by rfl) ⟨1642551, by rfl⟩ : syracuseStep 4380137 = 3285103) B3285103
theorem B2920091 : Blo 1945435 2920091 := bstep (se 1 (by rfl) ⟨2190068, by rfl⟩ : syracuseStep 2920091 = 4380137) B4380137
theorem B1946727 : Blo 1945435 1946727 := bstep (se 1 (by rfl) ⟨1460045, by rfl⟩ : syracuseStep 1946727 = 2920091) B2920091
theorem B2190073 : Blo 1945435 2190073 := bbase (se 2 (by rfl) ⟨821277, by rfl⟩ : syracuseStep 2190073 = 1642555) (by norm_num)
theorem B2920097 : Blo 1945435 2920097 := bstep (se 2 (by rfl) ⟨1095036, by rfl⟩ : syracuseStep 2920097 = 2190073) B2190073
theorem B1946731 : Blo 1945435 1946731 := bstep (se 1 (by rfl) ⟨1460048, by rfl⟩ : syracuseStep 1946731 = 2920097) B2920097
theorem B7016165 : Blo 1945435 7016165 := bbase (se 4 (by rfl) ⟨657765, by rfl⟩ : syracuseStep 7016165 = 1315531) (by norm_num)
theorem B4677443 : Blo 1945435 4677443 := bstep (se 1 (by rfl) ⟨3508082, by rfl⟩ : syracuseStep 4677443 = 7016165) B7016165
theorem B3118295 : Blo 1945435 3118295 := bstep (se 1 (by rfl) ⟨2338721, by rfl⟩ : syracuseStep 3118295 = 4677443) B4677443
theorem B8315453 : Blo 1945435 8315453 := bstep (se 3 (by rfl) ⟨1559147, by rfl⟩ : syracuseStep 8315453 = 3118295) B3118295
theorem B5543635 : Blo 1945435 5543635 := bstep (se 1 (by rfl) ⟨4157726, by rfl⟩ : syracuseStep 5543635 = 8315453) B8315453
theorem B7391513 : Blo 1945435 7391513 := bstep (se 2 (by rfl) ⟨2771817, by rfl⟩ : syracuseStep 7391513 = 5543635) B5543635
theorem B4927675 : Blo 1945435 4927675 := bstep (se 1 (by rfl) ⟨3695756, by rfl⟩ : syracuseStep 4927675 = 7391513) B7391513
theorem B6570233 : Blo 1945435 6570233 := bstep (se 2 (by rfl) ⟨2463837, by rfl⟩ : syracuseStep 6570233 = 4927675) B4927675
theorem B4380155 : Blo 1945435 4380155 := bstep (se 1 (by rfl) ⟨3285116, by rfl⟩ : syracuseStep 4380155 = 6570233) B6570233
theorem B2920103 : Blo 1945435 2920103 := bstep (se 1 (by rfl) ⟨2190077, by rfl⟩ : syracuseStep 2920103 = 4380155) B4380155
theorem B1946735 : Blo 1945435 1946735 := bstep (se 1 (by rfl) ⟨1460051, by rfl⟩ : syracuseStep 1946735 = 2920103) B2920103
theorem B2920109 : Blo 1945435 2920109 := bbase (se 3 (by rfl) ⟨547520, by rfl⟩ : syracuseStep 2920109 = 1095041) (by norm_num)
theorem B1946739 : Blo 1945435 1946739 := bstep (se 1 (by rfl) ⟨1460054, by rfl⟩ : syracuseStep 1946739 = 2920109) B2920109
theorem B4380173 : Blo 1945435 4380173 := bbase (se 3 (by rfl) ⟨821282, by rfl⟩ : syracuseStep 4380173 = 1642565) (by norm_num)
theorem B2920115 : Blo 1945435 2920115 := bstep (se 1 (by rfl) ⟨2190086, by rfl⟩ : syracuseStep 2920115 = 4380173) B4380173
theorem B1946743 : Blo 1945435 1946743 := bstep (se 1 (by rfl) ⟨1460057, by rfl⟩ : syracuseStep 1946743 = 2920115) B2920115
theorem B2463853 : Blo 1945435 2463853 := bbase (se 3 (by rfl) ⟨461972, by rfl⟩ : syracuseStep 2463853 = 923945) (by norm_num)
theorem B3285137 : Blo 1945435 3285137 := bstep (se 2 (by rfl) ⟨1231926, by rfl⟩ : syracuseStep 3285137 = 2463853) B2463853
theorem B2190091 : Blo 1945435 2190091 := bstep (se 1 (by rfl) ⟨1642568, by rfl⟩ : syracuseStep 2190091 = 3285137) B3285137
theorem B2920121 : Blo 1945435 2920121 := bstep (se 2 (by rfl) ⟨1095045, by rfl⟩ : syracuseStep 2920121 = 2190091) B2190091
theorem B1946747 : Blo 1945435 1946747 := bstep (se 1 (by rfl) ⟨1460060, by rfl⟩ : syracuseStep 1946747 = 2920121) B2920121
theorem B2219977 : Blo 1945435 2219977 := bbase (se 2 (by rfl) ⟨832491, by rfl⟩ : syracuseStep 2219977 = 1664983) (by norm_num)
theorem B2959969 : Blo 1945435 2959969 := bstep (se 2 (by rfl) ⟨1109988, by rfl⟩ : syracuseStep 2959969 = 2219977) B2219977
theorem B3946625 : Blo 1945435 3946625 := bstep (se 2 (by rfl) ⟨1479984, by rfl⟩ : syracuseStep 3946625 = 2959969) B2959969
theorem B2631083 : Blo 1945435 2631083 := bstep (se 1 (by rfl) ⟨1973312, by rfl⟩ : syracuseStep 2631083 = 3946625) B3946625
theorem B7016221 : Blo 1945435 7016221 := bstep (se 3 (by rfl) ⟨1315541, by rfl⟩ : syracuseStep 7016221 = 2631083) B2631083
theorem B9354961 : Blo 1945435 9354961 := bstep (se 2 (by rfl) ⟨3508110, by rfl⟩ : syracuseStep 9354961 = 7016221) B7016221
theorem B12473281 : Blo 1945435 12473281 := bstep (se 2 (by rfl) ⟨4677480, by rfl⟩ : syracuseStep 12473281 = 9354961) B9354961
theorem B16631041 : Blo 1945435 16631041 := bstep (se 2 (by rfl) ⟨6236640, by rfl⟩ : syracuseStep 16631041 = 12473281) B12473281
theorem B22174721 : Blo 1945435 22174721 := bstep (se 2 (by rfl) ⟨8315520, by rfl⟩ : syracuseStep 22174721 = 16631041) B16631041
theorem B14783147 : Blo 1945435 14783147 := bstep (se 1 (by rfl) ⟨11087360, by rfl⟩ : syracuseStep 14783147 = 22174721) B22174721
theorem B9855431 : Blo 1945435 9855431 := bstep (se 1 (by rfl) ⟨7391573, by rfl⟩ : syracuseStep 9855431 = 14783147) B14783147
theorem B6570287 : Blo 1945435 6570287 := bstep (se 1 (by rfl) ⟨4927715, by rfl⟩ : syracuseStep 6570287 = 9855431) B9855431
theorem B4380191 : Blo 1945435 4380191 := bstep (se 1 (by rfl) ⟨3285143, by rfl⟩ : syracuseStep 4380191 = 6570287) B6570287
theorem B2920127 : Blo 1945435 2920127 := bstep (se 1 (by rfl) ⟨2190095, by rfl⟩ : syracuseStep 2920127 = 4380191) B4380191
theorem B1946751 : Blo 1945435 1946751 := bstep (se 1 (by rfl) ⟨1460063, by rfl⟩ : syracuseStep 1946751 = 2920127) B2920127
theorem B2920133 : Blo 1945435 2920133 := bbase (se 4 (by rfl) ⟨273762, by rfl⟩ : syracuseStep 2920133 = 547525) (by norm_num)
theorem B1946755 : Blo 1945435 1946755 := bstep (se 1 (by rfl) ⟨1460066, by rfl⟩ : syracuseStep 1946755 = 2920133) B2920133
theorem B3285157 : Blo 1945435 3285157 := bbase (se 4 (by rfl) ⟨307983, by rfl⟩ : syracuseStep 3285157 = 615967) (by norm_num)
theorem B4380209 : Blo 1945435 4380209 := bstep (se 2 (by rfl) ⟨1642578, by rfl⟩ : syracuseStep 4380209 = 3285157) B3285157
theorem B2920139 : Blo 1945435 2920139 := bstep (se 1 (by rfl) ⟨2190104, by rfl⟩ : syracuseStep 2920139 = 4380209) B4380209
theorem B1946759 : Blo 1945435 1946759 := bstep (se 1 (by rfl) ⟨1460069, by rfl⟩ : syracuseStep 1946759 = 2920139) B2920139
theorem B2190109 : Blo 1945435 2190109 := bbase (se 3 (by rfl) ⟨410645, by rfl⟩ : syracuseStep 2190109 = 821291) (by norm_num)
theorem B2920145 : Blo 1945435 2920145 := bstep (se 2 (by rfl) ⟨1095054, by rfl⟩ : syracuseStep 2920145 = 2190109) B2190109
theorem B1946763 : Blo 1945435 1946763 := bstep (se 1 (by rfl) ⟨1460072, by rfl⟩ : syracuseStep 1946763 = 2920145) B2920145
theorem B6570341 : Blo 1945435 6570341 := bbase (se 4 (by rfl) ⟨615969, by rfl⟩ : syracuseStep 6570341 = 1231939) (by norm_num)
theorem B4380227 : Blo 1945435 4380227 := bstep (se 1 (by rfl) ⟨3285170, by rfl⟩ : syracuseStep 4380227 = 6570341) B6570341
theorem B2920151 : Blo 1945435 2920151 := bstep (se 1 (by rfl) ⟨2190113, by rfl⟩ : syracuseStep 2920151 = 4380227) B4380227
theorem B1946767 : Blo 1945435 1946767 := bstep (se 1 (by rfl) ⟨1460075, by rfl⟩ : syracuseStep 1946767 = 2920151) B2920151
theorem B2920157 : Blo 1945435 2920157 := bbase (se 3 (by rfl) ⟨547529, by rfl⟩ : syracuseStep 2920157 = 1095059) (by norm_num)
theorem B1946771 : Blo 1945435 1946771 := bstep (se 1 (by rfl) ⟨1460078, by rfl⟩ : syracuseStep 1946771 = 2920157) B2920157
theorem B4380245 : Blo 1945435 4380245 := bbase (se 8 (by rfl) ⟨25665, by rfl⟩ : syracuseStep 4380245 = 51331) (by norm_num)
theorem B2920163 : Blo 1945435 2920163 := bstep (se 1 (by rfl) ⟨2190122, by rfl⟩ : syracuseStep 2920163 = 4380245) B4380245
theorem B1946775 : Blo 1945435 1946775 := bstep (se 1 (by rfl) ⟨1460081, by rfl⟩ : syracuseStep 1946775 = 2920163) B2920163
theorem B4157821 : Blo 1945435 4157821 := bbase (se 3 (by rfl) ⟨779591, by rfl⟩ : syracuseStep 4157821 = 1559183) (by norm_num)
theorem B5543761 : Blo 1945435 5543761 := bstep (se 2 (by rfl) ⟨2078910, by rfl⟩ : syracuseStep 5543761 = 4157821) B4157821
theorem B7391681 : Blo 1945435 7391681 := bstep (se 2 (by rfl) ⟨2771880, by rfl⟩ : syracuseStep 7391681 = 5543761) B5543761
theorem B4927787 : Blo 1945435 4927787 := bstep (se 1 (by rfl) ⟨3695840, by rfl⟩ : syracuseStep 4927787 = 7391681) B7391681
theorem B3285191 : Blo 1945435 3285191 := bstep (se 1 (by rfl) ⟨2463893, by rfl⟩ : syracuseStep 3285191 = 4927787) B4927787
theorem B2190127 : Blo 1945435 2190127 := bstep (se 1 (by rfl) ⟨1642595, by rfl⟩ : syracuseStep 2190127 = 3285191) B3285191
theorem B2920169 : Blo 1945435 2920169 := bstep (se 2 (by rfl) ⟨1095063, by rfl⟩ : syracuseStep 2920169 = 2190127) B2190127
theorem B1946779 : Blo 1945435 1946779 := bstep (se 1 (by rfl) ⟨1460084, by rfl⟩ : syracuseStep 1946779 = 2920169) B2920169
theorem B2220013 : Blo 1945435 2220013 := bbase (se 3 (by rfl) ⟨416252, by rfl⟩ : syracuseStep 2220013 = 832505) (by norm_num)
theorem B11840069 : Blo 1945435 11840069 := bstep (se 4 (by rfl) ⟨1110006, by rfl⟩ : syracuseStep 11840069 = 2220013) B2220013
theorem B7893379 : Blo 1945435 7893379 := bstep (se 1 (by rfl) ⟨5920034, by rfl⟩ : syracuseStep 7893379 = 11840069) B11840069
theorem B10524505 : Blo 1945435 10524505 := bstep (se 2 (by rfl) ⟨3946689, by rfl⟩ : syracuseStep 10524505 = 7893379) B7893379
theorem B14032673 : Blo 1945435 14032673 := bstep (se 2 (by rfl) ⟨5262252, by rfl⟩ : syracuseStep 14032673 = 10524505) B10524505
theorem B9355115 : Blo 1945435 9355115 := bstep (se 1 (by rfl) ⟨7016336, by rfl⟩ : syracuseStep 9355115 = 14032673) B14032673
theorem B24946973 : Blo 1945435 24946973 := bstep (se 3 (by rfl) ⟨4677557, by rfl⟩ : syracuseStep 24946973 = 9355115) B9355115
theorem B16631315 : Blo 1945435 16631315 := bstep (se 1 (by rfl) ⟨12473486, by rfl⟩ : syracuseStep 16631315 = 24946973) B24946973
theorem B11087543 : Blo 1945435 11087543 := bstep (se 1 (by rfl) ⟨8315657, by rfl⟩ : syracuseStep 11087543 = 16631315) B16631315
theorem B7391695 : Blo 1945435 7391695 := bstep (se 1 (by rfl) ⟨5543771, by rfl⟩ : syracuseStep 7391695 = 11087543) B11087543
theorem B9855593 : Blo 1945435 9855593 := bstep (se 2 (by rfl) ⟨3695847, by rfl⟩ : syracuseStep 9855593 = 7391695) B7391695
theorem B6570395 : Blo 1945435 6570395 := bstep (se 1 (by rfl) ⟨4927796, by rfl⟩ : syracuseStep 6570395 = 9855593) B9855593
theorem B4380263 : Blo 1945435 4380263 := bstep (se 1 (by rfl) ⟨3285197, by rfl⟩ : syracuseStep 4380263 = 6570395) B6570395
theorem B2920175 : Blo 1945435 2920175 := bstep (se 1 (by rfl) ⟨2190131, by rfl⟩ : syracuseStep 2920175 = 4380263) B4380263
theorem B1946783 : Blo 1945435 1946783 := bstep (se 1 (by rfl) ⟨1460087, by rfl⟩ : syracuseStep 1946783 = 2920175) B2920175
theorem B2920181 : Blo 1945435 2920181 := bbase (se 5 (by rfl) ⟨136883, by rfl⟩ : syracuseStep 2920181 = 273767) (by norm_num)
theorem B1946787 : Blo 1945435 1946787 := bstep (se 1 (by rfl) ⟨1460090, by rfl⟩ : syracuseStep 1946787 = 2920181) B2920181
theorem B2338789 : Blo 1945435 2338789 := bbase (se 4 (by rfl) ⟨219261, by rfl⟩ : syracuseStep 2338789 = 438523) (by norm_num)
theorem B3118385 : Blo 1945435 3118385 := bstep (se 2 (by rfl) ⟨1169394, by rfl⟩ : syracuseStep 3118385 = 2338789) B2338789
theorem B8315693 : Blo 1945435 8315693 := bstep (se 3 (by rfl) ⟨1559192, by rfl⟩ : syracuseStep 8315693 = 3118385) B3118385
theorem B5543795 : Blo 1945435 5543795 := bstep (se 1 (by rfl) ⟨4157846, by rfl⟩ : syracuseStep 5543795 = 8315693) B8315693
theorem B3695863 : Blo 1945435 3695863 := bstep (se 1 (by rfl) ⟨2771897, by rfl⟩ : syracuseStep 3695863 = 5543795) B5543795
theorem B4927817 : Blo 1945435 4927817 := bstep (se 2 (by rfl) ⟨1847931, by rfl⟩ : syracuseStep 4927817 = 3695863) B3695863
theorem B3285211 : Blo 1945435 3285211 := bstep (se 1 (by rfl) ⟨2463908, by rfl⟩ : syracuseStep 3285211 = 4927817) B4927817
theorem B4380281 : Blo 1945435 4380281 := bstep (se 2 (by rfl) ⟨1642605, by rfl⟩ : syracuseStep 4380281 = 3285211) B3285211
theorem B2920187 : Blo 1945435 2920187 := bstep (se 1 (by rfl) ⟨2190140, by rfl⟩ : syracuseStep 2920187 = 4380281) B4380281
theorem B1946791 : Blo 1945435 1946791 := bstep (se 1 (by rfl) ⟨1460093, by rfl⟩ : syracuseStep 1946791 = 2920187) B2920187
theorem B2190145 : Blo 1945435 2190145 := bbase (se 2 (by rfl) ⟨821304, by rfl⟩ : syracuseStep 2190145 = 1642609) (by norm_num)
theorem B2920193 : Blo 1945435 2920193 := bstep (se 2 (by rfl) ⟨1095072, by rfl⟩ : syracuseStep 2920193 = 2190145) B2190145
theorem B1946795 : Blo 1945435 1946795 := bstep (se 1 (by rfl) ⟨1460096, by rfl⟩ : syracuseStep 1946795 = 2920193) B2920193
theorem B4927837 : Blo 1945435 4927837 := bbase (se 3 (by rfl) ⟨923969, by rfl⟩ : syracuseStep 4927837 = 1847939) (by norm_num)
theorem B6570449 : Blo 1945435 6570449 := bstep (se 2 (by rfl) ⟨2463918, by rfl⟩ : syracuseStep 6570449 = 4927837) B4927837
theorem B4380299 : Blo 1945435 4380299 := bstep (se 1 (by rfl) ⟨3285224, by rfl⟩ : syracuseStep 4380299 = 6570449) B6570449
theorem B2920199 : Blo 1945435 2920199 := bstep (se 1 (by rfl) ⟨2190149, by rfl⟩ : syracuseStep 2920199 = 4380299) B4380299
theorem B1946799 : Blo 1945435 1946799 := bstep (se 1 (by rfl) ⟨1460099, by rfl⟩ : syracuseStep 1946799 = 2920199) B2920199
theorem B2920205 : Blo 1945435 2920205 := bbase (se 3 (by rfl) ⟨547538, by rfl⟩ : syracuseStep 2920205 = 1095077) (by norm_num)
theorem B1946803 : Blo 1945435 1946803 := bstep (se 1 (by rfl) ⟨1460102, by rfl⟩ : syracuseStep 1946803 = 2920205) B2920205
theorem B4380317 : Blo 1945435 4380317 := bbase (se 3 (by rfl) ⟨821309, by rfl⟩ : syracuseStep 4380317 = 1642619) (by norm_num)
theorem B2920211 : Blo 1945435 2920211 := bstep (se 1 (by rfl) ⟨2190158, by rfl⟩ : syracuseStep 2920211 = 4380317) B4380317
theorem B1946807 : Blo 1945435 1946807 := bstep (se 1 (by rfl) ⟨1460105, by rfl⟩ : syracuseStep 1946807 = 2920211) B2920211
theorem B3285245 : Blo 1945435 3285245 := bbase (se 3 (by rfl) ⟨615983, by rfl⟩ : syracuseStep 3285245 = 1231967) (by norm_num)
theorem B2190163 : Blo 1945435 2190163 := bstep (se 1 (by rfl) ⟨1642622, by rfl⟩ : syracuseStep 2190163 = 3285245) B3285245
theorem B2920217 : Blo 1945435 2920217 := bstep (se 2 (by rfl) ⟨1095081, by rfl⟩ : syracuseStep 2920217 = 2190163) B2190163
theorem B1946811 : Blo 1945435 1946811 := bstep (se 1 (by rfl) ⟨1460108, by rfl⟩ : syracuseStep 1946811 = 2920217) B2920217
theorem B7016453 : Blo 1945435 7016453 := bbase (se 4 (by rfl) ⟨657792, by rfl⟩ : syracuseStep 7016453 = 1315585) (by norm_num)
theorem B4677635 : Blo 1945435 4677635 := bstep (se 1 (by rfl) ⟨3508226, by rfl⟩ : syracuseStep 4677635 = 7016453) B7016453
theorem B3118423 : Blo 1945435 3118423 := bstep (se 1 (by rfl) ⟨2338817, by rfl⟩ : syracuseStep 3118423 = 4677635) B4677635
theorem B4157897 : Blo 1945435 4157897 := bstep (se 2 (by rfl) ⟨1559211, by rfl⟩ : syracuseStep 4157897 = 3118423) B3118423
theorem B11087725 : Blo 1945435 11087725 := bstep (se 3 (by rfl) ⟨2078948, by rfl⟩ : syracuseStep 11087725 = 4157897) B4157897
theorem B14783633 : Blo 1945435 14783633 := bstep (se 2 (by rfl) ⟨5543862, by rfl⟩ : syracuseStep 14783633 = 11087725) B11087725
theorem B9855755 : Blo 1945435 9855755 := bstep (se 1 (by rfl) ⟨7391816, by rfl⟩ : syracuseStep 9855755 = 14783633) B14783633
theorem B6570503 : Blo 1945435 6570503 := bstep (se 1 (by rfl) ⟨4927877, by rfl⟩ : syracuseStep 6570503 = 9855755) B9855755
theorem B4380335 : Blo 1945435 4380335 := bstep (se 1 (by rfl) ⟨3285251, by rfl⟩ : syracuseStep 4380335 = 6570503) B6570503
theorem B2920223 : Blo 1945435 2920223 := bstep (se 1 (by rfl) ⟨2190167, by rfl⟩ : syracuseStep 2920223 = 4380335) B4380335
theorem B1946815 : Blo 1945435 1946815 := bstep (se 1 (by rfl) ⟨1460111, by rfl⟩ : syracuseStep 1946815 = 2920223) B2920223
theorem B2920229 : Blo 1945435 2920229 := bbase (se 4 (by rfl) ⟨273771, by rfl⟩ : syracuseStep 2920229 = 547543) (by norm_num)
theorem B1946819 : Blo 1945435 1946819 := bstep (se 1 (by rfl) ⟨1460114, by rfl⟩ : syracuseStep 1946819 = 2920229) B2920229
theorem B2463949 : Blo 1945435 2463949 := bbase (se 3 (by rfl) ⟨461990, by rfl⟩ : syracuseStep 2463949 = 923981) (by norm_num)
theorem B3285265 : Blo 1945435 3285265 := bstep (se 2 (by rfl) ⟨1231974, by rfl⟩ : syracuseStep 3285265 = 2463949) B2463949
theorem B4380353 : Blo 1945435 4380353 := bstep (se 2 (by rfl) ⟨1642632, by rfl⟩ : syracuseStep 4380353 = 3285265) B3285265
theorem B2920235 : Blo 1945435 2920235 := bstep (se 1 (by rfl) ⟨2190176, by rfl⟩ : syracuseStep 2920235 = 4380353) B4380353
theorem B1946823 : Blo 1945435 1946823 := bstep (se 1 (by rfl) ⟨1460117, by rfl⟩ : syracuseStep 1946823 = 2920235) B2920235
theorem B2190181 : Blo 1945435 2190181 := bbase (se 4 (by rfl) ⟨205329, by rfl⟩ : syracuseStep 2190181 = 410659) (by norm_num)
theorem B2920241 : Blo 1945435 2920241 := bstep (se 2 (by rfl) ⟨1095090, by rfl⟩ : syracuseStep 2920241 = 2190181) B2190181
theorem B1946827 : Blo 1945435 1946827 := bstep (se 1 (by rfl) ⟨1460120, by rfl⟩ : syracuseStep 1946827 = 2920241) B2920241
theorem B5543909 : Blo 1945435 5543909 := bbase (se 4 (by rfl) ⟨519741, by rfl⟩ : syracuseStep 5543909 = 1039483) (by norm_num)
theorem B3695939 : Blo 1945435 3695939 := bstep (se 1 (by rfl) ⟨2771954, by rfl⟩ : syracuseStep 3695939 = 5543909) B5543909
theorem B2463959 : Blo 1945435 2463959 := bstep (se 1 (by rfl) ⟨1847969, by rfl⟩ : syracuseStep 2463959 = 3695939) B3695939
theorem B6570557 : Blo 1945435 6570557 := bstep (se 3 (by rfl) ⟨1231979, by rfl⟩ : syracuseStep 6570557 = 2463959) B2463959
theorem B4380371 : Blo 1945435 4380371 := bstep (se 1 (by rfl) ⟨3285278, by rfl⟩ : syracuseStep 4380371 = 6570557) B6570557
theorem B2920247 : Blo 1945435 2920247 := bstep (se 1 (by rfl) ⟨2190185, by rfl⟩ : syracuseStep 2920247 = 4380371) B4380371
theorem B1946831 : Blo 1945435 1946831 := bstep (se 1 (by rfl) ⟨1460123, by rfl⟩ : syracuseStep 1946831 = 2920247) B2920247
theorem B2920253 : Blo 1945435 2920253 := bbase (se 3 (by rfl) ⟨547547, by rfl⟩ : syracuseStep 2920253 = 1095095) (by norm_num)
theorem B1946835 : Blo 1945435 1946835 := bstep (se 1 (by rfl) ⟨1460126, by rfl⟩ : syracuseStep 1946835 = 2920253) B2920253
theorem B4380389 : Blo 1945435 4380389 := bbase (se 4 (by rfl) ⟨410661, by rfl⟩ : syracuseStep 4380389 = 821323) (by norm_num)
theorem B2920259 : Blo 1945435 2920259 := bstep (se 1 (by rfl) ⟨2190194, by rfl⟩ : syracuseStep 2920259 = 4380389) B4380389
theorem B1946839 : Blo 1945435 1946839 := bstep (se 1 (by rfl) ⟨1460129, by rfl⟩ : syracuseStep 1946839 = 2920259) B2920259
theorem B4927949 : Blo 1945435 4927949 := bbase (se 3 (by rfl) ⟨923990, by rfl⟩ : syracuseStep 4927949 = 1847981) (by norm_num)
theorem B3285299 : Blo 1945435 3285299 := bstep (se 1 (by rfl) ⟨2463974, by rfl⟩ : syracuseStep 3285299 = 4927949) B4927949
theorem B2190199 : Blo 1945435 2190199 := bstep (se 1 (by rfl) ⟨1642649, by rfl⟩ : syracuseStep 2190199 = 3285299) B3285299
theorem B2920265 : Blo 1945435 2920265 := bstep (se 2 (by rfl) ⟨1095099, by rfl⟩ : syracuseStep 2920265 = 2190199) B2190199
theorem B1946843 : Blo 1945435 1946843 := bstep (se 1 (by rfl) ⟨1460132, by rfl⟩ : syracuseStep 1946843 = 2920265) B2920265
theorem B3508285 : Blo 1945435 3508285 := bbase (se 3 (by rfl) ⟨657803, by rfl⟩ : syracuseStep 3508285 = 1315607) (by norm_num)
theorem B4677713 : Blo 1945435 4677713 := bstep (se 2 (by rfl) ⟨1754142, by rfl⟩ : syracuseStep 4677713 = 3508285) B3508285
theorem B3118475 : Blo 1945435 3118475 := bstep (se 1 (by rfl) ⟨2338856, by rfl⟩ : syracuseStep 3118475 = 4677713) B4677713
theorem B2078983 : Blo 1945435 2078983 := bstep (se 1 (by rfl) ⟨1559237, by rfl⟩ : syracuseStep 2078983 = 3118475) B3118475
theorem B2771977 : Blo 1945435 2771977 := bstep (se 2 (by rfl) ⟨1039491, by rfl⟩ : syracuseStep 2771977 = 2078983) B2078983
theorem B3695969 : Blo 1945435 3695969 := bstep (se 2 (by rfl) ⟨1385988, by rfl⟩ : syracuseStep 3695969 = 2771977) B2771977
theorem B9855917 : Blo 1945435 9855917 := bstep (se 3 (by rfl) ⟨1847984, by rfl⟩ : syracuseStep 9855917 = 3695969) B3695969
theorem B6570611 : Blo 1945435 6570611 := bstep (se 1 (by rfl) ⟨4927958, by rfl⟩ : syracuseStep 6570611 = 9855917) B9855917
theorem B4380407 : Blo 1945435 4380407 := bstep (se 1 (by rfl) ⟨3285305, by rfl⟩ : syracuseStep 4380407 = 6570611) B6570611
theorem B2920271 : Blo 1945435 2920271 := bstep (se 1 (by rfl) ⟨2190203, by rfl⟩ : syracuseStep 2920271 = 4380407) B4380407
theorem B1946847 : Blo 1945435 1946847 := bstep (se 1 (by rfl) ⟨1460135, by rfl⟩ : syracuseStep 1946847 = 2920271) B2920271
theorem B2920277 : Blo 1945435 2920277 := bbase (se 9 (by rfl) ⟨8555, by rfl⟩ : syracuseStep 2920277 = 17111) (by norm_num)
theorem B1946851 : Blo 1945435 1946851 := bstep (se 1 (by rfl) ⟨1460138, by rfl⟩ : syracuseStep 1946851 = 2920277) B2920277
theorem B4806245 : Blo 1945435 4806245 := bbase (se 4 (by rfl) ⟨450585, by rfl⟩ : syracuseStep 4806245 = 901171) (by norm_num)
theorem B3204163 : Blo 1945435 3204163 := bstep (se 1 (by rfl) ⟨2403122, by rfl⟩ : syracuseStep 3204163 = 4806245) B4806245
theorem B17088869 : Blo 1945435 17088869 := bstep (se 4 (by rfl) ⟨1602081, by rfl⟩ : syracuseStep 17088869 = 3204163) B3204163
theorem B11392579 : Blo 1945435 11392579 := bstep (se 1 (by rfl) ⟨8544434, by rfl⟩ : syracuseStep 11392579 = 17088869) B17088869
theorem B15190105 : Blo 1945435 15190105 := bstep (se 2 (by rfl) ⟨5696289, by rfl⟩ : syracuseStep 15190105 = 11392579) B11392579
theorem B20253473 : Blo 1945435 20253473 := bstep (se 2 (by rfl) ⟨7595052, by rfl⟩ : syracuseStep 20253473 = 15190105) B15190105
theorem B13502315 : Blo 1945435 13502315 := bstep (se 1 (by rfl) ⟨10126736, by rfl⟩ : syracuseStep 13502315 = 20253473) B20253473
theorem B9001543 : Blo 1945435 9001543 := bstep (se 1 (by rfl) ⟨6751157, by rfl⟩ : syracuseStep 9001543 = 13502315) B13502315
theorem B12002057 : Blo 1945435 12002057 := bstep (se 2 (by rfl) ⟨4500771, by rfl⟩ : syracuseStep 12002057 = 9001543) B9001543
theorem B8001371 : Blo 1945435 8001371 := bstep (se 1 (by rfl) ⟨6001028, by rfl⟩ : syracuseStep 8001371 = 12002057) B12002057
theorem B5334247 : Blo 1945435 5334247 := bstep (se 1 (by rfl) ⟨4000685, by rfl⟩ : syracuseStep 5334247 = 8001371) B8001371
theorem B7112329 : Blo 1945435 7112329 := bstep (se 2 (by rfl) ⟨2667123, by rfl⟩ : syracuseStep 7112329 = 5334247) B5334247
theorem B37932421 : Blo 1945435 37932421 := bstep (se 4 (by rfl) ⟨3556164, by rfl⟩ : syracuseStep 37932421 = 7112329) B7112329
theorem B50576561 : Blo 1945435 50576561 := bstep (se 2 (by rfl) ⟨18966210, by rfl⟩ : syracuseStep 50576561 = 37932421) B37932421
theorem B33717707 : Blo 1945435 33717707 := bstep (se 1 (by rfl) ⟨25288280, by rfl⟩ : syracuseStep 33717707 = 50576561) B50576561
theorem B22478471 : Blo 1945435 22478471 := bstep (se 1 (by rfl) ⟨16858853, by rfl⟩ : syracuseStep 22478471 = 33717707) B33717707
theorem B14985647 : Blo 1945435 14985647 := bstep (se 1 (by rfl) ⟨11239235, by rfl⟩ : syracuseStep 14985647 = 22478471) B22478471
theorem B9990431 : Blo 1945435 9990431 := bstep (se 1 (by rfl) ⟨7492823, by rfl⟩ : syracuseStep 9990431 = 14985647) B14985647
theorem B6660287 : Blo 1945435 6660287 := bstep (se 1 (by rfl) ⟨4995215, by rfl⟩ : syracuseStep 6660287 = 9990431) B9990431
theorem B4440191 : Blo 1945435 4440191 := bstep (se 1 (by rfl) ⟨3330143, by rfl⟩ : syracuseStep 4440191 = 6660287) B6660287
theorem B11840509 : Blo 1945435 11840509 := bstep (se 3 (by rfl) ⟨2220095, by rfl⟩ : syracuseStep 11840509 = 4440191) B4440191
theorem B15787345 : Blo 1945435 15787345 := bstep (se 2 (by rfl) ⟨5920254, by rfl⟩ : syracuseStep 15787345 = 11840509) B11840509
theorem B21049793 : Blo 1945435 21049793 := bstep (se 2 (by rfl) ⟨7893672, by rfl⟩ : syracuseStep 21049793 = 15787345) B15787345
theorem B14033195 : Blo 1945435 14033195 := bstep (se 1 (by rfl) ⟨10524896, by rfl⟩ : syracuseStep 14033195 = 21049793) B21049793
theorem B9355463 : Blo 1945435 9355463 := bstep (se 1 (by rfl) ⟨7016597, by rfl⟩ : syracuseStep 9355463 = 14033195) B14033195
theorem B6236975 : Blo 1945435 6236975 := bstep (se 1 (by rfl) ⟨4677731, by rfl⟩ : syracuseStep 6236975 = 9355463) B9355463
theorem B4157983 : Blo 1945435 4157983 := bstep (se 1 (by rfl) ⟨3118487, by rfl⟩ : syracuseStep 4157983 = 6236975) B6236975
theorem B5543977 : Blo 1945435 5543977 := bstep (se 2 (by rfl) ⟨2078991, by rfl⟩ : syracuseStep 5543977 = 4157983) B4157983
theorem B7391969 : Blo 1945435 7391969 := bstep (se 2 (by rfl) ⟨2771988, by rfl⟩ : syracuseStep 7391969 = 5543977) B5543977
theorem B4927979 : Blo 1945435 4927979 := bstep (se 1 (by rfl) ⟨3695984, by rfl⟩ : syracuseStep 4927979 = 7391969) B7391969
theorem B3285319 : Blo 1945435 3285319 := bstep (se 1 (by rfl) ⟨2463989, by rfl⟩ : syracuseStep 3285319 = 4927979) B4927979
theorem B4380425 : Blo 1945435 4380425 := bstep (se 2 (by rfl) ⟨1642659, by rfl⟩ : syracuseStep 4380425 = 3285319) B3285319
theorem B2920283 : Blo 1945435 2920283 := bstep (se 1 (by rfl) ⟨2190212, by rfl⟩ : syracuseStep 2920283 = 4380425) B4380425
theorem B1946855 : Blo 1945435 1946855 := bstep (se 1 (by rfl) ⟨1460141, by rfl⟩ : syracuseStep 1946855 = 2920283) B2920283
theorem B2190217 : Blo 1945435 2190217 := bbase (se 2 (by rfl) ⟨821331, by rfl⟩ : syracuseStep 2190217 = 1642663) (by norm_num)
theorem B2920289 : Blo 1945435 2920289 := bstep (se 2 (by rfl) ⟨1095108, by rfl⟩ : syracuseStep 2920289 = 2190217) B2190217
theorem B1946859 : Blo 1945435 1946859 := bstep (se 1 (by rfl) ⟨1460144, by rfl⟩ : syracuseStep 1946859 = 2920289) B2920289
theorem B94724437 : Blo 1945435 94724437 := bbase (se 10 (by rfl) ⟨138756, by rfl⟩ : syracuseStep 94724437 = 277513) (by norm_num)
theorem B126299249 : Blo 1945435 126299249 := bstep (se 2 (by rfl) ⟨47362218, by rfl⟩ : syracuseStep 126299249 = 94724437) B94724437
theorem B84199499 : Blo 1945435 84199499 := bstep (se 1 (by rfl) ⟨63149624, by rfl⟩ : syracuseStep 84199499 = 126299249) B126299249
theorem B56132999 : Blo 1945435 56132999 := bstep (se 1 (by rfl) ⟨42099749, by rfl⟩ : syracuseStep 56132999 = 84199499) B84199499
theorem B37421999 : Blo 1945435 37421999 := bstep (se 1 (by rfl) ⟨28066499, by rfl⟩ : syracuseStep 37421999 = 56132999) B56132999
theorem B24947999 : Blo 1945435 24947999 := bstep (se 1 (by rfl) ⟨18710999, by rfl⟩ : syracuseStep 24947999 = 37421999) B37421999
theorem B16631999 : Blo 1945435 16631999 := bstep (se 1 (by rfl) ⟨12473999, by rfl⟩ : syracuseStep 16631999 = 24947999) B24947999
theorem B11087999 : Blo 1945435 11087999 := bstep (se 1 (by rfl) ⟨8315999, by rfl⟩ : syracuseStep 11087999 = 16631999) B16631999
theorem B7391999 : Blo 1945435 7391999 := bstep (se 1 (by rfl) ⟨5543999, by rfl⟩ : syracuseStep 7391999 = 11087999) B11087999
theorem B4927999 : Blo 1945435 4927999 := bstep (se 1 (by rfl) ⟨3695999, by rfl⟩ : syracuseStep 4927999 = 7391999) B7391999
theorem B6570665 : Blo 1945435 6570665 := bstep (se 2 (by rfl) ⟨2463999, by rfl⟩ : syracuseStep 6570665 = 4927999) B4927999
theorem B4380443 : Blo 1945435 4380443 := bstep (se 1 (by rfl) ⟨3285332, by rfl⟩ : syracuseStep 4380443 = 6570665) B6570665
theorem B2920295 : Blo 1945435 2920295 := bstep (se 1 (by rfl) ⟨2190221, by rfl⟩ : syracuseStep 2920295 = 4380443) B4380443
theorem B1946863 : Blo 1945435 1946863 := bstep (se 1 (by rfl) ⟨1460147, by rfl⟩ : syracuseStep 1946863 = 2920295) B2920295
theorem B2920301 : Blo 1945435 2920301 := bbase (se 3 (by rfl) ⟨547556, by rfl⟩ : syracuseStep 2920301 = 1095113) (by norm_num)
theorem B1946867 : Blo 1945435 1946867 := bstep (se 1 (by rfl) ⟨1460150, by rfl⟩ : syracuseStep 1946867 = 2920301) B2920301
theorem B4380461 : Blo 1945435 4380461 := bbase (se 3 (by rfl) ⟨821336, by rfl⟩ : syracuseStep 4380461 = 1642673) (by norm_num)
theorem B2920307 : Blo 1945435 2920307 := bstep (se 1 (by rfl) ⟨2190230, by rfl⟩ : syracuseStep 2920307 = 4380461) B4380461
theorem B1946871 : Blo 1945435 1946871 := bstep (se 1 (by rfl) ⟨1460153, by rfl⟩ : syracuseStep 1946871 = 2920307) B2920307
theorem B8316053 : Blo 1945435 8316053 := bbase (se 6 (by rfl) ⟨194907, by rfl⟩ : syracuseStep 8316053 = 389815) (by norm_num)
theorem B5544035 : Blo 1945435 5544035 := bstep (se 1 (by rfl) ⟨4158026, by rfl⟩ : syracuseStep 5544035 = 8316053) B8316053
theorem B3696023 : Blo 1945435 3696023 := bstep (se 1 (by rfl) ⟨2772017, by rfl⟩ : syracuseStep 3696023 = 5544035) B5544035
theorem B2464015 : Blo 1945435 2464015 := bstep (se 1 (by rfl) ⟨1848011, by rfl⟩ : syracuseStep 2464015 = 3696023) B3696023
theorem B3285353 : Blo 1945435 3285353 := bstep (se 2 (by rfl) ⟨1232007, by rfl⟩ : syracuseStep 3285353 = 2464015) B2464015
theorem B2190235 : Blo 1945435 2190235 := bstep (se 1 (by rfl) ⟨1642676, by rfl⟩ : syracuseStep 2190235 = 3285353) B3285353
theorem B2920313 : Blo 1945435 2920313 := bstep (se 2 (by rfl) ⟨1095117, by rfl⟩ : syracuseStep 2920313 = 2190235) B2190235
theorem B1946875 : Blo 1945435 1946875 := bstep (se 1 (by rfl) ⟨1460156, by rfl⟩ : syracuseStep 1946875 = 2920313) B2920313
theorem B12474101 : Blo 1945435 12474101 := bbase (se 5 (by rfl) ⟨584723, by rfl⟩ : syracuseStep 12474101 = 1169447) (by norm_num)
theorem B33264269 : Blo 1945435 33264269 := bstep (se 3 (by rfl) ⟨6237050, by rfl⟩ : syracuseStep 33264269 = 12474101) B12474101
theorem B22176179 : Blo 1945435 22176179 := bstep (se 1 (by rfl) ⟨16632134, by rfl⟩ : syracuseStep 22176179 = 33264269) B33264269
theorem B14784119 : Blo 1945435 14784119 := bstep (se 1 (by rfl) ⟨11088089, by rfl⟩ : syracuseStep 14784119 = 22176179) B22176179
theorem B9856079 : Blo 1945435 9856079 := bstep (se 1 (by rfl) ⟨7392059, by rfl⟩ : syracuseStep 9856079 = 14784119) B14784119
theorem B6570719 : Blo 1945435 6570719 := bstep (se 1 (by rfl) ⟨4928039, by rfl⟩ : syracuseStep 6570719 = 9856079) B9856079
theorem B4380479 : Blo 1945435 4380479 := bstep (se 1 (by rfl) ⟨3285359, by rfl⟩ : syracuseStep 4380479 = 6570719) B6570719
theorem B2920319 : Blo 1945435 2920319 := bstep (se 1 (by rfl) ⟨2190239, by rfl⟩ : syracuseStep 2920319 = 4380479) B4380479
theorem B1946879 : Blo 1945435 1946879 := bstep (se 1 (by rfl) ⟨1460159, by rfl⟩ : syracuseStep 1946879 = 2920319) B2920319
theorem B2920325 : Blo 1945435 2920325 := bbase (se 4 (by rfl) ⟨273780, by rfl⟩ : syracuseStep 2920325 = 547561) (by norm_num)
theorem B1946883 : Blo 1945435 1946883 := bstep (se 1 (by rfl) ⟨1460162, by rfl⟩ : syracuseStep 1946883 = 2920325) B2920325
theorem B3285373 : Blo 1945435 3285373 := bbase (se 3 (by rfl) ⟨616007, by rfl⟩ : syracuseStep 3285373 = 1232015) (by norm_num)
theorem B4380497 : Blo 1945435 4380497 := bstep (se 2 (by rfl) ⟨1642686, by rfl⟩ : syracuseStep 4380497 = 3285373) B3285373
theorem B2920331 : Blo 1945435 2920331 := bstep (se 1 (by rfl) ⟨2190248, by rfl⟩ : syracuseStep 2920331 = 4380497) B4380497
theorem B1946887 : Blo 1945435 1946887 := bstep (se 1 (by rfl) ⟨1460165, by rfl⟩ : syracuseStep 1946887 = 2920331) B2920331
theorem B2190253 : Blo 1945435 2190253 := bbase (se 3 (by rfl) ⟨410672, by rfl⟩ : syracuseStep 2190253 = 821345) (by norm_num)
theorem B2920337 : Blo 1945435 2920337 := bstep (se 2 (by rfl) ⟨1095126, by rfl⟩ : syracuseStep 2920337 = 2190253) B2190253
theorem B1946891 : Blo 1945435 1946891 := bstep (se 1 (by rfl) ⟨1460168, by rfl⟩ : syracuseStep 1946891 = 2920337) B2920337
theorem B6570773 : Blo 1945435 6570773 := bbase (se 6 (by rfl) ⟨154002, by rfl⟩ : syracuseStep 6570773 = 308005) (by norm_num)
theorem B4380515 : Blo 1945435 4380515 := bstep (se 1 (by rfl) ⟨3285386, by rfl⟩ : syracuseStep 4380515 = 6570773) B6570773
theorem B2920343 : Blo 1945435 2920343 := bstep (se 1 (by rfl) ⟨2190257, by rfl⟩ : syracuseStep 2920343 = 4380515) B4380515
theorem B1946895 : Blo 1945435 1946895 := bstep (se 1 (by rfl) ⟨1460171, by rfl⟩ : syracuseStep 1946895 = 2920343) B2920343
theorem B2920349 : Blo 1945435 2920349 := bbase (se 3 (by rfl) ⟨547565, by rfl⟩ : syracuseStep 2920349 = 1095131) (by norm_num)
theorem B1946899 : Blo 1945435 1946899 := bstep (se 1 (by rfl) ⟨1460174, by rfl⟩ : syracuseStep 1946899 = 2920349) B2920349
theorem B4380533 : Blo 1945435 4380533 := bbase (se 5 (by rfl) ⟨205337, by rfl⟩ : syracuseStep 4380533 = 410675) (by norm_num)
theorem B2920355 : Blo 1945435 2920355 := bstep (se 1 (by rfl) ⟨2190266, by rfl⟩ : syracuseStep 2920355 = 4380533) B4380533
theorem B1946903 : Blo 1945435 1946903 := bstep (se 1 (by rfl) ⟨1460177, by rfl⟩ : syracuseStep 1946903 = 2920355) B2920355
theorem B9124597 : Blo 1945435 9124597 := bbase (se 5 (by rfl) ⟨427715, by rfl⟩ : syracuseStep 9124597 = 855431) (by norm_num)
theorem B12166129 : Blo 1945435 12166129 := bstep (se 2 (by rfl) ⟨4562298, by rfl⟩ : syracuseStep 12166129 = 9124597) B9124597
theorem B16221505 : Blo 1945435 16221505 := bstep (se 2 (by rfl) ⟨6083064, by rfl⟩ : syracuseStep 16221505 = 12166129) B12166129
theorem B21628673 : Blo 1945435 21628673 := bstep (se 2 (by rfl) ⟨8110752, by rfl⟩ : syracuseStep 21628673 = 16221505) B16221505
theorem B14419115 : Blo 1945435 14419115 := bstep (se 1 (by rfl) ⟨10814336, by rfl⟩ : syracuseStep 14419115 = 21628673) B21628673
theorem B9612743 : Blo 1945435 9612743 := bstep (se 1 (by rfl) ⟨7209557, by rfl⟩ : syracuseStep 9612743 = 14419115) B14419115
theorem B25633981 : Blo 1945435 25633981 := bstep (se 3 (by rfl) ⟨4806371, by rfl⟩ : syracuseStep 25633981 = 9612743) B9612743
theorem B34178641 : Blo 1945435 34178641 := bstep (se 2 (by rfl) ⟨12816990, by rfl⟩ : syracuseStep 34178641 = 25633981) B25633981
theorem B182286085 : Blo 1945435 182286085 := bstep (se 4 (by rfl) ⟨17089320, by rfl⟩ : syracuseStep 182286085 = 34178641) B34178641
theorem B243048113 : Blo 1945435 243048113 := bstep (se 2 (by rfl) ⟨91143042, by rfl⟩ : syracuseStep 243048113 = 182286085) B182286085
theorem B162032075 : Blo 1945435 162032075 := bstep (se 1 (by rfl) ⟨121524056, by rfl⟩ : syracuseStep 162032075 = 243048113) B243048113
theorem B108021383 : Blo 1945435 108021383 := bstep (se 1 (by rfl) ⟨81016037, by rfl⟩ : syracuseStep 108021383 = 162032075) B162032075
theorem B72014255 : Blo 1945435 72014255 := bstep (se 1 (by rfl) ⟨54010691, by rfl⟩ : syracuseStep 72014255 = 108021383) B108021383
theorem B48009503 : Blo 1945435 48009503 := bstep (se 1 (by rfl) ⟨36007127, by rfl⟩ : syracuseStep 48009503 = 72014255) B72014255
theorem B32006335 : Blo 1945435 32006335 := bstep (se 1 (by rfl) ⟨24004751, by rfl⟩ : syracuseStep 32006335 = 48009503) B48009503
theorem B42675113 : Blo 1945435 42675113 := bstep (se 2 (by rfl) ⟨16003167, by rfl⟩ : syracuseStep 42675113 = 32006335) B32006335
theorem B28450075 : Blo 1945435 28450075 := bstep (se 1 (by rfl) ⟨21337556, by rfl⟩ : syracuseStep 28450075 = 42675113) B42675113
theorem B37933433 : Blo 1945435 37933433 := bstep (se 2 (by rfl) ⟨14225037, by rfl⟩ : syracuseStep 37933433 = 28450075) B28450075
theorem B25288955 : Blo 1945435 25288955 := bstep (se 1 (by rfl) ⟨18966716, by rfl⟩ : syracuseStep 25288955 = 37933433) B37933433
theorem B16859303 : Blo 1945435 16859303 := bstep (se 1 (by rfl) ⟨12644477, by rfl⟩ : syracuseStep 16859303 = 25288955) B25288955
theorem B11239535 : Blo 1945435 11239535 := bstep (se 1 (by rfl) ⟨8429651, by rfl⟩ : syracuseStep 11239535 = 16859303) B16859303
theorem B7493023 : Blo 1945435 7493023 := bstep (se 1 (by rfl) ⟨5619767, by rfl⟩ : syracuseStep 7493023 = 11239535) B11239535
theorem B9990697 : Blo 1945435 9990697 := bstep (se 2 (by rfl) ⟨3746511, by rfl⟩ : syracuseStep 9990697 = 7493023) B7493023
theorem B13320929 : Blo 1945435 13320929 := bstep (se 2 (by rfl) ⟨4995348, by rfl⟩ : syracuseStep 13320929 = 9990697) B9990697
theorem B8880619 : Blo 1945435 8880619 := bstep (se 1 (by rfl) ⟨6660464, by rfl⟩ : syracuseStep 8880619 = 13320929) B13320929
theorem B11840825 : Blo 1945435 11840825 := bstep (se 2 (by rfl) ⟨4440309, by rfl⟩ : syracuseStep 11840825 = 8880619) B8880619
theorem B7893883 : Blo 1945435 7893883 := bstep (se 1 (by rfl) ⟨5920412, by rfl⟩ : syracuseStep 7893883 = 11840825) B11840825
theorem B10525177 : Blo 1945435 10525177 := bstep (se 2 (by rfl) ⟨3946941, by rfl⟩ : syracuseStep 10525177 = 7893883) B7893883
theorem B14033569 : Blo 1945435 14033569 := bstep (se 2 (by rfl) ⟨5262588, by rfl⟩ : syracuseStep 14033569 = 10525177) B10525177
theorem B18711425 : Blo 1945435 18711425 := bstep (se 2 (by rfl) ⟨7016784, by rfl⟩ : syracuseStep 18711425 = 14033569) B14033569
theorem B12474283 : Blo 1945435 12474283 := bstep (se 1 (by rfl) ⟨9355712, by rfl⟩ : syracuseStep 12474283 = 18711425) B18711425
theorem B16632377 : Blo 1945435 16632377 := bstep (se 2 (by rfl) ⟨6237141, by rfl⟩ : syracuseStep 16632377 = 12474283) B12474283
theorem B11088251 : Blo 1945435 11088251 := bstep (se 1 (by rfl) ⟨8316188, by rfl⟩ : syracuseStep 11088251 = 16632377) B16632377
theorem B7392167 : Blo 1945435 7392167 := bstep (se 1 (by rfl) ⟨5544125, by rfl⟩ : syracuseStep 7392167 = 11088251) B11088251
theorem B4928111 : Blo 1945435 4928111 := bstep (se 1 (by rfl) ⟨3696083, by rfl⟩ : syracuseStep 4928111 = 7392167) B7392167
theorem B3285407 : Blo 1945435 3285407 := bstep (se 1 (by rfl) ⟨2464055, by rfl⟩ : syracuseStep 3285407 = 4928111) B4928111
theorem B2190271 : Blo 1945435 2190271 := bstep (se 1 (by rfl) ⟨1642703, by rfl⟩ : syracuseStep 2190271 = 3285407) B3285407
theorem B2920361 : Blo 1945435 2920361 := bstep (se 2 (by rfl) ⟨1095135, by rfl⟩ : syracuseStep 2920361 = 2190271) B2190271
theorem B1946907 : Blo 1945435 1946907 := bstep (se 1 (by rfl) ⟨1460180, by rfl⟩ : syracuseStep 1946907 = 2920361) B2920361
theorem B7392181 : Blo 1945435 7392181 := bbase (se 5 (by rfl) ⟨346508, by rfl⟩ : syracuseStep 7392181 = 693017) (by norm_num)
theorem B9856241 : Blo 1945435 9856241 := bstep (se 2 (by rfl) ⟨3696090, by rfl⟩ : syracuseStep 9856241 = 7392181) B7392181
theorem B6570827 : Blo 1945435 6570827 := bstep (se 1 (by rfl) ⟨4928120, by rfl⟩ : syracuseStep 6570827 = 9856241) B9856241
theorem B4380551 : Blo 1945435 4380551 := bstep (se 1 (by rfl) ⟨3285413, by rfl⟩ : syracuseStep 4380551 = 6570827) B6570827
theorem B2920367 : Blo 1945435 2920367 := bstep (se 1 (by rfl) ⟨2190275, by rfl⟩ : syracuseStep 2920367 = 4380551) B4380551
theorem B1946911 : Blo 1945435 1946911 := bstep (se 1 (by rfl) ⟨1460183, by rfl⟩ : syracuseStep 1946911 = 2920367) B2920367
theorem B2920373 : Blo 1945435 2920373 := bbase (se 5 (by rfl) ⟨136892, by rfl⟩ : syracuseStep 2920373 = 273785) (by norm_num)
theorem B1946915 : Blo 1945435 1946915 := bstep (se 1 (by rfl) ⟨1460186, by rfl⟩ : syracuseStep 1946915 = 2920373) B2920373
theorem B4928141 : Blo 1945435 4928141 := bbase (se 3 (by rfl) ⟨924026, by rfl⟩ : syracuseStep 4928141 = 1848053) (by norm_num)
theorem B3285427 : Blo 1945435 3285427 := bstep (se 1 (by rfl) ⟨2464070, by rfl⟩ : syracuseStep 3285427 = 4928141) B4928141
theorem B4380569 : Blo 1945435 4380569 := bstep (se 2 (by rfl) ⟨1642713, by rfl⟩ : syracuseStep 4380569 = 3285427) B3285427
theorem B2920379 : Blo 1945435 2920379 := bstep (se 1 (by rfl) ⟨2190284, by rfl⟩ : syracuseStep 2920379 = 4380569) B4380569
theorem B1946919 : Blo 1945435 1946919 := bstep (se 1 (by rfl) ⟨1460189, by rfl⟩ : syracuseStep 1946919 = 2920379) B2920379
theorem B2190289 : Blo 1945435 2190289 := bbase (se 2 (by rfl) ⟨821358, by rfl⟩ : syracuseStep 2190289 = 1642717) (by norm_num)
theorem B2920385 : Blo 1945435 2920385 := bstep (se 2 (by rfl) ⟨1095144, by rfl⟩ : syracuseStep 2920385 = 2190289) B2190289
theorem B1946923 : Blo 1945435 1946923 := bstep (se 1 (by rfl) ⟨1460192, by rfl⟩ : syracuseStep 1946923 = 2920385) B2920385
theorem B3508429 : Blo 1945435 3508429 := bbase (se 3 (by rfl) ⟨657830, by rfl⟩ : syracuseStep 3508429 = 1315661) (by norm_num)
theorem B4677905 : Blo 1945435 4677905 := bstep (se 2 (by rfl) ⟨1754214, by rfl⟩ : syracuseStep 4677905 = 3508429) B3508429
theorem B3118603 : Blo 1945435 3118603 := bstep (se 1 (by rfl) ⟨2338952, by rfl⟩ : syracuseStep 3118603 = 4677905) B4677905
theorem B4158137 : Blo 1945435 4158137 := bstep (se 2 (by rfl) ⟨1559301, by rfl⟩ : syracuseStep 4158137 = 3118603) B3118603
theorem B2772091 : Blo 1945435 2772091 := bstep (se 1 (by rfl) ⟨2079068, by rfl⟩ : syracuseStep 2772091 = 4158137) B4158137
theorem B3696121 : Blo 1945435 3696121 := bstep (se 2 (by rfl) ⟨1386045, by rfl⟩ : syracuseStep 3696121 = 2772091) B2772091
theorem B4928161 : Blo 1945435 4928161 := bstep (se 2 (by rfl) ⟨1848060, by rfl⟩ : syracuseStep 4928161 = 3696121) B3696121
theorem B6570881 : Blo 1945435 6570881 := bstep (se 2 (by rfl) ⟨2464080, by rfl⟩ : syracuseStep 6570881 = 4928161) B4928161
theorem B4380587 : Blo 1945435 4380587 := bstep (se 1 (by rfl) ⟨3285440, by rfl⟩ : syracuseStep 4380587 = 6570881) B6570881
theorem B2920391 : Blo 1945435 2920391 := bstep (se 1 (by rfl) ⟨2190293, by rfl⟩ : syracuseStep 2920391 = 4380587) B4380587
theorem B1946927 : Blo 1945435 1946927 := bstep (se 1 (by rfl) ⟨1460195, by rfl⟩ : syracuseStep 1946927 = 2920391) B2920391
theorem B2920397 : Blo 1945435 2920397 := bbase (se 3 (by rfl) ⟨547574, by rfl⟩ : syracuseStep 2920397 = 1095149) (by norm_num)
theorem B1946931 : Blo 1945435 1946931 := bstep (se 1 (by rfl) ⟨1460198, by rfl⟩ : syracuseStep 1946931 = 2920397) B2920397
theorem B4380605 : Blo 1945435 4380605 := bbase (se 3 (by rfl) ⟨821363, by rfl⟩ : syracuseStep 4380605 = 1642727) (by norm_num)
theorem B2920403 : Blo 1945435 2920403 := bstep (se 1 (by rfl) ⟨2190302, by rfl⟩ : syracuseStep 2920403 = 4380605) B4380605
theorem B1946935 : Blo 1945435 1946935 := bstep (se 1 (by rfl) ⟨1460201, by rfl⟩ : syracuseStep 1946935 = 2920403) B2920403
theorem B3285461 : Blo 1945435 3285461 := bbase (se 7 (by rfl) ⟨38501, by rfl⟩ : syracuseStep 3285461 = 77003) (by norm_num)
theorem B2190307 : Blo 1945435 2190307 := bstep (se 1 (by rfl) ⟨1642730, by rfl⟩ : syracuseStep 2190307 = 3285461) B3285461
theorem B2920409 : Blo 1945435 2920409 := bstep (se 2 (by rfl) ⟨1095153, by rfl⟩ : syracuseStep 2920409 = 2190307) B2190307
theorem B1946939 : Blo 1945435 1946939 := bstep (se 1 (by rfl) ⟨1460204, by rfl⟩ : syracuseStep 1946939 = 2920409) B2920409
theorem B8316341 : Blo 1945435 8316341 := bbase (se 5 (by rfl) ⟨389828, by rfl⟩ : syracuseStep 8316341 = 779657) (by norm_num)
theorem B5544227 : Blo 1945435 5544227 := bstep (se 1 (by rfl) ⟨4158170, by rfl⟩ : syracuseStep 5544227 = 8316341) B8316341
theorem B14784605 : Blo 1945435 14784605 := bstep (se 3 (by rfl) ⟨2772113, by rfl⟩ : syracuseStep 14784605 = 5544227) B5544227
theorem B9856403 : Blo 1945435 9856403 := bstep (se 1 (by rfl) ⟨7392302, by rfl⟩ : syracuseStep 9856403 = 14784605) B14784605
theorem B6570935 : Blo 1945435 6570935 := bstep (se 1 (by rfl) ⟨4928201, by rfl⟩ : syracuseStep 6570935 = 9856403) B9856403
theorem B4380623 : Blo 1945435 4380623 := bstep (se 1 (by rfl) ⟨3285467, by rfl⟩ : syracuseStep 4380623 = 6570935) B6570935
theorem B2920415 : Blo 1945435 2920415 := bstep (se 1 (by rfl) ⟨2190311, by rfl⟩ : syracuseStep 2920415 = 4380623) B4380623
theorem B1946943 : Blo 1945435 1946943 := bstep (se 1 (by rfl) ⟨1460207, by rfl⟩ : syracuseStep 1946943 = 2920415) B2920415
theorem B2920421 : Blo 1945435 2920421 := bbase (se 4 (by rfl) ⟨273789, by rfl⟩ : syracuseStep 2920421 = 547579) (by norm_num)
theorem B1946947 : Blo 1945435 1946947 := bstep (se 1 (by rfl) ⟨1460210, by rfl⟩ : syracuseStep 1946947 = 2920421) B2920421
theorem B9355925 : Blo 1945435 9355925 := bbase (se 6 (by rfl) ⟨219279, by rfl⟩ : syracuseStep 9355925 = 438559) (by norm_num)
theorem B6237283 : Blo 1945435 6237283 := bstep (se 1 (by rfl) ⟨4677962, by rfl⟩ : syracuseStep 6237283 = 9355925) B9355925
theorem B8316377 : Blo 1945435 8316377 := bstep (se 2 (by rfl) ⟨3118641, by rfl⟩ : syracuseStep 8316377 = 6237283) B6237283
theorem B5544251 : Blo 1945435 5544251 := bstep (se 1 (by rfl) ⟨4158188, by rfl⟩ : syracuseStep 5544251 = 8316377) B8316377
theorem B3696167 : Blo 1945435 3696167 := bstep (se 1 (by rfl) ⟨2772125, by rfl⟩ : syracuseStep 3696167 = 5544251) B5544251
theorem B2464111 : Blo 1945435 2464111 := bstep (se 1 (by rfl) ⟨1848083, by rfl⟩ : syracuseStep 2464111 = 3696167) B3696167
theorem B3285481 : Blo 1945435 3285481 := bstep (se 2 (by rfl) ⟨1232055, by rfl⟩ : syracuseStep 3285481 = 2464111) B2464111
theorem B4380641 : Blo 1945435 4380641 := bstep (se 2 (by rfl) ⟨1642740, by rfl⟩ : syracuseStep 4380641 = 3285481) B3285481
theorem B2920427 : Blo 1945435 2920427 := bstep (se 1 (by rfl) ⟨2190320, by rfl⟩ : syracuseStep 2920427 = 4380641) B4380641
theorem B1946951 : Blo 1945435 1946951 := bstep (se 1 (by rfl) ⟨1460213, by rfl⟩ : syracuseStep 1946951 = 2920427) B2920427
theorem B2190325 : Blo 1945435 2190325 := bbase (se 5 (by rfl) ⟨102671, by rfl⟩ : syracuseStep 2190325 = 205343) (by norm_num)
theorem B2920433 : Blo 1945435 2920433 := bstep (se 2 (by rfl) ⟨1095162, by rfl⟩ : syracuseStep 2920433 = 2190325) B2190325
theorem B1946955 : Blo 1945435 1946955 := bstep (se 1 (by rfl) ⟨1460216, by rfl⟩ : syracuseStep 1946955 = 2920433) B2920433
theorem B2464121 : Blo 1945435 2464121 := bbase (se 2 (by rfl) ⟨924045, by rfl⟩ : syracuseStep 2464121 = 1848091) (by norm_num)
theorem B6570989 : Blo 1945435 6570989 := bstep (se 3 (by rfl) ⟨1232060, by rfl⟩ : syracuseStep 6570989 = 2464121) B2464121
theorem B4380659 : Blo 1945435 4380659 := bstep (se 1 (by rfl) ⟨3285494, by rfl⟩ : syracuseStep 4380659 = 6570989) B6570989
theorem B2920439 : Blo 1945435 2920439 := bstep (se 1 (by rfl) ⟨2190329, by rfl⟩ : syracuseStep 2920439 = 4380659) B4380659
theorem B1946959 : Blo 1945435 1946959 := bstep (se 1 (by rfl) ⟨1460219, by rfl⟩ : syracuseStep 1946959 = 2920439) B2920439
theorem B2920445 : Blo 1945435 2920445 := bbase (se 3 (by rfl) ⟨547583, by rfl⟩ : syracuseStep 2920445 = 1095167) (by norm_num)
theorem B1946963 : Blo 1945435 1946963 := bstep (se 1 (by rfl) ⟨1460222, by rfl⟩ : syracuseStep 1946963 = 2920445) B2920445
theorem B4380677 : Blo 1945435 4380677 := bbase (se 4 (by rfl) ⟨410688, by rfl⟩ : syracuseStep 4380677 = 821377) (by norm_num)
theorem B2920451 : Blo 1945435 2920451 := bstep (se 1 (by rfl) ⟨2190338, by rfl⟩ : syracuseStep 2920451 = 4380677) B4380677
theorem B1946967 : Blo 1945435 1946967 := bstep (se 1 (by rfl) ⟨1460225, by rfl⟩ : syracuseStep 1946967 = 2920451) B2920451
theorem B3696205 : Blo 1945435 3696205 := bbase (se 3 (by rfl) ⟨693038, by rfl⟩ : syracuseStep 3696205 = 1386077) (by norm_num)
theorem B4928273 : Blo 1945435 4928273 := bstep (se 2 (by rfl) ⟨1848102, by rfl⟩ : syracuseStep 4928273 = 3696205) B3696205
theorem B3285515 : Blo 1945435 3285515 := bstep (se 1 (by rfl) ⟨2464136, by rfl⟩ : syracuseStep 3285515 = 4928273) B4928273
theorem B2190343 : Blo 1945435 2190343 := bstep (se 1 (by rfl) ⟨1642757, by rfl⟩ : syracuseStep 2190343 = 3285515) B3285515
theorem B2920457 : Blo 1945435 2920457 := bstep (se 2 (by rfl) ⟨1095171, by rfl⟩ : syracuseStep 2920457 = 2190343) B2190343
theorem B1946971 : Blo 1945435 1946971 := bstep (se 1 (by rfl) ⟨1460228, by rfl⟩ : syracuseStep 1946971 = 2920457) B2920457
theorem B9856565 : Blo 1945435 9856565 := bbase (se 5 (by rfl) ⟨462026, by rfl⟩ : syracuseStep 9856565 = 924053) (by norm_num)
theorem B6571043 : Blo 1945435 6571043 := bstep (se 1 (by rfl) ⟨4928282, by rfl⟩ : syracuseStep 6571043 = 9856565) B9856565
theorem B4380695 : Blo 1945435 4380695 := bstep (se 1 (by rfl) ⟨3285521, by rfl⟩ : syracuseStep 4380695 = 6571043) B6571043
theorem B2920463 : Blo 1945435 2920463 := bstep (se 1 (by rfl) ⟨2190347, by rfl⟩ : syracuseStep 2920463 = 4380695) B4380695
theorem B1946975 : Blo 1945435 1946975 := bstep (se 1 (by rfl) ⟨1460231, by rfl⟩ : syracuseStep 1946975 = 2920463) B2920463
theorem B2920469 : Blo 1945435 2920469 := bbase (se 6 (by rfl) ⟨68448, by rfl⟩ : syracuseStep 2920469 = 136897) (by norm_num)
theorem B1946979 : Blo 1945435 1946979 := bstep (se 1 (by rfl) ⟨1460234, by rfl⟩ : syracuseStep 1946979 = 2920469) B2920469
theorem B2631397 : Blo 1945435 2631397 := bbase (se 4 (by rfl) ⟨246693, by rfl⟩ : syracuseStep 2631397 = 493387) (by norm_num)
theorem B3508529 : Blo 1945435 3508529 := bstep (se 2 (by rfl) ⟨1315698, by rfl⟩ : syracuseStep 3508529 = 2631397) B2631397
theorem B9356077 : Blo 1945435 9356077 := bstep (se 3 (by rfl) ⟨1754264, by rfl⟩ : syracuseStep 9356077 = 3508529) B3508529
theorem B12474769 : Blo 1945435 12474769 := bstep (se 2 (by rfl) ⟨4678038, by rfl⟩ : syracuseStep 12474769 = 9356077) B9356077
theorem B16633025 : Blo 1945435 16633025 := bstep (se 2 (by rfl) ⟨6237384, by rfl⟩ : syracuseStep 16633025 = 12474769) B12474769
theorem B11088683 : Blo 1945435 11088683 := bstep (se 1 (by rfl) ⟨8316512, by rfl⟩ : syracuseStep 11088683 = 16633025) B16633025
theorem B7392455 : Blo 1945435 7392455 := bstep (se 1 (by rfl) ⟨5544341, by rfl⟩ : syracuseStep 7392455 = 11088683) B11088683
theorem B4928303 : Blo 1945435 4928303 := bstep (se 1 (by rfl) ⟨3696227, by rfl⟩ : syracuseStep 4928303 = 7392455) B7392455
theorem B3285535 : Blo 1945435 3285535 := bstep (se 1 (by rfl) ⟨2464151, by rfl⟩ : syracuseStep 3285535 = 4928303) B4928303
theorem B4380713 : Blo 1945435 4380713 := bstep (se 2 (by rfl) ⟨1642767, by rfl⟩ : syracuseStep 4380713 = 3285535) B3285535
theorem B2920475 : Blo 1945435 2920475 := bstep (se 1 (by rfl) ⟨2190356, by rfl⟩ : syracuseStep 2920475 = 4380713) B4380713
theorem B1946983 : Blo 1945435 1946983 := bstep (se 1 (by rfl) ⟨1460237, by rfl⟩ : syracuseStep 1946983 = 2920475) B2920475
theorem B2190361 : Blo 1945435 2190361 := bbase (se 2 (by rfl) ⟨821385, by rfl⟩ : syracuseStep 2190361 = 1642771) (by norm_num)
theorem B2920481 : Blo 1945435 2920481 := bstep (se 2 (by rfl) ⟨1095180, by rfl⟩ : syracuseStep 2920481 = 2190361) B2190361
theorem B1946987 : Blo 1945435 1946987 := bstep (se 1 (by rfl) ⟨1460240, by rfl⟩ : syracuseStep 1946987 = 2920481) B2920481
theorem B7392485 : Blo 1945435 7392485 := bbase (se 4 (by rfl) ⟨693045, by rfl⟩ : syracuseStep 7392485 = 1386091) (by norm_num)
theorem B4928323 : Blo 1945435 4928323 := bstep (se 1 (by rfl) ⟨3696242, by rfl⟩ : syracuseStep 4928323 = 7392485) B7392485
theorem B6571097 : Blo 1945435 6571097 := bstep (se 2 (by rfl) ⟨2464161, by rfl⟩ : syracuseStep 6571097 = 4928323) B4928323
theorem B4380731 : Blo 1945435 4380731 := bstep (se 1 (by rfl) ⟨3285548, by rfl⟩ : syracuseStep 4380731 = 6571097) B6571097
theorem B2920487 : Blo 1945435 2920487 := bstep (se 1 (by rfl) ⟨2190365, by rfl⟩ : syracuseStep 2920487 = 4380731) B4380731
theorem B1946991 : Blo 1945435 1946991 := bstep (se 1 (by rfl) ⟨1460243, by rfl⟩ : syracuseStep 1946991 = 2920487) B2920487
theorem B2920493 : Blo 1945435 2920493 := bbase (se 3 (by rfl) ⟨547592, by rfl⟩ : syracuseStep 2920493 = 1095185) (by norm_num)
theorem B1946995 : Blo 1945435 1946995 := bstep (se 1 (by rfl) ⟨1460246, by rfl⟩ : syracuseStep 1946995 = 2920493) B2920493
theorem B4380749 : Blo 1945435 4380749 := bbase (se 3 (by rfl) ⟨821390, by rfl⟩ : syracuseStep 4380749 = 1642781) (by norm_num)
theorem B2920499 : Blo 1945435 2920499 := bstep (se 1 (by rfl) ⟨2190374, by rfl⟩ : syracuseStep 2920499 = 4380749) B4380749
theorem B1946999 : Blo 1945435 1946999 := bstep (se 1 (by rfl) ⟨1460249, by rfl⟩ : syracuseStep 1946999 = 2920499) B2920499
theorem B2464177 : Blo 1945435 2464177 := bbase (se 2 (by rfl) ⟨924066, by rfl⟩ : syracuseStep 2464177 = 1848133) (by norm_num)
theorem B3285569 : Blo 1945435 3285569 := bstep (se 2 (by rfl) ⟨1232088, by rfl⟩ : syracuseStep 3285569 = 2464177) B2464177
theorem B2190379 : Blo 1945435 2190379 := bstep (se 1 (by rfl) ⟨1642784, by rfl⟩ : syracuseStep 2190379 = 3285569) B3285569
theorem B2920505 : Blo 1945435 2920505 := bstep (se 2 (by rfl) ⟨1095189, by rfl⟩ : syracuseStep 2920505 = 2190379) B2190379
theorem B1947003 : Blo 1945435 1947003 := bstep (se 1 (by rfl) ⟨1460252, by rfl⟩ : syracuseStep 1947003 = 2920505) B2920505
theorem B6237461 : Blo 1945435 6237461 := bbase (se 6 (by rfl) ⟨146190, by rfl⟩ : syracuseStep 6237461 = 292381) (by norm_num)
theorem B4158307 : Blo 1945435 4158307 := bstep (se 1 (by rfl) ⟨3118730, by rfl⟩ : syracuseStep 4158307 = 6237461) B6237461
theorem B22177637 : Blo 1945435 22177637 := bstep (se 4 (by rfl) ⟨2079153, by rfl⟩ : syracuseStep 22177637 = 4158307) B4158307
theorem B14785091 : Blo 1945435 14785091 := bstep (se 1 (by rfl) ⟨11088818, by rfl⟩ : syracuseStep 14785091 = 22177637) B22177637
theorem B9856727 : Blo 1945435 9856727 := bstep (se 1 (by rfl) ⟨7392545, by rfl⟩ : syracuseStep 9856727 = 14785091) B14785091
theorem B6571151 : Blo 1945435 6571151 := bstep (se 1 (by rfl) ⟨4928363, by rfl⟩ : syracuseStep 6571151 = 9856727) B9856727
theorem B4380767 : Blo 1945435 4380767 := bstep (se 1 (by rfl) ⟨3285575, by rfl⟩ : syracuseStep 4380767 = 6571151) B6571151
theorem B2920511 : Blo 1945435 2920511 := bstep (se 1 (by rfl) ⟨2190383, by rfl⟩ : syracuseStep 2920511 = 4380767) B4380767
theorem B1947007 : Blo 1945435 1947007 := bstep (se 1 (by rfl) ⟨1460255, by rfl⟩ : syracuseStep 1947007 = 2920511) B2920511
theorem B2920517 : Blo 1945435 2920517 := bbase (se 4 (by rfl) ⟨273798, by rfl⟩ : syracuseStep 2920517 = 547597) (by norm_num)
theorem B1947011 : Blo 1945435 1947011 := bstep (se 1 (by rfl) ⟨1460258, by rfl⟩ : syracuseStep 1947011 = 2920517) B2920517
theorem B3285589 : Blo 1945435 3285589 := bbase (se 8 (by rfl) ⟨19251, by rfl⟩ : syracuseStep 3285589 = 38503) (by norm_num)
theorem B4380785 : Blo 1945435 4380785 := bstep (se 2 (by rfl) ⟨1642794, by rfl⟩ : syracuseStep 4380785 = 3285589) B3285589
theorem B2920523 : Blo 1945435 2920523 := bstep (se 1 (by rfl) ⟨2190392, by rfl⟩ : syracuseStep 2920523 = 4380785) B4380785
theorem B1947015 : Blo 1945435 1947015 := bstep (se 1 (by rfl) ⟨1460261, by rfl⟩ : syracuseStep 1947015 = 2920523) B2920523
theorem B2190397 : Blo 1945435 2190397 := bbase (se 3 (by rfl) ⟨410699, by rfl⟩ : syracuseStep 2190397 = 821399) (by norm_num)
theorem B2920529 : Blo 1945435 2920529 := bstep (se 2 (by rfl) ⟨1095198, by rfl⟩ : syracuseStep 2920529 = 2190397) B2190397
theorem B1947019 : Blo 1945435 1947019 := bstep (se 1 (by rfl) ⟨1460264, by rfl⟩ : syracuseStep 1947019 = 2920529) B2920529
theorem B6571205 : Blo 1945435 6571205 := bbase (se 4 (by rfl) ⟨616050, by rfl⟩ : syracuseStep 6571205 = 1232101) (by norm_num)
theorem B4380803 : Blo 1945435 4380803 := bstep (se 1 (by rfl) ⟨3285602, by rfl⟩ : syracuseStep 4380803 = 6571205) B6571205
theorem B2920535 : Blo 1945435 2920535 := bstep (se 1 (by rfl) ⟨2190401, by rfl⟩ : syracuseStep 2920535 = 4380803) B4380803
theorem B1947023 : Blo 1945435 1947023 := bstep (se 1 (by rfl) ⟨1460267, by rfl⟩ : syracuseStep 1947023 = 2920535) B2920535
theorem B2920541 : Blo 1945435 2920541 := bbase (se 3 (by rfl) ⟨547601, by rfl⟩ : syracuseStep 2920541 = 1095203) (by norm_num)
theorem B1947027 : Blo 1945435 1947027 := bstep (se 1 (by rfl) ⟨1460270, by rfl⟩ : syracuseStep 1947027 = 2920541) B2920541
theorem B4380821 : Blo 1945435 4380821 := bbase (se 6 (by rfl) ⟨102675, by rfl⟩ : syracuseStep 4380821 = 205351) (by norm_num)
theorem B2920547 : Blo 1945435 2920547 := bstep (se 1 (by rfl) ⟨2190410, by rfl⟩ : syracuseStep 2920547 = 4380821) B4380821
theorem B1947031 : Blo 1945435 1947031 := bstep (se 1 (by rfl) ⟨1460273, by rfl⟩ : syracuseStep 1947031 = 2920547) B2920547
theorem B2772245 : Blo 1945435 2772245 := bbase (se 6 (by rfl) ⟨64974, by rfl⟩ : syracuseStep 2772245 = 129949) (by norm_num)
theorem B7392653 : Blo 1945435 7392653 := bstep (se 3 (by rfl) ⟨1386122, by rfl⟩ : syracuseStep 7392653 = 2772245) B2772245
theorem B4928435 : Blo 1945435 4928435 := bstep (se 1 (by rfl) ⟨3696326, by rfl⟩ : syracuseStep 4928435 = 7392653) B7392653
theorem B3285623 : Blo 1945435 3285623 := bstep (se 1 (by rfl) ⟨2464217, by rfl⟩ : syracuseStep 3285623 = 4928435) B4928435
theorem B2190415 : Blo 1945435 2190415 := bstep (se 1 (by rfl) ⟨1642811, by rfl⟩ : syracuseStep 2190415 = 3285623) B3285623
theorem B2920553 : Blo 1945435 2920553 := bstep (se 2 (by rfl) ⟨1095207, by rfl⟩ : syracuseStep 2920553 = 2190415) B2190415
theorem B1947035 : Blo 1945435 1947035 := bstep (se 1 (by rfl) ⟨1460276, by rfl⟩ : syracuseStep 1947035 = 2920553) B2920553
theorem B2220305 : Blo 1945435 2220305 := bbase (se 2 (by rfl) ⟨832614, by rfl⟩ : syracuseStep 2220305 = 1665229) (by norm_num)
theorem B5920813 : Blo 1945435 5920813 := bstep (se 3 (by rfl) ⟨1110152, by rfl⟩ : syracuseStep 5920813 = 2220305) B2220305
theorem B7894417 : Blo 1945435 7894417 := bstep (se 2 (by rfl) ⟨2960406, by rfl⟩ : syracuseStep 7894417 = 5920813) B5920813
theorem B10525889 : Blo 1945435 10525889 := bstep (se 2 (by rfl) ⟨3947208, by rfl⟩ : syracuseStep 10525889 = 7894417) B7894417
theorem B28069037 : Blo 1945435 28069037 := bstep (se 3 (by rfl) ⟨5262944, by rfl⟩ : syracuseStep 28069037 = 10525889) B10525889
theorem B18712691 : Blo 1945435 18712691 := bstep (se 1 (by rfl) ⟨14034518, by rfl⟩ : syracuseStep 18712691 = 28069037) B28069037
theorem B12475127 : Blo 1945435 12475127 := bstep (se 1 (by rfl) ⟨9356345, by rfl⟩ : syracuseStep 12475127 = 18712691) B18712691
theorem B8316751 : Blo 1945435 8316751 := bstep (se 1 (by rfl) ⟨6237563, by rfl⟩ : syracuseStep 8316751 = 12475127) B12475127
theorem B11089001 : Blo 1945435 11089001 := bstep (se 2 (by rfl) ⟨4158375, by rfl⟩ : syracuseStep 11089001 = 8316751) B8316751
theorem B7392667 : Blo 1945435 7392667 := bstep (se 1 (by rfl) ⟨5544500, by rfl⟩ : syracuseStep 7392667 = 11089001) B11089001
theorem B9856889 : Blo 1945435 9856889 := bstep (se 2 (by rfl) ⟨3696333, by rfl⟩ : syracuseStep 9856889 = 7392667) B7392667
theorem B6571259 : Blo 1945435 6571259 := bstep (se 1 (by rfl) ⟨4928444, by rfl⟩ : syracuseStep 6571259 = 9856889) B9856889
theorem B4380839 : Blo 1945435 4380839 := bstep (se 1 (by rfl) ⟨3285629, by rfl⟩ : syracuseStep 4380839 = 6571259) B6571259
theorem B2920559 : Blo 1945435 2920559 := bstep (se 1 (by rfl) ⟨2190419, by rfl⟩ : syracuseStep 2920559 = 4380839) B4380839
theorem B1947039 : Blo 1945435 1947039 := bstep (se 1 (by rfl) ⟨1460279, by rfl⟩ : syracuseStep 1947039 = 2920559) B2920559
theorem B2920565 : Blo 1945435 2920565 := bbase (se 5 (by rfl) ⟨136901, by rfl⟩ : syracuseStep 2920565 = 273803) (by norm_num)
theorem B1947043 : Blo 1945435 1947043 := bstep (se 1 (by rfl) ⟨1460282, by rfl⟩ : syracuseStep 1947043 = 2920565) B2920565
theorem B3696349 : Blo 1945435 3696349 := bbase (se 3 (by rfl) ⟨693065, by rfl⟩ : syracuseStep 3696349 = 1386131) (by norm_num)
theorem B4928465 : Blo 1945435 4928465 := bstep (se 2 (by rfl) ⟨1848174, by rfl⟩ : syracuseStep 4928465 = 3696349) B3696349
theorem B3285643 : Blo 1945435 3285643 := bstep (se 1 (by rfl) ⟨2464232, by rfl⟩ : syracuseStep 3285643 = 4928465) B4928465
theorem B4380857 : Blo 1945435 4380857 := bstep (se 2 (by rfl) ⟨1642821, by rfl⟩ : syracuseStep 4380857 = 3285643) B3285643
theorem B2920571 : Blo 1945435 2920571 := bstep (se 1 (by rfl) ⟨2190428, by rfl⟩ : syracuseStep 2920571 = 4380857) B4380857
theorem B1947047 : Blo 1945435 1947047 := bstep (se 1 (by rfl) ⟨1460285, by rfl⟩ : syracuseStep 1947047 = 2920571) B2920571
theorem B2190433 : Blo 1945435 2190433 := bbase (se 2 (by rfl) ⟨821412, by rfl⟩ : syracuseStep 2190433 = 1642825) (by norm_num)
theorem B2920577 : Blo 1945435 2920577 := bstep (se 2 (by rfl) ⟨1095216, by rfl⟩ : syracuseStep 2920577 = 2190433) B2190433
theorem B1947051 : Blo 1945435 1947051 := bstep (se 1 (by rfl) ⟨1460288, by rfl⟩ : syracuseStep 1947051 = 2920577) B2920577
theorem B4928485 : Blo 1945435 4928485 := bbase (se 4 (by rfl) ⟨462045, by rfl⟩ : syracuseStep 4928485 = 924091) (by norm_num)
theorem B6571313 : Blo 1945435 6571313 := bstep (se 2 (by rfl) ⟨2464242, by rfl⟩ : syracuseStep 6571313 = 4928485) B4928485
theorem B4380875 : Blo 1945435 4380875 := bstep (se 1 (by rfl) ⟨3285656, by rfl⟩ : syracuseStep 4380875 = 6571313) B6571313
theorem B2920583 : Blo 1945435 2920583 := bstep (se 1 (by rfl) ⟨2190437, by rfl⟩ : syracuseStep 2920583 = 4380875) B4380875
theorem B1947055 : Blo 1945435 1947055 := bstep (se 1 (by rfl) ⟨1460291, by rfl⟩ : syracuseStep 1947055 = 2920583) B2920583
theorem B2920589 : Blo 1945435 2920589 := bbase (se 3 (by rfl) ⟨547610, by rfl⟩ : syracuseStep 2920589 = 1095221) (by norm_num)
theorem B1947059 : Blo 1945435 1947059 := bstep (se 1 (by rfl) ⟨1460294, by rfl⟩ : syracuseStep 1947059 = 2920589) B2920589
theorem B4380893 : Blo 1945435 4380893 := bbase (se 3 (by rfl) ⟨821417, by rfl⟩ : syracuseStep 4380893 = 1642835) (by norm_num)
theorem B2920595 : Blo 1945435 2920595 := bstep (se 1 (by rfl) ⟨2190446, by rfl⟩ : syracuseStep 2920595 = 4380893) B4380893
theorem B1947063 : Blo 1945435 1947063 := bstep (se 1 (by rfl) ⟨1460297, by rfl⟩ : syracuseStep 1947063 = 2920595) B2920595
theorem B3285677 : Blo 1945435 3285677 := bbase (se 3 (by rfl) ⟨616064, by rfl⟩ : syracuseStep 3285677 = 1232129) (by norm_num)
theorem B2190451 : Blo 1945435 2190451 := bstep (se 1 (by rfl) ⟨1642838, by rfl⟩ : syracuseStep 2190451 = 3285677) B3285677
theorem B2920601 : Blo 1945435 2920601 := bstep (se 2 (by rfl) ⟨1095225, by rfl⟩ : syracuseStep 2920601 = 2190451) B2190451
theorem B1947067 : Blo 1945435 1947067 := bstep (se 1 (by rfl) ⟨1460300, by rfl⟩ : syracuseStep 1947067 = 2920601) B2920601
theorem B4215181 : Blo 1945435 4215181 := bbase (se 3 (by rfl) ⟨790346, by rfl⟩ : syracuseStep 4215181 = 1580693) (by norm_num)
theorem B5620241 : Blo 1945435 5620241 := bstep (se 2 (by rfl) ⟨2107590, by rfl⟩ : syracuseStep 5620241 = 4215181) B4215181
theorem B3746827 : Blo 1945435 3746827 := bstep (se 1 (by rfl) ⟨2810120, by rfl⟩ : syracuseStep 3746827 = 5620241) B5620241
theorem B4995769 : Blo 1945435 4995769 := bstep (se 2 (by rfl) ⟨1873413, by rfl⟩ : syracuseStep 4995769 = 3746827) B3746827
theorem B6661025 : Blo 1945435 6661025 := bstep (se 2 (by rfl) ⟨2497884, by rfl⟩ : syracuseStep 6661025 = 4995769) B4995769
theorem B4440683 : Blo 1945435 4440683 := bstep (se 1 (by rfl) ⟨3330512, by rfl⟩ : syracuseStep 4440683 = 6661025) B6661025
theorem B2960455 : Blo 1945435 2960455 := bstep (se 1 (by rfl) ⟨2220341, by rfl⟩ : syracuseStep 2960455 = 4440683) B4440683
theorem B3947273 : Blo 1945435 3947273 := bstep (se 2 (by rfl) ⟨1480227, by rfl⟩ : syracuseStep 3947273 = 2960455) B2960455
theorem B42104245 : Blo 1945435 42104245 := bstep (se 5 (by rfl) ⟨1973636, by rfl⟩ : syracuseStep 42104245 = 3947273) B3947273
theorem B56138993 : Blo 1945435 56138993 := bstep (se 2 (by rfl) ⟨21052122, by rfl⟩ : syracuseStep 56138993 = 42104245) B42104245
theorem B37425995 : Blo 1945435 37425995 := bstep (se 1 (by rfl) ⟨28069496, by rfl⟩ : syracuseStep 37425995 = 56138993) B56138993
theorem B24950663 : Blo 1945435 24950663 := bstep (se 1 (by rfl) ⟨18712997, by rfl⟩ : syracuseStep 24950663 = 37425995) B37425995
theorem B16633775 : Blo 1945435 16633775 := bstep (se 1 (by rfl) ⟨12475331, by rfl⟩ : syracuseStep 16633775 = 24950663) B24950663
theorem B11089183 : Blo 1945435 11089183 := bstep (se 1 (by rfl) ⟨8316887, by rfl⟩ : syracuseStep 11089183 = 16633775) B16633775
theorem B14785577 : Blo 1945435 14785577 := bstep (se 2 (by rfl) ⟨5544591, by rfl⟩ : syracuseStep 14785577 = 11089183) B11089183
theorem B9857051 : Blo 1945435 9857051 := bstep (se 1 (by rfl) ⟨7392788, by rfl⟩ : syracuseStep 9857051 = 14785577) B14785577
theorem B6571367 : Blo 1945435 6571367 := bstep (se 1 (by rfl) ⟨4928525, by rfl⟩ : syracuseStep 6571367 = 9857051) B9857051
theorem B4380911 : Blo 1945435 4380911 := bstep (se 1 (by rfl) ⟨3285683, by rfl⟩ : syracuseStep 4380911 = 6571367) B6571367
theorem B2920607 : Blo 1945435 2920607 := bstep (se 1 (by rfl) ⟨2190455, by rfl⟩ : syracuseStep 2920607 = 4380911) B4380911
theorem B1947071 : Blo 1945435 1947071 := bstep (se 1 (by rfl) ⟨1460303, by rfl⟩ : syracuseStep 1947071 = 2920607) B2920607
theorem B2920613 : Blo 1945435 2920613 := bbase (se 4 (by rfl) ⟨273807, by rfl⟩ : syracuseStep 2920613 = 547615) (by norm_num)
theorem B1947075 : Blo 1945435 1947075 := bstep (se 1 (by rfl) ⟨1460306, by rfl⟩ : syracuseStep 1947075 = 2920613) B2920613
theorem B2464273 : Blo 1945435 2464273 := bbase (se 2 (by rfl) ⟨924102, by rfl⟩ : syracuseStep 2464273 = 1848205) (by norm_num)
theorem B3285697 : Blo 1945435 3285697 := bstep (se 2 (by rfl) ⟨1232136, by rfl⟩ : syracuseStep 3285697 = 2464273) B2464273
theorem B4380929 : Blo 1945435 4380929 := bstep (se 2 (by rfl) ⟨1642848, by rfl⟩ : syracuseStep 4380929 = 3285697) B3285697
theorem B2920619 : Blo 1945435 2920619 := bstep (se 1 (by rfl) ⟨2190464, by rfl⟩ : syracuseStep 2920619 = 4380929) B4380929
theorem B1947079 : Blo 1945435 1947079 := bstep (se 1 (by rfl) ⟨1460309, by rfl⟩ : syracuseStep 1947079 = 2920619) B2920619
theorem B2190469 : Blo 1945435 2190469 := bbase (se 4 (by rfl) ⟨205356, by rfl⟩ : syracuseStep 2190469 = 410713) (by norm_num)
theorem B2920625 : Blo 1945435 2920625 := bstep (se 2 (by rfl) ⟨1095234, by rfl⟩ : syracuseStep 2920625 = 2190469) B2190469
theorem B1947083 : Blo 1945435 1947083 := bstep (se 1 (by rfl) ⟨1460312, by rfl⟩ : syracuseStep 1947083 = 2920625) B2920625
theorem B14034869 : Blo 1945435 14034869 := bbase (se 5 (by rfl) ⟨657884, by rfl⟩ : syracuseStep 14034869 = 1315769) (by norm_num)
theorem B9356579 : Blo 1945435 9356579 := bstep (se 1 (by rfl) ⟨7017434, by rfl⟩ : syracuseStep 9356579 = 14034869) B14034869
theorem B6237719 : Blo 1945435 6237719 := bstep (se 1 (by rfl) ⟨4678289, by rfl⟩ : syracuseStep 6237719 = 9356579) B9356579
theorem B4158479 : Blo 1945435 4158479 := bstep (se 1 (by rfl) ⟨3118859, by rfl⟩ : syracuseStep 4158479 = 6237719) B6237719
theorem B2772319 : Blo 1945435 2772319 := bstep (se 1 (by rfl) ⟨2079239, by rfl⟩ : syracuseStep 2772319 = 4158479) B4158479
theorem B3696425 : Blo 1945435 3696425 := bstep (se 2 (by rfl) ⟨1386159, by rfl⟩ : syracuseStep 3696425 = 2772319) B2772319
theorem B2464283 : Blo 1945435 2464283 := bstep (se 1 (by rfl) ⟨1848212, by rfl⟩ : syracuseStep 2464283 = 3696425) B3696425
theorem B6571421 : Blo 1945435 6571421 := bstep (se 3 (by rfl) ⟨1232141, by rfl⟩ : syracuseStep 6571421 = 2464283) B2464283
theorem B4380947 : Blo 1945435 4380947 := bstep (se 1 (by rfl) ⟨3285710, by rfl⟩ : syracuseStep 4380947 = 6571421) B6571421
theorem B2920631 : Blo 1945435 2920631 := bstep (se 1 (by rfl) ⟨2190473, by rfl⟩ : syracuseStep 2920631 = 4380947) B4380947
theorem B1947087 : Blo 1945435 1947087 := bstep (se 1 (by rfl) ⟨1460315, by rfl⟩ : syracuseStep 1947087 = 2920631) B2920631
theorem B2920637 : Blo 1945435 2920637 := bbase (se 3 (by rfl) ⟨547619, by rfl⟩ : syracuseStep 2920637 = 1095239) (by norm_num)
theorem B1947091 : Blo 1945435 1947091 := bstep (se 1 (by rfl) ⟨1460318, by rfl⟩ : syracuseStep 1947091 = 2920637) B2920637
theorem B4380965 : Blo 1945435 4380965 := bbase (se 4 (by rfl) ⟨410715, by rfl⟩ : syracuseStep 4380965 = 821431) (by norm_num)
theorem B2920643 : Blo 1945435 2920643 := bstep (se 1 (by rfl) ⟨2190482, by rfl⟩ : syracuseStep 2920643 = 4380965) B4380965
theorem B1947095 : Blo 1945435 1947095 := bstep (se 1 (by rfl) ⟨1460321, by rfl⟩ : syracuseStep 1947095 = 2920643) B2920643
theorem B4928597 : Blo 1945435 4928597 := bbase (se 8 (by rfl) ⟨28878, by rfl⟩ : syracuseStep 4928597 = 57757) (by norm_num)
theorem B3285731 : Blo 1945435 3285731 := bstep (se 1 (by rfl) ⟨2464298, by rfl⟩ : syracuseStep 3285731 = 4928597) B4928597
theorem B2190487 : Blo 1945435 2190487 := bstep (se 1 (by rfl) ⟨1642865, by rfl⟩ : syracuseStep 2190487 = 3285731) B3285731
theorem B2920649 : Blo 1945435 2920649 := bstep (se 2 (by rfl) ⟨1095243, by rfl⟩ : syracuseStep 2920649 = 2190487) B2190487
theorem B1947099 : Blo 1945435 1947099 := bstep (se 1 (by rfl) ⟨1460324, by rfl⟩ : syracuseStep 1947099 = 2920649) B2920649
theorem B4440757 : Blo 1945435 4440757 := bbase (se 5 (by rfl) ⟨208160, by rfl⟩ : syracuseStep 4440757 = 416321) (by norm_num)
theorem B5921009 : Blo 1945435 5921009 := bstep (se 2 (by rfl) ⟨2220378, by rfl⟩ : syracuseStep 5921009 = 4440757) B4440757
theorem B3947339 : Blo 1945435 3947339 := bstep (se 1 (by rfl) ⟨2960504, by rfl⟩ : syracuseStep 3947339 = 5921009) B5921009
theorem B10526237 : Blo 1945435 10526237 := bstep (se 3 (by rfl) ⟨1973669, by rfl⟩ : syracuseStep 10526237 = 3947339) B3947339
theorem B7017491 : Blo 1945435 7017491 := bstep (se 1 (by rfl) ⟨5263118, by rfl⟩ : syracuseStep 7017491 = 10526237) B10526237
theorem B4678327 : Blo 1945435 4678327 := bstep (se 1 (by rfl) ⟨3508745, by rfl⟩ : syracuseStep 4678327 = 7017491) B7017491
theorem B6237769 : Blo 1945435 6237769 := bstep (se 2 (by rfl) ⟨2339163, by rfl⟩ : syracuseStep 6237769 = 4678327) B4678327
theorem B8317025 : Blo 1945435 8317025 := bstep (se 2 (by rfl) ⟨3118884, by rfl⟩ : syracuseStep 8317025 = 6237769) B6237769
theorem B5544683 : Blo 1945435 5544683 := bstep (se 1 (by rfl) ⟨4158512, by rfl⟩ : syracuseStep 5544683 = 8317025) B8317025
theorem B3696455 : Blo 1945435 3696455 := bstep (se 1 (by rfl) ⟨2772341, by rfl⟩ : syracuseStep 3696455 = 5544683) B5544683
theorem B9857213 : Blo 1945435 9857213 := bstep (se 3 (by rfl) ⟨1848227, by rfl⟩ : syracuseStep 9857213 = 3696455) B3696455
theorem B6571475 : Blo 1945435 6571475 := bstep (se 1 (by rfl) ⟨4928606, by rfl⟩ : syracuseStep 6571475 = 9857213) B9857213
theorem B4380983 : Blo 1945435 4380983 := bstep (se 1 (by rfl) ⟨3285737, by rfl⟩ : syracuseStep 4380983 = 6571475) B6571475
theorem B2920655 : Blo 1945435 2920655 := bstep (se 1 (by rfl) ⟨2190491, by rfl⟩ : syracuseStep 2920655 = 4380983) B4380983
theorem B1947103 : Blo 1945435 1947103 := bstep (se 1 (by rfl) ⟨1460327, by rfl⟩ : syracuseStep 1947103 = 2920655) B2920655
theorem B2920661 : Blo 1945435 2920661 := bbase (se 7 (by rfl) ⟨34226, by rfl⟩ : syracuseStep 2920661 = 68453) (by norm_num)
theorem B1947107 : Blo 1945435 1947107 := bstep (se 1 (by rfl) ⟨1460330, by rfl⟩ : syracuseStep 1947107 = 2920661) B2920661
theorem B2079265 : Blo 1945435 2079265 := bbase (se 2 (by rfl) ⟨779724, by rfl⟩ : syracuseStep 2079265 = 1559449) (by norm_num)
theorem B2772353 : Blo 1945435 2772353 := bstep (se 2 (by rfl) ⟨1039632, by rfl⟩ : syracuseStep 2772353 = 2079265) B2079265
theorem B7392941 : Blo 1945435 7392941 := bstep (se 3 (by rfl) ⟨1386176, by rfl⟩ : syracuseStep 7392941 = 2772353) B2772353
theorem B4928627 : Blo 1945435 4928627 := bstep (se 1 (by rfl) ⟨3696470, by rfl⟩ : syracuseStep 4928627 = 7392941) B7392941
theorem B3285751 : Blo 1945435 3285751 := bstep (se 1 (by rfl) ⟨2464313, by rfl⟩ : syracuseStep 3285751 = 4928627) B4928627
theorem B4381001 : Blo 1945435 4381001 := bstep (se 2 (by rfl) ⟨1642875, by rfl⟩ : syracuseStep 4381001 = 3285751) B3285751
theorem B2920667 : Blo 1945435 2920667 := bstep (se 1 (by rfl) ⟨2190500, by rfl⟩ : syracuseStep 2920667 = 4381001) B4381001
theorem B1947111 : Blo 1945435 1947111 := bstep (se 1 (by rfl) ⟨1460333, by rfl⟩ : syracuseStep 1947111 = 2920667) B2920667
theorem B2190505 : Blo 1945435 2190505 := bbase (se 2 (by rfl) ⟨821439, by rfl⟩ : syracuseStep 2190505 = 1642879) (by norm_num)
theorem B2920673 : Blo 1945435 2920673 := bstep (se 2 (by rfl) ⟨1095252, by rfl⟩ : syracuseStep 2920673 = 2190505) B2190505
theorem B1947115 : Blo 1945435 1947115 := bstep (se 1 (by rfl) ⟨1460336, by rfl⟩ : syracuseStep 1947115 = 2920673) B2920673
theorem B8317093 : Blo 1945435 8317093 := bbase (se 4 (by rfl) ⟨779727, by rfl⟩ : syracuseStep 8317093 = 1559455) (by norm_num)
theorem B11089457 : Blo 1945435 11089457 := bstep (se 2 (by rfl) ⟨4158546, by rfl⟩ : syracuseStep 11089457 = 8317093) B8317093
theorem B7392971 : Blo 1945435 7392971 := bstep (se 1 (by rfl) ⟨5544728, by rfl⟩ : syracuseStep 7392971 = 11089457) B11089457
theorem B4928647 : Blo 1945435 4928647 := bstep (se 1 (by rfl) ⟨3696485, by rfl⟩ : syracuseStep 4928647 = 7392971) B7392971
theorem B6571529 : Blo 1945435 6571529 := bstep (se 2 (by rfl) ⟨2464323, by rfl⟩ : syracuseStep 6571529 = 4928647) B4928647
theorem B4381019 : Blo 1945435 4381019 := bstep (se 1 (by rfl) ⟨3285764, by rfl⟩ : syracuseStep 4381019 = 6571529) B6571529
theorem B2920679 : Blo 1945435 2920679 := bstep (se 1 (by rfl) ⟨2190509, by rfl⟩ : syracuseStep 2920679 = 4381019) B4381019
theorem B1947119 : Blo 1945435 1947119 := bstep (se 1 (by rfl) ⟨1460339, by rfl⟩ : syracuseStep 1947119 = 2920679) B2920679
theorem B2920685 : Blo 1945435 2920685 := bbase (se 3 (by rfl) ⟨547628, by rfl⟩ : syracuseStep 2920685 = 1095257) (by norm_num)
theorem B1947123 : Blo 1945435 1947123 := bstep (se 1 (by rfl) ⟨1460342, by rfl⟩ : syracuseStep 1947123 = 2920685) B2920685
theorem B4381037 : Blo 1945435 4381037 := bbase (se 3 (by rfl) ⟨821444, by rfl⟩ : syracuseStep 4381037 = 1642889) (by norm_num)
theorem B2920691 : Blo 1945435 2920691 := bstep (se 1 (by rfl) ⟨2190518, by rfl⟩ : syracuseStep 2920691 = 4381037) B4381037
theorem B1947127 : Blo 1945435 1947127 := bstep (se 1 (by rfl) ⟨1460345, by rfl⟩ : syracuseStep 1947127 = 2920691) B2920691
theorem B3696509 : Blo 1945435 3696509 := bbase (se 3 (by rfl) ⟨693095, by rfl⟩ : syracuseStep 3696509 = 1386191) (by norm_num)
theorem B2464339 : Blo 1945435 2464339 := bstep (se 1 (by rfl) ⟨1848254, by rfl⟩ : syracuseStep 2464339 = 3696509) B3696509
theorem B3285785 : Blo 1945435 3285785 := bstep (se 2 (by rfl) ⟨1232169, by rfl⟩ : syracuseStep 3285785 = 2464339) B2464339
theorem B2190523 : Blo 1945435 2190523 := bstep (se 1 (by rfl) ⟨1642892, by rfl⟩ : syracuseStep 2190523 = 3285785) B3285785
theorem B2920697 : Blo 1945435 2920697 := bstep (se 2 (by rfl) ⟨1095261, by rfl⟩ : syracuseStep 2920697 = 2190523) B2190523
theorem B1947131 : Blo 1945435 1947131 := bstep (se 1 (by rfl) ⟨1460348, by rfl⟩ : syracuseStep 1947131 = 2920697) B2920697
theorem B7017605 : Blo 1945435 7017605 := bbase (se 4 (by rfl) ⟨657900, by rfl⟩ : syracuseStep 7017605 = 1315801) (by norm_num)
theorem B4678403 : Blo 1945435 4678403 := bstep (se 1 (by rfl) ⟨3508802, by rfl⟩ : syracuseStep 4678403 = 7017605) B7017605
theorem B49902965 : Blo 1945435 49902965 := bstep (se 5 (by rfl) ⟨2339201, by rfl⟩ : syracuseStep 49902965 = 4678403) B4678403
theorem B33268643 : Blo 1945435 33268643 := bstep (se 1 (by rfl) ⟨24951482, by rfl⟩ : syracuseStep 33268643 = 49902965) B49902965
theorem B22179095 : Blo 1945435 22179095 := bstep (se 1 (by rfl) ⟨16634321, by rfl⟩ : syracuseStep 22179095 = 33268643) B33268643
theorem B14786063 : Blo 1945435 14786063 := bstep (se 1 (by rfl) ⟨11089547, by rfl⟩ : syracuseStep 14786063 = 22179095) B22179095
theorem B9857375 : Blo 1945435 9857375 := bstep (se 1 (by rfl) ⟨7393031, by rfl⟩ : syracuseStep 9857375 = 14786063) B14786063
theorem B6571583 : Blo 1945435 6571583 := bstep (se 1 (by rfl) ⟨4928687, by rfl⟩ : syracuseStep 6571583 = 9857375) B9857375
theorem B4381055 : Blo 1945435 4381055 := bstep (se 1 (by rfl) ⟨3285791, by rfl⟩ : syracuseStep 4381055 = 6571583) B6571583
theorem B2920703 : Blo 1945435 2920703 := bstep (se 1 (by rfl) ⟨2190527, by rfl⟩ : syracuseStep 2920703 = 4381055) B4381055
theorem B1947135 : Blo 1945435 1947135 := bstep (se 1 (by rfl) ⟨1460351, by rfl⟩ : syracuseStep 1947135 = 2920703) B2920703
theorem B2920709 : Blo 1945435 2920709 := bbase (se 4 (by rfl) ⟨273816, by rfl⟩ : syracuseStep 2920709 = 547633) (by norm_num)
theorem B1947139 : Blo 1945435 1947139 := bstep (se 1 (by rfl) ⟨1460354, by rfl⟩ : syracuseStep 1947139 = 2920709) B2920709
theorem B3285805 : Blo 1945435 3285805 := bbase (se 3 (by rfl) ⟨616088, by rfl⟩ : syracuseStep 3285805 = 1232177) (by norm_num)
theorem B4381073 : Blo 1945435 4381073 := bstep (se 2 (by rfl) ⟨1642902, by rfl⟩ : syracuseStep 4381073 = 3285805) B3285805
theorem B2920715 : Blo 1945435 2920715 := bstep (se 1 (by rfl) ⟨2190536, by rfl⟩ : syracuseStep 2920715 = 4381073) B4381073
theorem B1947143 : Blo 1945435 1947143 := bstep (se 1 (by rfl) ⟨1460357, by rfl⟩ : syracuseStep 1947143 = 2920715) B2920715
theorem B2190541 : Blo 1945435 2190541 := bbase (se 3 (by rfl) ⟨410726, by rfl⟩ : syracuseStep 2190541 = 821453) (by norm_num)
theorem B2920721 : Blo 1945435 2920721 := bstep (se 2 (by rfl) ⟨1095270, by rfl⟩ : syracuseStep 2920721 = 2190541) B2190541
theorem B1947147 : Blo 1945435 1947147 := bstep (se 1 (by rfl) ⟨1460360, by rfl⟩ : syracuseStep 1947147 = 2920721) B2920721
theorem B6571637 : Blo 1945435 6571637 := bbase (se 5 (by rfl) ⟨308045, by rfl⟩ : syracuseStep 6571637 = 616091) (by norm_num)
theorem B4381091 : Blo 1945435 4381091 := bstep (se 1 (by rfl) ⟨3285818, by rfl⟩ : syracuseStep 4381091 = 6571637) B6571637
theorem B2920727 : Blo 1945435 2920727 := bstep (se 1 (by rfl) ⟨2190545, by rfl⟩ : syracuseStep 2920727 = 4381091) B4381091
theorem B1947151 : Blo 1945435 1947151 := bstep (se 1 (by rfl) ⟨1460363, by rfl⟩ : syracuseStep 1947151 = 2920727) B2920727
theorem B2920733 : Blo 1945435 2920733 := bbase (se 3 (by rfl) ⟨547637, by rfl⟩ : syracuseStep 2920733 = 1095275) (by norm_num)
theorem B1947155 : Blo 1945435 1947155 := bstep (se 1 (by rfl) ⟨1460366, by rfl⟩ : syracuseStep 1947155 = 2920733) B2920733
theorem B4381109 : Blo 1945435 4381109 := bbase (se 5 (by rfl) ⟨205364, by rfl⟩ : syracuseStep 4381109 = 410729) (by norm_num)
theorem B2920739 : Blo 1945435 2920739 := bstep (se 1 (by rfl) ⟨2190554, by rfl⟩ : syracuseStep 2920739 = 4381109) B4381109
theorem B1947159 : Blo 1945435 1947159 := bstep (se 1 (by rfl) ⟨1460369, by rfl⟩ : syracuseStep 1947159 = 2920739) B2920739
theorem B3118981 : Blo 1945435 3118981 := bbase (se 4 (by rfl) ⟨292404, by rfl⟩ : syracuseStep 3118981 = 584809) (by norm_num)
theorem B4158641 : Blo 1945435 4158641 := bstep (se 2 (by rfl) ⟨1559490, by rfl⟩ : syracuseStep 4158641 = 3118981) B3118981
theorem B11089709 : Blo 1945435 11089709 := bstep (se 3 (by rfl) ⟨2079320, by rfl⟩ : syracuseStep 11089709 = 4158641) B4158641
theorem B7393139 : Blo 1945435 7393139 := bstep (se 1 (by rfl) ⟨5544854, by rfl⟩ : syracuseStep 7393139 = 11089709) B11089709
theorem B4928759 : Blo 1945435 4928759 := bstep (se 1 (by rfl) ⟨3696569, by rfl⟩ : syracuseStep 4928759 = 7393139) B7393139
theorem B3285839 : Blo 1945435 3285839 := bstep (se 1 (by rfl) ⟨2464379, by rfl⟩ : syracuseStep 3285839 = 4928759) B4928759
theorem B2190559 : Blo 1945435 2190559 := bstep (se 1 (by rfl) ⟨1642919, by rfl⟩ : syracuseStep 2190559 = 3285839) B3285839
theorem B2920745 : Blo 1945435 2920745 := bstep (se 2 (by rfl) ⟨1095279, by rfl⟩ : syracuseStep 2920745 = 2190559) B2190559
theorem B1947163 : Blo 1945435 1947163 := bstep (se 1 (by rfl) ⟨1460372, by rfl⟩ : syracuseStep 1947163 = 2920745) B2920745
theorem B3508861 : Blo 1945435 3508861 := bbase (se 3 (by rfl) ⟨657911, by rfl⟩ : syracuseStep 3508861 = 1315823) (by norm_num)
theorem B4678481 : Blo 1945435 4678481 := bstep (se 2 (by rfl) ⟨1754430, by rfl⟩ : syracuseStep 4678481 = 3508861) B3508861
theorem B3118987 : Blo 1945435 3118987 := bstep (se 1 (by rfl) ⟨2339240, by rfl⟩ : syracuseStep 3118987 = 4678481) B4678481
theorem B4158649 : Blo 1945435 4158649 := bstep (se 2 (by rfl) ⟨1559493, by rfl⟩ : syracuseStep 4158649 = 3118987) B3118987
theorem B5544865 : Blo 1945435 5544865 := bstep (se 2 (by rfl) ⟨2079324, by rfl⟩ : syracuseStep 5544865 = 4158649) B4158649
theorem B7393153 : Blo 1945435 7393153 := bstep (se 2 (by rfl) ⟨2772432, by rfl⟩ : syracuseStep 7393153 = 5544865) B5544865
theorem B9857537 : Blo 1945435 9857537 := bstep (se 2 (by rfl) ⟨3696576, by rfl⟩ : syracuseStep 9857537 = 7393153) B7393153
theorem B6571691 : Blo 1945435 6571691 := bstep (se 1 (by rfl) ⟨4928768, by rfl⟩ : syracuseStep 6571691 = 9857537) B9857537
theorem B4381127 : Blo 1945435 4381127 := bstep (se 1 (by rfl) ⟨3285845, by rfl⟩ : syracuseStep 4381127 = 6571691) B6571691
theorem B2920751 : Blo 1945435 2920751 := bstep (se 1 (by rfl) ⟨2190563, by rfl⟩ : syracuseStep 2920751 = 4381127) B4381127
theorem B1947167 : Blo 1945435 1947167 := bstep (se 1 (by rfl) ⟨1460375, by rfl⟩ : syracuseStep 1947167 = 2920751) B2920751
theorem B2920757 : Blo 1945435 2920757 := bbase (se 5 (by rfl) ⟨136910, by rfl⟩ : syracuseStep 2920757 = 273821) (by norm_num)
theorem B1947171 : Blo 1945435 1947171 := bstep (se 1 (by rfl) ⟨1460378, by rfl⟩ : syracuseStep 1947171 = 2920757) B2920757
theorem B4928789 : Blo 1945435 4928789 := bbase (se 6 (by rfl) ⟨115518, by rfl⟩ : syracuseStep 4928789 = 231037) (by norm_num)
theorem B3285859 : Blo 1945435 3285859 := bstep (se 1 (by rfl) ⟨2464394, by rfl⟩ : syracuseStep 3285859 = 4928789) B4928789
theorem B4381145 : Blo 1945435 4381145 := bstep (se 2 (by rfl) ⟨1642929, by rfl⟩ : syracuseStep 4381145 = 3285859) B3285859
theorem B2920763 : Blo 1945435 2920763 := bstep (se 1 (by rfl) ⟨2190572, by rfl⟩ : syracuseStep 2920763 = 4381145) B4381145
theorem B1947175 : Blo 1945435 1947175 := bstep (se 1 (by rfl) ⟨1460381, by rfl⟩ : syracuseStep 1947175 = 2920763) B2920763
theorem B2190577 : Blo 1945435 2190577 := bbase (se 2 (by rfl) ⟨821466, by rfl⟩ : syracuseStep 2190577 = 1642933) (by norm_num)
theorem B2920769 : Blo 1945435 2920769 := bstep (se 2 (by rfl) ⟨1095288, by rfl⟩ : syracuseStep 2920769 = 2190577) B2190577
theorem B1947179 : Blo 1945435 1947179 := bstep (se 1 (by rfl) ⟨1460384, by rfl⟩ : syracuseStep 1947179 = 2920769) B2920769
theorem B3947501 : Blo 1945435 3947501 := bbase (se 3 (by rfl) ⟨740156, by rfl⟩ : syracuseStep 3947501 = 1480313) (by norm_num)
theorem B10526669 : Blo 1945435 10526669 := bstep (se 3 (by rfl) ⟨1973750, by rfl⟩ : syracuseStep 10526669 = 3947501) B3947501
theorem B7017779 : Blo 1945435 7017779 := bstep (se 1 (by rfl) ⟨5263334, by rfl⟩ : syracuseStep 7017779 = 10526669) B10526669
theorem B18714077 : Blo 1945435 18714077 := bstep (se 3 (by rfl) ⟨3508889, by rfl⟩ : syracuseStep 18714077 = 7017779) B7017779
theorem B12476051 : Blo 1945435 12476051 := bstep (se 1 (by rfl) ⟨9357038, by rfl⟩ : syracuseStep 12476051 = 18714077) B18714077
theorem B8317367 : Blo 1945435 8317367 := bstep (se 1 (by rfl) ⟨6238025, by rfl⟩ : syracuseStep 8317367 = 12476051) B12476051
theorem B5544911 : Blo 1945435 5544911 := bstep (se 1 (by rfl) ⟨4158683, by rfl⟩ : syracuseStep 5544911 = 8317367) B8317367
theorem B3696607 : Blo 1945435 3696607 := bstep (se 1 (by rfl) ⟨2772455, by rfl⟩ : syracuseStep 3696607 = 5544911) B5544911
theorem B4928809 : Blo 1945435 4928809 := bstep (se 2 (by rfl) ⟨1848303, by rfl⟩ : syracuseStep 4928809 = 3696607) B3696607
theorem B6571745 : Blo 1945435 6571745 := bstep (se 2 (by rfl) ⟨2464404, by rfl⟩ : syracuseStep 6571745 = 4928809) B4928809
theorem B4381163 : Blo 1945435 4381163 := bstep (se 1 (by rfl) ⟨3285872, by rfl⟩ : syracuseStep 4381163 = 6571745) B6571745
theorem B2920775 : Blo 1945435 2920775 := bstep (se 1 (by rfl) ⟨2190581, by rfl⟩ : syracuseStep 2920775 = 4381163) B4381163
theorem B1947183 : Blo 1945435 1947183 := bstep (se 1 (by rfl) ⟨1460387, by rfl⟩ : syracuseStep 1947183 = 2920775) B2920775
theorem B2920781 : Blo 1945435 2920781 := bbase (se 3 (by rfl) ⟨547646, by rfl⟩ : syracuseStep 2920781 = 1095293) (by norm_num)
theorem B1947187 : Blo 1945435 1947187 := bstep (se 1 (by rfl) ⟨1460390, by rfl⟩ : syracuseStep 1947187 = 2920781) B2920781
theorem B4381181 : Blo 1945435 4381181 := bbase (se 3 (by rfl) ⟨821471, by rfl⟩ : syracuseStep 4381181 = 1642943) (by norm_num)
theorem B2920787 : Blo 1945435 2920787 := bstep (se 1 (by rfl) ⟨2190590, by rfl⟩ : syracuseStep 2920787 = 4381181) B4381181
theorem B1947191 : Blo 1945435 1947191 := bstep (se 1 (by rfl) ⟨1460393, by rfl⟩ : syracuseStep 1947191 = 2920787) B2920787
theorem B3285893 : Blo 1945435 3285893 := bbase (se 4 (by rfl) ⟨308052, by rfl⟩ : syracuseStep 3285893 = 616105) (by norm_num)
theorem B2190595 : Blo 1945435 2190595 := bstep (se 1 (by rfl) ⟨1642946, by rfl⟩ : syracuseStep 2190595 = 3285893) B3285893
theorem B2920793 : Blo 1945435 2920793 := bstep (se 2 (by rfl) ⟨1095297, by rfl⟩ : syracuseStep 2920793 = 2190595) B2190595
theorem B1947195 : Blo 1945435 1947195 := bstep (se 1 (by rfl) ⟨1460396, by rfl⟩ : syracuseStep 1947195 = 2920793) B2920793
theorem B14786549 : Blo 1945435 14786549 := bbase (se 5 (by rfl) ⟨693119, by rfl⟩ : syracuseStep 14786549 = 1386239) (by norm_num)
theorem B9857699 : Blo 1945435 9857699 := bstep (se 1 (by rfl) ⟨7393274, by rfl⟩ : syracuseStep 9857699 = 14786549) B14786549
theorem B6571799 : Blo 1945435 6571799 := bstep (se 1 (by rfl) ⟨4928849, by rfl⟩ : syracuseStep 6571799 = 9857699) B9857699
theorem B4381199 : Blo 1945435 4381199 := bstep (se 1 (by rfl) ⟨3285899, by rfl⟩ : syracuseStep 4381199 = 6571799) B6571799
theorem B2920799 : Blo 1945435 2920799 := bstep (se 1 (by rfl) ⟨2190599, by rfl⟩ : syracuseStep 2920799 = 4381199) B4381199
theorem B1947199 : Blo 1945435 1947199 := bstep (se 1 (by rfl) ⟨1460399, by rfl⟩ : syracuseStep 1947199 = 2920799) B2920799
theorem B2920805 : Blo 1945435 2920805 := bbase (se 4 (by rfl) ⟨273825, by rfl⟩ : syracuseStep 2920805 = 547651) (by norm_num)
theorem B1947203 : Blo 1945435 1947203 := bstep (se 1 (by rfl) ⟨1460402, by rfl⟩ : syracuseStep 1947203 = 2920805) B2920805
theorem B3696653 : Blo 1945435 3696653 := bbase (se 3 (by rfl) ⟨693122, by rfl⟩ : syracuseStep 3696653 = 1386245) (by norm_num)
theorem B2464435 : Blo 1945435 2464435 := bstep (se 1 (by rfl) ⟨1848326, by rfl⟩ : syracuseStep 2464435 = 3696653) B3696653
theorem B3285913 : Blo 1945435 3285913 := bstep (se 2 (by rfl) ⟨1232217, by rfl⟩ : syracuseStep 3285913 = 2464435) B2464435
theorem B4381217 : Blo 1945435 4381217 := bstep (se 2 (by rfl) ⟨1642956, by rfl⟩ : syracuseStep 4381217 = 3285913) B3285913
theorem B2920811 : Blo 1945435 2920811 := bstep (se 1 (by rfl) ⟨2190608, by rfl⟩ : syracuseStep 2920811 = 4381217) B4381217
theorem B1947207 : Blo 1945435 1947207 := bstep (se 1 (by rfl) ⟨1460405, by rfl⟩ : syracuseStep 1947207 = 2920811) B2920811
theorem B2190613 : Blo 1945435 2190613 := bbase (se 6 (by rfl) ⟨51342, by rfl⟩ : syracuseStep 2190613 = 102685) (by norm_num)
theorem B2920817 : Blo 1945435 2920817 := bstep (se 2 (by rfl) ⟨1095306, by rfl⟩ : syracuseStep 2920817 = 2190613) B2190613
theorem B1947211 : Blo 1945435 1947211 := bstep (se 1 (by rfl) ⟨1460408, by rfl⟩ : syracuseStep 1947211 = 2920817) B2920817
theorem B2464445 : Blo 1945435 2464445 := bbase (se 3 (by rfl) ⟨462083, by rfl⟩ : syracuseStep 2464445 = 924167) (by norm_num)
theorem B6571853 : Blo 1945435 6571853 := bstep (se 3 (by rfl) ⟨1232222, by rfl⟩ : syracuseStep 6571853 = 2464445) B2464445
theorem B4381235 : Blo 1945435 4381235 := bstep (se 1 (by rfl) ⟨3285926, by rfl⟩ : syracuseStep 4381235 = 6571853) B6571853
theorem B2920823 : Blo 1945435 2920823 := bstep (se 1 (by rfl) ⟨2190617, by rfl⟩ : syracuseStep 2920823 = 4381235) B4381235
theorem B1947215 : Blo 1945435 1947215 := bstep (se 1 (by rfl) ⟨1460411, by rfl⟩ : syracuseStep 1947215 = 2920823) B2920823
theorem B2920829 : Blo 1945435 2920829 := bbase (se 3 (by rfl) ⟨547655, by rfl⟩ : syracuseStep 2920829 = 1095311) (by norm_num)
theorem B1947219 : Blo 1945435 1947219 := bstep (se 1 (by rfl) ⟨1460414, by rfl⟩ : syracuseStep 1947219 = 2920829) B2920829
theorem B4381253 : Blo 1945435 4381253 := bbase (se 4 (by rfl) ⟨410742, by rfl⟩ : syracuseStep 4381253 = 821485) (by norm_num)
theorem B2920835 : Blo 1945435 2920835 := bstep (se 1 (by rfl) ⟨2190626, by rfl⟩ : syracuseStep 2920835 = 4381253) B4381253
theorem B1947223 : Blo 1945435 1947223 := bstep (se 1 (by rfl) ⟨1460417, by rfl⟩ : syracuseStep 1947223 = 2920835) B2920835
theorem B2079389 : Blo 1945435 2079389 := bbase (se 3 (by rfl) ⟨389885, by rfl⟩ : syracuseStep 2079389 = 779771) (by norm_num)
theorem B5545037 : Blo 1945435 5545037 := bstep (se 3 (by rfl) ⟨1039694, by rfl⟩ : syracuseStep 5545037 = 2079389) B2079389
theorem B3696691 : Blo 1945435 3696691 := bstep (se 1 (by rfl) ⟨2772518, by rfl⟩ : syracuseStep 3696691 = 5545037) B5545037
theorem B4928921 : Blo 1945435 4928921 := bstep (se 2 (by rfl) ⟨1848345, by rfl⟩ : syracuseStep 4928921 = 3696691) B3696691
theorem B3285947 : Blo 1945435 3285947 := bstep (se 1 (by rfl) ⟨2464460, by rfl⟩ : syracuseStep 3285947 = 4928921) B4928921
theorem B2190631 : Blo 1945435 2190631 := bstep (se 1 (by rfl) ⟨1642973, by rfl⟩ : syracuseStep 2190631 = 3285947) B3285947
theorem B2920841 : Blo 1945435 2920841 := bstep (se 2 (by rfl) ⟨1095315, by rfl⟩ : syracuseStep 2920841 = 2190631) B2190631
theorem B1947227 : Blo 1945435 1947227 := bstep (se 1 (by rfl) ⟨1460420, by rfl⟩ : syracuseStep 1947227 = 2920841) B2920841
theorem B9857861 : Blo 1945435 9857861 := bbase (se 4 (by rfl) ⟨924174, by rfl⟩ : syracuseStep 9857861 = 1848349) (by norm_num)
theorem B6571907 : Blo 1945435 6571907 := bstep (se 1 (by rfl) ⟨4928930, by rfl⟩ : syracuseStep 6571907 = 9857861) B9857861
theorem B4381271 : Blo 1945435 4381271 := bstep (se 1 (by rfl) ⟨3285953, by rfl⟩ : syracuseStep 4381271 = 6571907) B6571907
theorem B2920847 : Blo 1945435 2920847 := bstep (se 1 (by rfl) ⟨2190635, by rfl⟩ : syracuseStep 2920847 = 4381271) B4381271
theorem B1947231 : Blo 1945435 1947231 := bstep (se 1 (by rfl) ⟨1460423, by rfl⟩ : syracuseStep 1947231 = 2920847) B2920847
theorem B2920853 : Blo 1945435 2920853 := bbase (se 6 (by rfl) ⟨68457, by rfl⟩ : syracuseStep 2920853 = 136915) (by norm_num)
theorem B1947235 : Blo 1945435 1947235 := bstep (se 1 (by rfl) ⟨1460426, by rfl⟩ : syracuseStep 1947235 = 2920853) B2920853
theorem B5335301 : Blo 1945435 5335301 := bbase (se 4 (by rfl) ⟨500184, by rfl⟩ : syracuseStep 5335301 = 1000369) (by norm_num)
theorem B3556867 : Blo 1945435 3556867 := bstep (se 1 (by rfl) ⟨2667650, by rfl⟩ : syracuseStep 3556867 = 5335301) B5335301
theorem B4742489 : Blo 1945435 4742489 := bstep (se 2 (by rfl) ⟨1778433, by rfl⟩ : syracuseStep 4742489 = 3556867) B3556867
theorem B3161659 : Blo 1945435 3161659 := bstep (se 1 (by rfl) ⟨2371244, by rfl⟩ : syracuseStep 3161659 = 4742489) B4742489
theorem B4215545 : Blo 1945435 4215545 := bstep (se 2 (by rfl) ⟨1580829, by rfl⟩ : syracuseStep 4215545 = 3161659) B3161659
theorem B44965813 : Blo 1945435 44965813 := bstep (se 5 (by rfl) ⟨2107772, by rfl⟩ : syracuseStep 44965813 = 4215545) B4215545
theorem B59954417 : Blo 1945435 59954417 := bstep (se 2 (by rfl) ⟨22482906, by rfl⟩ : syracuseStep 59954417 = 44965813) B44965813
theorem B39969611 : Blo 1945435 39969611 := bstep (se 1 (by rfl) ⟨29977208, by rfl⟩ : syracuseStep 39969611 = 59954417) B59954417
theorem B26646407 : Blo 1945435 26646407 := bstep (se 1 (by rfl) ⟨19984805, by rfl⟩ : syracuseStep 26646407 = 39969611) B39969611
theorem B17764271 : Blo 1945435 17764271 := bstep (se 1 (by rfl) ⟨13323203, by rfl⟩ : syracuseStep 17764271 = 26646407) B26646407
theorem B11842847 : Blo 1945435 11842847 := bstep (se 1 (by rfl) ⟨8882135, by rfl⟩ : syracuseStep 11842847 = 17764271) B17764271
theorem B7895231 : Blo 1945435 7895231 := bstep (se 1 (by rfl) ⟨5921423, by rfl⟩ : syracuseStep 7895231 = 11842847) B11842847
theorem B5263487 : Blo 1945435 5263487 := bstep (se 1 (by rfl) ⟨3947615, by rfl⟩ : syracuseStep 5263487 = 7895231) B7895231
theorem B3508991 : Blo 1945435 3508991 := bstep (se 1 (by rfl) ⟨2631743, by rfl⟩ : syracuseStep 3508991 = 5263487) B5263487
theorem B2339327 : Blo 1945435 2339327 := bstep (se 1 (by rfl) ⟨1754495, by rfl⟩ : syracuseStep 2339327 = 3508991) B3508991
theorem B6238205 : Blo 1945435 6238205 := bstep (se 3 (by rfl) ⟨1169663, by rfl⟩ : syracuseStep 6238205 = 2339327) B2339327
theorem B4158803 : Blo 1945435 4158803 := bstep (se 1 (by rfl) ⟨3119102, by rfl⟩ : syracuseStep 4158803 = 6238205) B6238205
theorem B11090141 : Blo 1945435 11090141 := bstep (se 3 (by rfl) ⟨2079401, by rfl⟩ : syracuseStep 11090141 = 4158803) B4158803
theorem B7393427 : Blo 1945435 7393427 := bstep (se 1 (by rfl) ⟨5545070, by rfl⟩ : syracuseStep 7393427 = 11090141) B11090141
theorem B4928951 : Blo 1945435 4928951 := bstep (se 1 (by rfl) ⟨3696713, by rfl⟩ : syracuseStep 4928951 = 7393427) B7393427
theorem B3285967 : Blo 1945435 3285967 := bstep (se 1 (by rfl) ⟨2464475, by rfl⟩ : syracuseStep 3285967 = 4928951) B4928951
theorem B4381289 : Blo 1945435 4381289 := bstep (se 2 (by rfl) ⟨1642983, by rfl⟩ : syracuseStep 4381289 = 3285967) B3285967
theorem B2920859 : Blo 1945435 2920859 := bstep (se 1 (by rfl) ⟨2190644, by rfl⟩ : syracuseStep 2920859 = 4381289) B4381289
theorem B1947239 : Blo 1945435 1947239 := bstep (se 1 (by rfl) ⟨1460429, by rfl⟩ : syracuseStep 1947239 = 2920859) B2920859
theorem B2190649 : Blo 1945435 2190649 := bbase (se 2 (by rfl) ⟨821493, by rfl⟩ : syracuseStep 2190649 = 1642987) (by norm_num)
theorem B2920865 : Blo 1945435 2920865 := bstep (se 2 (by rfl) ⟨1095324, by rfl⟩ : syracuseStep 2920865 = 2190649) B2190649
theorem B1947243 : Blo 1945435 1947243 := bstep (se 1 (by rfl) ⟨1460432, by rfl⟩ : syracuseStep 1947243 = 2920865) B2920865
theorem B5545093 : Blo 1945435 5545093 := bbase (se 4 (by rfl) ⟨519852, by rfl⟩ : syracuseStep 5545093 = 1039705) (by norm_num)
theorem B7393457 : Blo 1945435 7393457 := bstep (se 2 (by rfl) ⟨2772546, by rfl⟩ : syracuseStep 7393457 = 5545093) B5545093
theorem B4928971 : Blo 1945435 4928971 := bstep (se 1 (by rfl) ⟨3696728, by rfl⟩ : syracuseStep 4928971 = 7393457) B7393457
theorem B6571961 : Blo 1945435 6571961 := bstep (se 2 (by rfl) ⟨2464485, by rfl⟩ : syracuseStep 6571961 = 4928971) B4928971
theorem B4381307 : Blo 1945435 4381307 := bstep (se 1 (by rfl) ⟨3285980, by rfl⟩ : syracuseStep 4381307 = 6571961) B6571961
theorem B2920871 : Blo 1945435 2920871 := bstep (se 1 (by rfl) ⟨2190653, by rfl⟩ : syracuseStep 2920871 = 4381307) B4381307
theorem B1947247 : Blo 1945435 1947247 := bstep (se 1 (by rfl) ⟨1460435, by rfl⟩ : syracuseStep 1947247 = 2920871) B2920871
theorem B2920877 : Blo 1945435 2920877 := bbase (se 3 (by rfl) ⟨547664, by rfl⟩ : syracuseStep 2920877 = 1095329) (by norm_num)
theorem B1947251 : Blo 1945435 1947251 := bstep (se 1 (by rfl) ⟨1460438, by rfl⟩ : syracuseStep 1947251 = 2920877) B2920877
theorem B4381325 : Blo 1945435 4381325 := bbase (se 3 (by rfl) ⟨821498, by rfl⟩ : syracuseStep 4381325 = 1642997) (by norm_num)
theorem B2920883 : Blo 1945435 2920883 := bstep (se 1 (by rfl) ⟨2190662, by rfl⟩ : syracuseStep 2920883 = 4381325) B4381325
theorem B1947255 : Blo 1945435 1947255 := bstep (se 1 (by rfl) ⟨1460441, by rfl⟩ : syracuseStep 1947255 = 2920883) B2920883
theorem B2464501 : Blo 1945435 2464501 := bbase (se 5 (by rfl) ⟨115523, by rfl⟩ : syracuseStep 2464501 = 231047) (by norm_num)
theorem B3286001 : Blo 1945435 3286001 := bstep (se 2 (by rfl) ⟨1232250, by rfl⟩ : syracuseStep 3286001 = 2464501) B2464501
theorem B2190667 : Blo 1945435 2190667 := bstep (se 1 (by rfl) ⟨1643000, by rfl⟩ : syracuseStep 2190667 = 3286001) B3286001
theorem B2920889 : Blo 1945435 2920889 := bstep (se 2 (by rfl) ⟨1095333, by rfl⟩ : syracuseStep 2920889 = 2190667) B2190667
theorem B1947259 : Blo 1945435 1947259 := bstep (se 1 (by rfl) ⟨1460444, by rfl⟩ : syracuseStep 1947259 = 2920889) B2920889
theorem B3747197 : Blo 1945435 3747197 := bbase (se 3 (by rfl) ⟨702599, by rfl⟩ : syracuseStep 3747197 = 1405199) (by norm_num)
theorem B2498131 : Blo 1945435 2498131 := bstep (se 1 (by rfl) ⟨1873598, by rfl⟩ : syracuseStep 2498131 = 3747197) B3747197
theorem B13323365 : Blo 1945435 13323365 := bstep (se 4 (by rfl) ⟨1249065, by rfl⟩ : syracuseStep 13323365 = 2498131) B2498131
theorem B8882243 : Blo 1945435 8882243 := bstep (se 1 (by rfl) ⟨6661682, by rfl⟩ : syracuseStep 8882243 = 13323365) B13323365
theorem B5921495 : Blo 1945435 5921495 := bstep (se 1 (by rfl) ⟨4441121, by rfl⟩ : syracuseStep 5921495 = 8882243) B8882243
theorem B3947663 : Blo 1945435 3947663 := bstep (se 1 (by rfl) ⟨2960747, by rfl⟩ : syracuseStep 3947663 = 5921495) B5921495
theorem B2631775 : Blo 1945435 2631775 := bstep (se 1 (by rfl) ⟨1973831, by rfl⟩ : syracuseStep 2631775 = 3947663) B3947663
theorem B3509033 : Blo 1945435 3509033 := bstep (se 2 (by rfl) ⟨1315887, by rfl⟩ : syracuseStep 3509033 = 2631775) B2631775
theorem B37429685 : Blo 1945435 37429685 := bstep (se 5 (by rfl) ⟨1754516, by rfl⟩ : syracuseStep 37429685 = 3509033) B3509033
theorem B24953123 : Blo 1945435 24953123 := bstep (se 1 (by rfl) ⟨18714842, by rfl⟩ : syracuseStep 24953123 = 37429685) B37429685
theorem B16635415 : Blo 1945435 16635415 := bstep (se 1 (by rfl) ⟨12476561, by rfl⟩ : syracuseStep 16635415 = 24953123) B24953123
theorem B22180553 : Blo 1945435 22180553 := bstep (se 2 (by rfl) ⟨8317707, by rfl⟩ : syracuseStep 22180553 = 16635415) B16635415
theorem B14787035 : Blo 1945435 14787035 := bstep (se 1 (by rfl) ⟨11090276, by rfl⟩ : syracuseStep 14787035 = 22180553) B22180553
theorem B9858023 : Blo 1945435 9858023 := bstep (se 1 (by rfl) ⟨7393517, by rfl⟩ : syracuseStep 9858023 = 14787035) B14787035
theorem B6572015 : Blo 1945435 6572015 := bstep (se 1 (by rfl) ⟨4929011, by rfl⟩ : syracuseStep 6572015 = 9858023) B9858023
theorem B4381343 : Blo 1945435 4381343 := bstep (se 1 (by rfl) ⟨3286007, by rfl⟩ : syracuseStep 4381343 = 6572015) B6572015
theorem B2920895 : Blo 1945435 2920895 := bstep (se 1 (by rfl) ⟨2190671, by rfl⟩ : syracuseStep 2920895 = 4381343) B4381343
theorem B1947263 : Blo 1945435 1947263 := bstep (se 1 (by rfl) ⟨1460447, by rfl⟩ : syracuseStep 1947263 = 2920895) B2920895
theorem B2920901 : Blo 1945435 2920901 := bbase (se 4 (by rfl) ⟨273834, by rfl⟩ : syracuseStep 2920901 = 547669) (by norm_num)
theorem B1947267 : Blo 1945435 1947267 := bstep (se 1 (by rfl) ⟨1460450, by rfl⟩ : syracuseStep 1947267 = 2920901) B2920901
theorem B3286021 : Blo 1945435 3286021 := bbase (se 4 (by rfl) ⟨308064, by rfl⟩ : syracuseStep 3286021 = 616129) (by norm_num)
theorem B4381361 : Blo 1945435 4381361 := bstep (se 2 (by rfl) ⟨1643010, by rfl⟩ : syracuseStep 4381361 = 3286021) B3286021
theorem B2920907 : Blo 1945435 2920907 := bstep (se 1 (by rfl) ⟨2190680, by rfl⟩ : syracuseStep 2920907 = 4381361) B4381361
theorem B1947271 : Blo 1945435 1947271 := bstep (se 1 (by rfl) ⟨1460453, by rfl⟩ : syracuseStep 1947271 = 2920907) B2920907
theorem B2190685 : Blo 1945435 2190685 := bbase (se 3 (by rfl) ⟨410753, by rfl⟩ : syracuseStep 2190685 = 821507) (by norm_num)
theorem B2920913 : Blo 1945435 2920913 := bstep (se 2 (by rfl) ⟨1095342, by rfl⟩ : syracuseStep 2920913 = 2190685) B2190685
theorem B1947275 : Blo 1945435 1947275 := bstep (se 1 (by rfl) ⟨1460456, by rfl⟩ : syracuseStep 1947275 = 2920913) B2920913
theorem B6572069 : Blo 1945435 6572069 := bbase (se 4 (by rfl) ⟨616131, by rfl⟩ : syracuseStep 6572069 = 1232263) (by norm_num)
theorem B4381379 : Blo 1945435 4381379 := bstep (se 1 (by rfl) ⟨3286034, by rfl⟩ : syracuseStep 4381379 = 6572069) B6572069
theorem B2920919 : Blo 1945435 2920919 := bstep (se 1 (by rfl) ⟨2190689, by rfl⟩ : syracuseStep 2920919 = 4381379) B4381379
theorem B1947279 : Blo 1945435 1947279 := bstep (se 1 (by rfl) ⟨1460459, by rfl⟩ : syracuseStep 1947279 = 2920919) B2920919
theorem B2920925 : Blo 1945435 2920925 := bbase (se 3 (by rfl) ⟨547673, by rfl⟩ : syracuseStep 2920925 = 1095347) (by norm_num)
theorem B1947283 : Blo 1945435 1947283 := bstep (se 1 (by rfl) ⟨1460462, by rfl⟩ : syracuseStep 1947283 = 2920925) B2920925
theorem B4381397 : Blo 1945435 4381397 := bbase (se 7 (by rfl) ⟨51344, by rfl⟩ : syracuseStep 4381397 = 102689) (by norm_num)
theorem B2920931 : Blo 1945435 2920931 := bstep (se 1 (by rfl) ⟨2190698, by rfl⟩ : syracuseStep 2920931 = 4381397) B4381397
theorem B1947287 : Blo 1945435 1947287 := bstep (se 1 (by rfl) ⟨1460465, by rfl⟩ : syracuseStep 1947287 = 2920931) B2920931
theorem B8317829 : Blo 1945435 8317829 := bbase (se 4 (by rfl) ⟨779796, by rfl⟩ : syracuseStep 8317829 = 1559593) (by norm_num)
theorem B5545219 : Blo 1945435 5545219 := bstep (se 1 (by rfl) ⟨4158914, by rfl⟩ : syracuseStep 5545219 = 8317829) B8317829
theorem B7393625 : Blo 1945435 7393625 := bstep (se 2 (by rfl) ⟨2772609, by rfl⟩ : syracuseStep 7393625 = 5545219) B5545219
theorem B4929083 : Blo 1945435 4929083 := bstep (se 1 (by rfl) ⟨3696812, by rfl⟩ : syracuseStep 4929083 = 7393625) B7393625
theorem B3286055 : Blo 1945435 3286055 := bstep (se 1 (by rfl) ⟨2464541, by rfl⟩ : syracuseStep 3286055 = 4929083) B4929083
theorem B2190703 : Blo 1945435 2190703 := bstep (se 1 (by rfl) ⟨1643027, by rfl⟩ : syracuseStep 2190703 = 3286055) B3286055
theorem B2920937 : Blo 1945435 2920937 := bstep (se 2 (by rfl) ⟨1095351, by rfl⟩ : syracuseStep 2920937 = 2190703) B2190703
theorem B1947291 : Blo 1945435 1947291 := bstep (se 1 (by rfl) ⟨1460468, by rfl⟩ : syracuseStep 1947291 = 2920937) B2920937
theorem B3161749 : Blo 1945435 3161749 := bbase (se 6 (by rfl) ⟨74103, by rfl⟩ : syracuseStep 3161749 = 148207) (by norm_num)
theorem B4215665 : Blo 1945435 4215665 := bstep (se 2 (by rfl) ⟨1580874, by rfl⟩ : syracuseStep 4215665 = 3161749) B3161749
theorem B11241773 : Blo 1945435 11241773 := bstep (se 3 (by rfl) ⟨2107832, by rfl⟩ : syracuseStep 11241773 = 4215665) B4215665
theorem B7494515 : Blo 1945435 7494515 := bstep (se 1 (by rfl) ⟨5620886, by rfl⟩ : syracuseStep 7494515 = 11241773) B11241773
theorem B4996343 : Blo 1945435 4996343 := bstep (se 1 (by rfl) ⟨3747257, by rfl⟩ : syracuseStep 4996343 = 7494515) B7494515
theorem B13323581 : Blo 1945435 13323581 := bstep (se 3 (by rfl) ⟨2498171, by rfl⟩ : syracuseStep 13323581 = 4996343) B4996343
theorem B8882387 : Blo 1945435 8882387 := bstep (se 1 (by rfl) ⟨6661790, by rfl⟩ : syracuseStep 8882387 = 13323581) B13323581
theorem B5921591 : Blo 1945435 5921591 := bstep (se 1 (by rfl) ⟨4441193, by rfl⟩ : syracuseStep 5921591 = 8882387) B8882387
theorem B63163637 : Blo 1945435 63163637 := bstep (se 5 (by rfl) ⟨2960795, by rfl⟩ : syracuseStep 63163637 = 5921591) B5921591
theorem B42109091 : Blo 1945435 42109091 := bstep (se 1 (by rfl) ⟨31581818, by rfl⟩ : syracuseStep 42109091 = 63163637) B63163637
theorem B28072727 : Blo 1945435 28072727 := bstep (se 1 (by rfl) ⟨21054545, by rfl⟩ : syracuseStep 28072727 = 42109091) B42109091
theorem B18715151 : Blo 1945435 18715151 := bstep (se 1 (by rfl) ⟨14036363, by rfl⟩ : syracuseStep 18715151 = 28072727) B28072727
theorem B12476767 : Blo 1945435 12476767 := bstep (se 1 (by rfl) ⟨9357575, by rfl⟩ : syracuseStep 12476767 = 18715151) B18715151
theorem B16635689 : Blo 1945435 16635689 := bstep (se 2 (by rfl) ⟨6238383, by rfl⟩ : syracuseStep 16635689 = 12476767) B12476767
theorem B11090459 : Blo 1945435 11090459 := bstep (se 1 (by rfl) ⟨8317844, by rfl⟩ : syracuseStep 11090459 = 16635689) B16635689
theorem B7393639 : Blo 1945435 7393639 := bstep (se 1 (by rfl) ⟨5545229, by rfl⟩ : syracuseStep 7393639 = 11090459) B11090459
theorem B9858185 : Blo 1945435 9858185 := bstep (se 2 (by rfl) ⟨3696819, by rfl⟩ : syracuseStep 9858185 = 7393639) B7393639
theorem B6572123 : Blo 1945435 6572123 := bstep (se 1 (by rfl) ⟨4929092, by rfl⟩ : syracuseStep 6572123 = 9858185) B9858185
theorem B4381415 : Blo 1945435 4381415 := bstep (se 1 (by rfl) ⟨3286061, by rfl⟩ : syracuseStep 4381415 = 6572123) B6572123
theorem B2920943 : Blo 1945435 2920943 := bstep (se 1 (by rfl) ⟨2190707, by rfl⟩ : syracuseStep 2920943 = 4381415) B4381415
theorem B1947295 : Blo 1945435 1947295 := bstep (se 1 (by rfl) ⟨1460471, by rfl⟩ : syracuseStep 1947295 = 2920943) B2920943
theorem B2920949 : Blo 1945435 2920949 := bbase (se 5 (by rfl) ⟨136919, by rfl⟩ : syracuseStep 2920949 = 273839) (by norm_num)
theorem B1947299 : Blo 1945435 1947299 := bstep (se 1 (by rfl) ⟨1460474, by rfl⟩ : syracuseStep 1947299 = 2920949) B2920949
theorem B5545253 : Blo 1945435 5545253 := bbase (se 4 (by rfl) ⟨519867, by rfl⟩ : syracuseStep 5545253 = 1039735) (by norm_num)
theorem B3696835 : Blo 1945435 3696835 := bstep (se 1 (by rfl) ⟨2772626, by rfl⟩ : syracuseStep 3696835 = 5545253) B5545253
theorem B4929113 : Blo 1945435 4929113 := bstep (se 2 (by rfl) ⟨1848417, by rfl⟩ : syracuseStep 4929113 = 3696835) B3696835
theorem B3286075 : Blo 1945435 3286075 := bstep (se 1 (by rfl) ⟨2464556, by rfl⟩ : syracuseStep 3286075 = 4929113) B4929113
theorem B4381433 : Blo 1945435 4381433 := bstep (se 2 (by rfl) ⟨1643037, by rfl⟩ : syracuseStep 4381433 = 3286075) B3286075
theorem B2920955 : Blo 1945435 2920955 := bstep (se 1 (by rfl) ⟨2190716, by rfl⟩ : syracuseStep 2920955 = 4381433) B4381433
theorem B1947303 : Blo 1945435 1947303 := bstep (se 1 (by rfl) ⟨1460477, by rfl⟩ : syracuseStep 1947303 = 2920955) B2920955
theorem B2190721 : Blo 1945435 2190721 := bbase (se 2 (by rfl) ⟨821520, by rfl⟩ : syracuseStep 2190721 = 1643041) (by norm_num)
theorem B2920961 : Blo 1945435 2920961 := bstep (se 2 (by rfl) ⟨1095360, by rfl⟩ : syracuseStep 2920961 = 2190721) B2190721
theorem B1947307 : Blo 1945435 1947307 := bstep (se 1 (by rfl) ⟨1460480, by rfl⟩ : syracuseStep 1947307 = 2920961) B2920961
theorem B4929133 : Blo 1945435 4929133 := bbase (se 3 (by rfl) ⟨924212, by rfl⟩ : syracuseStep 4929133 = 1848425) (by norm_num)
theorem B6572177 : Blo 1945435 6572177 := bstep (se 2 (by rfl) ⟨2464566, by rfl⟩ : syracuseStep 6572177 = 4929133) B4929133
theorem B4381451 : Blo 1945435 4381451 := bstep (se 1 (by rfl) ⟨3286088, by rfl⟩ : syracuseStep 4381451 = 6572177) B6572177
theorem B2920967 : Blo 1945435 2920967 := bstep (se 1 (by rfl) ⟨2190725, by rfl⟩ : syracuseStep 2920967 = 4381451) B4381451
theorem B1947311 : Blo 1945435 1947311 := bstep (se 1 (by rfl) ⟨1460483, by rfl⟩ : syracuseStep 1947311 = 2920967) B2920967
theorem B2920973 : Blo 1945435 2920973 := bbase (se 3 (by rfl) ⟨547682, by rfl⟩ : syracuseStep 2920973 = 1095365) (by norm_num)
theorem B1947315 : Blo 1945435 1947315 := bstep (se 1 (by rfl) ⟨1460486, by rfl⟩ : syracuseStep 1947315 = 2920973) B2920973
theorem B4381469 : Blo 1945435 4381469 := bbase (se 3 (by rfl) ⟨821525, by rfl⟩ : syracuseStep 4381469 = 1643051) (by norm_num)
theorem B2920979 : Blo 1945435 2920979 := bstep (se 1 (by rfl) ⟨2190734, by rfl⟩ : syracuseStep 2920979 = 4381469) B4381469
theorem B1947319 : Blo 1945435 1947319 := bstep (se 1 (by rfl) ⟨1460489, by rfl⟩ : syracuseStep 1947319 = 2920979) B2920979
theorem B3286109 : Blo 1945435 3286109 := bbase (se 3 (by rfl) ⟨616145, by rfl⟩ : syracuseStep 3286109 = 1232291) (by norm_num)
theorem B2190739 : Blo 1945435 2190739 := bstep (se 1 (by rfl) ⟨1643054, by rfl⟩ : syracuseStep 2190739 = 3286109) B3286109
theorem B2920985 : Blo 1945435 2920985 := bstep (se 2 (by rfl) ⟨1095369, by rfl⟩ : syracuseStep 2920985 = 2190739) B2190739
theorem B1947323 : Blo 1945435 1947323 := bstep (se 1 (by rfl) ⟨1460492, by rfl⟩ : syracuseStep 1947323 = 2920985) B2920985
theorem B3509149 : Blo 1945435 3509149 := bbase (se 3 (by rfl) ⟨657965, by rfl⟩ : syracuseStep 3509149 = 1315931) (by norm_num)
theorem B4678865 : Blo 1945435 4678865 := bstep (se 2 (by rfl) ⟨1754574, by rfl⟩ : syracuseStep 4678865 = 3509149) B3509149
theorem B3119243 : Blo 1945435 3119243 := bstep (se 1 (by rfl) ⟨2339432, by rfl⟩ : syracuseStep 3119243 = 4678865) B4678865
theorem B8317981 : Blo 1945435 8317981 := bstep (se 3 (by rfl) ⟨1559621, by rfl⟩ : syracuseStep 8317981 = 3119243) B3119243
theorem B11090641 : Blo 1945435 11090641 := bstep (se 2 (by rfl) ⟨4158990, by rfl⟩ : syracuseStep 11090641 = 8317981) B8317981
theorem B14787521 : Blo 1945435 14787521 := bstep (se 2 (by rfl) ⟨5545320, by rfl⟩ : syracuseStep 14787521 = 11090641) B11090641
theorem B9858347 : Blo 1945435 9858347 := bstep (se 1 (by rfl) ⟨7393760, by rfl⟩ : syracuseStep 9858347 = 14787521) B14787521
theorem B6572231 : Blo 1945435 6572231 := bstep (se 1 (by rfl) ⟨4929173, by rfl⟩ : syracuseStep 6572231 = 9858347) B9858347
theorem B4381487 : Blo 1945435 4381487 := bstep (se 1 (by rfl) ⟨3286115, by rfl⟩ : syracuseStep 4381487 = 6572231) B6572231
theorem B2920991 : Blo 1945435 2920991 := bstep (se 1 (by rfl) ⟨2190743, by rfl⟩ : syracuseStep 2920991 = 4381487) B4381487
theorem B1947327 : Blo 1945435 1947327 := bstep (se 1 (by rfl) ⟨1460495, by rfl⟩ : syracuseStep 1947327 = 2920991) B2920991
theorem B2920997 : Blo 1945435 2920997 := bbase (se 4 (by rfl) ⟨273843, by rfl⟩ : syracuseStep 2920997 = 547687) (by norm_num)
theorem B1947331 : Blo 1945435 1947331 := bstep (se 1 (by rfl) ⟨1460498, by rfl⟩ : syracuseStep 1947331 = 2920997) B2920997
theorem B2464597 : Blo 1945435 2464597 := bbase (se 9 (by rfl) ⟨7220, by rfl⟩ : syracuseStep 2464597 = 14441) (by norm_num)
theorem B3286129 : Blo 1945435 3286129 := bstep (se 2 (by rfl) ⟨1232298, by rfl⟩ : syracuseStep 3286129 = 2464597) B2464597
theorem B4381505 : Blo 1945435 4381505 := bstep (se 2 (by rfl) ⟨1643064, by rfl⟩ : syracuseStep 4381505 = 3286129) B3286129
theorem B2921003 : Blo 1945435 2921003 := bstep (se 1 (by rfl) ⟨2190752, by rfl⟩ : syracuseStep 2921003 = 4381505) B4381505
theorem B1947335 : Blo 1945435 1947335 := bstep (se 1 (by rfl) ⟨1460501, by rfl⟩ : syracuseStep 1947335 = 2921003) B2921003
theorem B2190757 : Blo 1945435 2190757 := bbase (se 4 (by rfl) ⟨205383, by rfl⟩ : syracuseStep 2190757 = 410767) (by norm_num)
theorem B2921009 : Blo 1945435 2921009 := bstep (se 2 (by rfl) ⟨1095378, by rfl⟩ : syracuseStep 2921009 = 2190757) B2190757
theorem B1947339 : Blo 1945435 1947339 := bstep (se 1 (by rfl) ⟨1460504, by rfl⟩ : syracuseStep 1947339 = 2921009) B2921009
theorem B12477077 : Blo 1945435 12477077 := bbase (se 6 (by rfl) ⟨292431, by rfl⟩ : syracuseStep 12477077 = 584863) (by norm_num)
theorem B8318051 : Blo 1945435 8318051 := bstep (se 1 (by rfl) ⟨6238538, by rfl⟩ : syracuseStep 8318051 = 12477077) B12477077
theorem B5545367 : Blo 1945435 5545367 := bstep (se 1 (by rfl) ⟨4159025, by rfl⟩ : syracuseStep 5545367 = 8318051) B8318051
theorem B3696911 : Blo 1945435 3696911 := bstep (se 1 (by rfl) ⟨2772683, by rfl⟩ : syracuseStep 3696911 = 5545367) B5545367
theorem B2464607 : Blo 1945435 2464607 := bstep (se 1 (by rfl) ⟨1848455, by rfl⟩ : syracuseStep 2464607 = 3696911) B3696911
theorem B6572285 : Blo 1945435 6572285 := bstep (se 3 (by rfl) ⟨1232303, by rfl⟩ : syracuseStep 6572285 = 2464607) B2464607
theorem B4381523 : Blo 1945435 4381523 := bstep (se 1 (by rfl) ⟨3286142, by rfl⟩ : syracuseStep 4381523 = 6572285) B6572285
theorem B2921015 : Blo 1945435 2921015 := bstep (se 1 (by rfl) ⟨2190761, by rfl⟩ : syracuseStep 2921015 = 4381523) B4381523
theorem B1947343 : Blo 1945435 1947343 := bstep (se 1 (by rfl) ⟨1460507, by rfl⟩ : syracuseStep 1947343 = 2921015) B2921015
theorem B2921021 : Blo 1945435 2921021 := bbase (se 3 (by rfl) ⟨547691, by rfl⟩ : syracuseStep 2921021 = 1095383) (by norm_num)
theorem B1947347 : Blo 1945435 1947347 := bstep (se 1 (by rfl) ⟨1460510, by rfl⟩ : syracuseStep 1947347 = 2921021) B2921021
theorem B4381541 : Blo 1945435 4381541 := bbase (se 4 (by rfl) ⟨410769, by rfl⟩ : syracuseStep 4381541 = 821539) (by norm_num)
theorem B2921027 : Blo 1945435 2921027 := bstep (se 1 (by rfl) ⟨2190770, by rfl⟩ : syracuseStep 2921027 = 4381541) B4381541
theorem B1947351 : Blo 1945435 1947351 := bstep (se 1 (by rfl) ⟨1460513, by rfl⟩ : syracuseStep 1947351 = 2921027) B2921027
theorem B4929245 : Blo 1945435 4929245 := bbase (se 3 (by rfl) ⟨924233, by rfl⟩ : syracuseStep 4929245 = 1848467) (by norm_num)
theorem B3286163 : Blo 1945435 3286163 := bstep (se 1 (by rfl) ⟨2464622, by rfl⟩ : syracuseStep 3286163 = 4929245) B4929245
theorem B2190775 : Blo 1945435 2190775 := bstep (se 1 (by rfl) ⟨1643081, by rfl⟩ : syracuseStep 2190775 = 3286163) B3286163
theorem B2921033 : Blo 1945435 2921033 := bstep (se 2 (by rfl) ⟨1095387, by rfl⟩ : syracuseStep 2921033 = 2190775) B2190775
theorem B1947355 : Blo 1945435 1947355 := bstep (se 1 (by rfl) ⟨1460516, by rfl⟩ : syracuseStep 1947355 = 2921033) B2921033
theorem B3696941 : Blo 1945435 3696941 := bbase (se 3 (by rfl) ⟨693176, by rfl⟩ : syracuseStep 3696941 = 1386353) (by norm_num)
theorem B9858509 : Blo 1945435 9858509 := bstep (se 3 (by rfl) ⟨1848470, by rfl⟩ : syracuseStep 9858509 = 3696941) B3696941
theorem B6572339 : Blo 1945435 6572339 := bstep (se 1 (by rfl) ⟨4929254, by rfl⟩ : syracuseStep 6572339 = 9858509) B9858509
theorem B4381559 : Blo 1945435 4381559 := bstep (se 1 (by rfl) ⟨3286169, by rfl⟩ : syracuseStep 4381559 = 6572339) B6572339
theorem B2921039 : Blo 1945435 2921039 := bstep (se 1 (by rfl) ⟨2190779, by rfl⟩ : syracuseStep 2921039 = 4381559) B4381559
theorem B1947359 : Blo 1945435 1947359 := bstep (se 1 (by rfl) ⟨1460519, by rfl⟩ : syracuseStep 1947359 = 2921039) B2921039
theorem B2921045 : Blo 1945435 2921045 := bbase (se 8 (by rfl) ⟨17115, by rfl⟩ : syracuseStep 2921045 = 34231) (by norm_num)
theorem B1947363 : Blo 1945435 1947363 := bstep (se 1 (by rfl) ⟨1460522, by rfl⟩ : syracuseStep 1947363 = 2921045) B2921045
theorem B14036885 : Blo 1945435 14036885 := bbase (se 6 (by rfl) ⟨328989, by rfl⟩ : syracuseStep 14036885 = 657979) (by norm_num)
theorem B9357923 : Blo 1945435 9357923 := bstep (se 1 (by rfl) ⟨7018442, by rfl⟩ : syracuseStep 9357923 = 14036885) B14036885
theorem B6238615 : Blo 1945435 6238615 := bstep (se 1 (by rfl) ⟨4678961, by rfl⟩ : syracuseStep 6238615 = 9357923) B9357923
theorem B8318153 : Blo 1945435 8318153 := bstep (se 2 (by rfl) ⟨3119307, by rfl⟩ : syracuseStep 8318153 = 6238615) B6238615
theorem B5545435 : Blo 1945435 5545435 := bstep (se 1 (by rfl) ⟨4159076, by rfl⟩ : syracuseStep 5545435 = 8318153) B8318153
theorem B7393913 : Blo 1945435 7393913 := bstep (se 2 (by rfl) ⟨2772717, by rfl⟩ : syracuseStep 7393913 = 5545435) B5545435
theorem B4929275 : Blo 1945435 4929275 := bstep (se 1 (by rfl) ⟨3696956, by rfl⟩ : syracuseStep 4929275 = 7393913) B7393913
theorem B3286183 : Blo 1945435 3286183 := bstep (se 1 (by rfl) ⟨2464637, by rfl⟩ : syracuseStep 3286183 = 4929275) B4929275
theorem B4381577 : Blo 1945435 4381577 := bstep (se 2 (by rfl) ⟨1643091, by rfl⟩ : syracuseStep 4381577 = 3286183) B3286183
theorem B2921051 : Blo 1945435 2921051 := bstep (se 1 (by rfl) ⟨2190788, by rfl⟩ : syracuseStep 2921051 = 4381577) B4381577
theorem B1947367 : Blo 1945435 1947367 := bstep (se 1 (by rfl) ⟨1460525, by rfl⟩ : syracuseStep 1947367 = 2921051) B2921051
theorem B2190793 : Blo 1945435 2190793 := bbase (se 2 (by rfl) ⟨821547, by rfl⟩ : syracuseStep 2190793 = 1643095) (by norm_num)
theorem B2921057 : Blo 1945435 2921057 := bstep (se 2 (by rfl) ⟨1095396, by rfl⟩ : syracuseStep 2921057 = 2190793) B2190793
theorem B1947371 : Blo 1945435 1947371 := bstep (se 1 (by rfl) ⟨1460528, by rfl⟩ : syracuseStep 1947371 = 2921057) B2921057
theorem B16636373 : Blo 1945435 16636373 := bbase (se 7 (by rfl) ⟨194957, by rfl⟩ : syracuseStep 16636373 = 389915) (by norm_num)
theorem B11090915 : Blo 1945435 11090915 := bstep (se 1 (by rfl) ⟨8318186, by rfl⟩ : syracuseStep 11090915 = 16636373) B16636373
theorem B7393943 : Blo 1945435 7393943 := bstep (se 1 (by rfl) ⟨5545457, by rfl⟩ : syracuseStep 7393943 = 11090915) B11090915
theorem B4929295 : Blo 1945435 4929295 := bstep (se 1 (by rfl) ⟨3696971, by rfl⟩ : syracuseStep 4929295 = 7393943) B7393943
theorem B6572393 : Blo 1945435 6572393 := bstep (se 2 (by rfl) ⟨2464647, by rfl⟩ : syracuseStep 6572393 = 4929295) B4929295
theorem B4381595 : Blo 1945435 4381595 := bstep (se 1 (by rfl) ⟨3286196, by rfl⟩ : syracuseStep 4381595 = 6572393) B6572393
theorem B2921063 : Blo 1945435 2921063 := bstep (se 1 (by rfl) ⟨2190797, by rfl⟩ : syracuseStep 2921063 = 4381595) B4381595
theorem B1947375 : Blo 1945435 1947375 := bstep (se 1 (by rfl) ⟨1460531, by rfl⟩ : syracuseStep 1947375 = 2921063) B2921063
theorem B2921069 : Blo 1945435 2921069 := bbase (se 3 (by rfl) ⟨547700, by rfl⟩ : syracuseStep 2921069 = 1095401) (by norm_num)
theorem B1947379 : Blo 1945435 1947379 := bstep (se 1 (by rfl) ⟨1460534, by rfl⟩ : syracuseStep 1947379 = 2921069) B2921069
theorem B4381613 : Blo 1945435 4381613 := bbase (se 3 (by rfl) ⟨821552, by rfl⟩ : syracuseStep 4381613 = 1643105) (by norm_num)
theorem B2921075 : Blo 1945435 2921075 := bstep (se 1 (by rfl) ⟨2190806, by rfl⟩ : syracuseStep 2921075 = 4381613) B4381613
theorem B1947383 : Blo 1945435 1947383 := bstep (se 1 (by rfl) ⟨1460537, by rfl⟩ : syracuseStep 1947383 = 2921075) B2921075
theorem B5545493 : Blo 1945435 5545493 := bbase (se 6 (by rfl) ⟨129972, by rfl⟩ : syracuseStep 5545493 = 259945) (by norm_num)
theorem B3696995 : Blo 1945435 3696995 := bstep (se 1 (by rfl) ⟨2772746, by rfl⟩ : syracuseStep 3696995 = 5545493) B5545493
theorem B2464663 : Blo 1945435 2464663 := bstep (se 1 (by rfl) ⟨1848497, by rfl⟩ : syracuseStep 2464663 = 3696995) B3696995
theorem B3286217 : Blo 1945435 3286217 := bstep (se 2 (by rfl) ⟨1232331, by rfl⟩ : syracuseStep 3286217 = 2464663) B2464663
theorem B2190811 : Blo 1945435 2190811 := bstep (se 1 (by rfl) ⟨1643108, by rfl⟩ : syracuseStep 2190811 = 3286217) B3286217
theorem B2921081 : Blo 1945435 2921081 := bstep (se 2 (by rfl) ⟨1095405, by rfl⟩ : syracuseStep 2921081 = 2190811) B2190811
theorem B1947387 : Blo 1945435 1947387 := bstep (se 1 (by rfl) ⟨1460540, by rfl⟩ : syracuseStep 1947387 = 2921081) B2921081
theorem B11242325 : Blo 1945435 11242325 := bbase (se 9 (by rfl) ⟨32936, by rfl⟩ : syracuseStep 11242325 = 65873) (by norm_num)
theorem B29979533 : Blo 1945435 29979533 := bstep (se 3 (by rfl) ⟨5621162, by rfl⟩ : syracuseStep 29979533 = 11242325) B11242325
theorem B19986355 : Blo 1945435 19986355 := bstep (se 1 (by rfl) ⟨14989766, by rfl⟩ : syracuseStep 19986355 = 29979533) B29979533
theorem B26648473 : Blo 1945435 26648473 := bstep (se 2 (by rfl) ⟨9993177, by rfl⟩ : syracuseStep 26648473 = 19986355) B19986355
theorem B35531297 : Blo 1945435 35531297 := bstep (se 2 (by rfl) ⟨13324236, by rfl⟩ : syracuseStep 35531297 = 26648473) B26648473
theorem B23687531 : Blo 1945435 23687531 := bstep (se 1 (by rfl) ⟨17765648, by rfl⟩ : syracuseStep 23687531 = 35531297) B35531297
theorem B15791687 : Blo 1945435 15791687 := bstep (se 1 (by rfl) ⟨11843765, by rfl⟩ : syracuseStep 15791687 = 23687531) B23687531
theorem B10527791 : Blo 1945435 10527791 := bstep (se 1 (by rfl) ⟨7895843, by rfl⟩ : syracuseStep 10527791 = 15791687) B15791687
theorem B28074109 : Blo 1945435 28074109 := bstep (se 3 (by rfl) ⟨5263895, by rfl⟩ : syracuseStep 28074109 = 10527791) B10527791
theorem B37432145 : Blo 1945435 37432145 := bstep (se 2 (by rfl) ⟨14037054, by rfl⟩ : syracuseStep 37432145 = 28074109) B28074109
theorem B24954763 : Blo 1945435 24954763 := bstep (se 1 (by rfl) ⟨18716072, by rfl⟩ : syracuseStep 24954763 = 37432145) B37432145
theorem B33273017 : Blo 1945435 33273017 := bstep (se 2 (by rfl) ⟨12477381, by rfl⟩ : syracuseStep 33273017 = 24954763) B24954763
theorem B22182011 : Blo 1945435 22182011 := bstep (se 1 (by rfl) ⟨16636508, by rfl⟩ : syracuseStep 22182011 = 33273017) B33273017
theorem B14788007 : Blo 1945435 14788007 := bstep (se 1 (by rfl) ⟨11091005, by rfl⟩ : syracuseStep 14788007 = 22182011) B22182011
theorem B9858671 : Blo 1945435 9858671 := bstep (se 1 (by rfl) ⟨7394003, by rfl⟩ : syracuseStep 9858671 = 14788007) B14788007
theorem B6572447 : Blo 1945435 6572447 := bstep (se 1 (by rfl) ⟨4929335, by rfl⟩ : syracuseStep 6572447 = 9858671) B9858671
theorem B4381631 : Blo 1945435 4381631 := bstep (se 1 (by rfl) ⟨3286223, by rfl⟩ : syracuseStep 4381631 = 6572447) B6572447
theorem B2921087 : Blo 1945435 2921087 := bstep (se 1 (by rfl) ⟨2190815, by rfl⟩ : syracuseStep 2921087 = 4381631) B4381631
theorem B1947391 : Blo 1945435 1947391 := bstep (se 1 (by rfl) ⟨1460543, by rfl⟩ : syracuseStep 1947391 = 2921087) B2921087
theorem B2921093 : Blo 1945435 2921093 := bbase (se 4 (by rfl) ⟨273852, by rfl⟩ : syracuseStep 2921093 = 547705) (by norm_num)
theorem B1947395 : Blo 1945435 1947395 := bstep (se 1 (by rfl) ⟨1460546, by rfl⟩ : syracuseStep 1947395 = 2921093) B2921093
theorem B3286237 : Blo 1945435 3286237 := bbase (se 3 (by rfl) ⟨616169, by rfl⟩ : syracuseStep 3286237 = 1232339) (by norm_num)
theorem B4381649 : Blo 1945435 4381649 := bstep (se 2 (by rfl) ⟨1643118, by rfl⟩ : syracuseStep 4381649 = 3286237) B3286237
theorem B2921099 : Blo 1945435 2921099 := bstep (se 1 (by rfl) ⟨2190824, by rfl⟩ : syracuseStep 2921099 = 4381649) B4381649
theorem B1947399 : Blo 1945435 1947399 := bstep (se 1 (by rfl) ⟨1460549, by rfl⟩ : syracuseStep 1947399 = 2921099) B2921099
theorem B2190829 : Blo 1945435 2190829 := bbase (se 3 (by rfl) ⟨410780, by rfl⟩ : syracuseStep 2190829 = 821561) (by norm_num)
theorem B2921105 : Blo 1945435 2921105 := bstep (se 2 (by rfl) ⟨1095414, by rfl⟩ : syracuseStep 2921105 = 2190829) B2190829
theorem B1947403 : Blo 1945435 1947403 := bstep (se 1 (by rfl) ⟨1460552, by rfl⟩ : syracuseStep 1947403 = 2921105) B2921105
theorem B6572501 : Blo 1945435 6572501 := bbase (se 7 (by rfl) ⟨77021, by rfl⟩ : syracuseStep 6572501 = 154043) (by norm_num)
theorem B4381667 : Blo 1945435 4381667 := bstep (se 1 (by rfl) ⟨3286250, by rfl⟩ : syracuseStep 4381667 = 6572501) B6572501
theorem B2921111 : Blo 1945435 2921111 := bstep (se 1 (by rfl) ⟨2190833, by rfl⟩ : syracuseStep 2921111 = 4381667) B4381667
theorem B1947407 : Blo 1945435 1947407 := bstep (se 1 (by rfl) ⟨1460555, by rfl⟩ : syracuseStep 1947407 = 2921111) B2921111
theorem B2921117 : Blo 1945435 2921117 := bbase (se 3 (by rfl) ⟨547709, by rfl⟩ : syracuseStep 2921117 = 1095419) (by norm_num)
theorem B1947411 : Blo 1945435 1947411 := bstep (se 1 (by rfl) ⟨1460558, by rfl⟩ : syracuseStep 1947411 = 2921117) B2921117
theorem B4381685 : Blo 1945435 4381685 := bbase (se 5 (by rfl) ⟨205391, by rfl⟩ : syracuseStep 4381685 = 410783) (by norm_num)
theorem B2921123 : Blo 1945435 2921123 := bstep (se 1 (by rfl) ⟨2190842, by rfl⟩ : syracuseStep 2921123 = 4381685) B4381685
theorem B1947415 : Blo 1945435 1947415 := bstep (se 1 (by rfl) ⟨1460561, by rfl⟩ : syracuseStep 1947415 = 2921123) B2921123
theorem B4441477 : Blo 1945435 4441477 := bbase (se 4 (by rfl) ⟨416388, by rfl⟩ : syracuseStep 4441477 = 832777) (by norm_num)
theorem B5921969 : Blo 1945435 5921969 := bstep (se 2 (by rfl) ⟨2220738, by rfl⟩ : syracuseStep 5921969 = 4441477) B4441477
theorem B15791917 : Blo 1945435 15791917 := bstep (se 3 (by rfl) ⟨2960984, by rfl⟩ : syracuseStep 15791917 = 5921969) B5921969
theorem B21055889 : Blo 1945435 21055889 := bstep (se 2 (by rfl) ⟨7895958, by rfl⟩ : syracuseStep 21055889 = 15791917) B15791917
theorem B56149037 : Blo 1945435 56149037 := bstep (se 3 (by rfl) ⟨10527944, by rfl⟩ : syracuseStep 56149037 = 21055889) B21055889
theorem B37432691 : Blo 1945435 37432691 := bstep (se 1 (by rfl) ⟨28074518, by rfl⟩ : syracuseStep 37432691 = 56149037) B56149037
theorem B24955127 : Blo 1945435 24955127 := bstep (se 1 (by rfl) ⟨18716345, by rfl⟩ : syracuseStep 24955127 = 37432691) B37432691
theorem B16636751 : Blo 1945435 16636751 := bstep (se 1 (by rfl) ⟨12477563, by rfl⟩ : syracuseStep 16636751 = 24955127) B24955127
theorem B11091167 : Blo 1945435 11091167 := bstep (se 1 (by rfl) ⟨8318375, by rfl⟩ : syracuseStep 11091167 = 16636751) B16636751
theorem B7394111 : Blo 1945435 7394111 := bstep (se 1 (by rfl) ⟨5545583, by rfl⟩ : syracuseStep 7394111 = 11091167) B11091167
theorem B4929407 : Blo 1945435 4929407 := bstep (se 1 (by rfl) ⟨3697055, by rfl⟩ : syracuseStep 4929407 = 7394111) B7394111
theorem B3286271 : Blo 1945435 3286271 := bstep (se 1 (by rfl) ⟨2464703, by rfl⟩ : syracuseStep 3286271 = 4929407) B4929407
theorem B2190847 : Blo 1945435 2190847 := bstep (se 1 (by rfl) ⟨1643135, by rfl⟩ : syracuseStep 2190847 = 3286271) B3286271
theorem B2921129 : Blo 1945435 2921129 := bstep (se 2 (by rfl) ⟨1095423, by rfl⟩ : syracuseStep 2921129 = 2190847) B2190847
theorem B1947419 : Blo 1945435 1947419 := bstep (se 1 (by rfl) ⟨1460564, by rfl⟩ : syracuseStep 1947419 = 2921129) B2921129
theorem B2772797 : Blo 1945435 2772797 := bbase (se 3 (by rfl) ⟨519899, by rfl⟩ : syracuseStep 2772797 = 1039799) (by norm_num)
theorem B7394125 : Blo 1945435 7394125 := bstep (se 3 (by rfl) ⟨1386398, by rfl⟩ : syracuseStep 7394125 = 2772797) B2772797
theorem B9858833 : Blo 1945435 9858833 := bstep (se 2 (by rfl) ⟨3697062, by rfl⟩ : syracuseStep 9858833 = 7394125) B7394125
theorem B6572555 : Blo 1945435 6572555 := bstep (se 1 (by rfl) ⟨4929416, by rfl⟩ : syracuseStep 6572555 = 9858833) B9858833
theorem B4381703 : Blo 1945435 4381703 := bstep (se 1 (by rfl) ⟨3286277, by rfl⟩ : syracuseStep 4381703 = 6572555) B6572555
theorem B2921135 : Blo 1945435 2921135 := bstep (se 1 (by rfl) ⟨2190851, by rfl⟩ : syracuseStep 2921135 = 4381703) B4381703
theorem B1947423 : Blo 1945435 1947423 := bstep (se 1 (by rfl) ⟨1460567, by rfl⟩ : syracuseStep 1947423 = 2921135) B2921135
theorem B2921141 : Blo 1945435 2921141 := bbase (se 5 (by rfl) ⟨136928, by rfl⟩ : syracuseStep 2921141 = 273857) (by norm_num)
theorem B1947427 : Blo 1945435 1947427 := bstep (se 1 (by rfl) ⟨1460570, by rfl⟩ : syracuseStep 1947427 = 2921141) B2921141
theorem B4929437 : Blo 1945435 4929437 := bbase (se 3 (by rfl) ⟨924269, by rfl⟩ : syracuseStep 4929437 = 1848539) (by norm_num)
theorem B3286291 : Blo 1945435 3286291 := bstep (se 1 (by rfl) ⟨2464718, by rfl⟩ : syracuseStep 3286291 = 4929437) B4929437
theorem B4381721 : Blo 1945435 4381721 := bstep (se 2 (by rfl) ⟨1643145, by rfl⟩ : syracuseStep 4381721 = 3286291) B3286291
theorem B2921147 : Blo 1945435 2921147 := bstep (se 1 (by rfl) ⟨2190860, by rfl⟩ : syracuseStep 2921147 = 4381721) B4381721
theorem B1947431 : Blo 1945435 1947431 := bstep (se 1 (by rfl) ⟨1460573, by rfl⟩ : syracuseStep 1947431 = 2921147) B2921147
theorem B2190865 : Blo 1945435 2190865 := bbase (se 2 (by rfl) ⟨821574, by rfl⟩ : syracuseStep 2190865 = 1643149) (by norm_num)
theorem B2921153 : Blo 1945435 2921153 := bstep (se 2 (by rfl) ⟨1095432, by rfl⟩ : syracuseStep 2921153 = 2190865) B2190865
theorem B1947435 : Blo 1945435 1947435 := bstep (se 1 (by rfl) ⟨1460576, by rfl⟩ : syracuseStep 1947435 = 2921153) B2921153
theorem C0 (j : ℕ) (h1 : 486358 ≤ j) (h2 : j ≤ 486858) : Blo 1945435 (4 * j + 3) := by
  interval_cases j
  · exact B1945435
  · exact B1945439
  · exact B1945443
  · exact B1945447
  · exact B1945451
  · exact B1945455
  · exact B1945459
  · exact B1945463
  · exact B1945467
  · exact B1945471
  · exact B1945475
  · exact B1945479
  · exact B1945483
  · exact B1945487
  · exact B1945491
  · exact B1945495
  · exact B1945499
  · exact B1945503
  · exact B1945507
  · exact B1945511
  · exact B1945515
  · exact B1945519
  · exact B1945523
  · exact B1945527
  · exact B1945531
  · exact B1945535
  · exact B1945539
  · exact B1945543
  · exact B1945547
  · exact B1945551
  · exact B1945555
  · exact B1945559
  · exact B1945563
  · exact B1945567
  · exact B1945571
  · exact B1945575
  · exact B1945579
  · exact B1945583
  · exact B1945587
  · exact B1945591
  · exact B1945595
  · exact B1945599
  · exact B1945603
  · exact B1945607
  · exact B1945611
  · exact B1945615
  · exact B1945619
  · exact B1945623
  · exact B1945627
  · exact B1945631
  · exact B1945635
  · exact B1945639
  · exact B1945643
  · exact B1945647
  · exact B1945651
  · exact B1945655
  · exact B1945659
  · exact B1945663
  · exact B1945667
  · exact B1945671
  · exact B1945675
  · exact B1945679
  · exact B1945683
  · exact B1945687
  · exact B1945691
  · exact B1945695
  · exact B1945699
  · exact B1945703
  · exact B1945707
  · exact B1945711
  · exact B1945715
  · exact B1945719
  · exact B1945723
  · exact B1945727
  · exact B1945731
  · exact B1945735
  · exact B1945739
  · exact B1945743
  · exact B1945747
  · exact B1945751
  · exact B1945755
  · exact B1945759
  · exact B1945763
  · exact B1945767
  · exact B1945771
  · exact B1945775
  · exact B1945779
  · exact B1945783
  · exact B1945787
  · exact B1945791
  · exact B1945795
  · exact B1945799
  · exact B1945803
  · exact B1945807
  · exact B1945811
  · exact B1945815
  · exact B1945819
  · exact B1945823
  · exact B1945827
  · exact B1945831
  · exact B1945835
  · exact B1945839
  · exact B1945843
  · exact B1945847
  · exact B1945851
  · exact B1945855
  · exact B1945859
  · exact B1945863
  · exact B1945867
  · exact B1945871
  · exact B1945875
  · exact B1945879
  · exact B1945883
  · exact B1945887
  · exact B1945891
  · exact B1945895
  · exact B1945899
  · exact B1945903
  · exact B1945907
  · exact B1945911
  · exact B1945915
  · exact B1945919
  · exact B1945923
  · exact B1945927
  · exact B1945931
  · exact B1945935
  · exact B1945939
  · exact B1945943
  · exact B1945947
  · exact B1945951
  · exact B1945955
  · exact B1945959
  · exact B1945963
  · exact B1945967
  · exact B1945971
  · exact B1945975
  · exact B1945979
  · exact B1945983
  · exact B1945987
  · exact B1945991
  · exact B1945995
  · exact B1945999
  · exact B1946003
  · exact B1946007
  · exact B1946011
  · exact B1946015
  · exact B1946019
  · exact B1946023
  · exact B1946027
  · exact B1946031
  · exact B1946035
  · exact B1946039
  · exact B1946043
  · exact B1946047
  · exact B1946051
  · exact B1946055
  · exact B1946059
  · exact B1946063
  · exact B1946067
  · exact B1946071
  · exact B1946075
  · exact B1946079
  · exact B1946083
  · exact B1946087
  · exact B1946091
  · exact B1946095
  · exact B1946099
  · exact B1946103
  · exact B1946107
  · exact B1946111
  · exact B1946115
  · exact B1946119
  · exact B1946123
  · exact B1946127
  · exact B1946131
  · exact B1946135
  · exact B1946139
  · exact B1946143
  · exact B1946147
  · exact B1946151
  · exact B1946155
  · exact B1946159
  · exact B1946163
  · exact B1946167
  · exact B1946171
  · exact B1946175
  · exact B1946179
  · exact B1946183
  · exact B1946187
  · exact B1946191
  · exact B1946195
  · exact B1946199
  · exact B1946203
  · exact B1946207
  · exact B1946211
  · exact B1946215
  · exact B1946219
  · exact B1946223
  · exact B1946227
  · exact B1946231
  · exact B1946235
  · exact B1946239
  · exact B1946243
  · exact B1946247
  · exact B1946251
  · exact B1946255
  · exact B1946259
  · exact B1946263
  · exact B1946267
  · exact B1946271
  · exact B1946275
  · exact B1946279
  · exact B1946283
  · exact B1946287
  · exact B1946291
  · exact B1946295
  · exact B1946299
  · exact B1946303
  · exact B1946307
  · exact B1946311
  · exact B1946315
  · exact B1946319
  · exact B1946323
  · exact B1946327
  · exact B1946331
  · exact B1946335
  · exact B1946339
  · exact B1946343
  · exact B1946347
  · exact B1946351
  · exact B1946355
  · exact B1946359
  · exact B1946363
  · exact B1946367
  · exact B1946371
  · exact B1946375
  · exact B1946379
  · exact B1946383
  · exact B1946387
  · exact B1946391
  · exact B1946395
  · exact B1946399
  · exact B1946403
  · exact B1946407
  · exact B1946411
  · exact B1946415
  · exact B1946419
  · exact B1946423
  · exact B1946427
  · exact B1946431
  · exact B1946435
  · exact B1946439
  · exact B1946443
  · exact B1946447
  · exact B1946451
  · exact B1946455
  · exact B1946459
  · exact B1946463
  · exact B1946467
  · exact B1946471
  · exact B1946475
  · exact B1946479
  · exact B1946483
  · exact B1946487
  · exact B1946491
  · exact B1946495
  · exact B1946499
  · exact B1946503
  · exact B1946507
  · exact B1946511
  · exact B1946515
  · exact B1946519
  · exact B1946523
  · exact B1946527
  · exact B1946531
  · exact B1946535
  · exact B1946539
  · exact B1946543
  · exact B1946547
  · exact B1946551
  · exact B1946555
  · exact B1946559
  · exact B1946563
  · exact B1946567
  · exact B1946571
  · exact B1946575
  · exact B1946579
  · exact B1946583
  · exact B1946587
  · exact B1946591
  · exact B1946595
  · exact B1946599
  · exact B1946603
  · exact B1946607
  · exact B1946611
  · exact B1946615
  · exact B1946619
  · exact B1946623
  · exact B1946627
  · exact B1946631
  · exact B1946635
  · exact B1946639
  · exact B1946643
  · exact B1946647
  · exact B1946651
  · exact B1946655
  · exact B1946659
  · exact B1946663
  · exact B1946667
  · exact B1946671
  · exact B1946675
  · exact B1946679
  · exact B1946683
  · exact B1946687
  · exact B1946691
  · exact B1946695
  · exact B1946699
  · exact B1946703
  · exact B1946707
  · exact B1946711
  · exact B1946715
  · exact B1946719
  · exact B1946723
  · exact B1946727
  · exact B1946731
  · exact B1946735
  · exact B1946739
  · exact B1946743
  · exact B1946747
  · exact B1946751
  · exact B1946755
  · exact B1946759
  · exact B1946763
  · exact B1946767
  · exact B1946771
  · exact B1946775
  · exact B1946779
  · exact B1946783
  · exact B1946787
  · exact B1946791
  · exact B1946795
  · exact B1946799
  · exact B1946803
  · exact B1946807
  · exact B1946811
  · exact B1946815
  · exact B1946819
  · exact B1946823
  · exact B1946827
  · exact B1946831
  · exact B1946835
  · exact B1946839
  · exact B1946843
  · exact B1946847
  · exact B1946851
  · exact B1946855
  · exact B1946859
  · exact B1946863
  · exact B1946867
  · exact B1946871
  · exact B1946875
  · exact B1946879
  · exact B1946883
  · exact B1946887
  · exact B1946891
  · exact B1946895
  · exact B1946899
  · exact B1946903
  · exact B1946907
  · exact B1946911
  · exact B1946915
  · exact B1946919
  · exact B1946923
  · exact B1946927
  · exact B1946931
  · exact B1946935
  · exact B1946939
  · exact B1946943
  · exact B1946947
  · exact B1946951
  · exact B1946955
  · exact B1946959
  · exact B1946963
  · exact B1946967
  · exact B1946971
  · exact B1946975
  · exact B1946979
  · exact B1946983
  · exact B1946987
  · exact B1946991
  · exact B1946995
  · exact B1946999
  · exact B1947003
  · exact B1947007
  · exact B1947011
  · exact B1947015
  · exact B1947019
  · exact B1947023
  · exact B1947027
  · exact B1947031
  · exact B1947035
  · exact B1947039
  · exact B1947043
  · exact B1947047
  · exact B1947051
  · exact B1947055
  · exact B1947059
  · exact B1947063
  · exact B1947067
  · exact B1947071
  · exact B1947075
  · exact B1947079
  · exact B1947083
  · exact B1947087
  · exact B1947091
  · exact B1947095
  · exact B1947099
  · exact B1947103
  · exact B1947107
  · exact B1947111
  · exact B1947115
  · exact B1947119
  · exact B1947123
  · exact B1947127
  · exact B1947131
  · exact B1947135
  · exact B1947139
  · exact B1947143
  · exact B1947147
  · exact B1947151
  · exact B1947155
  · exact B1947159
  · exact B1947163
  · exact B1947167
  · exact B1947171
  · exact B1947175
  · exact B1947179
  · exact B1947183
  · exact B1947187
  · exact B1947191
  · exact B1947195
  · exact B1947199
  · exact B1947203
  · exact B1947207
  · exact B1947211
  · exact B1947215
  · exact B1947219
  · exact B1947223
  · exact B1947227
  · exact B1947231
  · exact B1947235
  · exact B1947239
  · exact B1947243
  · exact B1947247
  · exact B1947251
  · exact B1947255
  · exact B1947259
  · exact B1947263
  · exact B1947267
  · exact B1947271
  · exact B1947275
  · exact B1947279
  · exact B1947283
  · exact B1947287
  · exact B1947291
  · exact B1947295
  · exact B1947299
  · exact B1947303
  · exact B1947307
  · exact B1947311
  · exact B1947315
  · exact B1947319
  · exact B1947323
  · exact B1947327
  · exact B1947331
  · exact B1947335
  · exact B1947339
  · exact B1947343
  · exact B1947347
  · exact B1947351
  · exact B1947355
  · exact B1947359
  · exact B1947363
  · exact B1947367
  · exact B1947371
  · exact B1947375
  · exact B1947379
  · exact B1947383
  · exact B1947387
  · exact B1947391
  · exact B1947395
  · exact B1947399
  · exact B1947403
  · exact B1947407
  · exact B1947411
  · exact B1947415
  · exact B1947419
  · exact B1947423
  · exact B1947427
  · exact B1947431
  · exact B1947435
theorem solution (m : ℕ) (hlo : 1945435 ≤ m) (hhi : m ≤ 1947435) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 486358 ≤ j := by omega
    have hj2 : j ≤ 486858 := by omega
    have hb : Blo 1945435 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
