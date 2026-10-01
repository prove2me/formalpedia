-- Prove2me | solution 1 for syracuse_descends_range_2247435_2249435
-- status  : ACCEPTED   (prove)
-- author  : @chstdu
-- created : 2026-09-23T17:49:04.389311+00:00
-- url     : https://prove2.me/submissions/83450b32-1ec4-4d60-8080-9fd5a6fa94fc

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

theorem B2528365 : Blo 2247435 2528365 := bbase (se 3 (by rfl) ⟨474068, by rfl⟩ : syracuseStep 2528365 = 948137) (by norm_num)
theorem B3371153 : Blo 2247435 3371153 := bstep (se 2 (by rfl) ⟨1264182, by rfl⟩ : syracuseStep 3371153 = 2528365) B2528365
theorem B2247435 : Blo 2247435 2247435 := bstep (se 1 (by rfl) ⟨1685576, by rfl⟩ : syracuseStep 2247435 = 3371153) B3371153
theorem B7585109 : Blo 2247435 7585109 := bbase (se 11 (by rfl) ⟨5555, by rfl⟩ : syracuseStep 7585109 = 11111) (by norm_num)
theorem B5056739 : Blo 2247435 5056739 := bstep (se 1 (by rfl) ⟨3792554, by rfl⟩ : syracuseStep 5056739 = 7585109) B7585109
theorem B3371159 : Blo 2247435 3371159 := bstep (se 1 (by rfl) ⟨2528369, by rfl⟩ : syracuseStep 3371159 = 5056739) B5056739
theorem B2247439 : Blo 2247435 2247439 := bstep (se 1 (by rfl) ⟨1685579, by rfl⟩ : syracuseStep 2247439 = 3371159) B3371159
theorem B3371165 : Blo 2247435 3371165 := bbase (se 3 (by rfl) ⟨632093, by rfl⟩ : syracuseStep 3371165 = 1264187) (by norm_num)
theorem B2247443 : Blo 2247435 2247443 := bstep (se 1 (by rfl) ⟨1685582, by rfl⟩ : syracuseStep 2247443 = 3371165) B3371165
theorem B5056757 : Blo 2247435 5056757 := bbase (se 5 (by rfl) ⟨237035, by rfl⟩ : syracuseStep 5056757 = 474071) (by norm_num)
theorem B3371171 : Blo 2247435 3371171 := bstep (se 1 (by rfl) ⟨2528378, by rfl⟩ : syracuseStep 3371171 = 5056757) B5056757
theorem B2247447 : Blo 2247435 2247447 := bstep (se 1 (by rfl) ⟨1685585, by rfl⟩ : syracuseStep 2247447 = 3371171) B3371171
theorem B5195693 : Blo 2247435 5195693 := bbase (se 3 (by rfl) ⟨974192, by rfl⟩ : syracuseStep 5195693 = 1948385) (by norm_num)
theorem B3463795 : Blo 2247435 3463795 := bstep (se 1 (by rfl) ⟨2597846, by rfl⟩ : syracuseStep 3463795 = 5195693) B5195693
theorem B4618393 : Blo 2247435 4618393 := bstep (se 2 (by rfl) ⟨1731897, by rfl⟩ : syracuseStep 4618393 = 3463795) B3463795
theorem B98525717 : Blo 2247435 98525717 := bstep (se 6 (by rfl) ⟨2309196, by rfl⟩ : syracuseStep 98525717 = 4618393) B4618393
theorem B65683811 : Blo 2247435 65683811 := bstep (se 1 (by rfl) ⟨49262858, by rfl⟩ : syracuseStep 65683811 = 98525717) B98525717
theorem B43789207 : Blo 2247435 43789207 := bstep (se 1 (by rfl) ⟨32841905, by rfl⟩ : syracuseStep 43789207 = 65683811) B65683811
theorem B58385609 : Blo 2247435 58385609 := bstep (se 2 (by rfl) ⟨21894603, by rfl⟩ : syracuseStep 58385609 = 43789207) B43789207
theorem B38923739 : Blo 2247435 38923739 := bstep (se 1 (by rfl) ⟨29192804, by rfl⟩ : syracuseStep 38923739 = 58385609) B58385609
theorem B25949159 : Blo 2247435 25949159 := bstep (se 1 (by rfl) ⟨19461869, by rfl⟩ : syracuseStep 25949159 = 38923739) B38923739
theorem B17299439 : Blo 2247435 17299439 := bstep (se 1 (by rfl) ⟨12974579, by rfl⟩ : syracuseStep 17299439 = 25949159) B25949159
theorem B11532959 : Blo 2247435 11532959 := bstep (se 1 (by rfl) ⟨8649719, by rfl⟩ : syracuseStep 11532959 = 17299439) B17299439
theorem B7688639 : Blo 2247435 7688639 := bstep (se 1 (by rfl) ⟨5766479, by rfl⟩ : syracuseStep 7688639 = 11532959) B11532959
theorem B20503037 : Blo 2247435 20503037 := bstep (se 3 (by rfl) ⟨3844319, by rfl⟩ : syracuseStep 20503037 = 7688639) B7688639
theorem B13668691 : Blo 2247435 13668691 := bstep (se 1 (by rfl) ⟨10251518, by rfl⟩ : syracuseStep 13668691 = 20503037) B20503037
theorem B18224921 : Blo 2247435 18224921 := bstep (se 2 (by rfl) ⟨6834345, by rfl⟩ : syracuseStep 18224921 = 13668691) B13668691
theorem B12149947 : Blo 2247435 12149947 := bstep (se 1 (by rfl) ⟨9112460, by rfl⟩ : syracuseStep 12149947 = 18224921) B18224921
theorem B16199929 : Blo 2247435 16199929 := bstep (se 2 (by rfl) ⟨6074973, by rfl⟩ : syracuseStep 16199929 = 12149947) B12149947
theorem B21599905 : Blo 2247435 21599905 := bstep (se 2 (by rfl) ⟨8099964, by rfl⟩ : syracuseStep 21599905 = 16199929) B16199929
theorem B28799873 : Blo 2247435 28799873 := bstep (se 2 (by rfl) ⟨10799952, by rfl⟩ : syracuseStep 28799873 = 21599905) B21599905
theorem B19199915 : Blo 2247435 19199915 := bstep (se 1 (by rfl) ⟨14399936, by rfl⟩ : syracuseStep 19199915 = 28799873) B28799873
theorem B12799943 : Blo 2247435 12799943 := bstep (se 1 (by rfl) ⟨9599957, by rfl⟩ : syracuseStep 12799943 = 19199915) B19199915
theorem B8533295 : Blo 2247435 8533295 := bstep (se 1 (by rfl) ⟨6399971, by rfl⟩ : syracuseStep 8533295 = 12799943) B12799943
theorem B5688863 : Blo 2247435 5688863 := bstep (se 1 (by rfl) ⟨4266647, by rfl⟩ : syracuseStep 5688863 = 8533295) B8533295
theorem B3792575 : Blo 2247435 3792575 := bstep (se 1 (by rfl) ⟨2844431, by rfl⟩ : syracuseStep 3792575 = 5688863) B5688863
theorem B2528383 : Blo 2247435 2528383 := bstep (se 1 (by rfl) ⟨1896287, by rfl⟩ : syracuseStep 2528383 = 3792575) B3792575
theorem B3371177 : Blo 2247435 3371177 := bstep (se 2 (by rfl) ⟨1264191, by rfl⟩ : syracuseStep 3371177 = 2528383) B2528383
theorem B2247451 : Blo 2247435 2247451 := bstep (se 1 (by rfl) ⟨1685588, by rfl⟩ : syracuseStep 2247451 = 3371177) B3371177
theorem B2699993 : Blo 2247435 2699993 := bbase (se 2 (by rfl) ⟨1012497, by rfl⟩ : syracuseStep 2699993 = 2024995) (by norm_num)
theorem B7199981 : Blo 2247435 7199981 := bstep (se 3 (by rfl) ⟨1349996, by rfl⟩ : syracuseStep 7199981 = 2699993) B2699993
theorem B4799987 : Blo 2247435 4799987 := bstep (se 1 (by rfl) ⟨3599990, by rfl⟩ : syracuseStep 4799987 = 7199981) B7199981
theorem B3199991 : Blo 2247435 3199991 := bstep (se 1 (by rfl) ⟨2399993, by rfl⟩ : syracuseStep 3199991 = 4799987) B4799987
theorem B8533309 : Blo 2247435 8533309 := bstep (se 3 (by rfl) ⟨1599995, by rfl⟩ : syracuseStep 8533309 = 3199991) B3199991
theorem B11377745 : Blo 2247435 11377745 := bstep (se 2 (by rfl) ⟨4266654, by rfl⟩ : syracuseStep 11377745 = 8533309) B8533309
theorem B7585163 : Blo 2247435 7585163 := bstep (se 1 (by rfl) ⟨5688872, by rfl⟩ : syracuseStep 7585163 = 11377745) B11377745
theorem B5056775 : Blo 2247435 5056775 := bstep (se 1 (by rfl) ⟨3792581, by rfl⟩ : syracuseStep 5056775 = 7585163) B7585163
theorem B3371183 : Blo 2247435 3371183 := bstep (se 1 (by rfl) ⟨2528387, by rfl⟩ : syracuseStep 3371183 = 5056775) B5056775
theorem B2247455 : Blo 2247435 2247455 := bstep (se 1 (by rfl) ⟨1685591, by rfl⟩ : syracuseStep 2247455 = 3371183) B3371183
theorem B3371189 : Blo 2247435 3371189 := bbase (se 5 (by rfl) ⟨158024, by rfl⟩ : syracuseStep 3371189 = 316049) (by norm_num)
theorem B2247459 : Blo 2247435 2247459 := bstep (se 1 (by rfl) ⟨1685594, by rfl⟩ : syracuseStep 2247459 = 3371189) B3371189
theorem B5688893 : Blo 2247435 5688893 := bbase (se 3 (by rfl) ⟨1066667, by rfl⟩ : syracuseStep 5688893 = 2133335) (by norm_num)
theorem B3792595 : Blo 2247435 3792595 := bstep (se 1 (by rfl) ⟨2844446, by rfl⟩ : syracuseStep 3792595 = 5688893) B5688893
theorem B5056793 : Blo 2247435 5056793 := bstep (se 2 (by rfl) ⟨1896297, by rfl⟩ : syracuseStep 5056793 = 3792595) B3792595
theorem B3371195 : Blo 2247435 3371195 := bstep (se 1 (by rfl) ⟨2528396, by rfl⟩ : syracuseStep 3371195 = 5056793) B5056793
theorem B2247463 : Blo 2247435 2247463 := bstep (se 1 (by rfl) ⟨1685597, by rfl⟩ : syracuseStep 2247463 = 3371195) B3371195
theorem B2528401 : Blo 2247435 2528401 := bbase (se 2 (by rfl) ⟨948150, by rfl⟩ : syracuseStep 2528401 = 1896301) (by norm_num)
theorem B3371201 : Blo 2247435 3371201 := bstep (se 2 (by rfl) ⟨1264200, by rfl⟩ : syracuseStep 3371201 = 2528401) B2528401
theorem B2247467 : Blo 2247435 2247467 := bstep (se 1 (by rfl) ⟨1685600, by rfl⟩ : syracuseStep 2247467 = 3371201) B3371201
theorem B4266685 : Blo 2247435 4266685 := bbase (se 3 (by rfl) ⟨800003, by rfl⟩ : syracuseStep 4266685 = 1600007) (by norm_num)
theorem B5688913 : Blo 2247435 5688913 := bstep (se 2 (by rfl) ⟨2133342, by rfl⟩ : syracuseStep 5688913 = 4266685) B4266685
theorem B7585217 : Blo 2247435 7585217 := bstep (se 2 (by rfl) ⟨2844456, by rfl⟩ : syracuseStep 7585217 = 5688913) B5688913
theorem B5056811 : Blo 2247435 5056811 := bstep (se 1 (by rfl) ⟨3792608, by rfl⟩ : syracuseStep 5056811 = 7585217) B7585217
theorem B3371207 : Blo 2247435 3371207 := bstep (se 1 (by rfl) ⟨2528405, by rfl⟩ : syracuseStep 3371207 = 5056811) B5056811
theorem B2247471 : Blo 2247435 2247471 := bstep (se 1 (by rfl) ⟨1685603, by rfl⟩ : syracuseStep 2247471 = 3371207) B3371207
theorem B3371213 : Blo 2247435 3371213 := bbase (se 3 (by rfl) ⟨632102, by rfl⟩ : syracuseStep 3371213 = 1264205) (by norm_num)
theorem B2247475 : Blo 2247435 2247475 := bstep (se 1 (by rfl) ⟨1685606, by rfl⟩ : syracuseStep 2247475 = 3371213) B3371213
theorem B5056829 : Blo 2247435 5056829 := bbase (se 3 (by rfl) ⟨948155, by rfl⟩ : syracuseStep 5056829 = 1896311) (by norm_num)
theorem B3371219 : Blo 2247435 3371219 := bstep (se 1 (by rfl) ⟨2528414, by rfl⟩ : syracuseStep 3371219 = 5056829) B5056829
theorem B2247479 : Blo 2247435 2247479 := bstep (se 1 (by rfl) ⟨1685609, by rfl⟩ : syracuseStep 2247479 = 3371219) B3371219
theorem B3792629 : Blo 2247435 3792629 := bbase (se 5 (by rfl) ⟨177779, by rfl⟩ : syracuseStep 3792629 = 355559) (by norm_num)
theorem B2528419 : Blo 2247435 2528419 := bstep (se 1 (by rfl) ⟨1896314, by rfl⟩ : syracuseStep 2528419 = 3792629) B3792629
theorem B3371225 : Blo 2247435 3371225 := bstep (se 2 (by rfl) ⟨1264209, by rfl⟩ : syracuseStep 3371225 = 2528419) B2528419
theorem B2247483 : Blo 2247435 2247483 := bstep (se 1 (by rfl) ⟨1685612, by rfl⟩ : syracuseStep 2247483 = 3371225) B3371225
theorem B43789909 : Blo 2247435 43789909 := bbase (se 8 (by rfl) ⟨256581, by rfl⟩ : syracuseStep 43789909 = 513163) (by norm_num)
theorem B58386545 : Blo 2247435 58386545 := bstep (se 2 (by rfl) ⟨21894954, by rfl⟩ : syracuseStep 58386545 = 43789909) B43789909
theorem B38924363 : Blo 2247435 38924363 := bstep (se 1 (by rfl) ⟨29193272, by rfl⟩ : syracuseStep 38924363 = 58386545) B58386545
theorem B25949575 : Blo 2247435 25949575 := bstep (se 1 (by rfl) ⟨19462181, by rfl⟩ : syracuseStep 25949575 = 38924363) B38924363
theorem B34599433 : Blo 2247435 34599433 := bstep (se 2 (by rfl) ⟨12974787, by rfl⟩ : syracuseStep 34599433 = 25949575) B25949575
theorem B46132577 : Blo 2247435 46132577 := bstep (se 2 (by rfl) ⟨17299716, by rfl⟩ : syracuseStep 46132577 = 34599433) B34599433
theorem B30755051 : Blo 2247435 30755051 := bstep (se 1 (by rfl) ⟨23066288, by rfl⟩ : syracuseStep 30755051 = 46132577) B46132577
theorem B20503367 : Blo 2247435 20503367 := bstep (se 1 (by rfl) ⟨15377525, by rfl⟩ : syracuseStep 20503367 = 30755051) B30755051
theorem B13668911 : Blo 2247435 13668911 := bstep (se 1 (by rfl) ⟨10251683, by rfl⟩ : syracuseStep 13668911 = 20503367) B20503367
theorem B9112607 : Blo 2247435 9112607 := bstep (se 1 (by rfl) ⟨6834455, by rfl⟩ : syracuseStep 9112607 = 13668911) B13668911
theorem B6075071 : Blo 2247435 6075071 := bstep (se 1 (by rfl) ⟨4556303, by rfl⟩ : syracuseStep 6075071 = 9112607) B9112607
theorem B4050047 : Blo 2247435 4050047 := bstep (se 1 (by rfl) ⟨3037535, by rfl⟩ : syracuseStep 4050047 = 6075071) B6075071
theorem B10800125 : Blo 2247435 10800125 := bstep (se 3 (by rfl) ⟨2025023, by rfl⟩ : syracuseStep 10800125 = 4050047) B4050047
theorem B7200083 : Blo 2247435 7200083 := bstep (se 1 (by rfl) ⟨5400062, by rfl⟩ : syracuseStep 7200083 = 10800125) B10800125
theorem B4800055 : Blo 2247435 4800055 := bstep (se 1 (by rfl) ⟨3600041, by rfl⟩ : syracuseStep 4800055 = 7200083) B7200083
theorem B6400073 : Blo 2247435 6400073 := bstep (se 2 (by rfl) ⟨2400027, by rfl⟩ : syracuseStep 6400073 = 4800055) B4800055
theorem B17066861 : Blo 2247435 17066861 := bstep (se 3 (by rfl) ⟨3200036, by rfl⟩ : syracuseStep 17066861 = 6400073) B6400073
theorem B11377907 : Blo 2247435 11377907 := bstep (se 1 (by rfl) ⟨8533430, by rfl⟩ : syracuseStep 11377907 = 17066861) B17066861
theorem B7585271 : Blo 2247435 7585271 := bstep (se 1 (by rfl) ⟨5688953, by rfl⟩ : syracuseStep 7585271 = 11377907) B11377907
theorem B5056847 : Blo 2247435 5056847 := bstep (se 1 (by rfl) ⟨3792635, by rfl⟩ : syracuseStep 5056847 = 7585271) B7585271
theorem B3371231 : Blo 2247435 3371231 := bstep (se 1 (by rfl) ⟨2528423, by rfl⟩ : syracuseStep 3371231 = 5056847) B5056847
theorem B2247487 : Blo 2247435 2247487 := bstep (se 1 (by rfl) ⟨1685615, by rfl⟩ : syracuseStep 2247487 = 3371231) B3371231
theorem B3371237 : Blo 2247435 3371237 := bbase (se 4 (by rfl) ⟨316053, by rfl⟩ : syracuseStep 3371237 = 632107) (by norm_num)
theorem B2247491 : Blo 2247435 2247491 := bstep (se 1 (by rfl) ⟨1685618, by rfl⟩ : syracuseStep 2247491 = 3371237) B3371237
theorem B3844397 : Blo 2247435 3844397 := bbase (se 3 (by rfl) ⟨720824, by rfl⟩ : syracuseStep 3844397 = 1441649) (by norm_num)
theorem B2562931 : Blo 2247435 2562931 := bstep (se 1 (by rfl) ⟨1922198, by rfl⟩ : syracuseStep 2562931 = 3844397) B3844397
theorem B3417241 : Blo 2247435 3417241 := bstep (se 2 (by rfl) ⟨1281465, by rfl⟩ : syracuseStep 3417241 = 2562931) B2562931
theorem B4556321 : Blo 2247435 4556321 := bstep (se 2 (by rfl) ⟨1708620, by rfl⟩ : syracuseStep 4556321 = 3417241) B3417241
theorem B3037547 : Blo 2247435 3037547 := bstep (se 1 (by rfl) ⟨2278160, by rfl⟩ : syracuseStep 3037547 = 4556321) B4556321
theorem B8100125 : Blo 2247435 8100125 := bstep (se 3 (by rfl) ⟨1518773, by rfl⟩ : syracuseStep 8100125 = 3037547) B3037547
theorem B5400083 : Blo 2247435 5400083 := bstep (se 1 (by rfl) ⟨4050062, by rfl⟩ : syracuseStep 5400083 = 8100125) B8100125
theorem B3600055 : Blo 2247435 3600055 := bstep (se 1 (by rfl) ⟨2700041, by rfl⟩ : syracuseStep 3600055 = 5400083) B5400083
theorem B4800073 : Blo 2247435 4800073 := bstep (se 2 (by rfl) ⟨1800027, by rfl⟩ : syracuseStep 4800073 = 3600055) B3600055
theorem B6400097 : Blo 2247435 6400097 := bstep (se 2 (by rfl) ⟨2400036, by rfl⟩ : syracuseStep 6400097 = 4800073) B4800073
theorem B4266731 : Blo 2247435 4266731 := bstep (se 1 (by rfl) ⟨3200048, by rfl⟩ : syracuseStep 4266731 = 6400097) B6400097
theorem B2844487 : Blo 2247435 2844487 := bstep (se 1 (by rfl) ⟨2133365, by rfl⟩ : syracuseStep 2844487 = 4266731) B4266731
theorem B3792649 : Blo 2247435 3792649 := bstep (se 2 (by rfl) ⟨1422243, by rfl⟩ : syracuseStep 3792649 = 2844487) B2844487
theorem B5056865 : Blo 2247435 5056865 := bstep (se 2 (by rfl) ⟨1896324, by rfl⟩ : syracuseStep 5056865 = 3792649) B3792649
theorem B3371243 : Blo 2247435 3371243 := bstep (se 1 (by rfl) ⟨2528432, by rfl⟩ : syracuseStep 3371243 = 5056865) B5056865
theorem B2247495 : Blo 2247435 2247495 := bstep (se 1 (by rfl) ⟨1685621, by rfl⟩ : syracuseStep 2247495 = 3371243) B3371243
theorem B2528437 : Blo 2247435 2528437 := bbase (se 5 (by rfl) ⟨118520, by rfl⟩ : syracuseStep 2528437 = 237041) (by norm_num)
theorem B3371249 : Blo 2247435 3371249 := bstep (se 2 (by rfl) ⟨1264218, by rfl⟩ : syracuseStep 3371249 = 2528437) B2528437
theorem B2247499 : Blo 2247435 2247499 := bstep (se 1 (by rfl) ⟨1685624, by rfl⟩ : syracuseStep 2247499 = 3371249) B3371249
theorem B2844497 : Blo 2247435 2844497 := bbase (se 2 (by rfl) ⟨1066686, by rfl⟩ : syracuseStep 2844497 = 2133373) (by norm_num)
theorem B7585325 : Blo 2247435 7585325 := bstep (se 3 (by rfl) ⟨1422248, by rfl⟩ : syracuseStep 7585325 = 2844497) B2844497
theorem B5056883 : Blo 2247435 5056883 := bstep (se 1 (by rfl) ⟨3792662, by rfl⟩ : syracuseStep 5056883 = 7585325) B7585325
theorem B3371255 : Blo 2247435 3371255 := bstep (se 1 (by rfl) ⟨2528441, by rfl⟩ : syracuseStep 3371255 = 5056883) B5056883
theorem B2247503 : Blo 2247435 2247503 := bstep (se 1 (by rfl) ⟨1685627, by rfl⟩ : syracuseStep 2247503 = 3371255) B3371255
theorem B3371261 : Blo 2247435 3371261 := bbase (se 3 (by rfl) ⟨632111, by rfl⟩ : syracuseStep 3371261 = 1264223) (by norm_num)
theorem B2247507 : Blo 2247435 2247507 := bstep (se 1 (by rfl) ⟨1685630, by rfl⟩ : syracuseStep 2247507 = 3371261) B3371261
theorem B5056901 : Blo 2247435 5056901 := bbase (se 4 (by rfl) ⟨474084, by rfl⟩ : syracuseStep 5056901 = 948169) (by norm_num)
theorem B3371267 : Blo 2247435 3371267 := bstep (se 1 (by rfl) ⟨2528450, by rfl⟩ : syracuseStep 3371267 = 5056901) B5056901
theorem B2247511 : Blo 2247435 2247511 := bstep (se 1 (by rfl) ⟨1685633, by rfl⟩ : syracuseStep 2247511 = 3371267) B3371267
theorem B3200077 : Blo 2247435 3200077 := bbase (se 3 (by rfl) ⟨600014, by rfl⟩ : syracuseStep 3200077 = 1200029) (by norm_num)
theorem B4266769 : Blo 2247435 4266769 := bstep (se 2 (by rfl) ⟨1600038, by rfl⟩ : syracuseStep 4266769 = 3200077) B3200077
theorem B5689025 : Blo 2247435 5689025 := bstep (se 2 (by rfl) ⟨2133384, by rfl⟩ : syracuseStep 5689025 = 4266769) B4266769
theorem B3792683 : Blo 2247435 3792683 := bstep (se 1 (by rfl) ⟨2844512, by rfl⟩ : syracuseStep 3792683 = 5689025) B5689025
theorem B2528455 : Blo 2247435 2528455 := bstep (se 1 (by rfl) ⟨1896341, by rfl⟩ : syracuseStep 2528455 = 3792683) B3792683
theorem B3371273 : Blo 2247435 3371273 := bstep (se 2 (by rfl) ⟨1264227, by rfl⟩ : syracuseStep 3371273 = 2528455) B2528455
theorem B2247515 : Blo 2247435 2247515 := bstep (se 1 (by rfl) ⟨1685636, by rfl⟩ : syracuseStep 2247515 = 3371273) B3371273
theorem B11378069 : Blo 2247435 11378069 := bbase (se 6 (by rfl) ⟨266673, by rfl⟩ : syracuseStep 11378069 = 533347) (by norm_num)
theorem B7585379 : Blo 2247435 7585379 := bstep (se 1 (by rfl) ⟨5689034, by rfl⟩ : syracuseStep 7585379 = 11378069) B11378069
theorem B5056919 : Blo 2247435 5056919 := bstep (se 1 (by rfl) ⟨3792689, by rfl⟩ : syracuseStep 5056919 = 7585379) B7585379
theorem B3371279 : Blo 2247435 3371279 := bstep (se 1 (by rfl) ⟨2528459, by rfl⟩ : syracuseStep 3371279 = 5056919) B5056919
theorem B2247519 : Blo 2247435 2247519 := bstep (se 1 (by rfl) ⟨1685639, by rfl⟩ : syracuseStep 2247519 = 3371279) B3371279
theorem B3371285 : Blo 2247435 3371285 := bbase (se 6 (by rfl) ⟨79014, by rfl⟩ : syracuseStep 3371285 = 158029) (by norm_num)
theorem B2247523 : Blo 2247435 2247523 := bstep (se 1 (by rfl) ⟨1685642, by rfl⟩ : syracuseStep 2247523 = 3371285) B3371285
theorem B5125933 : Blo 2247435 5125933 := bbase (se 3 (by rfl) ⟨961112, by rfl⟩ : syracuseStep 5125933 = 1922225) (by norm_num)
theorem B6834577 : Blo 2247435 6834577 := bstep (se 2 (by rfl) ⟨2562966, by rfl⟩ : syracuseStep 6834577 = 5125933) B5125933
theorem B9112769 : Blo 2247435 9112769 := bstep (se 2 (by rfl) ⟨3417288, by rfl⟩ : syracuseStep 9112769 = 6834577) B6834577
theorem B6075179 : Blo 2247435 6075179 := bstep (se 1 (by rfl) ⟨4556384, by rfl⟩ : syracuseStep 6075179 = 9112769) B9112769
theorem B4050119 : Blo 2247435 4050119 := bstep (se 1 (by rfl) ⟨3037589, by rfl⟩ : syracuseStep 4050119 = 6075179) B6075179
theorem B10800317 : Blo 2247435 10800317 := bstep (se 3 (by rfl) ⟨2025059, by rfl⟩ : syracuseStep 10800317 = 4050119) B4050119
theorem B28800845 : Blo 2247435 28800845 := bstep (se 3 (by rfl) ⟨5400158, by rfl⟩ : syracuseStep 28800845 = 10800317) B10800317
theorem B19200563 : Blo 2247435 19200563 := bstep (se 1 (by rfl) ⟨14400422, by rfl⟩ : syracuseStep 19200563 = 28800845) B28800845
theorem B12800375 : Blo 2247435 12800375 := bstep (se 1 (by rfl) ⟨9600281, by rfl⟩ : syracuseStep 12800375 = 19200563) B19200563
theorem B8533583 : Blo 2247435 8533583 := bstep (se 1 (by rfl) ⟨6400187, by rfl⟩ : syracuseStep 8533583 = 12800375) B12800375
theorem B5689055 : Blo 2247435 5689055 := bstep (se 1 (by rfl) ⟨4266791, by rfl⟩ : syracuseStep 5689055 = 8533583) B8533583
theorem B3792703 : Blo 2247435 3792703 := bstep (se 1 (by rfl) ⟨2844527, by rfl⟩ : syracuseStep 3792703 = 5689055) B5689055
theorem B5056937 : Blo 2247435 5056937 := bstep (se 2 (by rfl) ⟨1896351, by rfl⟩ : syracuseStep 5056937 = 3792703) B3792703
theorem B3371291 : Blo 2247435 3371291 := bstep (se 1 (by rfl) ⟨2528468, by rfl⟩ : syracuseStep 3371291 = 5056937) B5056937
theorem B2247527 : Blo 2247435 2247527 := bstep (se 1 (by rfl) ⟨1685645, by rfl⟩ : syracuseStep 2247527 = 3371291) B3371291
theorem B2528473 : Blo 2247435 2528473 := bbase (se 2 (by rfl) ⟨948177, by rfl⟩ : syracuseStep 2528473 = 1896355) (by norm_num)
theorem B3371297 : Blo 2247435 3371297 := bstep (se 2 (by rfl) ⟨1264236, by rfl⟩ : syracuseStep 3371297 = 2528473) B2528473
theorem B2247531 : Blo 2247435 2247531 := bstep (se 1 (by rfl) ⟨1685648, by rfl⟩ : syracuseStep 2247531 = 3371297) B3371297
theorem B2278201 : Blo 2247435 2278201 := bbase (se 2 (by rfl) ⟨854325, by rfl⟩ : syracuseStep 2278201 = 1708651) (by norm_num)
theorem B3037601 : Blo 2247435 3037601 := bstep (se 2 (by rfl) ⟨1139100, by rfl⟩ : syracuseStep 3037601 = 2278201) B2278201
theorem B8100269 : Blo 2247435 8100269 := bstep (se 3 (by rfl) ⟨1518800, by rfl⟩ : syracuseStep 8100269 = 3037601) B3037601
theorem B5400179 : Blo 2247435 5400179 := bstep (se 1 (by rfl) ⟨4050134, by rfl⟩ : syracuseStep 5400179 = 8100269) B8100269
theorem B3600119 : Blo 2247435 3600119 := bstep (se 1 (by rfl) ⟨2700089, by rfl⟩ : syracuseStep 3600119 = 5400179) B5400179
theorem B2400079 : Blo 2247435 2400079 := bstep (se 1 (by rfl) ⟨1800059, by rfl⟩ : syracuseStep 2400079 = 3600119) B3600119
theorem B3200105 : Blo 2247435 3200105 := bstep (se 2 (by rfl) ⟨1200039, by rfl⟩ : syracuseStep 3200105 = 2400079) B2400079
theorem B8533613 : Blo 2247435 8533613 := bstep (se 3 (by rfl) ⟨1600052, by rfl⟩ : syracuseStep 8533613 = 3200105) B3200105
theorem B5689075 : Blo 2247435 5689075 := bstep (se 1 (by rfl) ⟨4266806, by rfl⟩ : syracuseStep 5689075 = 8533613) B8533613
theorem B7585433 : Blo 2247435 7585433 := bstep (se 2 (by rfl) ⟨2844537, by rfl⟩ : syracuseStep 7585433 = 5689075) B5689075
theorem B5056955 : Blo 2247435 5056955 := bstep (se 1 (by rfl) ⟨3792716, by rfl⟩ : syracuseStep 5056955 = 7585433) B7585433
theorem B3371303 : Blo 2247435 3371303 := bstep (se 1 (by rfl) ⟨2528477, by rfl⟩ : syracuseStep 3371303 = 5056955) B5056955
theorem B2247535 : Blo 2247435 2247535 := bstep (se 1 (by rfl) ⟨1685651, by rfl⟩ : syracuseStep 2247535 = 3371303) B3371303
theorem B3371309 : Blo 2247435 3371309 := bbase (se 3 (by rfl) ⟨632120, by rfl⟩ : syracuseStep 3371309 = 1264241) (by norm_num)
theorem B2247539 : Blo 2247435 2247539 := bstep (se 1 (by rfl) ⟨1685654, by rfl⟩ : syracuseStep 2247539 = 3371309) B3371309
theorem B5056973 : Blo 2247435 5056973 := bbase (se 3 (by rfl) ⟨948182, by rfl⟩ : syracuseStep 5056973 = 1896365) (by norm_num)
theorem B3371315 : Blo 2247435 3371315 := bstep (se 1 (by rfl) ⟨2528486, by rfl⟩ : syracuseStep 3371315 = 5056973) B5056973
theorem B2247543 : Blo 2247435 2247543 := bstep (se 1 (by rfl) ⟨1685657, by rfl⟩ : syracuseStep 2247543 = 3371315) B3371315
theorem B2844553 : Blo 2247435 2844553 := bbase (se 2 (by rfl) ⟨1066707, by rfl⟩ : syracuseStep 2844553 = 2133415) (by norm_num)
theorem B3792737 : Blo 2247435 3792737 := bstep (se 2 (by rfl) ⟨1422276, by rfl⟩ : syracuseStep 3792737 = 2844553) B2844553
theorem B2528491 : Blo 2247435 2528491 := bstep (se 1 (by rfl) ⟨1896368, by rfl⟩ : syracuseStep 2528491 = 3792737) B3792737
theorem B3371321 : Blo 2247435 3371321 := bstep (se 2 (by rfl) ⟨1264245, by rfl⟩ : syracuseStep 3371321 = 2528491) B2528491
theorem B2247547 : Blo 2247435 2247547 := bstep (se 1 (by rfl) ⟨1685660, by rfl⟩ : syracuseStep 2247547 = 3371321) B3371321
theorem B38925461 : Blo 2247435 38925461 := bbase (se 6 (by rfl) ⟨912315, by rfl⟩ : syracuseStep 38925461 = 1824631) (by norm_num)
theorem B25950307 : Blo 2247435 25950307 := bstep (se 1 (by rfl) ⟨19462730, by rfl⟩ : syracuseStep 25950307 = 38925461) B38925461
theorem B34600409 : Blo 2247435 34600409 := bstep (se 2 (by rfl) ⟨12975153, by rfl⟩ : syracuseStep 34600409 = 25950307) B25950307
theorem B23066939 : Blo 2247435 23066939 := bstep (se 1 (by rfl) ⟨17300204, by rfl⟩ : syracuseStep 23066939 = 34600409) B34600409
theorem B15377959 : Blo 2247435 15377959 := bstep (se 1 (by rfl) ⟨11533469, by rfl⟩ : syracuseStep 15377959 = 23066939) B23066939
theorem B20503945 : Blo 2247435 20503945 := bstep (se 2 (by rfl) ⟨7688979, by rfl⟩ : syracuseStep 20503945 = 15377959) B15377959
theorem B109354373 : Blo 2247435 109354373 := bstep (se 4 (by rfl) ⟨10251972, by rfl⟩ : syracuseStep 109354373 = 20503945) B20503945
theorem B72902915 : Blo 2247435 72902915 := bstep (se 1 (by rfl) ⟨54677186, by rfl⟩ : syracuseStep 72902915 = 109354373) B109354373
theorem B48601943 : Blo 2247435 48601943 := bstep (se 1 (by rfl) ⟨36451457, by rfl⟩ : syracuseStep 48601943 = 72902915) B72902915
theorem B32401295 : Blo 2247435 32401295 := bstep (se 1 (by rfl) ⟨24300971, by rfl⟩ : syracuseStep 32401295 = 48601943) B48601943
theorem B21600863 : Blo 2247435 21600863 := bstep (se 1 (by rfl) ⟨16200647, by rfl⟩ : syracuseStep 21600863 = 32401295) B32401295
theorem B14400575 : Blo 2247435 14400575 := bstep (se 1 (by rfl) ⟨10800431, by rfl⟩ : syracuseStep 14400575 = 21600863) B21600863
theorem B9600383 : Blo 2247435 9600383 := bstep (se 1 (by rfl) ⟨7200287, by rfl⟩ : syracuseStep 9600383 = 14400575) B14400575
theorem B25601021 : Blo 2247435 25601021 := bstep (se 3 (by rfl) ⟨4800191, by rfl⟩ : syracuseStep 25601021 = 9600383) B9600383
theorem B17067347 : Blo 2247435 17067347 := bstep (se 1 (by rfl) ⟨12800510, by rfl⟩ : syracuseStep 17067347 = 25601021) B25601021
theorem B11378231 : Blo 2247435 11378231 := bstep (se 1 (by rfl) ⟨8533673, by rfl⟩ : syracuseStep 11378231 = 17067347) B17067347
theorem B7585487 : Blo 2247435 7585487 := bstep (se 1 (by rfl) ⟨5689115, by rfl⟩ : syracuseStep 7585487 = 11378231) B11378231
theorem B5056991 : Blo 2247435 5056991 := bstep (se 1 (by rfl) ⟨3792743, by rfl⟩ : syracuseStep 5056991 = 7585487) B7585487
theorem B3371327 : Blo 2247435 3371327 := bstep (se 1 (by rfl) ⟨2528495, by rfl⟩ : syracuseStep 3371327 = 5056991) B5056991
theorem B2247551 : Blo 2247435 2247551 := bstep (se 1 (by rfl) ⟨1685663, by rfl⟩ : syracuseStep 2247551 = 3371327) B3371327
theorem B3371333 : Blo 2247435 3371333 := bbase (se 4 (by rfl) ⟨316062, by rfl⟩ : syracuseStep 3371333 = 632125) (by norm_num)
theorem B2247555 : Blo 2247435 2247555 := bstep (se 1 (by rfl) ⟨1685666, by rfl⟩ : syracuseStep 2247555 = 3371333) B3371333
theorem B3792757 : Blo 2247435 3792757 := bbase (se 5 (by rfl) ⟨177785, by rfl⟩ : syracuseStep 3792757 = 355571) (by norm_num)
theorem B5057009 : Blo 2247435 5057009 := bstep (se 2 (by rfl) ⟨1896378, by rfl⟩ : syracuseStep 5057009 = 3792757) B3792757
theorem B3371339 : Blo 2247435 3371339 := bstep (se 1 (by rfl) ⟨2528504, by rfl⟩ : syracuseStep 3371339 = 5057009) B5057009
theorem B2247559 : Blo 2247435 2247559 := bstep (se 1 (by rfl) ⟨1685669, by rfl⟩ : syracuseStep 2247559 = 3371339) B3371339
theorem B2528509 : Blo 2247435 2528509 := bbase (se 3 (by rfl) ⟨474095, by rfl⟩ : syracuseStep 2528509 = 948191) (by norm_num)
theorem B3371345 : Blo 2247435 3371345 := bstep (se 2 (by rfl) ⟨1264254, by rfl⟩ : syracuseStep 3371345 = 2528509) B2528509
theorem B2247563 : Blo 2247435 2247563 := bstep (se 1 (by rfl) ⟨1685672, by rfl⟩ : syracuseStep 2247563 = 3371345) B3371345
theorem B7585541 : Blo 2247435 7585541 := bbase (se 4 (by rfl) ⟨711144, by rfl⟩ : syracuseStep 7585541 = 1422289) (by norm_num)
theorem B5057027 : Blo 2247435 5057027 := bstep (se 1 (by rfl) ⟨3792770, by rfl⟩ : syracuseStep 5057027 = 7585541) B7585541
theorem B3371351 : Blo 2247435 3371351 := bstep (se 1 (by rfl) ⟨2528513, by rfl⟩ : syracuseStep 3371351 = 5057027) B5057027
theorem B2247567 : Blo 2247435 2247567 := bstep (se 1 (by rfl) ⟨1685675, by rfl⟩ : syracuseStep 2247567 = 3371351) B3371351
theorem B3371357 : Blo 2247435 3371357 := bbase (se 3 (by rfl) ⟨632129, by rfl⟩ : syracuseStep 3371357 = 1264259) (by norm_num)
theorem B2247571 : Blo 2247435 2247571 := bstep (se 1 (by rfl) ⟨1685678, by rfl⟩ : syracuseStep 2247571 = 3371357) B3371357
theorem B5057045 : Blo 2247435 5057045 := bbase (se 6 (by rfl) ⟨118524, by rfl⟩ : syracuseStep 5057045 = 237049) (by norm_num)
theorem B3371363 : Blo 2247435 3371363 := bstep (se 1 (by rfl) ⟨2528522, by rfl⟩ : syracuseStep 3371363 = 5057045) B5057045
theorem B2247575 : Blo 2247435 2247575 := bstep (se 1 (by rfl) ⟨1685681, by rfl⟩ : syracuseStep 2247575 = 3371363) B3371363
theorem B8533781 : Blo 2247435 8533781 := bbase (se 6 (by rfl) ⟨200010, by rfl⟩ : syracuseStep 8533781 = 400021) (by norm_num)
theorem B5689187 : Blo 2247435 5689187 := bstep (se 1 (by rfl) ⟨4266890, by rfl⟩ : syracuseStep 5689187 = 8533781) B8533781
theorem B3792791 : Blo 2247435 3792791 := bstep (se 1 (by rfl) ⟨2844593, by rfl⟩ : syracuseStep 3792791 = 5689187) B5689187
theorem B2528527 : Blo 2247435 2528527 := bstep (se 1 (by rfl) ⟨1896395, by rfl⟩ : syracuseStep 2528527 = 3792791) B3792791
theorem B3371369 : Blo 2247435 3371369 := bstep (se 2 (by rfl) ⟨1264263, by rfl⟩ : syracuseStep 3371369 = 2528527) B2528527
theorem B2247579 : Blo 2247435 2247579 := bstep (se 1 (by rfl) ⟨1685684, by rfl⟩ : syracuseStep 2247579 = 3371369) B3371369
theorem B12800693 : Blo 2247435 12800693 := bbase (se 5 (by rfl) ⟨600032, by rfl⟩ : syracuseStep 12800693 = 1200065) (by norm_num)
theorem B8533795 : Blo 2247435 8533795 := bstep (se 1 (by rfl) ⟨6400346, by rfl⟩ : syracuseStep 8533795 = 12800693) B12800693
theorem B11378393 : Blo 2247435 11378393 := bstep (se 2 (by rfl) ⟨4266897, by rfl⟩ : syracuseStep 11378393 = 8533795) B8533795
theorem B7585595 : Blo 2247435 7585595 := bstep (se 1 (by rfl) ⟨5689196, by rfl⟩ : syracuseStep 7585595 = 11378393) B11378393
theorem B5057063 : Blo 2247435 5057063 := bstep (se 1 (by rfl) ⟨3792797, by rfl⟩ : syracuseStep 5057063 = 7585595) B7585595
theorem B3371375 : Blo 2247435 3371375 := bstep (se 1 (by rfl) ⟨2528531, by rfl⟩ : syracuseStep 3371375 = 5057063) B5057063
theorem B2247583 : Blo 2247435 2247583 := bstep (se 1 (by rfl) ⟨1685687, by rfl⟩ : syracuseStep 2247583 = 3371375) B3371375
theorem B3371381 : Blo 2247435 3371381 := bbase (se 5 (by rfl) ⟨158033, by rfl⟩ : syracuseStep 3371381 = 316067) (by norm_num)
theorem B2247587 : Blo 2247435 2247587 := bstep (se 1 (by rfl) ⟨1685690, by rfl⟩ : syracuseStep 2247587 = 3371381) B3371381
theorem B2700157 : Blo 2247435 2700157 := bbase (se 3 (by rfl) ⟨506279, by rfl⟩ : syracuseStep 2700157 = 1012559) (by norm_num)
theorem B3600209 : Blo 2247435 3600209 := bstep (se 2 (by rfl) ⟨1350078, by rfl⟩ : syracuseStep 3600209 = 2700157) B2700157
theorem B2400139 : Blo 2247435 2400139 := bstep (se 1 (by rfl) ⟨1800104, by rfl⟩ : syracuseStep 2400139 = 3600209) B3600209
theorem B3200185 : Blo 2247435 3200185 := bstep (se 2 (by rfl) ⟨1200069, by rfl⟩ : syracuseStep 3200185 = 2400139) B2400139
theorem B4266913 : Blo 2247435 4266913 := bstep (se 2 (by rfl) ⟨1600092, by rfl⟩ : syracuseStep 4266913 = 3200185) B3200185
theorem B5689217 : Blo 2247435 5689217 := bstep (se 2 (by rfl) ⟨2133456, by rfl⟩ : syracuseStep 5689217 = 4266913) B4266913
theorem B3792811 : Blo 2247435 3792811 := bstep (se 1 (by rfl) ⟨2844608, by rfl⟩ : syracuseStep 3792811 = 5689217) B5689217
theorem B5057081 : Blo 2247435 5057081 := bstep (se 2 (by rfl) ⟨1896405, by rfl⟩ : syracuseStep 5057081 = 3792811) B3792811
theorem B3371387 : Blo 2247435 3371387 := bstep (se 1 (by rfl) ⟨2528540, by rfl⟩ : syracuseStep 3371387 = 5057081) B5057081
theorem B2247591 : Blo 2247435 2247591 := bstep (se 1 (by rfl) ⟨1685693, by rfl⟩ : syracuseStep 2247591 = 3371387) B3371387
theorem B2528545 : Blo 2247435 2528545 := bbase (se 2 (by rfl) ⟨948204, by rfl⟩ : syracuseStep 2528545 = 1896409) (by norm_num)
theorem B3371393 : Blo 2247435 3371393 := bstep (se 2 (by rfl) ⟨1264272, by rfl⟩ : syracuseStep 3371393 = 2528545) B2528545
theorem B2247595 : Blo 2247435 2247595 := bstep (se 1 (by rfl) ⟨1685696, by rfl⟩ : syracuseStep 2247595 = 3371393) B3371393
theorem B5689237 : Blo 2247435 5689237 := bbase (se 6 (by rfl) ⟨133341, by rfl⟩ : syracuseStep 5689237 = 266683) (by norm_num)
theorem B7585649 : Blo 2247435 7585649 := bstep (se 2 (by rfl) ⟨2844618, by rfl⟩ : syracuseStep 7585649 = 5689237) B5689237
theorem B5057099 : Blo 2247435 5057099 := bstep (se 1 (by rfl) ⟨3792824, by rfl⟩ : syracuseStep 5057099 = 7585649) B7585649
theorem B3371399 : Blo 2247435 3371399 := bstep (se 1 (by rfl) ⟨2528549, by rfl⟩ : syracuseStep 3371399 = 5057099) B5057099
theorem B2247599 : Blo 2247435 2247599 := bstep (se 1 (by rfl) ⟨1685699, by rfl⟩ : syracuseStep 2247599 = 3371399) B3371399
theorem B3371405 : Blo 2247435 3371405 := bbase (se 3 (by rfl) ⟨632138, by rfl⟩ : syracuseStep 3371405 = 1264277) (by norm_num)
theorem B2247603 : Blo 2247435 2247603 := bstep (se 1 (by rfl) ⟨1685702, by rfl⟩ : syracuseStep 2247603 = 3371405) B3371405
theorem B5057117 : Blo 2247435 5057117 := bbase (se 3 (by rfl) ⟨948209, by rfl⟩ : syracuseStep 5057117 = 1896419) (by norm_num)
theorem B3371411 : Blo 2247435 3371411 := bstep (se 1 (by rfl) ⟨2528558, by rfl⟩ : syracuseStep 3371411 = 5057117) B5057117
theorem B2247607 : Blo 2247435 2247607 := bstep (se 1 (by rfl) ⟨1685705, by rfl⟩ : syracuseStep 2247607 = 3371411) B3371411
theorem B3792845 : Blo 2247435 3792845 := bbase (se 3 (by rfl) ⟨711158, by rfl⟩ : syracuseStep 3792845 = 1422317) (by norm_num)
theorem B2528563 : Blo 2247435 2528563 := bstep (se 1 (by rfl) ⟨1896422, by rfl⟩ : syracuseStep 2528563 = 3792845) B3792845
theorem B3371417 : Blo 2247435 3371417 := bstep (se 2 (by rfl) ⟨1264281, by rfl⟩ : syracuseStep 3371417 = 2528563) B2528563
theorem B2247611 : Blo 2247435 2247611 := bstep (se 1 (by rfl) ⟨1685708, by rfl⟩ : syracuseStep 2247611 = 3371417) B3371417
theorem B16201109 : Blo 2247435 16201109 := bbase (se 6 (by rfl) ⟨379713, by rfl⟩ : syracuseStep 16201109 = 759427) (by norm_num)
theorem B10800739 : Blo 2247435 10800739 := bstep (se 1 (by rfl) ⟨8100554, by rfl⟩ : syracuseStep 10800739 = 16201109) B16201109
theorem B14400985 : Blo 2247435 14400985 := bstep (se 2 (by rfl) ⟨5400369, by rfl⟩ : syracuseStep 14400985 = 10800739) B10800739
theorem B19201313 : Blo 2247435 19201313 := bstep (se 2 (by rfl) ⟨7200492, by rfl⟩ : syracuseStep 19201313 = 14400985) B14400985
theorem B12800875 : Blo 2247435 12800875 := bstep (se 1 (by rfl) ⟨9600656, by rfl⟩ : syracuseStep 12800875 = 19201313) B19201313
theorem B17067833 : Blo 2247435 17067833 := bstep (se 2 (by rfl) ⟨6400437, by rfl⟩ : syracuseStep 17067833 = 12800875) B12800875
theorem B11378555 : Blo 2247435 11378555 := bstep (se 1 (by rfl) ⟨8533916, by rfl⟩ : syracuseStep 11378555 = 17067833) B17067833
theorem B7585703 : Blo 2247435 7585703 := bstep (se 1 (by rfl) ⟨5689277, by rfl⟩ : syracuseStep 7585703 = 11378555) B11378555
theorem B5057135 : Blo 2247435 5057135 := bstep (se 1 (by rfl) ⟨3792851, by rfl⟩ : syracuseStep 5057135 = 7585703) B7585703
theorem B3371423 : Blo 2247435 3371423 := bstep (se 1 (by rfl) ⟨2528567, by rfl⟩ : syracuseStep 3371423 = 5057135) B5057135
theorem B2247615 : Blo 2247435 2247615 := bstep (se 1 (by rfl) ⟨1685711, by rfl⟩ : syracuseStep 2247615 = 3371423) B3371423
theorem B3371429 : Blo 2247435 3371429 := bbase (se 4 (by rfl) ⟨316071, by rfl⟩ : syracuseStep 3371429 = 632143) (by norm_num)
theorem B2247619 : Blo 2247435 2247619 := bstep (se 1 (by rfl) ⟨1685714, by rfl⟩ : syracuseStep 2247619 = 3371429) B3371429
theorem B2844649 : Blo 2247435 2844649 := bbase (se 2 (by rfl) ⟨1066743, by rfl⟩ : syracuseStep 2844649 = 2133487) (by norm_num)
theorem B3792865 : Blo 2247435 3792865 := bstep (se 2 (by rfl) ⟨1422324, by rfl⟩ : syracuseStep 3792865 = 2844649) B2844649
theorem B5057153 : Blo 2247435 5057153 := bstep (se 2 (by rfl) ⟨1896432, by rfl⟩ : syracuseStep 5057153 = 3792865) B3792865
theorem B3371435 : Blo 2247435 3371435 := bstep (se 1 (by rfl) ⟨2528576, by rfl⟩ : syracuseStep 3371435 = 5057153) B5057153
theorem B2247623 : Blo 2247435 2247623 := bstep (se 1 (by rfl) ⟨1685717, by rfl⟩ : syracuseStep 2247623 = 3371435) B3371435
theorem B2528581 : Blo 2247435 2528581 := bbase (se 4 (by rfl) ⟨237054, by rfl⟩ : syracuseStep 2528581 = 474109) (by norm_num)
theorem B3371441 : Blo 2247435 3371441 := bstep (se 2 (by rfl) ⟨1264290, by rfl⟩ : syracuseStep 3371441 = 2528581) B2528581
theorem B2247627 : Blo 2247435 2247627 := bstep (se 1 (by rfl) ⟨1685720, by rfl⟩ : syracuseStep 2247627 = 3371441) B3371441
theorem B4266989 : Blo 2247435 4266989 := bbase (se 3 (by rfl) ⟨800060, by rfl⟩ : syracuseStep 4266989 = 1600121) (by norm_num)
theorem B2844659 : Blo 2247435 2844659 := bstep (se 1 (by rfl) ⟨2133494, by rfl⟩ : syracuseStep 2844659 = 4266989) B4266989
theorem B7585757 : Blo 2247435 7585757 := bstep (se 3 (by rfl) ⟨1422329, by rfl⟩ : syracuseStep 7585757 = 2844659) B2844659
theorem B5057171 : Blo 2247435 5057171 := bstep (se 1 (by rfl) ⟨3792878, by rfl⟩ : syracuseStep 5057171 = 7585757) B7585757
theorem B3371447 : Blo 2247435 3371447 := bstep (se 1 (by rfl) ⟨2528585, by rfl⟩ : syracuseStep 3371447 = 5057171) B5057171
theorem B2247631 : Blo 2247435 2247631 := bstep (se 1 (by rfl) ⟨1685723, by rfl⟩ : syracuseStep 2247631 = 3371447) B3371447
theorem B3371453 : Blo 2247435 3371453 := bbase (se 3 (by rfl) ⟨632147, by rfl⟩ : syracuseStep 3371453 = 1264295) (by norm_num)
theorem B2247635 : Blo 2247435 2247635 := bstep (se 1 (by rfl) ⟨1685726, by rfl⟩ : syracuseStep 2247635 = 3371453) B3371453
theorem B5057189 : Blo 2247435 5057189 := bbase (se 4 (by rfl) ⟨474111, by rfl⟩ : syracuseStep 5057189 = 948223) (by norm_num)
theorem B3371459 : Blo 2247435 3371459 := bstep (se 1 (by rfl) ⟨2528594, by rfl⟩ : syracuseStep 3371459 = 5057189) B5057189
theorem B2247639 : Blo 2247435 2247639 := bstep (se 1 (by rfl) ⟨1685729, by rfl⟩ : syracuseStep 2247639 = 3371459) B3371459
theorem B5689349 : Blo 2247435 5689349 := bbase (se 4 (by rfl) ⟨533376, by rfl⟩ : syracuseStep 5689349 = 1066753) (by norm_num)
theorem B3792899 : Blo 2247435 3792899 := bstep (se 1 (by rfl) ⟨2844674, by rfl⟩ : syracuseStep 3792899 = 5689349) B5689349
theorem B2528599 : Blo 2247435 2528599 := bstep (se 1 (by rfl) ⟨1896449, by rfl⟩ : syracuseStep 2528599 = 3792899) B3792899
theorem B3371465 : Blo 2247435 3371465 := bstep (se 2 (by rfl) ⟨1264299, by rfl⟩ : syracuseStep 3371465 = 2528599) B2528599
theorem B2247643 : Blo 2247435 2247643 := bstep (se 1 (by rfl) ⟨1685732, by rfl⟩ : syracuseStep 2247643 = 3371465) B3371465
theorem B4800397 : Blo 2247435 4800397 := bbase (se 3 (by rfl) ⟨900074, by rfl⟩ : syracuseStep 4800397 = 1800149) (by norm_num)
theorem B6400529 : Blo 2247435 6400529 := bstep (se 2 (by rfl) ⟨2400198, by rfl⟩ : syracuseStep 6400529 = 4800397) B4800397
theorem B4267019 : Blo 2247435 4267019 := bstep (se 1 (by rfl) ⟨3200264, by rfl⟩ : syracuseStep 4267019 = 6400529) B6400529
theorem B11378717 : Blo 2247435 11378717 := bstep (se 3 (by rfl) ⟨2133509, by rfl⟩ : syracuseStep 11378717 = 4267019) B4267019
theorem B7585811 : Blo 2247435 7585811 := bstep (se 1 (by rfl) ⟨5689358, by rfl⟩ : syracuseStep 7585811 = 11378717) B11378717
theorem B5057207 : Blo 2247435 5057207 := bstep (se 1 (by rfl) ⟨3792905, by rfl⟩ : syracuseStep 5057207 = 7585811) B7585811
theorem B3371471 : Blo 2247435 3371471 := bstep (se 1 (by rfl) ⟨2528603, by rfl⟩ : syracuseStep 3371471 = 5057207) B5057207
theorem B2247647 : Blo 2247435 2247647 := bstep (se 1 (by rfl) ⟨1685735, by rfl⟩ : syracuseStep 2247647 = 3371471) B3371471
theorem B3371477 : Blo 2247435 3371477 := bbase (se 7 (by rfl) ⟨39509, by rfl⟩ : syracuseStep 3371477 = 79019) (by norm_num)
theorem B2247651 : Blo 2247435 2247651 := bstep (se 1 (by rfl) ⟨1685738, by rfl⟩ : syracuseStep 2247651 = 3371477) B3371477
theorem B8534069 : Blo 2247435 8534069 := bbase (se 5 (by rfl) ⟨400034, by rfl⟩ : syracuseStep 8534069 = 800069) (by norm_num)
theorem B5689379 : Blo 2247435 5689379 := bstep (se 1 (by rfl) ⟨4267034, by rfl⟩ : syracuseStep 5689379 = 8534069) B8534069
theorem B3792919 : Blo 2247435 3792919 := bstep (se 1 (by rfl) ⟨2844689, by rfl⟩ : syracuseStep 3792919 = 5689379) B5689379
theorem B5057225 : Blo 2247435 5057225 := bstep (se 2 (by rfl) ⟨1896459, by rfl⟩ : syracuseStep 5057225 = 3792919) B3792919
theorem B3371483 : Blo 2247435 3371483 := bstep (se 1 (by rfl) ⟨2528612, by rfl⟩ : syracuseStep 3371483 = 5057225) B5057225
theorem B2247655 : Blo 2247435 2247655 := bstep (se 1 (by rfl) ⟨1685741, by rfl⟩ : syracuseStep 2247655 = 3371483) B3371483
theorem B2528617 : Blo 2247435 2528617 := bbase (se 2 (by rfl) ⟨948231, by rfl⟩ : syracuseStep 2528617 = 1896463) (by norm_num)
theorem B3371489 : Blo 2247435 3371489 := bstep (se 2 (by rfl) ⟨1264308, by rfl⟩ : syracuseStep 3371489 = 2528617) B2528617
theorem B2247659 : Blo 2247435 2247659 := bstep (se 1 (by rfl) ⟨1685744, by rfl⟩ : syracuseStep 2247659 = 3371489) B3371489
theorem B12151093 : Blo 2247435 12151093 := bbase (se 5 (by rfl) ⟨569582, by rfl⟩ : syracuseStep 12151093 = 1139165) (by norm_num)
theorem B16201457 : Blo 2247435 16201457 := bstep (se 2 (by rfl) ⟨6075546, by rfl⟩ : syracuseStep 16201457 = 12151093) B12151093
theorem B10800971 : Blo 2247435 10800971 := bstep (se 1 (by rfl) ⟨8100728, by rfl⟩ : syracuseStep 10800971 = 16201457) B16201457
theorem B7200647 : Blo 2247435 7200647 := bstep (se 1 (by rfl) ⟨5400485, by rfl⟩ : syracuseStep 7200647 = 10800971) B10800971
theorem B4800431 : Blo 2247435 4800431 := bstep (se 1 (by rfl) ⟨3600323, by rfl⟩ : syracuseStep 4800431 = 7200647) B7200647
theorem B12801149 : Blo 2247435 12801149 := bstep (se 3 (by rfl) ⟨2400215, by rfl⟩ : syracuseStep 12801149 = 4800431) B4800431
theorem B8534099 : Blo 2247435 8534099 := bstep (se 1 (by rfl) ⟨6400574, by rfl⟩ : syracuseStep 8534099 = 12801149) B12801149
theorem B5689399 : Blo 2247435 5689399 := bstep (se 1 (by rfl) ⟨4267049, by rfl⟩ : syracuseStep 5689399 = 8534099) B8534099
theorem B7585865 : Blo 2247435 7585865 := bstep (se 2 (by rfl) ⟨2844699, by rfl⟩ : syracuseStep 7585865 = 5689399) B5689399
theorem B5057243 : Blo 2247435 5057243 := bstep (se 1 (by rfl) ⟨3792932, by rfl⟩ : syracuseStep 5057243 = 7585865) B7585865
theorem B3371495 : Blo 2247435 3371495 := bstep (se 1 (by rfl) ⟨2528621, by rfl⟩ : syracuseStep 3371495 = 5057243) B5057243
theorem B2247663 : Blo 2247435 2247663 := bstep (se 1 (by rfl) ⟨1685747, by rfl⟩ : syracuseStep 2247663 = 3371495) B3371495
theorem B3371501 : Blo 2247435 3371501 := bbase (se 3 (by rfl) ⟨632156, by rfl⟩ : syracuseStep 3371501 = 1264313) (by norm_num)
theorem B2247667 : Blo 2247435 2247667 := bstep (se 1 (by rfl) ⟨1685750, by rfl⟩ : syracuseStep 2247667 = 3371501) B3371501
theorem B5057261 : Blo 2247435 5057261 := bbase (se 3 (by rfl) ⟨948236, by rfl⟩ : syracuseStep 5057261 = 1896473) (by norm_num)
theorem B3371507 : Blo 2247435 3371507 := bstep (se 1 (by rfl) ⟨2528630, by rfl⟩ : syracuseStep 3371507 = 5057261) B5057261
theorem B2247671 : Blo 2247435 2247671 := bstep (se 1 (by rfl) ⟨1685753, by rfl⟩ : syracuseStep 2247671 = 3371507) B3371507
theorem B2400229 : Blo 2247435 2400229 := bbase (se 4 (by rfl) ⟨225021, by rfl⟩ : syracuseStep 2400229 = 450043) (by norm_num)
theorem B3200305 : Blo 2247435 3200305 := bstep (se 2 (by rfl) ⟨1200114, by rfl⟩ : syracuseStep 3200305 = 2400229) B2400229
theorem B4267073 : Blo 2247435 4267073 := bstep (se 2 (by rfl) ⟨1600152, by rfl⟩ : syracuseStep 4267073 = 3200305) B3200305
theorem B2844715 : Blo 2247435 2844715 := bstep (se 1 (by rfl) ⟨2133536, by rfl⟩ : syracuseStep 2844715 = 4267073) B4267073
theorem B3792953 : Blo 2247435 3792953 := bstep (se 2 (by rfl) ⟨1422357, by rfl⟩ : syracuseStep 3792953 = 2844715) B2844715
theorem B2528635 : Blo 2247435 2528635 := bstep (se 1 (by rfl) ⟨1896476, by rfl⟩ : syracuseStep 2528635 = 3792953) B3792953
theorem B3371513 : Blo 2247435 3371513 := bstep (se 2 (by rfl) ⟨1264317, by rfl⟩ : syracuseStep 3371513 = 2528635) B2528635
theorem B2247675 : Blo 2247435 2247675 := bstep (se 1 (by rfl) ⟨1685756, by rfl⟩ : syracuseStep 2247675 = 3371513) B3371513
theorem B12975893 : Blo 2247435 12975893 := bbase (se 6 (by rfl) ⟨304122, by rfl⟩ : syracuseStep 12975893 = 608245) (by norm_num)
theorem B8650595 : Blo 2247435 8650595 := bstep (se 1 (by rfl) ⟨6487946, by rfl⟩ : syracuseStep 8650595 = 12975893) B12975893
theorem B23068253 : Blo 2247435 23068253 := bstep (se 3 (by rfl) ⟨4325297, by rfl⟩ : syracuseStep 23068253 = 8650595) B8650595
theorem B15378835 : Blo 2247435 15378835 := bstep (se 1 (by rfl) ⟨11534126, by rfl⟩ : syracuseStep 15378835 = 23068253) B23068253
theorem B20505113 : Blo 2247435 20505113 := bstep (se 2 (by rfl) ⟨7689417, by rfl⟩ : syracuseStep 20505113 = 15378835) B15378835
theorem B13670075 : Blo 2247435 13670075 := bstep (se 1 (by rfl) ⟨10252556, by rfl⟩ : syracuseStep 13670075 = 20505113) B20505113
theorem B9113383 : Blo 2247435 9113383 := bstep (se 1 (by rfl) ⟨6835037, by rfl⟩ : syracuseStep 9113383 = 13670075) B13670075
theorem B12151177 : Blo 2247435 12151177 := bstep (se 2 (by rfl) ⟨4556691, by rfl⟩ : syracuseStep 12151177 = 9113383) B9113383
theorem B64806277 : Blo 2247435 64806277 := bstep (se 4 (by rfl) ⟨6075588, by rfl⟩ : syracuseStep 64806277 = 12151177) B12151177
theorem B86408369 : Blo 2247435 86408369 := bstep (se 2 (by rfl) ⟨32403138, by rfl⟩ : syracuseStep 86408369 = 64806277) B64806277
theorem B57605579 : Blo 2247435 57605579 := bstep (se 1 (by rfl) ⟨43204184, by rfl⟩ : syracuseStep 57605579 = 86408369) B86408369
theorem B38403719 : Blo 2247435 38403719 := bstep (se 1 (by rfl) ⟨28802789, by rfl⟩ : syracuseStep 38403719 = 57605579) B57605579
theorem B25602479 : Blo 2247435 25602479 := bstep (se 1 (by rfl) ⟨19201859, by rfl⟩ : syracuseStep 25602479 = 38403719) B38403719
theorem B17068319 : Blo 2247435 17068319 := bstep (se 1 (by rfl) ⟨12801239, by rfl⟩ : syracuseStep 17068319 = 25602479) B25602479
theorem B11378879 : Blo 2247435 11378879 := bstep (se 1 (by rfl) ⟨8534159, by rfl⟩ : syracuseStep 11378879 = 17068319) B17068319
theorem B7585919 : Blo 2247435 7585919 := bstep (se 1 (by rfl) ⟨5689439, by rfl⟩ : syracuseStep 7585919 = 11378879) B11378879
theorem B5057279 : Blo 2247435 5057279 := bstep (se 1 (by rfl) ⟨3792959, by rfl⟩ : syracuseStep 5057279 = 7585919) B7585919
theorem B3371519 : Blo 2247435 3371519 := bstep (se 1 (by rfl) ⟨2528639, by rfl⟩ : syracuseStep 3371519 = 5057279) B5057279
theorem B2247679 : Blo 2247435 2247679 := bstep (se 1 (by rfl) ⟨1685759, by rfl⟩ : syracuseStep 2247679 = 3371519) B3371519
theorem B3371525 : Blo 2247435 3371525 := bbase (se 4 (by rfl) ⟨316080, by rfl⟩ : syracuseStep 3371525 = 632161) (by norm_num)
theorem B2247683 : Blo 2247435 2247683 := bstep (se 1 (by rfl) ⟨1685762, by rfl⟩ : syracuseStep 2247683 = 3371525) B3371525
theorem B3792973 : Blo 2247435 3792973 := bbase (se 3 (by rfl) ⟨711182, by rfl⟩ : syracuseStep 3792973 = 1422365) (by norm_num)
theorem B5057297 : Blo 2247435 5057297 := bstep (se 2 (by rfl) ⟨1896486, by rfl⟩ : syracuseStep 5057297 = 3792973) B3792973
theorem B3371531 : Blo 2247435 3371531 := bstep (se 1 (by rfl) ⟨2528648, by rfl⟩ : syracuseStep 3371531 = 5057297) B5057297
theorem B2247687 : Blo 2247435 2247687 := bstep (se 1 (by rfl) ⟨1685765, by rfl⟩ : syracuseStep 2247687 = 3371531) B3371531
theorem B2528653 : Blo 2247435 2528653 := bbase (se 3 (by rfl) ⟨474122, by rfl⟩ : syracuseStep 2528653 = 948245) (by norm_num)
theorem B3371537 : Blo 2247435 3371537 := bstep (se 2 (by rfl) ⟨1264326, by rfl⟩ : syracuseStep 3371537 = 2528653) B2528653
theorem B2247691 : Blo 2247435 2247691 := bstep (se 1 (by rfl) ⟨1685768, by rfl⟩ : syracuseStep 2247691 = 3371537) B3371537
theorem B7585973 : Blo 2247435 7585973 := bbase (se 5 (by rfl) ⟨355592, by rfl⟩ : syracuseStep 7585973 = 711185) (by norm_num)
theorem B5057315 : Blo 2247435 5057315 := bstep (se 1 (by rfl) ⟨3792986, by rfl⟩ : syracuseStep 5057315 = 7585973) B7585973
theorem B3371543 : Blo 2247435 3371543 := bstep (se 1 (by rfl) ⟨2528657, by rfl⟩ : syracuseStep 3371543 = 5057315) B5057315
theorem B2247695 : Blo 2247435 2247695 := bstep (se 1 (by rfl) ⟨1685771, by rfl⟩ : syracuseStep 2247695 = 3371543) B3371543
theorem B3371549 : Blo 2247435 3371549 := bbase (se 3 (by rfl) ⟨632165, by rfl⟩ : syracuseStep 3371549 = 1264331) (by norm_num)
theorem B2247699 : Blo 2247435 2247699 := bstep (se 1 (by rfl) ⟨1685774, by rfl⟩ : syracuseStep 2247699 = 3371549) B3371549
theorem B5057333 : Blo 2247435 5057333 := bbase (se 5 (by rfl) ⟨237062, by rfl⟩ : syracuseStep 5057333 = 474125) (by norm_num)
theorem B3371555 : Blo 2247435 3371555 := bstep (se 1 (by rfl) ⟨2528666, by rfl⟩ : syracuseStep 3371555 = 5057333) B5057333
theorem B2247703 : Blo 2247435 2247703 := bstep (se 1 (by rfl) ⟨1685777, by rfl⟩ : syracuseStep 2247703 = 3371555) B3371555
theorem B19464085 : Blo 2247435 19464085 := bbase (se 6 (by rfl) ⟨456189, by rfl⟩ : syracuseStep 19464085 = 912379) (by norm_num)
theorem B25952113 : Blo 2247435 25952113 := bstep (se 2 (by rfl) ⟨9732042, by rfl⟩ : syracuseStep 25952113 = 19464085) B19464085
theorem B34602817 : Blo 2247435 34602817 := bstep (se 2 (by rfl) ⟨12976056, by rfl⟩ : syracuseStep 34602817 = 25952113) B25952113
theorem B46137089 : Blo 2247435 46137089 := bstep (se 2 (by rfl) ⟨17301408, by rfl⟩ : syracuseStep 46137089 = 34602817) B34602817
theorem B30758059 : Blo 2247435 30758059 := bstep (se 1 (by rfl) ⟨23068544, by rfl⟩ : syracuseStep 30758059 = 46137089) B46137089
theorem B41010745 : Blo 2247435 41010745 := bstep (se 2 (by rfl) ⟨15379029, by rfl⟩ : syracuseStep 41010745 = 30758059) B30758059
theorem B54680993 : Blo 2247435 54680993 := bstep (se 2 (by rfl) ⟨20505372, by rfl⟩ : syracuseStep 54680993 = 41010745) B41010745
theorem B36453995 : Blo 2247435 36453995 := bstep (se 1 (by rfl) ⟨27340496, by rfl⟩ : syracuseStep 36453995 = 54680993) B54680993
theorem B24302663 : Blo 2247435 24302663 := bstep (se 1 (by rfl) ⟨18226997, by rfl⟩ : syracuseStep 24302663 = 36453995) B36453995
theorem B16201775 : Blo 2247435 16201775 := bstep (se 1 (by rfl) ⟨12151331, by rfl⟩ : syracuseStep 16201775 = 24302663) B24302663
theorem B10801183 : Blo 2247435 10801183 := bstep (se 1 (by rfl) ⟨8100887, by rfl⟩ : syracuseStep 10801183 = 16201775) B16201775
theorem B14401577 : Blo 2247435 14401577 := bstep (se 2 (by rfl) ⟨5400591, by rfl⟩ : syracuseStep 14401577 = 10801183) B10801183
theorem B9601051 : Blo 2247435 9601051 := bstep (se 1 (by rfl) ⟨7200788, by rfl⟩ : syracuseStep 9601051 = 14401577) B14401577
theorem B12801401 : Blo 2247435 12801401 := bstep (se 2 (by rfl) ⟨4800525, by rfl⟩ : syracuseStep 12801401 = 9601051) B9601051
theorem B8534267 : Blo 2247435 8534267 := bstep (se 1 (by rfl) ⟨6400700, by rfl⟩ : syracuseStep 8534267 = 12801401) B12801401
theorem B5689511 : Blo 2247435 5689511 := bstep (se 1 (by rfl) ⟨4267133, by rfl⟩ : syracuseStep 5689511 = 8534267) B8534267
theorem B3793007 : Blo 2247435 3793007 := bstep (se 1 (by rfl) ⟨2844755, by rfl⟩ : syracuseStep 3793007 = 5689511) B5689511
theorem B2528671 : Blo 2247435 2528671 := bstep (se 1 (by rfl) ⟨1896503, by rfl⟩ : syracuseStep 2528671 = 3793007) B3793007
theorem B3371561 : Blo 2247435 3371561 := bstep (se 2 (by rfl) ⟨1264335, by rfl⟩ : syracuseStep 3371561 = 2528671) B2528671
theorem B2247707 : Blo 2247435 2247707 := bstep (se 1 (by rfl) ⟨1685780, by rfl⟩ : syracuseStep 2247707 = 3371561) B3371561
theorem B8100901 : Blo 2247435 8100901 := bbase (se 4 (by rfl) ⟨759459, by rfl⟩ : syracuseStep 8100901 = 1518919) (by norm_num)
theorem B10801201 : Blo 2247435 10801201 := bstep (se 2 (by rfl) ⟨4050450, by rfl⟩ : syracuseStep 10801201 = 8100901) B8100901
theorem B14401601 : Blo 2247435 14401601 := bstep (se 2 (by rfl) ⟨5400600, by rfl⟩ : syracuseStep 14401601 = 10801201) B10801201
theorem B9601067 : Blo 2247435 9601067 := bstep (se 1 (by rfl) ⟨7200800, by rfl⟩ : syracuseStep 9601067 = 14401601) B14401601
theorem B6400711 : Blo 2247435 6400711 := bstep (se 1 (by rfl) ⟨4800533, by rfl⟩ : syracuseStep 6400711 = 9601067) B9601067
theorem B8534281 : Blo 2247435 8534281 := bstep (se 2 (by rfl) ⟨3200355, by rfl⟩ : syracuseStep 8534281 = 6400711) B6400711
theorem B11379041 : Blo 2247435 11379041 := bstep (se 2 (by rfl) ⟨4267140, by rfl⟩ : syracuseStep 11379041 = 8534281) B8534281
theorem B7586027 : Blo 2247435 7586027 := bstep (se 1 (by rfl) ⟨5689520, by rfl⟩ : syracuseStep 7586027 = 11379041) B11379041
theorem B5057351 : Blo 2247435 5057351 := bstep (se 1 (by rfl) ⟨3793013, by rfl⟩ : syracuseStep 5057351 = 7586027) B7586027
theorem B3371567 : Blo 2247435 3371567 := bstep (se 1 (by rfl) ⟨2528675, by rfl⟩ : syracuseStep 3371567 = 5057351) B5057351
theorem B2247711 : Blo 2247435 2247711 := bstep (se 1 (by rfl) ⟨1685783, by rfl⟩ : syracuseStep 2247711 = 3371567) B3371567
theorem B3371573 : Blo 2247435 3371573 := bbase (se 5 (by rfl) ⟨158042, by rfl⟩ : syracuseStep 3371573 = 316085) (by norm_num)
theorem B2247715 : Blo 2247435 2247715 := bstep (se 1 (by rfl) ⟨1685786, by rfl⟩ : syracuseStep 2247715 = 3371573) B3371573
theorem B5689541 : Blo 2247435 5689541 := bbase (se 4 (by rfl) ⟨533394, by rfl⟩ : syracuseStep 5689541 = 1066789) (by norm_num)
theorem B3793027 : Blo 2247435 3793027 := bstep (se 1 (by rfl) ⟨2844770, by rfl⟩ : syracuseStep 3793027 = 5689541) B5689541
theorem B5057369 : Blo 2247435 5057369 := bstep (se 2 (by rfl) ⟨1896513, by rfl⟩ : syracuseStep 5057369 = 3793027) B3793027
theorem B3371579 : Blo 2247435 3371579 := bstep (se 1 (by rfl) ⟨2528684, by rfl⟩ : syracuseStep 3371579 = 5057369) B5057369
theorem B2247719 : Blo 2247435 2247719 := bstep (se 1 (by rfl) ⟨1685789, by rfl⟩ : syracuseStep 2247719 = 3371579) B3371579
theorem B2528689 : Blo 2247435 2528689 := bbase (se 2 (by rfl) ⟨948258, by rfl⟩ : syracuseStep 2528689 = 1896517) (by norm_num)
theorem B3371585 : Blo 2247435 3371585 := bstep (se 2 (by rfl) ⟨1264344, by rfl⟩ : syracuseStep 3371585 = 2528689) B2528689
theorem B2247723 : Blo 2247435 2247723 := bstep (se 1 (by rfl) ⟨1685792, by rfl⟩ : syracuseStep 2247723 = 3371585) B3371585
theorem B6400757 : Blo 2247435 6400757 := bbase (se 5 (by rfl) ⟨300035, by rfl⟩ : syracuseStep 6400757 = 600071) (by norm_num)
theorem B4267171 : Blo 2247435 4267171 := bstep (se 1 (by rfl) ⟨3200378, by rfl⟩ : syracuseStep 4267171 = 6400757) B6400757
theorem B5689561 : Blo 2247435 5689561 := bstep (se 2 (by rfl) ⟨2133585, by rfl⟩ : syracuseStep 5689561 = 4267171) B4267171
theorem B7586081 : Blo 2247435 7586081 := bstep (se 2 (by rfl) ⟨2844780, by rfl⟩ : syracuseStep 7586081 = 5689561) B5689561
theorem B5057387 : Blo 2247435 5057387 := bstep (se 1 (by rfl) ⟨3793040, by rfl⟩ : syracuseStep 5057387 = 7586081) B7586081
theorem B3371591 : Blo 2247435 3371591 := bstep (se 1 (by rfl) ⟨2528693, by rfl⟩ : syracuseStep 3371591 = 5057387) B5057387
theorem B2247727 : Blo 2247435 2247727 := bstep (se 1 (by rfl) ⟨1685795, by rfl⟩ : syracuseStep 2247727 = 3371591) B3371591
theorem B3371597 : Blo 2247435 3371597 := bbase (se 3 (by rfl) ⟨632174, by rfl⟩ : syracuseStep 3371597 = 1264349) (by norm_num)
theorem B2247731 : Blo 2247435 2247731 := bstep (se 1 (by rfl) ⟨1685798, by rfl⟩ : syracuseStep 2247731 = 3371597) B3371597
theorem B5057405 : Blo 2247435 5057405 := bbase (se 3 (by rfl) ⟨948263, by rfl⟩ : syracuseStep 5057405 = 1896527) (by norm_num)
theorem B3371603 : Blo 2247435 3371603 := bstep (se 1 (by rfl) ⟨2528702, by rfl⟩ : syracuseStep 3371603 = 5057405) B5057405
theorem B2247735 : Blo 2247435 2247735 := bstep (se 1 (by rfl) ⟨1685801, by rfl⟩ : syracuseStep 2247735 = 3371603) B3371603
theorem B3793061 : Blo 2247435 3793061 := bbase (se 4 (by rfl) ⟨355599, by rfl⟩ : syracuseStep 3793061 = 711199) (by norm_num)
theorem B2528707 : Blo 2247435 2528707 := bstep (se 1 (by rfl) ⟨1896530, by rfl⟩ : syracuseStep 2528707 = 3793061) B3793061
theorem B3371609 : Blo 2247435 3371609 := bstep (se 2 (by rfl) ⟨1264353, by rfl⟩ : syracuseStep 3371609 = 2528707) B2528707
theorem B2247739 : Blo 2247435 2247739 := bstep (se 1 (by rfl) ⟨1685804, by rfl⟩ : syracuseStep 2247739 = 3371609) B3371609
theorem B2400301 : Blo 2247435 2400301 := bbase (se 3 (by rfl) ⟨450056, by rfl⟩ : syracuseStep 2400301 = 900113) (by norm_num)
theorem B3200401 : Blo 2247435 3200401 := bstep (se 2 (by rfl) ⟨1200150, by rfl⟩ : syracuseStep 3200401 = 2400301) B2400301
theorem B17068805 : Blo 2247435 17068805 := bstep (se 4 (by rfl) ⟨1600200, by rfl⟩ : syracuseStep 17068805 = 3200401) B3200401
theorem B11379203 : Blo 2247435 11379203 := bstep (se 1 (by rfl) ⟨8534402, by rfl⟩ : syracuseStep 11379203 = 17068805) B17068805
theorem B7586135 : Blo 2247435 7586135 := bstep (se 1 (by rfl) ⟨5689601, by rfl⟩ : syracuseStep 7586135 = 11379203) B11379203
theorem B5057423 : Blo 2247435 5057423 := bstep (se 1 (by rfl) ⟨3793067, by rfl⟩ : syracuseStep 5057423 = 7586135) B7586135
theorem B3371615 : Blo 2247435 3371615 := bstep (se 1 (by rfl) ⟨2528711, by rfl⟩ : syracuseStep 3371615 = 5057423) B5057423
theorem B2247743 : Blo 2247435 2247743 := bstep (se 1 (by rfl) ⟨1685807, by rfl⟩ : syracuseStep 2247743 = 3371615) B3371615
theorem B3371621 : Blo 2247435 3371621 := bbase (se 4 (by rfl) ⟨316089, by rfl⟩ : syracuseStep 3371621 = 632179) (by norm_num)
theorem B2247747 : Blo 2247435 2247747 := bstep (se 1 (by rfl) ⟨1685810, by rfl⟩ : syracuseStep 2247747 = 3371621) B3371621
theorem B3200413 : Blo 2247435 3200413 := bbase (se 3 (by rfl) ⟨600077, by rfl⟩ : syracuseStep 3200413 = 1200155) (by norm_num)
theorem B4267217 : Blo 2247435 4267217 := bstep (se 2 (by rfl) ⟨1600206, by rfl⟩ : syracuseStep 4267217 = 3200413) B3200413
theorem B2844811 : Blo 2247435 2844811 := bstep (se 1 (by rfl) ⟨2133608, by rfl⟩ : syracuseStep 2844811 = 4267217) B4267217
theorem B3793081 : Blo 2247435 3793081 := bstep (se 2 (by rfl) ⟨1422405, by rfl⟩ : syracuseStep 3793081 = 2844811) B2844811
theorem B5057441 : Blo 2247435 5057441 := bstep (se 2 (by rfl) ⟨1896540, by rfl⟩ : syracuseStep 5057441 = 3793081) B3793081
theorem B3371627 : Blo 2247435 3371627 := bstep (se 1 (by rfl) ⟨2528720, by rfl⟩ : syracuseStep 3371627 = 5057441) B5057441
theorem B2247751 : Blo 2247435 2247751 := bstep (se 1 (by rfl) ⟨1685813, by rfl⟩ : syracuseStep 2247751 = 3371627) B3371627
theorem B2528725 : Blo 2247435 2528725 := bbase (se 7 (by rfl) ⟨29633, by rfl⟩ : syracuseStep 2528725 = 59267) (by norm_num)
theorem B3371633 : Blo 2247435 3371633 := bstep (se 2 (by rfl) ⟨1264362, by rfl⟩ : syracuseStep 3371633 = 2528725) B2528725
theorem B2247755 : Blo 2247435 2247755 := bstep (se 1 (by rfl) ⟨1685816, by rfl⟩ : syracuseStep 2247755 = 3371633) B3371633
theorem B2844821 : Blo 2247435 2844821 := bbase (se 6 (by rfl) ⟨66675, by rfl⟩ : syracuseStep 2844821 = 133351) (by norm_num)
theorem B7586189 : Blo 2247435 7586189 := bstep (se 3 (by rfl) ⟨1422410, by rfl⟩ : syracuseStep 7586189 = 2844821) B2844821
theorem B5057459 : Blo 2247435 5057459 := bstep (se 1 (by rfl) ⟨3793094, by rfl⟩ : syracuseStep 5057459 = 7586189) B7586189
theorem B3371639 : Blo 2247435 3371639 := bstep (se 1 (by rfl) ⟨2528729, by rfl⟩ : syracuseStep 3371639 = 5057459) B5057459
theorem B2247759 : Blo 2247435 2247759 := bstep (se 1 (by rfl) ⟨1685819, by rfl⟩ : syracuseStep 2247759 = 3371639) B3371639
theorem B3371645 : Blo 2247435 3371645 := bbase (se 3 (by rfl) ⟨632183, by rfl⟩ : syracuseStep 3371645 = 1264367) (by norm_num)
theorem B2247763 : Blo 2247435 2247763 := bstep (se 1 (by rfl) ⟨1685822, by rfl⟩ : syracuseStep 2247763 = 3371645) B3371645
theorem B5057477 : Blo 2247435 5057477 := bbase (se 4 (by rfl) ⟨474138, by rfl⟩ : syracuseStep 5057477 = 948277) (by norm_num)
theorem B3371651 : Blo 2247435 3371651 := bstep (se 1 (by rfl) ⟨2528738, by rfl⟩ : syracuseStep 3371651 = 5057477) B5057477
theorem B2247767 : Blo 2247435 2247767 := bstep (se 1 (by rfl) ⟨1685825, by rfl⟩ : syracuseStep 2247767 = 3371651) B3371651
theorem B2700373 : Blo 2247435 2700373 := bbase (se 8 (by rfl) ⟨15822, by rfl⟩ : syracuseStep 2700373 = 31645) (by norm_num)
theorem B3600497 : Blo 2247435 3600497 := bstep (se 2 (by rfl) ⟨1350186, by rfl⟩ : syracuseStep 3600497 = 2700373) B2700373
theorem B9601325 : Blo 2247435 9601325 := bstep (se 3 (by rfl) ⟨1800248, by rfl⟩ : syracuseStep 9601325 = 3600497) B3600497
theorem B6400883 : Blo 2247435 6400883 := bstep (se 1 (by rfl) ⟨4800662, by rfl⟩ : syracuseStep 6400883 = 9601325) B9601325
theorem B4267255 : Blo 2247435 4267255 := bstep (se 1 (by rfl) ⟨3200441, by rfl⟩ : syracuseStep 4267255 = 6400883) B6400883
theorem B5689673 : Blo 2247435 5689673 := bstep (se 2 (by rfl) ⟨2133627, by rfl⟩ : syracuseStep 5689673 = 4267255) B4267255
theorem B3793115 : Blo 2247435 3793115 := bstep (se 1 (by rfl) ⟨2844836, by rfl⟩ : syracuseStep 3793115 = 5689673) B5689673
theorem B2528743 : Blo 2247435 2528743 := bstep (se 1 (by rfl) ⟨1896557, by rfl⟩ : syracuseStep 2528743 = 3793115) B3793115
theorem B3371657 : Blo 2247435 3371657 := bstep (se 2 (by rfl) ⟨1264371, by rfl⟩ : syracuseStep 3371657 = 2528743) B2528743
theorem B2247771 : Blo 2247435 2247771 := bstep (se 1 (by rfl) ⟨1685828, by rfl⟩ : syracuseStep 2247771 = 3371657) B3371657
theorem B11379365 : Blo 2247435 11379365 := bbase (se 4 (by rfl) ⟨1066815, by rfl⟩ : syracuseStep 11379365 = 2133631) (by norm_num)
theorem B7586243 : Blo 2247435 7586243 := bstep (se 1 (by rfl) ⟨5689682, by rfl⟩ : syracuseStep 7586243 = 11379365) B11379365
theorem B5057495 : Blo 2247435 5057495 := bstep (se 1 (by rfl) ⟨3793121, by rfl⟩ : syracuseStep 5057495 = 7586243) B7586243
theorem B3371663 : Blo 2247435 3371663 := bstep (se 1 (by rfl) ⟨2528747, by rfl⟩ : syracuseStep 3371663 = 5057495) B5057495
theorem B2247775 : Blo 2247435 2247775 := bstep (se 1 (by rfl) ⟨1685831, by rfl⟩ : syracuseStep 2247775 = 3371663) B3371663
theorem B3371669 : Blo 2247435 3371669 := bbase (se 6 (by rfl) ⟨79023, by rfl⟩ : syracuseStep 3371669 = 158047) (by norm_num)
theorem B2247779 : Blo 2247435 2247779 := bstep (se 1 (by rfl) ⟨1685834, by rfl⟩ : syracuseStep 2247779 = 3371669) B3371669
theorem B2466289 : Blo 2247435 2466289 := bbase (se 2 (by rfl) ⟨924858, by rfl⟩ : syracuseStep 2466289 = 1849717) (by norm_num)
theorem B3288385 : Blo 2247435 3288385 := bstep (se 2 (by rfl) ⟨1233144, by rfl⟩ : syracuseStep 3288385 = 2466289) B2466289
theorem B17538053 : Blo 2247435 17538053 := bstep (se 4 (by rfl) ⟨1644192, by rfl⟩ : syracuseStep 17538053 = 3288385) B3288385
theorem B46768141 : Blo 2247435 46768141 := bstep (se 3 (by rfl) ⟨8769026, by rfl⟩ : syracuseStep 46768141 = 17538053) B17538053
theorem B62357521 : Blo 2247435 62357521 := bstep (se 2 (by rfl) ⟨23384070, by rfl⟩ : syracuseStep 62357521 = 46768141) B46768141
theorem B83143361 : Blo 2247435 83143361 := bstep (se 2 (by rfl) ⟨31178760, by rfl⟩ : syracuseStep 83143361 = 62357521) B62357521
theorem B55428907 : Blo 2247435 55428907 := bstep (se 1 (by rfl) ⟨41571680, by rfl⟩ : syracuseStep 55428907 = 83143361) B83143361
theorem B73905209 : Blo 2247435 73905209 := bstep (se 2 (by rfl) ⟨27714453, by rfl⟩ : syracuseStep 73905209 = 55428907) B55428907
theorem B49270139 : Blo 2247435 49270139 := bstep (se 1 (by rfl) ⟨36952604, by rfl⟩ : syracuseStep 49270139 = 73905209) B73905209
theorem B32846759 : Blo 2247435 32846759 := bstep (se 1 (by rfl) ⟨24635069, by rfl⟩ : syracuseStep 32846759 = 49270139) B49270139
theorem B21897839 : Blo 2247435 21897839 := bstep (se 1 (by rfl) ⟨16423379, by rfl⟩ : syracuseStep 21897839 = 32846759) B32846759
theorem B14598559 : Blo 2247435 14598559 := bstep (se 1 (by rfl) ⟨10948919, by rfl⟩ : syracuseStep 14598559 = 21897839) B21897839
theorem B19464745 : Blo 2247435 19464745 := bstep (se 2 (by rfl) ⟨7299279, by rfl⟩ : syracuseStep 19464745 = 14598559) B14598559
theorem B25952993 : Blo 2247435 25952993 := bstep (se 2 (by rfl) ⟨9732372, by rfl⟩ : syracuseStep 25952993 = 19464745) B19464745
theorem B17301995 : Blo 2247435 17301995 := bstep (se 1 (by rfl) ⟨12976496, by rfl⟩ : syracuseStep 17301995 = 25952993) B25952993
theorem B11534663 : Blo 2247435 11534663 := bstep (se 1 (by rfl) ⟨8650997, by rfl⟩ : syracuseStep 11534663 = 17301995) B17301995
theorem B7689775 : Blo 2247435 7689775 := bstep (se 1 (by rfl) ⟨5767331, by rfl⟩ : syracuseStep 7689775 = 11534663) B11534663
theorem B10253033 : Blo 2247435 10253033 := bstep (se 2 (by rfl) ⟨3844887, by rfl⟩ : syracuseStep 10253033 = 7689775) B7689775
theorem B6835355 : Blo 2247435 6835355 := bstep (se 1 (by rfl) ⟨5126516, by rfl⟩ : syracuseStep 6835355 = 10253033) B10253033
theorem B4556903 : Blo 2247435 4556903 := bstep (se 1 (by rfl) ⟨3417677, by rfl⟩ : syracuseStep 4556903 = 6835355) B6835355
theorem B48606965 : Blo 2247435 48606965 := bstep (se 5 (by rfl) ⟨2278451, by rfl⟩ : syracuseStep 48606965 = 4556903) B4556903
theorem B32404643 : Blo 2247435 32404643 := bstep (se 1 (by rfl) ⟨24303482, by rfl⟩ : syracuseStep 32404643 = 48606965) B48606965
theorem B21603095 : Blo 2247435 21603095 := bstep (se 1 (by rfl) ⟨16202321, by rfl⟩ : syracuseStep 21603095 = 32404643) B32404643
theorem B14402063 : Blo 2247435 14402063 := bstep (se 1 (by rfl) ⟨10801547, by rfl⟩ : syracuseStep 14402063 = 21603095) B21603095
theorem B9601375 : Blo 2247435 9601375 := bstep (se 1 (by rfl) ⟨7201031, by rfl⟩ : syracuseStep 9601375 = 14402063) B14402063
theorem B12801833 : Blo 2247435 12801833 := bstep (se 2 (by rfl) ⟨4800687, by rfl⟩ : syracuseStep 12801833 = 9601375) B9601375
theorem B8534555 : Blo 2247435 8534555 := bstep (se 1 (by rfl) ⟨6400916, by rfl⟩ : syracuseStep 8534555 = 12801833) B12801833
theorem B5689703 : Blo 2247435 5689703 := bstep (se 1 (by rfl) ⟨4267277, by rfl⟩ : syracuseStep 5689703 = 8534555) B8534555
theorem B3793135 : Blo 2247435 3793135 := bstep (se 1 (by rfl) ⟨2844851, by rfl⟩ : syracuseStep 3793135 = 5689703) B5689703
theorem B5057513 : Blo 2247435 5057513 := bstep (se 2 (by rfl) ⟨1896567, by rfl⟩ : syracuseStep 5057513 = 3793135) B3793135
theorem B3371675 : Blo 2247435 3371675 := bstep (se 1 (by rfl) ⟨2528756, by rfl⟩ : syracuseStep 3371675 = 5057513) B5057513
theorem B2247783 : Blo 2247435 2247783 := bstep (se 1 (by rfl) ⟨1685837, by rfl⟩ : syracuseStep 2247783 = 3371675) B3371675
theorem B2528761 : Blo 2247435 2528761 := bbase (se 2 (by rfl) ⟨948285, by rfl⟩ : syracuseStep 2528761 = 1896571) (by norm_num)
theorem B3371681 : Blo 2247435 3371681 := bstep (se 2 (by rfl) ⟨1264380, by rfl⟩ : syracuseStep 3371681 = 2528761) B2528761
theorem B2247787 : Blo 2247435 2247787 := bstep (se 1 (by rfl) ⟨1685840, by rfl⟩ : syracuseStep 2247787 = 3371681) B3371681
theorem B6075893 : Blo 2247435 6075893 := bbase (se 5 (by rfl) ⟨284807, by rfl⟩ : syracuseStep 6075893 = 569615) (by norm_num)
theorem B4050595 : Blo 2247435 4050595 := bstep (se 1 (by rfl) ⟨3037946, by rfl⟩ : syracuseStep 4050595 = 6075893) B6075893
theorem B5400793 : Blo 2247435 5400793 := bstep (se 2 (by rfl) ⟨2025297, by rfl⟩ : syracuseStep 5400793 = 4050595) B4050595
theorem B7201057 : Blo 2247435 7201057 := bstep (se 2 (by rfl) ⟨2700396, by rfl⟩ : syracuseStep 7201057 = 5400793) B5400793
theorem B9601409 : Blo 2247435 9601409 := bstep (se 2 (by rfl) ⟨3600528, by rfl⟩ : syracuseStep 9601409 = 7201057) B7201057
theorem B6400939 : Blo 2247435 6400939 := bstep (se 1 (by rfl) ⟨4800704, by rfl⟩ : syracuseStep 6400939 = 9601409) B9601409
theorem B8534585 : Blo 2247435 8534585 := bstep (se 2 (by rfl) ⟨3200469, by rfl⟩ : syracuseStep 8534585 = 6400939) B6400939
theorem B5689723 : Blo 2247435 5689723 := bstep (se 1 (by rfl) ⟨4267292, by rfl⟩ : syracuseStep 5689723 = 8534585) B8534585
theorem B7586297 : Blo 2247435 7586297 := bstep (se 2 (by rfl) ⟨2844861, by rfl⟩ : syracuseStep 7586297 = 5689723) B5689723
theorem B5057531 : Blo 2247435 5057531 := bstep (se 1 (by rfl) ⟨3793148, by rfl⟩ : syracuseStep 5057531 = 7586297) B7586297
theorem B3371687 : Blo 2247435 3371687 := bstep (se 1 (by rfl) ⟨2528765, by rfl⟩ : syracuseStep 3371687 = 5057531) B5057531
theorem B2247791 : Blo 2247435 2247791 := bstep (se 1 (by rfl) ⟨1685843, by rfl⟩ : syracuseStep 2247791 = 3371687) B3371687
theorem B3371693 : Blo 2247435 3371693 := bbase (se 3 (by rfl) ⟨632192, by rfl⟩ : syracuseStep 3371693 = 1264385) (by norm_num)
theorem B2247795 : Blo 2247435 2247795 := bstep (se 1 (by rfl) ⟨1685846, by rfl⟩ : syracuseStep 2247795 = 3371693) B3371693
theorem B5057549 : Blo 2247435 5057549 := bbase (se 3 (by rfl) ⟨948290, by rfl⟩ : syracuseStep 5057549 = 1896581) (by norm_num)
theorem B3371699 : Blo 2247435 3371699 := bstep (se 1 (by rfl) ⟨2528774, by rfl⟩ : syracuseStep 3371699 = 5057549) B5057549
theorem B2247799 : Blo 2247435 2247799 := bstep (se 1 (by rfl) ⟨1685849, by rfl⟩ : syracuseStep 2247799 = 3371699) B3371699
theorem B2844877 : Blo 2247435 2844877 := bbase (se 3 (by rfl) ⟨533414, by rfl⟩ : syracuseStep 2844877 = 1066829) (by norm_num)
theorem B3793169 : Blo 2247435 3793169 := bstep (se 2 (by rfl) ⟨1422438, by rfl⟩ : syracuseStep 3793169 = 2844877) B2844877
theorem B2528779 : Blo 2247435 2528779 := bstep (se 1 (by rfl) ⟨1896584, by rfl⟩ : syracuseStep 2528779 = 3793169) B3793169
theorem B3371705 : Blo 2247435 3371705 := bstep (se 2 (by rfl) ⟨1264389, by rfl⟩ : syracuseStep 3371705 = 2528779) B2528779
theorem B2247803 : Blo 2247435 2247803 := bstep (se 1 (by rfl) ⟨1685852, by rfl⟩ : syracuseStep 2247803 = 3371705) B3371705
theorem B4932629 : Blo 2247435 4932629 := bbase (se 6 (by rfl) ⟨115608, by rfl⟩ : syracuseStep 4932629 = 231217) (by norm_num)
theorem B3288419 : Blo 2247435 3288419 := bstep (se 1 (by rfl) ⟨2466314, by rfl⟩ : syracuseStep 3288419 = 4932629) B4932629
theorem B140305877 : Blo 2247435 140305877 := bstep (se 7 (by rfl) ⟨1644209, by rfl⟩ : syracuseStep 140305877 = 3288419) B3288419
theorem B93537251 : Blo 2247435 93537251 := bstep (se 1 (by rfl) ⟨70152938, by rfl⟩ : syracuseStep 93537251 = 140305877) B140305877
theorem B62358167 : Blo 2247435 62358167 := bstep (se 1 (by rfl) ⟨46768625, by rfl⟩ : syracuseStep 62358167 = 93537251) B93537251
theorem B41572111 : Blo 2247435 41572111 := bstep (se 1 (by rfl) ⟨31179083, by rfl⟩ : syracuseStep 41572111 = 62358167) B62358167
theorem B55429481 : Blo 2247435 55429481 := bstep (se 2 (by rfl) ⟨20786055, by rfl⟩ : syracuseStep 55429481 = 41572111) B41572111
theorem B147811949 : Blo 2247435 147811949 := bstep (se 3 (by rfl) ⟨27714740, by rfl⟩ : syracuseStep 147811949 = 55429481) B55429481
theorem B98541299 : Blo 2247435 98541299 := bstep (se 1 (by rfl) ⟨73905974, by rfl⟩ : syracuseStep 98541299 = 147811949) B147811949
theorem B65694199 : Blo 2247435 65694199 := bstep (se 1 (by rfl) ⟨49270649, by rfl⟩ : syracuseStep 65694199 = 98541299) B98541299
theorem B87592265 : Blo 2247435 87592265 := bstep (se 2 (by rfl) ⟨32847099, by rfl⟩ : syracuseStep 87592265 = 65694199) B65694199
theorem B58394843 : Blo 2247435 58394843 := bstep (se 1 (by rfl) ⟨43796132, by rfl⟩ : syracuseStep 58394843 = 87592265) B87592265
theorem B38929895 : Blo 2247435 38929895 := bstep (se 1 (by rfl) ⟨29197421, by rfl⟩ : syracuseStep 38929895 = 58394843) B58394843
theorem B25953263 : Blo 2247435 25953263 := bstep (se 1 (by rfl) ⟨19464947, by rfl⟩ : syracuseStep 25953263 = 38929895) B38929895
theorem B17302175 : Blo 2247435 17302175 := bstep (se 1 (by rfl) ⟨12976631, by rfl⟩ : syracuseStep 17302175 = 25953263) B25953263
theorem B11534783 : Blo 2247435 11534783 := bstep (se 1 (by rfl) ⟨8651087, by rfl⟩ : syracuseStep 11534783 = 17302175) B17302175
theorem B30759421 : Blo 2247435 30759421 := bstep (se 3 (by rfl) ⟨5767391, by rfl⟩ : syracuseStep 30759421 = 11534783) B11534783
theorem B41012561 : Blo 2247435 41012561 := bstep (se 2 (by rfl) ⟨15379710, by rfl⟩ : syracuseStep 41012561 = 30759421) B30759421
theorem B27341707 : Blo 2247435 27341707 := bstep (se 1 (by rfl) ⟨20506280, by rfl⟩ : syracuseStep 27341707 = 41012561) B41012561
theorem B36455609 : Blo 2247435 36455609 := bstep (se 2 (by rfl) ⟨13670853, by rfl⟩ : syracuseStep 36455609 = 27341707) B27341707
theorem B24303739 : Blo 2247435 24303739 := bstep (se 1 (by rfl) ⟨18227804, by rfl⟩ : syracuseStep 24303739 = 36455609) B36455609
theorem B32404985 : Blo 2247435 32404985 := bstep (se 2 (by rfl) ⟨12151869, by rfl⟩ : syracuseStep 32404985 = 24303739) B24303739
theorem B21603323 : Blo 2247435 21603323 := bstep (se 1 (by rfl) ⟨16202492, by rfl⟩ : syracuseStep 21603323 = 32404985) B32404985
theorem B14402215 : Blo 2247435 14402215 := bstep (se 1 (by rfl) ⟨10801661, by rfl⟩ : syracuseStep 14402215 = 21603323) B21603323
theorem B19202953 : Blo 2247435 19202953 := bstep (se 2 (by rfl) ⟨7201107, by rfl⟩ : syracuseStep 19202953 = 14402215) B14402215
theorem B25603937 : Blo 2247435 25603937 := bstep (se 2 (by rfl) ⟨9601476, by rfl⟩ : syracuseStep 25603937 = 19202953) B19202953
theorem B17069291 : Blo 2247435 17069291 := bstep (se 1 (by rfl) ⟨12801968, by rfl⟩ : syracuseStep 17069291 = 25603937) B25603937
theorem B11379527 : Blo 2247435 11379527 := bstep (se 1 (by rfl) ⟨8534645, by rfl⟩ : syracuseStep 11379527 = 17069291) B17069291
theorem B7586351 : Blo 2247435 7586351 := bstep (se 1 (by rfl) ⟨5689763, by rfl⟩ : syracuseStep 7586351 = 11379527) B11379527
theorem B5057567 : Blo 2247435 5057567 := bstep (se 1 (by rfl) ⟨3793175, by rfl⟩ : syracuseStep 5057567 = 7586351) B7586351
theorem B3371711 : Blo 2247435 3371711 := bstep (se 1 (by rfl) ⟨2528783, by rfl⟩ : syracuseStep 3371711 = 5057567) B5057567
theorem B2247807 : Blo 2247435 2247807 := bstep (se 1 (by rfl) ⟨1685855, by rfl⟩ : syracuseStep 2247807 = 3371711) B3371711
theorem B3371717 : Blo 2247435 3371717 := bbase (se 4 (by rfl) ⟨316098, by rfl⟩ : syracuseStep 3371717 = 632197) (by norm_num)
theorem B2247811 : Blo 2247435 2247811 := bstep (se 1 (by rfl) ⟨1685858, by rfl⟩ : syracuseStep 2247811 = 3371717) B3371717
theorem B3793189 : Blo 2247435 3793189 := bbase (se 4 (by rfl) ⟨355611, by rfl⟩ : syracuseStep 3793189 = 711223) (by norm_num)
theorem B5057585 : Blo 2247435 5057585 := bstep (se 2 (by rfl) ⟨1896594, by rfl⟩ : syracuseStep 5057585 = 3793189) B3793189
theorem B3371723 : Blo 2247435 3371723 := bstep (se 1 (by rfl) ⟨2528792, by rfl⟩ : syracuseStep 3371723 = 5057585) B5057585
theorem B2247815 : Blo 2247435 2247815 := bstep (se 1 (by rfl) ⟨1685861, by rfl⟩ : syracuseStep 2247815 = 3371723) B3371723
theorem B2528797 : Blo 2247435 2528797 := bbase (se 3 (by rfl) ⟨474149, by rfl⟩ : syracuseStep 2528797 = 948299) (by norm_num)
theorem B3371729 : Blo 2247435 3371729 := bstep (se 2 (by rfl) ⟨1264398, by rfl⟩ : syracuseStep 3371729 = 2528797) B2528797
theorem B2247819 : Blo 2247435 2247819 := bstep (se 1 (by rfl) ⟨1685864, by rfl⟩ : syracuseStep 2247819 = 3371729) B3371729
theorem B7586405 : Blo 2247435 7586405 := bbase (se 4 (by rfl) ⟨711225, by rfl⟩ : syracuseStep 7586405 = 1422451) (by norm_num)
theorem B5057603 : Blo 2247435 5057603 := bstep (se 1 (by rfl) ⟨3793202, by rfl⟩ : syracuseStep 5057603 = 7586405) B7586405
theorem B3371735 : Blo 2247435 3371735 := bstep (se 1 (by rfl) ⟨2528801, by rfl⟩ : syracuseStep 3371735 = 5057603) B5057603
theorem B2247823 : Blo 2247435 2247823 := bstep (se 1 (by rfl) ⟨1685867, by rfl⟩ : syracuseStep 2247823 = 3371735) B3371735
theorem B3371741 : Blo 2247435 3371741 := bbase (se 3 (by rfl) ⟨632201, by rfl⟩ : syracuseStep 3371741 = 1264403) (by norm_num)
theorem B2247827 : Blo 2247435 2247827 := bstep (se 1 (by rfl) ⟨1685870, by rfl⟩ : syracuseStep 2247827 = 3371741) B3371741
theorem B5057621 : Blo 2247435 5057621 := bbase (se 8 (by rfl) ⟨29634, by rfl⟩ : syracuseStep 5057621 = 59269) (by norm_num)
theorem B3371747 : Blo 2247435 3371747 := bstep (se 1 (by rfl) ⟨2528810, by rfl⟩ : syracuseStep 3371747 = 5057621) B5057621
theorem B2247831 : Blo 2247435 2247831 := bstep (se 1 (by rfl) ⟨1685873, by rfl⟩ : syracuseStep 2247831 = 3371747) B3371747
theorem B3417757 : Blo 2247435 3417757 := bbase (se 3 (by rfl) ⟨640829, by rfl⟩ : syracuseStep 3417757 = 1281659) (by norm_num)
theorem B18228037 : Blo 2247435 18228037 := bstep (se 4 (by rfl) ⟨1708878, by rfl⟩ : syracuseStep 18228037 = 3417757) B3417757
theorem B24304049 : Blo 2247435 24304049 := bstep (se 2 (by rfl) ⟨9114018, by rfl⟩ : syracuseStep 24304049 = 18228037) B18228037
theorem B16202699 : Blo 2247435 16202699 := bstep (se 1 (by rfl) ⟨12152024, by rfl⟩ : syracuseStep 16202699 = 24304049) B24304049
theorem B10801799 : Blo 2247435 10801799 := bstep (se 1 (by rfl) ⟨8101349, by rfl⟩ : syracuseStep 10801799 = 16202699) B16202699
theorem B7201199 : Blo 2247435 7201199 := bstep (se 1 (by rfl) ⟨5400899, by rfl⟩ : syracuseStep 7201199 = 10801799) B10801799
theorem B4800799 : Blo 2247435 4800799 := bstep (se 1 (by rfl) ⟨3600599, by rfl⟩ : syracuseStep 4800799 = 7201199) B7201199
theorem B6401065 : Blo 2247435 6401065 := bstep (se 2 (by rfl) ⟨2400399, by rfl⟩ : syracuseStep 6401065 = 4800799) B4800799
theorem B8534753 : Blo 2247435 8534753 := bstep (se 2 (by rfl) ⟨3200532, by rfl⟩ : syracuseStep 8534753 = 6401065) B6401065
theorem B5689835 : Blo 2247435 5689835 := bstep (se 1 (by rfl) ⟨4267376, by rfl⟩ : syracuseStep 5689835 = 8534753) B8534753
theorem B3793223 : Blo 2247435 3793223 := bstep (se 1 (by rfl) ⟨2844917, by rfl⟩ : syracuseStep 3793223 = 5689835) B5689835
theorem B2528815 : Blo 2247435 2528815 := bstep (se 1 (by rfl) ⟨1896611, by rfl⟩ : syracuseStep 2528815 = 3793223) B3793223
theorem B3371753 : Blo 2247435 3371753 := bstep (se 2 (by rfl) ⟨1264407, by rfl⟩ : syracuseStep 3371753 = 2528815) B2528815
theorem B2247835 : Blo 2247435 2247835 := bstep (se 1 (by rfl) ⟨1685876, by rfl⟩ : syracuseStep 2247835 = 3371753) B3371753
theorem B17302421 : Blo 2247435 17302421 := bbase (se 6 (by rfl) ⟨405525, by rfl⟩ : syracuseStep 17302421 = 811051) (by norm_num)
theorem B46139789 : Blo 2247435 46139789 := bstep (se 3 (by rfl) ⟨8651210, by rfl⟩ : syracuseStep 46139789 = 17302421) B17302421
theorem B30759859 : Blo 2247435 30759859 := bstep (se 1 (by rfl) ⟨23069894, by rfl⟩ : syracuseStep 30759859 = 46139789) B46139789
theorem B41013145 : Blo 2247435 41013145 := bstep (se 2 (by rfl) ⟨15379929, by rfl⟩ : syracuseStep 41013145 = 30759859) B30759859
theorem B54684193 : Blo 2247435 54684193 := bstep (se 2 (by rfl) ⟨20506572, by rfl⟩ : syracuseStep 54684193 = 41013145) B41013145
theorem B72912257 : Blo 2247435 72912257 := bstep (se 2 (by rfl) ⟨27342096, by rfl⟩ : syracuseStep 72912257 = 54684193) B54684193
theorem B48608171 : Blo 2247435 48608171 := bstep (se 1 (by rfl) ⟨36456128, by rfl⟩ : syracuseStep 48608171 = 72912257) B72912257
theorem B32405447 : Blo 2247435 32405447 := bstep (se 1 (by rfl) ⟨24304085, by rfl⟩ : syracuseStep 32405447 = 48608171) B48608171
theorem B21603631 : Blo 2247435 21603631 := bstep (se 1 (by rfl) ⟨16202723, by rfl⟩ : syracuseStep 21603631 = 32405447) B32405447
theorem B28804841 : Blo 2247435 28804841 := bstep (se 2 (by rfl) ⟨10801815, by rfl⟩ : syracuseStep 28804841 = 21603631) B21603631
theorem B19203227 : Blo 2247435 19203227 := bstep (se 1 (by rfl) ⟨14402420, by rfl⟩ : syracuseStep 19203227 = 28804841) B28804841
theorem B12802151 : Blo 2247435 12802151 := bstep (se 1 (by rfl) ⟨9601613, by rfl⟩ : syracuseStep 12802151 = 19203227) B19203227
theorem B8534767 : Blo 2247435 8534767 := bstep (se 1 (by rfl) ⟨6401075, by rfl⟩ : syracuseStep 8534767 = 12802151) B12802151
theorem B11379689 : Blo 2247435 11379689 := bstep (se 2 (by rfl) ⟨4267383, by rfl⟩ : syracuseStep 11379689 = 8534767) B8534767
theorem B7586459 : Blo 2247435 7586459 := bstep (se 1 (by rfl) ⟨5689844, by rfl⟩ : syracuseStep 7586459 = 11379689) B11379689
theorem B5057639 : Blo 2247435 5057639 := bstep (se 1 (by rfl) ⟨3793229, by rfl⟩ : syracuseStep 5057639 = 7586459) B7586459
theorem B3371759 : Blo 2247435 3371759 := bstep (se 1 (by rfl) ⟨2528819, by rfl⟩ : syracuseStep 3371759 = 5057639) B5057639
theorem B2247839 : Blo 2247435 2247839 := bstep (se 1 (by rfl) ⟨1685879, by rfl⟩ : syracuseStep 2247839 = 3371759) B3371759
theorem B3371765 : Blo 2247435 3371765 := bbase (se 5 (by rfl) ⟨158051, by rfl⟩ : syracuseStep 3371765 = 316103) (by norm_num)
theorem B2247843 : Blo 2247435 2247843 := bstep (se 1 (by rfl) ⟨1685882, by rfl⟩ : syracuseStep 2247843 = 3371765) B3371765
theorem B7201237 : Blo 2247435 7201237 := bbase (se 7 (by rfl) ⟨84389, by rfl⟩ : syracuseStep 7201237 = 168779) (by norm_num)
theorem B9601649 : Blo 2247435 9601649 := bstep (se 2 (by rfl) ⟨3600618, by rfl⟩ : syracuseStep 9601649 = 7201237) B7201237
theorem B6401099 : Blo 2247435 6401099 := bstep (se 1 (by rfl) ⟨4800824, by rfl⟩ : syracuseStep 6401099 = 9601649) B9601649
theorem B4267399 : Blo 2247435 4267399 := bstep (se 1 (by rfl) ⟨3200549, by rfl⟩ : syracuseStep 4267399 = 6401099) B6401099
theorem B5689865 : Blo 2247435 5689865 := bstep (se 2 (by rfl) ⟨2133699, by rfl⟩ : syracuseStep 5689865 = 4267399) B4267399
theorem B3793243 : Blo 2247435 3793243 := bstep (se 1 (by rfl) ⟨2844932, by rfl⟩ : syracuseStep 3793243 = 5689865) B5689865
theorem B5057657 : Blo 2247435 5057657 := bstep (se 2 (by rfl) ⟨1896621, by rfl⟩ : syracuseStep 5057657 = 3793243) B3793243
theorem B3371771 : Blo 2247435 3371771 := bstep (se 1 (by rfl) ⟨2528828, by rfl⟩ : syracuseStep 3371771 = 5057657) B5057657
theorem B2247847 : Blo 2247435 2247847 := bstep (se 1 (by rfl) ⟨1685885, by rfl⟩ : syracuseStep 2247847 = 3371771) B3371771
theorem B2528833 : Blo 2247435 2528833 := bbase (se 2 (by rfl) ⟨948312, by rfl⟩ : syracuseStep 2528833 = 1896625) (by norm_num)
theorem B3371777 : Blo 2247435 3371777 := bstep (se 2 (by rfl) ⟨1264416, by rfl⟩ : syracuseStep 3371777 = 2528833) B2528833
theorem B2247851 : Blo 2247435 2247851 := bstep (se 1 (by rfl) ⟨1685888, by rfl⟩ : syracuseStep 2247851 = 3371777) B3371777
theorem B5689885 : Blo 2247435 5689885 := bbase (se 3 (by rfl) ⟨1066853, by rfl⟩ : syracuseStep 5689885 = 2133707) (by norm_num)
theorem B7586513 : Blo 2247435 7586513 := bstep (se 2 (by rfl) ⟨2844942, by rfl⟩ : syracuseStep 7586513 = 5689885) B5689885
theorem B5057675 : Blo 2247435 5057675 := bstep (se 1 (by rfl) ⟨3793256, by rfl⟩ : syracuseStep 5057675 = 7586513) B7586513
theorem B3371783 : Blo 2247435 3371783 := bstep (se 1 (by rfl) ⟨2528837, by rfl⟩ : syracuseStep 3371783 = 5057675) B5057675
theorem B2247855 : Blo 2247435 2247855 := bstep (se 1 (by rfl) ⟨1685891, by rfl⟩ : syracuseStep 2247855 = 3371783) B3371783
theorem B3371789 : Blo 2247435 3371789 := bbase (se 3 (by rfl) ⟨632210, by rfl⟩ : syracuseStep 3371789 = 1264421) (by norm_num)
theorem B2247859 : Blo 2247435 2247859 := bstep (se 1 (by rfl) ⟨1685894, by rfl⟩ : syracuseStep 2247859 = 3371789) B3371789
theorem B5057693 : Blo 2247435 5057693 := bbase (se 3 (by rfl) ⟨948317, by rfl⟩ : syracuseStep 5057693 = 1896635) (by norm_num)
theorem B3371795 : Blo 2247435 3371795 := bstep (se 1 (by rfl) ⟨2528846, by rfl⟩ : syracuseStep 3371795 = 5057693) B5057693
theorem B2247863 : Blo 2247435 2247863 := bstep (se 1 (by rfl) ⟨1685897, by rfl⟩ : syracuseStep 2247863 = 3371795) B3371795
theorem B3793277 : Blo 2247435 3793277 := bbase (se 3 (by rfl) ⟨711239, by rfl⟩ : syracuseStep 3793277 = 1422479) (by norm_num)
theorem B2528851 : Blo 2247435 2528851 := bstep (se 1 (by rfl) ⟨1896638, by rfl⟩ : syracuseStep 2528851 = 3793277) B3793277
theorem B3371801 : Blo 2247435 3371801 := bstep (se 2 (by rfl) ⟨1264425, by rfl⟩ : syracuseStep 3371801 = 2528851) B2528851
theorem B2247867 : Blo 2247435 2247867 := bstep (se 1 (by rfl) ⟨1685900, by rfl⟩ : syracuseStep 2247867 = 3371801) B3371801
theorem B2278541 : Blo 2247435 2278541 := bbase (se 3 (by rfl) ⟨427226, by rfl⟩ : syracuseStep 2278541 = 854453) (by norm_num)
theorem B6076109 : Blo 2247435 6076109 := bstep (se 3 (by rfl) ⟨1139270, by rfl⟩ : syracuseStep 6076109 = 2278541) B2278541
theorem B4050739 : Blo 2247435 4050739 := bstep (se 1 (by rfl) ⟨3038054, by rfl⟩ : syracuseStep 4050739 = 6076109) B6076109
theorem B5400985 : Blo 2247435 5400985 := bstep (se 2 (by rfl) ⟨2025369, by rfl⟩ : syracuseStep 5400985 = 4050739) B4050739
theorem B7201313 : Blo 2247435 7201313 := bstep (se 2 (by rfl) ⟨2700492, by rfl⟩ : syracuseStep 7201313 = 5400985) B5400985
theorem B4800875 : Blo 2247435 4800875 := bstep (se 1 (by rfl) ⟨3600656, by rfl⟩ : syracuseStep 4800875 = 7201313) B7201313
theorem B12802333 : Blo 2247435 12802333 := bstep (se 3 (by rfl) ⟨2400437, by rfl⟩ : syracuseStep 12802333 = 4800875) B4800875
theorem B17069777 : Blo 2247435 17069777 := bstep (se 2 (by rfl) ⟨6401166, by rfl⟩ : syracuseStep 17069777 = 12802333) B12802333
theorem B11379851 : Blo 2247435 11379851 := bstep (se 1 (by rfl) ⟨8534888, by rfl⟩ : syracuseStep 11379851 = 17069777) B17069777
theorem B7586567 : Blo 2247435 7586567 := bstep (se 1 (by rfl) ⟨5689925, by rfl⟩ : syracuseStep 7586567 = 11379851) B11379851
theorem B5057711 : Blo 2247435 5057711 := bstep (se 1 (by rfl) ⟨3793283, by rfl⟩ : syracuseStep 5057711 = 7586567) B7586567
theorem B3371807 : Blo 2247435 3371807 := bstep (se 1 (by rfl) ⟨2528855, by rfl⟩ : syracuseStep 3371807 = 5057711) B5057711
theorem B2247871 : Blo 2247435 2247871 := bstep (se 1 (by rfl) ⟨1685903, by rfl⟩ : syracuseStep 2247871 = 3371807) B3371807
theorem B3371813 : Blo 2247435 3371813 := bbase (se 4 (by rfl) ⟨316107, by rfl⟩ : syracuseStep 3371813 = 632215) (by norm_num)
theorem B2247875 : Blo 2247435 2247875 := bstep (se 1 (by rfl) ⟨1685906, by rfl⟩ : syracuseStep 2247875 = 3371813) B3371813
theorem B2844973 : Blo 2247435 2844973 := bbase (se 3 (by rfl) ⟨533432, by rfl⟩ : syracuseStep 2844973 = 1066865) (by norm_num)
theorem B3793297 : Blo 2247435 3793297 := bstep (se 2 (by rfl) ⟨1422486, by rfl⟩ : syracuseStep 3793297 = 2844973) B2844973
theorem B5057729 : Blo 2247435 5057729 := bstep (se 2 (by rfl) ⟨1896648, by rfl⟩ : syracuseStep 5057729 = 3793297) B3793297
theorem B3371819 : Blo 2247435 3371819 := bstep (se 1 (by rfl) ⟨2528864, by rfl⟩ : syracuseStep 3371819 = 5057729) B5057729
theorem B2247879 : Blo 2247435 2247879 := bstep (se 1 (by rfl) ⟨1685909, by rfl⟩ : syracuseStep 2247879 = 3371819) B3371819
theorem B2528869 : Blo 2247435 2528869 := bbase (se 4 (by rfl) ⟨237081, by rfl⟩ : syracuseStep 2528869 = 474163) (by norm_num)
theorem B3371825 : Blo 2247435 3371825 := bstep (se 2 (by rfl) ⟨1264434, by rfl⟩ : syracuseStep 3371825 = 2528869) B2528869
theorem B2247883 : Blo 2247435 2247883 := bstep (se 1 (by rfl) ⟨1685912, by rfl⟩ : syracuseStep 2247883 = 3371825) B3371825
theorem B3038077 : Blo 2247435 3038077 := bbase (se 3 (by rfl) ⟨569639, by rfl⟩ : syracuseStep 3038077 = 1139279) (by norm_num)
theorem B4050769 : Blo 2247435 4050769 := bstep (se 2 (by rfl) ⟨1519038, by rfl⟩ : syracuseStep 4050769 = 3038077) B3038077
theorem B5401025 : Blo 2247435 5401025 := bstep (se 2 (by rfl) ⟨2025384, by rfl⟩ : syracuseStep 5401025 = 4050769) B4050769
theorem B3600683 : Blo 2247435 3600683 := bstep (se 1 (by rfl) ⟨2700512, by rfl⟩ : syracuseStep 3600683 = 5401025) B5401025
theorem B2400455 : Blo 2247435 2400455 := bstep (se 1 (by rfl) ⟨1800341, by rfl⟩ : syracuseStep 2400455 = 3600683) B3600683
theorem B6401213 : Blo 2247435 6401213 := bstep (se 3 (by rfl) ⟨1200227, by rfl⟩ : syracuseStep 6401213 = 2400455) B2400455
theorem B4267475 : Blo 2247435 4267475 := bstep (se 1 (by rfl) ⟨3200606, by rfl⟩ : syracuseStep 4267475 = 6401213) B6401213
theorem B2844983 : Blo 2247435 2844983 := bstep (se 1 (by rfl) ⟨2133737, by rfl⟩ : syracuseStep 2844983 = 4267475) B4267475
theorem B7586621 : Blo 2247435 7586621 := bstep (se 3 (by rfl) ⟨1422491, by rfl⟩ : syracuseStep 7586621 = 2844983) B2844983
theorem B5057747 : Blo 2247435 5057747 := bstep (se 1 (by rfl) ⟨3793310, by rfl⟩ : syracuseStep 5057747 = 7586621) B7586621
theorem B3371831 : Blo 2247435 3371831 := bstep (se 1 (by rfl) ⟨2528873, by rfl⟩ : syracuseStep 3371831 = 5057747) B5057747
theorem B2247887 : Blo 2247435 2247887 := bstep (se 1 (by rfl) ⟨1685915, by rfl⟩ : syracuseStep 2247887 = 3371831) B3371831
theorem B3371837 : Blo 2247435 3371837 := bbase (se 3 (by rfl) ⟨632219, by rfl⟩ : syracuseStep 3371837 = 1264439) (by norm_num)
theorem B2247891 : Blo 2247435 2247891 := bstep (se 1 (by rfl) ⟨1685918, by rfl⟩ : syracuseStep 2247891 = 3371837) B3371837
theorem B5057765 : Blo 2247435 5057765 := bbase (se 4 (by rfl) ⟨474165, by rfl⟩ : syracuseStep 5057765 = 948331) (by norm_num)
theorem B3371843 : Blo 2247435 3371843 := bstep (se 1 (by rfl) ⟨2528882, by rfl⟩ : syracuseStep 3371843 = 5057765) B5057765
theorem B2247895 : Blo 2247435 2247895 := bstep (se 1 (by rfl) ⟨1685921, by rfl⟩ : syracuseStep 2247895 = 3371843) B3371843
theorem B5689997 : Blo 2247435 5689997 := bbase (se 3 (by rfl) ⟨1066874, by rfl⟩ : syracuseStep 5689997 = 2133749) (by norm_num)
theorem B3793331 : Blo 2247435 3793331 := bstep (se 1 (by rfl) ⟨2844998, by rfl⟩ : syracuseStep 3793331 = 5689997) B5689997
theorem B2528887 : Blo 2247435 2528887 := bstep (se 1 (by rfl) ⟨1896665, by rfl⟩ : syracuseStep 2528887 = 3793331) B3793331
theorem B3371849 : Blo 2247435 3371849 := bstep (se 2 (by rfl) ⟨1264443, by rfl⟩ : syracuseStep 3371849 = 2528887) B2528887
theorem B2247899 : Blo 2247435 2247899 := bstep (se 1 (by rfl) ⟨1685924, by rfl⟩ : syracuseStep 2247899 = 3371849) B3371849
theorem B3200629 : Blo 2247435 3200629 := bbase (se 5 (by rfl) ⟨150029, by rfl⟩ : syracuseStep 3200629 = 300059) (by norm_num)
theorem B4267505 : Blo 2247435 4267505 := bstep (se 2 (by rfl) ⟨1600314, by rfl⟩ : syracuseStep 4267505 = 3200629) B3200629
theorem B11380013 : Blo 2247435 11380013 := bstep (se 3 (by rfl) ⟨2133752, by rfl⟩ : syracuseStep 11380013 = 4267505) B4267505
theorem B7586675 : Blo 2247435 7586675 := bstep (se 1 (by rfl) ⟨5690006, by rfl⟩ : syracuseStep 7586675 = 11380013) B11380013
theorem B5057783 : Blo 2247435 5057783 := bstep (se 1 (by rfl) ⟨3793337, by rfl⟩ : syracuseStep 5057783 = 7586675) B7586675
theorem B3371855 : Blo 2247435 3371855 := bstep (se 1 (by rfl) ⟨2528891, by rfl⟩ : syracuseStep 3371855 = 5057783) B5057783
theorem B2247903 : Blo 2247435 2247903 := bstep (se 1 (by rfl) ⟨1685927, by rfl⟩ : syracuseStep 2247903 = 3371855) B3371855
theorem B3371861 : Blo 2247435 3371861 := bbase (se 9 (by rfl) ⟨9878, by rfl⟩ : syracuseStep 3371861 = 19757) (by norm_num)
theorem B2247907 : Blo 2247435 2247907 := bstep (se 1 (by rfl) ⟨1685930, by rfl⟩ : syracuseStep 2247907 = 3371861) B3371861
theorem B2700541 : Blo 2247435 2700541 := bbase (se 3 (by rfl) ⟨506351, by rfl⟩ : syracuseStep 2700541 = 1012703) (by norm_num)
theorem B3600721 : Blo 2247435 3600721 := bstep (se 2 (by rfl) ⟨1350270, by rfl⟩ : syracuseStep 3600721 = 2700541) B2700541
theorem B4800961 : Blo 2247435 4800961 := bstep (se 2 (by rfl) ⟨1800360, by rfl⟩ : syracuseStep 4800961 = 3600721) B3600721
theorem B6401281 : Blo 2247435 6401281 := bstep (se 2 (by rfl) ⟨2400480, by rfl⟩ : syracuseStep 6401281 = 4800961) B4800961
theorem B8535041 : Blo 2247435 8535041 := bstep (se 2 (by rfl) ⟨3200640, by rfl⟩ : syracuseStep 8535041 = 6401281) B6401281
theorem B5690027 : Blo 2247435 5690027 := bstep (se 1 (by rfl) ⟨4267520, by rfl⟩ : syracuseStep 5690027 = 8535041) B8535041
theorem B3793351 : Blo 2247435 3793351 := bstep (se 1 (by rfl) ⟨2845013, by rfl⟩ : syracuseStep 3793351 = 5690027) B5690027
theorem B5057801 : Blo 2247435 5057801 := bstep (se 2 (by rfl) ⟨1896675, by rfl⟩ : syracuseStep 5057801 = 3793351) B3793351
theorem B3371867 : Blo 2247435 3371867 := bstep (se 1 (by rfl) ⟨2528900, by rfl⟩ : syracuseStep 3371867 = 5057801) B5057801
theorem B2247911 : Blo 2247435 2247911 := bstep (se 1 (by rfl) ⟨1685933, by rfl⟩ : syracuseStep 2247911 = 3371867) B3371867
theorem B2528905 : Blo 2247435 2528905 := bbase (se 2 (by rfl) ⟨948339, by rfl⟩ : syracuseStep 2528905 = 1896679) (by norm_num)
theorem B3371873 : Blo 2247435 3371873 := bstep (se 2 (by rfl) ⟨1264452, by rfl⟩ : syracuseStep 3371873 = 2528905) B2528905
theorem B2247915 : Blo 2247435 2247915 := bstep (se 1 (by rfl) ⟨1685936, by rfl⟩ : syracuseStep 2247915 = 3371873) B3371873
theorem B5196773 : Blo 2247435 5196773 := bbase (se 4 (by rfl) ⟨487197, by rfl⟩ : syracuseStep 5196773 = 974395) (by norm_num)
theorem B13858061 : Blo 2247435 13858061 := bstep (se 3 (by rfl) ⟨2598386, by rfl⟩ : syracuseStep 13858061 = 5196773) B5196773
theorem B36954829 : Blo 2247435 36954829 := bstep (se 3 (by rfl) ⟨6929030, by rfl⟩ : syracuseStep 36954829 = 13858061) B13858061
theorem B49273105 : Blo 2247435 49273105 := bstep (se 2 (by rfl) ⟨18477414, by rfl⟩ : syracuseStep 49273105 = 36954829) B36954829
theorem B65697473 : Blo 2247435 65697473 := bstep (se 2 (by rfl) ⟨24636552, by rfl⟩ : syracuseStep 65697473 = 49273105) B49273105
theorem B43798315 : Blo 2247435 43798315 := bstep (se 1 (by rfl) ⟨32848736, by rfl⟩ : syracuseStep 43798315 = 65697473) B65697473
theorem B58397753 : Blo 2247435 58397753 := bstep (se 2 (by rfl) ⟨21899157, by rfl⟩ : syracuseStep 58397753 = 43798315) B43798315
theorem B38931835 : Blo 2247435 38931835 := bstep (se 1 (by rfl) ⟨29198876, by rfl⟩ : syracuseStep 38931835 = 58397753) B58397753
theorem B51909113 : Blo 2247435 51909113 := bstep (se 2 (by rfl) ⟨19465917, by rfl⟩ : syracuseStep 51909113 = 38931835) B38931835
theorem B34606075 : Blo 2247435 34606075 := bstep (se 1 (by rfl) ⟨25954556, by rfl⟩ : syracuseStep 34606075 = 51909113) B51909113
theorem B46141433 : Blo 2247435 46141433 := bstep (se 2 (by rfl) ⟨17303037, by rfl⟩ : syracuseStep 46141433 = 34606075) B34606075
theorem B30760955 : Blo 2247435 30760955 := bstep (se 1 (by rfl) ⟨23070716, by rfl⟩ : syracuseStep 30760955 = 46141433) B46141433
theorem B20507303 : Blo 2247435 20507303 := bstep (se 1 (by rfl) ⟨15380477, by rfl⟩ : syracuseStep 20507303 = 30760955) B30760955
theorem B54686141 : Blo 2247435 54686141 := bstep (se 3 (by rfl) ⟨10253651, by rfl⟩ : syracuseStep 54686141 = 20507303) B20507303
theorem B36457427 : Blo 2247435 36457427 := bstep (se 1 (by rfl) ⟨27343070, by rfl⟩ : syracuseStep 36457427 = 54686141) B54686141
theorem B24304951 : Blo 2247435 24304951 := bstep (se 1 (by rfl) ⟨18228713, by rfl⟩ : syracuseStep 24304951 = 36457427) B36457427
theorem B32406601 : Blo 2247435 32406601 := bstep (se 2 (by rfl) ⟨12152475, by rfl⟩ : syracuseStep 32406601 = 24304951) B24304951
theorem B43208801 : Blo 2247435 43208801 := bstep (se 2 (by rfl) ⟨16203300, by rfl⟩ : syracuseStep 43208801 = 32406601) B32406601
theorem B28805867 : Blo 2247435 28805867 := bstep (se 1 (by rfl) ⟨21604400, by rfl⟩ : syracuseStep 28805867 = 43208801) B43208801
theorem B19203911 : Blo 2247435 19203911 := bstep (se 1 (by rfl) ⟨14402933, by rfl⟩ : syracuseStep 19203911 = 28805867) B28805867
theorem B12802607 : Blo 2247435 12802607 := bstep (se 1 (by rfl) ⟨9601955, by rfl⟩ : syracuseStep 12802607 = 19203911) B19203911
theorem B8535071 : Blo 2247435 8535071 := bstep (se 1 (by rfl) ⟨6401303, by rfl⟩ : syracuseStep 8535071 = 12802607) B12802607
theorem B5690047 : Blo 2247435 5690047 := bstep (se 1 (by rfl) ⟨4267535, by rfl⟩ : syracuseStep 5690047 = 8535071) B8535071
theorem B7586729 : Blo 2247435 7586729 := bstep (se 2 (by rfl) ⟨2845023, by rfl⟩ : syracuseStep 7586729 = 5690047) B5690047
theorem B5057819 : Blo 2247435 5057819 := bstep (se 1 (by rfl) ⟨3793364, by rfl⟩ : syracuseStep 5057819 = 7586729) B7586729
theorem B3371879 : Blo 2247435 3371879 := bstep (se 1 (by rfl) ⟨2528909, by rfl⟩ : syracuseStep 3371879 = 5057819) B5057819
theorem B2247919 : Blo 2247435 2247919 := bstep (se 1 (by rfl) ⟨1685939, by rfl⟩ : syracuseStep 2247919 = 3371879) B3371879
theorem B3371885 : Blo 2247435 3371885 := bbase (se 3 (by rfl) ⟨632228, by rfl⟩ : syracuseStep 3371885 = 1264457) (by norm_num)
theorem B2247923 : Blo 2247435 2247923 := bstep (se 1 (by rfl) ⟨1685942, by rfl⟩ : syracuseStep 2247923 = 3371885) B3371885
theorem B5057837 : Blo 2247435 5057837 := bbase (se 3 (by rfl) ⟨948344, by rfl⟩ : syracuseStep 5057837 = 1896689) (by norm_num)
theorem B3371891 : Blo 2247435 3371891 := bstep (se 1 (by rfl) ⟨2528918, by rfl⟩ : syracuseStep 3371891 = 5057837) B5057837
theorem B2247927 : Blo 2247435 2247927 := bstep (se 1 (by rfl) ⟨1685945, by rfl⟩ : syracuseStep 2247927 = 3371891) B3371891
theorem B10802261 : Blo 2247435 10802261 := bbase (se 8 (by rfl) ⟨63294, by rfl⟩ : syracuseStep 10802261 = 126589) (by norm_num)
theorem B7201507 : Blo 2247435 7201507 := bstep (se 1 (by rfl) ⟨5401130, by rfl⟩ : syracuseStep 7201507 = 10802261) B10802261
theorem B9602009 : Blo 2247435 9602009 := bstep (se 2 (by rfl) ⟨3600753, by rfl⟩ : syracuseStep 9602009 = 7201507) B7201507
theorem B6401339 : Blo 2247435 6401339 := bstep (se 1 (by rfl) ⟨4801004, by rfl⟩ : syracuseStep 6401339 = 9602009) B9602009
theorem B4267559 : Blo 2247435 4267559 := bstep (se 1 (by rfl) ⟨3200669, by rfl⟩ : syracuseStep 4267559 = 6401339) B6401339
theorem B2845039 : Blo 2247435 2845039 := bstep (se 1 (by rfl) ⟨2133779, by rfl⟩ : syracuseStep 2845039 = 4267559) B4267559
theorem B3793385 : Blo 2247435 3793385 := bstep (se 2 (by rfl) ⟨1422519, by rfl⟩ : syracuseStep 3793385 = 2845039) B2845039
theorem B2528923 : Blo 2247435 2528923 := bstep (se 1 (by rfl) ⟨1896692, by rfl⟩ : syracuseStep 2528923 = 3793385) B3793385
theorem B3371897 : Blo 2247435 3371897 := bstep (se 2 (by rfl) ⟨1264461, by rfl⟩ : syracuseStep 3371897 = 2528923) B2528923
theorem B2247931 : Blo 2247435 2247931 := bstep (se 1 (by rfl) ⟨1685948, by rfl⟩ : syracuseStep 2247931 = 3371897) B3371897
theorem B36457685 : Blo 2247435 36457685 := bbase (se 7 (by rfl) ⟨427238, by rfl⟩ : syracuseStep 36457685 = 854477) (by norm_num)
theorem B24305123 : Blo 2247435 24305123 := bstep (se 1 (by rfl) ⟨18228842, by rfl⟩ : syracuseStep 24305123 = 36457685) B36457685
theorem B16203415 : Blo 2247435 16203415 := bstep (se 1 (by rfl) ⟨12152561, by rfl⟩ : syracuseStep 16203415 = 24305123) B24305123
theorem B21604553 : Blo 2247435 21604553 := bstep (se 2 (by rfl) ⟨8101707, by rfl⟩ : syracuseStep 21604553 = 16203415) B16203415
theorem B14403035 : Blo 2247435 14403035 := bstep (se 1 (by rfl) ⟨10802276, by rfl⟩ : syracuseStep 14403035 = 21604553) B21604553
theorem B38408093 : Blo 2247435 38408093 := bstep (se 3 (by rfl) ⟨7201517, by rfl⟩ : syracuseStep 38408093 = 14403035) B14403035
theorem B25605395 : Blo 2247435 25605395 := bstep (se 1 (by rfl) ⟨19204046, by rfl⟩ : syracuseStep 25605395 = 38408093) B38408093
theorem B17070263 : Blo 2247435 17070263 := bstep (se 1 (by rfl) ⟨12802697, by rfl⟩ : syracuseStep 17070263 = 25605395) B25605395
theorem B11380175 : Blo 2247435 11380175 := bstep (se 1 (by rfl) ⟨8535131, by rfl⟩ : syracuseStep 11380175 = 17070263) B17070263
theorem B7586783 : Blo 2247435 7586783 := bstep (se 1 (by rfl) ⟨5690087, by rfl⟩ : syracuseStep 7586783 = 11380175) B11380175
theorem B5057855 : Blo 2247435 5057855 := bstep (se 1 (by rfl) ⟨3793391, by rfl⟩ : syracuseStep 5057855 = 7586783) B7586783
theorem B3371903 : Blo 2247435 3371903 := bstep (se 1 (by rfl) ⟨2528927, by rfl⟩ : syracuseStep 3371903 = 5057855) B5057855
theorem B2247935 : Blo 2247435 2247935 := bstep (se 1 (by rfl) ⟨1685951, by rfl⟩ : syracuseStep 2247935 = 3371903) B3371903
theorem B3371909 : Blo 2247435 3371909 := bbase (se 4 (by rfl) ⟨316116, by rfl⟩ : syracuseStep 3371909 = 632233) (by norm_num)
theorem B2247939 : Blo 2247435 2247939 := bstep (se 1 (by rfl) ⟨1685954, by rfl⟩ : syracuseStep 2247939 = 3371909) B3371909
theorem B3793405 : Blo 2247435 3793405 := bbase (se 3 (by rfl) ⟨711263, by rfl⟩ : syracuseStep 3793405 = 1422527) (by norm_num)
theorem B5057873 : Blo 2247435 5057873 := bstep (se 2 (by rfl) ⟨1896702, by rfl⟩ : syracuseStep 5057873 = 3793405) B3793405
theorem B3371915 : Blo 2247435 3371915 := bstep (se 1 (by rfl) ⟨2528936, by rfl⟩ : syracuseStep 3371915 = 5057873) B5057873
theorem B2247943 : Blo 2247435 2247943 := bstep (se 1 (by rfl) ⟨1685957, by rfl⟩ : syracuseStep 2247943 = 3371915) B3371915
theorem B2528941 : Blo 2247435 2528941 := bbase (se 3 (by rfl) ⟨474176, by rfl⟩ : syracuseStep 2528941 = 948353) (by norm_num)
theorem B3371921 : Blo 2247435 3371921 := bstep (se 2 (by rfl) ⟨1264470, by rfl⟩ : syracuseStep 3371921 = 2528941) B2528941
theorem B2247947 : Blo 2247435 2247947 := bstep (se 1 (by rfl) ⟨1685960, by rfl⟩ : syracuseStep 2247947 = 3371921) B3371921
theorem B7586837 : Blo 2247435 7586837 := bbase (se 6 (by rfl) ⟨177816, by rfl⟩ : syracuseStep 7586837 = 355633) (by norm_num)
theorem B5057891 : Blo 2247435 5057891 := bstep (se 1 (by rfl) ⟨3793418, by rfl⟩ : syracuseStep 5057891 = 7586837) B7586837
theorem B3371927 : Blo 2247435 3371927 := bstep (se 1 (by rfl) ⟨2528945, by rfl⟩ : syracuseStep 3371927 = 5057891) B5057891
theorem B2247951 : Blo 2247435 2247951 := bstep (se 1 (by rfl) ⟨1685963, by rfl⟩ : syracuseStep 2247951 = 3371927) B3371927
theorem B3371933 : Blo 2247435 3371933 := bbase (se 3 (by rfl) ⟨632237, by rfl⟩ : syracuseStep 3371933 = 1264475) (by norm_num)
theorem B2247955 : Blo 2247435 2247955 := bstep (se 1 (by rfl) ⟨1685966, by rfl⟩ : syracuseStep 2247955 = 3371933) B3371933
theorem B5057909 : Blo 2247435 5057909 := bbase (se 5 (by rfl) ⟨237089, by rfl⟩ : syracuseStep 5057909 = 474179) (by norm_num)
theorem B3371939 : Blo 2247435 3371939 := bstep (se 1 (by rfl) ⟨2528954, by rfl⟩ : syracuseStep 3371939 = 5057909) B5057909
theorem B2247959 : Blo 2247435 2247959 := bstep (se 1 (by rfl) ⟨1685969, by rfl⟩ : syracuseStep 2247959 = 3371939) B3371939
theorem B4557269 : Blo 2247435 4557269 := bbase (se 7 (by rfl) ⟨53405, by rfl⟩ : syracuseStep 4557269 = 106811) (by norm_num)
theorem B3038179 : Blo 2247435 3038179 := bstep (se 1 (by rfl) ⟨2278634, by rfl⟩ : syracuseStep 3038179 = 4557269) B4557269
theorem B4050905 : Blo 2247435 4050905 := bstep (se 2 (by rfl) ⟨1519089, by rfl⟩ : syracuseStep 4050905 = 3038179) B3038179
theorem B10802413 : Blo 2247435 10802413 := bstep (se 3 (by rfl) ⟨2025452, by rfl⟩ : syracuseStep 10802413 = 4050905) B4050905
theorem B14403217 : Blo 2247435 14403217 := bstep (se 2 (by rfl) ⟨5401206, by rfl⟩ : syracuseStep 14403217 = 10802413) B10802413
theorem B19204289 : Blo 2247435 19204289 := bstep (se 2 (by rfl) ⟨7201608, by rfl⟩ : syracuseStep 19204289 = 14403217) B14403217
theorem B12802859 : Blo 2247435 12802859 := bstep (se 1 (by rfl) ⟨9602144, by rfl⟩ : syracuseStep 12802859 = 19204289) B19204289
theorem B8535239 : Blo 2247435 8535239 := bstep (se 1 (by rfl) ⟨6401429, by rfl⟩ : syracuseStep 8535239 = 12802859) B12802859
theorem B5690159 : Blo 2247435 5690159 := bstep (se 1 (by rfl) ⟨4267619, by rfl⟩ : syracuseStep 5690159 = 8535239) B8535239
theorem B3793439 : Blo 2247435 3793439 := bstep (se 1 (by rfl) ⟨2845079, by rfl⟩ : syracuseStep 3793439 = 5690159) B5690159
theorem B2528959 : Blo 2247435 2528959 := bstep (se 1 (by rfl) ⟨1896719, by rfl⟩ : syracuseStep 2528959 = 3793439) B3793439
theorem B3371945 : Blo 2247435 3371945 := bstep (se 2 (by rfl) ⟨1264479, by rfl⟩ : syracuseStep 3371945 = 2528959) B2528959
theorem B2247963 : Blo 2247435 2247963 := bstep (se 1 (by rfl) ⟨1685972, by rfl⟩ : syracuseStep 2247963 = 3371945) B3371945
theorem B8535253 : Blo 2247435 8535253 := bbase (se 7 (by rfl) ⟨100022, by rfl⟩ : syracuseStep 8535253 = 200045) (by norm_num)
theorem B11380337 : Blo 2247435 11380337 := bstep (se 2 (by rfl) ⟨4267626, by rfl⟩ : syracuseStep 11380337 = 8535253) B8535253
theorem B7586891 : Blo 2247435 7586891 := bstep (se 1 (by rfl) ⟨5690168, by rfl⟩ : syracuseStep 7586891 = 11380337) B11380337
theorem B5057927 : Blo 2247435 5057927 := bstep (se 1 (by rfl) ⟨3793445, by rfl⟩ : syracuseStep 5057927 = 7586891) B7586891
theorem B3371951 : Blo 2247435 3371951 := bstep (se 1 (by rfl) ⟨2528963, by rfl⟩ : syracuseStep 3371951 = 5057927) B5057927
theorem B2247967 : Blo 2247435 2247967 := bstep (se 1 (by rfl) ⟨1685975, by rfl⟩ : syracuseStep 2247967 = 3371951) B3371951
theorem B3371957 : Blo 2247435 3371957 := bbase (se 5 (by rfl) ⟨158060, by rfl⟩ : syracuseStep 3371957 = 316121) (by norm_num)
theorem B2247971 : Blo 2247435 2247971 := bstep (se 1 (by rfl) ⟨1685978, by rfl⟩ : syracuseStep 2247971 = 3371957) B3371957
theorem B5690189 : Blo 2247435 5690189 := bbase (se 3 (by rfl) ⟨1066910, by rfl⟩ : syracuseStep 5690189 = 2133821) (by norm_num)
theorem B3793459 : Blo 2247435 3793459 := bstep (se 1 (by rfl) ⟨2845094, by rfl⟩ : syracuseStep 3793459 = 5690189) B5690189
theorem B5057945 : Blo 2247435 5057945 := bstep (se 2 (by rfl) ⟨1896729, by rfl⟩ : syracuseStep 5057945 = 3793459) B3793459
theorem B3371963 : Blo 2247435 3371963 := bstep (se 1 (by rfl) ⟨2528972, by rfl⟩ : syracuseStep 3371963 = 5057945) B5057945
theorem B2247975 : Blo 2247435 2247975 := bstep (se 1 (by rfl) ⟨1685981, by rfl⟩ : syracuseStep 2247975 = 3371963) B3371963
theorem B2528977 : Blo 2247435 2528977 := bbase (se 2 (by rfl) ⟨948366, by rfl⟩ : syracuseStep 2528977 = 1896733) (by norm_num)
theorem B3371969 : Blo 2247435 3371969 := bstep (se 2 (by rfl) ⟨1264488, by rfl⟩ : syracuseStep 3371969 = 2528977) B2528977
theorem B2247979 : Blo 2247435 2247979 := bstep (se 1 (by rfl) ⟨1685984, by rfl⟩ : syracuseStep 2247979 = 3371969) B3371969
theorem B12977653 : Blo 2247435 12977653 := bbase (se 5 (by rfl) ⟨608327, by rfl⟩ : syracuseStep 12977653 = 1216655) (by norm_num)
theorem B17303537 : Blo 2247435 17303537 := bstep (se 2 (by rfl) ⟨6488826, by rfl⟩ : syracuseStep 17303537 = 12977653) B12977653
theorem B11535691 : Blo 2247435 11535691 := bstep (se 1 (by rfl) ⟨8651768, by rfl⟩ : syracuseStep 11535691 = 17303537) B17303537
theorem B15380921 : Blo 2247435 15380921 := bstep (se 2 (by rfl) ⟨5767845, by rfl⟩ : syracuseStep 15380921 = 11535691) B11535691
theorem B10253947 : Blo 2247435 10253947 := bstep (se 1 (by rfl) ⟨7690460, by rfl⟩ : syracuseStep 10253947 = 15380921) B15380921
theorem B13671929 : Blo 2247435 13671929 := bstep (se 2 (by rfl) ⟨5126973, by rfl⟩ : syracuseStep 13671929 = 10253947) B10253947
theorem B9114619 : Blo 2247435 9114619 := bstep (se 1 (by rfl) ⟨6835964, by rfl⟩ : syracuseStep 9114619 = 13671929) B13671929
theorem B12152825 : Blo 2247435 12152825 := bstep (se 2 (by rfl) ⟨4557309, by rfl⟩ : syracuseStep 12152825 = 9114619) B9114619
theorem B8101883 : Blo 2247435 8101883 := bstep (se 1 (by rfl) ⟨6076412, by rfl⟩ : syracuseStep 8101883 = 12152825) B12152825
theorem B5401255 : Blo 2247435 5401255 := bstep (se 1 (by rfl) ⟨4050941, by rfl⟩ : syracuseStep 5401255 = 8101883) B8101883
theorem B7201673 : Blo 2247435 7201673 := bstep (se 2 (by rfl) ⟨2700627, by rfl⟩ : syracuseStep 7201673 = 5401255) B5401255
theorem B4801115 : Blo 2247435 4801115 := bstep (se 1 (by rfl) ⟨3600836, by rfl⟩ : syracuseStep 4801115 = 7201673) B7201673
theorem B3200743 : Blo 2247435 3200743 := bstep (se 1 (by rfl) ⟨2400557, by rfl⟩ : syracuseStep 3200743 = 4801115) B4801115
theorem B4267657 : Blo 2247435 4267657 := bstep (se 2 (by rfl) ⟨1600371, by rfl⟩ : syracuseStep 4267657 = 3200743) B3200743
theorem B5690209 : Blo 2247435 5690209 := bstep (se 2 (by rfl) ⟨2133828, by rfl⟩ : syracuseStep 5690209 = 4267657) B4267657
theorem B7586945 : Blo 2247435 7586945 := bstep (se 2 (by rfl) ⟨2845104, by rfl⟩ : syracuseStep 7586945 = 5690209) B5690209
theorem B5057963 : Blo 2247435 5057963 := bstep (se 1 (by rfl) ⟨3793472, by rfl⟩ : syracuseStep 5057963 = 7586945) B7586945
theorem B3371975 : Blo 2247435 3371975 := bstep (se 1 (by rfl) ⟨2528981, by rfl⟩ : syracuseStep 3371975 = 5057963) B5057963
theorem B2247983 : Blo 2247435 2247983 := bstep (se 1 (by rfl) ⟨1685987, by rfl⟩ : syracuseStep 2247983 = 3371975) B3371975
theorem B3371981 : Blo 2247435 3371981 := bbase (se 3 (by rfl) ⟨632246, by rfl⟩ : syracuseStep 3371981 = 1264493) (by norm_num)
theorem B2247987 : Blo 2247435 2247987 := bstep (se 1 (by rfl) ⟨1685990, by rfl⟩ : syracuseStep 2247987 = 3371981) B3371981
theorem B5057981 : Blo 2247435 5057981 := bbase (se 3 (by rfl) ⟨948371, by rfl⟩ : syracuseStep 5057981 = 1896743) (by norm_num)
theorem B3371987 : Blo 2247435 3371987 := bstep (se 1 (by rfl) ⟨2528990, by rfl⟩ : syracuseStep 3371987 = 5057981) B5057981
theorem B2247991 : Blo 2247435 2247991 := bstep (se 1 (by rfl) ⟨1685993, by rfl⟩ : syracuseStep 2247991 = 3371987) B3371987
theorem B3793493 : Blo 2247435 3793493 := bbase (se 8 (by rfl) ⟨22227, by rfl⟩ : syracuseStep 3793493 = 44455) (by norm_num)
theorem B2528995 : Blo 2247435 2528995 := bstep (se 1 (by rfl) ⟨1896746, by rfl⟩ : syracuseStep 2528995 = 3793493) B3793493
theorem B3371993 : Blo 2247435 3371993 := bstep (se 2 (by rfl) ⟨1264497, by rfl⟩ : syracuseStep 3371993 = 2528995) B2528995
theorem B2247995 : Blo 2247435 2247995 := bstep (se 1 (by rfl) ⟨1685996, by rfl⟩ : syracuseStep 2247995 = 3371993) B3371993
theorem B4557341 : Blo 2247435 4557341 := bbase (se 3 (by rfl) ⟨854501, by rfl⟩ : syracuseStep 4557341 = 1709003) (by norm_num)
theorem B12152909 : Blo 2247435 12152909 := bstep (se 3 (by rfl) ⟨2278670, by rfl⟩ : syracuseStep 12152909 = 4557341) B4557341
theorem B8101939 : Blo 2247435 8101939 := bstep (se 1 (by rfl) ⟨6076454, by rfl⟩ : syracuseStep 8101939 = 12152909) B12152909
theorem B10802585 : Blo 2247435 10802585 := bstep (se 2 (by rfl) ⟨4050969, by rfl⟩ : syracuseStep 10802585 = 8101939) B8101939
theorem B7201723 : Blo 2247435 7201723 := bstep (se 1 (by rfl) ⟨5401292, by rfl⟩ : syracuseStep 7201723 = 10802585) B10802585
theorem B9602297 : Blo 2247435 9602297 := bstep (se 2 (by rfl) ⟨3600861, by rfl⟩ : syracuseStep 9602297 = 7201723) B7201723
theorem B6401531 : Blo 2247435 6401531 := bstep (se 1 (by rfl) ⟨4801148, by rfl⟩ : syracuseStep 6401531 = 9602297) B9602297
theorem B17070749 : Blo 2247435 17070749 := bstep (se 3 (by rfl) ⟨3200765, by rfl⟩ : syracuseStep 17070749 = 6401531) B6401531
theorem B11380499 : Blo 2247435 11380499 := bstep (se 1 (by rfl) ⟨8535374, by rfl⟩ : syracuseStep 11380499 = 17070749) B17070749
theorem B7586999 : Blo 2247435 7586999 := bstep (se 1 (by rfl) ⟨5690249, by rfl⟩ : syracuseStep 7586999 = 11380499) B11380499
theorem B5057999 : Blo 2247435 5057999 := bstep (se 1 (by rfl) ⟨3793499, by rfl⟩ : syracuseStep 5057999 = 7586999) B7586999
theorem B3371999 : Blo 2247435 3371999 := bstep (se 1 (by rfl) ⟨2528999, by rfl⟩ : syracuseStep 3371999 = 5057999) B5057999
theorem B2247999 : Blo 2247435 2247999 := bstep (se 1 (by rfl) ⟨1685999, by rfl⟩ : syracuseStep 2247999 = 3371999) B3371999
theorem B3372005 : Blo 2247435 3372005 := bbase (se 4 (by rfl) ⟨316125, by rfl⟩ : syracuseStep 3372005 = 632251) (by norm_num)
theorem B2248003 : Blo 2247435 2248003 := bstep (se 1 (by rfl) ⟨1686002, by rfl⟩ : syracuseStep 2248003 = 3372005) B3372005
theorem B3650005 : Blo 2247435 3650005 := bbase (se 7 (by rfl) ⟨42773, by rfl⟩ : syracuseStep 3650005 = 85547) (by norm_num)
theorem B19466693 : Blo 2247435 19466693 := bstep (se 4 (by rfl) ⟨1825002, by rfl⟩ : syracuseStep 19466693 = 3650005) B3650005
theorem B12977795 : Blo 2247435 12977795 := bstep (se 1 (by rfl) ⟨9733346, by rfl⟩ : syracuseStep 12977795 = 19466693) B19466693
theorem B8651863 : Blo 2247435 8651863 := bstep (se 1 (by rfl) ⟨6488897, by rfl⟩ : syracuseStep 8651863 = 12977795) B12977795
theorem B11535817 : Blo 2247435 11535817 := bstep (se 2 (by rfl) ⟨4325931, by rfl⟩ : syracuseStep 11535817 = 8651863) B8651863
theorem B15381089 : Blo 2247435 15381089 := bstep (se 2 (by rfl) ⟨5767908, by rfl⟩ : syracuseStep 15381089 = 11535817) B11535817
theorem B10254059 : Blo 2247435 10254059 := bstep (se 1 (by rfl) ⟨7690544, by rfl⟩ : syracuseStep 10254059 = 15381089) B15381089
theorem B6836039 : Blo 2247435 6836039 := bstep (se 1 (by rfl) ⟨5127029, by rfl⟩ : syracuseStep 6836039 = 10254059) B10254059
theorem B4557359 : Blo 2247435 4557359 := bstep (se 1 (by rfl) ⟨3418019, by rfl⟩ : syracuseStep 4557359 = 6836039) B6836039
theorem B3038239 : Blo 2247435 3038239 := bstep (se 1 (by rfl) ⟨2278679, by rfl⟩ : syracuseStep 3038239 = 4557359) B4557359
theorem B4050985 : Blo 2247435 4050985 := bstep (se 2 (by rfl) ⟨1519119, by rfl⟩ : syracuseStep 4050985 = 3038239) B3038239
theorem B5401313 : Blo 2247435 5401313 := bstep (se 2 (by rfl) ⟨2025492, by rfl⟩ : syracuseStep 5401313 = 4050985) B4050985
theorem B3600875 : Blo 2247435 3600875 := bstep (se 1 (by rfl) ⟨2700656, by rfl⟩ : syracuseStep 3600875 = 5401313) B5401313
theorem B9602333 : Blo 2247435 9602333 := bstep (se 3 (by rfl) ⟨1800437, by rfl⟩ : syracuseStep 9602333 = 3600875) B3600875
theorem B6401555 : Blo 2247435 6401555 := bstep (se 1 (by rfl) ⟨4801166, by rfl⟩ : syracuseStep 6401555 = 9602333) B9602333
theorem B4267703 : Blo 2247435 4267703 := bstep (se 1 (by rfl) ⟨3200777, by rfl⟩ : syracuseStep 4267703 = 6401555) B6401555
theorem B2845135 : Blo 2247435 2845135 := bstep (se 1 (by rfl) ⟨2133851, by rfl⟩ : syracuseStep 2845135 = 4267703) B4267703
theorem B3793513 : Blo 2247435 3793513 := bstep (se 2 (by rfl) ⟨1422567, by rfl⟩ : syracuseStep 3793513 = 2845135) B2845135
theorem B5058017 : Blo 2247435 5058017 := bstep (se 2 (by rfl) ⟨1896756, by rfl⟩ : syracuseStep 5058017 = 3793513) B3793513
theorem B3372011 : Blo 2247435 3372011 := bstep (se 1 (by rfl) ⟨2529008, by rfl⟩ : syracuseStep 3372011 = 5058017) B5058017
theorem B2248007 : Blo 2247435 2248007 := bstep (se 1 (by rfl) ⟨1686005, by rfl⟩ : syracuseStep 2248007 = 3372011) B3372011
theorem B2529013 : Blo 2247435 2529013 := bbase (se 5 (by rfl) ⟨118547, by rfl⟩ : syracuseStep 2529013 = 237095) (by norm_num)
theorem B3372017 : Blo 2247435 3372017 := bstep (se 2 (by rfl) ⟨1264506, by rfl⟩ : syracuseStep 3372017 = 2529013) B2529013
theorem B2248011 : Blo 2247435 2248011 := bstep (se 1 (by rfl) ⟨1686008, by rfl⟩ : syracuseStep 2248011 = 3372017) B3372017
theorem B2845145 : Blo 2247435 2845145 := bbase (se 2 (by rfl) ⟨1066929, by rfl⟩ : syracuseStep 2845145 = 2133859) (by norm_num)
theorem B7587053 : Blo 2247435 7587053 := bstep (se 3 (by rfl) ⟨1422572, by rfl⟩ : syracuseStep 7587053 = 2845145) B2845145
theorem B5058035 : Blo 2247435 5058035 := bstep (se 1 (by rfl) ⟨3793526, by rfl⟩ : syracuseStep 5058035 = 7587053) B7587053
theorem B3372023 : Blo 2247435 3372023 := bstep (se 1 (by rfl) ⟨2529017, by rfl⟩ : syracuseStep 3372023 = 5058035) B5058035
theorem B2248015 : Blo 2247435 2248015 := bstep (se 1 (by rfl) ⟨1686011, by rfl⟩ : syracuseStep 2248015 = 3372023) B3372023
theorem B3372029 : Blo 2247435 3372029 := bbase (se 3 (by rfl) ⟨632255, by rfl⟩ : syracuseStep 3372029 = 1264511) (by norm_num)
theorem B2248019 : Blo 2247435 2248019 := bstep (se 1 (by rfl) ⟨1686014, by rfl⟩ : syracuseStep 2248019 = 3372029) B3372029
theorem B5058053 : Blo 2247435 5058053 := bbase (se 4 (by rfl) ⟨474192, by rfl⟩ : syracuseStep 5058053 = 948385) (by norm_num)
theorem B3372035 : Blo 2247435 3372035 := bstep (se 1 (by rfl) ⟨2529026, by rfl⟩ : syracuseStep 3372035 = 5058053) B5058053
theorem B2248023 : Blo 2247435 2248023 := bstep (se 1 (by rfl) ⟨1686017, by rfl⟩ : syracuseStep 2248023 = 3372035) B3372035
theorem B4267741 : Blo 2247435 4267741 := bbase (se 3 (by rfl) ⟨800201, by rfl⟩ : syracuseStep 4267741 = 1600403) (by norm_num)
theorem B5690321 : Blo 2247435 5690321 := bstep (se 2 (by rfl) ⟨2133870, by rfl⟩ : syracuseStep 5690321 = 4267741) B4267741
theorem B3793547 : Blo 2247435 3793547 := bstep (se 1 (by rfl) ⟨2845160, by rfl⟩ : syracuseStep 3793547 = 5690321) B5690321
theorem B2529031 : Blo 2247435 2529031 := bstep (se 1 (by rfl) ⟨1896773, by rfl⟩ : syracuseStep 2529031 = 3793547) B3793547
theorem B3372041 : Blo 2247435 3372041 := bstep (se 2 (by rfl) ⟨1264515, by rfl⟩ : syracuseStep 3372041 = 2529031) B2529031
theorem B2248027 : Blo 2247435 2248027 := bstep (se 1 (by rfl) ⟨1686020, by rfl⟩ : syracuseStep 2248027 = 3372041) B3372041
theorem B11380661 : Blo 2247435 11380661 := bbase (se 5 (by rfl) ⟨533468, by rfl⟩ : syracuseStep 11380661 = 1066937) (by norm_num)
theorem B7587107 : Blo 2247435 7587107 := bstep (se 1 (by rfl) ⟨5690330, by rfl⟩ : syracuseStep 7587107 = 11380661) B11380661
theorem B5058071 : Blo 2247435 5058071 := bstep (se 1 (by rfl) ⟨3793553, by rfl⟩ : syracuseStep 5058071 = 7587107) B7587107
theorem B3372047 : Blo 2247435 3372047 := bstep (se 1 (by rfl) ⟨2529035, by rfl⟩ : syracuseStep 3372047 = 5058071) B5058071
theorem B2248031 : Blo 2247435 2248031 := bstep (se 1 (by rfl) ⟨1686023, by rfl⟩ : syracuseStep 2248031 = 3372047) B3372047
theorem B3372053 : Blo 2247435 3372053 := bbase (se 6 (by rfl) ⟨79032, by rfl⟩ : syracuseStep 3372053 = 158065) (by norm_num)
theorem B2248035 : Blo 2247435 2248035 := bstep (se 1 (by rfl) ⟨1686026, by rfl⟩ : syracuseStep 2248035 = 3372053) B3372053
theorem B5127101 : Blo 2247435 5127101 := bbase (se 3 (by rfl) ⟨961331, by rfl⟩ : syracuseStep 5127101 = 1922663) (by norm_num)
theorem B3418067 : Blo 2247435 3418067 := bstep (se 1 (by rfl) ⟨2563550, by rfl⟩ : syracuseStep 3418067 = 5127101) B5127101
theorem B2278711 : Blo 2247435 2278711 := bstep (se 1 (by rfl) ⟨1709033, by rfl⟩ : syracuseStep 2278711 = 3418067) B3418067
theorem B12153125 : Blo 2247435 12153125 := bstep (se 4 (by rfl) ⟨1139355, by rfl⟩ : syracuseStep 12153125 = 2278711) B2278711
theorem B32408333 : Blo 2247435 32408333 := bstep (se 3 (by rfl) ⟨6076562, by rfl⟩ : syracuseStep 32408333 = 12153125) B12153125
theorem B21605555 : Blo 2247435 21605555 := bstep (se 1 (by rfl) ⟨16204166, by rfl⟩ : syracuseStep 21605555 = 32408333) B32408333
theorem B14403703 : Blo 2247435 14403703 := bstep (se 1 (by rfl) ⟨10802777, by rfl⟩ : syracuseStep 14403703 = 21605555) B21605555
theorem B19204937 : Blo 2247435 19204937 := bstep (se 2 (by rfl) ⟨7201851, by rfl⟩ : syracuseStep 19204937 = 14403703) B14403703
theorem B12803291 : Blo 2247435 12803291 := bstep (se 1 (by rfl) ⟨9602468, by rfl⟩ : syracuseStep 12803291 = 19204937) B19204937
theorem B8535527 : Blo 2247435 8535527 := bstep (se 1 (by rfl) ⟨6401645, by rfl⟩ : syracuseStep 8535527 = 12803291) B12803291
theorem B5690351 : Blo 2247435 5690351 := bstep (se 1 (by rfl) ⟨4267763, by rfl⟩ : syracuseStep 5690351 = 8535527) B8535527
theorem B3793567 : Blo 2247435 3793567 := bstep (se 1 (by rfl) ⟨2845175, by rfl⟩ : syracuseStep 3793567 = 5690351) B5690351
theorem B5058089 : Blo 2247435 5058089 := bstep (se 2 (by rfl) ⟨1896783, by rfl⟩ : syracuseStep 5058089 = 3793567) B3793567
theorem B3372059 : Blo 2247435 3372059 := bstep (se 1 (by rfl) ⟨2529044, by rfl⟩ : syracuseStep 3372059 = 5058089) B5058089
theorem B2248039 : Blo 2247435 2248039 := bstep (se 1 (by rfl) ⟨1686029, by rfl⟩ : syracuseStep 2248039 = 3372059) B3372059
theorem B2529049 : Blo 2247435 2529049 := bbase (se 2 (by rfl) ⟨948393, by rfl⟩ : syracuseStep 2529049 = 1896787) (by norm_num)
theorem B3372065 : Blo 2247435 3372065 := bstep (se 2 (by rfl) ⟨1264524, by rfl⟩ : syracuseStep 3372065 = 2529049) B2529049
theorem B2248043 : Blo 2247435 2248043 := bstep (se 1 (by rfl) ⟨1686032, by rfl⟩ : syracuseStep 2248043 = 3372065) B3372065
theorem B8535557 : Blo 2247435 8535557 := bbase (se 4 (by rfl) ⟨800208, by rfl⟩ : syracuseStep 8535557 = 1600417) (by norm_num)
theorem B5690371 : Blo 2247435 5690371 := bstep (se 1 (by rfl) ⟨4267778, by rfl⟩ : syracuseStep 5690371 = 8535557) B8535557
theorem B7587161 : Blo 2247435 7587161 := bstep (se 2 (by rfl) ⟨2845185, by rfl⟩ : syracuseStep 7587161 = 5690371) B5690371
theorem B5058107 : Blo 2247435 5058107 := bstep (se 1 (by rfl) ⟨3793580, by rfl⟩ : syracuseStep 5058107 = 7587161) B7587161
theorem B3372071 : Blo 2247435 3372071 := bstep (se 1 (by rfl) ⟨2529053, by rfl⟩ : syracuseStep 3372071 = 5058107) B5058107
theorem B2248047 : Blo 2247435 2248047 := bstep (se 1 (by rfl) ⟨1686035, by rfl⟩ : syracuseStep 2248047 = 3372071) B3372071
theorem B3372077 : Blo 2247435 3372077 := bbase (se 3 (by rfl) ⟨632264, by rfl⟩ : syracuseStep 3372077 = 1264529) (by norm_num)
theorem B2248051 : Blo 2247435 2248051 := bstep (se 1 (by rfl) ⟨1686038, by rfl⟩ : syracuseStep 2248051 = 3372077) B3372077
theorem B5058125 : Blo 2247435 5058125 := bbase (se 3 (by rfl) ⟨948398, by rfl⟩ : syracuseStep 5058125 = 1896797) (by norm_num)
theorem B3372083 : Blo 2247435 3372083 := bstep (se 1 (by rfl) ⟨2529062, by rfl⟩ : syracuseStep 3372083 = 5058125) B5058125
theorem B2248055 : Blo 2247435 2248055 := bstep (se 1 (by rfl) ⟨1686041, by rfl⟩ : syracuseStep 2248055 = 3372083) B3372083
theorem B2845201 : Blo 2247435 2845201 := bbase (se 2 (by rfl) ⟨1066950, by rfl⟩ : syracuseStep 2845201 = 2133901) (by norm_num)
theorem B3793601 : Blo 2247435 3793601 := bstep (se 2 (by rfl) ⟨1422600, by rfl⟩ : syracuseStep 3793601 = 2845201) B2845201
theorem B2529067 : Blo 2247435 2529067 := bstep (se 1 (by rfl) ⟨1896800, by rfl⟩ : syracuseStep 2529067 = 3793601) B3793601
theorem B3372089 : Blo 2247435 3372089 := bstep (se 2 (by rfl) ⟨1264533, by rfl⟩ : syracuseStep 3372089 = 2529067) B2529067
theorem B2248059 : Blo 2247435 2248059 := bstep (se 1 (by rfl) ⟨1686044, by rfl⟩ : syracuseStep 2248059 = 3372089) B3372089
theorem B4801285 : Blo 2247435 4801285 := bbase (se 4 (by rfl) ⟨450120, by rfl⟩ : syracuseStep 4801285 = 900241) (by norm_num)
theorem B25606853 : Blo 2247435 25606853 := bstep (se 4 (by rfl) ⟨2400642, by rfl⟩ : syracuseStep 25606853 = 4801285) B4801285
theorem B17071235 : Blo 2247435 17071235 := bstep (se 1 (by rfl) ⟨12803426, by rfl⟩ : syracuseStep 17071235 = 25606853) B25606853
theorem B11380823 : Blo 2247435 11380823 := bstep (se 1 (by rfl) ⟨8535617, by rfl⟩ : syracuseStep 11380823 = 17071235) B17071235
theorem B7587215 : Blo 2247435 7587215 := bstep (se 1 (by rfl) ⟨5690411, by rfl⟩ : syracuseStep 7587215 = 11380823) B11380823
theorem B5058143 : Blo 2247435 5058143 := bstep (se 1 (by rfl) ⟨3793607, by rfl⟩ : syracuseStep 5058143 = 7587215) B7587215
theorem B3372095 : Blo 2247435 3372095 := bstep (se 1 (by rfl) ⟨2529071, by rfl⟩ : syracuseStep 3372095 = 5058143) B5058143
theorem B2248063 : Blo 2247435 2248063 := bstep (se 1 (by rfl) ⟨1686047, by rfl⟩ : syracuseStep 2248063 = 3372095) B3372095
theorem B3372101 : Blo 2247435 3372101 := bbase (se 4 (by rfl) ⟨316134, by rfl⟩ : syracuseStep 3372101 = 632269) (by norm_num)
theorem B2248067 : Blo 2247435 2248067 := bstep (se 1 (by rfl) ⟨1686050, by rfl⟩ : syracuseStep 2248067 = 3372101) B3372101
theorem B3793621 : Blo 2247435 3793621 := bbase (se 7 (by rfl) ⟨44456, by rfl⟩ : syracuseStep 3793621 = 88913) (by norm_num)
theorem B5058161 : Blo 2247435 5058161 := bstep (se 2 (by rfl) ⟨1896810, by rfl⟩ : syracuseStep 5058161 = 3793621) B3793621
theorem B3372107 : Blo 2247435 3372107 := bstep (se 1 (by rfl) ⟨2529080, by rfl⟩ : syracuseStep 3372107 = 5058161) B5058161
theorem B2248071 : Blo 2247435 2248071 := bstep (se 1 (by rfl) ⟨1686053, by rfl⟩ : syracuseStep 2248071 = 3372107) B3372107
theorem B2529085 : Blo 2247435 2529085 := bbase (se 3 (by rfl) ⟨474203, by rfl⟩ : syracuseStep 2529085 = 948407) (by norm_num)
theorem B3372113 : Blo 2247435 3372113 := bstep (se 2 (by rfl) ⟨1264542, by rfl⟩ : syracuseStep 3372113 = 2529085) B2529085
theorem B2248075 : Blo 2247435 2248075 := bstep (se 1 (by rfl) ⟨1686056, by rfl⟩ : syracuseStep 2248075 = 3372113) B3372113
theorem B7587269 : Blo 2247435 7587269 := bbase (se 4 (by rfl) ⟨711306, by rfl⟩ : syracuseStep 7587269 = 1422613) (by norm_num)
theorem B5058179 : Blo 2247435 5058179 := bstep (se 1 (by rfl) ⟨3793634, by rfl⟩ : syracuseStep 5058179 = 7587269) B7587269
theorem B3372119 : Blo 2247435 3372119 := bstep (se 1 (by rfl) ⟨2529089, by rfl⟩ : syracuseStep 3372119 = 5058179) B5058179
theorem B2248079 : Blo 2247435 2248079 := bstep (se 1 (by rfl) ⟨1686059, by rfl⟩ : syracuseStep 2248079 = 3372119) B3372119
theorem B3372125 : Blo 2247435 3372125 := bbase (se 3 (by rfl) ⟨632273, by rfl⟩ : syracuseStep 3372125 = 1264547) (by norm_num)
theorem B2248083 : Blo 2247435 2248083 := bstep (se 1 (by rfl) ⟨1686062, by rfl⟩ : syracuseStep 2248083 = 3372125) B3372125
theorem B5058197 : Blo 2247435 5058197 := bbase (se 6 (by rfl) ⟨118551, by rfl⟩ : syracuseStep 5058197 = 237103) (by norm_num)
theorem B3372131 : Blo 2247435 3372131 := bstep (se 1 (by rfl) ⟨2529098, by rfl⟩ : syracuseStep 3372131 = 5058197) B5058197
theorem B2248087 : Blo 2247435 2248087 := bstep (se 1 (by rfl) ⟨1686065, by rfl⟩ : syracuseStep 2248087 = 3372131) B3372131
theorem B2400673 : Blo 2247435 2400673 := bbase (se 2 (by rfl) ⟨900252, by rfl⟩ : syracuseStep 2400673 = 1800505) (by norm_num)
theorem B3200897 : Blo 2247435 3200897 := bstep (se 2 (by rfl) ⟨1200336, by rfl⟩ : syracuseStep 3200897 = 2400673) B2400673
theorem B8535725 : Blo 2247435 8535725 := bstep (se 3 (by rfl) ⟨1600448, by rfl⟩ : syracuseStep 8535725 = 3200897) B3200897
theorem B5690483 : Blo 2247435 5690483 := bstep (se 1 (by rfl) ⟨4267862, by rfl⟩ : syracuseStep 5690483 = 8535725) B8535725
theorem B3793655 : Blo 2247435 3793655 := bstep (se 1 (by rfl) ⟨2845241, by rfl⟩ : syracuseStep 3793655 = 5690483) B5690483
theorem B2529103 : Blo 2247435 2529103 := bstep (se 1 (by rfl) ⟨1896827, by rfl⟩ : syracuseStep 2529103 = 3793655) B3793655
theorem B3372137 : Blo 2247435 3372137 := bstep (se 2 (by rfl) ⟨1264551, by rfl⟩ : syracuseStep 3372137 = 2529103) B2529103
theorem B2248091 : Blo 2247435 2248091 := bstep (se 1 (by rfl) ⟨1686068, by rfl⟩ : syracuseStep 2248091 = 3372137) B3372137
theorem B3038357 : Blo 2247435 3038357 := bbase (se 6 (by rfl) ⟨71211, by rfl⟩ : syracuseStep 3038357 = 142423) (by norm_num)
theorem B8102285 : Blo 2247435 8102285 := bstep (se 3 (by rfl) ⟨1519178, by rfl⟩ : syracuseStep 8102285 = 3038357) B3038357
theorem B5401523 : Blo 2247435 5401523 := bstep (se 1 (by rfl) ⟨4051142, by rfl⟩ : syracuseStep 5401523 = 8102285) B8102285
theorem B14404061 : Blo 2247435 14404061 := bstep (se 3 (by rfl) ⟨2700761, by rfl⟩ : syracuseStep 14404061 = 5401523) B5401523
theorem B9602707 : Blo 2247435 9602707 := bstep (se 1 (by rfl) ⟨7202030, by rfl⟩ : syracuseStep 9602707 = 14404061) B14404061
theorem B12803609 : Blo 2247435 12803609 := bstep (se 2 (by rfl) ⟨4801353, by rfl⟩ : syracuseStep 12803609 = 9602707) B9602707
theorem B8535739 : Blo 2247435 8535739 := bstep (se 1 (by rfl) ⟨6401804, by rfl⟩ : syracuseStep 8535739 = 12803609) B12803609
theorem B11380985 : Blo 2247435 11380985 := bstep (se 2 (by rfl) ⟨4267869, by rfl⟩ : syracuseStep 11380985 = 8535739) B8535739
theorem B7587323 : Blo 2247435 7587323 := bstep (se 1 (by rfl) ⟨5690492, by rfl⟩ : syracuseStep 7587323 = 11380985) B11380985
theorem B5058215 : Blo 2247435 5058215 := bstep (se 1 (by rfl) ⟨3793661, by rfl⟩ : syracuseStep 5058215 = 7587323) B7587323
theorem B3372143 : Blo 2247435 3372143 := bstep (se 1 (by rfl) ⟨2529107, by rfl⟩ : syracuseStep 3372143 = 5058215) B5058215
theorem B2248095 : Blo 2247435 2248095 := bstep (se 1 (by rfl) ⟨1686071, by rfl⟩ : syracuseStep 2248095 = 3372143) B3372143
theorem B3372149 : Blo 2247435 3372149 := bbase (se 5 (by rfl) ⟨158069, by rfl⟩ : syracuseStep 3372149 = 316139) (by norm_num)
theorem B2248099 : Blo 2247435 2248099 := bstep (se 1 (by rfl) ⟨1686074, by rfl⟩ : syracuseStep 2248099 = 3372149) B3372149
theorem B4267885 : Blo 2247435 4267885 := bbase (se 3 (by rfl) ⟨800228, by rfl⟩ : syracuseStep 4267885 = 1600457) (by norm_num)
theorem B5690513 : Blo 2247435 5690513 := bstep (se 2 (by rfl) ⟨2133942, by rfl⟩ : syracuseStep 5690513 = 4267885) B4267885
theorem B3793675 : Blo 2247435 3793675 := bstep (se 1 (by rfl) ⟨2845256, by rfl⟩ : syracuseStep 3793675 = 5690513) B5690513
theorem B5058233 : Blo 2247435 5058233 := bstep (se 2 (by rfl) ⟨1896837, by rfl⟩ : syracuseStep 5058233 = 3793675) B3793675
theorem B3372155 : Blo 2247435 3372155 := bstep (se 1 (by rfl) ⟨2529116, by rfl⟩ : syracuseStep 3372155 = 5058233) B5058233
theorem B2248103 : Blo 2247435 2248103 := bstep (se 1 (by rfl) ⟨1686077, by rfl⟩ : syracuseStep 2248103 = 3372155) B3372155
theorem B2529121 : Blo 2247435 2529121 := bbase (se 2 (by rfl) ⟨948420, by rfl⟩ : syracuseStep 2529121 = 1896841) (by norm_num)
theorem B3372161 : Blo 2247435 3372161 := bstep (se 2 (by rfl) ⟨1264560, by rfl⟩ : syracuseStep 3372161 = 2529121) B2529121
theorem B2248107 : Blo 2247435 2248107 := bstep (se 1 (by rfl) ⟨1686080, by rfl⟩ : syracuseStep 2248107 = 3372161) B3372161
theorem B5690533 : Blo 2247435 5690533 := bbase (se 4 (by rfl) ⟨533487, by rfl⟩ : syracuseStep 5690533 = 1066975) (by norm_num)
theorem B7587377 : Blo 2247435 7587377 := bstep (se 2 (by rfl) ⟨2845266, by rfl⟩ : syracuseStep 7587377 = 5690533) B5690533
theorem B5058251 : Blo 2247435 5058251 := bstep (se 1 (by rfl) ⟨3793688, by rfl⟩ : syracuseStep 5058251 = 7587377) B7587377
theorem B3372167 : Blo 2247435 3372167 := bstep (se 1 (by rfl) ⟨2529125, by rfl⟩ : syracuseStep 3372167 = 5058251) B5058251
theorem B2248111 : Blo 2247435 2248111 := bstep (se 1 (by rfl) ⟨1686083, by rfl⟩ : syracuseStep 2248111 = 3372167) B3372167
theorem B3372173 : Blo 2247435 3372173 := bbase (se 3 (by rfl) ⟨632282, by rfl⟩ : syracuseStep 3372173 = 1264565) (by norm_num)
theorem B2248115 : Blo 2247435 2248115 := bstep (se 1 (by rfl) ⟨1686086, by rfl⟩ : syracuseStep 2248115 = 3372173) B3372173
theorem B5058269 : Blo 2247435 5058269 := bbase (se 3 (by rfl) ⟨948425, by rfl⟩ : syracuseStep 5058269 = 1896851) (by norm_num)
theorem B3372179 : Blo 2247435 3372179 := bstep (se 1 (by rfl) ⟨2529134, by rfl⟩ : syracuseStep 3372179 = 5058269) B5058269
theorem B2248119 : Blo 2247435 2248119 := bstep (se 1 (by rfl) ⟨1686089, by rfl⟩ : syracuseStep 2248119 = 3372179) B3372179
theorem B3793709 : Blo 2247435 3793709 := bbase (se 3 (by rfl) ⟨711320, by rfl⟩ : syracuseStep 3793709 = 1422641) (by norm_num)
theorem B2529139 : Blo 2247435 2529139 := bstep (se 1 (by rfl) ⟨1896854, by rfl⟩ : syracuseStep 2529139 = 3793709) B3793709
theorem B3372185 : Blo 2247435 3372185 := bstep (se 2 (by rfl) ⟨1264569, by rfl⟩ : syracuseStep 3372185 = 2529139) B2529139
theorem B2248123 : Blo 2247435 2248123 := bstep (se 1 (by rfl) ⟨1686092, by rfl⟩ : syracuseStep 2248123 = 3372185) B3372185
theorem B2341405 : Blo 2247435 2341405 := bbase (se 3 (by rfl) ⟨439013, by rfl⟩ : syracuseStep 2341405 = 878027) (by norm_num)
theorem B12487493 : Blo 2247435 12487493 := bstep (se 4 (by rfl) ⟨1170702, by rfl⟩ : syracuseStep 12487493 = 2341405) B2341405
theorem B8324995 : Blo 2247435 8324995 := bstep (se 1 (by rfl) ⟨6243746, by rfl⟩ : syracuseStep 8324995 = 12487493) B12487493
theorem B11099993 : Blo 2247435 11099993 := bstep (se 2 (by rfl) ⟨4162497, by rfl⟩ : syracuseStep 11099993 = 8324995) B8324995
theorem B29599981 : Blo 2247435 29599981 := bstep (se 3 (by rfl) ⟨5549996, by rfl⟩ : syracuseStep 29599981 = 11099993) B11099993
theorem B157866565 : Blo 2247435 157866565 := bstep (se 4 (by rfl) ⟨14799990, by rfl⟩ : syracuseStep 157866565 = 29599981) B29599981
theorem B210488753 : Blo 2247435 210488753 := bstep (se 2 (by rfl) ⟨78933282, by rfl⟩ : syracuseStep 210488753 = 157866565) B157866565
theorem B561303341 : Blo 2247435 561303341 := bstep (se 3 (by rfl) ⟨105244376, by rfl⟩ : syracuseStep 561303341 = 210488753) B210488753
theorem B374202227 : Blo 2247435 374202227 := bstep (se 1 (by rfl) ⟨280651670, by rfl⟩ : syracuseStep 374202227 = 561303341) B561303341
theorem B997872605 : Blo 2247435 997872605 := bstep (se 3 (by rfl) ⟨187101113, by rfl⟩ : syracuseStep 997872605 = 374202227) B374202227
theorem B665248403 : Blo 2247435 665248403 := bstep (se 1 (by rfl) ⟨498936302, by rfl⟩ : syracuseStep 665248403 = 997872605) B997872605
theorem B443498935 : Blo 2247435 443498935 := bstep (se 1 (by rfl) ⟨332624201, by rfl⟩ : syracuseStep 443498935 = 665248403) B665248403
theorem B591331913 : Blo 2247435 591331913 := bstep (se 2 (by rfl) ⟨221749467, by rfl⟩ : syracuseStep 591331913 = 443498935) B443498935
theorem B394221275 : Blo 2247435 394221275 := bstep (se 1 (by rfl) ⟨295665956, by rfl⟩ : syracuseStep 394221275 = 591331913) B591331913
theorem B262814183 : Blo 2247435 262814183 := bstep (se 1 (by rfl) ⟨197110637, by rfl⟩ : syracuseStep 262814183 = 394221275) B394221275
theorem B175209455 : Blo 2247435 175209455 := bstep (se 1 (by rfl) ⟨131407091, by rfl⟩ : syracuseStep 175209455 = 262814183) B262814183
theorem B116806303 : Blo 2247435 116806303 := bstep (se 1 (by rfl) ⟨87604727, by rfl⟩ : syracuseStep 116806303 = 175209455) B175209455
theorem B622966949 : Blo 2247435 622966949 := bstep (se 4 (by rfl) ⟨58403151, by rfl⟩ : syracuseStep 622966949 = 116806303) B116806303
theorem B415311299 : Blo 2247435 415311299 := bstep (se 1 (by rfl) ⟨311483474, by rfl⟩ : syracuseStep 415311299 = 622966949) B622966949
theorem B276874199 : Blo 2247435 276874199 := bstep (se 1 (by rfl) ⟨207655649, by rfl⟩ : syracuseStep 276874199 = 415311299) B415311299
theorem B184582799 : Blo 2247435 184582799 := bstep (se 1 (by rfl) ⟨138437099, by rfl⟩ : syracuseStep 184582799 = 276874199) B276874199
theorem B123055199 : Blo 2247435 123055199 := bstep (se 1 (by rfl) ⟨92291399, by rfl⟩ : syracuseStep 123055199 = 184582799) B184582799
theorem B82036799 : Blo 2247435 82036799 := bstep (se 1 (by rfl) ⟨61527599, by rfl⟩ : syracuseStep 82036799 = 123055199) B123055199
theorem B54691199 : Blo 2247435 54691199 := bstep (se 1 (by rfl) ⟨41018399, by rfl⟩ : syracuseStep 54691199 = 82036799) B82036799
theorem B36460799 : Blo 2247435 36460799 := bstep (se 1 (by rfl) ⟨27345599, by rfl⟩ : syracuseStep 36460799 = 54691199) B54691199
theorem B24307199 : Blo 2247435 24307199 := bstep (se 1 (by rfl) ⟨18230399, by rfl⟩ : syracuseStep 24307199 = 36460799) B36460799
theorem B16204799 : Blo 2247435 16204799 := bstep (se 1 (by rfl) ⟨12153599, by rfl⟩ : syracuseStep 16204799 = 24307199) B24307199
theorem B43212797 : Blo 2247435 43212797 := bstep (se 3 (by rfl) ⟨8102399, by rfl⟩ : syracuseStep 43212797 = 16204799) B16204799
theorem B28808531 : Blo 2247435 28808531 := bstep (se 1 (by rfl) ⟨21606398, by rfl⟩ : syracuseStep 28808531 = 43212797) B43212797
theorem B19205687 : Blo 2247435 19205687 := bstep (se 1 (by rfl) ⟨14404265, by rfl⟩ : syracuseStep 19205687 = 28808531) B28808531
theorem B12803791 : Blo 2247435 12803791 := bstep (se 1 (by rfl) ⟨9602843, by rfl⟩ : syracuseStep 12803791 = 19205687) B19205687
theorem B17071721 : Blo 2247435 17071721 := bstep (se 2 (by rfl) ⟨6401895, by rfl⟩ : syracuseStep 17071721 = 12803791) B12803791
theorem B11381147 : Blo 2247435 11381147 := bstep (se 1 (by rfl) ⟨8535860, by rfl⟩ : syracuseStep 11381147 = 17071721) B17071721
theorem B7587431 : Blo 2247435 7587431 := bstep (se 1 (by rfl) ⟨5690573, by rfl⟩ : syracuseStep 7587431 = 11381147) B11381147
theorem B5058287 : Blo 2247435 5058287 := bstep (se 1 (by rfl) ⟨3793715, by rfl⟩ : syracuseStep 5058287 = 7587431) B7587431
theorem B3372191 : Blo 2247435 3372191 := bstep (se 1 (by rfl) ⟨2529143, by rfl⟩ : syracuseStep 3372191 = 5058287) B5058287
theorem B2248127 : Blo 2247435 2248127 := bstep (se 1 (by rfl) ⟨1686095, by rfl⟩ : syracuseStep 2248127 = 3372191) B3372191
theorem B3372197 : Blo 2247435 3372197 := bbase (se 4 (by rfl) ⟨316143, by rfl⟩ : syracuseStep 3372197 = 632287) (by norm_num)
theorem B2248131 : Blo 2247435 2248131 := bstep (se 1 (by rfl) ⟨1686098, by rfl⟩ : syracuseStep 2248131 = 3372197) B3372197
theorem B2845297 : Blo 2247435 2845297 := bbase (se 2 (by rfl) ⟨1066986, by rfl⟩ : syracuseStep 2845297 = 2133973) (by norm_num)
theorem B3793729 : Blo 2247435 3793729 := bstep (se 2 (by rfl) ⟨1422648, by rfl⟩ : syracuseStep 3793729 = 2845297) B2845297
theorem B5058305 : Blo 2247435 5058305 := bstep (se 2 (by rfl) ⟨1896864, by rfl⟩ : syracuseStep 5058305 = 3793729) B3793729
theorem B3372203 : Blo 2247435 3372203 := bstep (se 1 (by rfl) ⟨2529152, by rfl⟩ : syracuseStep 3372203 = 5058305) B5058305
theorem B2248135 : Blo 2247435 2248135 := bstep (se 1 (by rfl) ⟨1686101, by rfl⟩ : syracuseStep 2248135 = 3372203) B3372203
theorem B2529157 : Blo 2247435 2529157 := bbase (se 4 (by rfl) ⟨237108, by rfl⟩ : syracuseStep 2529157 = 474217) (by norm_num)
theorem B3372209 : Blo 2247435 3372209 := bstep (se 2 (by rfl) ⟨1264578, by rfl⟩ : syracuseStep 3372209 = 2529157) B2529157
theorem B2248139 : Blo 2247435 2248139 := bstep (se 1 (by rfl) ⟨1686104, by rfl⟩ : syracuseStep 2248139 = 3372209) B3372209
theorem B3601093 : Blo 2247435 3601093 := bbase (se 4 (by rfl) ⟨337602, by rfl⟩ : syracuseStep 3601093 = 675205) (by norm_num)
theorem B4801457 : Blo 2247435 4801457 := bstep (se 2 (by rfl) ⟨1800546, by rfl⟩ : syracuseStep 4801457 = 3601093) B3601093
theorem B3200971 : Blo 2247435 3200971 := bstep (se 1 (by rfl) ⟨2400728, by rfl⟩ : syracuseStep 3200971 = 4801457) B4801457
theorem B4267961 : Blo 2247435 4267961 := bstep (se 2 (by rfl) ⟨1600485, by rfl⟩ : syracuseStep 4267961 = 3200971) B3200971
theorem B2845307 : Blo 2247435 2845307 := bstep (se 1 (by rfl) ⟨2133980, by rfl⟩ : syracuseStep 2845307 = 4267961) B4267961
theorem B7587485 : Blo 2247435 7587485 := bstep (se 3 (by rfl) ⟨1422653, by rfl⟩ : syracuseStep 7587485 = 2845307) B2845307
theorem B5058323 : Blo 2247435 5058323 := bstep (se 1 (by rfl) ⟨3793742, by rfl⟩ : syracuseStep 5058323 = 7587485) B7587485
theorem B3372215 : Blo 2247435 3372215 := bstep (se 1 (by rfl) ⟨2529161, by rfl⟩ : syracuseStep 3372215 = 5058323) B5058323
theorem B2248143 : Blo 2247435 2248143 := bstep (se 1 (by rfl) ⟨1686107, by rfl⟩ : syracuseStep 2248143 = 3372215) B3372215
theorem B3372221 : Blo 2247435 3372221 := bbase (se 3 (by rfl) ⟨632291, by rfl⟩ : syracuseStep 3372221 = 1264583) (by norm_num)
theorem B2248147 : Blo 2247435 2248147 := bstep (se 1 (by rfl) ⟨1686110, by rfl⟩ : syracuseStep 2248147 = 3372221) B3372221
theorem B5058341 : Blo 2247435 5058341 := bbase (se 4 (by rfl) ⟨474219, by rfl⟩ : syracuseStep 5058341 = 948439) (by norm_num)
theorem B3372227 : Blo 2247435 3372227 := bstep (se 1 (by rfl) ⟨2529170, by rfl⟩ : syracuseStep 3372227 = 5058341) B5058341
theorem B2248151 : Blo 2247435 2248151 := bstep (se 1 (by rfl) ⟨1686113, by rfl⟩ : syracuseStep 2248151 = 3372227) B3372227
theorem B5690645 : Blo 2247435 5690645 := bbase (se 6 (by rfl) ⟨133374, by rfl⟩ : syracuseStep 5690645 = 266749) (by norm_num)
theorem B3793763 : Blo 2247435 3793763 := bstep (se 1 (by rfl) ⟨2845322, by rfl⟩ : syracuseStep 3793763 = 5690645) B5690645
theorem B2529175 : Blo 2247435 2529175 := bstep (se 1 (by rfl) ⟨1896881, by rfl⟩ : syracuseStep 2529175 = 3793763) B3793763
theorem B3372233 : Blo 2247435 3372233 := bstep (se 2 (by rfl) ⟨1264587, by rfl⟩ : syracuseStep 3372233 = 2529175) B2529175
theorem B2248155 : Blo 2247435 2248155 := bstep (se 1 (by rfl) ⟨1686116, by rfl⟩ : syracuseStep 2248155 = 3372233) B3372233
theorem B9602981 : Blo 2247435 9602981 := bbase (se 4 (by rfl) ⟨900279, by rfl⟩ : syracuseStep 9602981 = 1800559) (by norm_num)
theorem B6401987 : Blo 2247435 6401987 := bstep (se 1 (by rfl) ⟨4801490, by rfl⟩ : syracuseStep 6401987 = 9602981) B9602981
theorem B4267991 : Blo 2247435 4267991 := bstep (se 1 (by rfl) ⟨3200993, by rfl⟩ : syracuseStep 4267991 = 6401987) B6401987
theorem B11381309 : Blo 2247435 11381309 := bstep (se 3 (by rfl) ⟨2133995, by rfl⟩ : syracuseStep 11381309 = 4267991) B4267991
theorem B7587539 : Blo 2247435 7587539 := bstep (se 1 (by rfl) ⟨5690654, by rfl⟩ : syracuseStep 7587539 = 11381309) B11381309
theorem B5058359 : Blo 2247435 5058359 := bstep (se 1 (by rfl) ⟨3793769, by rfl⟩ : syracuseStep 5058359 = 7587539) B7587539
theorem B3372239 : Blo 2247435 3372239 := bstep (se 1 (by rfl) ⟨2529179, by rfl⟩ : syracuseStep 3372239 = 5058359) B5058359
theorem B2248159 : Blo 2247435 2248159 := bstep (se 1 (by rfl) ⟨1686119, by rfl⟩ : syracuseStep 2248159 = 3372239) B3372239
theorem B3372245 : Blo 2247435 3372245 := bbase (se 7 (by rfl) ⟨39518, by rfl⟩ : syracuseStep 3372245 = 79037) (by norm_num)
theorem B2248163 : Blo 2247435 2248163 := bstep (se 1 (by rfl) ⟨1686122, by rfl⟩ : syracuseStep 2248163 = 3372245) B3372245
theorem B3201005 : Blo 2247435 3201005 := bbase (se 3 (by rfl) ⟨600188, by rfl⟩ : syracuseStep 3201005 = 1200377) (by norm_num)
theorem B8536013 : Blo 2247435 8536013 := bstep (se 3 (by rfl) ⟨1600502, by rfl⟩ : syracuseStep 8536013 = 3201005) B3201005
theorem B5690675 : Blo 2247435 5690675 := bstep (se 1 (by rfl) ⟨4268006, by rfl⟩ : syracuseStep 5690675 = 8536013) B8536013
theorem B3793783 : Blo 2247435 3793783 := bstep (se 1 (by rfl) ⟨2845337, by rfl⟩ : syracuseStep 3793783 = 5690675) B5690675
theorem B5058377 : Blo 2247435 5058377 := bstep (se 2 (by rfl) ⟨1896891, by rfl⟩ : syracuseStep 5058377 = 3793783) B3793783
theorem B3372251 : Blo 2247435 3372251 := bstep (se 1 (by rfl) ⟨2529188, by rfl⟩ : syracuseStep 3372251 = 5058377) B5058377
theorem B2248167 : Blo 2247435 2248167 := bstep (se 1 (by rfl) ⟨1686125, by rfl⟩ : syracuseStep 2248167 = 3372251) B3372251
theorem B2529193 : Blo 2247435 2529193 := bbase (se 2 (by rfl) ⟨948447, by rfl⟩ : syracuseStep 2529193 = 1896895) (by norm_num)
theorem B3372257 : Blo 2247435 3372257 := bstep (se 2 (by rfl) ⟨1264596, by rfl⟩ : syracuseStep 3372257 = 2529193) B2529193
theorem B2248171 : Blo 2247435 2248171 := bstep (se 1 (by rfl) ⟨1686128, by rfl⟩ : syracuseStep 2248171 = 3372257) B3372257
theorem B9734069 : Blo 2247435 9734069 := bbase (se 5 (by rfl) ⟨456284, by rfl⟩ : syracuseStep 9734069 = 912569) (by norm_num)
theorem B6489379 : Blo 2247435 6489379 := bstep (se 1 (by rfl) ⟨4867034, by rfl⟩ : syracuseStep 6489379 = 9734069) B9734069
theorem B8652505 : Blo 2247435 8652505 := bstep (se 2 (by rfl) ⟨3244689, by rfl⟩ : syracuseStep 8652505 = 6489379) B6489379
theorem B11536673 : Blo 2247435 11536673 := bstep (se 2 (by rfl) ⟨4326252, by rfl⟩ : syracuseStep 11536673 = 8652505) B8652505
theorem B30764461 : Blo 2247435 30764461 := bstep (se 3 (by rfl) ⟨5768336, by rfl⟩ : syracuseStep 30764461 = 11536673) B11536673
theorem B41019281 : Blo 2247435 41019281 := bstep (se 2 (by rfl) ⟨15382230, by rfl⟩ : syracuseStep 41019281 = 30764461) B30764461
theorem B27346187 : Blo 2247435 27346187 := bstep (se 1 (by rfl) ⟨20509640, by rfl⟩ : syracuseStep 27346187 = 41019281) B41019281
theorem B18230791 : Blo 2247435 18230791 := bstep (se 1 (by rfl) ⟨13673093, by rfl⟩ : syracuseStep 18230791 = 27346187) B27346187
theorem B24307721 : Blo 2247435 24307721 := bstep (se 2 (by rfl) ⟨9115395, by rfl⟩ : syracuseStep 24307721 = 18230791) B18230791
theorem B16205147 : Blo 2247435 16205147 := bstep (se 1 (by rfl) ⟨12153860, by rfl⟩ : syracuseStep 16205147 = 24307721) B24307721
theorem B10803431 : Blo 2247435 10803431 := bstep (se 1 (by rfl) ⟨8102573, by rfl⟩ : syracuseStep 10803431 = 16205147) B16205147
theorem B7202287 : Blo 2247435 7202287 := bstep (se 1 (by rfl) ⟨5401715, by rfl⟩ : syracuseStep 7202287 = 10803431) B10803431
theorem B9603049 : Blo 2247435 9603049 := bstep (se 2 (by rfl) ⟨3601143, by rfl⟩ : syracuseStep 9603049 = 7202287) B7202287
theorem B12804065 : Blo 2247435 12804065 := bstep (se 2 (by rfl) ⟨4801524, by rfl⟩ : syracuseStep 12804065 = 9603049) B9603049
theorem B8536043 : Blo 2247435 8536043 := bstep (se 1 (by rfl) ⟨6402032, by rfl⟩ : syracuseStep 8536043 = 12804065) B12804065
theorem B5690695 : Blo 2247435 5690695 := bstep (se 1 (by rfl) ⟨4268021, by rfl⟩ : syracuseStep 5690695 = 8536043) B8536043
theorem B7587593 : Blo 2247435 7587593 := bstep (se 2 (by rfl) ⟨2845347, by rfl⟩ : syracuseStep 7587593 = 5690695) B5690695
theorem B5058395 : Blo 2247435 5058395 := bstep (se 1 (by rfl) ⟨3793796, by rfl⟩ : syracuseStep 5058395 = 7587593) B7587593
theorem B3372263 : Blo 2247435 3372263 := bstep (se 1 (by rfl) ⟨2529197, by rfl⟩ : syracuseStep 3372263 = 5058395) B5058395
theorem B2248175 : Blo 2247435 2248175 := bstep (se 1 (by rfl) ⟨1686131, by rfl⟩ : syracuseStep 2248175 = 3372263) B3372263
theorem B3372269 : Blo 2247435 3372269 := bbase (se 3 (by rfl) ⟨632300, by rfl⟩ : syracuseStep 3372269 = 1264601) (by norm_num)
theorem B2248179 : Blo 2247435 2248179 := bstep (se 1 (by rfl) ⟨1686134, by rfl⟩ : syracuseStep 2248179 = 3372269) B3372269
theorem B5058413 : Blo 2247435 5058413 := bbase (se 3 (by rfl) ⟨948452, by rfl⟩ : syracuseStep 5058413 = 1896905) (by norm_num)
theorem B3372275 : Blo 2247435 3372275 := bstep (se 1 (by rfl) ⟨2529206, by rfl⟩ : syracuseStep 3372275 = 5058413) B5058413
theorem B2248183 : Blo 2247435 2248183 := bstep (se 1 (by rfl) ⟨1686137, by rfl⟩ : syracuseStep 2248183 = 3372275) B3372275
theorem B4268045 : Blo 2247435 4268045 := bbase (se 3 (by rfl) ⟨800258, by rfl⟩ : syracuseStep 4268045 = 1600517) (by norm_num)
theorem B2845363 : Blo 2247435 2845363 := bstep (se 1 (by rfl) ⟨2134022, by rfl⟩ : syracuseStep 2845363 = 4268045) B4268045
theorem B3793817 : Blo 2247435 3793817 := bstep (se 2 (by rfl) ⟨1422681, by rfl⟩ : syracuseStep 3793817 = 2845363) B2845363
theorem B2529211 : Blo 2247435 2529211 := bstep (se 1 (by rfl) ⟨1896908, by rfl⟩ : syracuseStep 2529211 = 3793817) B3793817
theorem B3372281 : Blo 2247435 3372281 := bstep (se 2 (by rfl) ⟨1264605, by rfl⟩ : syracuseStep 3372281 = 2529211) B2529211
theorem B2248187 : Blo 2247435 2248187 := bstep (se 1 (by rfl) ⟨1686140, by rfl⟩ : syracuseStep 2248187 = 3372281) B3372281
theorem B2278865 : Blo 2247435 2278865 := bbase (se 2 (by rfl) ⟨854574, by rfl⟩ : syracuseStep 2278865 = 1709149) (by norm_num)
theorem B6076973 : Blo 2247435 6076973 := bstep (se 3 (by rfl) ⟨1139432, by rfl⟩ : syracuseStep 6076973 = 2278865) B2278865
theorem B4051315 : Blo 2247435 4051315 := bstep (se 1 (by rfl) ⟨3038486, by rfl⟩ : syracuseStep 4051315 = 6076973) B6076973
theorem B21607013 : Blo 2247435 21607013 := bstep (se 4 (by rfl) ⟨2025657, by rfl⟩ : syracuseStep 21607013 = 4051315) B4051315
theorem B57618701 : Blo 2247435 57618701 := bstep (se 3 (by rfl) ⟨10803506, by rfl⟩ : syracuseStep 57618701 = 21607013) B21607013
theorem B38412467 : Blo 2247435 38412467 := bstep (se 1 (by rfl) ⟨28809350, by rfl⟩ : syracuseStep 38412467 = 57618701) B57618701
theorem B25608311 : Blo 2247435 25608311 := bstep (se 1 (by rfl) ⟨19206233, by rfl⟩ : syracuseStep 25608311 = 38412467) B38412467
theorem B17072207 : Blo 2247435 17072207 := bstep (se 1 (by rfl) ⟨12804155, by rfl⟩ : syracuseStep 17072207 = 25608311) B25608311
theorem B11381471 : Blo 2247435 11381471 := bstep (se 1 (by rfl) ⟨8536103, by rfl⟩ : syracuseStep 11381471 = 17072207) B17072207
theorem B7587647 : Blo 2247435 7587647 := bstep (se 1 (by rfl) ⟨5690735, by rfl⟩ : syracuseStep 7587647 = 11381471) B11381471
theorem B5058431 : Blo 2247435 5058431 := bstep (se 1 (by rfl) ⟨3793823, by rfl⟩ : syracuseStep 5058431 = 7587647) B7587647
theorem B3372287 : Blo 2247435 3372287 := bstep (se 1 (by rfl) ⟨2529215, by rfl⟩ : syracuseStep 3372287 = 5058431) B5058431
theorem B2248191 : Blo 2247435 2248191 := bstep (se 1 (by rfl) ⟨1686143, by rfl⟩ : syracuseStep 2248191 = 3372287) B3372287
theorem B3372293 : Blo 2247435 3372293 := bbase (se 4 (by rfl) ⟨316152, by rfl⟩ : syracuseStep 3372293 = 632305) (by norm_num)
theorem B2248195 : Blo 2247435 2248195 := bstep (se 1 (by rfl) ⟨1686146, by rfl⟩ : syracuseStep 2248195 = 3372293) B3372293
theorem B3793837 : Blo 2247435 3793837 := bbase (se 3 (by rfl) ⟨711344, by rfl⟩ : syracuseStep 3793837 = 1422689) (by norm_num)
theorem B5058449 : Blo 2247435 5058449 := bstep (se 2 (by rfl) ⟨1896918, by rfl⟩ : syracuseStep 5058449 = 3793837) B3793837
theorem B3372299 : Blo 2247435 3372299 := bstep (se 1 (by rfl) ⟨2529224, by rfl⟩ : syracuseStep 3372299 = 5058449) B5058449
theorem B2248199 : Blo 2247435 2248199 := bstep (se 1 (by rfl) ⟨1686149, by rfl⟩ : syracuseStep 2248199 = 3372299) B3372299
theorem B2529229 : Blo 2247435 2529229 := bbase (se 3 (by rfl) ⟨474230, by rfl⟩ : syracuseStep 2529229 = 948461) (by norm_num)
theorem B3372305 : Blo 2247435 3372305 := bstep (se 2 (by rfl) ⟨1264614, by rfl⟩ : syracuseStep 3372305 = 2529229) B2529229
theorem B2248203 : Blo 2247435 2248203 := bstep (se 1 (by rfl) ⟨1686152, by rfl⟩ : syracuseStep 2248203 = 3372305) B3372305
theorem B7587701 : Blo 2247435 7587701 := bbase (se 5 (by rfl) ⟨355673, by rfl⟩ : syracuseStep 7587701 = 711347) (by norm_num)
theorem B5058467 : Blo 2247435 5058467 := bstep (se 1 (by rfl) ⟨3793850, by rfl⟩ : syracuseStep 5058467 = 7587701) B7587701
theorem B3372311 : Blo 2247435 3372311 := bstep (se 1 (by rfl) ⟨2529233, by rfl⟩ : syracuseStep 3372311 = 5058467) B5058467
theorem B2248207 : Blo 2247435 2248207 := bstep (se 1 (by rfl) ⟨1686155, by rfl⟩ : syracuseStep 2248207 = 3372311) B3372311
theorem B3372317 : Blo 2247435 3372317 := bbase (se 3 (by rfl) ⟨632309, by rfl⟩ : syracuseStep 3372317 = 1264619) (by norm_num)
theorem B2248211 : Blo 2247435 2248211 := bstep (se 1 (by rfl) ⟨1686158, by rfl⟩ : syracuseStep 2248211 = 3372317) B3372317
theorem B5058485 : Blo 2247435 5058485 := bbase (se 5 (by rfl) ⟨237116, by rfl⟩ : syracuseStep 5058485 = 474233) (by norm_num)
theorem B3372323 : Blo 2247435 3372323 := bstep (se 1 (by rfl) ⟨2529242, by rfl⟩ : syracuseStep 3372323 = 5058485) B5058485
theorem B2248215 : Blo 2247435 2248215 := bstep (se 1 (by rfl) ⟨1686161, by rfl⟩ : syracuseStep 2248215 = 3372323) B3372323
theorem B7691269 : Blo 2247435 7691269 := bbase (se 4 (by rfl) ⟨721056, by rfl⟩ : syracuseStep 7691269 = 1442113) (by norm_num)
theorem B10255025 : Blo 2247435 10255025 := bstep (se 2 (by rfl) ⟨3845634, by rfl⟩ : syracuseStep 10255025 = 7691269) B7691269
theorem B6836683 : Blo 2247435 6836683 := bstep (se 1 (by rfl) ⟨5127512, by rfl⟩ : syracuseStep 6836683 = 10255025) B10255025
theorem B9115577 : Blo 2247435 9115577 := bstep (se 2 (by rfl) ⟨3418341, by rfl⟩ : syracuseStep 9115577 = 6836683) B6836683
theorem B6077051 : Blo 2247435 6077051 := bstep (se 1 (by rfl) ⟨4557788, by rfl⟩ : syracuseStep 6077051 = 9115577) B9115577
theorem B4051367 : Blo 2247435 4051367 := bstep (se 1 (by rfl) ⟨3038525, by rfl⟩ : syracuseStep 4051367 = 6077051) B6077051
theorem B2700911 : Blo 2247435 2700911 := bstep (se 1 (by rfl) ⟨2025683, by rfl⟩ : syracuseStep 2700911 = 4051367) B4051367
theorem B7202429 : Blo 2247435 7202429 := bstep (se 3 (by rfl) ⟨1350455, by rfl⟩ : syracuseStep 7202429 = 2700911) B2700911
theorem B4801619 : Blo 2247435 4801619 := bstep (se 1 (by rfl) ⟨3601214, by rfl⟩ : syracuseStep 4801619 = 7202429) B7202429
theorem B12804317 : Blo 2247435 12804317 := bstep (se 3 (by rfl) ⟨2400809, by rfl⟩ : syracuseStep 12804317 = 4801619) B4801619
theorem B8536211 : Blo 2247435 8536211 := bstep (se 1 (by rfl) ⟨6402158, by rfl⟩ : syracuseStep 8536211 = 12804317) B12804317
theorem B5690807 : Blo 2247435 5690807 := bstep (se 1 (by rfl) ⟨4268105, by rfl⟩ : syracuseStep 5690807 = 8536211) B8536211
theorem B3793871 : Blo 2247435 3793871 := bstep (se 1 (by rfl) ⟨2845403, by rfl⟩ : syracuseStep 3793871 = 5690807) B5690807
theorem B2529247 : Blo 2247435 2529247 := bstep (se 1 (by rfl) ⟨1896935, by rfl⟩ : syracuseStep 2529247 = 3793871) B3793871
theorem B3372329 : Blo 2247435 3372329 := bstep (se 2 (by rfl) ⟨1264623, by rfl⟩ : syracuseStep 3372329 = 2529247) B2529247
theorem B2248219 : Blo 2247435 2248219 := bstep (se 1 (by rfl) ⟨1686164, by rfl⟩ : syracuseStep 2248219 = 3372329) B3372329
theorem B7300709 : Blo 2247435 7300709 := bbase (se 4 (by rfl) ⟨684441, by rfl⟩ : syracuseStep 7300709 = 1368883) (by norm_num)
theorem B4867139 : Blo 2247435 4867139 := bstep (se 1 (by rfl) ⟨3650354, by rfl⟩ : syracuseStep 4867139 = 7300709) B7300709
theorem B12979037 : Blo 2247435 12979037 := bstep (se 3 (by rfl) ⟨2433569, by rfl⟩ : syracuseStep 12979037 = 4867139) B4867139
theorem B8652691 : Blo 2247435 8652691 := bstep (se 1 (by rfl) ⟨6489518, by rfl⟩ : syracuseStep 8652691 = 12979037) B12979037
theorem B11536921 : Blo 2247435 11536921 := bstep (se 2 (by rfl) ⟨4326345, by rfl⟩ : syracuseStep 11536921 = 8652691) B8652691
theorem B15382561 : Blo 2247435 15382561 := bstep (se 2 (by rfl) ⟨5768460, by rfl⟩ : syracuseStep 15382561 = 11536921) B11536921
theorem B20510081 : Blo 2247435 20510081 := bstep (se 2 (by rfl) ⟨7691280, by rfl⟩ : syracuseStep 20510081 = 15382561) B15382561
theorem B13673387 : Blo 2247435 13673387 := bstep (se 1 (by rfl) ⟨10255040, by rfl⟩ : syracuseStep 13673387 = 20510081) B20510081
theorem B9115591 : Blo 2247435 9115591 := bstep (se 1 (by rfl) ⟨6836693, by rfl⟩ : syracuseStep 9115591 = 13673387) B13673387
theorem B12154121 : Blo 2247435 12154121 := bstep (se 2 (by rfl) ⟨4557795, by rfl⟩ : syracuseStep 12154121 = 9115591) B9115591
theorem B8102747 : Blo 2247435 8102747 := bstep (se 1 (by rfl) ⟨6077060, by rfl⟩ : syracuseStep 8102747 = 12154121) B12154121
theorem B5401831 : Blo 2247435 5401831 := bstep (se 1 (by rfl) ⟨4051373, by rfl⟩ : syracuseStep 5401831 = 8102747) B8102747
theorem B7202441 : Blo 2247435 7202441 := bstep (se 2 (by rfl) ⟨2700915, by rfl⟩ : syracuseStep 7202441 = 5401831) B5401831
theorem B4801627 : Blo 2247435 4801627 := bstep (se 1 (by rfl) ⟨3601220, by rfl⟩ : syracuseStep 4801627 = 7202441) B7202441
theorem B6402169 : Blo 2247435 6402169 := bstep (se 2 (by rfl) ⟨2400813, by rfl⟩ : syracuseStep 6402169 = 4801627) B4801627
theorem B8536225 : Blo 2247435 8536225 := bstep (se 2 (by rfl) ⟨3201084, by rfl⟩ : syracuseStep 8536225 = 6402169) B6402169
theorem B11381633 : Blo 2247435 11381633 := bstep (se 2 (by rfl) ⟨4268112, by rfl⟩ : syracuseStep 11381633 = 8536225) B8536225
theorem B7587755 : Blo 2247435 7587755 := bstep (se 1 (by rfl) ⟨5690816, by rfl⟩ : syracuseStep 7587755 = 11381633) B11381633
theorem B5058503 : Blo 2247435 5058503 := bstep (se 1 (by rfl) ⟨3793877, by rfl⟩ : syracuseStep 5058503 = 7587755) B7587755
theorem B3372335 : Blo 2247435 3372335 := bstep (se 1 (by rfl) ⟨2529251, by rfl⟩ : syracuseStep 3372335 = 5058503) B5058503
theorem B2248223 : Blo 2247435 2248223 := bstep (se 1 (by rfl) ⟨1686167, by rfl⟩ : syracuseStep 2248223 = 3372335) B3372335
theorem B3372341 : Blo 2247435 3372341 := bbase (se 5 (by rfl) ⟨158078, by rfl⟩ : syracuseStep 3372341 = 316157) (by norm_num)
theorem B2248227 : Blo 2247435 2248227 := bstep (se 1 (by rfl) ⟨1686170, by rfl⟩ : syracuseStep 2248227 = 3372341) B3372341
theorem B5690837 : Blo 2247435 5690837 := bbase (se 7 (by rfl) ⟨66689, by rfl⟩ : syracuseStep 5690837 = 133379) (by norm_num)
theorem B3793891 : Blo 2247435 3793891 := bstep (se 1 (by rfl) ⟨2845418, by rfl⟩ : syracuseStep 3793891 = 5690837) B5690837
theorem B5058521 : Blo 2247435 5058521 := bstep (se 2 (by rfl) ⟨1896945, by rfl⟩ : syracuseStep 5058521 = 3793891) B3793891
theorem B3372347 : Blo 2247435 3372347 := bstep (se 1 (by rfl) ⟨2529260, by rfl⟩ : syracuseStep 3372347 = 5058521) B5058521
theorem B2248231 : Blo 2247435 2248231 := bstep (se 1 (by rfl) ⟨1686173, by rfl⟩ : syracuseStep 2248231 = 3372347) B3372347
theorem B2529265 : Blo 2247435 2529265 := bbase (se 2 (by rfl) ⟨948474, by rfl⟩ : syracuseStep 2529265 = 1896949) (by norm_num)
theorem B3372353 : Blo 2247435 3372353 := bstep (se 2 (by rfl) ⟨1264632, by rfl⟩ : syracuseStep 3372353 = 2529265) B2529265
theorem B2248235 : Blo 2247435 2248235 := bstep (se 1 (by rfl) ⟨1686176, by rfl⟩ : syracuseStep 2248235 = 3372353) B3372353
theorem B5768501 : Blo 2247435 5768501 := bbase (se 5 (by rfl) ⟨270398, by rfl⟩ : syracuseStep 5768501 = 540797) (by norm_num)
theorem B61530677 : Blo 2247435 61530677 := bstep (se 5 (by rfl) ⟨2884250, by rfl⟩ : syracuseStep 61530677 = 5768501) B5768501
theorem B41020451 : Blo 2247435 41020451 := bstep (se 1 (by rfl) ⟨30765338, by rfl⟩ : syracuseStep 41020451 = 61530677) B61530677
theorem B27346967 : Blo 2247435 27346967 := bstep (se 1 (by rfl) ⟨20510225, by rfl⟩ : syracuseStep 27346967 = 41020451) B41020451
theorem B18231311 : Blo 2247435 18231311 := bstep (se 1 (by rfl) ⟨13673483, by rfl⟩ : syracuseStep 18231311 = 27346967) B27346967
theorem B12154207 : Blo 2247435 12154207 := bstep (se 1 (by rfl) ⟨9115655, by rfl⟩ : syracuseStep 12154207 = 18231311) B18231311
theorem B16205609 : Blo 2247435 16205609 := bstep (se 2 (by rfl) ⟨6077103, by rfl⟩ : syracuseStep 16205609 = 12154207) B12154207
theorem B10803739 : Blo 2247435 10803739 := bstep (se 1 (by rfl) ⟨8102804, by rfl⟩ : syracuseStep 10803739 = 16205609) B16205609
theorem B14404985 : Blo 2247435 14404985 := bstep (se 2 (by rfl) ⟨5401869, by rfl⟩ : syracuseStep 14404985 = 10803739) B10803739
theorem B9603323 : Blo 2247435 9603323 := bstep (se 1 (by rfl) ⟨7202492, by rfl⟩ : syracuseStep 9603323 = 14404985) B14404985
theorem B6402215 : Blo 2247435 6402215 := bstep (se 1 (by rfl) ⟨4801661, by rfl⟩ : syracuseStep 6402215 = 9603323) B9603323
theorem B4268143 : Blo 2247435 4268143 := bstep (se 1 (by rfl) ⟨3201107, by rfl⟩ : syracuseStep 4268143 = 6402215) B6402215
theorem B5690857 : Blo 2247435 5690857 := bstep (se 2 (by rfl) ⟨2134071, by rfl⟩ : syracuseStep 5690857 = 4268143) B4268143
theorem B7587809 : Blo 2247435 7587809 := bstep (se 2 (by rfl) ⟨2845428, by rfl⟩ : syracuseStep 7587809 = 5690857) B5690857
theorem B5058539 : Blo 2247435 5058539 := bstep (se 1 (by rfl) ⟨3793904, by rfl⟩ : syracuseStep 5058539 = 7587809) B7587809
theorem B3372359 : Blo 2247435 3372359 := bstep (se 1 (by rfl) ⟨2529269, by rfl⟩ : syracuseStep 3372359 = 5058539) B5058539
theorem B2248239 : Blo 2247435 2248239 := bstep (se 1 (by rfl) ⟨1686179, by rfl⟩ : syracuseStep 2248239 = 3372359) B3372359
theorem B3372365 : Blo 2247435 3372365 := bbase (se 3 (by rfl) ⟨632318, by rfl⟩ : syracuseStep 3372365 = 1264637) (by norm_num)
theorem B2248243 : Blo 2247435 2248243 := bstep (se 1 (by rfl) ⟨1686182, by rfl⟩ : syracuseStep 2248243 = 3372365) B3372365
theorem B5058557 : Blo 2247435 5058557 := bbase (se 3 (by rfl) ⟨948479, by rfl⟩ : syracuseStep 5058557 = 1896959) (by norm_num)
theorem B3372371 : Blo 2247435 3372371 := bstep (se 1 (by rfl) ⟨2529278, by rfl⟩ : syracuseStep 3372371 = 5058557) B5058557
theorem B2248247 : Blo 2247435 2248247 := bstep (se 1 (by rfl) ⟨1686185, by rfl⟩ : syracuseStep 2248247 = 3372371) B3372371
theorem B3793925 : Blo 2247435 3793925 := bbase (se 4 (by rfl) ⟨355680, by rfl⟩ : syracuseStep 3793925 = 711361) (by norm_num)
theorem B2529283 : Blo 2247435 2529283 := bstep (se 1 (by rfl) ⟨1896962, by rfl⟩ : syracuseStep 2529283 = 3793925) B3793925
theorem B3372377 : Blo 2247435 3372377 := bstep (se 2 (by rfl) ⟨1264641, by rfl⟩ : syracuseStep 3372377 = 2529283) B2529283
theorem B2248251 : Blo 2247435 2248251 := bstep (se 1 (by rfl) ⟨1686188, by rfl⟩ : syracuseStep 2248251 = 3372377) B3372377
theorem B17072693 : Blo 2247435 17072693 := bbase (se 5 (by rfl) ⟨800282, by rfl⟩ : syracuseStep 17072693 = 1600565) (by norm_num)
theorem B11381795 : Blo 2247435 11381795 := bstep (se 1 (by rfl) ⟨8536346, by rfl⟩ : syracuseStep 11381795 = 17072693) B17072693
theorem B7587863 : Blo 2247435 7587863 := bstep (se 1 (by rfl) ⟨5690897, by rfl⟩ : syracuseStep 7587863 = 11381795) B11381795
theorem B5058575 : Blo 2247435 5058575 := bstep (se 1 (by rfl) ⟨3793931, by rfl⟩ : syracuseStep 5058575 = 7587863) B7587863
theorem B3372383 : Blo 2247435 3372383 := bstep (se 1 (by rfl) ⟨2529287, by rfl⟩ : syracuseStep 3372383 = 5058575) B5058575
theorem B2248255 : Blo 2247435 2248255 := bstep (se 1 (by rfl) ⟨1686191, by rfl⟩ : syracuseStep 2248255 = 3372383) B3372383
theorem B3372389 : Blo 2247435 3372389 := bbase (se 4 (by rfl) ⟨316161, by rfl⟩ : syracuseStep 3372389 = 632323) (by norm_num)
theorem B2248259 : Blo 2247435 2248259 := bstep (se 1 (by rfl) ⟨1686194, by rfl⟩ : syracuseStep 2248259 = 3372389) B3372389
theorem B4268189 : Blo 2247435 4268189 := bbase (se 3 (by rfl) ⟨800285, by rfl⟩ : syracuseStep 4268189 = 1600571) (by norm_num)
theorem B2845459 : Blo 2247435 2845459 := bstep (se 1 (by rfl) ⟨2134094, by rfl⟩ : syracuseStep 2845459 = 4268189) B4268189
theorem B3793945 : Blo 2247435 3793945 := bstep (se 2 (by rfl) ⟨1422729, by rfl⟩ : syracuseStep 3793945 = 2845459) B2845459
theorem B5058593 : Blo 2247435 5058593 := bstep (se 2 (by rfl) ⟨1896972, by rfl⟩ : syracuseStep 5058593 = 3793945) B3793945
theorem B3372395 : Blo 2247435 3372395 := bstep (se 1 (by rfl) ⟨2529296, by rfl⟩ : syracuseStep 3372395 = 5058593) B5058593
theorem B2248263 : Blo 2247435 2248263 := bstep (se 1 (by rfl) ⟨1686197, by rfl⟩ : syracuseStep 2248263 = 3372395) B3372395
theorem B2529301 : Blo 2247435 2529301 := bbase (se 6 (by rfl) ⟨59280, by rfl⟩ : syracuseStep 2529301 = 118561) (by norm_num)
theorem B3372401 : Blo 2247435 3372401 := bstep (se 2 (by rfl) ⟨1264650, by rfl⟩ : syracuseStep 3372401 = 2529301) B2529301
theorem B2248267 : Blo 2247435 2248267 := bstep (se 1 (by rfl) ⟨1686200, by rfl⟩ : syracuseStep 2248267 = 3372401) B3372401
theorem B2845469 : Blo 2247435 2845469 := bbase (se 3 (by rfl) ⟨533525, by rfl⟩ : syracuseStep 2845469 = 1067051) (by norm_num)
theorem B7587917 : Blo 2247435 7587917 := bstep (se 3 (by rfl) ⟨1422734, by rfl⟩ : syracuseStep 7587917 = 2845469) B2845469
theorem B5058611 : Blo 2247435 5058611 := bstep (se 1 (by rfl) ⟨3793958, by rfl⟩ : syracuseStep 5058611 = 7587917) B7587917
theorem B3372407 : Blo 2247435 3372407 := bstep (se 1 (by rfl) ⟨2529305, by rfl⟩ : syracuseStep 3372407 = 5058611) B5058611
theorem B2248271 : Blo 2247435 2248271 := bstep (se 1 (by rfl) ⟨1686203, by rfl⟩ : syracuseStep 2248271 = 3372407) B3372407
theorem B3372413 : Blo 2247435 3372413 := bbase (se 3 (by rfl) ⟨632327, by rfl⟩ : syracuseStep 3372413 = 1264655) (by norm_num)
theorem B2248275 : Blo 2247435 2248275 := bstep (se 1 (by rfl) ⟨1686206, by rfl⟩ : syracuseStep 2248275 = 3372413) B3372413
theorem B5058629 : Blo 2247435 5058629 := bbase (se 4 (by rfl) ⟨474246, by rfl⟩ : syracuseStep 5058629 = 948493) (by norm_num)
theorem B3372419 : Blo 2247435 3372419 := bstep (se 1 (by rfl) ⟨2529314, by rfl⟩ : syracuseStep 3372419 = 5058629) B5058629
theorem B2248279 : Blo 2247435 2248279 := bstep (se 1 (by rfl) ⟨1686209, by rfl⟩ : syracuseStep 2248279 = 3372419) B3372419
theorem B6402341 : Blo 2247435 6402341 := bbase (se 4 (by rfl) ⟨600219, by rfl⟩ : syracuseStep 6402341 = 1200439) (by norm_num)
theorem B4268227 : Blo 2247435 4268227 := bstep (se 1 (by rfl) ⟨3201170, by rfl⟩ : syracuseStep 4268227 = 6402341) B6402341
theorem B5690969 : Blo 2247435 5690969 := bstep (se 2 (by rfl) ⟨2134113, by rfl⟩ : syracuseStep 5690969 = 4268227) B4268227
theorem B3793979 : Blo 2247435 3793979 := bstep (se 1 (by rfl) ⟨2845484, by rfl⟩ : syracuseStep 3793979 = 5690969) B5690969
theorem B2529319 : Blo 2247435 2529319 := bstep (se 1 (by rfl) ⟨1896989, by rfl⟩ : syracuseStep 2529319 = 3793979) B3793979
theorem B3372425 : Blo 2247435 3372425 := bstep (se 2 (by rfl) ⟨1264659, by rfl⟩ : syracuseStep 3372425 = 2529319) B2529319
theorem B2248283 : Blo 2247435 2248283 := bstep (se 1 (by rfl) ⟨1686212, by rfl⟩ : syracuseStep 2248283 = 3372425) B3372425
theorem B11381957 : Blo 2247435 11381957 := bbase (se 4 (by rfl) ⟨1067058, by rfl⟩ : syracuseStep 11381957 = 2134117) (by norm_num)
theorem B7587971 : Blo 2247435 7587971 := bstep (se 1 (by rfl) ⟨5690978, by rfl⟩ : syracuseStep 7587971 = 11381957) B11381957
theorem B5058647 : Blo 2247435 5058647 := bstep (se 1 (by rfl) ⟨3793985, by rfl⟩ : syracuseStep 5058647 = 7587971) B7587971
theorem B3372431 : Blo 2247435 3372431 := bstep (se 1 (by rfl) ⟨2529323, by rfl⟩ : syracuseStep 3372431 = 5058647) B5058647
theorem B2248287 : Blo 2247435 2248287 := bstep (se 1 (by rfl) ⟨1686215, by rfl⟩ : syracuseStep 2248287 = 3372431) B3372431
theorem B3372437 : Blo 2247435 3372437 := bbase (se 6 (by rfl) ⟨79041, by rfl⟩ : syracuseStep 3372437 = 158083) (by norm_num)
theorem B2248291 : Blo 2247435 2248291 := bstep (se 1 (by rfl) ⟨1686218, by rfl⟩ : syracuseStep 2248291 = 3372437) B3372437
theorem B4801781 : Blo 2247435 4801781 := bbase (se 5 (by rfl) ⟨225083, by rfl⟩ : syracuseStep 4801781 = 450167) (by norm_num)
theorem B12804749 : Blo 2247435 12804749 := bstep (se 3 (by rfl) ⟨2400890, by rfl⟩ : syracuseStep 12804749 = 4801781) B4801781
theorem B8536499 : Blo 2247435 8536499 := bstep (se 1 (by rfl) ⟨6402374, by rfl⟩ : syracuseStep 8536499 = 12804749) B12804749
theorem B5690999 : Blo 2247435 5690999 := bstep (se 1 (by rfl) ⟨4268249, by rfl⟩ : syracuseStep 5690999 = 8536499) B8536499
theorem B3793999 : Blo 2247435 3793999 := bstep (se 1 (by rfl) ⟨2845499, by rfl⟩ : syracuseStep 3793999 = 5690999) B5690999
theorem B5058665 : Blo 2247435 5058665 := bstep (se 2 (by rfl) ⟨1896999, by rfl⟩ : syracuseStep 5058665 = 3793999) B3793999
theorem B3372443 : Blo 2247435 3372443 := bstep (se 1 (by rfl) ⟨2529332, by rfl⟩ : syracuseStep 3372443 = 5058665) B5058665
theorem B2248295 : Blo 2247435 2248295 := bstep (se 1 (by rfl) ⟨1686221, by rfl⟩ : syracuseStep 2248295 = 3372443) B3372443
theorem B2529337 : Blo 2247435 2529337 := bbase (se 2 (by rfl) ⟨948501, by rfl⟩ : syracuseStep 2529337 = 1897003) (by norm_num)
theorem B3372449 : Blo 2247435 3372449 := bstep (se 2 (by rfl) ⟨1264668, by rfl⟩ : syracuseStep 3372449 = 2529337) B2529337
theorem B2248299 : Blo 2247435 2248299 := bstep (se 1 (by rfl) ⟨1686224, by rfl⟩ : syracuseStep 2248299 = 3372449) B3372449
theorem B3601349 : Blo 2247435 3601349 := bbase (se 4 (by rfl) ⟨337626, by rfl⟩ : syracuseStep 3601349 = 675253) (by norm_num)
theorem B2400899 : Blo 2247435 2400899 := bstep (se 1 (by rfl) ⟨1800674, by rfl⟩ : syracuseStep 2400899 = 3601349) B3601349
theorem B6402397 : Blo 2247435 6402397 := bstep (se 3 (by rfl) ⟨1200449, by rfl⟩ : syracuseStep 6402397 = 2400899) B2400899
theorem B8536529 : Blo 2247435 8536529 := bstep (se 2 (by rfl) ⟨3201198, by rfl⟩ : syracuseStep 8536529 = 6402397) B6402397
theorem B5691019 : Blo 2247435 5691019 := bstep (se 1 (by rfl) ⟨4268264, by rfl⟩ : syracuseStep 5691019 = 8536529) B8536529
theorem B7588025 : Blo 2247435 7588025 := bstep (se 2 (by rfl) ⟨2845509, by rfl⟩ : syracuseStep 7588025 = 5691019) B5691019
theorem B5058683 : Blo 2247435 5058683 := bstep (se 1 (by rfl) ⟨3794012, by rfl⟩ : syracuseStep 5058683 = 7588025) B7588025
theorem B3372455 : Blo 2247435 3372455 := bstep (se 1 (by rfl) ⟨2529341, by rfl⟩ : syracuseStep 3372455 = 5058683) B5058683
theorem B2248303 : Blo 2247435 2248303 := bstep (se 1 (by rfl) ⟨1686227, by rfl⟩ : syracuseStep 2248303 = 3372455) B3372455
theorem B3372461 : Blo 2247435 3372461 := bbase (se 3 (by rfl) ⟨632336, by rfl⟩ : syracuseStep 3372461 = 1264673) (by norm_num)
theorem B2248307 : Blo 2247435 2248307 := bstep (se 1 (by rfl) ⟨1686230, by rfl⟩ : syracuseStep 2248307 = 3372461) B3372461
theorem B5058701 : Blo 2247435 5058701 := bbase (se 3 (by rfl) ⟨948506, by rfl⟩ : syracuseStep 5058701 = 1897013) (by norm_num)
theorem B3372467 : Blo 2247435 3372467 := bstep (se 1 (by rfl) ⟨2529350, by rfl⟩ : syracuseStep 3372467 = 5058701) B5058701
theorem B2248311 : Blo 2247435 2248311 := bstep (se 1 (by rfl) ⟨1686233, by rfl⟩ : syracuseStep 2248311 = 3372467) B3372467
theorem B2845525 : Blo 2247435 2845525 := bbase (se 9 (by rfl) ⟨8336, by rfl⟩ : syracuseStep 2845525 = 16673) (by norm_num)
theorem B3794033 : Blo 2247435 3794033 := bstep (se 2 (by rfl) ⟨1422762, by rfl⟩ : syracuseStep 3794033 = 2845525) B2845525
theorem B2529355 : Blo 2247435 2529355 := bstep (se 1 (by rfl) ⟨1897016, by rfl⟩ : syracuseStep 2529355 = 3794033) B3794033
theorem B3372473 : Blo 2247435 3372473 := bstep (se 2 (by rfl) ⟨1264677, by rfl⟩ : syracuseStep 3372473 = 2529355) B2529355
theorem B2248315 : Blo 2247435 2248315 := bstep (se 1 (by rfl) ⟨1686236, by rfl⟩ : syracuseStep 2248315 = 3372473) B3372473
theorem B3650509 : Blo 2247435 3650509 := bbase (se 3 (by rfl) ⟨684470, by rfl⟩ : syracuseStep 3650509 = 1368941) (by norm_num)
theorem B4867345 : Blo 2247435 4867345 := bstep (se 2 (by rfl) ⟨1825254, by rfl⟩ : syracuseStep 4867345 = 3650509) B3650509
theorem B6489793 : Blo 2247435 6489793 := bstep (se 2 (by rfl) ⟨2433672, by rfl⟩ : syracuseStep 6489793 = 4867345) B4867345
theorem B34612229 : Blo 2247435 34612229 := bstep (se 4 (by rfl) ⟨3244896, by rfl⟩ : syracuseStep 34612229 = 6489793) B6489793
theorem B92299277 : Blo 2247435 92299277 := bstep (se 3 (by rfl) ⟨17306114, by rfl⟩ : syracuseStep 92299277 = 34612229) B34612229
theorem B246131405 : Blo 2247435 246131405 := bstep (se 3 (by rfl) ⟨46149638, by rfl⟩ : syracuseStep 246131405 = 92299277) B92299277
theorem B164087603 : Blo 2247435 164087603 := bstep (se 1 (by rfl) ⟨123065702, by rfl⟩ : syracuseStep 164087603 = 246131405) B246131405
theorem B109391735 : Blo 2247435 109391735 := bstep (se 1 (by rfl) ⟨82043801, by rfl⟩ : syracuseStep 109391735 = 164087603) B164087603
theorem B72927823 : Blo 2247435 72927823 := bstep (se 1 (by rfl) ⟨54695867, by rfl⟩ : syracuseStep 72927823 = 109391735) B109391735
theorem B97237097 : Blo 2247435 97237097 := bstep (se 2 (by rfl) ⟨36463911, by rfl⟩ : syracuseStep 97237097 = 72927823) B72927823
theorem B64824731 : Blo 2247435 64824731 := bstep (se 1 (by rfl) ⟨48618548, by rfl⟩ : syracuseStep 64824731 = 97237097) B97237097
theorem B43216487 : Blo 2247435 43216487 := bstep (se 1 (by rfl) ⟨32412365, by rfl⟩ : syracuseStep 43216487 = 64824731) B64824731
theorem B28810991 : Blo 2247435 28810991 := bstep (se 1 (by rfl) ⟨21608243, by rfl⟩ : syracuseStep 28810991 = 43216487) B43216487
theorem B19207327 : Blo 2247435 19207327 := bstep (se 1 (by rfl) ⟨14405495, by rfl⟩ : syracuseStep 19207327 = 28810991) B28810991
theorem B25609769 : Blo 2247435 25609769 := bstep (se 2 (by rfl) ⟨9603663, by rfl⟩ : syracuseStep 25609769 = 19207327) B19207327
theorem B17073179 : Blo 2247435 17073179 := bstep (se 1 (by rfl) ⟨12804884, by rfl⟩ : syracuseStep 17073179 = 25609769) B25609769
theorem B11382119 : Blo 2247435 11382119 := bstep (se 1 (by rfl) ⟨8536589, by rfl⟩ : syracuseStep 11382119 = 17073179) B17073179
theorem B7588079 : Blo 2247435 7588079 := bstep (se 1 (by rfl) ⟨5691059, by rfl⟩ : syracuseStep 7588079 = 11382119) B11382119
theorem B5058719 : Blo 2247435 5058719 := bstep (se 1 (by rfl) ⟨3794039, by rfl⟩ : syracuseStep 5058719 = 7588079) B7588079
theorem B3372479 : Blo 2247435 3372479 := bstep (se 1 (by rfl) ⟨2529359, by rfl⟩ : syracuseStep 3372479 = 5058719) B5058719
theorem B2248319 : Blo 2247435 2248319 := bstep (se 1 (by rfl) ⟨1686239, by rfl⟩ : syracuseStep 2248319 = 3372479) B3372479
theorem B3372485 : Blo 2247435 3372485 := bbase (se 4 (by rfl) ⟨316170, by rfl⟩ : syracuseStep 3372485 = 632341) (by norm_num)
theorem B2248323 : Blo 2247435 2248323 := bstep (se 1 (by rfl) ⟨1686242, by rfl⟩ : syracuseStep 2248323 = 3372485) B3372485
theorem B3794053 : Blo 2247435 3794053 := bbase (se 4 (by rfl) ⟨355692, by rfl⟩ : syracuseStep 3794053 = 711385) (by norm_num)
theorem B5058737 : Blo 2247435 5058737 := bstep (se 2 (by rfl) ⟨1897026, by rfl⟩ : syracuseStep 5058737 = 3794053) B3794053
theorem B3372491 : Blo 2247435 3372491 := bstep (se 1 (by rfl) ⟨2529368, by rfl⟩ : syracuseStep 3372491 = 5058737) B5058737
theorem B2248327 : Blo 2247435 2248327 := bstep (se 1 (by rfl) ⟨1686245, by rfl⟩ : syracuseStep 2248327 = 3372491) B3372491
theorem B2529373 : Blo 2247435 2529373 := bbase (se 3 (by rfl) ⟨474257, by rfl⟩ : syracuseStep 2529373 = 948515) (by norm_num)
theorem B3372497 : Blo 2247435 3372497 := bstep (se 2 (by rfl) ⟨1264686, by rfl⟩ : syracuseStep 3372497 = 2529373) B2529373
theorem B2248331 : Blo 2247435 2248331 := bstep (se 1 (by rfl) ⟨1686248, by rfl⟩ : syracuseStep 2248331 = 3372497) B3372497
theorem B7588133 : Blo 2247435 7588133 := bbase (se 4 (by rfl) ⟨711387, by rfl⟩ : syracuseStep 7588133 = 1422775) (by norm_num)
theorem B5058755 : Blo 2247435 5058755 := bstep (se 1 (by rfl) ⟨3794066, by rfl⟩ : syracuseStep 5058755 = 7588133) B7588133
theorem B3372503 : Blo 2247435 3372503 := bstep (se 1 (by rfl) ⟨2529377, by rfl⟩ : syracuseStep 3372503 = 5058755) B5058755
theorem B2248335 : Blo 2247435 2248335 := bstep (se 1 (by rfl) ⟨1686251, by rfl⟩ : syracuseStep 2248335 = 3372503) B3372503
theorem B3372509 : Blo 2247435 3372509 := bbase (se 3 (by rfl) ⟨632345, by rfl⟩ : syracuseStep 3372509 = 1264691) (by norm_num)
theorem B2248339 : Blo 2247435 2248339 := bstep (se 1 (by rfl) ⟨1686254, by rfl⟩ : syracuseStep 2248339 = 3372509) B3372509
theorem B5058773 : Blo 2247435 5058773 := bbase (se 7 (by rfl) ⟨59282, by rfl⟩ : syracuseStep 5058773 = 118565) (by norm_num)
theorem B3372515 : Blo 2247435 3372515 := bstep (se 1 (by rfl) ⟨2529386, by rfl⟩ : syracuseStep 3372515 = 5058773) B5058773
theorem B2248343 : Blo 2247435 2248343 := bstep (se 1 (by rfl) ⟨1686257, by rfl⟩ : syracuseStep 2248343 = 3372515) B3372515
theorem B16206389 : Blo 2247435 16206389 := bbase (se 5 (by rfl) ⟨759674, by rfl⟩ : syracuseStep 16206389 = 1519349) (by norm_num)
theorem B10804259 : Blo 2247435 10804259 := bstep (se 1 (by rfl) ⟨8103194, by rfl⟩ : syracuseStep 10804259 = 16206389) B16206389
theorem B7202839 : Blo 2247435 7202839 := bstep (se 1 (by rfl) ⟨5402129, by rfl⟩ : syracuseStep 7202839 = 10804259) B10804259
theorem B9603785 : Blo 2247435 9603785 := bstep (se 2 (by rfl) ⟨3601419, by rfl⟩ : syracuseStep 9603785 = 7202839) B7202839
theorem B6402523 : Blo 2247435 6402523 := bstep (se 1 (by rfl) ⟨4801892, by rfl⟩ : syracuseStep 6402523 = 9603785) B9603785
theorem B8536697 : Blo 2247435 8536697 := bstep (se 2 (by rfl) ⟨3201261, by rfl⟩ : syracuseStep 8536697 = 6402523) B6402523
theorem B5691131 : Blo 2247435 5691131 := bstep (se 1 (by rfl) ⟨4268348, by rfl⟩ : syracuseStep 5691131 = 8536697) B8536697
theorem B3794087 : Blo 2247435 3794087 := bstep (se 1 (by rfl) ⟨2845565, by rfl⟩ : syracuseStep 3794087 = 5691131) B5691131
theorem B2529391 : Blo 2247435 2529391 := bstep (se 1 (by rfl) ⟨1897043, by rfl⟩ : syracuseStep 2529391 = 3794087) B3794087
theorem B3372521 : Blo 2247435 3372521 := bstep (se 2 (by rfl) ⟨1264695, by rfl⟩ : syracuseStep 3372521 = 2529391) B2529391
theorem B2248347 : Blo 2247435 2248347 := bstep (se 1 (by rfl) ⟨1686260, by rfl⟩ : syracuseStep 2248347 = 3372521) B3372521
theorem B2701069 : Blo 2247435 2701069 := bbase (se 3 (by rfl) ⟨506450, by rfl⟩ : syracuseStep 2701069 = 1012901) (by norm_num)
theorem B14405701 : Blo 2247435 14405701 := bstep (se 4 (by rfl) ⟨1350534, by rfl⟩ : syracuseStep 14405701 = 2701069) B2701069
theorem B19207601 : Blo 2247435 19207601 := bstep (se 2 (by rfl) ⟨7202850, by rfl⟩ : syracuseStep 19207601 = 14405701) B14405701
theorem B12805067 : Blo 2247435 12805067 := bstep (se 1 (by rfl) ⟨9603800, by rfl⟩ : syracuseStep 12805067 = 19207601) B19207601
theorem B8536711 : Blo 2247435 8536711 := bstep (se 1 (by rfl) ⟨6402533, by rfl⟩ : syracuseStep 8536711 = 12805067) B12805067
theorem B11382281 : Blo 2247435 11382281 := bstep (se 2 (by rfl) ⟨4268355, by rfl⟩ : syracuseStep 11382281 = 8536711) B8536711
theorem B7588187 : Blo 2247435 7588187 := bstep (se 1 (by rfl) ⟨5691140, by rfl⟩ : syracuseStep 7588187 = 11382281) B11382281
theorem B5058791 : Blo 2247435 5058791 := bstep (se 1 (by rfl) ⟨3794093, by rfl⟩ : syracuseStep 5058791 = 7588187) B7588187
theorem B3372527 : Blo 2247435 3372527 := bstep (se 1 (by rfl) ⟨2529395, by rfl⟩ : syracuseStep 3372527 = 5058791) B5058791
theorem B2248351 : Blo 2247435 2248351 := bstep (se 1 (by rfl) ⟨1686263, by rfl⟩ : syracuseStep 2248351 = 3372527) B3372527
theorem B3372533 : Blo 2247435 3372533 := bbase (se 5 (by rfl) ⟨158087, by rfl⟩ : syracuseStep 3372533 = 316175) (by norm_num)
theorem B2248355 : Blo 2247435 2248355 := bstep (se 1 (by rfl) ⟨1686266, by rfl⟩ : syracuseStep 2248355 = 3372533) B3372533
theorem B5847517 : Blo 2247435 5847517 := bbase (se 3 (by rfl) ⟨1096409, by rfl⟩ : syracuseStep 5847517 = 2192819) (by norm_num)
theorem B31186757 : Blo 2247435 31186757 := bstep (se 4 (by rfl) ⟨2923758, by rfl⟩ : syracuseStep 31186757 = 5847517) B5847517
theorem B20791171 : Blo 2247435 20791171 := bstep (se 1 (by rfl) ⟨15593378, by rfl⟩ : syracuseStep 20791171 = 31186757) B31186757
theorem B110886245 : Blo 2247435 110886245 := bstep (se 4 (by rfl) ⟨10395585, by rfl⟩ : syracuseStep 110886245 = 20791171) B20791171
theorem B73924163 : Blo 2247435 73924163 := bstep (se 1 (by rfl) ⟨55443122, by rfl⟩ : syracuseStep 73924163 = 110886245) B110886245
theorem B49282775 : Blo 2247435 49282775 := bstep (se 1 (by rfl) ⟨36962081, by rfl⟩ : syracuseStep 49282775 = 73924163) B73924163
theorem B32855183 : Blo 2247435 32855183 := bstep (se 1 (by rfl) ⟨24641387, by rfl⟩ : syracuseStep 32855183 = 49282775) B49282775
theorem B21903455 : Blo 2247435 21903455 := bstep (se 1 (by rfl) ⟨16427591, by rfl⟩ : syracuseStep 21903455 = 32855183) B32855183
theorem B14602303 : Blo 2247435 14602303 := bstep (se 1 (by rfl) ⟨10951727, by rfl⟩ : syracuseStep 14602303 = 21903455) B21903455
theorem B19469737 : Blo 2247435 19469737 := bstep (se 2 (by rfl) ⟨7301151, by rfl⟩ : syracuseStep 19469737 = 14602303) B14602303
theorem B25959649 : Blo 2247435 25959649 := bstep (se 2 (by rfl) ⟨9734868, by rfl⟩ : syracuseStep 25959649 = 19469737) B19469737
theorem B34612865 : Blo 2247435 34612865 := bstep (se 2 (by rfl) ⟨12979824, by rfl⟩ : syracuseStep 34612865 = 25959649) B25959649
theorem B23075243 : Blo 2247435 23075243 := bstep (se 1 (by rfl) ⟨17306432, by rfl⟩ : syracuseStep 23075243 = 34612865) B34612865
theorem B15383495 : Blo 2247435 15383495 := bstep (se 1 (by rfl) ⟨11537621, by rfl⟩ : syracuseStep 15383495 = 23075243) B23075243
theorem B10255663 : Blo 2247435 10255663 := bstep (se 1 (by rfl) ⟨7691747, by rfl⟩ : syracuseStep 10255663 = 15383495) B15383495
theorem B13674217 : Blo 2247435 13674217 := bstep (se 2 (by rfl) ⟨5127831, by rfl⟩ : syracuseStep 13674217 = 10255663) B10255663
theorem B18232289 : Blo 2247435 18232289 := bstep (se 2 (by rfl) ⟨6837108, by rfl⟩ : syracuseStep 18232289 = 13674217) B13674217
theorem B12154859 : Blo 2247435 12154859 := bstep (se 1 (by rfl) ⟨9116144, by rfl⟩ : syracuseStep 12154859 = 18232289) B18232289
theorem B8103239 : Blo 2247435 8103239 := bstep (se 1 (by rfl) ⟨6077429, by rfl⟩ : syracuseStep 8103239 = 12154859) B12154859
theorem B5402159 : Blo 2247435 5402159 := bstep (se 1 (by rfl) ⟨4051619, by rfl⟩ : syracuseStep 5402159 = 8103239) B8103239
theorem B3601439 : Blo 2247435 3601439 := bstep (se 1 (by rfl) ⟨2701079, by rfl⟩ : syracuseStep 3601439 = 5402159) B5402159
theorem B2400959 : Blo 2247435 2400959 := bstep (se 1 (by rfl) ⟨1800719, by rfl⟩ : syracuseStep 2400959 = 3601439) B3601439
theorem B6402557 : Blo 2247435 6402557 := bstep (se 3 (by rfl) ⟨1200479, by rfl⟩ : syracuseStep 6402557 = 2400959) B2400959
theorem B4268371 : Blo 2247435 4268371 := bstep (se 1 (by rfl) ⟨3201278, by rfl⟩ : syracuseStep 4268371 = 6402557) B6402557
theorem B5691161 : Blo 2247435 5691161 := bstep (se 2 (by rfl) ⟨2134185, by rfl⟩ : syracuseStep 5691161 = 4268371) B4268371
theorem B3794107 : Blo 2247435 3794107 := bstep (se 1 (by rfl) ⟨2845580, by rfl⟩ : syracuseStep 3794107 = 5691161) B5691161
theorem B5058809 : Blo 2247435 5058809 := bstep (se 2 (by rfl) ⟨1897053, by rfl⟩ : syracuseStep 5058809 = 3794107) B3794107
theorem B3372539 : Blo 2247435 3372539 := bstep (se 1 (by rfl) ⟨2529404, by rfl⟩ : syracuseStep 3372539 = 5058809) B5058809
theorem B2248359 : Blo 2247435 2248359 := bstep (se 1 (by rfl) ⟨1686269, by rfl⟩ : syracuseStep 2248359 = 3372539) B3372539
theorem B2529409 : Blo 2247435 2529409 := bbase (se 2 (by rfl) ⟨948528, by rfl⟩ : syracuseStep 2529409 = 1897057) (by norm_num)
theorem B3372545 : Blo 2247435 3372545 := bstep (se 2 (by rfl) ⟨1264704, by rfl⟩ : syracuseStep 3372545 = 2529409) B2529409
theorem B2248363 : Blo 2247435 2248363 := bstep (se 1 (by rfl) ⟨1686272, by rfl⟩ : syracuseStep 2248363 = 3372545) B3372545
theorem B5691181 : Blo 2247435 5691181 := bbase (se 3 (by rfl) ⟨1067096, by rfl⟩ : syracuseStep 5691181 = 2134193) (by norm_num)
theorem B7588241 : Blo 2247435 7588241 := bstep (se 2 (by rfl) ⟨2845590, by rfl⟩ : syracuseStep 7588241 = 5691181) B5691181
theorem B5058827 : Blo 2247435 5058827 := bstep (se 1 (by rfl) ⟨3794120, by rfl⟩ : syracuseStep 5058827 = 7588241) B7588241
theorem B3372551 : Blo 2247435 3372551 := bstep (se 1 (by rfl) ⟨2529413, by rfl⟩ : syracuseStep 3372551 = 5058827) B5058827
theorem B2248367 : Blo 2247435 2248367 := bstep (se 1 (by rfl) ⟨1686275, by rfl⟩ : syracuseStep 2248367 = 3372551) B3372551
theorem B3372557 : Blo 2247435 3372557 := bbase (se 3 (by rfl) ⟨632354, by rfl⟩ : syracuseStep 3372557 = 1264709) (by norm_num)
theorem B2248371 : Blo 2247435 2248371 := bstep (se 1 (by rfl) ⟨1686278, by rfl⟩ : syracuseStep 2248371 = 3372557) B3372557
theorem B5058845 : Blo 2247435 5058845 := bbase (se 3 (by rfl) ⟨948533, by rfl⟩ : syracuseStep 5058845 = 1897067) (by norm_num)
theorem B3372563 : Blo 2247435 3372563 := bstep (se 1 (by rfl) ⟨2529422, by rfl⟩ : syracuseStep 3372563 = 5058845) B5058845
theorem B2248375 : Blo 2247435 2248375 := bstep (se 1 (by rfl) ⟨1686281, by rfl⟩ : syracuseStep 2248375 = 3372563) B3372563
theorem B3794141 : Blo 2247435 3794141 := bbase (se 3 (by rfl) ⟨711401, by rfl⟩ : syracuseStep 3794141 = 1422803) (by norm_num)
theorem B2529427 : Blo 2247435 2529427 := bstep (se 1 (by rfl) ⟨1897070, by rfl⟩ : syracuseStep 2529427 = 3794141) B3794141
theorem B3372569 : Blo 2247435 3372569 := bstep (se 2 (by rfl) ⟨1264713, by rfl⟩ : syracuseStep 3372569 = 2529427) B2529427
theorem B2248379 : Blo 2247435 2248379 := bstep (se 1 (by rfl) ⟨1686284, by rfl⟩ : syracuseStep 2248379 = 3372569) B3372569
theorem B4326653 : Blo 2247435 4326653 := bbase (se 3 (by rfl) ⟨811247, by rfl⟩ : syracuseStep 4326653 = 1622495) (by norm_num)
theorem B11537741 : Blo 2247435 11537741 := bstep (se 3 (by rfl) ⟨2163326, by rfl⟩ : syracuseStep 11537741 = 4326653) B4326653
theorem B30767309 : Blo 2247435 30767309 := bstep (se 3 (by rfl) ⟨5768870, by rfl⟩ : syracuseStep 30767309 = 11537741) B11537741
theorem B20511539 : Blo 2247435 20511539 := bstep (se 1 (by rfl) ⟨15383654, by rfl⟩ : syracuseStep 20511539 = 30767309) B30767309
theorem B13674359 : Blo 2247435 13674359 := bstep (se 1 (by rfl) ⟨10255769, by rfl⟩ : syracuseStep 13674359 = 20511539) B20511539
theorem B9116239 : Blo 2247435 9116239 := bstep (se 1 (by rfl) ⟨6837179, by rfl⟩ : syracuseStep 9116239 = 13674359) B13674359
theorem B12154985 : Blo 2247435 12154985 := bstep (se 2 (by rfl) ⟨4558119, by rfl⟩ : syracuseStep 12154985 = 9116239) B9116239
theorem B8103323 : Blo 2247435 8103323 := bstep (se 1 (by rfl) ⟨6077492, by rfl⟩ : syracuseStep 8103323 = 12154985) B12154985
theorem B5402215 : Blo 2247435 5402215 := bstep (se 1 (by rfl) ⟨4051661, by rfl⟩ : syracuseStep 5402215 = 8103323) B8103323
theorem B7202953 : Blo 2247435 7202953 := bstep (se 2 (by rfl) ⟨2701107, by rfl⟩ : syracuseStep 7202953 = 5402215) B5402215
theorem B9603937 : Blo 2247435 9603937 := bstep (se 2 (by rfl) ⟨3601476, by rfl⟩ : syracuseStep 9603937 = 7202953) B7202953
theorem B12805249 : Blo 2247435 12805249 := bstep (se 2 (by rfl) ⟨4801968, by rfl⟩ : syracuseStep 12805249 = 9603937) B9603937
theorem B17073665 : Blo 2247435 17073665 := bstep (se 2 (by rfl) ⟨6402624, by rfl⟩ : syracuseStep 17073665 = 12805249) B12805249
theorem B11382443 : Blo 2247435 11382443 := bstep (se 1 (by rfl) ⟨8536832, by rfl⟩ : syracuseStep 11382443 = 17073665) B17073665
theorem B7588295 : Blo 2247435 7588295 := bstep (se 1 (by rfl) ⟨5691221, by rfl⟩ : syracuseStep 7588295 = 11382443) B11382443
theorem B5058863 : Blo 2247435 5058863 := bstep (se 1 (by rfl) ⟨3794147, by rfl⟩ : syracuseStep 5058863 = 7588295) B7588295
theorem B3372575 : Blo 2247435 3372575 := bstep (se 1 (by rfl) ⟨2529431, by rfl⟩ : syracuseStep 3372575 = 5058863) B5058863
theorem B2248383 : Blo 2247435 2248383 := bstep (se 1 (by rfl) ⟨1686287, by rfl⟩ : syracuseStep 2248383 = 3372575) B3372575
theorem B3372581 : Blo 2247435 3372581 := bbase (se 4 (by rfl) ⟨316179, by rfl⟩ : syracuseStep 3372581 = 632359) (by norm_num)
theorem B2248387 : Blo 2247435 2248387 := bstep (se 1 (by rfl) ⟨1686290, by rfl⟩ : syracuseStep 2248387 = 3372581) B3372581
theorem B2845621 : Blo 2247435 2845621 := bbase (se 5 (by rfl) ⟨133388, by rfl⟩ : syracuseStep 2845621 = 266777) (by norm_num)
theorem B3794161 : Blo 2247435 3794161 := bstep (se 2 (by rfl) ⟨1422810, by rfl⟩ : syracuseStep 3794161 = 2845621) B2845621
theorem B5058881 : Blo 2247435 5058881 := bstep (se 2 (by rfl) ⟨1897080, by rfl⟩ : syracuseStep 5058881 = 3794161) B3794161
theorem B3372587 : Blo 2247435 3372587 := bstep (se 1 (by rfl) ⟨2529440, by rfl⟩ : syracuseStep 3372587 = 5058881) B5058881
theorem B2248391 : Blo 2247435 2248391 := bstep (se 1 (by rfl) ⟨1686293, by rfl⟩ : syracuseStep 2248391 = 3372587) B3372587
theorem B2529445 : Blo 2247435 2529445 := bbase (se 4 (by rfl) ⟨237135, by rfl⟩ : syracuseStep 2529445 = 474271) (by norm_num)
theorem B3372593 : Blo 2247435 3372593 := bstep (se 2 (by rfl) ⟨1264722, by rfl⟩ : syracuseStep 3372593 = 2529445) B2529445
theorem B2248395 : Blo 2247435 2248395 := bstep (se 1 (by rfl) ⟨1686296, by rfl⟩ : syracuseStep 2248395 = 3372593) B3372593
theorem B15383765 : Blo 2247435 15383765 := bbase (se 7 (by rfl) ⟨180278, by rfl⟩ : syracuseStep 15383765 = 360557) (by norm_num)
theorem B10255843 : Blo 2247435 10255843 := bstep (se 1 (by rfl) ⟨7691882, by rfl⟩ : syracuseStep 10255843 = 15383765) B15383765
theorem B13674457 : Blo 2247435 13674457 := bstep (se 2 (by rfl) ⟨5127921, by rfl⟩ : syracuseStep 13674457 = 10255843) B10255843
theorem B18232609 : Blo 2247435 18232609 := bstep (se 2 (by rfl) ⟨6837228, by rfl⟩ : syracuseStep 18232609 = 13674457) B13674457
theorem B24310145 : Blo 2247435 24310145 := bstep (se 2 (by rfl) ⟨9116304, by rfl⟩ : syracuseStep 24310145 = 18232609) B18232609
theorem B16206763 : Blo 2247435 16206763 := bstep (se 1 (by rfl) ⟨12155072, by rfl⟩ : syracuseStep 16206763 = 24310145) B24310145
theorem B21609017 : Blo 2247435 21609017 := bstep (se 2 (by rfl) ⟨8103381, by rfl⟩ : syracuseStep 21609017 = 16206763) B16206763
theorem B14406011 : Blo 2247435 14406011 := bstep (se 1 (by rfl) ⟨10804508, by rfl⟩ : syracuseStep 14406011 = 21609017) B21609017
theorem B9604007 : Blo 2247435 9604007 := bstep (se 1 (by rfl) ⟨7203005, by rfl⟩ : syracuseStep 9604007 = 14406011) B14406011
theorem B6402671 : Blo 2247435 6402671 := bstep (se 1 (by rfl) ⟨4802003, by rfl⟩ : syracuseStep 6402671 = 9604007) B9604007
theorem B4268447 : Blo 2247435 4268447 := bstep (se 1 (by rfl) ⟨3201335, by rfl⟩ : syracuseStep 4268447 = 6402671) B6402671
theorem B2845631 : Blo 2247435 2845631 := bstep (se 1 (by rfl) ⟨2134223, by rfl⟩ : syracuseStep 2845631 = 4268447) B4268447
theorem B7588349 : Blo 2247435 7588349 := bstep (se 3 (by rfl) ⟨1422815, by rfl⟩ : syracuseStep 7588349 = 2845631) B2845631
theorem B5058899 : Blo 2247435 5058899 := bstep (se 1 (by rfl) ⟨3794174, by rfl⟩ : syracuseStep 5058899 = 7588349) B7588349
theorem B3372599 : Blo 2247435 3372599 := bstep (se 1 (by rfl) ⟨2529449, by rfl⟩ : syracuseStep 3372599 = 5058899) B5058899
theorem B2248399 : Blo 2247435 2248399 := bstep (se 1 (by rfl) ⟨1686299, by rfl⟩ : syracuseStep 2248399 = 3372599) B3372599
theorem B3372605 : Blo 2247435 3372605 := bbase (se 3 (by rfl) ⟨632363, by rfl⟩ : syracuseStep 3372605 = 1264727) (by norm_num)
theorem B2248403 : Blo 2247435 2248403 := bstep (se 1 (by rfl) ⟨1686302, by rfl⟩ : syracuseStep 2248403 = 3372605) B3372605
theorem B5058917 : Blo 2247435 5058917 := bbase (se 4 (by rfl) ⟨474273, by rfl⟩ : syracuseStep 5058917 = 948547) (by norm_num)
theorem B3372611 : Blo 2247435 3372611 := bstep (se 1 (by rfl) ⟨2529458, by rfl⟩ : syracuseStep 3372611 = 5058917) B5058917
theorem B2248407 : Blo 2247435 2248407 := bstep (se 1 (by rfl) ⟨1686305, by rfl⟩ : syracuseStep 2248407 = 3372611) B3372611
theorem B5691293 : Blo 2247435 5691293 := bbase (se 3 (by rfl) ⟨1067117, by rfl⟩ : syracuseStep 5691293 = 2134235) (by norm_num)
theorem B3794195 : Blo 2247435 3794195 := bstep (se 1 (by rfl) ⟨2845646, by rfl⟩ : syracuseStep 3794195 = 5691293) B5691293
theorem B2529463 : Blo 2247435 2529463 := bstep (se 1 (by rfl) ⟨1897097, by rfl⟩ : syracuseStep 2529463 = 3794195) B3794195
theorem B3372617 : Blo 2247435 3372617 := bstep (se 2 (by rfl) ⟨1264731, by rfl⟩ : syracuseStep 3372617 = 2529463) B2529463
theorem B2248411 : Blo 2247435 2248411 := bstep (se 1 (by rfl) ⟨1686308, by rfl⟩ : syracuseStep 2248411 = 3372617) B3372617
theorem B4268477 : Blo 2247435 4268477 := bbase (se 3 (by rfl) ⟨800339, by rfl⟩ : syracuseStep 4268477 = 1600679) (by norm_num)
theorem B11382605 : Blo 2247435 11382605 := bstep (se 3 (by rfl) ⟨2134238, by rfl⟩ : syracuseStep 11382605 = 4268477) B4268477
theorem B7588403 : Blo 2247435 7588403 := bstep (se 1 (by rfl) ⟨5691302, by rfl⟩ : syracuseStep 7588403 = 11382605) B11382605
theorem B5058935 : Blo 2247435 5058935 := bstep (se 1 (by rfl) ⟨3794201, by rfl⟩ : syracuseStep 5058935 = 7588403) B7588403
theorem B3372623 : Blo 2247435 3372623 := bstep (se 1 (by rfl) ⟨2529467, by rfl⟩ : syracuseStep 3372623 = 5058935) B5058935
theorem B2248415 : Blo 2247435 2248415 := bstep (se 1 (by rfl) ⟨1686311, by rfl⟩ : syracuseStep 2248415 = 3372623) B3372623
theorem B3372629 : Blo 2247435 3372629 := bbase (se 8 (by rfl) ⟨19761, by rfl⟩ : syracuseStep 3372629 = 39523) (by norm_num)
theorem B2248419 : Blo 2247435 2248419 := bstep (se 1 (by rfl) ⟨1686314, by rfl⟩ : syracuseStep 2248419 = 3372629) B3372629
theorem B3601541 : Blo 2247435 3601541 := bbase (se 4 (by rfl) ⟨337644, by rfl⟩ : syracuseStep 3601541 = 675289) (by norm_num)
theorem B9604109 : Blo 2247435 9604109 := bstep (se 3 (by rfl) ⟨1800770, by rfl⟩ : syracuseStep 9604109 = 3601541) B3601541
theorem B6402739 : Blo 2247435 6402739 := bstep (se 1 (by rfl) ⟨4802054, by rfl⟩ : syracuseStep 6402739 = 9604109) B9604109
theorem B8536985 : Blo 2247435 8536985 := bstep (se 2 (by rfl) ⟨3201369, by rfl⟩ : syracuseStep 8536985 = 6402739) B6402739
theorem B5691323 : Blo 2247435 5691323 := bstep (se 1 (by rfl) ⟨4268492, by rfl⟩ : syracuseStep 5691323 = 8536985) B8536985
theorem B3794215 : Blo 2247435 3794215 := bstep (se 1 (by rfl) ⟨2845661, by rfl⟩ : syracuseStep 3794215 = 5691323) B5691323
theorem B5058953 : Blo 2247435 5058953 := bstep (se 2 (by rfl) ⟨1897107, by rfl⟩ : syracuseStep 5058953 = 3794215) B3794215
theorem B3372635 : Blo 2247435 3372635 := bstep (se 1 (by rfl) ⟨2529476, by rfl⟩ : syracuseStep 3372635 = 5058953) B5058953
theorem B2248423 : Blo 2247435 2248423 := bstep (se 1 (by rfl) ⟨1686317, by rfl⟩ : syracuseStep 2248423 = 3372635) B3372635
theorem B2529481 : Blo 2247435 2529481 := bbase (se 2 (by rfl) ⟨948555, by rfl⟩ : syracuseStep 2529481 = 1897111) (by norm_num)
theorem B3372641 : Blo 2247435 3372641 := bstep (se 2 (by rfl) ⟨1264740, by rfl⟩ : syracuseStep 3372641 = 2529481) B2529481
theorem B2248427 : Blo 2247435 2248427 := bstep (se 1 (by rfl) ⟨1686320, by rfl⟩ : syracuseStep 2248427 = 3372641) B3372641
theorem B10804661 : Blo 2247435 10804661 := bbase (se 5 (by rfl) ⟨506468, by rfl⟩ : syracuseStep 10804661 = 1012937) (by norm_num)
theorem B7203107 : Blo 2247435 7203107 := bstep (se 1 (by rfl) ⟨5402330, by rfl⟩ : syracuseStep 7203107 = 10804661) B10804661
theorem B19208285 : Blo 2247435 19208285 := bstep (se 3 (by rfl) ⟨3601553, by rfl⟩ : syracuseStep 19208285 = 7203107) B7203107
theorem B12805523 : Blo 2247435 12805523 := bstep (se 1 (by rfl) ⟨9604142, by rfl⟩ : syracuseStep 12805523 = 19208285) B19208285
theorem B8537015 : Blo 2247435 8537015 := bstep (se 1 (by rfl) ⟨6402761, by rfl⟩ : syracuseStep 8537015 = 12805523) B12805523
theorem B5691343 : Blo 2247435 5691343 := bstep (se 1 (by rfl) ⟨4268507, by rfl⟩ : syracuseStep 5691343 = 8537015) B8537015
theorem B7588457 : Blo 2247435 7588457 := bstep (se 2 (by rfl) ⟨2845671, by rfl⟩ : syracuseStep 7588457 = 5691343) B5691343
theorem B5058971 : Blo 2247435 5058971 := bstep (se 1 (by rfl) ⟨3794228, by rfl⟩ : syracuseStep 5058971 = 7588457) B7588457
theorem B3372647 : Blo 2247435 3372647 := bstep (se 1 (by rfl) ⟨2529485, by rfl⟩ : syracuseStep 3372647 = 5058971) B5058971
theorem B2248431 : Blo 2247435 2248431 := bstep (se 1 (by rfl) ⟨1686323, by rfl⟩ : syracuseStep 2248431 = 3372647) B3372647
theorem B3372653 : Blo 2247435 3372653 := bbase (se 3 (by rfl) ⟨632372, by rfl⟩ : syracuseStep 3372653 = 1264745) (by norm_num)
theorem B2248435 : Blo 2247435 2248435 := bstep (se 1 (by rfl) ⟨1686326, by rfl⟩ : syracuseStep 2248435 = 3372653) B3372653
theorem B5058989 : Blo 2247435 5058989 := bbase (se 3 (by rfl) ⟨948560, by rfl⟩ : syracuseStep 5058989 = 1897121) (by norm_num)
theorem B3372659 : Blo 2247435 3372659 := bstep (se 1 (by rfl) ⟨2529494, by rfl⟩ : syracuseStep 3372659 = 5058989) B5058989
theorem B2248439 : Blo 2247435 2248439 := bstep (se 1 (by rfl) ⟨1686329, by rfl⟩ : syracuseStep 2248439 = 3372659) B3372659
theorem B2401049 : Blo 2247435 2401049 := bbase (se 2 (by rfl) ⟨900393, by rfl⟩ : syracuseStep 2401049 = 1800787) (by norm_num)
theorem B6402797 : Blo 2247435 6402797 := bstep (se 3 (by rfl) ⟨1200524, by rfl⟩ : syracuseStep 6402797 = 2401049) B2401049
theorem B4268531 : Blo 2247435 4268531 := bstep (se 1 (by rfl) ⟨3201398, by rfl⟩ : syracuseStep 4268531 = 6402797) B6402797
theorem B2845687 : Blo 2247435 2845687 := bstep (se 1 (by rfl) ⟨2134265, by rfl⟩ : syracuseStep 2845687 = 4268531) B4268531
theorem B3794249 : Blo 2247435 3794249 := bstep (se 2 (by rfl) ⟨1422843, by rfl⟩ : syracuseStep 3794249 = 2845687) B2845687
theorem B2529499 : Blo 2247435 2529499 := bstep (se 1 (by rfl) ⟨1897124, by rfl⟩ : syracuseStep 2529499 = 3794249) B3794249
theorem B3372665 : Blo 2247435 3372665 := bstep (se 2 (by rfl) ⟨1264749, by rfl⟩ : syracuseStep 3372665 = 2529499) B2529499
theorem B2248443 : Blo 2247435 2248443 := bstep (se 1 (by rfl) ⟨1686332, by rfl⟩ : syracuseStep 2248443 = 3372665) B3372665
theorem B6490165 : Blo 2247435 6490165 := bbase (se 5 (by rfl) ⟨304226, by rfl⟩ : syracuseStep 6490165 = 608453) (by norm_num)
theorem B8653553 : Blo 2247435 8653553 := bstep (se 2 (by rfl) ⟨3245082, by rfl⟩ : syracuseStep 8653553 = 6490165) B6490165
theorem B5769035 : Blo 2247435 5769035 := bstep (se 1 (by rfl) ⟨4326776, by rfl⟩ : syracuseStep 5769035 = 8653553) B8653553
theorem B3846023 : Blo 2247435 3846023 := bstep (se 1 (by rfl) ⟨2884517, by rfl⟩ : syracuseStep 3846023 = 5769035) B5769035
theorem B2564015 : Blo 2247435 2564015 := bstep (se 1 (by rfl) ⟨1923011, by rfl⟩ : syracuseStep 2564015 = 3846023) B3846023
theorem B6837373 : Blo 2247435 6837373 := bstep (se 3 (by rfl) ⟨1282007, by rfl⟩ : syracuseStep 6837373 = 2564015) B2564015
theorem B9116497 : Blo 2247435 9116497 := bstep (se 2 (by rfl) ⟨3418686, by rfl⟩ : syracuseStep 9116497 = 6837373) B6837373
theorem B12155329 : Blo 2247435 12155329 := bstep (se 2 (by rfl) ⟨4558248, by rfl⟩ : syracuseStep 12155329 = 9116497) B9116497
theorem B64828421 : Blo 2247435 64828421 := bstep (se 4 (by rfl) ⟨6077664, by rfl⟩ : syracuseStep 64828421 = 12155329) B12155329
theorem B43218947 : Blo 2247435 43218947 := bstep (se 1 (by rfl) ⟨32414210, by rfl⟩ : syracuseStep 43218947 = 64828421) B64828421
theorem B28812631 : Blo 2247435 28812631 := bstep (se 1 (by rfl) ⟨21609473, by rfl⟩ : syracuseStep 28812631 = 43218947) B43218947
theorem B38416841 : Blo 2247435 38416841 := bstep (se 2 (by rfl) ⟨14406315, by rfl⟩ : syracuseStep 38416841 = 28812631) B28812631
theorem B25611227 : Blo 2247435 25611227 := bstep (se 1 (by rfl) ⟨19208420, by rfl⟩ : syracuseStep 25611227 = 38416841) B38416841
theorem B17074151 : Blo 2247435 17074151 := bstep (se 1 (by rfl) ⟨12805613, by rfl⟩ : syracuseStep 17074151 = 25611227) B25611227
theorem B11382767 : Blo 2247435 11382767 := bstep (se 1 (by rfl) ⟨8537075, by rfl⟩ : syracuseStep 11382767 = 17074151) B17074151
theorem B7588511 : Blo 2247435 7588511 := bstep (se 1 (by rfl) ⟨5691383, by rfl⟩ : syracuseStep 7588511 = 11382767) B11382767
theorem B5059007 : Blo 2247435 5059007 := bstep (se 1 (by rfl) ⟨3794255, by rfl⟩ : syracuseStep 5059007 = 7588511) B7588511
theorem B3372671 : Blo 2247435 3372671 := bstep (se 1 (by rfl) ⟨2529503, by rfl⟩ : syracuseStep 3372671 = 5059007) B5059007
theorem B2248447 : Blo 2247435 2248447 := bstep (se 1 (by rfl) ⟨1686335, by rfl⟩ : syracuseStep 2248447 = 3372671) B3372671
theorem B3372677 : Blo 2247435 3372677 := bbase (se 4 (by rfl) ⟨316188, by rfl⟩ : syracuseStep 3372677 = 632377) (by norm_num)
theorem B2248451 : Blo 2247435 2248451 := bstep (se 1 (by rfl) ⟨1686338, by rfl⟩ : syracuseStep 2248451 = 3372677) B3372677
theorem B3794269 : Blo 2247435 3794269 := bbase (se 3 (by rfl) ⟨711425, by rfl⟩ : syracuseStep 3794269 = 1422851) (by norm_num)
theorem B5059025 : Blo 2247435 5059025 := bstep (se 2 (by rfl) ⟨1897134, by rfl⟩ : syracuseStep 5059025 = 3794269) B3794269
theorem B3372683 : Blo 2247435 3372683 := bstep (se 1 (by rfl) ⟨2529512, by rfl⟩ : syracuseStep 3372683 = 5059025) B5059025
theorem B2248455 : Blo 2247435 2248455 := bstep (se 1 (by rfl) ⟨1686341, by rfl⟩ : syracuseStep 2248455 = 3372683) B3372683
theorem B2529517 : Blo 2247435 2529517 := bbase (se 3 (by rfl) ⟨474284, by rfl⟩ : syracuseStep 2529517 = 948569) (by norm_num)
theorem B3372689 : Blo 2247435 3372689 := bstep (se 2 (by rfl) ⟨1264758, by rfl⟩ : syracuseStep 3372689 = 2529517) B2529517
theorem B2248459 : Blo 2247435 2248459 := bstep (se 1 (by rfl) ⟨1686344, by rfl⟩ : syracuseStep 2248459 = 3372689) B3372689
theorem B7588565 : Blo 2247435 7588565 := bbase (se 7 (by rfl) ⟨88928, by rfl⟩ : syracuseStep 7588565 = 177857) (by norm_num)
theorem B5059043 : Blo 2247435 5059043 := bstep (se 1 (by rfl) ⟨3794282, by rfl⟩ : syracuseStep 5059043 = 7588565) B7588565
theorem B3372695 : Blo 2247435 3372695 := bstep (se 1 (by rfl) ⟨2529521, by rfl⟩ : syracuseStep 3372695 = 5059043) B5059043
theorem B2248463 : Blo 2247435 2248463 := bstep (se 1 (by rfl) ⟨1686347, by rfl⟩ : syracuseStep 2248463 = 3372695) B3372695
theorem B3372701 : Blo 2247435 3372701 := bbase (se 3 (by rfl) ⟨632381, by rfl⟩ : syracuseStep 3372701 = 1264763) (by norm_num)
theorem B2248467 : Blo 2247435 2248467 := bstep (se 1 (by rfl) ⟨1686350, by rfl⟩ : syracuseStep 2248467 = 3372701) B3372701
theorem B5059061 : Blo 2247435 5059061 := bbase (se 5 (by rfl) ⟨237143, by rfl⟩ : syracuseStep 5059061 = 474287) (by norm_num)
theorem B3372707 : Blo 2247435 3372707 := bstep (se 1 (by rfl) ⟨2529530, by rfl⟩ : syracuseStep 3372707 = 5059061) B5059061
theorem B2248471 : Blo 2247435 2248471 := bstep (se 1 (by rfl) ⟨1686353, by rfl⟩ : syracuseStep 2248471 = 3372707) B3372707
theorem B25960981 : Blo 2247435 25960981 := bbase (se 6 (by rfl) ⟨608460, by rfl⟩ : syracuseStep 25960981 = 1216921) (by norm_num)
theorem B34614641 : Blo 2247435 34614641 := bstep (se 2 (by rfl) ⟨12980490, by rfl⟩ : syracuseStep 34614641 = 25960981) B25960981
theorem B23076427 : Blo 2247435 23076427 := bstep (se 1 (by rfl) ⟨17307320, by rfl⟩ : syracuseStep 23076427 = 34614641) B34614641
theorem B30768569 : Blo 2247435 30768569 := bstep (se 2 (by rfl) ⟨11538213, by rfl⟩ : syracuseStep 30768569 = 23076427) B23076427
theorem B20512379 : Blo 2247435 20512379 := bstep (se 1 (by rfl) ⟨15384284, by rfl⟩ : syracuseStep 20512379 = 30768569) B30768569
theorem B13674919 : Blo 2247435 13674919 := bstep (se 1 (by rfl) ⟨10256189, by rfl⟩ : syracuseStep 13674919 = 20512379) B20512379
theorem B18233225 : Blo 2247435 18233225 := bstep (se 2 (by rfl) ⟨6837459, by rfl⟩ : syracuseStep 18233225 = 13674919) B13674919
theorem B12155483 : Blo 2247435 12155483 := bstep (se 1 (by rfl) ⟨9116612, by rfl⟩ : syracuseStep 12155483 = 18233225) B18233225
theorem B8103655 : Blo 2247435 8103655 := bstep (se 1 (by rfl) ⟨6077741, by rfl⟩ : syracuseStep 8103655 = 12155483) B12155483
theorem B43219493 : Blo 2247435 43219493 := bstep (se 4 (by rfl) ⟨4051827, by rfl⟩ : syracuseStep 43219493 = 8103655) B8103655
theorem B28812995 : Blo 2247435 28812995 := bstep (se 1 (by rfl) ⟨21609746, by rfl⟩ : syracuseStep 28812995 = 43219493) B43219493
theorem B19208663 : Blo 2247435 19208663 := bstep (se 1 (by rfl) ⟨14406497, by rfl⟩ : syracuseStep 19208663 = 28812995) B28812995
theorem B12805775 : Blo 2247435 12805775 := bstep (se 1 (by rfl) ⟨9604331, by rfl⟩ : syracuseStep 12805775 = 19208663) B19208663
theorem B8537183 : Blo 2247435 8537183 := bstep (se 1 (by rfl) ⟨6402887, by rfl⟩ : syracuseStep 8537183 = 12805775) B12805775
theorem B5691455 : Blo 2247435 5691455 := bstep (se 1 (by rfl) ⟨4268591, by rfl⟩ : syracuseStep 5691455 = 8537183) B8537183
theorem B3794303 : Blo 2247435 3794303 := bstep (se 1 (by rfl) ⟨2845727, by rfl⟩ : syracuseStep 3794303 = 5691455) B5691455
theorem B2529535 : Blo 2247435 2529535 := bstep (se 1 (by rfl) ⟨1897151, by rfl⟩ : syracuseStep 2529535 = 3794303) B3794303
theorem B3372713 : Blo 2247435 3372713 := bstep (se 2 (by rfl) ⟨1264767, by rfl⟩ : syracuseStep 3372713 = 2529535) B2529535
theorem B2248475 : Blo 2247435 2248475 := bstep (se 1 (by rfl) ⟨1686356, by rfl⟩ : syracuseStep 2248475 = 3372713) B3372713
theorem B3289405 : Blo 2247435 3289405 := bbase (se 3 (by rfl) ⟨616763, by rfl⟩ : syracuseStep 3289405 = 1233527) (by norm_num)
theorem B4385873 : Blo 2247435 4385873 := bstep (se 2 (by rfl) ⟨1644702, by rfl⟩ : syracuseStep 4385873 = 3289405) B3289405
theorem B11695661 : Blo 2247435 11695661 := bstep (se 3 (by rfl) ⟨2192936, by rfl⟩ : syracuseStep 11695661 = 4385873) B4385873
theorem B7797107 : Blo 2247435 7797107 := bstep (se 1 (by rfl) ⟨5847830, by rfl⟩ : syracuseStep 7797107 = 11695661) B11695661
theorem B20792285 : Blo 2247435 20792285 := bstep (se 3 (by rfl) ⟨3898553, by rfl⟩ : syracuseStep 20792285 = 7797107) B7797107
theorem B13861523 : Blo 2247435 13861523 := bstep (se 1 (by rfl) ⟨10396142, by rfl⟩ : syracuseStep 13861523 = 20792285) B20792285
theorem B9241015 : Blo 2247435 9241015 := bstep (se 1 (by rfl) ⟨6930761, by rfl⟩ : syracuseStep 9241015 = 13861523) B13861523
theorem B12321353 : Blo 2247435 12321353 := bstep (se 2 (by rfl) ⟨4620507, by rfl⟩ : syracuseStep 12321353 = 9241015) B9241015
theorem B32856941 : Blo 2247435 32856941 := bstep (se 3 (by rfl) ⟨6160676, by rfl⟩ : syracuseStep 32856941 = 12321353) B12321353
theorem B21904627 : Blo 2247435 21904627 := bstep (se 1 (by rfl) ⟨16428470, by rfl⟩ : syracuseStep 21904627 = 32856941) B32856941
theorem B29206169 : Blo 2247435 29206169 := bstep (se 2 (by rfl) ⟨10952313, by rfl⟩ : syracuseStep 29206169 = 21904627) B21904627
theorem B19470779 : Blo 2247435 19470779 := bstep (se 1 (by rfl) ⟨14603084, by rfl⟩ : syracuseStep 19470779 = 29206169) B29206169
theorem B12980519 : Blo 2247435 12980519 := bstep (se 1 (by rfl) ⟨9735389, by rfl⟩ : syracuseStep 12980519 = 19470779) B19470779
theorem B8653679 : Blo 2247435 8653679 := bstep (se 1 (by rfl) ⟨6490259, by rfl⟩ : syracuseStep 8653679 = 12980519) B12980519
theorem B5769119 : Blo 2247435 5769119 := bstep (se 1 (by rfl) ⟨4326839, by rfl⟩ : syracuseStep 5769119 = 8653679) B8653679
theorem B3846079 : Blo 2247435 3846079 := bstep (se 1 (by rfl) ⟨2884559, by rfl⟩ : syracuseStep 3846079 = 5769119) B5769119
theorem B5128105 : Blo 2247435 5128105 := bstep (se 2 (by rfl) ⟨1923039, by rfl⟩ : syracuseStep 5128105 = 3846079) B3846079
theorem B6837473 : Blo 2247435 6837473 := bstep (se 2 (by rfl) ⟨2564052, by rfl⟩ : syracuseStep 6837473 = 5128105) B5128105
theorem B18233261 : Blo 2247435 18233261 := bstep (se 3 (by rfl) ⟨3418736, by rfl⟩ : syracuseStep 18233261 = 6837473) B6837473
theorem B12155507 : Blo 2247435 12155507 := bstep (se 1 (by rfl) ⟨9116630, by rfl⟩ : syracuseStep 12155507 = 18233261) B18233261
theorem B8103671 : Blo 2247435 8103671 := bstep (se 1 (by rfl) ⟨6077753, by rfl⟩ : syracuseStep 8103671 = 12155507) B12155507
theorem B5402447 : Blo 2247435 5402447 := bstep (se 1 (by rfl) ⟨4051835, by rfl⟩ : syracuseStep 5402447 = 8103671) B8103671
theorem B3601631 : Blo 2247435 3601631 := bstep (se 1 (by rfl) ⟨2701223, by rfl⟩ : syracuseStep 3601631 = 5402447) B5402447
theorem B2401087 : Blo 2247435 2401087 := bstep (se 1 (by rfl) ⟨1800815, by rfl⟩ : syracuseStep 2401087 = 3601631) B3601631
theorem B3201449 : Blo 2247435 3201449 := bstep (se 2 (by rfl) ⟨1200543, by rfl⟩ : syracuseStep 3201449 = 2401087) B2401087
theorem B8537197 : Blo 2247435 8537197 := bstep (se 3 (by rfl) ⟨1600724, by rfl⟩ : syracuseStep 8537197 = 3201449) B3201449
theorem B11382929 : Blo 2247435 11382929 := bstep (se 2 (by rfl) ⟨4268598, by rfl⟩ : syracuseStep 11382929 = 8537197) B8537197
theorem B7588619 : Blo 2247435 7588619 := bstep (se 1 (by rfl) ⟨5691464, by rfl⟩ : syracuseStep 7588619 = 11382929) B11382929
theorem B5059079 : Blo 2247435 5059079 := bstep (se 1 (by rfl) ⟨3794309, by rfl⟩ : syracuseStep 5059079 = 7588619) B7588619
theorem B3372719 : Blo 2247435 3372719 := bstep (se 1 (by rfl) ⟨2529539, by rfl⟩ : syracuseStep 3372719 = 5059079) B5059079
theorem B2248479 : Blo 2247435 2248479 := bstep (se 1 (by rfl) ⟨1686359, by rfl⟩ : syracuseStep 2248479 = 3372719) B3372719
theorem B3372725 : Blo 2247435 3372725 := bbase (se 5 (by rfl) ⟨158096, by rfl⟩ : syracuseStep 3372725 = 316193) (by norm_num)
theorem B2248483 : Blo 2247435 2248483 := bstep (se 1 (by rfl) ⟨1686362, by rfl⟩ : syracuseStep 2248483 = 3372725) B3372725
theorem B5691485 : Blo 2247435 5691485 := bbase (se 3 (by rfl) ⟨1067153, by rfl⟩ : syracuseStep 5691485 = 2134307) (by norm_num)
theorem B3794323 : Blo 2247435 3794323 := bstep (se 1 (by rfl) ⟨2845742, by rfl⟩ : syracuseStep 3794323 = 5691485) B5691485
theorem B5059097 : Blo 2247435 5059097 := bstep (se 2 (by rfl) ⟨1897161, by rfl⟩ : syracuseStep 5059097 = 3794323) B3794323
theorem B3372731 : Blo 2247435 3372731 := bstep (se 1 (by rfl) ⟨2529548, by rfl⟩ : syracuseStep 3372731 = 5059097) B5059097
theorem B2248487 : Blo 2247435 2248487 := bstep (se 1 (by rfl) ⟨1686365, by rfl⟩ : syracuseStep 2248487 = 3372731) B3372731
theorem B2529553 : Blo 2247435 2529553 := bbase (se 2 (by rfl) ⟨948582, by rfl⟩ : syracuseStep 2529553 = 1897165) (by norm_num)
theorem B3372737 : Blo 2247435 3372737 := bstep (se 2 (by rfl) ⟨1264776, by rfl⟩ : syracuseStep 3372737 = 2529553) B2529553
theorem B2248491 : Blo 2247435 2248491 := bstep (se 1 (by rfl) ⟨1686368, by rfl⟩ : syracuseStep 2248491 = 3372737) B3372737
theorem B4268629 : Blo 2247435 4268629 := bbase (se 8 (by rfl) ⟨25011, by rfl⟩ : syracuseStep 4268629 = 50023) (by norm_num)
theorem B5691505 : Blo 2247435 5691505 := bstep (se 2 (by rfl) ⟨2134314, by rfl⟩ : syracuseStep 5691505 = 4268629) B4268629
theorem B7588673 : Blo 2247435 7588673 := bstep (se 2 (by rfl) ⟨2845752, by rfl⟩ : syracuseStep 7588673 = 5691505) B5691505
theorem B5059115 : Blo 2247435 5059115 := bstep (se 1 (by rfl) ⟨3794336, by rfl⟩ : syracuseStep 5059115 = 7588673) B7588673
theorem B3372743 : Blo 2247435 3372743 := bstep (se 1 (by rfl) ⟨2529557, by rfl⟩ : syracuseStep 3372743 = 5059115) B5059115
theorem B2248495 : Blo 2247435 2248495 := bstep (se 1 (by rfl) ⟨1686371, by rfl⟩ : syracuseStep 2248495 = 3372743) B3372743
theorem B3372749 : Blo 2247435 3372749 := bbase (se 3 (by rfl) ⟨632390, by rfl⟩ : syracuseStep 3372749 = 1264781) (by norm_num)
theorem B2248499 : Blo 2247435 2248499 := bstep (se 1 (by rfl) ⟨1686374, by rfl⟩ : syracuseStep 2248499 = 3372749) B3372749
theorem B5059133 : Blo 2247435 5059133 := bbase (se 3 (by rfl) ⟨948587, by rfl⟩ : syracuseStep 5059133 = 1897175) (by norm_num)
theorem B3372755 : Blo 2247435 3372755 := bstep (se 1 (by rfl) ⟨2529566, by rfl⟩ : syracuseStep 3372755 = 5059133) B5059133
theorem B2248503 : Blo 2247435 2248503 := bstep (se 1 (by rfl) ⟨1686377, by rfl⟩ : syracuseStep 2248503 = 3372755) B3372755
theorem B3794357 : Blo 2247435 3794357 := bbase (se 5 (by rfl) ⟨177860, by rfl⟩ : syracuseStep 3794357 = 355721) (by norm_num)
theorem B2529571 : Blo 2247435 2529571 := bstep (se 1 (by rfl) ⟨1897178, by rfl⟩ : syracuseStep 2529571 = 3794357) B3794357
theorem B3372761 : Blo 2247435 3372761 := bstep (se 2 (by rfl) ⟨1264785, by rfl⟩ : syracuseStep 3372761 = 2529571) B2529571
theorem B2248507 : Blo 2247435 2248507 := bstep (se 1 (by rfl) ⟨1686380, by rfl⟩ : syracuseStep 2248507 = 3372761) B3372761
theorem B2401121 : Blo 2247435 2401121 := bbase (se 2 (by rfl) ⟨900420, by rfl⟩ : syracuseStep 2401121 = 1800841) (by norm_num)
theorem B6402989 : Blo 2247435 6402989 := bstep (se 3 (by rfl) ⟨1200560, by rfl⟩ : syracuseStep 6402989 = 2401121) B2401121
theorem B17074637 : Blo 2247435 17074637 := bstep (se 3 (by rfl) ⟨3201494, by rfl⟩ : syracuseStep 17074637 = 6402989) B6402989
theorem B11383091 : Blo 2247435 11383091 := bstep (se 1 (by rfl) ⟨8537318, by rfl⟩ : syracuseStep 11383091 = 17074637) B17074637
theorem B7588727 : Blo 2247435 7588727 := bstep (se 1 (by rfl) ⟨5691545, by rfl⟩ : syracuseStep 7588727 = 11383091) B11383091
theorem B5059151 : Blo 2247435 5059151 := bstep (se 1 (by rfl) ⟨3794363, by rfl⟩ : syracuseStep 5059151 = 7588727) B7588727
theorem B3372767 : Blo 2247435 3372767 := bstep (se 1 (by rfl) ⟨2529575, by rfl⟩ : syracuseStep 3372767 = 5059151) B5059151
theorem B2248511 : Blo 2247435 2248511 := bstep (se 1 (by rfl) ⟨1686383, by rfl⟩ : syracuseStep 2248511 = 3372767) B3372767
theorem B3372773 : Blo 2247435 3372773 := bbase (se 4 (by rfl) ⟨316197, by rfl⟩ : syracuseStep 3372773 = 632395) (by norm_num)
theorem B2248515 : Blo 2247435 2248515 := bstep (se 1 (by rfl) ⟨1686386, by rfl⟩ : syracuseStep 2248515 = 3372773) B3372773
theorem B6403013 : Blo 2247435 6403013 := bbase (se 4 (by rfl) ⟨600282, by rfl⟩ : syracuseStep 6403013 = 1200565) (by norm_num)
theorem B4268675 : Blo 2247435 4268675 := bstep (se 1 (by rfl) ⟨3201506, by rfl⟩ : syracuseStep 4268675 = 6403013) B6403013
theorem B2845783 : Blo 2247435 2845783 := bstep (se 1 (by rfl) ⟨2134337, by rfl⟩ : syracuseStep 2845783 = 4268675) B4268675
theorem B3794377 : Blo 2247435 3794377 := bstep (se 2 (by rfl) ⟨1422891, by rfl⟩ : syracuseStep 3794377 = 2845783) B2845783
theorem B5059169 : Blo 2247435 5059169 := bstep (se 2 (by rfl) ⟨1897188, by rfl⟩ : syracuseStep 5059169 = 3794377) B3794377
theorem B3372779 : Blo 2247435 3372779 := bstep (se 1 (by rfl) ⟨2529584, by rfl⟩ : syracuseStep 3372779 = 5059169) B5059169
theorem B2248519 : Blo 2247435 2248519 := bstep (se 1 (by rfl) ⟨1686389, by rfl⟩ : syracuseStep 2248519 = 3372779) B3372779
theorem B2529589 : Blo 2247435 2529589 := bbase (se 5 (by rfl) ⟨118574, by rfl⟩ : syracuseStep 2529589 = 237149) (by norm_num)
theorem B3372785 : Blo 2247435 3372785 := bstep (se 2 (by rfl) ⟨1264794, by rfl⟩ : syracuseStep 3372785 = 2529589) B2529589
theorem B2248523 : Blo 2247435 2248523 := bstep (se 1 (by rfl) ⟨1686392, by rfl⟩ : syracuseStep 2248523 = 3372785) B3372785
theorem B2845793 : Blo 2247435 2845793 := bbase (se 2 (by rfl) ⟨1067172, by rfl⟩ : syracuseStep 2845793 = 2134345) (by norm_num)
theorem B7588781 : Blo 2247435 7588781 := bstep (se 3 (by rfl) ⟨1422896, by rfl⟩ : syracuseStep 7588781 = 2845793) B2845793
theorem B5059187 : Blo 2247435 5059187 := bstep (se 1 (by rfl) ⟨3794390, by rfl⟩ : syracuseStep 5059187 = 7588781) B7588781
theorem B3372791 : Blo 2247435 3372791 := bstep (se 1 (by rfl) ⟨2529593, by rfl⟩ : syracuseStep 3372791 = 5059187) B5059187
theorem B2248527 : Blo 2247435 2248527 := bstep (se 1 (by rfl) ⟨1686395, by rfl⟩ : syracuseStep 2248527 = 3372791) B3372791
theorem B3372797 : Blo 2247435 3372797 := bbase (se 3 (by rfl) ⟨632399, by rfl⟩ : syracuseStep 3372797 = 1264799) (by norm_num)
theorem B2248531 : Blo 2247435 2248531 := bstep (se 1 (by rfl) ⟨1686398, by rfl⟩ : syracuseStep 2248531 = 3372797) B3372797
theorem B5059205 : Blo 2247435 5059205 := bbase (se 4 (by rfl) ⟨474300, by rfl⟩ : syracuseStep 5059205 = 948601) (by norm_num)
theorem B3372803 : Blo 2247435 3372803 := bstep (se 1 (by rfl) ⟨2529602, by rfl⟩ : syracuseStep 3372803 = 5059205) B5059205
theorem B2248535 : Blo 2247435 2248535 := bstep (se 1 (by rfl) ⟨1686401, by rfl⟩ : syracuseStep 2248535 = 3372803) B3372803
theorem B6668741 : Blo 2247435 6668741 := bbase (se 4 (by rfl) ⟨625194, by rfl⟩ : syracuseStep 6668741 = 1250389) (by norm_num)
theorem B17783309 : Blo 2247435 17783309 := bstep (se 3 (by rfl) ⟨3334370, by rfl⟩ : syracuseStep 17783309 = 6668741) B6668741
theorem B47422157 : Blo 2247435 47422157 := bstep (se 3 (by rfl) ⟨8891654, by rfl⟩ : syracuseStep 47422157 = 17783309) B17783309
theorem B126459085 : Blo 2247435 126459085 := bstep (se 3 (by rfl) ⟨23711078, by rfl⟩ : syracuseStep 126459085 = 47422157) B47422157
theorem B168612113 : Blo 2247435 168612113 := bstep (se 2 (by rfl) ⟨63229542, by rfl⟩ : syracuseStep 168612113 = 126459085) B126459085
theorem B449632301 : Blo 2247435 449632301 := bstep (se 3 (by rfl) ⟨84306056, by rfl⟩ : syracuseStep 449632301 = 168612113) B168612113
theorem B1199019469 : Blo 2247435 1199019469 := bstep (se 3 (by rfl) ⟨224816150, by rfl⟩ : syracuseStep 1199019469 = 449632301) B449632301
theorem B1598692625 : Blo 2247435 1598692625 := bstep (se 2 (by rfl) ⟨599509734, by rfl⟩ : syracuseStep 1598692625 = 1199019469) B1199019469
theorem B1065795083 : Blo 2247435 1065795083 := bstep (se 1 (by rfl) ⟨799346312, by rfl⟩ : syracuseStep 1065795083 = 1598692625) B1598692625
theorem B710530055 : Blo 2247435 710530055 := bstep (se 1 (by rfl) ⟨532897541, by rfl⟩ : syracuseStep 710530055 = 1065795083) B1065795083
theorem B473686703 : Blo 2247435 473686703 := bstep (se 1 (by rfl) ⟨355265027, by rfl⟩ : syracuseStep 473686703 = 710530055) B710530055
theorem B315791135 : Blo 2247435 315791135 := bstep (se 1 (by rfl) ⟨236843351, by rfl⟩ : syracuseStep 315791135 = 473686703) B473686703
theorem B210527423 : Blo 2247435 210527423 := bstep (se 1 (by rfl) ⟨157895567, by rfl⟩ : syracuseStep 210527423 = 315791135) B315791135
theorem B140351615 : Blo 2247435 140351615 := bstep (se 1 (by rfl) ⟨105263711, by rfl⟩ : syracuseStep 140351615 = 210527423) B210527423
theorem B93567743 : Blo 2247435 93567743 := bstep (se 1 (by rfl) ⟨70175807, by rfl⟩ : syracuseStep 93567743 = 140351615) B140351615
theorem B62378495 : Blo 2247435 62378495 := bstep (se 1 (by rfl) ⟨46783871, by rfl⟩ : syracuseStep 62378495 = 93567743) B93567743
theorem B41585663 : Blo 2247435 41585663 := bstep (se 1 (by rfl) ⟨31189247, by rfl⟩ : syracuseStep 41585663 = 62378495) B62378495
theorem B110895101 : Blo 2247435 110895101 := bstep (se 3 (by rfl) ⟨20792831, by rfl⟩ : syracuseStep 110895101 = 41585663) B41585663
theorem B73930067 : Blo 2247435 73930067 := bstep (se 1 (by rfl) ⟨55447550, by rfl⟩ : syracuseStep 73930067 = 110895101) B110895101
theorem B49286711 : Blo 2247435 49286711 := bstep (se 1 (by rfl) ⟨36965033, by rfl⟩ : syracuseStep 49286711 = 73930067) B73930067
theorem B32857807 : Blo 2247435 32857807 := bstep (se 1 (by rfl) ⟨24643355, by rfl⟩ : syracuseStep 32857807 = 49286711) B49286711
theorem B43810409 : Blo 2247435 43810409 := bstep (se 2 (by rfl) ⟨16428903, by rfl⟩ : syracuseStep 43810409 = 32857807) B32857807
theorem B116827757 : Blo 2247435 116827757 := bstep (se 3 (by rfl) ⟨21905204, by rfl⟩ : syracuseStep 116827757 = 43810409) B43810409
theorem B77885171 : Blo 2247435 77885171 := bstep (se 1 (by rfl) ⟨58413878, by rfl⟩ : syracuseStep 77885171 = 116827757) B116827757
theorem B51923447 : Blo 2247435 51923447 := bstep (se 1 (by rfl) ⟨38942585, by rfl⟩ : syracuseStep 51923447 = 77885171) B77885171
theorem B34615631 : Blo 2247435 34615631 := bstep (se 1 (by rfl) ⟨25961723, by rfl⟩ : syracuseStep 34615631 = 51923447) B51923447
theorem B92308349 : Blo 2247435 92308349 := bstep (se 3 (by rfl) ⟨17307815, by rfl⟩ : syracuseStep 92308349 = 34615631) B34615631
theorem B61538899 : Blo 2247435 61538899 := bstep (se 1 (by rfl) ⟨46154174, by rfl⟩ : syracuseStep 61538899 = 92308349) B92308349
theorem B82051865 : Blo 2247435 82051865 := bstep (se 2 (by rfl) ⟨30769449, by rfl⟩ : syracuseStep 82051865 = 61538899) B61538899
theorem B54701243 : Blo 2247435 54701243 := bstep (se 1 (by rfl) ⟨41025932, by rfl⟩ : syracuseStep 54701243 = 82051865) B82051865
theorem B36467495 : Blo 2247435 36467495 := bstep (se 1 (by rfl) ⟨27350621, by rfl⟩ : syracuseStep 36467495 = 54701243) B54701243
theorem B24311663 : Blo 2247435 24311663 := bstep (se 1 (by rfl) ⟨18233747, by rfl⟩ : syracuseStep 24311663 = 36467495) B36467495
theorem B16207775 : Blo 2247435 16207775 := bstep (se 1 (by rfl) ⟨12155831, by rfl⟩ : syracuseStep 16207775 = 24311663) B24311663
theorem B10805183 : Blo 2247435 10805183 := bstep (se 1 (by rfl) ⟨8103887, by rfl⟩ : syracuseStep 10805183 = 16207775) B16207775
theorem B7203455 : Blo 2247435 7203455 := bstep (se 1 (by rfl) ⟨5402591, by rfl⟩ : syracuseStep 7203455 = 10805183) B10805183
theorem B4802303 : Blo 2247435 4802303 := bstep (se 1 (by rfl) ⟨3601727, by rfl⟩ : syracuseStep 4802303 = 7203455) B7203455
theorem B3201535 : Blo 2247435 3201535 := bstep (se 1 (by rfl) ⟨2401151, by rfl⟩ : syracuseStep 3201535 = 4802303) B4802303
theorem B4268713 : Blo 2247435 4268713 := bstep (se 2 (by rfl) ⟨1600767, by rfl⟩ : syracuseStep 4268713 = 3201535) B3201535
theorem B5691617 : Blo 2247435 5691617 := bstep (se 2 (by rfl) ⟨2134356, by rfl⟩ : syracuseStep 5691617 = 4268713) B4268713
theorem B3794411 : Blo 2247435 3794411 := bstep (se 1 (by rfl) ⟨2845808, by rfl⟩ : syracuseStep 3794411 = 5691617) B5691617
theorem B2529607 : Blo 2247435 2529607 := bstep (se 1 (by rfl) ⟨1897205, by rfl⟩ : syracuseStep 2529607 = 3794411) B3794411
theorem B3372809 : Blo 2247435 3372809 := bstep (se 2 (by rfl) ⟨1264803, by rfl⟩ : syracuseStep 3372809 = 2529607) B2529607
theorem B2248539 : Blo 2247435 2248539 := bstep (se 1 (by rfl) ⟨1686404, by rfl⟩ : syracuseStep 2248539 = 3372809) B3372809
theorem B11383253 : Blo 2247435 11383253 := bbase (se 7 (by rfl) ⟨133397, by rfl⟩ : syracuseStep 11383253 = 266795) (by norm_num)
theorem B7588835 : Blo 2247435 7588835 := bstep (se 1 (by rfl) ⟨5691626, by rfl⟩ : syracuseStep 7588835 = 11383253) B11383253
theorem B5059223 : Blo 2247435 5059223 := bstep (se 1 (by rfl) ⟨3794417, by rfl⟩ : syracuseStep 5059223 = 7588835) B7588835
theorem B3372815 : Blo 2247435 3372815 := bstep (se 1 (by rfl) ⟨2529611, by rfl⟩ : syracuseStep 3372815 = 5059223) B5059223
theorem B2248543 : Blo 2247435 2248543 := bstep (se 1 (by rfl) ⟨1686407, by rfl⟩ : syracuseStep 2248543 = 3372815) B3372815
theorem B3372821 : Blo 2247435 3372821 := bbase (se 6 (by rfl) ⟨79050, by rfl⟩ : syracuseStep 3372821 = 158101) (by norm_num)
theorem B2248547 : Blo 2247435 2248547 := bstep (se 1 (by rfl) ⟨1686410, by rfl⟩ : syracuseStep 2248547 = 3372821) B3372821
theorem B2599117 : Blo 2247435 2599117 := bbase (se 3 (by rfl) ⟨487334, by rfl⟩ : syracuseStep 2599117 = 974669) (by norm_num)
theorem B55447829 : Blo 2247435 55447829 := bstep (se 6 (by rfl) ⟨1299558, by rfl⟩ : syracuseStep 55447829 = 2599117) B2599117
theorem B36965219 : Blo 2247435 36965219 := bstep (se 1 (by rfl) ⟨27723914, by rfl⟩ : syracuseStep 36965219 = 55447829) B55447829
theorem B98573917 : Blo 2247435 98573917 := bstep (se 3 (by rfl) ⟨18482609, by rfl⟩ : syracuseStep 98573917 = 36965219) B36965219
theorem B131431889 : Blo 2247435 131431889 := bstep (se 2 (by rfl) ⟨49286958, by rfl⟩ : syracuseStep 131431889 = 98573917) B98573917
theorem B87621259 : Blo 2247435 87621259 := bstep (se 1 (by rfl) ⟨65715944, by rfl⟩ : syracuseStep 87621259 = 131431889) B131431889
theorem B116828345 : Blo 2247435 116828345 := bstep (se 2 (by rfl) ⟨43810629, by rfl⟩ : syracuseStep 116828345 = 87621259) B87621259
theorem B77885563 : Blo 2247435 77885563 := bstep (se 1 (by rfl) ⟨58414172, by rfl⟩ : syracuseStep 77885563 = 116828345) B116828345
theorem B103847417 : Blo 2247435 103847417 := bstep (se 2 (by rfl) ⟨38942781, by rfl⟩ : syracuseStep 103847417 = 77885563) B77885563
theorem B69231611 : Blo 2247435 69231611 := bstep (se 1 (by rfl) ⟨51923708, by rfl⟩ : syracuseStep 69231611 = 103847417) B103847417
theorem B46154407 : Blo 2247435 46154407 := bstep (se 1 (by rfl) ⟨34615805, by rfl⟩ : syracuseStep 46154407 = 69231611) B69231611
theorem B61539209 : Blo 2247435 61539209 := bstep (se 2 (by rfl) ⟨23077203, by rfl⟩ : syracuseStep 61539209 = 46154407) B46154407
theorem B41026139 : Blo 2247435 41026139 := bstep (se 1 (by rfl) ⟨30769604, by rfl⟩ : syracuseStep 41026139 = 61539209) B61539209
theorem B27350759 : Blo 2247435 27350759 := bstep (se 1 (by rfl) ⟨20513069, by rfl⟩ : syracuseStep 27350759 = 41026139) B41026139
theorem B18233839 : Blo 2247435 18233839 := bstep (se 1 (by rfl) ⟨13675379, by rfl⟩ : syracuseStep 18233839 = 27350759) B27350759
theorem B97247141 : Blo 2247435 97247141 := bstep (se 4 (by rfl) ⟨9116919, by rfl⟩ : syracuseStep 97247141 = 18233839) B18233839
theorem B64831427 : Blo 2247435 64831427 := bstep (se 1 (by rfl) ⟨48623570, by rfl⟩ : syracuseStep 64831427 = 97247141) B97247141
theorem B43220951 : Blo 2247435 43220951 := bstep (se 1 (by rfl) ⟨32415713, by rfl⟩ : syracuseStep 43220951 = 64831427) B64831427
theorem B28813967 : Blo 2247435 28813967 := bstep (se 1 (by rfl) ⟨21610475, by rfl⟩ : syracuseStep 28813967 = 43220951) B43220951
theorem B19209311 : Blo 2247435 19209311 := bstep (se 1 (by rfl) ⟨14406983, by rfl⟩ : syracuseStep 19209311 = 28813967) B28813967
theorem B12806207 : Blo 2247435 12806207 := bstep (se 1 (by rfl) ⟨9604655, by rfl⟩ : syracuseStep 12806207 = 19209311) B19209311
theorem B8537471 : Blo 2247435 8537471 := bstep (se 1 (by rfl) ⟨6403103, by rfl⟩ : syracuseStep 8537471 = 12806207) B12806207
theorem B5691647 : Blo 2247435 5691647 := bstep (se 1 (by rfl) ⟨4268735, by rfl⟩ : syracuseStep 5691647 = 8537471) B8537471
theorem B3794431 : Blo 2247435 3794431 := bstep (se 1 (by rfl) ⟨2845823, by rfl⟩ : syracuseStep 3794431 = 5691647) B5691647
theorem B5059241 : Blo 2247435 5059241 := bstep (se 2 (by rfl) ⟨1897215, by rfl⟩ : syracuseStep 5059241 = 3794431) B3794431
theorem B3372827 : Blo 2247435 3372827 := bstep (se 1 (by rfl) ⟨2529620, by rfl⟩ : syracuseStep 3372827 = 5059241) B5059241
theorem B2248551 : Blo 2247435 2248551 := bstep (se 1 (by rfl) ⟨1686413, by rfl⟩ : syracuseStep 2248551 = 3372827) B3372827
theorem B2529625 : Blo 2247435 2529625 := bbase (se 2 (by rfl) ⟨948609, by rfl⟩ : syracuseStep 2529625 = 1897219) (by norm_num)
theorem B3372833 : Blo 2247435 3372833 := bstep (se 2 (by rfl) ⟨1264812, by rfl⟩ : syracuseStep 3372833 = 2529625) B2529625
theorem B2248555 : Blo 2247435 2248555 := bstep (se 1 (by rfl) ⟨1686416, by rfl⟩ : syracuseStep 2248555 = 3372833) B3372833
theorem B18233909 : Blo 2247435 18233909 := bbase (se 5 (by rfl) ⟨854714, by rfl⟩ : syracuseStep 18233909 = 1709429) (by norm_num)
theorem B12155939 : Blo 2247435 12155939 := bstep (se 1 (by rfl) ⟨9116954, by rfl⟩ : syracuseStep 12155939 = 18233909) B18233909
theorem B8103959 : Blo 2247435 8103959 := bstep (se 1 (by rfl) ⟨6077969, by rfl⟩ : syracuseStep 8103959 = 12155939) B12155939
theorem B5402639 : Blo 2247435 5402639 := bstep (se 1 (by rfl) ⟨4051979, by rfl⟩ : syracuseStep 5402639 = 8103959) B8103959
theorem B3601759 : Blo 2247435 3601759 := bstep (se 1 (by rfl) ⟨2701319, by rfl⟩ : syracuseStep 3601759 = 5402639) B5402639
theorem B4802345 : Blo 2247435 4802345 := bstep (se 2 (by rfl) ⟨1800879, by rfl⟩ : syracuseStep 4802345 = 3601759) B3601759
theorem B3201563 : Blo 2247435 3201563 := bstep (se 1 (by rfl) ⟨2401172, by rfl⟩ : syracuseStep 3201563 = 4802345) B4802345
theorem B8537501 : Blo 2247435 8537501 := bstep (se 3 (by rfl) ⟨1600781, by rfl⟩ : syracuseStep 8537501 = 3201563) B3201563
theorem B5691667 : Blo 2247435 5691667 := bstep (se 1 (by rfl) ⟨4268750, by rfl⟩ : syracuseStep 5691667 = 8537501) B8537501
theorem B7588889 : Blo 2247435 7588889 := bstep (se 2 (by rfl) ⟨2845833, by rfl⟩ : syracuseStep 7588889 = 5691667) B5691667
theorem B5059259 : Blo 2247435 5059259 := bstep (se 1 (by rfl) ⟨3794444, by rfl⟩ : syracuseStep 5059259 = 7588889) B7588889
theorem B3372839 : Blo 2247435 3372839 := bstep (se 1 (by rfl) ⟨2529629, by rfl⟩ : syracuseStep 3372839 = 5059259) B5059259
theorem B2248559 : Blo 2247435 2248559 := bstep (se 1 (by rfl) ⟨1686419, by rfl⟩ : syracuseStep 2248559 = 3372839) B3372839
theorem B3372845 : Blo 2247435 3372845 := bbase (se 3 (by rfl) ⟨632408, by rfl⟩ : syracuseStep 3372845 = 1264817) (by norm_num)
theorem B2248563 : Blo 2247435 2248563 := bstep (se 1 (by rfl) ⟨1686422, by rfl⟩ : syracuseStep 2248563 = 3372845) B3372845
theorem B5059277 : Blo 2247435 5059277 := bbase (se 3 (by rfl) ⟨948614, by rfl⟩ : syracuseStep 5059277 = 1897229) (by norm_num)
theorem B3372851 : Blo 2247435 3372851 := bstep (se 1 (by rfl) ⟨2529638, by rfl⟩ : syracuseStep 3372851 = 5059277) B5059277
theorem B2248567 : Blo 2247435 2248567 := bstep (se 1 (by rfl) ⟨1686425, by rfl⟩ : syracuseStep 2248567 = 3372851) B3372851
theorem B2845849 : Blo 2247435 2845849 := bbase (se 2 (by rfl) ⟨1067193, by rfl⟩ : syracuseStep 2845849 = 2134387) (by norm_num)
theorem B3794465 : Blo 2247435 3794465 := bstep (se 2 (by rfl) ⟨1422924, by rfl⟩ : syracuseStep 3794465 = 2845849) B2845849
theorem B2529643 : Blo 2247435 2529643 := bstep (se 1 (by rfl) ⟨1897232, by rfl⟩ : syracuseStep 2529643 = 3794465) B3794465
theorem B3372857 : Blo 2247435 3372857 := bstep (se 2 (by rfl) ⟨1264821, by rfl⟩ : syracuseStep 3372857 = 2529643) B2529643
theorem B2248571 : Blo 2247435 2248571 := bstep (se 1 (by rfl) ⟨1686428, by rfl⟩ : syracuseStep 2248571 = 3372857) B3372857
theorem B9604757 : Blo 2247435 9604757 := bbase (se 6 (by rfl) ⟨225111, by rfl⟩ : syracuseStep 9604757 = 450223) (by norm_num)
theorem B25612685 : Blo 2247435 25612685 := bstep (se 3 (by rfl) ⟨4802378, by rfl⟩ : syracuseStep 25612685 = 9604757) B9604757
theorem B17075123 : Blo 2247435 17075123 := bstep (se 1 (by rfl) ⟨12806342, by rfl⟩ : syracuseStep 17075123 = 25612685) B25612685
theorem B11383415 : Blo 2247435 11383415 := bstep (se 1 (by rfl) ⟨8537561, by rfl⟩ : syracuseStep 11383415 = 17075123) B17075123
theorem B7588943 : Blo 2247435 7588943 := bstep (se 1 (by rfl) ⟨5691707, by rfl⟩ : syracuseStep 7588943 = 11383415) B11383415
theorem B5059295 : Blo 2247435 5059295 := bstep (se 1 (by rfl) ⟨3794471, by rfl⟩ : syracuseStep 5059295 = 7588943) B7588943
theorem B3372863 : Blo 2247435 3372863 := bstep (se 1 (by rfl) ⟨2529647, by rfl⟩ : syracuseStep 3372863 = 5059295) B5059295
theorem B2248575 : Blo 2247435 2248575 := bstep (se 1 (by rfl) ⟨1686431, by rfl⟩ : syracuseStep 2248575 = 3372863) B3372863
theorem B3372869 : Blo 2247435 3372869 := bbase (se 4 (by rfl) ⟨316206, by rfl⟩ : syracuseStep 3372869 = 632413) (by norm_num)
theorem B2248579 : Blo 2247435 2248579 := bstep (se 1 (by rfl) ⟨1686434, by rfl⟩ : syracuseStep 2248579 = 3372869) B3372869
theorem B3794485 : Blo 2247435 3794485 := bbase (se 5 (by rfl) ⟨177866, by rfl⟩ : syracuseStep 3794485 = 355733) (by norm_num)
theorem B5059313 : Blo 2247435 5059313 := bstep (se 2 (by rfl) ⟨1897242, by rfl⟩ : syracuseStep 5059313 = 3794485) B3794485
theorem B3372875 : Blo 2247435 3372875 := bstep (se 1 (by rfl) ⟨2529656, by rfl⟩ : syracuseStep 3372875 = 5059313) B5059313
theorem B2248583 : Blo 2247435 2248583 := bstep (se 1 (by rfl) ⟨1686437, by rfl⟩ : syracuseStep 2248583 = 3372875) B3372875
theorem B2529661 : Blo 2247435 2529661 := bbase (se 3 (by rfl) ⟨474311, by rfl⟩ : syracuseStep 2529661 = 948623) (by norm_num)
theorem B3372881 : Blo 2247435 3372881 := bstep (se 2 (by rfl) ⟨1264830, by rfl⟩ : syracuseStep 3372881 = 2529661) B2529661
theorem B2248587 : Blo 2247435 2248587 := bstep (se 1 (by rfl) ⟨1686440, by rfl⟩ : syracuseStep 2248587 = 3372881) B3372881
theorem B7588997 : Blo 2247435 7588997 := bbase (se 4 (by rfl) ⟨711468, by rfl⟩ : syracuseStep 7588997 = 1422937) (by norm_num)
theorem B5059331 : Blo 2247435 5059331 := bstep (se 1 (by rfl) ⟨3794498, by rfl⟩ : syracuseStep 5059331 = 7588997) B7588997
theorem B3372887 : Blo 2247435 3372887 := bstep (se 1 (by rfl) ⟨2529665, by rfl⟩ : syracuseStep 3372887 = 5059331) B5059331
theorem B2248591 : Blo 2247435 2248591 := bstep (se 1 (by rfl) ⟨1686443, by rfl⟩ : syracuseStep 2248591 = 3372887) B3372887
theorem B3372893 : Blo 2247435 3372893 := bbase (se 3 (by rfl) ⟨632417, by rfl⟩ : syracuseStep 3372893 = 1264835) (by norm_num)
theorem B2248595 : Blo 2247435 2248595 := bstep (se 1 (by rfl) ⟨1686446, by rfl⟩ : syracuseStep 2248595 = 3372893) B3372893
theorem B5059349 : Blo 2247435 5059349 := bbase (se 6 (by rfl) ⟨118578, by rfl⟩ : syracuseStep 5059349 = 237157) (by norm_num)
theorem B3372899 : Blo 2247435 3372899 := bstep (se 1 (by rfl) ⟨2529674, by rfl⟩ : syracuseStep 3372899 = 5059349) B5059349
theorem B2248599 : Blo 2247435 2248599 := bstep (se 1 (by rfl) ⟨1686449, by rfl⟩ : syracuseStep 2248599 = 3372899) B3372899
theorem B8537669 : Blo 2247435 8537669 := bbase (se 4 (by rfl) ⟨800406, by rfl⟩ : syracuseStep 8537669 = 1600813) (by norm_num)
theorem B5691779 : Blo 2247435 5691779 := bstep (se 1 (by rfl) ⟨4268834, by rfl⟩ : syracuseStep 5691779 = 8537669) B8537669
theorem B3794519 : Blo 2247435 3794519 := bstep (se 1 (by rfl) ⟨2845889, by rfl⟩ : syracuseStep 3794519 = 5691779) B5691779
theorem B2529679 : Blo 2247435 2529679 := bstep (se 1 (by rfl) ⟨1897259, by rfl⟩ : syracuseStep 2529679 = 3794519) B3794519
theorem B3372905 : Blo 2247435 3372905 := bstep (se 2 (by rfl) ⟨1264839, by rfl⟩ : syracuseStep 3372905 = 2529679) B2529679
theorem B2248603 : Blo 2247435 2248603 := bstep (se 1 (by rfl) ⟨1686452, by rfl⟩ : syracuseStep 2248603 = 3372905) B3372905
theorem B5128397 : Blo 2247435 5128397 := bbase (se 3 (by rfl) ⟨961574, by rfl⟩ : syracuseStep 5128397 = 1923149) (by norm_num)
theorem B3418931 : Blo 2247435 3418931 := bstep (se 1 (by rfl) ⟨2564198, by rfl⟩ : syracuseStep 3418931 = 5128397) B5128397
theorem B2279287 : Blo 2247435 2279287 := bstep (se 1 (by rfl) ⟨1709465, by rfl⟩ : syracuseStep 2279287 = 3418931) B3418931
theorem B3039049 : Blo 2247435 3039049 := bstep (se 2 (by rfl) ⟨1139643, by rfl⟩ : syracuseStep 3039049 = 2279287) B2279287
theorem B16208261 : Blo 2247435 16208261 := bstep (se 4 (by rfl) ⟨1519524, by rfl⟩ : syracuseStep 16208261 = 3039049) B3039049
theorem B10805507 : Blo 2247435 10805507 := bstep (se 1 (by rfl) ⟨8104130, by rfl⟩ : syracuseStep 10805507 = 16208261) B16208261
theorem B7203671 : Blo 2247435 7203671 := bstep (se 1 (by rfl) ⟨5402753, by rfl⟩ : syracuseStep 7203671 = 10805507) B10805507
theorem B4802447 : Blo 2247435 4802447 := bstep (se 1 (by rfl) ⟨3601835, by rfl⟩ : syracuseStep 4802447 = 7203671) B7203671
theorem B12806525 : Blo 2247435 12806525 := bstep (se 3 (by rfl) ⟨2401223, by rfl⟩ : syracuseStep 12806525 = 4802447) B4802447
theorem B8537683 : Blo 2247435 8537683 := bstep (se 1 (by rfl) ⟨6403262, by rfl⟩ : syracuseStep 8537683 = 12806525) B12806525
theorem B11383577 : Blo 2247435 11383577 := bstep (se 2 (by rfl) ⟨4268841, by rfl⟩ : syracuseStep 11383577 = 8537683) B8537683
theorem B7589051 : Blo 2247435 7589051 := bstep (se 1 (by rfl) ⟨5691788, by rfl⟩ : syracuseStep 7589051 = 11383577) B11383577
theorem B5059367 : Blo 2247435 5059367 := bstep (se 1 (by rfl) ⟨3794525, by rfl⟩ : syracuseStep 5059367 = 7589051) B7589051
theorem B3372911 : Blo 2247435 3372911 := bstep (se 1 (by rfl) ⟨2529683, by rfl⟩ : syracuseStep 3372911 = 5059367) B5059367
theorem B2248607 : Blo 2247435 2248607 := bstep (se 1 (by rfl) ⟨1686455, by rfl⟩ : syracuseStep 2248607 = 3372911) B3372911
theorem B3372917 : Blo 2247435 3372917 := bbase (se 5 (by rfl) ⟨158105, by rfl⟩ : syracuseStep 3372917 = 316211) (by norm_num)
theorem B2248611 : Blo 2247435 2248611 := bstep (se 1 (by rfl) ⟨1686458, by rfl⟩ : syracuseStep 2248611 = 3372917) B3372917
theorem B3039061 : Blo 2247435 3039061 := bbase (se 9 (by rfl) ⟨8903, by rfl⟩ : syracuseStep 3039061 = 17807) (by norm_num)
theorem B4052081 : Blo 2247435 4052081 := bstep (se 2 (by rfl) ⟨1519530, by rfl⟩ : syracuseStep 4052081 = 3039061) B3039061
theorem B2701387 : Blo 2247435 2701387 := bstep (se 1 (by rfl) ⟨2026040, by rfl⟩ : syracuseStep 2701387 = 4052081) B4052081
theorem B3601849 : Blo 2247435 3601849 := bstep (se 2 (by rfl) ⟨1350693, by rfl⟩ : syracuseStep 3601849 = 2701387) B2701387
theorem B4802465 : Blo 2247435 4802465 := bstep (se 2 (by rfl) ⟨1800924, by rfl⟩ : syracuseStep 4802465 = 3601849) B3601849
theorem B3201643 : Blo 2247435 3201643 := bstep (se 1 (by rfl) ⟨2401232, by rfl⟩ : syracuseStep 3201643 = 4802465) B4802465
theorem B4268857 : Blo 2247435 4268857 := bstep (se 2 (by rfl) ⟨1600821, by rfl⟩ : syracuseStep 4268857 = 3201643) B3201643
theorem B5691809 : Blo 2247435 5691809 := bstep (se 2 (by rfl) ⟨2134428, by rfl⟩ : syracuseStep 5691809 = 4268857) B4268857
theorem B3794539 : Blo 2247435 3794539 := bstep (se 1 (by rfl) ⟨2845904, by rfl⟩ : syracuseStep 3794539 = 5691809) B5691809
theorem B5059385 : Blo 2247435 5059385 := bstep (se 2 (by rfl) ⟨1897269, by rfl⟩ : syracuseStep 5059385 = 3794539) B3794539
theorem B3372923 : Blo 2247435 3372923 := bstep (se 1 (by rfl) ⟨2529692, by rfl⟩ : syracuseStep 3372923 = 5059385) B5059385
theorem B2248615 : Blo 2247435 2248615 := bstep (se 1 (by rfl) ⟨1686461, by rfl⟩ : syracuseStep 2248615 = 3372923) B3372923
theorem B2529697 : Blo 2247435 2529697 := bbase (se 2 (by rfl) ⟨948636, by rfl⟩ : syracuseStep 2529697 = 1897273) (by norm_num)
theorem B3372929 : Blo 2247435 3372929 := bstep (se 2 (by rfl) ⟨1264848, by rfl⟩ : syracuseStep 3372929 = 2529697) B2529697
theorem B2248619 : Blo 2247435 2248619 := bstep (se 1 (by rfl) ⟨1686464, by rfl⟩ : syracuseStep 2248619 = 3372929) B3372929
theorem B5691829 : Blo 2247435 5691829 := bbase (se 5 (by rfl) ⟨266804, by rfl⟩ : syracuseStep 5691829 = 533609) (by norm_num)
theorem B7589105 : Blo 2247435 7589105 := bstep (se 2 (by rfl) ⟨2845914, by rfl⟩ : syracuseStep 7589105 = 5691829) B5691829
theorem B5059403 : Blo 2247435 5059403 := bstep (se 1 (by rfl) ⟨3794552, by rfl⟩ : syracuseStep 5059403 = 7589105) B7589105
theorem B3372935 : Blo 2247435 3372935 := bstep (se 1 (by rfl) ⟨2529701, by rfl⟩ : syracuseStep 3372935 = 5059403) B5059403
theorem B2248623 : Blo 2247435 2248623 := bstep (se 1 (by rfl) ⟨1686467, by rfl⟩ : syracuseStep 2248623 = 3372935) B3372935
theorem B3372941 : Blo 2247435 3372941 := bbase (se 3 (by rfl) ⟨632426, by rfl⟩ : syracuseStep 3372941 = 1264853) (by norm_num)
theorem B2248627 : Blo 2247435 2248627 := bstep (se 1 (by rfl) ⟨1686470, by rfl⟩ : syracuseStep 2248627 = 3372941) B3372941
theorem B5059421 : Blo 2247435 5059421 := bbase (se 3 (by rfl) ⟨948641, by rfl⟩ : syracuseStep 5059421 = 1897283) (by norm_num)
theorem B3372947 : Blo 2247435 3372947 := bstep (se 1 (by rfl) ⟨2529710, by rfl⟩ : syracuseStep 3372947 = 5059421) B5059421
theorem B2248631 : Blo 2247435 2248631 := bstep (se 1 (by rfl) ⟨1686473, by rfl⟩ : syracuseStep 2248631 = 3372947) B3372947
theorem B3794573 : Blo 2247435 3794573 := bbase (se 3 (by rfl) ⟨711482, by rfl⟩ : syracuseStep 3794573 = 1422965) (by norm_num)
theorem B2529715 : Blo 2247435 2529715 := bstep (se 1 (by rfl) ⟨1897286, by rfl⟩ : syracuseStep 2529715 = 3794573) B3794573
theorem B3372953 : Blo 2247435 3372953 := bstep (se 2 (by rfl) ⟨1264857, by rfl⟩ : syracuseStep 3372953 = 2529715) B2529715
theorem B2248635 : Blo 2247435 2248635 := bstep (se 1 (by rfl) ⟨1686476, by rfl⟩ : syracuseStep 2248635 = 3372953) B3372953
theorem B8654293 : Blo 2247435 8654293 := bbase (se 7 (by rfl) ⟨101417, by rfl⟩ : syracuseStep 8654293 = 202835) (by norm_num)
theorem B11539057 : Blo 2247435 11539057 := bstep (se 2 (by rfl) ⟨4327146, by rfl⟩ : syracuseStep 11539057 = 8654293) B8654293
theorem B15385409 : Blo 2247435 15385409 := bstep (se 2 (by rfl) ⟨5769528, by rfl⟩ : syracuseStep 15385409 = 11539057) B11539057
theorem B10256939 : Blo 2247435 10256939 := bstep (se 1 (by rfl) ⟨7692704, by rfl⟩ : syracuseStep 10256939 = 15385409) B15385409
theorem B6837959 : Blo 2247435 6837959 := bstep (se 1 (by rfl) ⟨5128469, by rfl⟩ : syracuseStep 6837959 = 10256939) B10256939
theorem B4558639 : Blo 2247435 4558639 := bstep (se 1 (by rfl) ⟨3418979, by rfl⟩ : syracuseStep 4558639 = 6837959) B6837959
theorem B6078185 : Blo 2247435 6078185 := bstep (se 2 (by rfl) ⟨2279319, by rfl⟩ : syracuseStep 6078185 = 4558639) B4558639
theorem B4052123 : Blo 2247435 4052123 := bstep (se 1 (by rfl) ⟨3039092, by rfl⟩ : syracuseStep 4052123 = 6078185) B6078185
theorem B2701415 : Blo 2247435 2701415 := bstep (se 1 (by rfl) ⟨2026061, by rfl⟩ : syracuseStep 2701415 = 4052123) B4052123
theorem B7203773 : Blo 2247435 7203773 := bstep (se 3 (by rfl) ⟨1350707, by rfl⟩ : syracuseStep 7203773 = 2701415) B2701415
theorem B19210061 : Blo 2247435 19210061 := bstep (se 3 (by rfl) ⟨3601886, by rfl⟩ : syracuseStep 19210061 = 7203773) B7203773
theorem B12806707 : Blo 2247435 12806707 := bstep (se 1 (by rfl) ⟨9605030, by rfl⟩ : syracuseStep 12806707 = 19210061) B19210061
theorem B17075609 : Blo 2247435 17075609 := bstep (se 2 (by rfl) ⟨6403353, by rfl⟩ : syracuseStep 17075609 = 12806707) B12806707
theorem B11383739 : Blo 2247435 11383739 := bstep (se 1 (by rfl) ⟨8537804, by rfl⟩ : syracuseStep 11383739 = 17075609) B17075609
theorem B7589159 : Blo 2247435 7589159 := bstep (se 1 (by rfl) ⟨5691869, by rfl⟩ : syracuseStep 7589159 = 11383739) B11383739
theorem B5059439 : Blo 2247435 5059439 := bstep (se 1 (by rfl) ⟨3794579, by rfl⟩ : syracuseStep 5059439 = 7589159) B7589159
theorem B3372959 : Blo 2247435 3372959 := bstep (se 1 (by rfl) ⟨2529719, by rfl⟩ : syracuseStep 3372959 = 5059439) B5059439
theorem B2248639 : Blo 2247435 2248639 := bstep (se 1 (by rfl) ⟨1686479, by rfl⟩ : syracuseStep 2248639 = 3372959) B3372959
theorem B3372965 : Blo 2247435 3372965 := bbase (se 4 (by rfl) ⟨316215, by rfl⟩ : syracuseStep 3372965 = 632431) (by norm_num)
theorem B2248643 : Blo 2247435 2248643 := bstep (se 1 (by rfl) ⟨1686482, by rfl⟩ : syracuseStep 2248643 = 3372965) B3372965
theorem B2845945 : Blo 2247435 2845945 := bbase (se 2 (by rfl) ⟨1067229, by rfl⟩ : syracuseStep 2845945 = 2134459) (by norm_num)
theorem B3794593 : Blo 2247435 3794593 := bstep (se 2 (by rfl) ⟨1422972, by rfl⟩ : syracuseStep 3794593 = 2845945) B2845945
theorem B5059457 : Blo 2247435 5059457 := bstep (se 2 (by rfl) ⟨1897296, by rfl⟩ : syracuseStep 5059457 = 3794593) B3794593
theorem B3372971 : Blo 2247435 3372971 := bstep (se 1 (by rfl) ⟨2529728, by rfl⟩ : syracuseStep 3372971 = 5059457) B5059457
theorem B2248647 : Blo 2247435 2248647 := bstep (se 1 (by rfl) ⟨1686485, by rfl⟩ : syracuseStep 2248647 = 3372971) B3372971
theorem B2529733 : Blo 2247435 2529733 := bbase (se 4 (by rfl) ⟨237162, by rfl⟩ : syracuseStep 2529733 = 474325) (by norm_num)
theorem B3372977 : Blo 2247435 3372977 := bstep (se 2 (by rfl) ⟨1264866, by rfl⟩ : syracuseStep 3372977 = 2529733) B2529733
theorem B2248651 : Blo 2247435 2248651 := bstep (se 1 (by rfl) ⟨1686488, by rfl⟩ : syracuseStep 2248651 = 3372977) B3372977
theorem B4268933 : Blo 2247435 4268933 := bbase (se 4 (by rfl) ⟨400212, by rfl⟩ : syracuseStep 4268933 = 800425) (by norm_num)
theorem B2845955 : Blo 2247435 2845955 := bstep (se 1 (by rfl) ⟨2134466, by rfl⟩ : syracuseStep 2845955 = 4268933) B4268933
theorem B7589213 : Blo 2247435 7589213 := bstep (se 3 (by rfl) ⟨1422977, by rfl⟩ : syracuseStep 7589213 = 2845955) B2845955
theorem B5059475 : Blo 2247435 5059475 := bstep (se 1 (by rfl) ⟨3794606, by rfl⟩ : syracuseStep 5059475 = 7589213) B7589213
theorem B3372983 : Blo 2247435 3372983 := bstep (se 1 (by rfl) ⟨2529737, by rfl⟩ : syracuseStep 3372983 = 5059475) B5059475
theorem B2248655 : Blo 2247435 2248655 := bstep (se 1 (by rfl) ⟨1686491, by rfl⟩ : syracuseStep 2248655 = 3372983) B3372983
theorem B3372989 : Blo 2247435 3372989 := bbase (se 3 (by rfl) ⟨632435, by rfl⟩ : syracuseStep 3372989 = 1264871) (by norm_num)
theorem B2248659 : Blo 2247435 2248659 := bstep (se 1 (by rfl) ⟨1686494, by rfl⟩ : syracuseStep 2248659 = 3372989) B3372989
theorem B5059493 : Blo 2247435 5059493 := bbase (se 4 (by rfl) ⟨474327, by rfl⟩ : syracuseStep 5059493 = 948655) (by norm_num)
theorem B3372995 : Blo 2247435 3372995 := bstep (se 1 (by rfl) ⟨2529746, by rfl⟩ : syracuseStep 3372995 = 5059493) B5059493
theorem B2248663 : Blo 2247435 2248663 := bstep (se 1 (by rfl) ⟨1686497, by rfl⟩ : syracuseStep 2248663 = 3372995) B3372995
theorem B5691941 : Blo 2247435 5691941 := bbase (se 4 (by rfl) ⟨533619, by rfl⟩ : syracuseStep 5691941 = 1067239) (by norm_num)
theorem B3794627 : Blo 2247435 3794627 := bstep (se 1 (by rfl) ⟨2845970, by rfl⟩ : syracuseStep 3794627 = 5691941) B5691941
theorem B2529751 : Blo 2247435 2529751 := bstep (se 1 (by rfl) ⟨1897313, by rfl⟩ : syracuseStep 2529751 = 3794627) B3794627
theorem B3373001 : Blo 2247435 3373001 := bstep (se 2 (by rfl) ⟨1264875, by rfl⟩ : syracuseStep 3373001 = 2529751) B2529751
theorem B2248667 : Blo 2247435 2248667 := bstep (se 1 (by rfl) ⟨1686500, by rfl⟩ : syracuseStep 2248667 = 3373001) B3373001
theorem B6403445 : Blo 2247435 6403445 := bbase (se 5 (by rfl) ⟨300161, by rfl⟩ : syracuseStep 6403445 = 600323) (by norm_num)
theorem B4268963 : Blo 2247435 4268963 := bstep (se 1 (by rfl) ⟨3201722, by rfl⟩ : syracuseStep 4268963 = 6403445) B6403445
theorem B11383901 : Blo 2247435 11383901 := bstep (se 3 (by rfl) ⟨2134481, by rfl⟩ : syracuseStep 11383901 = 4268963) B4268963
theorem B7589267 : Blo 2247435 7589267 := bstep (se 1 (by rfl) ⟨5691950, by rfl⟩ : syracuseStep 7589267 = 11383901) B11383901
theorem B5059511 : Blo 2247435 5059511 := bstep (se 1 (by rfl) ⟨3794633, by rfl⟩ : syracuseStep 5059511 = 7589267) B7589267
theorem B3373007 : Blo 2247435 3373007 := bstep (se 1 (by rfl) ⟨2529755, by rfl⟩ : syracuseStep 3373007 = 5059511) B5059511
theorem B2248671 : Blo 2247435 2248671 := bstep (se 1 (by rfl) ⟨1686503, by rfl⟩ : syracuseStep 2248671 = 3373007) B3373007
theorem B3373013 : Blo 2247435 3373013 := bbase (se 7 (by rfl) ⟨39527, by rfl⟩ : syracuseStep 3373013 = 79055) (by norm_num)
theorem B2248675 : Blo 2247435 2248675 := bstep (se 1 (by rfl) ⟨1686506, by rfl⟩ : syracuseStep 2248675 = 3373013) B3373013
theorem B8537957 : Blo 2247435 8537957 := bbase (se 4 (by rfl) ⟨800433, by rfl⟩ : syracuseStep 8537957 = 1600867) (by norm_num)
theorem B5691971 : Blo 2247435 5691971 := bstep (se 1 (by rfl) ⟨4268978, by rfl⟩ : syracuseStep 5691971 = 8537957) B8537957
theorem B3794647 : Blo 2247435 3794647 := bstep (se 1 (by rfl) ⟨2845985, by rfl⟩ : syracuseStep 3794647 = 5691971) B5691971
theorem B5059529 : Blo 2247435 5059529 := bstep (se 2 (by rfl) ⟨1897323, by rfl⟩ : syracuseStep 5059529 = 3794647) B3794647
theorem B3373019 : Blo 2247435 3373019 := bstep (se 1 (by rfl) ⟨2529764, by rfl⟩ : syracuseStep 3373019 = 5059529) B5059529
theorem B2248679 : Blo 2247435 2248679 := bstep (se 1 (by rfl) ⟨1686509, by rfl⟩ : syracuseStep 2248679 = 3373019) B3373019
theorem B2529769 : Blo 2247435 2529769 := bbase (se 2 (by rfl) ⟨948663, by rfl⟩ : syracuseStep 2529769 = 1897327) (by norm_num)
theorem B3373025 : Blo 2247435 3373025 := bstep (se 2 (by rfl) ⟨1264884, by rfl⟩ : syracuseStep 3373025 = 2529769) B2529769
theorem B2248683 : Blo 2247435 2248683 := bstep (se 1 (by rfl) ⟨1686512, by rfl⟩ : syracuseStep 2248683 = 3373025) B3373025
theorem B2401309 : Blo 2247435 2401309 := bbase (se 3 (by rfl) ⟨450245, by rfl⟩ : syracuseStep 2401309 = 900491) (by norm_num)
theorem B12806981 : Blo 2247435 12806981 := bstep (se 4 (by rfl) ⟨1200654, by rfl⟩ : syracuseStep 12806981 = 2401309) B2401309
theorem B8537987 : Blo 2247435 8537987 := bstep (se 1 (by rfl) ⟨6403490, by rfl⟩ : syracuseStep 8537987 = 12806981) B12806981
theorem B5691991 : Blo 2247435 5691991 := bstep (se 1 (by rfl) ⟨4268993, by rfl⟩ : syracuseStep 5691991 = 8537987) B8537987
theorem B7589321 : Blo 2247435 7589321 := bstep (se 2 (by rfl) ⟨2845995, by rfl⟩ : syracuseStep 7589321 = 5691991) B5691991
theorem B5059547 : Blo 2247435 5059547 := bstep (se 1 (by rfl) ⟨3794660, by rfl⟩ : syracuseStep 5059547 = 7589321) B7589321
theorem B3373031 : Blo 2247435 3373031 := bstep (se 1 (by rfl) ⟨2529773, by rfl⟩ : syracuseStep 3373031 = 5059547) B5059547
theorem B2248687 : Blo 2247435 2248687 := bstep (se 1 (by rfl) ⟨1686515, by rfl⟩ : syracuseStep 2248687 = 3373031) B3373031
theorem B3373037 : Blo 2247435 3373037 := bbase (se 3 (by rfl) ⟨632444, by rfl⟩ : syracuseStep 3373037 = 1264889) (by norm_num)
theorem B2248691 : Blo 2247435 2248691 := bstep (se 1 (by rfl) ⟨1686518, by rfl⟩ : syracuseStep 2248691 = 3373037) B3373037
theorem B5059565 : Blo 2247435 5059565 := bbase (se 3 (by rfl) ⟨948668, by rfl⟩ : syracuseStep 5059565 = 1897337) (by norm_num)
theorem B3373043 : Blo 2247435 3373043 := bstep (se 1 (by rfl) ⟨2529782, by rfl⟩ : syracuseStep 3373043 = 5059565) B5059565
theorem B2248695 : Blo 2247435 2248695 := bstep (se 1 (by rfl) ⟨1686521, by rfl⟩ : syracuseStep 2248695 = 3373043) B3373043
theorem B4802645 : Blo 2247435 4802645 := bbase (se 8 (by rfl) ⟨28140, by rfl⟩ : syracuseStep 4802645 = 56281) (by norm_num)
theorem B3201763 : Blo 2247435 3201763 := bstep (se 1 (by rfl) ⟨2401322, by rfl⟩ : syracuseStep 3201763 = 4802645) B4802645
theorem B4269017 : Blo 2247435 4269017 := bstep (se 2 (by rfl) ⟨1600881, by rfl⟩ : syracuseStep 4269017 = 3201763) B3201763
theorem B2846011 : Blo 2247435 2846011 := bstep (se 1 (by rfl) ⟨2134508, by rfl⟩ : syracuseStep 2846011 = 4269017) B4269017
theorem B3794681 : Blo 2247435 3794681 := bstep (se 2 (by rfl) ⟨1423005, by rfl⟩ : syracuseStep 3794681 = 2846011) B2846011
theorem B2529787 : Blo 2247435 2529787 := bstep (se 1 (by rfl) ⟨1897340, by rfl⟩ : syracuseStep 2529787 = 3794681) B3794681
theorem B3373049 : Blo 2247435 3373049 := bstep (se 2 (by rfl) ⟨1264893, by rfl⟩ : syracuseStep 3373049 = 2529787) B2529787
theorem B2248699 : Blo 2247435 2248699 := bstep (se 1 (by rfl) ⟨1686524, by rfl⟩ : syracuseStep 2248699 = 3373049) B3373049
theorem B11539381 : Blo 2247435 11539381 := bbase (se 5 (by rfl) ⟨540908, by rfl⟩ : syracuseStep 11539381 = 1081817) (by norm_num)
theorem B15385841 : Blo 2247435 15385841 := bstep (se 2 (by rfl) ⟨5769690, by rfl⟩ : syracuseStep 15385841 = 11539381) B11539381
theorem B10257227 : Blo 2247435 10257227 := bstep (se 1 (by rfl) ⟨7692920, by rfl⟩ : syracuseStep 10257227 = 15385841) B15385841
theorem B6838151 : Blo 2247435 6838151 := bstep (se 1 (by rfl) ⟨5128613, by rfl⟩ : syracuseStep 6838151 = 10257227) B10257227
theorem B72940277 : Blo 2247435 72940277 := bstep (se 5 (by rfl) ⟨3419075, by rfl⟩ : syracuseStep 72940277 = 6838151) B6838151
theorem B194507405 : Blo 2247435 194507405 := bstep (se 3 (by rfl) ⟨36470138, by rfl⟩ : syracuseStep 194507405 = 72940277) B72940277
theorem B129671603 : Blo 2247435 129671603 := bstep (se 1 (by rfl) ⟨97253702, by rfl⟩ : syracuseStep 129671603 = 194507405) B194507405
theorem B86447735 : Blo 2247435 86447735 := bstep (se 1 (by rfl) ⟨64835801, by rfl⟩ : syracuseStep 86447735 = 129671603) B129671603
theorem B57631823 : Blo 2247435 57631823 := bstep (se 1 (by rfl) ⟨43223867, by rfl⟩ : syracuseStep 57631823 = 86447735) B86447735
theorem B38421215 : Blo 2247435 38421215 := bstep (se 1 (by rfl) ⟨28815911, by rfl⟩ : syracuseStep 38421215 = 57631823) B57631823
theorem B25614143 : Blo 2247435 25614143 := bstep (se 1 (by rfl) ⟨19210607, by rfl⟩ : syracuseStep 25614143 = 38421215) B38421215
theorem B17076095 : Blo 2247435 17076095 := bstep (se 1 (by rfl) ⟨12807071, by rfl⟩ : syracuseStep 17076095 = 25614143) B25614143
theorem B11384063 : Blo 2247435 11384063 := bstep (se 1 (by rfl) ⟨8538047, by rfl⟩ : syracuseStep 11384063 = 17076095) B17076095
theorem B7589375 : Blo 2247435 7589375 := bstep (se 1 (by rfl) ⟨5692031, by rfl⟩ : syracuseStep 7589375 = 11384063) B11384063
theorem B5059583 : Blo 2247435 5059583 := bstep (se 1 (by rfl) ⟨3794687, by rfl⟩ : syracuseStep 5059583 = 7589375) B7589375
theorem B3373055 : Blo 2247435 3373055 := bstep (se 1 (by rfl) ⟨2529791, by rfl⟩ : syracuseStep 3373055 = 5059583) B5059583
theorem B2248703 : Blo 2247435 2248703 := bstep (se 1 (by rfl) ⟨1686527, by rfl⟩ : syracuseStep 2248703 = 3373055) B3373055
theorem B3373061 : Blo 2247435 3373061 := bbase (se 4 (by rfl) ⟨316224, by rfl⟩ : syracuseStep 3373061 = 632449) (by norm_num)
theorem B2248707 : Blo 2247435 2248707 := bstep (se 1 (by rfl) ⟨1686530, by rfl⟩ : syracuseStep 2248707 = 3373061) B3373061
theorem B3794701 : Blo 2247435 3794701 := bbase (se 3 (by rfl) ⟨711506, by rfl⟩ : syracuseStep 3794701 = 1423013) (by norm_num)
theorem B5059601 : Blo 2247435 5059601 := bstep (se 2 (by rfl) ⟨1897350, by rfl⟩ : syracuseStep 5059601 = 3794701) B3794701
theorem B3373067 : Blo 2247435 3373067 := bstep (se 1 (by rfl) ⟨2529800, by rfl⟩ : syracuseStep 3373067 = 5059601) B5059601
theorem B2248711 : Blo 2247435 2248711 := bstep (se 1 (by rfl) ⟨1686533, by rfl⟩ : syracuseStep 2248711 = 3373067) B3373067
theorem B2529805 : Blo 2247435 2529805 := bbase (se 3 (by rfl) ⟨474338, by rfl⟩ : syracuseStep 2529805 = 948677) (by norm_num)
theorem B3373073 : Blo 2247435 3373073 := bstep (se 2 (by rfl) ⟨1264902, by rfl⟩ : syracuseStep 3373073 = 2529805) B2529805
theorem B2248715 : Blo 2247435 2248715 := bstep (se 1 (by rfl) ⟨1686536, by rfl⟩ : syracuseStep 2248715 = 3373073) B3373073
theorem B7589429 : Blo 2247435 7589429 := bbase (se 5 (by rfl) ⟨355754, by rfl⟩ : syracuseStep 7589429 = 711509) (by norm_num)
theorem B5059619 : Blo 2247435 5059619 := bstep (se 1 (by rfl) ⟨3794714, by rfl⟩ : syracuseStep 5059619 = 7589429) B7589429
theorem B3373079 : Blo 2247435 3373079 := bstep (se 1 (by rfl) ⟨2529809, by rfl⟩ : syracuseStep 3373079 = 5059619) B5059619
theorem B2248719 : Blo 2247435 2248719 := bstep (se 1 (by rfl) ⟨1686539, by rfl⟩ : syracuseStep 2248719 = 3373079) B3373079
theorem B3373085 : Blo 2247435 3373085 := bbase (se 3 (by rfl) ⟨632453, by rfl⟩ : syracuseStep 3373085 = 1264907) (by norm_num)
theorem B2248723 : Blo 2247435 2248723 := bstep (se 1 (by rfl) ⟨1686542, by rfl⟩ : syracuseStep 2248723 = 3373085) B3373085
theorem B5059637 : Blo 2247435 5059637 := bbase (se 5 (by rfl) ⟨237170, by rfl⟩ : syracuseStep 5059637 = 474341) (by norm_num)
theorem B3373091 : Blo 2247435 3373091 := bstep (se 1 (by rfl) ⟨2529818, by rfl⟩ : syracuseStep 3373091 = 5059637) B5059637
theorem B2248727 : Blo 2247435 2248727 := bstep (se 1 (by rfl) ⟨1686545, by rfl⟩ : syracuseStep 2248727 = 3373091) B3373091
theorem B7204069 : Blo 2247435 7204069 := bbase (se 4 (by rfl) ⟨675381, by rfl⟩ : syracuseStep 7204069 = 1350763) (by norm_num)
theorem B9605425 : Blo 2247435 9605425 := bstep (se 2 (by rfl) ⟨3602034, by rfl⟩ : syracuseStep 9605425 = 7204069) B7204069
theorem B12807233 : Blo 2247435 12807233 := bstep (se 2 (by rfl) ⟨4802712, by rfl⟩ : syracuseStep 12807233 = 9605425) B9605425
theorem B8538155 : Blo 2247435 8538155 := bstep (se 1 (by rfl) ⟨6403616, by rfl⟩ : syracuseStep 8538155 = 12807233) B12807233
theorem B5692103 : Blo 2247435 5692103 := bstep (se 1 (by rfl) ⟨4269077, by rfl⟩ : syracuseStep 5692103 = 8538155) B8538155
theorem B3794735 : Blo 2247435 3794735 := bstep (se 1 (by rfl) ⟨2846051, by rfl⟩ : syracuseStep 3794735 = 5692103) B5692103
theorem B2529823 : Blo 2247435 2529823 := bstep (se 1 (by rfl) ⟨1897367, by rfl⟩ : syracuseStep 2529823 = 3794735) B3794735
theorem B3373097 : Blo 2247435 3373097 := bstep (se 2 (by rfl) ⟨1264911, by rfl⟩ : syracuseStep 3373097 = 2529823) B2529823
theorem B2248731 : Blo 2247435 2248731 := bstep (se 1 (by rfl) ⟨1686548, by rfl⟩ : syracuseStep 2248731 = 3373097) B3373097
theorem B5403061 : Blo 2247435 5403061 := bbase (se 5 (by rfl) ⟨253268, by rfl⟩ : syracuseStep 5403061 = 506537) (by norm_num)
theorem B7204081 : Blo 2247435 7204081 := bstep (se 2 (by rfl) ⟨2701530, by rfl⟩ : syracuseStep 7204081 = 5403061) B5403061
theorem B9605441 : Blo 2247435 9605441 := bstep (se 2 (by rfl) ⟨3602040, by rfl⟩ : syracuseStep 9605441 = 7204081) B7204081
theorem B6403627 : Blo 2247435 6403627 := bstep (se 1 (by rfl) ⟨4802720, by rfl⟩ : syracuseStep 6403627 = 9605441) B9605441
theorem B8538169 : Blo 2247435 8538169 := bstep (se 2 (by rfl) ⟨3201813, by rfl⟩ : syracuseStep 8538169 = 6403627) B6403627
theorem B11384225 : Blo 2247435 11384225 := bstep (se 2 (by rfl) ⟨4269084, by rfl⟩ : syracuseStep 11384225 = 8538169) B8538169
theorem B7589483 : Blo 2247435 7589483 := bstep (se 1 (by rfl) ⟨5692112, by rfl⟩ : syracuseStep 7589483 = 11384225) B11384225
theorem B5059655 : Blo 2247435 5059655 := bstep (se 1 (by rfl) ⟨3794741, by rfl⟩ : syracuseStep 5059655 = 7589483) B7589483
theorem B3373103 : Blo 2247435 3373103 := bstep (se 1 (by rfl) ⟨2529827, by rfl⟩ : syracuseStep 3373103 = 5059655) B5059655
theorem B2248735 : Blo 2247435 2248735 := bstep (se 1 (by rfl) ⟨1686551, by rfl⟩ : syracuseStep 2248735 = 3373103) B3373103
theorem B3373109 : Blo 2247435 3373109 := bbase (se 5 (by rfl) ⟨158114, by rfl⟩ : syracuseStep 3373109 = 316229) (by norm_num)
theorem B2248739 : Blo 2247435 2248739 := bstep (se 1 (by rfl) ⟨1686554, by rfl⟩ : syracuseStep 2248739 = 3373109) B3373109
theorem B5692133 : Blo 2247435 5692133 := bbase (se 4 (by rfl) ⟨533637, by rfl⟩ : syracuseStep 5692133 = 1067275) (by norm_num)
theorem B3794755 : Blo 2247435 3794755 := bstep (se 1 (by rfl) ⟨2846066, by rfl⟩ : syracuseStep 3794755 = 5692133) B5692133
theorem B5059673 : Blo 2247435 5059673 := bstep (se 2 (by rfl) ⟨1897377, by rfl⟩ : syracuseStep 5059673 = 3794755) B3794755
theorem B3373115 : Blo 2247435 3373115 := bstep (se 1 (by rfl) ⟨2529836, by rfl⟩ : syracuseStep 3373115 = 5059673) B5059673
theorem B2248743 : Blo 2247435 2248743 := bstep (se 1 (by rfl) ⟨1686557, by rfl⟩ : syracuseStep 2248743 = 3373115) B3373115
theorem B2529841 : Blo 2247435 2529841 := bbase (se 2 (by rfl) ⟨948690, by rfl⟩ : syracuseStep 2529841 = 1897381) (by norm_num)
theorem B3373121 : Blo 2247435 3373121 := bstep (se 2 (by rfl) ⟨1264920, by rfl⟩ : syracuseStep 3373121 = 2529841) B2529841
theorem B2248747 : Blo 2247435 2248747 := bstep (se 1 (by rfl) ⟨1686560, by rfl⟩ : syracuseStep 2248747 = 3373121) B3373121
theorem B7204133 : Blo 2247435 7204133 := bbase (se 4 (by rfl) ⟨675387, by rfl⟩ : syracuseStep 7204133 = 1350775) (by norm_num)
theorem B4802755 : Blo 2247435 4802755 := bstep (se 1 (by rfl) ⟨3602066, by rfl⟩ : syracuseStep 4802755 = 7204133) B7204133
theorem B6403673 : Blo 2247435 6403673 := bstep (se 2 (by rfl) ⟨2401377, by rfl⟩ : syracuseStep 6403673 = 4802755) B4802755
theorem B4269115 : Blo 2247435 4269115 := bstep (se 1 (by rfl) ⟨3201836, by rfl⟩ : syracuseStep 4269115 = 6403673) B6403673
theorem B5692153 : Blo 2247435 5692153 := bstep (se 2 (by rfl) ⟨2134557, by rfl⟩ : syracuseStep 5692153 = 4269115) B4269115
theorem B7589537 : Blo 2247435 7589537 := bstep (se 2 (by rfl) ⟨2846076, by rfl⟩ : syracuseStep 7589537 = 5692153) B5692153
theorem B5059691 : Blo 2247435 5059691 := bstep (se 1 (by rfl) ⟨3794768, by rfl⟩ : syracuseStep 5059691 = 7589537) B7589537
theorem B3373127 : Blo 2247435 3373127 := bstep (se 1 (by rfl) ⟨2529845, by rfl⟩ : syracuseStep 3373127 = 5059691) B5059691
theorem B2248751 : Blo 2247435 2248751 := bstep (se 1 (by rfl) ⟨1686563, by rfl⟩ : syracuseStep 2248751 = 3373127) B3373127
theorem B3373133 : Blo 2247435 3373133 := bbase (se 3 (by rfl) ⟨632462, by rfl⟩ : syracuseStep 3373133 = 1264925) (by norm_num)
theorem B2248755 : Blo 2247435 2248755 := bstep (se 1 (by rfl) ⟨1686566, by rfl⟩ : syracuseStep 2248755 = 3373133) B3373133
theorem B5059709 : Blo 2247435 5059709 := bbase (se 3 (by rfl) ⟨948695, by rfl⟩ : syracuseStep 5059709 = 1897391) (by norm_num)
theorem B3373139 : Blo 2247435 3373139 := bstep (se 1 (by rfl) ⟨2529854, by rfl⟩ : syracuseStep 3373139 = 5059709) B5059709
theorem B2248759 : Blo 2247435 2248759 := bstep (se 1 (by rfl) ⟨1686569, by rfl⟩ : syracuseStep 2248759 = 3373139) B3373139
theorem B3794789 : Blo 2247435 3794789 := bbase (se 4 (by rfl) ⟨355761, by rfl⟩ : syracuseStep 3794789 = 711523) (by norm_num)
theorem B2529859 : Blo 2247435 2529859 := bstep (se 1 (by rfl) ⟨1897394, by rfl⟩ : syracuseStep 2529859 = 3794789) B3794789
theorem B3373145 : Blo 2247435 3373145 := bstep (se 2 (by rfl) ⟨1264929, by rfl⟩ : syracuseStep 3373145 = 2529859) B2529859
theorem B2248763 : Blo 2247435 2248763 := bstep (se 1 (by rfl) ⟨1686572, by rfl⟩ : syracuseStep 2248763 = 3373145) B3373145
theorem B4802789 : Blo 2247435 4802789 := bbase (se 4 (by rfl) ⟨450261, by rfl⟩ : syracuseStep 4802789 = 900523) (by norm_num)
theorem B3201859 : Blo 2247435 3201859 := bstep (se 1 (by rfl) ⟨2401394, by rfl⟩ : syracuseStep 3201859 = 4802789) B4802789
theorem B17076581 : Blo 2247435 17076581 := bstep (se 4 (by rfl) ⟨1600929, by rfl⟩ : syracuseStep 17076581 = 3201859) B3201859
theorem B11384387 : Blo 2247435 11384387 := bstep (se 1 (by rfl) ⟨8538290, by rfl⟩ : syracuseStep 11384387 = 17076581) B17076581
theorem B7589591 : Blo 2247435 7589591 := bstep (se 1 (by rfl) ⟨5692193, by rfl⟩ : syracuseStep 7589591 = 11384387) B11384387
theorem B5059727 : Blo 2247435 5059727 := bstep (se 1 (by rfl) ⟨3794795, by rfl⟩ : syracuseStep 5059727 = 7589591) B7589591
theorem B3373151 : Blo 2247435 3373151 := bstep (se 1 (by rfl) ⟨2529863, by rfl⟩ : syracuseStep 3373151 = 5059727) B5059727
theorem B2248767 : Blo 2247435 2248767 := bstep (se 1 (by rfl) ⟨1686575, by rfl⟩ : syracuseStep 2248767 = 3373151) B3373151
theorem B3373157 : Blo 2247435 3373157 := bbase (se 4 (by rfl) ⟨316233, by rfl⟩ : syracuseStep 3373157 = 632467) (by norm_num)
theorem B2248771 : Blo 2247435 2248771 := bstep (se 1 (by rfl) ⟨1686578, by rfl⟩ : syracuseStep 2248771 = 3373157) B3373157
theorem B3039277 : Blo 2247435 3039277 := bbase (se 3 (by rfl) ⟨569864, by rfl⟩ : syracuseStep 3039277 = 1139729) (by norm_num)
theorem B4052369 : Blo 2247435 4052369 := bstep (se 2 (by rfl) ⟨1519638, by rfl⟩ : syracuseStep 4052369 = 3039277) B3039277
theorem B10806317 : Blo 2247435 10806317 := bstep (se 3 (by rfl) ⟨2026184, by rfl⟩ : syracuseStep 10806317 = 4052369) B4052369
theorem B7204211 : Blo 2247435 7204211 := bstep (se 1 (by rfl) ⟨5403158, by rfl⟩ : syracuseStep 7204211 = 10806317) B10806317
theorem B4802807 : Blo 2247435 4802807 := bstep (se 1 (by rfl) ⟨3602105, by rfl⟩ : syracuseStep 4802807 = 7204211) B7204211
theorem B3201871 : Blo 2247435 3201871 := bstep (se 1 (by rfl) ⟨2401403, by rfl⟩ : syracuseStep 3201871 = 4802807) B4802807
theorem B4269161 : Blo 2247435 4269161 := bstep (se 2 (by rfl) ⟨1600935, by rfl⟩ : syracuseStep 4269161 = 3201871) B3201871
theorem B2846107 : Blo 2247435 2846107 := bstep (se 1 (by rfl) ⟨2134580, by rfl⟩ : syracuseStep 2846107 = 4269161) B4269161
theorem B3794809 : Blo 2247435 3794809 := bstep (se 2 (by rfl) ⟨1423053, by rfl⟩ : syracuseStep 3794809 = 2846107) B2846107
theorem B5059745 : Blo 2247435 5059745 := bstep (se 2 (by rfl) ⟨1897404, by rfl⟩ : syracuseStep 5059745 = 3794809) B3794809
theorem B3373163 : Blo 2247435 3373163 := bstep (se 1 (by rfl) ⟨2529872, by rfl⟩ : syracuseStep 3373163 = 5059745) B5059745
theorem B2248775 : Blo 2247435 2248775 := bstep (se 1 (by rfl) ⟨1686581, by rfl⟩ : syracuseStep 2248775 = 3373163) B3373163
theorem B2529877 : Blo 2247435 2529877 := bbase (se 8 (by rfl) ⟨14823, by rfl⟩ : syracuseStep 2529877 = 29647) (by norm_num)
theorem B3373169 : Blo 2247435 3373169 := bstep (se 2 (by rfl) ⟨1264938, by rfl⟩ : syracuseStep 3373169 = 2529877) B2529877
theorem B2248779 : Blo 2247435 2248779 := bstep (se 1 (by rfl) ⟨1686584, by rfl⟩ : syracuseStep 2248779 = 3373169) B3373169
theorem B2846117 : Blo 2247435 2846117 := bbase (se 4 (by rfl) ⟨266823, by rfl⟩ : syracuseStep 2846117 = 533647) (by norm_num)
theorem B7589645 : Blo 2247435 7589645 := bstep (se 3 (by rfl) ⟨1423058, by rfl⟩ : syracuseStep 7589645 = 2846117) B2846117
theorem B5059763 : Blo 2247435 5059763 := bstep (se 1 (by rfl) ⟨3794822, by rfl⟩ : syracuseStep 5059763 = 7589645) B7589645
theorem B3373175 : Blo 2247435 3373175 := bstep (se 1 (by rfl) ⟨2529881, by rfl⟩ : syracuseStep 3373175 = 5059763) B5059763
theorem B2248783 : Blo 2247435 2248783 := bstep (se 1 (by rfl) ⟨1686587, by rfl⟩ : syracuseStep 2248783 = 3373175) B3373175
theorem B3373181 : Blo 2247435 3373181 := bbase (se 3 (by rfl) ⟨632471, by rfl⟩ : syracuseStep 3373181 = 1264943) (by norm_num)
theorem B2248787 : Blo 2247435 2248787 := bstep (se 1 (by rfl) ⟨1686590, by rfl⟩ : syracuseStep 2248787 = 3373181) B3373181
theorem B5059781 : Blo 2247435 5059781 := bbase (se 4 (by rfl) ⟨474354, by rfl⟩ : syracuseStep 5059781 = 948709) (by norm_num)
theorem B3373187 : Blo 2247435 3373187 := bstep (se 1 (by rfl) ⟨2529890, by rfl⟩ : syracuseStep 3373187 = 5059781) B5059781
theorem B2248791 : Blo 2247435 2248791 := bstep (se 1 (by rfl) ⟨1686593, by rfl⟩ : syracuseStep 2248791 = 3373187) B3373187
theorem B4052405 : Blo 2247435 4052405 := bbase (se 5 (by rfl) ⟨189956, by rfl⟩ : syracuseStep 4052405 = 379913) (by norm_num)
theorem B2701603 : Blo 2247435 2701603 := bstep (se 1 (by rfl) ⟨2026202, by rfl⟩ : syracuseStep 2701603 = 4052405) B4052405
theorem B14408549 : Blo 2247435 14408549 := bstep (se 4 (by rfl) ⟨1350801, by rfl⟩ : syracuseStep 14408549 = 2701603) B2701603
theorem B9605699 : Blo 2247435 9605699 := bstep (se 1 (by rfl) ⟨7204274, by rfl⟩ : syracuseStep 9605699 = 14408549) B14408549
theorem B6403799 : Blo 2247435 6403799 := bstep (se 1 (by rfl) ⟨4802849, by rfl⟩ : syracuseStep 6403799 = 9605699) B9605699
theorem B4269199 : Blo 2247435 4269199 := bstep (se 1 (by rfl) ⟨3201899, by rfl⟩ : syracuseStep 4269199 = 6403799) B6403799
theorem B5692265 : Blo 2247435 5692265 := bstep (se 2 (by rfl) ⟨2134599, by rfl⟩ : syracuseStep 5692265 = 4269199) B4269199
theorem B3794843 : Blo 2247435 3794843 := bstep (se 1 (by rfl) ⟨2846132, by rfl⟩ : syracuseStep 3794843 = 5692265) B5692265
theorem B2529895 : Blo 2247435 2529895 := bstep (se 1 (by rfl) ⟨1897421, by rfl⟩ : syracuseStep 2529895 = 3794843) B3794843
theorem B3373193 : Blo 2247435 3373193 := bstep (se 2 (by rfl) ⟨1264947, by rfl⟩ : syracuseStep 3373193 = 2529895) B2529895
theorem B2248795 : Blo 2247435 2248795 := bstep (se 1 (by rfl) ⟨1686596, by rfl⟩ : syracuseStep 2248795 = 3373193) B3373193
theorem B11384549 : Blo 2247435 11384549 := bbase (se 4 (by rfl) ⟨1067301, by rfl⟩ : syracuseStep 11384549 = 2134603) (by norm_num)
theorem B7589699 : Blo 2247435 7589699 := bstep (se 1 (by rfl) ⟨5692274, by rfl⟩ : syracuseStep 7589699 = 11384549) B11384549
theorem B5059799 : Blo 2247435 5059799 := bstep (se 1 (by rfl) ⟨3794849, by rfl⟩ : syracuseStep 5059799 = 7589699) B7589699
theorem B3373199 : Blo 2247435 3373199 := bstep (se 1 (by rfl) ⟨2529899, by rfl⟩ : syracuseStep 3373199 = 5059799) B5059799
theorem B2248799 : Blo 2247435 2248799 := bstep (se 1 (by rfl) ⟨1686599, by rfl⟩ : syracuseStep 2248799 = 3373199) B3373199
theorem B3373205 : Blo 2247435 3373205 := bbase (se 6 (by rfl) ⟨79059, by rfl⟩ : syracuseStep 3373205 = 158119) (by norm_num)
theorem B2248803 : Blo 2247435 2248803 := bstep (se 1 (by rfl) ⟨1686602, by rfl⟩ : syracuseStep 2248803 = 3373205) B3373205
theorem B9605749 : Blo 2247435 9605749 := bbase (se 5 (by rfl) ⟨450269, by rfl⟩ : syracuseStep 9605749 = 900539) (by norm_num)
theorem B12807665 : Blo 2247435 12807665 := bstep (se 2 (by rfl) ⟨4802874, by rfl⟩ : syracuseStep 12807665 = 9605749) B9605749
theorem B8538443 : Blo 2247435 8538443 := bstep (se 1 (by rfl) ⟨6403832, by rfl⟩ : syracuseStep 8538443 = 12807665) B12807665
theorem B5692295 : Blo 2247435 5692295 := bstep (se 1 (by rfl) ⟨4269221, by rfl⟩ : syracuseStep 5692295 = 8538443) B8538443
theorem B3794863 : Blo 2247435 3794863 := bstep (se 1 (by rfl) ⟨2846147, by rfl⟩ : syracuseStep 3794863 = 5692295) B5692295
theorem B5059817 : Blo 2247435 5059817 := bstep (se 2 (by rfl) ⟨1897431, by rfl⟩ : syracuseStep 5059817 = 3794863) B3794863
theorem B3373211 : Blo 2247435 3373211 := bstep (se 1 (by rfl) ⟨2529908, by rfl⟩ : syracuseStep 3373211 = 5059817) B5059817
theorem B2248807 : Blo 2247435 2248807 := bstep (se 1 (by rfl) ⟨1686605, by rfl⟩ : syracuseStep 2248807 = 3373211) B3373211
theorem B2529913 : Blo 2247435 2529913 := bbase (se 2 (by rfl) ⟨948717, by rfl⟩ : syracuseStep 2529913 = 1897435) (by norm_num)
theorem B3373217 : Blo 2247435 3373217 := bstep (se 2 (by rfl) ⟨1264956, by rfl⟩ : syracuseStep 3373217 = 2529913) B2529913
theorem B2248811 : Blo 2247435 2248811 := bstep (se 1 (by rfl) ⟨1686608, by rfl⟩ : syracuseStep 2248811 = 3373217) B3373217
theorem B21613013 : Blo 2247435 21613013 := bbase (se 7 (by rfl) ⟨253277, by rfl⟩ : syracuseStep 21613013 = 506555) (by norm_num)
theorem B14408675 : Blo 2247435 14408675 := bstep (se 1 (by rfl) ⟨10806506, by rfl⟩ : syracuseStep 14408675 = 21613013) B21613013
theorem B9605783 : Blo 2247435 9605783 := bstep (se 1 (by rfl) ⟨7204337, by rfl⟩ : syracuseStep 9605783 = 14408675) B14408675
theorem B6403855 : Blo 2247435 6403855 := bstep (se 1 (by rfl) ⟨4802891, by rfl⟩ : syracuseStep 6403855 = 9605783) B9605783
theorem B8538473 : Blo 2247435 8538473 := bstep (se 2 (by rfl) ⟨3201927, by rfl⟩ : syracuseStep 8538473 = 6403855) B6403855
theorem B5692315 : Blo 2247435 5692315 := bstep (se 1 (by rfl) ⟨4269236, by rfl⟩ : syracuseStep 5692315 = 8538473) B8538473
theorem B7589753 : Blo 2247435 7589753 := bstep (se 2 (by rfl) ⟨2846157, by rfl⟩ : syracuseStep 7589753 = 5692315) B5692315
theorem B5059835 : Blo 2247435 5059835 := bstep (se 1 (by rfl) ⟨3794876, by rfl⟩ : syracuseStep 5059835 = 7589753) B7589753
theorem B3373223 : Blo 2247435 3373223 := bstep (se 1 (by rfl) ⟨2529917, by rfl⟩ : syracuseStep 3373223 = 5059835) B5059835
theorem B2248815 : Blo 2247435 2248815 := bstep (se 1 (by rfl) ⟨1686611, by rfl⟩ : syracuseStep 2248815 = 3373223) B3373223
theorem B3373229 : Blo 2247435 3373229 := bbase (se 3 (by rfl) ⟨632480, by rfl⟩ : syracuseStep 3373229 = 1264961) (by norm_num)
theorem B2248819 : Blo 2247435 2248819 := bstep (se 1 (by rfl) ⟨1686614, by rfl⟩ : syracuseStep 2248819 = 3373229) B3373229
theorem B5059853 : Blo 2247435 5059853 := bbase (se 3 (by rfl) ⟨948722, by rfl⟩ : syracuseStep 5059853 = 1897445) (by norm_num)
theorem B3373235 : Blo 2247435 3373235 := bstep (se 1 (by rfl) ⟨2529926, by rfl⟩ : syracuseStep 3373235 = 5059853) B5059853
theorem B2248823 : Blo 2247435 2248823 := bstep (se 1 (by rfl) ⟨1686617, by rfl⟩ : syracuseStep 2248823 = 3373235) B3373235
theorem B2846173 : Blo 2247435 2846173 := bbase (se 3 (by rfl) ⟨533657, by rfl⟩ : syracuseStep 2846173 = 1067315) (by norm_num)
theorem B3794897 : Blo 2247435 3794897 := bstep (se 2 (by rfl) ⟨1423086, by rfl⟩ : syracuseStep 3794897 = 2846173) B2846173
theorem B2529931 : Blo 2247435 2529931 := bstep (se 1 (by rfl) ⟨1897448, by rfl⟩ : syracuseStep 2529931 = 3794897) B3794897
theorem B3373241 : Blo 2247435 3373241 := bstep (se 2 (by rfl) ⟨1264965, by rfl⟩ : syracuseStep 3373241 = 2529931) B2529931
theorem B2248827 : Blo 2247435 2248827 := bstep (se 1 (by rfl) ⟨1686620, by rfl⟩ : syracuseStep 2248827 = 3373241) B3373241
theorem B19211701 : Blo 2247435 19211701 := bbase (se 5 (by rfl) ⟨900548, by rfl⟩ : syracuseStep 19211701 = 1801097) (by norm_num)
theorem B25615601 : Blo 2247435 25615601 := bstep (se 2 (by rfl) ⟨9605850, by rfl⟩ : syracuseStep 25615601 = 19211701) B19211701
theorem B17077067 : Blo 2247435 17077067 := bstep (se 1 (by rfl) ⟨12807800, by rfl⟩ : syracuseStep 17077067 = 25615601) B25615601
theorem B11384711 : Blo 2247435 11384711 := bstep (se 1 (by rfl) ⟨8538533, by rfl⟩ : syracuseStep 11384711 = 17077067) B17077067
theorem B7589807 : Blo 2247435 7589807 := bstep (se 1 (by rfl) ⟨5692355, by rfl⟩ : syracuseStep 7589807 = 11384711) B11384711
theorem B5059871 : Blo 2247435 5059871 := bstep (se 1 (by rfl) ⟨3794903, by rfl⟩ : syracuseStep 5059871 = 7589807) B7589807
theorem B3373247 : Blo 2247435 3373247 := bstep (se 1 (by rfl) ⟨2529935, by rfl⟩ : syracuseStep 3373247 = 5059871) B5059871
theorem B2248831 : Blo 2247435 2248831 := bstep (se 1 (by rfl) ⟨1686623, by rfl⟩ : syracuseStep 2248831 = 3373247) B3373247
theorem B3373253 : Blo 2247435 3373253 := bbase (se 4 (by rfl) ⟨316242, by rfl⟩ : syracuseStep 3373253 = 632485) (by norm_num)
theorem B2248835 : Blo 2247435 2248835 := bstep (se 1 (by rfl) ⟨1686626, by rfl⟩ : syracuseStep 2248835 = 3373253) B3373253
theorem B3794917 : Blo 2247435 3794917 := bbase (se 4 (by rfl) ⟨355773, by rfl⟩ : syracuseStep 3794917 = 711547) (by norm_num)
theorem B5059889 : Blo 2247435 5059889 := bstep (se 2 (by rfl) ⟨1897458, by rfl⟩ : syracuseStep 5059889 = 3794917) B3794917
theorem B3373259 : Blo 2247435 3373259 := bstep (se 1 (by rfl) ⟨2529944, by rfl⟩ : syracuseStep 3373259 = 5059889) B5059889
theorem B2248839 : Blo 2247435 2248839 := bstep (se 1 (by rfl) ⟨1686629, by rfl⟩ : syracuseStep 2248839 = 3373259) B3373259
theorem B2529949 : Blo 2247435 2529949 := bbase (se 3 (by rfl) ⟨474365, by rfl⟩ : syracuseStep 2529949 = 948731) (by norm_num)
theorem B3373265 : Blo 2247435 3373265 := bstep (se 2 (by rfl) ⟨1264974, by rfl⟩ : syracuseStep 3373265 = 2529949) B2529949
theorem B2248843 : Blo 2247435 2248843 := bstep (se 1 (by rfl) ⟨1686632, by rfl⟩ : syracuseStep 2248843 = 3373265) B3373265
theorem B7589861 : Blo 2247435 7589861 := bbase (se 4 (by rfl) ⟨711549, by rfl⟩ : syracuseStep 7589861 = 1423099) (by norm_num)
theorem B5059907 : Blo 2247435 5059907 := bstep (se 1 (by rfl) ⟨3794930, by rfl⟩ : syracuseStep 5059907 = 7589861) B7589861
theorem B3373271 : Blo 2247435 3373271 := bstep (se 1 (by rfl) ⟨2529953, by rfl⟩ : syracuseStep 3373271 = 5059907) B5059907
theorem B2248847 : Blo 2247435 2248847 := bstep (se 1 (by rfl) ⟨1686635, by rfl⟩ : syracuseStep 2248847 = 3373271) B3373271
theorem B3373277 : Blo 2247435 3373277 := bbase (se 3 (by rfl) ⟨632489, by rfl⟩ : syracuseStep 3373277 = 1264979) (by norm_num)
theorem B2248851 : Blo 2247435 2248851 := bstep (se 1 (by rfl) ⟨1686638, by rfl⟩ : syracuseStep 2248851 = 3373277) B3373277
theorem B5059925 : Blo 2247435 5059925 := bbase (se 13 (by rfl) ⟨926, by rfl⟩ : syracuseStep 5059925 = 1853) (by norm_num)
theorem B3373283 : Blo 2247435 3373283 := bstep (se 1 (by rfl) ⟨2529962, by rfl⟩ : syracuseStep 3373283 = 5059925) B5059925
theorem B2248855 : Blo 2247435 2248855 := bstep (se 1 (by rfl) ⟨1686641, by rfl⟩ : syracuseStep 2248855 = 3373283) B3373283
theorem B2401493 : Blo 2247435 2401493 := bbase (se 7 (by rfl) ⟨28142, by rfl⟩ : syracuseStep 2401493 = 56285) (by norm_num)
theorem B6403981 : Blo 2247435 6403981 := bstep (se 3 (by rfl) ⟨1200746, by rfl⟩ : syracuseStep 6403981 = 2401493) B2401493
theorem B8538641 : Blo 2247435 8538641 := bstep (se 2 (by rfl) ⟨3201990, by rfl⟩ : syracuseStep 8538641 = 6403981) B6403981
theorem B5692427 : Blo 2247435 5692427 := bstep (se 1 (by rfl) ⟨4269320, by rfl⟩ : syracuseStep 5692427 = 8538641) B8538641
theorem B3794951 : Blo 2247435 3794951 := bstep (se 1 (by rfl) ⟨2846213, by rfl⟩ : syracuseStep 3794951 = 5692427) B5692427
theorem B2529967 : Blo 2247435 2529967 := bstep (se 1 (by rfl) ⟨1897475, by rfl⟩ : syracuseStep 2529967 = 3794951) B3794951
theorem B3373289 : Blo 2247435 3373289 := bstep (se 2 (by rfl) ⟨1264983, by rfl⟩ : syracuseStep 3373289 = 2529967) B2529967
theorem B2248859 : Blo 2247435 2248859 := bstep (se 1 (by rfl) ⟨1686644, by rfl⟩ : syracuseStep 2248859 = 3373289) B3373289
theorem B24315157 : Blo 2247435 24315157 := bbase (se 6 (by rfl) ⟨569886, by rfl⟩ : syracuseStep 24315157 = 1139773) (by norm_num)
theorem B32420209 : Blo 2247435 32420209 := bstep (se 2 (by rfl) ⟨12157578, by rfl⟩ : syracuseStep 32420209 = 24315157) B24315157
theorem B43226945 : Blo 2247435 43226945 := bstep (se 2 (by rfl) ⟨16210104, by rfl⟩ : syracuseStep 43226945 = 32420209) B32420209
theorem B28817963 : Blo 2247435 28817963 := bstep (se 1 (by rfl) ⟨21613472, by rfl⟩ : syracuseStep 28817963 = 43226945) B43226945
theorem B19211975 : Blo 2247435 19211975 := bstep (se 1 (by rfl) ⟨14408981, by rfl⟩ : syracuseStep 19211975 = 28817963) B28817963
theorem B12807983 : Blo 2247435 12807983 := bstep (se 1 (by rfl) ⟨9605987, by rfl⟩ : syracuseStep 12807983 = 19211975) B19211975
theorem B8538655 : Blo 2247435 8538655 := bstep (se 1 (by rfl) ⟨6403991, by rfl⟩ : syracuseStep 8538655 = 12807983) B12807983
theorem B11384873 : Blo 2247435 11384873 := bstep (se 2 (by rfl) ⟨4269327, by rfl⟩ : syracuseStep 11384873 = 8538655) B8538655
theorem B7589915 : Blo 2247435 7589915 := bstep (se 1 (by rfl) ⟨5692436, by rfl⟩ : syracuseStep 7589915 = 11384873) B11384873
theorem B5059943 : Blo 2247435 5059943 := bstep (se 1 (by rfl) ⟨3794957, by rfl⟩ : syracuseStep 5059943 = 7589915) B7589915
theorem B3373295 : Blo 2247435 3373295 := bstep (se 1 (by rfl) ⟨2529971, by rfl⟩ : syracuseStep 3373295 = 5059943) B5059943
theorem B2248863 : Blo 2247435 2248863 := bstep (se 1 (by rfl) ⟨1686647, by rfl⟩ : syracuseStep 2248863 = 3373295) B3373295
theorem B3373301 : Blo 2247435 3373301 := bbase (se 5 (by rfl) ⟨158123, by rfl⟩ : syracuseStep 3373301 = 316247) (by norm_num)
theorem B2248867 : Blo 2247435 2248867 := bstep (se 1 (by rfl) ⟨1686650, by rfl⟩ : syracuseStep 2248867 = 3373301) B3373301
theorem B16210165 : Blo 2247435 16210165 := bbase (se 5 (by rfl) ⟨759851, by rfl⟩ : syracuseStep 16210165 = 1519703) (by norm_num)
theorem B21613553 : Blo 2247435 21613553 := bstep (se 2 (by rfl) ⟨8105082, by rfl⟩ : syracuseStep 21613553 = 16210165) B16210165
theorem B14409035 : Blo 2247435 14409035 := bstep (se 1 (by rfl) ⟨10806776, by rfl⟩ : syracuseStep 14409035 = 21613553) B21613553
theorem B9606023 : Blo 2247435 9606023 := bstep (se 1 (by rfl) ⟨7204517, by rfl⟩ : syracuseStep 9606023 = 14409035) B14409035
theorem B6404015 : Blo 2247435 6404015 := bstep (se 1 (by rfl) ⟨4803011, by rfl⟩ : syracuseStep 6404015 = 9606023) B9606023
theorem B4269343 : Blo 2247435 4269343 := bstep (se 1 (by rfl) ⟨3202007, by rfl⟩ : syracuseStep 4269343 = 6404015) B6404015
theorem B5692457 : Blo 2247435 5692457 := bstep (se 2 (by rfl) ⟨2134671, by rfl⟩ : syracuseStep 5692457 = 4269343) B4269343
theorem B3794971 : Blo 2247435 3794971 := bstep (se 1 (by rfl) ⟨2846228, by rfl⟩ : syracuseStep 3794971 = 5692457) B5692457
theorem B5059961 : Blo 2247435 5059961 := bstep (se 2 (by rfl) ⟨1897485, by rfl⟩ : syracuseStep 5059961 = 3794971) B3794971
theorem B3373307 : Blo 2247435 3373307 := bstep (se 1 (by rfl) ⟨2529980, by rfl⟩ : syracuseStep 3373307 = 5059961) B5059961
theorem B2248871 : Blo 2247435 2248871 := bstep (se 1 (by rfl) ⟨1686653, by rfl⟩ : syracuseStep 2248871 = 3373307) B3373307
theorem B2529985 : Blo 2247435 2529985 := bbase (se 2 (by rfl) ⟨948744, by rfl⟩ : syracuseStep 2529985 = 1897489) (by norm_num)
theorem B3373313 : Blo 2247435 3373313 := bstep (se 2 (by rfl) ⟨1264992, by rfl⟩ : syracuseStep 3373313 = 2529985) B2529985
theorem B2248875 : Blo 2247435 2248875 := bstep (se 1 (by rfl) ⟨1686656, by rfl⟩ : syracuseStep 2248875 = 3373313) B3373313
theorem B5692477 : Blo 2247435 5692477 := bbase (se 3 (by rfl) ⟨1067339, by rfl⟩ : syracuseStep 5692477 = 2134679) (by norm_num)
theorem B7589969 : Blo 2247435 7589969 := bstep (se 2 (by rfl) ⟨2846238, by rfl⟩ : syracuseStep 7589969 = 5692477) B5692477
theorem B5059979 : Blo 2247435 5059979 := bstep (se 1 (by rfl) ⟨3794984, by rfl⟩ : syracuseStep 5059979 = 7589969) B7589969
theorem B3373319 : Blo 2247435 3373319 := bstep (se 1 (by rfl) ⟨2529989, by rfl⟩ : syracuseStep 3373319 = 5059979) B5059979
theorem B2248879 : Blo 2247435 2248879 := bstep (se 1 (by rfl) ⟨1686659, by rfl⟩ : syracuseStep 2248879 = 3373319) B3373319
theorem B3373325 : Blo 2247435 3373325 := bbase (se 3 (by rfl) ⟨632498, by rfl⟩ : syracuseStep 3373325 = 1264997) (by norm_num)
theorem B2248883 : Blo 2247435 2248883 := bstep (se 1 (by rfl) ⟨1686662, by rfl⟩ : syracuseStep 2248883 = 3373325) B3373325
theorem B5059997 : Blo 2247435 5059997 := bbase (se 3 (by rfl) ⟨948749, by rfl⟩ : syracuseStep 5059997 = 1897499) (by norm_num)
theorem B3373331 : Blo 2247435 3373331 := bstep (se 1 (by rfl) ⟨2529998, by rfl⟩ : syracuseStep 3373331 = 5059997) B5059997
theorem B2248887 : Blo 2247435 2248887 := bstep (se 1 (by rfl) ⟨1686665, by rfl⟩ : syracuseStep 2248887 = 3373331) B3373331
theorem B3795005 : Blo 2247435 3795005 := bbase (se 3 (by rfl) ⟨711563, by rfl⟩ : syracuseStep 3795005 = 1423127) (by norm_num)
theorem B2530003 : Blo 2247435 2530003 := bstep (se 1 (by rfl) ⟨1897502, by rfl⟩ : syracuseStep 2530003 = 3795005) B3795005
theorem B3373337 : Blo 2247435 3373337 := bstep (se 2 (by rfl) ⟨1265001, by rfl⟩ : syracuseStep 3373337 = 2530003) B2530003
theorem B2248891 : Blo 2247435 2248891 := bstep (se 1 (by rfl) ⟨1686668, by rfl⟩ : syracuseStep 2248891 = 3373337) B3373337
theorem B6491461 : Blo 2247435 6491461 := bbase (se 4 (by rfl) ⟨608574, by rfl⟩ : syracuseStep 6491461 = 1217149) (by norm_num)
theorem B8655281 : Blo 2247435 8655281 := bstep (se 2 (by rfl) ⟨3245730, by rfl⟩ : syracuseStep 8655281 = 6491461) B6491461
theorem B5770187 : Blo 2247435 5770187 := bstep (se 1 (by rfl) ⟨4327640, by rfl⟩ : syracuseStep 5770187 = 8655281) B8655281
theorem B3846791 : Blo 2247435 3846791 := bstep (se 1 (by rfl) ⟨2885093, by rfl⟩ : syracuseStep 3846791 = 5770187) B5770187
theorem B10258109 : Blo 2247435 10258109 := bstep (se 3 (by rfl) ⟨1923395, by rfl⟩ : syracuseStep 10258109 = 3846791) B3846791
theorem B6838739 : Blo 2247435 6838739 := bstep (se 1 (by rfl) ⟨5129054, by rfl⟩ : syracuseStep 6838739 = 10258109) B10258109
theorem B4559159 : Blo 2247435 4559159 := bstep (se 1 (by rfl) ⟨3419369, by rfl⟩ : syracuseStep 4559159 = 6838739) B6838739
theorem B3039439 : Blo 2247435 3039439 := bstep (se 1 (by rfl) ⟨2279579, by rfl⟩ : syracuseStep 3039439 = 4559159) B4559159
theorem B4052585 : Blo 2247435 4052585 := bstep (se 2 (by rfl) ⟨1519719, by rfl⟩ : syracuseStep 4052585 = 3039439) B3039439
theorem B2701723 : Blo 2247435 2701723 := bstep (se 1 (by rfl) ⟨2026292, by rfl⟩ : syracuseStep 2701723 = 4052585) B4052585
theorem B3602297 : Blo 2247435 3602297 := bstep (se 2 (by rfl) ⟨1350861, by rfl⟩ : syracuseStep 3602297 = 2701723) B2701723
theorem B2401531 : Blo 2247435 2401531 := bstep (se 1 (by rfl) ⟨1801148, by rfl⟩ : syracuseStep 2401531 = 3602297) B3602297
theorem B12808165 : Blo 2247435 12808165 := bstep (se 4 (by rfl) ⟨1200765, by rfl⟩ : syracuseStep 12808165 = 2401531) B2401531
theorem B17077553 : Blo 2247435 17077553 := bstep (se 2 (by rfl) ⟨6404082, by rfl⟩ : syracuseStep 17077553 = 12808165) B12808165
theorem B11385035 : Blo 2247435 11385035 := bstep (se 1 (by rfl) ⟨8538776, by rfl⟩ : syracuseStep 11385035 = 17077553) B17077553
theorem B7590023 : Blo 2247435 7590023 := bstep (se 1 (by rfl) ⟨5692517, by rfl⟩ : syracuseStep 7590023 = 11385035) B11385035
theorem B5060015 : Blo 2247435 5060015 := bstep (se 1 (by rfl) ⟨3795011, by rfl⟩ : syracuseStep 5060015 = 7590023) B7590023
theorem B3373343 : Blo 2247435 3373343 := bstep (se 1 (by rfl) ⟨2530007, by rfl⟩ : syracuseStep 3373343 = 5060015) B5060015
theorem B2248895 : Blo 2247435 2248895 := bstep (se 1 (by rfl) ⟨1686671, by rfl⟩ : syracuseStep 2248895 = 3373343) B3373343
theorem B3373349 : Blo 2247435 3373349 := bbase (se 4 (by rfl) ⟨316251, by rfl⟩ : syracuseStep 3373349 = 632503) (by norm_num)
theorem B2248899 : Blo 2247435 2248899 := bstep (se 1 (by rfl) ⟨1686674, by rfl⟩ : syracuseStep 2248899 = 3373349) B3373349
theorem B2846269 : Blo 2247435 2846269 := bbase (se 3 (by rfl) ⟨533675, by rfl⟩ : syracuseStep 2846269 = 1067351) (by norm_num)
theorem B3795025 : Blo 2247435 3795025 := bstep (se 2 (by rfl) ⟨1423134, by rfl⟩ : syracuseStep 3795025 = 2846269) B2846269
theorem B5060033 : Blo 2247435 5060033 := bstep (se 2 (by rfl) ⟨1897512, by rfl⟩ : syracuseStep 5060033 = 3795025) B3795025
theorem B3373355 : Blo 2247435 3373355 := bstep (se 1 (by rfl) ⟨2530016, by rfl⟩ : syracuseStep 3373355 = 5060033) B5060033
theorem B2248903 : Blo 2247435 2248903 := bstep (se 1 (by rfl) ⟨1686677, by rfl⟩ : syracuseStep 2248903 = 3373355) B3373355
theorem B2530021 : Blo 2247435 2530021 := bbase (se 4 (by rfl) ⟨237189, by rfl⟩ : syracuseStep 2530021 = 474379) (by norm_num)
theorem B3373361 : Blo 2247435 3373361 := bstep (se 2 (by rfl) ⟨1265010, by rfl⟩ : syracuseStep 3373361 = 2530021) B2530021
theorem B2248907 : Blo 2247435 2248907 := bstep (se 1 (by rfl) ⟨1686680, by rfl⟩ : syracuseStep 2248907 = 3373361) B3373361
theorem B5403485 : Blo 2247435 5403485 := bbase (se 3 (by rfl) ⟨1013153, by rfl⟩ : syracuseStep 5403485 = 2026307) (by norm_num)
theorem B3602323 : Blo 2247435 3602323 := bstep (se 1 (by rfl) ⟨2701742, by rfl⟩ : syracuseStep 3602323 = 5403485) B5403485
theorem B4803097 : Blo 2247435 4803097 := bstep (se 2 (by rfl) ⟨1801161, by rfl⟩ : syracuseStep 4803097 = 3602323) B3602323
theorem B6404129 : Blo 2247435 6404129 := bstep (se 2 (by rfl) ⟨2401548, by rfl⟩ : syracuseStep 6404129 = 4803097) B4803097
theorem B4269419 : Blo 2247435 4269419 := bstep (se 1 (by rfl) ⟨3202064, by rfl⟩ : syracuseStep 4269419 = 6404129) B6404129
theorem B2846279 : Blo 2247435 2846279 := bstep (se 1 (by rfl) ⟨2134709, by rfl⟩ : syracuseStep 2846279 = 4269419) B4269419
theorem B7590077 : Blo 2247435 7590077 := bstep (se 3 (by rfl) ⟨1423139, by rfl⟩ : syracuseStep 7590077 = 2846279) B2846279
theorem B5060051 : Blo 2247435 5060051 := bstep (se 1 (by rfl) ⟨3795038, by rfl⟩ : syracuseStep 5060051 = 7590077) B7590077
theorem B3373367 : Blo 2247435 3373367 := bstep (se 1 (by rfl) ⟨2530025, by rfl⟩ : syracuseStep 3373367 = 5060051) B5060051
theorem B2248911 : Blo 2247435 2248911 := bstep (se 1 (by rfl) ⟨1686683, by rfl⟩ : syracuseStep 2248911 = 3373367) B3373367
theorem B3373373 : Blo 2247435 3373373 := bbase (se 3 (by rfl) ⟨632507, by rfl⟩ : syracuseStep 3373373 = 1265015) (by norm_num)
theorem B2248915 : Blo 2247435 2248915 := bstep (se 1 (by rfl) ⟨1686686, by rfl⟩ : syracuseStep 2248915 = 3373373) B3373373
theorem B5060069 : Blo 2247435 5060069 := bbase (se 4 (by rfl) ⟨474381, by rfl⟩ : syracuseStep 5060069 = 948763) (by norm_num)
theorem B3373379 : Blo 2247435 3373379 := bstep (se 1 (by rfl) ⟨2530034, by rfl⟩ : syracuseStep 3373379 = 5060069) B5060069
theorem B2248919 : Blo 2247435 2248919 := bstep (se 1 (by rfl) ⟨1686689, by rfl⟩ : syracuseStep 2248919 = 3373379) B3373379
theorem B5692589 : Blo 2247435 5692589 := bbase (se 3 (by rfl) ⟨1067360, by rfl⟩ : syracuseStep 5692589 = 2134721) (by norm_num)
theorem B3795059 : Blo 2247435 3795059 := bstep (se 1 (by rfl) ⟨2846294, by rfl⟩ : syracuseStep 3795059 = 5692589) B5692589
theorem B2530039 : Blo 2247435 2530039 := bstep (se 1 (by rfl) ⟨1897529, by rfl⟩ : syracuseStep 2530039 = 3795059) B3795059
theorem B3373385 : Blo 2247435 3373385 := bstep (se 2 (by rfl) ⟨1265019, by rfl⟩ : syracuseStep 3373385 = 2530039) B2530039
theorem B2248923 : Blo 2247435 2248923 := bstep (se 1 (by rfl) ⟨1686692, by rfl⟩ : syracuseStep 2248923 = 3373385) B3373385
theorem B8105285 : Blo 2247435 8105285 := bbase (se 4 (by rfl) ⟨759870, by rfl⟩ : syracuseStep 8105285 = 1519741) (by norm_num)
theorem B5403523 : Blo 2247435 5403523 := bstep (se 1 (by rfl) ⟨4052642, by rfl⟩ : syracuseStep 5403523 = 8105285) B8105285
theorem B7204697 : Blo 2247435 7204697 := bstep (se 2 (by rfl) ⟨2701761, by rfl⟩ : syracuseStep 7204697 = 5403523) B5403523
theorem B4803131 : Blo 2247435 4803131 := bstep (se 1 (by rfl) ⟨3602348, by rfl⟩ : syracuseStep 4803131 = 7204697) B7204697
theorem B3202087 : Blo 2247435 3202087 := bstep (se 1 (by rfl) ⟨2401565, by rfl⟩ : syracuseStep 3202087 = 4803131) B4803131
theorem B4269449 : Blo 2247435 4269449 := bstep (se 2 (by rfl) ⟨1601043, by rfl⟩ : syracuseStep 4269449 = 3202087) B3202087
theorem B11385197 : Blo 2247435 11385197 := bstep (se 3 (by rfl) ⟨2134724, by rfl⟩ : syracuseStep 11385197 = 4269449) B4269449
theorem B7590131 : Blo 2247435 7590131 := bstep (se 1 (by rfl) ⟨5692598, by rfl⟩ : syracuseStep 7590131 = 11385197) B11385197
theorem B5060087 : Blo 2247435 5060087 := bstep (se 1 (by rfl) ⟨3795065, by rfl⟩ : syracuseStep 5060087 = 7590131) B7590131
theorem B3373391 : Blo 2247435 3373391 := bstep (se 1 (by rfl) ⟨2530043, by rfl⟩ : syracuseStep 3373391 = 5060087) B5060087
theorem B2248927 : Blo 2247435 2248927 := bstep (se 1 (by rfl) ⟨1686695, by rfl⟩ : syracuseStep 2248927 = 3373391) B3373391
theorem B3373397 : Blo 2247435 3373397 := bbase (se 10 (by rfl) ⟨4941, by rfl⟩ : syracuseStep 3373397 = 9883) (by norm_num)
theorem B2248931 : Blo 2247435 2248931 := bstep (se 1 (by rfl) ⟨1686698, by rfl⟩ : syracuseStep 2248931 = 3373397) B3373397
theorem B6404197 : Blo 2247435 6404197 := bbase (se 4 (by rfl) ⟨600393, by rfl⟩ : syracuseStep 6404197 = 1200787) (by norm_num)
theorem B8538929 : Blo 2247435 8538929 := bstep (se 2 (by rfl) ⟨3202098, by rfl⟩ : syracuseStep 8538929 = 6404197) B6404197
theorem B5692619 : Blo 2247435 5692619 := bstep (se 1 (by rfl) ⟨4269464, by rfl⟩ : syracuseStep 5692619 = 8538929) B8538929
theorem B3795079 : Blo 2247435 3795079 := bstep (se 1 (by rfl) ⟨2846309, by rfl⟩ : syracuseStep 3795079 = 5692619) B5692619
theorem B5060105 : Blo 2247435 5060105 := bstep (se 2 (by rfl) ⟨1897539, by rfl⟩ : syracuseStep 5060105 = 3795079) B3795079
theorem B3373403 : Blo 2247435 3373403 := bstep (se 1 (by rfl) ⟨2530052, by rfl⟩ : syracuseStep 3373403 = 5060105) B5060105
theorem B2248935 : Blo 2247435 2248935 := bstep (se 1 (by rfl) ⟨1686701, by rfl⟩ : syracuseStep 2248935 = 3373403) B3373403
theorem B2530057 : Blo 2247435 2530057 := bbase (se 2 (by rfl) ⟨948771, by rfl⟩ : syracuseStep 2530057 = 1897543) (by norm_num)
theorem B3373409 : Blo 2247435 3373409 := bstep (se 2 (by rfl) ⟨1265028, by rfl⟩ : syracuseStep 3373409 = 2530057) B2530057
theorem B2248939 : Blo 2247435 2248939 := bstep (se 1 (by rfl) ⟨1686704, by rfl⟩ : syracuseStep 2248939 = 3373409) B3373409
theorem B10258325 : Blo 2247435 10258325 := bbase (se 6 (by rfl) ⟨240429, by rfl⟩ : syracuseStep 10258325 = 480859) (by norm_num)
theorem B6838883 : Blo 2247435 6838883 := bstep (se 1 (by rfl) ⟨5129162, by rfl⟩ : syracuseStep 6838883 = 10258325) B10258325
theorem B4559255 : Blo 2247435 4559255 := bstep (se 1 (by rfl) ⟨3419441, by rfl⟩ : syracuseStep 4559255 = 6838883) B6838883
theorem B3039503 : Blo 2247435 3039503 := bstep (se 1 (by rfl) ⟨2279627, by rfl⟩ : syracuseStep 3039503 = 4559255) B4559255
theorem B8105341 : Blo 2247435 8105341 := bstep (se 3 (by rfl) ⟨1519751, by rfl⟩ : syracuseStep 8105341 = 3039503) B3039503
theorem B10807121 : Blo 2247435 10807121 := bstep (se 2 (by rfl) ⟨4052670, by rfl⟩ : syracuseStep 10807121 = 8105341) B8105341
theorem B28818989 : Blo 2247435 28818989 := bstep (se 3 (by rfl) ⟨5403560, by rfl⟩ : syracuseStep 28818989 = 10807121) B10807121
theorem B19212659 : Blo 2247435 19212659 := bstep (se 1 (by rfl) ⟨14409494, by rfl⟩ : syracuseStep 19212659 = 28818989) B28818989
theorem B12808439 : Blo 2247435 12808439 := bstep (se 1 (by rfl) ⟨9606329, by rfl⟩ : syracuseStep 12808439 = 19212659) B19212659
theorem B8538959 : Blo 2247435 8538959 := bstep (se 1 (by rfl) ⟨6404219, by rfl⟩ : syracuseStep 8538959 = 12808439) B12808439
theorem B5692639 : Blo 2247435 5692639 := bstep (se 1 (by rfl) ⟨4269479, by rfl⟩ : syracuseStep 5692639 = 8538959) B8538959
theorem B7590185 : Blo 2247435 7590185 := bstep (se 2 (by rfl) ⟨2846319, by rfl⟩ : syracuseStep 7590185 = 5692639) B5692639
theorem B5060123 : Blo 2247435 5060123 := bstep (se 1 (by rfl) ⟨3795092, by rfl⟩ : syracuseStep 5060123 = 7590185) B7590185
theorem B3373415 : Blo 2247435 3373415 := bstep (se 1 (by rfl) ⟨2530061, by rfl⟩ : syracuseStep 3373415 = 5060123) B5060123
theorem B2248943 : Blo 2247435 2248943 := bstep (se 1 (by rfl) ⟨1686707, by rfl⟩ : syracuseStep 2248943 = 3373415) B3373415
theorem B3373421 : Blo 2247435 3373421 := bbase (se 3 (by rfl) ⟨632516, by rfl⟩ : syracuseStep 3373421 = 1265033) (by norm_num)
theorem B2248947 : Blo 2247435 2248947 := bstep (se 1 (by rfl) ⟨1686710, by rfl⟩ : syracuseStep 2248947 = 3373421) B3373421
theorem B5060141 : Blo 2247435 5060141 := bbase (se 3 (by rfl) ⟨948776, by rfl⟩ : syracuseStep 5060141 = 1897553) (by norm_num)
theorem B3373427 : Blo 2247435 3373427 := bstep (se 1 (by rfl) ⟨2530070, by rfl⟩ : syracuseStep 3373427 = 5060141) B5060141
theorem B2248951 : Blo 2247435 2248951 := bstep (se 1 (by rfl) ⟨1686713, by rfl⟩ : syracuseStep 2248951 = 3373427) B3373427
theorem B2738657 : Blo 2247435 2738657 := bbase (se 2 (by rfl) ⟨1026996, by rfl⟩ : syracuseStep 2738657 = 2053993) (by norm_num)
theorem B7303085 : Blo 2247435 7303085 := bstep (se 3 (by rfl) ⟨1369328, by rfl⟩ : syracuseStep 7303085 = 2738657) B2738657
theorem B77899573 : Blo 2247435 77899573 := bstep (se 5 (by rfl) ⟨3651542, by rfl⟩ : syracuseStep 77899573 = 7303085) B7303085
theorem B415464389 : Blo 2247435 415464389 := bstep (se 4 (by rfl) ⟨38949786, by rfl⟩ : syracuseStep 415464389 = 77899573) B77899573
theorem B276976259 : Blo 2247435 276976259 := bstep (se 1 (by rfl) ⟨207732194, by rfl⟩ : syracuseStep 276976259 = 415464389) B415464389
theorem B184650839 : Blo 2247435 184650839 := bstep (se 1 (by rfl) ⟨138488129, by rfl⟩ : syracuseStep 184650839 = 276976259) B276976259
theorem B123100559 : Blo 2247435 123100559 := bstep (se 1 (by rfl) ⟨92325419, by rfl⟩ : syracuseStep 123100559 = 184650839) B184650839
theorem B82067039 : Blo 2247435 82067039 := bstep (se 1 (by rfl) ⟨61550279, by rfl⟩ : syracuseStep 82067039 = 123100559) B123100559
theorem B54711359 : Blo 2247435 54711359 := bstep (se 1 (by rfl) ⟨41033519, by rfl⟩ : syracuseStep 54711359 = 82067039) B82067039
theorem B36474239 : Blo 2247435 36474239 := bstep (se 1 (by rfl) ⟨27355679, by rfl⟩ : syracuseStep 36474239 = 54711359) B54711359
theorem B24316159 : Blo 2247435 24316159 := bstep (se 1 (by rfl) ⟨18237119, by rfl⟩ : syracuseStep 24316159 = 36474239) B36474239
theorem B32421545 : Blo 2247435 32421545 := bstep (se 2 (by rfl) ⟨12158079, by rfl⟩ : syracuseStep 32421545 = 24316159) B24316159
theorem B21614363 : Blo 2247435 21614363 := bstep (se 1 (by rfl) ⟨16210772, by rfl⟩ : syracuseStep 21614363 = 32421545) B32421545
theorem B14409575 : Blo 2247435 14409575 := bstep (se 1 (by rfl) ⟨10807181, by rfl⟩ : syracuseStep 14409575 = 21614363) B21614363
theorem B9606383 : Blo 2247435 9606383 := bstep (se 1 (by rfl) ⟨7204787, by rfl⟩ : syracuseStep 9606383 = 14409575) B14409575
theorem B6404255 : Blo 2247435 6404255 := bstep (se 1 (by rfl) ⟨4803191, by rfl⟩ : syracuseStep 6404255 = 9606383) B9606383
theorem B4269503 : Blo 2247435 4269503 := bstep (se 1 (by rfl) ⟨3202127, by rfl⟩ : syracuseStep 4269503 = 6404255) B6404255
theorem B2846335 : Blo 2247435 2846335 := bstep (se 1 (by rfl) ⟨2134751, by rfl⟩ : syracuseStep 2846335 = 4269503) B4269503
theorem B3795113 : Blo 2247435 3795113 := bstep (se 2 (by rfl) ⟨1423167, by rfl⟩ : syracuseStep 3795113 = 2846335) B2846335
theorem B2530075 : Blo 2247435 2530075 := bstep (se 1 (by rfl) ⟨1897556, by rfl⟩ : syracuseStep 2530075 = 3795113) B3795113
theorem B3373433 : Blo 2247435 3373433 := bstep (se 2 (by rfl) ⟨1265037, by rfl⟩ : syracuseStep 3373433 = 2530075) B2530075
theorem B2248955 : Blo 2247435 2248955 := bstep (se 1 (by rfl) ⟨1686716, by rfl⟩ : syracuseStep 2248955 = 3373433) B3373433
theorem B5770349 : Blo 2247435 5770349 := bbase (se 3 (by rfl) ⟨1081940, by rfl⟩ : syracuseStep 5770349 = 2163881) (by norm_num)
theorem B3846899 : Blo 2247435 3846899 := bstep (se 1 (by rfl) ⟨2885174, by rfl⟩ : syracuseStep 3846899 = 5770349) B5770349
theorem B10258397 : Blo 2247435 10258397 := bstep (se 3 (by rfl) ⟨1923449, by rfl⟩ : syracuseStep 10258397 = 3846899) B3846899
theorem B6838931 : Blo 2247435 6838931 := bstep (se 1 (by rfl) ⟨5129198, by rfl⟩ : syracuseStep 6838931 = 10258397) B10258397
theorem B18237149 : Blo 2247435 18237149 := bstep (se 3 (by rfl) ⟨3419465, by rfl⟩ : syracuseStep 18237149 = 6838931) B6838931
theorem B12158099 : Blo 2247435 12158099 := bstep (se 1 (by rfl) ⟨9118574, by rfl⟩ : syracuseStep 12158099 = 18237149) B18237149
theorem B8105399 : Blo 2247435 8105399 := bstep (se 1 (by rfl) ⟨6079049, by rfl⟩ : syracuseStep 8105399 = 12158099) B12158099
theorem B5403599 : Blo 2247435 5403599 := bstep (se 1 (by rfl) ⟨4052699, by rfl⟩ : syracuseStep 5403599 = 8105399) B8105399
theorem B3602399 : Blo 2247435 3602399 := bstep (se 1 (by rfl) ⟨2701799, by rfl⟩ : syracuseStep 3602399 = 5403599) B5403599
theorem B38425589 : Blo 2247435 38425589 := bstep (se 5 (by rfl) ⟨1801199, by rfl⟩ : syracuseStep 38425589 = 3602399) B3602399
theorem B25617059 : Blo 2247435 25617059 := bstep (se 1 (by rfl) ⟨19212794, by rfl⟩ : syracuseStep 25617059 = 38425589) B38425589
theorem B17078039 : Blo 2247435 17078039 := bstep (se 1 (by rfl) ⟨12808529, by rfl⟩ : syracuseStep 17078039 = 25617059) B25617059
theorem B11385359 : Blo 2247435 11385359 := bstep (se 1 (by rfl) ⟨8539019, by rfl⟩ : syracuseStep 11385359 = 17078039) B17078039
theorem B7590239 : Blo 2247435 7590239 := bstep (se 1 (by rfl) ⟨5692679, by rfl⟩ : syracuseStep 7590239 = 11385359) B11385359
theorem B5060159 : Blo 2247435 5060159 := bstep (se 1 (by rfl) ⟨3795119, by rfl⟩ : syracuseStep 5060159 = 7590239) B7590239
theorem B3373439 : Blo 2247435 3373439 := bstep (se 1 (by rfl) ⟨2530079, by rfl⟩ : syracuseStep 3373439 = 5060159) B5060159
theorem B2248959 : Blo 2247435 2248959 := bstep (se 1 (by rfl) ⟨1686719, by rfl⟩ : syracuseStep 2248959 = 3373439) B3373439
theorem B3373445 : Blo 2247435 3373445 := bbase (se 4 (by rfl) ⟨316260, by rfl⟩ : syracuseStep 3373445 = 632521) (by norm_num)
theorem B2248963 : Blo 2247435 2248963 := bstep (se 1 (by rfl) ⟨1686722, by rfl⟩ : syracuseStep 2248963 = 3373445) B3373445
theorem B3795133 : Blo 2247435 3795133 := bbase (se 3 (by rfl) ⟨711587, by rfl⟩ : syracuseStep 3795133 = 1423175) (by norm_num)
theorem B5060177 : Blo 2247435 5060177 := bstep (se 2 (by rfl) ⟨1897566, by rfl⟩ : syracuseStep 5060177 = 3795133) B3795133
theorem B3373451 : Blo 2247435 3373451 := bstep (se 1 (by rfl) ⟨2530088, by rfl⟩ : syracuseStep 3373451 = 5060177) B5060177
theorem B2248967 : Blo 2247435 2248967 := bstep (se 1 (by rfl) ⟨1686725, by rfl⟩ : syracuseStep 2248967 = 3373451) B3373451
theorem B2530093 : Blo 2247435 2530093 := bbase (se 3 (by rfl) ⟨474392, by rfl⟩ : syracuseStep 2530093 = 948785) (by norm_num)
theorem B3373457 : Blo 2247435 3373457 := bstep (se 2 (by rfl) ⟨1265046, by rfl⟩ : syracuseStep 3373457 = 2530093) B2530093
theorem B2248971 : Blo 2247435 2248971 := bstep (se 1 (by rfl) ⟨1686728, by rfl⟩ : syracuseStep 2248971 = 3373457) B3373457
theorem B7590293 : Blo 2247435 7590293 := bbase (se 6 (by rfl) ⟨177897, by rfl⟩ : syracuseStep 7590293 = 355795) (by norm_num)
theorem B5060195 : Blo 2247435 5060195 := bstep (se 1 (by rfl) ⟨3795146, by rfl⟩ : syracuseStep 5060195 = 7590293) B7590293
theorem B3373463 : Blo 2247435 3373463 := bstep (se 1 (by rfl) ⟨2530097, by rfl⟩ : syracuseStep 3373463 = 5060195) B5060195
theorem B2248975 : Blo 2247435 2248975 := bstep (se 1 (by rfl) ⟨1686731, by rfl⟩ : syracuseStep 2248975 = 3373463) B3373463
theorem B3373469 : Blo 2247435 3373469 := bbase (se 3 (by rfl) ⟨632525, by rfl⟩ : syracuseStep 3373469 = 1265051) (by norm_num)
theorem B2248979 : Blo 2247435 2248979 := bstep (se 1 (by rfl) ⟨1686734, by rfl⟩ : syracuseStep 2248979 = 3373469) B3373469
theorem B5060213 : Blo 2247435 5060213 := bbase (se 5 (by rfl) ⟨237197, by rfl⟩ : syracuseStep 5060213 = 474395) (by norm_num)
theorem B3373475 : Blo 2247435 3373475 := bstep (se 1 (by rfl) ⟨2530106, by rfl⟩ : syracuseStep 3373475 = 5060213) B5060213
theorem B2248983 : Blo 2247435 2248983 := bstep (se 1 (by rfl) ⟨1686737, by rfl⟩ : syracuseStep 2248983 = 3373475) B3373475
theorem B3419509 : Blo 2247435 3419509 := bbase (se 5 (by rfl) ⟨160289, by rfl⟩ : syracuseStep 3419509 = 320579) (by norm_num)
theorem B4559345 : Blo 2247435 4559345 := bstep (se 2 (by rfl) ⟨1709754, by rfl⟩ : syracuseStep 4559345 = 3419509) B3419509
theorem B3039563 : Blo 2247435 3039563 := bstep (se 1 (by rfl) ⟨2279672, by rfl⟩ : syracuseStep 3039563 = 4559345) B4559345
theorem B8105501 : Blo 2247435 8105501 := bstep (se 3 (by rfl) ⟨1519781, by rfl⟩ : syracuseStep 8105501 = 3039563) B3039563
theorem B5403667 : Blo 2247435 5403667 := bstep (se 1 (by rfl) ⟨4052750, by rfl⟩ : syracuseStep 5403667 = 8105501) B8105501
theorem B7204889 : Blo 2247435 7204889 := bstep (se 2 (by rfl) ⟨2701833, by rfl⟩ : syracuseStep 7204889 = 5403667) B5403667
theorem B19213037 : Blo 2247435 19213037 := bstep (se 3 (by rfl) ⟨3602444, by rfl⟩ : syracuseStep 19213037 = 7204889) B7204889
theorem B12808691 : Blo 2247435 12808691 := bstep (se 1 (by rfl) ⟨9606518, by rfl⟩ : syracuseStep 12808691 = 19213037) B19213037
theorem B8539127 : Blo 2247435 8539127 := bstep (se 1 (by rfl) ⟨6404345, by rfl⟩ : syracuseStep 8539127 = 12808691) B12808691
theorem B5692751 : Blo 2247435 5692751 := bstep (se 1 (by rfl) ⟨4269563, by rfl⟩ : syracuseStep 5692751 = 8539127) B8539127
theorem B3795167 : Blo 2247435 3795167 := bstep (se 1 (by rfl) ⟨2846375, by rfl⟩ : syracuseStep 3795167 = 5692751) B5692751
theorem B2530111 : Blo 2247435 2530111 := bstep (se 1 (by rfl) ⟨1897583, by rfl⟩ : syracuseStep 2530111 = 3795167) B3795167
theorem B3373481 : Blo 2247435 3373481 := bstep (se 2 (by rfl) ⟨1265055, by rfl⟩ : syracuseStep 3373481 = 2530111) B2530111
theorem B2248987 : Blo 2247435 2248987 := bstep (se 1 (by rfl) ⟨1686740, by rfl⟩ : syracuseStep 2248987 = 3373481) B3373481
theorem B8539141 : Blo 2247435 8539141 := bbase (se 4 (by rfl) ⟨800544, by rfl⟩ : syracuseStep 8539141 = 1601089) (by norm_num)
theorem B11385521 : Blo 2247435 11385521 := bstep (se 2 (by rfl) ⟨4269570, by rfl⟩ : syracuseStep 11385521 = 8539141) B8539141
theorem B7590347 : Blo 2247435 7590347 := bstep (se 1 (by rfl) ⟨5692760, by rfl⟩ : syracuseStep 7590347 = 11385521) B11385521
theorem B5060231 : Blo 2247435 5060231 := bstep (se 1 (by rfl) ⟨3795173, by rfl⟩ : syracuseStep 5060231 = 7590347) B7590347
theorem B3373487 : Blo 2247435 3373487 := bstep (se 1 (by rfl) ⟨2530115, by rfl⟩ : syracuseStep 3373487 = 5060231) B5060231
theorem B2248991 : Blo 2247435 2248991 := bstep (se 1 (by rfl) ⟨1686743, by rfl⟩ : syracuseStep 2248991 = 3373487) B3373487
theorem B3373493 : Blo 2247435 3373493 := bbase (se 5 (by rfl) ⟨158132, by rfl⟩ : syracuseStep 3373493 = 316265) (by norm_num)
theorem B2248995 : Blo 2247435 2248995 := bstep (se 1 (by rfl) ⟨1686746, by rfl⟩ : syracuseStep 2248995 = 3373493) B3373493
theorem B5692781 : Blo 2247435 5692781 := bbase (se 3 (by rfl) ⟨1067396, by rfl⟩ : syracuseStep 5692781 = 2134793) (by norm_num)
theorem B3795187 : Blo 2247435 3795187 := bstep (se 1 (by rfl) ⟨2846390, by rfl⟩ : syracuseStep 3795187 = 5692781) B5692781
theorem B5060249 : Blo 2247435 5060249 := bstep (se 2 (by rfl) ⟨1897593, by rfl⟩ : syracuseStep 5060249 = 3795187) B3795187
theorem B3373499 : Blo 2247435 3373499 := bstep (se 1 (by rfl) ⟨2530124, by rfl⟩ : syracuseStep 3373499 = 5060249) B5060249
theorem B2248999 : Blo 2247435 2248999 := bstep (se 1 (by rfl) ⟨1686749, by rfl⟩ : syracuseStep 2248999 = 3373499) B3373499
theorem B2530129 : Blo 2247435 2530129 := bbase (se 2 (by rfl) ⟨948798, by rfl⟩ : syracuseStep 2530129 = 1897597) (by norm_num)
theorem B3373505 : Blo 2247435 3373505 := bstep (se 2 (by rfl) ⟨1265064, by rfl⟩ : syracuseStep 3373505 = 2530129) B2530129
theorem B2249003 : Blo 2247435 2249003 := bstep (se 1 (by rfl) ⟨1686752, by rfl⟩ : syracuseStep 2249003 = 3373505) B3373505
theorem B3602477 : Blo 2247435 3602477 := bbase (se 3 (by rfl) ⟨675464, by rfl⟩ : syracuseStep 3602477 = 1350929) (by norm_num)
theorem B2401651 : Blo 2247435 2401651 := bstep (se 1 (by rfl) ⟨1801238, by rfl⟩ : syracuseStep 2401651 = 3602477) B3602477
theorem B3202201 : Blo 2247435 3202201 := bstep (se 2 (by rfl) ⟨1200825, by rfl⟩ : syracuseStep 3202201 = 2401651) B2401651
theorem B4269601 : Blo 2247435 4269601 := bstep (se 2 (by rfl) ⟨1601100, by rfl⟩ : syracuseStep 4269601 = 3202201) B3202201
theorem B5692801 : Blo 2247435 5692801 := bstep (se 2 (by rfl) ⟨2134800, by rfl⟩ : syracuseStep 5692801 = 4269601) B4269601
theorem B7590401 : Blo 2247435 7590401 := bstep (se 2 (by rfl) ⟨2846400, by rfl⟩ : syracuseStep 7590401 = 5692801) B5692801
theorem B5060267 : Blo 2247435 5060267 := bstep (se 1 (by rfl) ⟨3795200, by rfl⟩ : syracuseStep 5060267 = 7590401) B7590401
theorem B3373511 : Blo 2247435 3373511 := bstep (se 1 (by rfl) ⟨2530133, by rfl⟩ : syracuseStep 3373511 = 5060267) B5060267
theorem B2249007 : Blo 2247435 2249007 := bstep (se 1 (by rfl) ⟨1686755, by rfl⟩ : syracuseStep 2249007 = 3373511) B3373511
theorem B3373517 : Blo 2247435 3373517 := bbase (se 3 (by rfl) ⟨632534, by rfl⟩ : syracuseStep 3373517 = 1265069) (by norm_num)
theorem B2249011 : Blo 2247435 2249011 := bstep (se 1 (by rfl) ⟨1686758, by rfl⟩ : syracuseStep 2249011 = 3373517) B3373517
theorem B5060285 : Blo 2247435 5060285 := bbase (se 3 (by rfl) ⟨948803, by rfl⟩ : syracuseStep 5060285 = 1897607) (by norm_num)
theorem B3373523 : Blo 2247435 3373523 := bstep (se 1 (by rfl) ⟨2530142, by rfl⟩ : syracuseStep 3373523 = 5060285) B5060285
theorem B2249015 : Blo 2247435 2249015 := bstep (se 1 (by rfl) ⟨1686761, by rfl⟩ : syracuseStep 2249015 = 3373523) B3373523
theorem B3795221 : Blo 2247435 3795221 := bbase (se 6 (by rfl) ⟨88950, by rfl⟩ : syracuseStep 3795221 = 177901) (by norm_num)
theorem B2530147 : Blo 2247435 2530147 := bstep (se 1 (by rfl) ⟨1897610, by rfl⟩ : syracuseStep 2530147 = 3795221) B3795221
theorem B3373529 : Blo 2247435 3373529 := bstep (se 2 (by rfl) ⟨1265073, by rfl⟩ : syracuseStep 3373529 = 2530147) B2530147
theorem B2249019 : Blo 2247435 2249019 := bstep (se 1 (by rfl) ⟨1686764, by rfl⟩ : syracuseStep 2249019 = 3373529) B3373529
theorem B2885257 : Blo 2247435 2885257 := bbase (se 2 (by rfl) ⟨1081971, by rfl⟩ : syracuseStep 2885257 = 2163943) (by norm_num)
theorem B3847009 : Blo 2247435 3847009 := bstep (se 2 (by rfl) ⟨1442628, by rfl⟩ : syracuseStep 3847009 = 2885257) B2885257
theorem B5129345 : Blo 2247435 5129345 := bstep (se 2 (by rfl) ⟨1923504, by rfl⟩ : syracuseStep 5129345 = 3847009) B3847009
theorem B3419563 : Blo 2247435 3419563 := bstep (se 1 (by rfl) ⟨2564672, by rfl⟩ : syracuseStep 3419563 = 5129345) B5129345
theorem B4559417 : Blo 2247435 4559417 := bstep (se 2 (by rfl) ⟨1709781, by rfl⟩ : syracuseStep 4559417 = 3419563) B3419563
theorem B3039611 : Blo 2247435 3039611 := bstep (se 1 (by rfl) ⟨2279708, by rfl⟩ : syracuseStep 3039611 = 4559417) B4559417
theorem B32422517 : Blo 2247435 32422517 := bstep (se 5 (by rfl) ⟨1519805, by rfl⟩ : syracuseStep 32422517 = 3039611) B3039611
theorem B21615011 : Blo 2247435 21615011 := bstep (se 1 (by rfl) ⟨16211258, by rfl⟩ : syracuseStep 21615011 = 32422517) B32422517
theorem B14410007 : Blo 2247435 14410007 := bstep (se 1 (by rfl) ⟨10807505, by rfl⟩ : syracuseStep 14410007 = 21615011) B21615011
theorem B9606671 : Blo 2247435 9606671 := bstep (se 1 (by rfl) ⟨7205003, by rfl⟩ : syracuseStep 9606671 = 14410007) B14410007
theorem B6404447 : Blo 2247435 6404447 := bstep (se 1 (by rfl) ⟨4803335, by rfl⟩ : syracuseStep 6404447 = 9606671) B9606671
theorem B17078525 : Blo 2247435 17078525 := bstep (se 3 (by rfl) ⟨3202223, by rfl⟩ : syracuseStep 17078525 = 6404447) B6404447
theorem B11385683 : Blo 2247435 11385683 := bstep (se 1 (by rfl) ⟨8539262, by rfl⟩ : syracuseStep 11385683 = 17078525) B17078525
theorem B7590455 : Blo 2247435 7590455 := bstep (se 1 (by rfl) ⟨5692841, by rfl⟩ : syracuseStep 7590455 = 11385683) B11385683
theorem B5060303 : Blo 2247435 5060303 := bstep (se 1 (by rfl) ⟨3795227, by rfl⟩ : syracuseStep 5060303 = 7590455) B7590455
theorem B3373535 : Blo 2247435 3373535 := bstep (se 1 (by rfl) ⟨2530151, by rfl⟩ : syracuseStep 3373535 = 5060303) B5060303
theorem B2249023 : Blo 2247435 2249023 := bstep (se 1 (by rfl) ⟨1686767, by rfl⟩ : syracuseStep 2249023 = 3373535) B3373535
theorem B3373541 : Blo 2247435 3373541 := bbase (se 4 (by rfl) ⟨316269, by rfl⟩ : syracuseStep 3373541 = 632539) (by norm_num)
theorem B2249027 : Blo 2247435 2249027 := bstep (se 1 (by rfl) ⟨1686770, by rfl⟩ : syracuseStep 2249027 = 3373541) B3373541
theorem B5403773 : Blo 2247435 5403773 := bbase (se 3 (by rfl) ⟨1013207, by rfl⟩ : syracuseStep 5403773 = 2026415) (by norm_num)
theorem B14410061 : Blo 2247435 14410061 := bstep (se 3 (by rfl) ⟨2701886, by rfl⟩ : syracuseStep 14410061 = 5403773) B5403773
theorem B9606707 : Blo 2247435 9606707 := bstep (se 1 (by rfl) ⟨7205030, by rfl⟩ : syracuseStep 9606707 = 14410061) B14410061
theorem B6404471 : Blo 2247435 6404471 := bstep (se 1 (by rfl) ⟨4803353, by rfl⟩ : syracuseStep 6404471 = 9606707) B9606707
theorem B4269647 : Blo 2247435 4269647 := bstep (se 1 (by rfl) ⟨3202235, by rfl⟩ : syracuseStep 4269647 = 6404471) B6404471
theorem B2846431 : Blo 2247435 2846431 := bstep (se 1 (by rfl) ⟨2134823, by rfl⟩ : syracuseStep 2846431 = 4269647) B4269647
theorem B3795241 : Blo 2247435 3795241 := bstep (se 2 (by rfl) ⟨1423215, by rfl⟩ : syracuseStep 3795241 = 2846431) B2846431
theorem B5060321 : Blo 2247435 5060321 := bstep (se 2 (by rfl) ⟨1897620, by rfl⟩ : syracuseStep 5060321 = 3795241) B3795241
theorem B3373547 : Blo 2247435 3373547 := bstep (se 1 (by rfl) ⟨2530160, by rfl⟩ : syracuseStep 3373547 = 5060321) B5060321
theorem B2249031 : Blo 2247435 2249031 := bstep (se 1 (by rfl) ⟨1686773, by rfl⟩ : syracuseStep 2249031 = 3373547) B3373547
theorem B2530165 : Blo 2247435 2530165 := bbase (se 5 (by rfl) ⟨118601, by rfl⟩ : syracuseStep 2530165 = 237203) (by norm_num)
theorem B3373553 : Blo 2247435 3373553 := bstep (se 2 (by rfl) ⟨1265082, by rfl⟩ : syracuseStep 3373553 = 2530165) B2530165
theorem B2249035 : Blo 2247435 2249035 := bstep (se 1 (by rfl) ⟨1686776, by rfl⟩ : syracuseStep 2249035 = 3373553) B3373553
theorem B2846441 : Blo 2247435 2846441 := bbase (se 2 (by rfl) ⟨1067415, by rfl⟩ : syracuseStep 2846441 = 2134831) (by norm_num)
theorem B7590509 : Blo 2247435 7590509 := bstep (se 3 (by rfl) ⟨1423220, by rfl⟩ : syracuseStep 7590509 = 2846441) B2846441
theorem B5060339 : Blo 2247435 5060339 := bstep (se 1 (by rfl) ⟨3795254, by rfl⟩ : syracuseStep 5060339 = 7590509) B7590509
theorem B3373559 : Blo 2247435 3373559 := bstep (se 1 (by rfl) ⟨2530169, by rfl⟩ : syracuseStep 3373559 = 5060339) B5060339
theorem B2249039 : Blo 2247435 2249039 := bstep (se 1 (by rfl) ⟨1686779, by rfl⟩ : syracuseStep 2249039 = 3373559) B3373559
theorem B3373565 : Blo 2247435 3373565 := bbase (se 3 (by rfl) ⟨632543, by rfl⟩ : syracuseStep 3373565 = 1265087) (by norm_num)
theorem B2249043 : Blo 2247435 2249043 := bstep (se 1 (by rfl) ⟨1686782, by rfl⟩ : syracuseStep 2249043 = 3373565) B3373565
theorem B5060357 : Blo 2247435 5060357 := bbase (se 4 (by rfl) ⟨474408, by rfl⟩ : syracuseStep 5060357 = 948817) (by norm_num)
theorem B3373571 : Blo 2247435 3373571 := bstep (se 1 (by rfl) ⟨2530178, by rfl⟩ : syracuseStep 3373571 = 5060357) B5060357
theorem B2249047 : Blo 2247435 2249047 := bstep (se 1 (by rfl) ⟨1686785, by rfl⟩ : syracuseStep 2249047 = 3373571) B3373571
theorem B4269685 : Blo 2247435 4269685 := bbase (se 5 (by rfl) ⟨200141, by rfl⟩ : syracuseStep 4269685 = 400283) (by norm_num)
theorem B5692913 : Blo 2247435 5692913 := bstep (se 2 (by rfl) ⟨2134842, by rfl⟩ : syracuseStep 5692913 = 4269685) B4269685
theorem B3795275 : Blo 2247435 3795275 := bstep (se 1 (by rfl) ⟨2846456, by rfl⟩ : syracuseStep 3795275 = 5692913) B5692913
theorem B2530183 : Blo 2247435 2530183 := bstep (se 1 (by rfl) ⟨1897637, by rfl⟩ : syracuseStep 2530183 = 3795275) B3795275
theorem B3373577 : Blo 2247435 3373577 := bstep (se 2 (by rfl) ⟨1265091, by rfl⟩ : syracuseStep 3373577 = 2530183) B2530183
theorem B2249051 : Blo 2247435 2249051 := bstep (se 1 (by rfl) ⟨1686788, by rfl⟩ : syracuseStep 2249051 = 3373577) B3373577
theorem B11385845 : Blo 2247435 11385845 := bbase (se 5 (by rfl) ⟨533711, by rfl⟩ : syracuseStep 11385845 = 1067423) (by norm_num)
theorem B7590563 : Blo 2247435 7590563 := bstep (se 1 (by rfl) ⟨5692922, by rfl⟩ : syracuseStep 7590563 = 11385845) B11385845
theorem B5060375 : Blo 2247435 5060375 := bstep (se 1 (by rfl) ⟨3795281, by rfl⟩ : syracuseStep 5060375 = 7590563) B7590563
theorem B3373583 : Blo 2247435 3373583 := bstep (se 1 (by rfl) ⟨2530187, by rfl⟩ : syracuseStep 3373583 = 5060375) B5060375
theorem B2249055 : Blo 2247435 2249055 := bstep (se 1 (by rfl) ⟨1686791, by rfl⟩ : syracuseStep 2249055 = 3373583) B3373583
theorem B3373589 : Blo 2247435 3373589 := bbase (se 6 (by rfl) ⟨79068, by rfl⟩ : syracuseStep 3373589 = 158137) (by norm_num)
theorem B2249059 : Blo 2247435 2249059 := bstep (se 1 (by rfl) ⟨1686794, by rfl⟩ : syracuseStep 2249059 = 3373589) B3373589
theorem B19213685 : Blo 2247435 19213685 := bbase (se 5 (by rfl) ⟨900641, by rfl⟩ : syracuseStep 19213685 = 1801283) (by norm_num)
theorem B12809123 : Blo 2247435 12809123 := bstep (se 1 (by rfl) ⟨9606842, by rfl⟩ : syracuseStep 12809123 = 19213685) B19213685
theorem B8539415 : Blo 2247435 8539415 := bstep (se 1 (by rfl) ⟨6404561, by rfl⟩ : syracuseStep 8539415 = 12809123) B12809123
theorem B5692943 : Blo 2247435 5692943 := bstep (se 1 (by rfl) ⟨4269707, by rfl⟩ : syracuseStep 5692943 = 8539415) B8539415
theorem B3795295 : Blo 2247435 3795295 := bstep (se 1 (by rfl) ⟨2846471, by rfl⟩ : syracuseStep 3795295 = 5692943) B5692943
theorem B5060393 : Blo 2247435 5060393 := bstep (se 2 (by rfl) ⟨1897647, by rfl⟩ : syracuseStep 5060393 = 3795295) B3795295
theorem B3373595 : Blo 2247435 3373595 := bstep (se 1 (by rfl) ⟨2530196, by rfl⟩ : syracuseStep 3373595 = 5060393) B5060393
theorem B2249063 : Blo 2247435 2249063 := bstep (se 1 (by rfl) ⟨1686797, by rfl⟩ : syracuseStep 2249063 = 3373595) B3373595
theorem B2530201 : Blo 2247435 2530201 := bbase (se 2 (by rfl) ⟨948825, by rfl⟩ : syracuseStep 2530201 = 1897651) (by norm_num)
theorem B3373601 : Blo 2247435 3373601 := bstep (se 2 (by rfl) ⟨1265100, by rfl⟩ : syracuseStep 3373601 = 2530201) B2530201
theorem B2249067 : Blo 2247435 2249067 := bstep (se 1 (by rfl) ⟨1686800, by rfl⟩ : syracuseStep 2249067 = 3373601) B3373601
theorem B8539445 : Blo 2247435 8539445 := bbase (se 5 (by rfl) ⟨400286, by rfl⟩ : syracuseStep 8539445 = 800573) (by norm_num)
theorem B5692963 : Blo 2247435 5692963 := bstep (se 1 (by rfl) ⟨4269722, by rfl⟩ : syracuseStep 5692963 = 8539445) B8539445
theorem B7590617 : Blo 2247435 7590617 := bstep (se 2 (by rfl) ⟨2846481, by rfl⟩ : syracuseStep 7590617 = 5692963) B5692963
theorem B5060411 : Blo 2247435 5060411 := bstep (se 1 (by rfl) ⟨3795308, by rfl⟩ : syracuseStep 5060411 = 7590617) B7590617
theorem B3373607 : Blo 2247435 3373607 := bstep (se 1 (by rfl) ⟨2530205, by rfl⟩ : syracuseStep 3373607 = 5060411) B5060411
theorem B2249071 : Blo 2247435 2249071 := bstep (se 1 (by rfl) ⟨1686803, by rfl⟩ : syracuseStep 2249071 = 3373607) B3373607
theorem B3373613 : Blo 2247435 3373613 := bbase (se 3 (by rfl) ⟨632552, by rfl⟩ : syracuseStep 3373613 = 1265105) (by norm_num)
theorem B2249075 : Blo 2247435 2249075 := bstep (se 1 (by rfl) ⟨1686806, by rfl⟩ : syracuseStep 2249075 = 3373613) B3373613
theorem B5060429 : Blo 2247435 5060429 := bbase (se 3 (by rfl) ⟨948830, by rfl⟩ : syracuseStep 5060429 = 1897661) (by norm_num)
theorem B3373619 : Blo 2247435 3373619 := bstep (se 1 (by rfl) ⟨2530214, by rfl⟩ : syracuseStep 3373619 = 5060429) B5060429
theorem B2249079 : Blo 2247435 2249079 := bstep (se 1 (by rfl) ⟨1686809, by rfl⟩ : syracuseStep 2249079 = 3373619) B3373619
theorem B2846497 : Blo 2247435 2846497 := bbase (se 2 (by rfl) ⟨1067436, by rfl⟩ : syracuseStep 2846497 = 2134873) (by norm_num)
theorem B3795329 : Blo 2247435 3795329 := bstep (se 2 (by rfl) ⟨1423248, by rfl⟩ : syracuseStep 3795329 = 2846497) B2846497
theorem B2530219 : Blo 2247435 2530219 := bstep (se 1 (by rfl) ⟨1897664, by rfl⟩ : syracuseStep 2530219 = 3795329) B3795329
theorem B3373625 : Blo 2247435 3373625 := bstep (se 2 (by rfl) ⟨1265109, by rfl⟩ : syracuseStep 3373625 = 2530219) B2530219
theorem B2249083 : Blo 2247435 2249083 := bstep (se 1 (by rfl) ⟨1686812, by rfl⟩ : syracuseStep 2249083 = 3373625) B3373625
theorem B25618517 : Blo 2247435 25618517 := bbase (se 8 (by rfl) ⟨150108, by rfl⟩ : syracuseStep 25618517 = 300217) (by norm_num)
theorem B17079011 : Blo 2247435 17079011 := bstep (se 1 (by rfl) ⟨12809258, by rfl⟩ : syracuseStep 17079011 = 25618517) B25618517
theorem B11386007 : Blo 2247435 11386007 := bstep (se 1 (by rfl) ⟨8539505, by rfl⟩ : syracuseStep 11386007 = 17079011) B17079011
theorem B7590671 : Blo 2247435 7590671 := bstep (se 1 (by rfl) ⟨5693003, by rfl⟩ : syracuseStep 7590671 = 11386007) B11386007
theorem B5060447 : Blo 2247435 5060447 := bstep (se 1 (by rfl) ⟨3795335, by rfl⟩ : syracuseStep 5060447 = 7590671) B7590671
theorem B3373631 : Blo 2247435 3373631 := bstep (se 1 (by rfl) ⟨2530223, by rfl⟩ : syracuseStep 3373631 = 5060447) B5060447
theorem B2249087 : Blo 2247435 2249087 := bstep (se 1 (by rfl) ⟨1686815, by rfl⟩ : syracuseStep 2249087 = 3373631) B3373631
theorem B3373637 : Blo 2247435 3373637 := bbase (se 4 (by rfl) ⟨316278, by rfl⟩ : syracuseStep 3373637 = 632557) (by norm_num)
theorem B2249091 : Blo 2247435 2249091 := bstep (se 1 (by rfl) ⟨1686818, by rfl⟩ : syracuseStep 2249091 = 3373637) B3373637
theorem B3795349 : Blo 2247435 3795349 := bbase (se 6 (by rfl) ⟨88953, by rfl⟩ : syracuseStep 3795349 = 177907) (by norm_num)
theorem B5060465 : Blo 2247435 5060465 := bstep (se 2 (by rfl) ⟨1897674, by rfl⟩ : syracuseStep 5060465 = 3795349) B3795349
theorem B3373643 : Blo 2247435 3373643 := bstep (se 1 (by rfl) ⟨2530232, by rfl⟩ : syracuseStep 3373643 = 5060465) B5060465
theorem B2249095 : Blo 2247435 2249095 := bstep (se 1 (by rfl) ⟨1686821, by rfl⟩ : syracuseStep 2249095 = 3373643) B3373643
theorem B2530237 : Blo 2247435 2530237 := bbase (se 3 (by rfl) ⟨474419, by rfl⟩ : syracuseStep 2530237 = 948839) (by norm_num)
theorem B3373649 : Blo 2247435 3373649 := bstep (se 2 (by rfl) ⟨1265118, by rfl⟩ : syracuseStep 3373649 = 2530237) B2530237
theorem B2249099 : Blo 2247435 2249099 := bstep (se 1 (by rfl) ⟨1686824, by rfl⟩ : syracuseStep 2249099 = 3373649) B3373649
theorem B7590725 : Blo 2247435 7590725 := bbase (se 4 (by rfl) ⟨711630, by rfl⟩ : syracuseStep 7590725 = 1423261) (by norm_num)
theorem B5060483 : Blo 2247435 5060483 := bstep (se 1 (by rfl) ⟨3795362, by rfl⟩ : syracuseStep 5060483 = 7590725) B7590725
theorem B3373655 : Blo 2247435 3373655 := bstep (se 1 (by rfl) ⟨2530241, by rfl⟩ : syracuseStep 3373655 = 5060483) B5060483
theorem B2249103 : Blo 2247435 2249103 := bstep (se 1 (by rfl) ⟨1686827, by rfl⟩ : syracuseStep 2249103 = 3373655) B3373655
theorem B3373661 : Blo 2247435 3373661 := bbase (se 3 (by rfl) ⟨632561, by rfl⟩ : syracuseStep 3373661 = 1265123) (by norm_num)
theorem B2249107 : Blo 2247435 2249107 := bstep (se 1 (by rfl) ⟨1686830, by rfl⟩ : syracuseStep 2249107 = 3373661) B3373661
theorem B5060501 : Blo 2247435 5060501 := bbase (se 6 (by rfl) ⟨118605, by rfl⟩ : syracuseStep 5060501 = 237211) (by norm_num)
theorem B3373667 : Blo 2247435 3373667 := bstep (se 1 (by rfl) ⟨2530250, by rfl⟩ : syracuseStep 3373667 = 5060501) B5060501
theorem B2249111 : Blo 2247435 2249111 := bstep (se 1 (by rfl) ⟨1686833, by rfl⟩ : syracuseStep 2249111 = 3373667) B3373667
theorem B4803533 : Blo 2247435 4803533 := bbase (se 3 (by rfl) ⟨900662, by rfl⟩ : syracuseStep 4803533 = 1801325) (by norm_num)
theorem B3202355 : Blo 2247435 3202355 := bstep (se 1 (by rfl) ⟨2401766, by rfl⟩ : syracuseStep 3202355 = 4803533) B4803533
theorem B8539613 : Blo 2247435 8539613 := bstep (se 3 (by rfl) ⟨1601177, by rfl⟩ : syracuseStep 8539613 = 3202355) B3202355
theorem B5693075 : Blo 2247435 5693075 := bstep (se 1 (by rfl) ⟨4269806, by rfl⟩ : syracuseStep 5693075 = 8539613) B8539613
theorem B3795383 : Blo 2247435 3795383 := bstep (se 1 (by rfl) ⟨2846537, by rfl⟩ : syracuseStep 3795383 = 5693075) B5693075
theorem B2530255 : Blo 2247435 2530255 := bstep (se 1 (by rfl) ⟨1897691, by rfl⟩ : syracuseStep 2530255 = 3795383) B3795383
theorem B3373673 : Blo 2247435 3373673 := bstep (se 2 (by rfl) ⟨1265127, by rfl⟩ : syracuseStep 3373673 = 2530255) B2530255
theorem B2249115 : Blo 2247435 2249115 := bstep (se 1 (by rfl) ⟨1686836, by rfl⟩ : syracuseStep 2249115 = 3373673) B3373673
theorem B5929301 : Blo 2247435 5929301 := bbase (se 10 (by rfl) ⟨8685, by rfl⟩ : syracuseStep 5929301 = 17371) (by norm_num)
theorem B15811469 : Blo 2247435 15811469 := bstep (se 3 (by rfl) ⟨2964650, by rfl⟩ : syracuseStep 15811469 = 5929301) B5929301
theorem B10540979 : Blo 2247435 10540979 := bstep (se 1 (by rfl) ⟨7905734, by rfl⟩ : syracuseStep 10540979 = 15811469) B15811469
theorem B7027319 : Blo 2247435 7027319 := bstep (se 1 (by rfl) ⟨5270489, by rfl⟩ : syracuseStep 7027319 = 10540979) B10540979
theorem B4684879 : Blo 2247435 4684879 := bstep (se 1 (by rfl) ⟨3513659, by rfl⟩ : syracuseStep 4684879 = 7027319) B7027319
theorem B6246505 : Blo 2247435 6246505 := bstep (se 2 (by rfl) ⟨2342439, by rfl⟩ : syracuseStep 6246505 = 4684879) B4684879
theorem B8328673 : Blo 2247435 8328673 := bstep (se 2 (by rfl) ⟨3123252, by rfl⟩ : syracuseStep 8328673 = 6246505) B6246505
theorem B44419589 : Blo 2247435 44419589 := bstep (se 4 (by rfl) ⟨4164336, by rfl⟩ : syracuseStep 44419589 = 8328673) B8328673
theorem B29613059 : Blo 2247435 29613059 := bstep (se 1 (by rfl) ⟨22209794, by rfl⟩ : syracuseStep 29613059 = 44419589) B44419589
theorem B19742039 : Blo 2247435 19742039 := bstep (se 1 (by rfl) ⟨14806529, by rfl⟩ : syracuseStep 19742039 = 29613059) B29613059
theorem B13161359 : Blo 2247435 13161359 := bstep (se 1 (by rfl) ⟨9871019, by rfl⟩ : syracuseStep 13161359 = 19742039) B19742039
theorem B8774239 : Blo 2247435 8774239 := bstep (se 1 (by rfl) ⟨6580679, by rfl⟩ : syracuseStep 8774239 = 13161359) B13161359
theorem B11698985 : Blo 2247435 11698985 := bstep (se 2 (by rfl) ⟨4387119, by rfl⟩ : syracuseStep 11698985 = 8774239) B8774239
theorem B7799323 : Blo 2247435 7799323 := bstep (se 1 (by rfl) ⟨5849492, by rfl⟩ : syracuseStep 7799323 = 11698985) B11698985
theorem B10399097 : Blo 2247435 10399097 := bstep (se 2 (by rfl) ⟨3899661, by rfl⟩ : syracuseStep 10399097 = 7799323) B7799323
theorem B6932731 : Blo 2247435 6932731 := bstep (se 1 (by rfl) ⟨5199548, by rfl⟩ : syracuseStep 6932731 = 10399097) B10399097
theorem B9243641 : Blo 2247435 9243641 := bstep (se 2 (by rfl) ⟨3466365, by rfl⟩ : syracuseStep 9243641 = 6932731) B6932731
theorem B6162427 : Blo 2247435 6162427 := bstep (se 1 (by rfl) ⟨4621820, by rfl⟩ : syracuseStep 6162427 = 9243641) B9243641
theorem B8216569 : Blo 2247435 8216569 := bstep (se 2 (by rfl) ⟨3081213, by rfl⟩ : syracuseStep 8216569 = 6162427) B6162427
theorem B10955425 : Blo 2247435 10955425 := bstep (se 2 (by rfl) ⟨4108284, by rfl⟩ : syracuseStep 10955425 = 8216569) B8216569
theorem B14607233 : Blo 2247435 14607233 := bstep (se 2 (by rfl) ⟨5477712, by rfl⟩ : syracuseStep 14607233 = 10955425) B10955425
theorem B9738155 : Blo 2247435 9738155 := bstep (se 1 (by rfl) ⟨7303616, by rfl⟩ : syracuseStep 9738155 = 14607233) B14607233
theorem B25968413 : Blo 2247435 25968413 := bstep (se 3 (by rfl) ⟨4869077, by rfl⟩ : syracuseStep 25968413 = 9738155) B9738155
theorem B17312275 : Blo 2247435 17312275 := bstep (se 1 (by rfl) ⟨12984206, by rfl⟩ : syracuseStep 17312275 = 25968413) B25968413
theorem B92332133 : Blo 2247435 92332133 := bstep (se 4 (by rfl) ⟨8656137, by rfl⟩ : syracuseStep 92332133 = 17312275) B17312275
theorem B61554755 : Blo 2247435 61554755 := bstep (se 1 (by rfl) ⟨46166066, by rfl⟩ : syracuseStep 61554755 = 92332133) B92332133
theorem B41036503 : Blo 2247435 41036503 := bstep (se 1 (by rfl) ⟨30777377, by rfl⟩ : syracuseStep 41036503 = 61554755) B61554755
theorem B54715337 : Blo 2247435 54715337 := bstep (se 2 (by rfl) ⟨20518251, by rfl⟩ : syracuseStep 54715337 = 41036503) B41036503
theorem B36476891 : Blo 2247435 36476891 := bstep (se 1 (by rfl) ⟨27357668, by rfl⟩ : syracuseStep 36476891 = 54715337) B54715337
theorem B24317927 : Blo 2247435 24317927 := bstep (se 1 (by rfl) ⟨18238445, by rfl⟩ : syracuseStep 24317927 = 36476891) B36476891
theorem B16211951 : Blo 2247435 16211951 := bstep (se 1 (by rfl) ⟨12158963, by rfl⟩ : syracuseStep 16211951 = 24317927) B24317927
theorem B10807967 : Blo 2247435 10807967 := bstep (se 1 (by rfl) ⟨8105975, by rfl⟩ : syracuseStep 10807967 = 16211951) B16211951
theorem B7205311 : Blo 2247435 7205311 := bstep (se 1 (by rfl) ⟨5403983, by rfl⟩ : syracuseStep 7205311 = 10807967) B10807967
theorem B9607081 : Blo 2247435 9607081 := bstep (se 2 (by rfl) ⟨3602655, by rfl⟩ : syracuseStep 9607081 = 7205311) B7205311
theorem B12809441 : Blo 2247435 12809441 := bstep (se 2 (by rfl) ⟨4803540, by rfl⟩ : syracuseStep 12809441 = 9607081) B9607081
theorem B8539627 : Blo 2247435 8539627 := bstep (se 1 (by rfl) ⟨6404720, by rfl⟩ : syracuseStep 8539627 = 12809441) B12809441
theorem B11386169 : Blo 2247435 11386169 := bstep (se 2 (by rfl) ⟨4269813, by rfl⟩ : syracuseStep 11386169 = 8539627) B8539627
theorem B7590779 : Blo 2247435 7590779 := bstep (se 1 (by rfl) ⟨5693084, by rfl⟩ : syracuseStep 7590779 = 11386169) B11386169
theorem B5060519 : Blo 2247435 5060519 := bstep (se 1 (by rfl) ⟨3795389, by rfl⟩ : syracuseStep 5060519 = 7590779) B7590779
theorem B3373679 : Blo 2247435 3373679 := bstep (se 1 (by rfl) ⟨2530259, by rfl⟩ : syracuseStep 3373679 = 5060519) B5060519
theorem B2249119 : Blo 2247435 2249119 := bstep (se 1 (by rfl) ⟨1686839, by rfl⟩ : syracuseStep 2249119 = 3373679) B3373679
theorem B3373685 : Blo 2247435 3373685 := bbase (se 5 (by rfl) ⟨158141, by rfl⟩ : syracuseStep 3373685 = 316283) (by norm_num)
theorem B2249123 : Blo 2247435 2249123 := bstep (se 1 (by rfl) ⟨1686842, by rfl⟩ : syracuseStep 2249123 = 3373685) B3373685
theorem B4269829 : Blo 2247435 4269829 := bbase (se 4 (by rfl) ⟨400296, by rfl⟩ : syracuseStep 4269829 = 800593) (by norm_num)
theorem B5693105 : Blo 2247435 5693105 := bstep (se 2 (by rfl) ⟨2134914, by rfl⟩ : syracuseStep 5693105 = 4269829) B4269829
theorem B3795403 : Blo 2247435 3795403 := bstep (se 1 (by rfl) ⟨2846552, by rfl⟩ : syracuseStep 3795403 = 5693105) B5693105
theorem B5060537 : Blo 2247435 5060537 := bstep (se 2 (by rfl) ⟨1897701, by rfl⟩ : syracuseStep 5060537 = 3795403) B3795403
theorem B3373691 : Blo 2247435 3373691 := bstep (se 1 (by rfl) ⟨2530268, by rfl⟩ : syracuseStep 3373691 = 5060537) B5060537
theorem B2249127 : Blo 2247435 2249127 := bstep (se 1 (by rfl) ⟨1686845, by rfl⟩ : syracuseStep 2249127 = 3373691) B3373691
theorem B2530273 : Blo 2247435 2530273 := bbase (se 2 (by rfl) ⟨948852, by rfl⟩ : syracuseStep 2530273 = 1897705) (by norm_num)
theorem B3373697 : Blo 2247435 3373697 := bstep (se 2 (by rfl) ⟨1265136, by rfl⟩ : syracuseStep 3373697 = 2530273) B2530273
theorem B2249131 : Blo 2247435 2249131 := bstep (se 1 (by rfl) ⟨1686848, by rfl⟩ : syracuseStep 2249131 = 3373697) B3373697
theorem B5693125 : Blo 2247435 5693125 := bbase (se 4 (by rfl) ⟨533730, by rfl⟩ : syracuseStep 5693125 = 1067461) (by norm_num)
theorem B7590833 : Blo 2247435 7590833 := bstep (se 2 (by rfl) ⟨2846562, by rfl⟩ : syracuseStep 7590833 = 5693125) B5693125
theorem B5060555 : Blo 2247435 5060555 := bstep (se 1 (by rfl) ⟨3795416, by rfl⟩ : syracuseStep 5060555 = 7590833) B7590833
theorem B3373703 : Blo 2247435 3373703 := bstep (se 1 (by rfl) ⟨2530277, by rfl⟩ : syracuseStep 3373703 = 5060555) B5060555
theorem B2249135 : Blo 2247435 2249135 := bstep (se 1 (by rfl) ⟨1686851, by rfl⟩ : syracuseStep 2249135 = 3373703) B3373703
theorem B3373709 : Blo 2247435 3373709 := bbase (se 3 (by rfl) ⟨632570, by rfl⟩ : syracuseStep 3373709 = 1265141) (by norm_num)
theorem B2249139 : Blo 2247435 2249139 := bstep (se 1 (by rfl) ⟨1686854, by rfl⟩ : syracuseStep 2249139 = 3373709) B3373709
theorem B5060573 : Blo 2247435 5060573 := bbase (se 3 (by rfl) ⟨948857, by rfl⟩ : syracuseStep 5060573 = 1897715) (by norm_num)
theorem B3373715 : Blo 2247435 3373715 := bstep (se 1 (by rfl) ⟨2530286, by rfl⟩ : syracuseStep 3373715 = 5060573) B5060573
theorem B2249143 : Blo 2247435 2249143 := bstep (se 1 (by rfl) ⟨1686857, by rfl⟩ : syracuseStep 2249143 = 3373715) B3373715
theorem B3795437 : Blo 2247435 3795437 := bbase (se 3 (by rfl) ⟨711644, by rfl⟩ : syracuseStep 3795437 = 1423289) (by norm_num)
theorem B2530291 : Blo 2247435 2530291 := bstep (se 1 (by rfl) ⟨1897718, by rfl⟩ : syracuseStep 2530291 = 3795437) B3795437
theorem B3373721 : Blo 2247435 3373721 := bstep (se 2 (by rfl) ⟨1265145, by rfl⟩ : syracuseStep 3373721 = 2530291) B2530291
theorem B2249147 : Blo 2247435 2249147 := bstep (se 1 (by rfl) ⟨1686860, by rfl⟩ : syracuseStep 2249147 = 3373721) B3373721
theorem B28821653 : Blo 2247435 28821653 := bbase (se 6 (by rfl) ⟨675507, by rfl⟩ : syracuseStep 28821653 = 1351015) (by norm_num)
theorem B19214435 : Blo 2247435 19214435 := bstep (se 1 (by rfl) ⟨14410826, by rfl⟩ : syracuseStep 19214435 = 28821653) B28821653
theorem B12809623 : Blo 2247435 12809623 := bstep (se 1 (by rfl) ⟨9607217, by rfl⟩ : syracuseStep 12809623 = 19214435) B19214435
theorem B17079497 : Blo 2247435 17079497 := bstep (se 2 (by rfl) ⟨6404811, by rfl⟩ : syracuseStep 17079497 = 12809623) B12809623
theorem B11386331 : Blo 2247435 11386331 := bstep (se 1 (by rfl) ⟨8539748, by rfl⟩ : syracuseStep 11386331 = 17079497) B17079497
theorem B7590887 : Blo 2247435 7590887 := bstep (se 1 (by rfl) ⟨5693165, by rfl⟩ : syracuseStep 7590887 = 11386331) B11386331
theorem B5060591 : Blo 2247435 5060591 := bstep (se 1 (by rfl) ⟨3795443, by rfl⟩ : syracuseStep 5060591 = 7590887) B7590887
theorem B3373727 : Blo 2247435 3373727 := bstep (se 1 (by rfl) ⟨2530295, by rfl⟩ : syracuseStep 3373727 = 5060591) B5060591
theorem B2249151 : Blo 2247435 2249151 := bstep (se 1 (by rfl) ⟨1686863, by rfl⟩ : syracuseStep 2249151 = 3373727) B3373727
theorem B3373733 : Blo 2247435 3373733 := bbase (se 4 (by rfl) ⟨316287, by rfl⟩ : syracuseStep 3373733 = 632575) (by norm_num)
theorem B2249155 : Blo 2247435 2249155 := bstep (se 1 (by rfl) ⟨1686866, by rfl⟩ : syracuseStep 2249155 = 3373733) B3373733
theorem B2846593 : Blo 2247435 2846593 := bbase (se 2 (by rfl) ⟨1067472, by rfl⟩ : syracuseStep 2846593 = 2134945) (by norm_num)
theorem B3795457 : Blo 2247435 3795457 := bstep (se 2 (by rfl) ⟨1423296, by rfl⟩ : syracuseStep 3795457 = 2846593) B2846593
theorem B5060609 : Blo 2247435 5060609 := bstep (se 2 (by rfl) ⟨1897728, by rfl⟩ : syracuseStep 5060609 = 3795457) B3795457
theorem B3373739 : Blo 2247435 3373739 := bstep (se 1 (by rfl) ⟨2530304, by rfl⟩ : syracuseStep 3373739 = 5060609) B5060609
theorem B2249159 : Blo 2247435 2249159 := bstep (se 1 (by rfl) ⟨1686869, by rfl⟩ : syracuseStep 2249159 = 3373739) B3373739
theorem B2530309 : Blo 2247435 2530309 := bbase (se 4 (by rfl) ⟨237216, by rfl⟩ : syracuseStep 2530309 = 474433) (by norm_num)
theorem B3373745 : Blo 2247435 3373745 := bstep (se 2 (by rfl) ⟨1265154, by rfl⟩ : syracuseStep 3373745 = 2530309) B2530309
theorem B2249163 : Blo 2247435 2249163 := bstep (se 1 (by rfl) ⟨1686872, by rfl⟩ : syracuseStep 2249163 = 3373745) B3373745
theorem B3202429 : Blo 2247435 3202429 := bbase (se 3 (by rfl) ⟨600455, by rfl⟩ : syracuseStep 3202429 = 1200911) (by norm_num)
theorem B4269905 : Blo 2247435 4269905 := bstep (se 2 (by rfl) ⟨1601214, by rfl⟩ : syracuseStep 4269905 = 3202429) B3202429
theorem B2846603 : Blo 2247435 2846603 := bstep (se 1 (by rfl) ⟨2134952, by rfl⟩ : syracuseStep 2846603 = 4269905) B4269905
theorem B7590941 : Blo 2247435 7590941 := bstep (se 3 (by rfl) ⟨1423301, by rfl⟩ : syracuseStep 7590941 = 2846603) B2846603
theorem B5060627 : Blo 2247435 5060627 := bstep (se 1 (by rfl) ⟨3795470, by rfl⟩ : syracuseStep 5060627 = 7590941) B7590941
theorem B3373751 : Blo 2247435 3373751 := bstep (se 1 (by rfl) ⟨2530313, by rfl⟩ : syracuseStep 3373751 = 5060627) B5060627
theorem B2249167 : Blo 2247435 2249167 := bstep (se 1 (by rfl) ⟨1686875, by rfl⟩ : syracuseStep 2249167 = 3373751) B3373751
theorem B3373757 : Blo 2247435 3373757 := bbase (se 3 (by rfl) ⟨632579, by rfl⟩ : syracuseStep 3373757 = 1265159) (by norm_num)
theorem B2249171 : Blo 2247435 2249171 := bstep (se 1 (by rfl) ⟨1686878, by rfl⟩ : syracuseStep 2249171 = 3373757) B3373757
theorem B5060645 : Blo 2247435 5060645 := bbase (se 4 (by rfl) ⟨474435, by rfl⟩ : syracuseStep 5060645 = 948871) (by norm_num)
theorem B3373763 : Blo 2247435 3373763 := bstep (se 1 (by rfl) ⟨2530322, by rfl⟩ : syracuseStep 3373763 = 5060645) B5060645
theorem B2249175 : Blo 2247435 2249175 := bstep (se 1 (by rfl) ⟨1686881, by rfl⟩ : syracuseStep 2249175 = 3373763) B3373763
theorem B5693237 : Blo 2247435 5693237 := bbase (se 5 (by rfl) ⟨266870, by rfl⟩ : syracuseStep 5693237 = 533741) (by norm_num)
theorem B3795491 : Blo 2247435 3795491 := bstep (se 1 (by rfl) ⟨2846618, by rfl⟩ : syracuseStep 3795491 = 5693237) B5693237
theorem B2530327 : Blo 2247435 2530327 := bstep (se 1 (by rfl) ⟨1897745, by rfl⟩ : syracuseStep 2530327 = 3795491) B3795491
theorem B3373769 : Blo 2247435 3373769 := bstep (se 2 (by rfl) ⟨1265163, by rfl⟩ : syracuseStep 3373769 = 2530327) B2530327
theorem B2249179 : Blo 2247435 2249179 := bstep (se 1 (by rfl) ⟨1686884, by rfl⟩ : syracuseStep 2249179 = 3373769) B3373769
theorem B2310977 : Blo 2247435 2310977 := bbase (se 2 (by rfl) ⟨866616, by rfl⟩ : syracuseStep 2310977 = 1733233) (by norm_num)
theorem B6162605 : Blo 2247435 6162605 := bstep (se 3 (by rfl) ⟨1155488, by rfl⟩ : syracuseStep 6162605 = 2310977) B2310977
theorem B4108403 : Blo 2247435 4108403 := bstep (se 1 (by rfl) ⟨3081302, by rfl⟩ : syracuseStep 4108403 = 6162605) B6162605
theorem B2738935 : Blo 2247435 2738935 := bstep (se 1 (by rfl) ⟨2054201, by rfl⟩ : syracuseStep 2738935 = 4108403) B4108403
theorem B3651913 : Blo 2247435 3651913 := bstep (se 2 (by rfl) ⟨1369467, by rfl⟩ : syracuseStep 3651913 = 2738935) B2738935
theorem B4869217 : Blo 2247435 4869217 := bstep (se 2 (by rfl) ⟨1825956, by rfl⟩ : syracuseStep 4869217 = 3651913) B3651913
theorem B25969157 : Blo 2247435 25969157 := bstep (se 4 (by rfl) ⟨2434608, by rfl⟩ : syracuseStep 25969157 = 4869217) B4869217
theorem B17312771 : Blo 2247435 17312771 := bstep (se 1 (by rfl) ⟨12984578, by rfl⟩ : syracuseStep 17312771 = 25969157) B25969157
theorem B11541847 : Blo 2247435 11541847 := bstep (se 1 (by rfl) ⟨8656385, by rfl⟩ : syracuseStep 11541847 = 17312771) B17312771
theorem B15389129 : Blo 2247435 15389129 := bstep (se 2 (by rfl) ⟨5770923, by rfl⟩ : syracuseStep 15389129 = 11541847) B11541847
theorem B10259419 : Blo 2247435 10259419 := bstep (se 1 (by rfl) ⟨7694564, by rfl⟩ : syracuseStep 10259419 = 15389129) B15389129
theorem B13679225 : Blo 2247435 13679225 := bstep (se 2 (by rfl) ⟨5129709, by rfl⟩ : syracuseStep 13679225 = 10259419) B10259419
theorem B9119483 : Blo 2247435 9119483 := bstep (se 1 (by rfl) ⟨6839612, by rfl⟩ : syracuseStep 9119483 = 13679225) B13679225
theorem B6079655 : Blo 2247435 6079655 := bstep (se 1 (by rfl) ⟨4559741, by rfl⟩ : syracuseStep 6079655 = 9119483) B9119483
theorem B16212413 : Blo 2247435 16212413 := bstep (se 3 (by rfl) ⟨3039827, by rfl⟩ : syracuseStep 16212413 = 6079655) B6079655
theorem B10808275 : Blo 2247435 10808275 := bstep (se 1 (by rfl) ⟨8106206, by rfl⟩ : syracuseStep 10808275 = 16212413) B16212413
theorem B14411033 : Blo 2247435 14411033 := bstep (se 2 (by rfl) ⟨5404137, by rfl⟩ : syracuseStep 14411033 = 10808275) B10808275
theorem B9607355 : Blo 2247435 9607355 := bstep (se 1 (by rfl) ⟨7205516, by rfl⟩ : syracuseStep 9607355 = 14411033) B14411033
theorem B6404903 : Blo 2247435 6404903 := bstep (se 1 (by rfl) ⟨4803677, by rfl⟩ : syracuseStep 6404903 = 9607355) B9607355
theorem B4269935 : Blo 2247435 4269935 := bstep (se 1 (by rfl) ⟨3202451, by rfl⟩ : syracuseStep 4269935 = 6404903) B6404903
theorem B11386493 : Blo 2247435 11386493 := bstep (se 3 (by rfl) ⟨2134967, by rfl⟩ : syracuseStep 11386493 = 4269935) B4269935
theorem B7590995 : Blo 2247435 7590995 := bstep (se 1 (by rfl) ⟨5693246, by rfl⟩ : syracuseStep 7590995 = 11386493) B11386493
theorem B5060663 : Blo 2247435 5060663 := bstep (se 1 (by rfl) ⟨3795497, by rfl⟩ : syracuseStep 5060663 = 7590995) B7590995
theorem B3373775 : Blo 2247435 3373775 := bstep (se 1 (by rfl) ⟨2530331, by rfl⟩ : syracuseStep 3373775 = 5060663) B5060663
theorem B2249183 : Blo 2247435 2249183 := bstep (se 1 (by rfl) ⟨1686887, by rfl⟩ : syracuseStep 2249183 = 3373775) B3373775
theorem B3373781 : Blo 2247435 3373781 := bbase (se 7 (by rfl) ⟨39536, by rfl⟩ : syracuseStep 3373781 = 79073) (by norm_num)
theorem B2249187 : Blo 2247435 2249187 := bstep (se 1 (by rfl) ⟨1686890, by rfl⟩ : syracuseStep 2249187 = 3373781) B3373781
theorem B2738945 : Blo 2247435 2738945 := bbase (se 2 (by rfl) ⟨1027104, by rfl⟩ : syracuseStep 2738945 = 2054209) (by norm_num)
theorem B7303853 : Blo 2247435 7303853 := bstep (se 3 (by rfl) ⟨1369472, by rfl⟩ : syracuseStep 7303853 = 2738945) B2738945
theorem B4869235 : Blo 2247435 4869235 := bstep (se 1 (by rfl) ⟨3651926, by rfl⟩ : syracuseStep 4869235 = 7303853) B7303853
theorem B6492313 : Blo 2247435 6492313 := bstep (se 2 (by rfl) ⟨2434617, by rfl⟩ : syracuseStep 6492313 = 4869235) B4869235
theorem B8656417 : Blo 2247435 8656417 := bstep (se 2 (by rfl) ⟨3246156, by rfl⟩ : syracuseStep 8656417 = 6492313) B6492313
theorem B11541889 : Blo 2247435 11541889 := bstep (se 2 (by rfl) ⟨4328208, by rfl⟩ : syracuseStep 11541889 = 8656417) B8656417
theorem B15389185 : Blo 2247435 15389185 := bstep (se 2 (by rfl) ⟨5770944, by rfl⟩ : syracuseStep 15389185 = 11541889) B11541889
theorem B20518913 : Blo 2247435 20518913 := bstep (se 2 (by rfl) ⟨7694592, by rfl⟩ : syracuseStep 20518913 = 15389185) B15389185
theorem B13679275 : Blo 2247435 13679275 := bstep (se 1 (by rfl) ⟨10259456, by rfl⟩ : syracuseStep 13679275 = 20518913) B20518913
theorem B18239033 : Blo 2247435 18239033 := bstep (se 2 (by rfl) ⟨6839637, by rfl⟩ : syracuseStep 18239033 = 13679275) B13679275
theorem B12159355 : Blo 2247435 12159355 := bstep (se 1 (by rfl) ⟨9119516, by rfl⟩ : syracuseStep 12159355 = 18239033) B18239033
theorem B16212473 : Blo 2247435 16212473 := bstep (se 2 (by rfl) ⟨6079677, by rfl⟩ : syracuseStep 16212473 = 12159355) B12159355
theorem B10808315 : Blo 2247435 10808315 := bstep (se 1 (by rfl) ⟨8106236, by rfl⟩ : syracuseStep 10808315 = 16212473) B16212473
theorem B7205543 : Blo 2247435 7205543 := bstep (se 1 (by rfl) ⟨5404157, by rfl⟩ : syracuseStep 7205543 = 10808315) B10808315
theorem B4803695 : Blo 2247435 4803695 := bstep (se 1 (by rfl) ⟨3602771, by rfl⟩ : syracuseStep 4803695 = 7205543) B7205543
theorem B3202463 : Blo 2247435 3202463 := bstep (se 1 (by rfl) ⟨2401847, by rfl⟩ : syracuseStep 3202463 = 4803695) B4803695
theorem B8539901 : Blo 2247435 8539901 := bstep (se 3 (by rfl) ⟨1601231, by rfl⟩ : syracuseStep 8539901 = 3202463) B3202463
theorem B5693267 : Blo 2247435 5693267 := bstep (se 1 (by rfl) ⟨4269950, by rfl⟩ : syracuseStep 5693267 = 8539901) B8539901
theorem B3795511 : Blo 2247435 3795511 := bstep (se 1 (by rfl) ⟨2846633, by rfl⟩ : syracuseStep 3795511 = 5693267) B5693267
theorem B5060681 : Blo 2247435 5060681 := bstep (se 2 (by rfl) ⟨1897755, by rfl⟩ : syracuseStep 5060681 = 3795511) B3795511
theorem B3373787 : Blo 2247435 3373787 := bstep (se 1 (by rfl) ⟨2530340, by rfl⟩ : syracuseStep 3373787 = 5060681) B5060681
theorem B2249191 : Blo 2247435 2249191 := bstep (se 1 (by rfl) ⟨1686893, by rfl⟩ : syracuseStep 2249191 = 3373787) B3373787
theorem B2530345 : Blo 2247435 2530345 := bbase (se 2 (by rfl) ⟨948879, by rfl⟩ : syracuseStep 2530345 = 1897759) (by norm_num)
theorem B3373793 : Blo 2247435 3373793 := bstep (se 2 (by rfl) ⟨1265172, by rfl⟩ : syracuseStep 3373793 = 2530345) B2530345
theorem B2249195 : Blo 2247435 2249195 := bstep (se 1 (by rfl) ⟨1686896, by rfl⟩ : syracuseStep 2249195 = 3373793) B3373793
theorem B2635337 : Blo 2247435 2635337 := bbase (se 2 (by rfl) ⟨988251, by rfl⟩ : syracuseStep 2635337 = 1976503) (by norm_num)
theorem B7027565 : Blo 2247435 7027565 := bstep (se 3 (by rfl) ⟨1317668, by rfl⟩ : syracuseStep 7027565 = 2635337) B2635337
theorem B18740173 : Blo 2247435 18740173 := bstep (se 3 (by rfl) ⟨3513782, by rfl⟩ : syracuseStep 18740173 = 7027565) B7027565
theorem B24986897 : Blo 2247435 24986897 := bstep (se 2 (by rfl) ⟨9370086, by rfl⟩ : syracuseStep 24986897 = 18740173) B18740173
theorem B16657931 : Blo 2247435 16657931 := bstep (se 1 (by rfl) ⟨12493448, by rfl⟩ : syracuseStep 16657931 = 24986897) B24986897
theorem B11105287 : Blo 2247435 11105287 := bstep (se 1 (by rfl) ⟨8328965, by rfl⟩ : syracuseStep 11105287 = 16657931) B16657931
theorem B236912789 : Blo 2247435 236912789 := bstep (se 6 (by rfl) ⟨5552643, by rfl⟩ : syracuseStep 236912789 = 11105287) B11105287
theorem B631767437 : Blo 2247435 631767437 := bstep (se 3 (by rfl) ⟨118456394, by rfl⟩ : syracuseStep 631767437 = 236912789) B236912789
theorem B421178291 : Blo 2247435 421178291 := bstep (se 1 (by rfl) ⟨315883718, by rfl⟩ : syracuseStep 421178291 = 631767437) B631767437
theorem B280785527 : Blo 2247435 280785527 := bstep (se 1 (by rfl) ⟨210589145, by rfl⟩ : syracuseStep 280785527 = 421178291) B421178291
theorem B187190351 : Blo 2247435 187190351 := bstep (se 1 (by rfl) ⟨140392763, by rfl⟩ : syracuseStep 187190351 = 280785527) B280785527
theorem B124793567 : Blo 2247435 124793567 := bstep (se 1 (by rfl) ⟨93595175, by rfl⟩ : syracuseStep 124793567 = 187190351) B187190351
theorem B83195711 : Blo 2247435 83195711 := bstep (se 1 (by rfl) ⟨62396783, by rfl⟩ : syracuseStep 83195711 = 124793567) B124793567
theorem B55463807 : Blo 2247435 55463807 := bstep (se 1 (by rfl) ⟨41597855, by rfl⟩ : syracuseStep 55463807 = 83195711) B83195711
theorem B36975871 : Blo 2247435 36975871 := bstep (se 1 (by rfl) ⟨27731903, by rfl⟩ : syracuseStep 36975871 = 55463807) B55463807
theorem B197204645 : Blo 2247435 197204645 := bstep (se 4 (by rfl) ⟨18487935, by rfl⟩ : syracuseStep 197204645 = 36975871) B36975871
theorem B131469763 : Blo 2247435 131469763 := bstep (se 1 (by rfl) ⟨98602322, by rfl⟩ : syracuseStep 131469763 = 197204645) B197204645
theorem B175293017 : Blo 2247435 175293017 := bstep (se 2 (by rfl) ⟨65734881, by rfl⟩ : syracuseStep 175293017 = 131469763) B131469763
theorem B116862011 : Blo 2247435 116862011 := bstep (se 1 (by rfl) ⟨87646508, by rfl⟩ : syracuseStep 116862011 = 175293017) B175293017
theorem B77908007 : Blo 2247435 77908007 := bstep (se 1 (by rfl) ⟨58431005, by rfl⟩ : syracuseStep 77908007 = 116862011) B116862011
theorem B51938671 : Blo 2247435 51938671 := bstep (se 1 (by rfl) ⟨38954003, by rfl⟩ : syracuseStep 51938671 = 77908007) B77908007
theorem B69251561 : Blo 2247435 69251561 := bstep (se 2 (by rfl) ⟨25969335, by rfl⟩ : syracuseStep 69251561 = 51938671) B51938671
theorem B46167707 : Blo 2247435 46167707 := bstep (se 1 (by rfl) ⟨34625780, by rfl⟩ : syracuseStep 46167707 = 69251561) B69251561
theorem B30778471 : Blo 2247435 30778471 := bstep (se 1 (by rfl) ⟨23083853, by rfl⟩ : syracuseStep 30778471 = 46167707) B46167707
theorem B164151845 : Blo 2247435 164151845 := bstep (se 4 (by rfl) ⟨15389235, by rfl⟩ : syracuseStep 164151845 = 30778471) B30778471
theorem B109434563 : Blo 2247435 109434563 := bstep (se 1 (by rfl) ⟨82075922, by rfl⟩ : syracuseStep 109434563 = 164151845) B164151845
theorem B72956375 : Blo 2247435 72956375 := bstep (se 1 (by rfl) ⟨54717281, by rfl⟩ : syracuseStep 72956375 = 109434563) B109434563
theorem B48637583 : Blo 2247435 48637583 := bstep (se 1 (by rfl) ⟨36478187, by rfl⟩ : syracuseStep 48637583 = 72956375) B72956375
theorem B32425055 : Blo 2247435 32425055 := bstep (se 1 (by rfl) ⟨24318791, by rfl⟩ : syracuseStep 32425055 = 48637583) B48637583
theorem B21616703 : Blo 2247435 21616703 := bstep (se 1 (by rfl) ⟨16212527, by rfl⟩ : syracuseStep 21616703 = 32425055) B32425055
theorem B14411135 : Blo 2247435 14411135 := bstep (se 1 (by rfl) ⟨10808351, by rfl⟩ : syracuseStep 14411135 = 21616703) B21616703
theorem B9607423 : Blo 2247435 9607423 := bstep (se 1 (by rfl) ⟨7205567, by rfl⟩ : syracuseStep 9607423 = 14411135) B14411135
theorem B12809897 : Blo 2247435 12809897 := bstep (se 2 (by rfl) ⟨4803711, by rfl⟩ : syracuseStep 12809897 = 9607423) B9607423
theorem B8539931 : Blo 2247435 8539931 := bstep (se 1 (by rfl) ⟨6404948, by rfl⟩ : syracuseStep 8539931 = 12809897) B12809897
theorem B5693287 : Blo 2247435 5693287 := bstep (se 1 (by rfl) ⟨4269965, by rfl⟩ : syracuseStep 5693287 = 8539931) B8539931
theorem B7591049 : Blo 2247435 7591049 := bstep (se 2 (by rfl) ⟨2846643, by rfl⟩ : syracuseStep 7591049 = 5693287) B5693287
theorem B5060699 : Blo 2247435 5060699 := bstep (se 1 (by rfl) ⟨3795524, by rfl⟩ : syracuseStep 5060699 = 7591049) B7591049
theorem B3373799 : Blo 2247435 3373799 := bstep (se 1 (by rfl) ⟨2530349, by rfl⟩ : syracuseStep 3373799 = 5060699) B5060699
theorem B2249199 : Blo 2247435 2249199 := bstep (se 1 (by rfl) ⟨1686899, by rfl⟩ : syracuseStep 2249199 = 3373799) B3373799
theorem B3373805 : Blo 2247435 3373805 := bbase (se 3 (by rfl) ⟨632588, by rfl⟩ : syracuseStep 3373805 = 1265177) (by norm_num)
theorem B2249203 : Blo 2247435 2249203 := bstep (se 1 (by rfl) ⟨1686902, by rfl⟩ : syracuseStep 2249203 = 3373805) B3373805
theorem B5060717 : Blo 2247435 5060717 := bbase (se 3 (by rfl) ⟨948884, by rfl⟩ : syracuseStep 5060717 = 1897769) (by norm_num)
theorem B3373811 : Blo 2247435 3373811 := bstep (se 1 (by rfl) ⟨2530358, by rfl⟩ : syracuseStep 3373811 = 5060717) B5060717
theorem B2249207 : Blo 2247435 2249207 := bstep (se 1 (by rfl) ⟨1686905, by rfl⟩ : syracuseStep 2249207 = 3373811) B3373811
theorem B4269989 : Blo 2247435 4269989 := bbase (se 4 (by rfl) ⟨400311, by rfl⟩ : syracuseStep 4269989 = 800623) (by norm_num)
theorem B2846659 : Blo 2247435 2846659 := bstep (se 1 (by rfl) ⟨2134994, by rfl⟩ : syracuseStep 2846659 = 4269989) B4269989
theorem B3795545 : Blo 2247435 3795545 := bstep (se 2 (by rfl) ⟨1423329, by rfl⟩ : syracuseStep 3795545 = 2846659) B2846659
theorem B2530363 : Blo 2247435 2530363 := bstep (se 1 (by rfl) ⟨1897772, by rfl⟩ : syracuseStep 2530363 = 3795545) B3795545
theorem B3373817 : Blo 2247435 3373817 := bstep (se 2 (by rfl) ⟨1265181, by rfl⟩ : syracuseStep 3373817 = 2530363) B2530363
theorem B2249211 : Blo 2247435 2249211 := bstep (se 1 (by rfl) ⟨1686908, by rfl⟩ : syracuseStep 2249211 = 3373817) B3373817
theorem B10955893 : Blo 2247435 10955893 := bbase (se 5 (by rfl) ⟨513557, by rfl⟩ : syracuseStep 10955893 = 1027115) (by norm_num)
theorem B14607857 : Blo 2247435 14607857 := bstep (se 2 (by rfl) ⟨5477946, by rfl⟩ : syracuseStep 14607857 = 10955893) B10955893
theorem B9738571 : Blo 2247435 9738571 := bstep (se 1 (by rfl) ⟨7303928, by rfl⟩ : syracuseStep 9738571 = 14607857) B14607857
theorem B12984761 : Blo 2247435 12984761 := bstep (se 2 (by rfl) ⟨4869285, by rfl⟩ : syracuseStep 12984761 = 9738571) B9738571
theorem B8656507 : Blo 2247435 8656507 := bstep (se 1 (by rfl) ⟨6492380, by rfl⟩ : syracuseStep 8656507 = 12984761) B12984761
theorem B11542009 : Blo 2247435 11542009 := bstep (se 2 (by rfl) ⟨4328253, by rfl⟩ : syracuseStep 11542009 = 8656507) B8656507
theorem B15389345 : Blo 2247435 15389345 := bstep (se 2 (by rfl) ⟨5771004, by rfl⟩ : syracuseStep 15389345 = 11542009) B11542009
theorem B10259563 : Blo 2247435 10259563 := bstep (se 1 (by rfl) ⟨7694672, by rfl⟩ : syracuseStep 10259563 = 15389345) B15389345
theorem B13679417 : Blo 2247435 13679417 := bstep (se 2 (by rfl) ⟨5129781, by rfl⟩ : syracuseStep 13679417 = 10259563) B10259563
theorem B9119611 : Blo 2247435 9119611 := bstep (se 1 (by rfl) ⟨6839708, by rfl⟩ : syracuseStep 9119611 = 13679417) B13679417
theorem B12159481 : Blo 2247435 12159481 := bstep (se 2 (by rfl) ⟨4559805, by rfl⟩ : syracuseStep 12159481 = 9119611) B9119611
theorem B16212641 : Blo 2247435 16212641 := bstep (se 2 (by rfl) ⟨6079740, by rfl⟩ : syracuseStep 16212641 = 12159481) B12159481
theorem B43233709 : Blo 2247435 43233709 := bstep (se 3 (by rfl) ⟨8106320, by rfl⟩ : syracuseStep 43233709 = 16212641) B16212641
theorem B57644945 : Blo 2247435 57644945 := bstep (se 2 (by rfl) ⟨21616854, by rfl⟩ : syracuseStep 57644945 = 43233709) B43233709
theorem B38429963 : Blo 2247435 38429963 := bstep (se 1 (by rfl) ⟨28822472, by rfl⟩ : syracuseStep 38429963 = 57644945) B57644945
theorem B25619975 : Blo 2247435 25619975 := bstep (se 1 (by rfl) ⟨19214981, by rfl⟩ : syracuseStep 25619975 = 38429963) B38429963
theorem B17079983 : Blo 2247435 17079983 := bstep (se 1 (by rfl) ⟨12809987, by rfl⟩ : syracuseStep 17079983 = 25619975) B25619975
theorem B11386655 : Blo 2247435 11386655 := bstep (se 1 (by rfl) ⟨8539991, by rfl⟩ : syracuseStep 11386655 = 17079983) B17079983
theorem B7591103 : Blo 2247435 7591103 := bstep (se 1 (by rfl) ⟨5693327, by rfl⟩ : syracuseStep 7591103 = 11386655) B11386655
theorem B5060735 : Blo 2247435 5060735 := bstep (se 1 (by rfl) ⟨3795551, by rfl⟩ : syracuseStep 5060735 = 7591103) B7591103
theorem B3373823 : Blo 2247435 3373823 := bstep (se 1 (by rfl) ⟨2530367, by rfl⟩ : syracuseStep 3373823 = 5060735) B5060735
theorem B2249215 : Blo 2247435 2249215 := bstep (se 1 (by rfl) ⟨1686911, by rfl⟩ : syracuseStep 2249215 = 3373823) B3373823
theorem B3373829 : Blo 2247435 3373829 := bbase (se 4 (by rfl) ⟨316296, by rfl⟩ : syracuseStep 3373829 = 632593) (by norm_num)
theorem B2249219 : Blo 2247435 2249219 := bstep (se 1 (by rfl) ⟨1686914, by rfl⟩ : syracuseStep 2249219 = 3373829) B3373829
theorem B3795565 : Blo 2247435 3795565 := bbase (se 3 (by rfl) ⟨711668, by rfl⟩ : syracuseStep 3795565 = 1423337) (by norm_num)
theorem B5060753 : Blo 2247435 5060753 := bstep (se 2 (by rfl) ⟨1897782, by rfl⟩ : syracuseStep 5060753 = 3795565) B3795565
theorem B3373835 : Blo 2247435 3373835 := bstep (se 1 (by rfl) ⟨2530376, by rfl⟩ : syracuseStep 3373835 = 5060753) B5060753
theorem B2249223 : Blo 2247435 2249223 := bstep (se 1 (by rfl) ⟨1686917, by rfl⟩ : syracuseStep 2249223 = 3373835) B3373835
theorem B2530381 : Blo 2247435 2530381 := bbase (se 3 (by rfl) ⟨474446, by rfl⟩ : syracuseStep 2530381 = 948893) (by norm_num)
theorem B3373841 : Blo 2247435 3373841 := bstep (se 2 (by rfl) ⟨1265190, by rfl⟩ : syracuseStep 3373841 = 2530381) B2530381
theorem B2249227 : Blo 2247435 2249227 := bstep (se 1 (by rfl) ⟨1686920, by rfl⟩ : syracuseStep 2249227 = 3373841) B3373841
theorem B7591157 : Blo 2247435 7591157 := bbase (se 5 (by rfl) ⟨355835, by rfl⟩ : syracuseStep 7591157 = 711671) (by norm_num)
theorem B5060771 : Blo 2247435 5060771 := bstep (se 1 (by rfl) ⟨3795578, by rfl⟩ : syracuseStep 5060771 = 7591157) B7591157
theorem B3373847 : Blo 2247435 3373847 := bstep (se 1 (by rfl) ⟨2530385, by rfl⟩ : syracuseStep 3373847 = 5060771) B5060771
theorem B2249231 : Blo 2247435 2249231 := bstep (se 1 (by rfl) ⟨1686923, by rfl⟩ : syracuseStep 2249231 = 3373847) B3373847
theorem B3373853 : Blo 2247435 3373853 := bbase (se 3 (by rfl) ⟨632597, by rfl⟩ : syracuseStep 3373853 = 1265195) (by norm_num)
theorem B2249235 : Blo 2247435 2249235 := bstep (se 1 (by rfl) ⟨1686926, by rfl⟩ : syracuseStep 2249235 = 3373853) B3373853
theorem B5060789 : Blo 2247435 5060789 := bbase (se 5 (by rfl) ⟨237224, by rfl⟩ : syracuseStep 5060789 = 474449) (by norm_num)
theorem B3373859 : Blo 2247435 3373859 := bstep (se 1 (by rfl) ⟨2530394, by rfl⟩ : syracuseStep 3373859 = 5060789) B5060789
theorem B2249239 : Blo 2247435 2249239 := bstep (se 1 (by rfl) ⟨1686929, by rfl⟩ : syracuseStep 2249239 = 3373859) B3373859
theorem B6839797 : Blo 2247435 6839797 := bbase (se 5 (by rfl) ⟨320615, by rfl⟩ : syracuseStep 6839797 = 641231) (by norm_num)
theorem B9119729 : Blo 2247435 9119729 := bstep (se 2 (by rfl) ⟨3419898, by rfl⟩ : syracuseStep 9119729 = 6839797) B6839797
theorem B6079819 : Blo 2247435 6079819 := bstep (se 1 (by rfl) ⟨4559864, by rfl⟩ : syracuseStep 6079819 = 9119729) B9119729
theorem B8106425 : Blo 2247435 8106425 := bstep (se 2 (by rfl) ⟨3039909, by rfl⟩ : syracuseStep 8106425 = 6079819) B6079819
theorem B5404283 : Blo 2247435 5404283 := bstep (se 1 (by rfl) ⟨4053212, by rfl⟩ : syracuseStep 5404283 = 8106425) B8106425
theorem B3602855 : Blo 2247435 3602855 := bstep (se 1 (by rfl) ⟨2702141, by rfl⟩ : syracuseStep 3602855 = 5404283) B5404283
theorem B2401903 : Blo 2247435 2401903 := bstep (se 1 (by rfl) ⟨1801427, by rfl⟩ : syracuseStep 2401903 = 3602855) B3602855
theorem B12810149 : Blo 2247435 12810149 := bstep (se 4 (by rfl) ⟨1200951, by rfl⟩ : syracuseStep 12810149 = 2401903) B2401903
theorem B8540099 : Blo 2247435 8540099 := bstep (se 1 (by rfl) ⟨6405074, by rfl⟩ : syracuseStep 8540099 = 12810149) B12810149
theorem B5693399 : Blo 2247435 5693399 := bstep (se 1 (by rfl) ⟨4270049, by rfl⟩ : syracuseStep 5693399 = 8540099) B8540099
theorem B3795599 : Blo 2247435 3795599 := bstep (se 1 (by rfl) ⟨2846699, by rfl⟩ : syracuseStep 3795599 = 5693399) B5693399
theorem B2530399 : Blo 2247435 2530399 := bstep (se 1 (by rfl) ⟨1897799, by rfl⟩ : syracuseStep 2530399 = 3795599) B3795599
theorem B3373865 : Blo 2247435 3373865 := bstep (se 2 (by rfl) ⟨1265199, by rfl⟩ : syracuseStep 3373865 = 2530399) B2530399
theorem B2249243 : Blo 2247435 2249243 := bstep (se 1 (by rfl) ⟨1686932, by rfl⟩ : syracuseStep 2249243 = 3373865) B3373865
theorem B3602861 : Blo 2247435 3602861 := bbase (se 3 (by rfl) ⟨675536, by rfl⟩ : syracuseStep 3602861 = 1351073) (by norm_num)
theorem B2401907 : Blo 2247435 2401907 := bstep (se 1 (by rfl) ⟨1801430, by rfl⟩ : syracuseStep 2401907 = 3602861) B3602861
theorem B6405085 : Blo 2247435 6405085 := bstep (se 3 (by rfl) ⟨1200953, by rfl⟩ : syracuseStep 6405085 = 2401907) B2401907
theorem B8540113 : Blo 2247435 8540113 := bstep (se 2 (by rfl) ⟨3202542, by rfl⟩ : syracuseStep 8540113 = 6405085) B6405085
theorem B11386817 : Blo 2247435 11386817 := bstep (se 2 (by rfl) ⟨4270056, by rfl⟩ : syracuseStep 11386817 = 8540113) B8540113
theorem B7591211 : Blo 2247435 7591211 := bstep (se 1 (by rfl) ⟨5693408, by rfl⟩ : syracuseStep 7591211 = 11386817) B11386817
theorem B5060807 : Blo 2247435 5060807 := bstep (se 1 (by rfl) ⟨3795605, by rfl⟩ : syracuseStep 5060807 = 7591211) B7591211
theorem B3373871 : Blo 2247435 3373871 := bstep (se 1 (by rfl) ⟨2530403, by rfl⟩ : syracuseStep 3373871 = 5060807) B5060807
theorem B2249247 : Blo 2247435 2249247 := bstep (se 1 (by rfl) ⟨1686935, by rfl⟩ : syracuseStep 2249247 = 3373871) B3373871
theorem B3373877 : Blo 2247435 3373877 := bbase (se 5 (by rfl) ⟨158150, by rfl⟩ : syracuseStep 3373877 = 316301) (by norm_num)
theorem B2249251 : Blo 2247435 2249251 := bstep (se 1 (by rfl) ⟨1686938, by rfl⟩ : syracuseStep 2249251 = 3373877) B3373877
theorem B5693429 : Blo 2247435 5693429 := bbase (se 5 (by rfl) ⟨266879, by rfl⟩ : syracuseStep 5693429 = 533759) (by norm_num)
theorem B3795619 : Blo 2247435 3795619 := bstep (se 1 (by rfl) ⟨2846714, by rfl⟩ : syracuseStep 3795619 = 5693429) B5693429
theorem B5060825 : Blo 2247435 5060825 := bstep (se 2 (by rfl) ⟨1897809, by rfl⟩ : syracuseStep 5060825 = 3795619) B3795619
theorem B3373883 : Blo 2247435 3373883 := bstep (se 1 (by rfl) ⟨2530412, by rfl⟩ : syracuseStep 3373883 = 5060825) B5060825
theorem B2249255 : Blo 2247435 2249255 := bstep (se 1 (by rfl) ⟨1686941, by rfl⟩ : syracuseStep 2249255 = 3373883) B3373883
theorem B2530417 : Blo 2247435 2530417 := bbase (se 2 (by rfl) ⟨948906, by rfl⟩ : syracuseStep 2530417 = 1897813) (by norm_num)
theorem B3373889 : Blo 2247435 3373889 := bstep (se 2 (by rfl) ⟨1265208, by rfl⟩ : syracuseStep 3373889 = 2530417) B2530417
theorem B2249259 : Blo 2247435 2249259 := bstep (se 1 (by rfl) ⟨1686944, by rfl⟩ : syracuseStep 2249259 = 3373889) B3373889
theorem B2702165 : Blo 2247435 2702165 := bbase (se 9 (by rfl) ⟨7916, by rfl⟩ : syracuseStep 2702165 = 15833) (by norm_num)
theorem B7205773 : Blo 2247435 7205773 := bstep (se 3 (by rfl) ⟨1351082, by rfl⟩ : syracuseStep 7205773 = 2702165) B2702165
theorem B9607697 : Blo 2247435 9607697 := bstep (se 2 (by rfl) ⟨3602886, by rfl⟩ : syracuseStep 9607697 = 7205773) B7205773
theorem B6405131 : Blo 2247435 6405131 := bstep (se 1 (by rfl) ⟨4803848, by rfl⟩ : syracuseStep 6405131 = 9607697) B9607697
theorem B4270087 : Blo 2247435 4270087 := bstep (se 1 (by rfl) ⟨3202565, by rfl⟩ : syracuseStep 4270087 = 6405131) B6405131
theorem B5693449 : Blo 2247435 5693449 := bstep (se 2 (by rfl) ⟨2135043, by rfl⟩ : syracuseStep 5693449 = 4270087) B4270087
theorem B7591265 : Blo 2247435 7591265 := bstep (se 2 (by rfl) ⟨2846724, by rfl⟩ : syracuseStep 7591265 = 5693449) B5693449
theorem B5060843 : Blo 2247435 5060843 := bstep (se 1 (by rfl) ⟨3795632, by rfl⟩ : syracuseStep 5060843 = 7591265) B7591265
theorem B3373895 : Blo 2247435 3373895 := bstep (se 1 (by rfl) ⟨2530421, by rfl⟩ : syracuseStep 3373895 = 5060843) B5060843
theorem B2249263 : Blo 2247435 2249263 := bstep (se 1 (by rfl) ⟨1686947, by rfl⟩ : syracuseStep 2249263 = 3373895) B3373895
theorem B3373901 : Blo 2247435 3373901 := bbase (se 3 (by rfl) ⟨632606, by rfl⟩ : syracuseStep 3373901 = 1265213) (by norm_num)
theorem B2249267 : Blo 2247435 2249267 := bstep (se 1 (by rfl) ⟨1686950, by rfl⟩ : syracuseStep 2249267 = 3373901) B3373901
theorem B5060861 : Blo 2247435 5060861 := bbase (se 3 (by rfl) ⟨948911, by rfl⟩ : syracuseStep 5060861 = 1897823) (by norm_num)
theorem B3373907 : Blo 2247435 3373907 := bstep (se 1 (by rfl) ⟨2530430, by rfl⟩ : syracuseStep 3373907 = 5060861) B5060861
theorem B2249271 : Blo 2247435 2249271 := bstep (se 1 (by rfl) ⟨1686953, by rfl⟩ : syracuseStep 2249271 = 3373907) B3373907
theorem B3795653 : Blo 2247435 3795653 := bbase (se 4 (by rfl) ⟨355842, by rfl⟩ : syracuseStep 3795653 = 711685) (by norm_num)
theorem B2530435 : Blo 2247435 2530435 := bstep (se 1 (by rfl) ⟨1897826, by rfl⟩ : syracuseStep 2530435 = 3795653) B3795653
theorem B3373913 : Blo 2247435 3373913 := bstep (se 2 (by rfl) ⟨1265217, by rfl⟩ : syracuseStep 3373913 = 2530435) B2530435
theorem B2249275 : Blo 2247435 2249275 := bstep (se 1 (by rfl) ⟨1686956, by rfl⟩ : syracuseStep 2249275 = 3373913) B3373913
theorem B17080469 : Blo 2247435 17080469 := bbase (se 6 (by rfl) ⟨400323, by rfl⟩ : syracuseStep 17080469 = 800647) (by norm_num)
theorem B11386979 : Blo 2247435 11386979 := bstep (se 1 (by rfl) ⟨8540234, by rfl⟩ : syracuseStep 11386979 = 17080469) B17080469
theorem B7591319 : Blo 2247435 7591319 := bstep (se 1 (by rfl) ⟨5693489, by rfl⟩ : syracuseStep 7591319 = 11386979) B11386979
theorem B5060879 : Blo 2247435 5060879 := bstep (se 1 (by rfl) ⟨3795659, by rfl⟩ : syracuseStep 5060879 = 7591319) B7591319
theorem B3373919 : Blo 2247435 3373919 := bstep (se 1 (by rfl) ⟨2530439, by rfl⟩ : syracuseStep 3373919 = 5060879) B5060879
theorem B2249279 : Blo 2247435 2249279 := bstep (se 1 (by rfl) ⟨1686959, by rfl⟩ : syracuseStep 2249279 = 3373919) B3373919
theorem B3373925 : Blo 2247435 3373925 := bbase (se 4 (by rfl) ⟨316305, by rfl⟩ : syracuseStep 3373925 = 632611) (by norm_num)
theorem B2249283 : Blo 2247435 2249283 := bstep (se 1 (by rfl) ⟨1686962, by rfl⟩ : syracuseStep 2249283 = 3373925) B3373925
theorem B4270133 : Blo 2247435 4270133 := bbase (se 5 (by rfl) ⟨200162, by rfl⟩ : syracuseStep 4270133 = 400325) (by norm_num)
theorem B2846755 : Blo 2247435 2846755 := bstep (se 1 (by rfl) ⟨2135066, by rfl⟩ : syracuseStep 2846755 = 4270133) B4270133
theorem B3795673 : Blo 2247435 3795673 := bstep (se 2 (by rfl) ⟨1423377, by rfl⟩ : syracuseStep 3795673 = 2846755) B2846755
theorem B5060897 : Blo 2247435 5060897 := bstep (se 2 (by rfl) ⟨1897836, by rfl⟩ : syracuseStep 5060897 = 3795673) B3795673
theorem B3373931 : Blo 2247435 3373931 := bstep (se 1 (by rfl) ⟨2530448, by rfl⟩ : syracuseStep 3373931 = 5060897) B5060897
theorem B2249287 : Blo 2247435 2249287 := bstep (se 1 (by rfl) ⟨1686965, by rfl⟩ : syracuseStep 2249287 = 3373931) B3373931
theorem B2530453 : Blo 2247435 2530453 := bbase (se 6 (by rfl) ⟨59307, by rfl⟩ : syracuseStep 2530453 = 118615) (by norm_num)
theorem B3373937 : Blo 2247435 3373937 := bstep (se 2 (by rfl) ⟨1265226, by rfl⟩ : syracuseStep 3373937 = 2530453) B2530453
theorem B2249291 : Blo 2247435 2249291 := bstep (se 1 (by rfl) ⟨1686968, by rfl⟩ : syracuseStep 2249291 = 3373937) B3373937
theorem B2846765 : Blo 2247435 2846765 := bbase (se 3 (by rfl) ⟨533768, by rfl⟩ : syracuseStep 2846765 = 1067537) (by norm_num)
theorem B7591373 : Blo 2247435 7591373 := bstep (se 3 (by rfl) ⟨1423382, by rfl⟩ : syracuseStep 7591373 = 2846765) B2846765
theorem B5060915 : Blo 2247435 5060915 := bstep (se 1 (by rfl) ⟨3795686, by rfl⟩ : syracuseStep 5060915 = 7591373) B7591373
theorem B3373943 : Blo 2247435 3373943 := bstep (se 1 (by rfl) ⟨2530457, by rfl⟩ : syracuseStep 3373943 = 5060915) B5060915
theorem B2249295 : Blo 2247435 2249295 := bstep (se 1 (by rfl) ⟨1686971, by rfl⟩ : syracuseStep 2249295 = 3373943) B3373943
theorem B3373949 : Blo 2247435 3373949 := bbase (se 3 (by rfl) ⟨632615, by rfl⟩ : syracuseStep 3373949 = 1265231) (by norm_num)
theorem B2249299 : Blo 2247435 2249299 := bstep (se 1 (by rfl) ⟨1686974, by rfl⟩ : syracuseStep 2249299 = 3373949) B3373949
theorem B5060933 : Blo 2247435 5060933 := bbase (se 4 (by rfl) ⟨474462, by rfl⟩ : syracuseStep 5060933 = 948925) (by norm_num)
theorem B3373955 : Blo 2247435 3373955 := bstep (se 1 (by rfl) ⟨2530466, by rfl⟩ : syracuseStep 3373955 = 5060933) B5060933
theorem B2249303 : Blo 2247435 2249303 := bstep (se 1 (by rfl) ⟨1686977, by rfl⟩ : syracuseStep 2249303 = 3373955) B3373955
theorem B8894693 : Blo 2247435 8894693 := bbase (se 4 (by rfl) ⟨833877, by rfl⟩ : syracuseStep 8894693 = 1667755) (by norm_num)
theorem B5929795 : Blo 2247435 5929795 := bstep (se 1 (by rfl) ⟨4447346, by rfl⟩ : syracuseStep 5929795 = 8894693) B8894693
theorem B7906393 : Blo 2247435 7906393 := bstep (se 2 (by rfl) ⟨2964897, by rfl⟩ : syracuseStep 7906393 = 5929795) B5929795
theorem B42167429 : Blo 2247435 42167429 := bstep (se 4 (by rfl) ⟨3953196, by rfl⟩ : syracuseStep 42167429 = 7906393) B7906393
theorem B28111619 : Blo 2247435 28111619 := bstep (se 1 (by rfl) ⟨21083714, by rfl⟩ : syracuseStep 28111619 = 42167429) B42167429
theorem B18741079 : Blo 2247435 18741079 := bstep (se 1 (by rfl) ⟨14055809, by rfl⟩ : syracuseStep 18741079 = 28111619) B28111619
theorem B24988105 : Blo 2247435 24988105 := bstep (se 2 (by rfl) ⟨9370539, by rfl⟩ : syracuseStep 24988105 = 18741079) B18741079
theorem B133269893 : Blo 2247435 133269893 := bstep (se 4 (by rfl) ⟨12494052, by rfl⟩ : syracuseStep 133269893 = 24988105) B24988105
theorem B88846595 : Blo 2247435 88846595 := bstep (se 1 (by rfl) ⟨66634946, by rfl⟩ : syracuseStep 88846595 = 133269893) B133269893
theorem B59231063 : Blo 2247435 59231063 := bstep (se 1 (by rfl) ⟨44423297, by rfl⟩ : syracuseStep 59231063 = 88846595) B88846595
theorem B39487375 : Blo 2247435 39487375 := bstep (se 1 (by rfl) ⟨29615531, by rfl⟩ : syracuseStep 39487375 = 59231063) B59231063
theorem B52649833 : Blo 2247435 52649833 := bstep (se 2 (by rfl) ⟨19743687, by rfl⟩ : syracuseStep 52649833 = 39487375) B39487375
theorem B70199777 : Blo 2247435 70199777 := bstep (se 2 (by rfl) ⟨26324916, by rfl⟩ : syracuseStep 70199777 = 52649833) B52649833
theorem B46799851 : Blo 2247435 46799851 := bstep (se 1 (by rfl) ⟨35099888, by rfl⟩ : syracuseStep 46799851 = 70199777) B70199777
theorem B62399801 : Blo 2247435 62399801 := bstep (se 2 (by rfl) ⟨23399925, by rfl⟩ : syracuseStep 62399801 = 46799851) B46799851
theorem B41599867 : Blo 2247435 41599867 := bstep (se 1 (by rfl) ⟨31199900, by rfl⟩ : syracuseStep 41599867 = 62399801) B62399801
theorem B55466489 : Blo 2247435 55466489 := bstep (se 2 (by rfl) ⟨20799933, by rfl⟩ : syracuseStep 55466489 = 41599867) B41599867
theorem B147910637 : Blo 2247435 147910637 := bstep (se 3 (by rfl) ⟨27733244, by rfl⟩ : syracuseStep 147910637 = 55466489) B55466489
theorem B98607091 : Blo 2247435 98607091 := bstep (se 1 (by rfl) ⟨73955318, by rfl⟩ : syracuseStep 98607091 = 147910637) B147910637
theorem B131476121 : Blo 2247435 131476121 := bstep (se 2 (by rfl) ⟨49303545, by rfl⟩ : syracuseStep 131476121 = 98607091) B98607091
theorem B87650747 : Blo 2247435 87650747 := bstep (se 1 (by rfl) ⟨65738060, by rfl⟩ : syracuseStep 87650747 = 131476121) B131476121
theorem B58433831 : Blo 2247435 58433831 := bstep (se 1 (by rfl) ⟨43825373, by rfl⟩ : syracuseStep 58433831 = 87650747) B87650747
theorem B38955887 : Blo 2247435 38955887 := bstep (se 1 (by rfl) ⟨29216915, by rfl⟩ : syracuseStep 38955887 = 58433831) B58433831
theorem B25970591 : Blo 2247435 25970591 := bstep (se 1 (by rfl) ⟨19477943, by rfl⟩ : syracuseStep 25970591 = 38955887) B38955887
theorem B69254909 : Blo 2247435 69254909 := bstep (se 3 (by rfl) ⟨12985295, by rfl⟩ : syracuseStep 69254909 = 25970591) B25970591
theorem B46169939 : Blo 2247435 46169939 := bstep (se 1 (by rfl) ⟨34627454, by rfl⟩ : syracuseStep 46169939 = 69254909) B69254909
theorem B30779959 : Blo 2247435 30779959 := bstep (se 1 (by rfl) ⟨23084969, by rfl⟩ : syracuseStep 30779959 = 46169939) B46169939
theorem B41039945 : Blo 2247435 41039945 := bstep (se 2 (by rfl) ⟨15389979, by rfl⟩ : syracuseStep 41039945 = 30779959) B30779959
theorem B27359963 : Blo 2247435 27359963 := bstep (se 1 (by rfl) ⟨20519972, by rfl⟩ : syracuseStep 27359963 = 41039945) B41039945
theorem B18239975 : Blo 2247435 18239975 := bstep (se 1 (by rfl) ⟨13679981, by rfl⟩ : syracuseStep 18239975 = 27359963) B27359963
theorem B12159983 : Blo 2247435 12159983 := bstep (se 1 (by rfl) ⟨9119987, by rfl⟩ : syracuseStep 12159983 = 18239975) B18239975
theorem B8106655 : Blo 2247435 8106655 := bstep (se 1 (by rfl) ⟨6079991, by rfl⟩ : syracuseStep 8106655 = 12159983) B12159983
theorem B10808873 : Blo 2247435 10808873 := bstep (se 2 (by rfl) ⟨4053327, by rfl⟩ : syracuseStep 10808873 = 8106655) B8106655
theorem B7205915 : Blo 2247435 7205915 := bstep (se 1 (by rfl) ⟨5404436, by rfl⟩ : syracuseStep 7205915 = 10808873) B10808873
theorem B4803943 : Blo 2247435 4803943 := bstep (se 1 (by rfl) ⟨3602957, by rfl⟩ : syracuseStep 4803943 = 7205915) B7205915
theorem B6405257 : Blo 2247435 6405257 := bstep (se 2 (by rfl) ⟨2401971, by rfl⟩ : syracuseStep 6405257 = 4803943) B4803943
theorem B4270171 : Blo 2247435 4270171 := bstep (se 1 (by rfl) ⟨3202628, by rfl⟩ : syracuseStep 4270171 = 6405257) B6405257
theorem B5693561 : Blo 2247435 5693561 := bstep (se 2 (by rfl) ⟨2135085, by rfl⟩ : syracuseStep 5693561 = 4270171) B4270171
theorem B3795707 : Blo 2247435 3795707 := bstep (se 1 (by rfl) ⟨2846780, by rfl⟩ : syracuseStep 3795707 = 5693561) B5693561
theorem B2530471 : Blo 2247435 2530471 := bstep (se 1 (by rfl) ⟨1897853, by rfl⟩ : syracuseStep 2530471 = 3795707) B3795707
theorem B3373961 : Blo 2247435 3373961 := bstep (se 2 (by rfl) ⟨1265235, by rfl⟩ : syracuseStep 3373961 = 2530471) B2530471
theorem B2249307 : Blo 2247435 2249307 := bstep (se 1 (by rfl) ⟨1686980, by rfl⟩ : syracuseStep 2249307 = 3373961) B3373961
theorem B11387141 : Blo 2247435 11387141 := bbase (se 4 (by rfl) ⟨1067544, by rfl⟩ : syracuseStep 11387141 = 2135089) (by norm_num)
theorem B7591427 : Blo 2247435 7591427 := bstep (se 1 (by rfl) ⟨5693570, by rfl⟩ : syracuseStep 7591427 = 11387141) B11387141
theorem B5060951 : Blo 2247435 5060951 := bstep (se 1 (by rfl) ⟨3795713, by rfl⟩ : syracuseStep 5060951 = 7591427) B7591427
theorem B3373967 : Blo 2247435 3373967 := bstep (se 1 (by rfl) ⟨2530475, by rfl⟩ : syracuseStep 3373967 = 5060951) B5060951
theorem B2249311 : Blo 2247435 2249311 := bstep (se 1 (by rfl) ⟨1686983, by rfl⟩ : syracuseStep 2249311 = 3373967) B3373967
theorem B3373973 : Blo 2247435 3373973 := bbase (se 6 (by rfl) ⟨79077, by rfl⟩ : syracuseStep 3373973 = 158155) (by norm_num)
theorem B2249315 : Blo 2247435 2249315 := bstep (se 1 (by rfl) ⟨1686986, by rfl⟩ : syracuseStep 2249315 = 3373973) B3373973
theorem B12810581 : Blo 2247435 12810581 := bbase (se 10 (by rfl) ⟨18765, by rfl⟩ : syracuseStep 12810581 = 37531) (by norm_num)
theorem B8540387 : Blo 2247435 8540387 := bstep (se 1 (by rfl) ⟨6405290, by rfl⟩ : syracuseStep 8540387 = 12810581) B12810581
theorem B5693591 : Blo 2247435 5693591 := bstep (se 1 (by rfl) ⟨4270193, by rfl⟩ : syracuseStep 5693591 = 8540387) B8540387
theorem B3795727 : Blo 2247435 3795727 := bstep (se 1 (by rfl) ⟨2846795, by rfl⟩ : syracuseStep 3795727 = 5693591) B5693591
theorem B5060969 : Blo 2247435 5060969 := bstep (se 2 (by rfl) ⟨1897863, by rfl⟩ : syracuseStep 5060969 = 3795727) B3795727
theorem B3373979 : Blo 2247435 3373979 := bstep (se 1 (by rfl) ⟨2530484, by rfl⟩ : syracuseStep 3373979 = 5060969) B5060969
theorem B2249319 : Blo 2247435 2249319 := bstep (se 1 (by rfl) ⟨1686989, by rfl⟩ : syracuseStep 2249319 = 3373979) B3373979
theorem B2530489 : Blo 2247435 2530489 := bbase (se 2 (by rfl) ⟨948933, by rfl⟩ : syracuseStep 2530489 = 1897867) (by norm_num)
theorem B3373985 : Blo 2247435 3373985 := bstep (se 2 (by rfl) ⟨1265244, by rfl⟩ : syracuseStep 3373985 = 2530489) B2530489
theorem B2249323 : Blo 2247435 2249323 := bstep (se 1 (by rfl) ⟨1686992, by rfl⟩ : syracuseStep 2249323 = 3373985) B3373985
theorem B3602989 : Blo 2247435 3602989 := bbase (se 3 (by rfl) ⟨675560, by rfl⟩ : syracuseStep 3602989 = 1351121) (by norm_num)
theorem B4803985 : Blo 2247435 4803985 := bstep (se 2 (by rfl) ⟨1801494, by rfl⟩ : syracuseStep 4803985 = 3602989) B3602989
theorem B6405313 : Blo 2247435 6405313 := bstep (se 2 (by rfl) ⟨2401992, by rfl⟩ : syracuseStep 6405313 = 4803985) B4803985
theorem B8540417 : Blo 2247435 8540417 := bstep (se 2 (by rfl) ⟨3202656, by rfl⟩ : syracuseStep 8540417 = 6405313) B6405313
theorem B5693611 : Blo 2247435 5693611 := bstep (se 1 (by rfl) ⟨4270208, by rfl⟩ : syracuseStep 5693611 = 8540417) B8540417
theorem B7591481 : Blo 2247435 7591481 := bstep (se 2 (by rfl) ⟨2846805, by rfl⟩ : syracuseStep 7591481 = 5693611) B5693611
theorem B5060987 : Blo 2247435 5060987 := bstep (se 1 (by rfl) ⟨3795740, by rfl⟩ : syracuseStep 5060987 = 7591481) B7591481
theorem B3373991 : Blo 2247435 3373991 := bstep (se 1 (by rfl) ⟨2530493, by rfl⟩ : syracuseStep 3373991 = 5060987) B5060987
theorem B2249327 : Blo 2247435 2249327 := bstep (se 1 (by rfl) ⟨1686995, by rfl⟩ : syracuseStep 2249327 = 3373991) B3373991
theorem B3373997 : Blo 2247435 3373997 := bbase (se 3 (by rfl) ⟨632624, by rfl⟩ : syracuseStep 3373997 = 1265249) (by norm_num)
theorem B2249331 : Blo 2247435 2249331 := bstep (se 1 (by rfl) ⟨1686998, by rfl⟩ : syracuseStep 2249331 = 3373997) B3373997
theorem B5061005 : Blo 2247435 5061005 := bbase (se 3 (by rfl) ⟨948938, by rfl⟩ : syracuseStep 5061005 = 1897877) (by norm_num)
theorem B3374003 : Blo 2247435 3374003 := bstep (se 1 (by rfl) ⟨2530502, by rfl⟩ : syracuseStep 3374003 = 5061005) B5061005
theorem B2249335 : Blo 2247435 2249335 := bstep (se 1 (by rfl) ⟨1687001, by rfl⟩ : syracuseStep 2249335 = 3374003) B3374003
theorem B2846821 : Blo 2247435 2846821 := bbase (se 4 (by rfl) ⟨266889, by rfl⟩ : syracuseStep 2846821 = 533779) (by norm_num)
theorem B3795761 : Blo 2247435 3795761 := bstep (se 2 (by rfl) ⟨1423410, by rfl⟩ : syracuseStep 3795761 = 2846821) B2846821
theorem B2530507 : Blo 2247435 2530507 := bstep (se 1 (by rfl) ⟨1897880, by rfl⟩ : syracuseStep 2530507 = 3795761) B3795761
theorem B3374009 : Blo 2247435 3374009 := bstep (se 2 (by rfl) ⟨1265253, by rfl⟩ : syracuseStep 3374009 = 2530507) B2530507
theorem B2249339 : Blo 2247435 2249339 := bstep (se 1 (by rfl) ⟨1687004, by rfl⟩ : syracuseStep 2249339 = 3374009) B3374009
theorem B2565037 : Blo 2247435 2565037 := bbase (se 3 (by rfl) ⟨480944, by rfl⟩ : syracuseStep 2565037 = 961889) (by norm_num)
theorem B13680197 : Blo 2247435 13680197 := bstep (se 4 (by rfl) ⟨1282518, by rfl⟩ : syracuseStep 13680197 = 2565037) B2565037
theorem B9120131 : Blo 2247435 9120131 := bstep (se 1 (by rfl) ⟨6840098, by rfl⟩ : syracuseStep 9120131 = 13680197) B13680197
theorem B6080087 : Blo 2247435 6080087 := bstep (se 1 (by rfl) ⟨4560065, by rfl⟩ : syracuseStep 6080087 = 9120131) B9120131
theorem B4053391 : Blo 2247435 4053391 := bstep (se 1 (by rfl) ⟨3040043, by rfl⟩ : syracuseStep 4053391 = 6080087) B6080087
theorem B21618085 : Blo 2247435 21618085 := bstep (se 4 (by rfl) ⟨2026695, by rfl⟩ : syracuseStep 21618085 = 4053391) B4053391
theorem B28824113 : Blo 2247435 28824113 := bstep (se 2 (by rfl) ⟨10809042, by rfl⟩ : syracuseStep 28824113 = 21618085) B21618085
theorem B19216075 : Blo 2247435 19216075 := bstep (se 1 (by rfl) ⟨14412056, by rfl⟩ : syracuseStep 19216075 = 28824113) B28824113
theorem B25621433 : Blo 2247435 25621433 := bstep (se 2 (by rfl) ⟨9608037, by rfl⟩ : syracuseStep 25621433 = 19216075) B19216075
theorem B17080955 : Blo 2247435 17080955 := bstep (se 1 (by rfl) ⟨12810716, by rfl⟩ : syracuseStep 17080955 = 25621433) B25621433
theorem B11387303 : Blo 2247435 11387303 := bstep (se 1 (by rfl) ⟨8540477, by rfl⟩ : syracuseStep 11387303 = 17080955) B17080955
theorem B7591535 : Blo 2247435 7591535 := bstep (se 1 (by rfl) ⟨5693651, by rfl⟩ : syracuseStep 7591535 = 11387303) B11387303
theorem B5061023 : Blo 2247435 5061023 := bstep (se 1 (by rfl) ⟨3795767, by rfl⟩ : syracuseStep 5061023 = 7591535) B7591535
theorem B3374015 : Blo 2247435 3374015 := bstep (se 1 (by rfl) ⟨2530511, by rfl⟩ : syracuseStep 3374015 = 5061023) B5061023
theorem B2249343 : Blo 2247435 2249343 := bstep (se 1 (by rfl) ⟨1687007, by rfl⟩ : syracuseStep 2249343 = 3374015) B3374015
theorem B3374021 : Blo 2247435 3374021 := bbase (se 4 (by rfl) ⟨316314, by rfl⟩ : syracuseStep 3374021 = 632629) (by norm_num)
theorem B2249347 : Blo 2247435 2249347 := bstep (se 1 (by rfl) ⟨1687010, by rfl⟩ : syracuseStep 2249347 = 3374021) B3374021
theorem B3795781 : Blo 2247435 3795781 := bbase (se 4 (by rfl) ⟨355854, by rfl⟩ : syracuseStep 3795781 = 711709) (by norm_num)
theorem B5061041 : Blo 2247435 5061041 := bstep (se 2 (by rfl) ⟨1897890, by rfl⟩ : syracuseStep 5061041 = 3795781) B3795781
theorem B3374027 : Blo 2247435 3374027 := bstep (se 1 (by rfl) ⟨2530520, by rfl⟩ : syracuseStep 3374027 = 5061041) B5061041
theorem B2249351 : Blo 2247435 2249351 := bstep (se 1 (by rfl) ⟨1687013, by rfl⟩ : syracuseStep 2249351 = 3374027) B3374027
theorem B2530525 : Blo 2247435 2530525 := bbase (se 3 (by rfl) ⟨474473, by rfl⟩ : syracuseStep 2530525 = 948947) (by norm_num)
theorem B3374033 : Blo 2247435 3374033 := bstep (se 2 (by rfl) ⟨1265262, by rfl⟩ : syracuseStep 3374033 = 2530525) B2530525
theorem B2249355 : Blo 2247435 2249355 := bstep (se 1 (by rfl) ⟨1687016, by rfl⟩ : syracuseStep 2249355 = 3374033) B3374033
theorem B7591589 : Blo 2247435 7591589 := bbase (se 4 (by rfl) ⟨711711, by rfl⟩ : syracuseStep 7591589 = 1423423) (by norm_num)
theorem B5061059 : Blo 2247435 5061059 := bstep (se 1 (by rfl) ⟨3795794, by rfl⟩ : syracuseStep 5061059 = 7591589) B7591589
theorem B3374039 : Blo 2247435 3374039 := bstep (se 1 (by rfl) ⟨2530529, by rfl⟩ : syracuseStep 3374039 = 5061059) B5061059
theorem B2249359 : Blo 2247435 2249359 := bstep (se 1 (by rfl) ⟨1687019, by rfl⟩ : syracuseStep 2249359 = 3374039) B3374039
theorem B3374045 : Blo 2247435 3374045 := bbase (se 3 (by rfl) ⟨632633, by rfl⟩ : syracuseStep 3374045 = 1265267) (by norm_num)
theorem B2249363 : Blo 2247435 2249363 := bstep (se 1 (by rfl) ⟨1687022, by rfl⟩ : syracuseStep 2249363 = 3374045) B3374045
theorem B5061077 : Blo 2247435 5061077 := bbase (se 7 (by rfl) ⟨59309, by rfl⟩ : syracuseStep 5061077 = 118619) (by norm_num)
theorem B3374051 : Blo 2247435 3374051 := bstep (se 1 (by rfl) ⟨2530538, by rfl⟩ : syracuseStep 3374051 = 5061077) B5061077
theorem B2249367 : Blo 2247435 2249367 := bstep (se 1 (by rfl) ⟨1687025, by rfl⟩ : syracuseStep 2249367 = 3374051) B3374051
theorem B8775221 : Blo 2247435 8775221 := bbase (se 5 (by rfl) ⟨411338, by rfl⟩ : syracuseStep 8775221 = 822677) (by norm_num)
theorem B23400589 : Blo 2247435 23400589 := bstep (se 3 (by rfl) ⟨4387610, by rfl⟩ : syracuseStep 23400589 = 8775221) B8775221
theorem B31200785 : Blo 2247435 31200785 := bstep (se 2 (by rfl) ⟨11700294, by rfl⟩ : syracuseStep 31200785 = 23400589) B23400589
theorem B20800523 : Blo 2247435 20800523 := bstep (se 1 (by rfl) ⟨15600392, by rfl⟩ : syracuseStep 20800523 = 31200785) B31200785
theorem B55468061 : Blo 2247435 55468061 := bstep (se 3 (by rfl) ⟨10400261, by rfl⟩ : syracuseStep 55468061 = 20800523) B20800523
theorem B36978707 : Blo 2247435 36978707 := bstep (se 1 (by rfl) ⟨27734030, by rfl⟩ : syracuseStep 36978707 = 55468061) B55468061
theorem B98609885 : Blo 2247435 98609885 := bstep (se 3 (by rfl) ⟨18489353, by rfl⟩ : syracuseStep 98609885 = 36978707) B36978707
theorem B65739923 : Blo 2247435 65739923 := bstep (se 1 (by rfl) ⟨49304942, by rfl⟩ : syracuseStep 65739923 = 98609885) B98609885
theorem B43826615 : Blo 2247435 43826615 := bstep (se 1 (by rfl) ⟨32869961, by rfl⟩ : syracuseStep 43826615 = 65739923) B65739923
theorem B29217743 : Blo 2247435 29217743 := bstep (se 1 (by rfl) ⟨21913307, by rfl⟩ : syracuseStep 29217743 = 43826615) B43826615
theorem B19478495 : Blo 2247435 19478495 := bstep (se 1 (by rfl) ⟨14608871, by rfl⟩ : syracuseStep 19478495 = 29217743) B29217743
theorem B51942653 : Blo 2247435 51942653 := bstep (se 3 (by rfl) ⟨9739247, by rfl⟩ : syracuseStep 51942653 = 19478495) B19478495
theorem B34628435 : Blo 2247435 34628435 := bstep (se 1 (by rfl) ⟨25971326, by rfl⟩ : syracuseStep 34628435 = 51942653) B51942653
theorem B23085623 : Blo 2247435 23085623 := bstep (se 1 (by rfl) ⟨17314217, by rfl⟩ : syracuseStep 23085623 = 34628435) B34628435
theorem B15390415 : Blo 2247435 15390415 := bstep (se 1 (by rfl) ⟨11542811, by rfl⟩ : syracuseStep 15390415 = 23085623) B23085623
theorem B20520553 : Blo 2247435 20520553 := bstep (se 2 (by rfl) ⟨7695207, by rfl⟩ : syracuseStep 20520553 = 15390415) B15390415
theorem B27360737 : Blo 2247435 27360737 := bstep (se 2 (by rfl) ⟨10260276, by rfl⟩ : syracuseStep 27360737 = 20520553) B20520553
theorem B18240491 : Blo 2247435 18240491 := bstep (se 1 (by rfl) ⟨13680368, by rfl⟩ : syracuseStep 18240491 = 27360737) B27360737
theorem B48641309 : Blo 2247435 48641309 := bstep (se 3 (by rfl) ⟨9120245, by rfl⟩ : syracuseStep 48641309 = 18240491) B18240491
theorem B32427539 : Blo 2247435 32427539 := bstep (se 1 (by rfl) ⟨24320654, by rfl⟩ : syracuseStep 32427539 = 48641309) B48641309
theorem B21618359 : Blo 2247435 21618359 := bstep (se 1 (by rfl) ⟨16213769, by rfl⟩ : syracuseStep 21618359 = 32427539) B32427539
theorem B14412239 : Blo 2247435 14412239 := bstep (se 1 (by rfl) ⟨10809179, by rfl⟩ : syracuseStep 14412239 = 21618359) B21618359
theorem B9608159 : Blo 2247435 9608159 := bstep (se 1 (by rfl) ⟨7206119, by rfl⟩ : syracuseStep 9608159 = 14412239) B14412239
theorem B6405439 : Blo 2247435 6405439 := bstep (se 1 (by rfl) ⟨4804079, by rfl⟩ : syracuseStep 6405439 = 9608159) B9608159
theorem B8540585 : Blo 2247435 8540585 := bstep (se 2 (by rfl) ⟨3202719, by rfl⟩ : syracuseStep 8540585 = 6405439) B6405439
theorem B5693723 : Blo 2247435 5693723 := bstep (se 1 (by rfl) ⟨4270292, by rfl⟩ : syracuseStep 5693723 = 8540585) B8540585
theorem B3795815 : Blo 2247435 3795815 := bstep (se 1 (by rfl) ⟨2846861, by rfl⟩ : syracuseStep 3795815 = 5693723) B5693723
theorem B2530543 : Blo 2247435 2530543 := bstep (se 1 (by rfl) ⟨1897907, by rfl⟩ : syracuseStep 2530543 = 3795815) B3795815
theorem B3374057 : Blo 2247435 3374057 := bstep (se 2 (by rfl) ⟨1265271, by rfl⟩ : syracuseStep 3374057 = 2530543) B2530543
theorem B2249371 : Blo 2247435 2249371 := bstep (se 1 (by rfl) ⟨1687028, by rfl⟩ : syracuseStep 2249371 = 3374057) B3374057
theorem B6840197 : Blo 2247435 6840197 := bbase (se 4 (by rfl) ⟨641268, by rfl⟩ : syracuseStep 6840197 = 1282537) (by norm_num)
theorem B4560131 : Blo 2247435 4560131 := bstep (se 1 (by rfl) ⟨3420098, by rfl⟩ : syracuseStep 4560131 = 6840197) B6840197
theorem B3040087 : Blo 2247435 3040087 := bstep (se 1 (by rfl) ⟨2280065, by rfl⟩ : syracuseStep 3040087 = 4560131) B4560131
theorem B4053449 : Blo 2247435 4053449 := bstep (se 2 (by rfl) ⟨1520043, by rfl⟩ : syracuseStep 4053449 = 3040087) B3040087
theorem B10809197 : Blo 2247435 10809197 := bstep (se 3 (by rfl) ⟨2026724, by rfl⟩ : syracuseStep 10809197 = 4053449) B4053449
theorem B7206131 : Blo 2247435 7206131 := bstep (se 1 (by rfl) ⟨5404598, by rfl⟩ : syracuseStep 7206131 = 10809197) B10809197
theorem B19216349 : Blo 2247435 19216349 := bstep (se 3 (by rfl) ⟨3603065, by rfl⟩ : syracuseStep 19216349 = 7206131) B7206131
theorem B12810899 : Blo 2247435 12810899 := bstep (se 1 (by rfl) ⟨9608174, by rfl⟩ : syracuseStep 12810899 = 19216349) B19216349
theorem B8540599 : Blo 2247435 8540599 := bstep (se 1 (by rfl) ⟨6405449, by rfl⟩ : syracuseStep 8540599 = 12810899) B12810899
theorem B11387465 : Blo 2247435 11387465 := bstep (se 2 (by rfl) ⟨4270299, by rfl⟩ : syracuseStep 11387465 = 8540599) B8540599
theorem B7591643 : Blo 2247435 7591643 := bstep (se 1 (by rfl) ⟨5693732, by rfl⟩ : syracuseStep 7591643 = 11387465) B11387465
theorem B5061095 : Blo 2247435 5061095 := bstep (se 1 (by rfl) ⟨3795821, by rfl⟩ : syracuseStep 5061095 = 7591643) B7591643
theorem B3374063 : Blo 2247435 3374063 := bstep (se 1 (by rfl) ⟨2530547, by rfl⟩ : syracuseStep 3374063 = 5061095) B5061095
theorem B2249375 : Blo 2247435 2249375 := bstep (se 1 (by rfl) ⟨1687031, by rfl⟩ : syracuseStep 2249375 = 3374063) B3374063
theorem B3374069 : Blo 2247435 3374069 := bbase (se 5 (by rfl) ⟨158159, by rfl⟩ : syracuseStep 3374069 = 316319) (by norm_num)
theorem B2249379 : Blo 2247435 2249379 := bstep (se 1 (by rfl) ⟨1687034, by rfl⟩ : syracuseStep 2249379 = 3374069) B3374069
theorem B6080197 : Blo 2247435 6080197 := bbase (se 4 (by rfl) ⟨570018, by rfl⟩ : syracuseStep 6080197 = 1140037) (by norm_num)
theorem B8106929 : Blo 2247435 8106929 := bstep (se 2 (by rfl) ⟨3040098, by rfl⟩ : syracuseStep 8106929 = 6080197) B6080197
theorem B5404619 : Blo 2247435 5404619 := bstep (se 1 (by rfl) ⟨4053464, by rfl⟩ : syracuseStep 5404619 = 8106929) B8106929
theorem B3603079 : Blo 2247435 3603079 := bstep (se 1 (by rfl) ⟨2702309, by rfl⟩ : syracuseStep 3603079 = 5404619) B5404619
theorem B4804105 : Blo 2247435 4804105 := bstep (se 2 (by rfl) ⟨1801539, by rfl⟩ : syracuseStep 4804105 = 3603079) B3603079
theorem B6405473 : Blo 2247435 6405473 := bstep (se 2 (by rfl) ⟨2402052, by rfl⟩ : syracuseStep 6405473 = 4804105) B4804105
theorem B4270315 : Blo 2247435 4270315 := bstep (se 1 (by rfl) ⟨3202736, by rfl⟩ : syracuseStep 4270315 = 6405473) B6405473
theorem B5693753 : Blo 2247435 5693753 := bstep (se 2 (by rfl) ⟨2135157, by rfl⟩ : syracuseStep 5693753 = 4270315) B4270315
theorem B3795835 : Blo 2247435 3795835 := bstep (se 1 (by rfl) ⟨2846876, by rfl⟩ : syracuseStep 3795835 = 5693753) B5693753
theorem B5061113 : Blo 2247435 5061113 := bstep (se 2 (by rfl) ⟨1897917, by rfl⟩ : syracuseStep 5061113 = 3795835) B3795835
theorem B3374075 : Blo 2247435 3374075 := bstep (se 1 (by rfl) ⟨2530556, by rfl⟩ : syracuseStep 3374075 = 5061113) B5061113
theorem B2249383 : Blo 2247435 2249383 := bstep (se 1 (by rfl) ⟨1687037, by rfl⟩ : syracuseStep 2249383 = 3374075) B3374075
theorem B2530561 : Blo 2247435 2530561 := bbase (se 2 (by rfl) ⟨948960, by rfl⟩ : syracuseStep 2530561 = 1897921) (by norm_num)
theorem B3374081 : Blo 2247435 3374081 := bstep (se 2 (by rfl) ⟨1265280, by rfl⟩ : syracuseStep 3374081 = 2530561) B2530561
theorem B2249387 : Blo 2247435 2249387 := bstep (se 1 (by rfl) ⟨1687040, by rfl⟩ : syracuseStep 2249387 = 3374081) B3374081
theorem B5693773 : Blo 2247435 5693773 := bbase (se 3 (by rfl) ⟨1067582, by rfl⟩ : syracuseStep 5693773 = 2135165) (by norm_num)
theorem B7591697 : Blo 2247435 7591697 := bstep (se 2 (by rfl) ⟨2846886, by rfl⟩ : syracuseStep 7591697 = 5693773) B5693773
theorem B5061131 : Blo 2247435 5061131 := bstep (se 1 (by rfl) ⟨3795848, by rfl⟩ : syracuseStep 5061131 = 7591697) B7591697
theorem B3374087 : Blo 2247435 3374087 := bstep (se 1 (by rfl) ⟨2530565, by rfl⟩ : syracuseStep 3374087 = 5061131) B5061131
theorem B2249391 : Blo 2247435 2249391 := bstep (se 1 (by rfl) ⟨1687043, by rfl⟩ : syracuseStep 2249391 = 3374087) B3374087
theorem B3374093 : Blo 2247435 3374093 := bbase (se 3 (by rfl) ⟨632642, by rfl⟩ : syracuseStep 3374093 = 1265285) (by norm_num)
theorem B2249395 : Blo 2247435 2249395 := bstep (se 1 (by rfl) ⟨1687046, by rfl⟩ : syracuseStep 2249395 = 3374093) B3374093
theorem B5061149 : Blo 2247435 5061149 := bbase (se 3 (by rfl) ⟨948965, by rfl⟩ : syracuseStep 5061149 = 1897931) (by norm_num)
theorem B3374099 : Blo 2247435 3374099 := bstep (se 1 (by rfl) ⟨2530574, by rfl⟩ : syracuseStep 3374099 = 5061149) B5061149
theorem B2249399 : Blo 2247435 2249399 := bstep (se 1 (by rfl) ⟨1687049, by rfl⟩ : syracuseStep 2249399 = 3374099) B3374099
theorem B3795869 : Blo 2247435 3795869 := bbase (se 3 (by rfl) ⟨711725, by rfl⟩ : syracuseStep 3795869 = 1423451) (by norm_num)
theorem B2530579 : Blo 2247435 2530579 := bstep (se 1 (by rfl) ⟨1897934, by rfl⟩ : syracuseStep 2530579 = 3795869) B3795869
theorem B3374105 : Blo 2247435 3374105 := bstep (se 2 (by rfl) ⟨1265289, by rfl⟩ : syracuseStep 3374105 = 2530579) B2530579
theorem B2249403 : Blo 2247435 2249403 := bstep (se 1 (by rfl) ⟨1687052, by rfl⟩ : syracuseStep 2249403 = 3374105) B3374105
theorem B8107013 : Blo 2247435 8107013 := bbase (se 4 (by rfl) ⟨760032, by rfl⟩ : syracuseStep 8107013 = 1520065) (by norm_num)
theorem B21618701 : Blo 2247435 21618701 := bstep (se 3 (by rfl) ⟨4053506, by rfl⟩ : syracuseStep 21618701 = 8107013) B8107013
theorem B14412467 : Blo 2247435 14412467 := bstep (se 1 (by rfl) ⟨10809350, by rfl⟩ : syracuseStep 14412467 = 21618701) B21618701
theorem B9608311 : Blo 2247435 9608311 := bstep (se 1 (by rfl) ⟨7206233, by rfl⟩ : syracuseStep 9608311 = 14412467) B14412467
theorem B12811081 : Blo 2247435 12811081 := bstep (se 2 (by rfl) ⟨4804155, by rfl⟩ : syracuseStep 12811081 = 9608311) B9608311
theorem B17081441 : Blo 2247435 17081441 := bstep (se 2 (by rfl) ⟨6405540, by rfl⟩ : syracuseStep 17081441 = 12811081) B12811081
theorem B11387627 : Blo 2247435 11387627 := bstep (se 1 (by rfl) ⟨8540720, by rfl⟩ : syracuseStep 11387627 = 17081441) B17081441
theorem B7591751 : Blo 2247435 7591751 := bstep (se 1 (by rfl) ⟨5693813, by rfl⟩ : syracuseStep 7591751 = 11387627) B11387627
theorem B5061167 : Blo 2247435 5061167 := bstep (se 1 (by rfl) ⟨3795875, by rfl⟩ : syracuseStep 5061167 = 7591751) B7591751
theorem B3374111 : Blo 2247435 3374111 := bstep (se 1 (by rfl) ⟨2530583, by rfl⟩ : syracuseStep 3374111 = 5061167) B5061167
theorem B2249407 : Blo 2247435 2249407 := bstep (se 1 (by rfl) ⟨1687055, by rfl⟩ : syracuseStep 2249407 = 3374111) B3374111
theorem B3374117 : Blo 2247435 3374117 := bbase (se 4 (by rfl) ⟨316323, by rfl⟩ : syracuseStep 3374117 = 632647) (by norm_num)
theorem B2249411 : Blo 2247435 2249411 := bstep (se 1 (by rfl) ⟨1687058, by rfl⟩ : syracuseStep 2249411 = 3374117) B3374117
theorem B2846917 : Blo 2247435 2846917 := bbase (se 4 (by rfl) ⟨266898, by rfl⟩ : syracuseStep 2846917 = 533797) (by norm_num)
theorem B3795889 : Blo 2247435 3795889 := bstep (se 2 (by rfl) ⟨1423458, by rfl⟩ : syracuseStep 3795889 = 2846917) B2846917
theorem B5061185 : Blo 2247435 5061185 := bstep (se 2 (by rfl) ⟨1897944, by rfl⟩ : syracuseStep 5061185 = 3795889) B3795889
theorem B3374123 : Blo 2247435 3374123 := bstep (se 1 (by rfl) ⟨2530592, by rfl⟩ : syracuseStep 3374123 = 5061185) B5061185
theorem B2249415 : Blo 2247435 2249415 := bstep (se 1 (by rfl) ⟨1687061, by rfl⟩ : syracuseStep 2249415 = 3374123) B3374123
theorem B2530597 : Blo 2247435 2530597 := bbase (se 4 (by rfl) ⟨237243, by rfl⟩ : syracuseStep 2530597 = 474487) (by norm_num)
theorem B3374129 : Blo 2247435 3374129 := bstep (se 2 (by rfl) ⟨1265298, by rfl⟩ : syracuseStep 3374129 = 2530597) B2530597
theorem B2249419 : Blo 2247435 2249419 := bstep (se 1 (by rfl) ⟨1687064, by rfl⟩ : syracuseStep 2249419 = 3374129) B3374129
theorem B4560229 : Blo 2247435 4560229 := bbase (se 4 (by rfl) ⟨427521, by rfl⟩ : syracuseStep 4560229 = 855043) (by norm_num)
theorem B6080305 : Blo 2247435 6080305 := bstep (se 2 (by rfl) ⟨2280114, by rfl⟩ : syracuseStep 6080305 = 4560229) B4560229
theorem B8107073 : Blo 2247435 8107073 := bstep (se 2 (by rfl) ⟨3040152, by rfl⟩ : syracuseStep 8107073 = 6080305) B6080305
theorem B5404715 : Blo 2247435 5404715 := bstep (se 1 (by rfl) ⟨4053536, by rfl⟩ : syracuseStep 5404715 = 8107073) B8107073
theorem B3603143 : Blo 2247435 3603143 := bstep (se 1 (by rfl) ⟨2702357, by rfl⟩ : syracuseStep 3603143 = 5404715) B5404715
theorem B9608381 : Blo 2247435 9608381 := bstep (se 3 (by rfl) ⟨1801571, by rfl⟩ : syracuseStep 9608381 = 3603143) B3603143
theorem B6405587 : Blo 2247435 6405587 := bstep (se 1 (by rfl) ⟨4804190, by rfl⟩ : syracuseStep 6405587 = 9608381) B9608381
theorem B4270391 : Blo 2247435 4270391 := bstep (se 1 (by rfl) ⟨3202793, by rfl⟩ : syracuseStep 4270391 = 6405587) B6405587
theorem B2846927 : Blo 2247435 2846927 := bstep (se 1 (by rfl) ⟨2135195, by rfl⟩ : syracuseStep 2846927 = 4270391) B4270391
theorem B7591805 : Blo 2247435 7591805 := bstep (se 3 (by rfl) ⟨1423463, by rfl⟩ : syracuseStep 7591805 = 2846927) B2846927
theorem B5061203 : Blo 2247435 5061203 := bstep (se 1 (by rfl) ⟨3795902, by rfl⟩ : syracuseStep 5061203 = 7591805) B7591805
theorem B3374135 : Blo 2247435 3374135 := bstep (se 1 (by rfl) ⟨2530601, by rfl⟩ : syracuseStep 3374135 = 5061203) B5061203
theorem B2249423 : Blo 2247435 2249423 := bstep (se 1 (by rfl) ⟨1687067, by rfl⟩ : syracuseStep 2249423 = 3374135) B3374135
theorem B3374141 : Blo 2247435 3374141 := bbase (se 3 (by rfl) ⟨632651, by rfl⟩ : syracuseStep 3374141 = 1265303) (by norm_num)
theorem B2249427 : Blo 2247435 2249427 := bstep (se 1 (by rfl) ⟨1687070, by rfl⟩ : syracuseStep 2249427 = 3374141) B3374141
theorem B5061221 : Blo 2247435 5061221 := bbase (se 4 (by rfl) ⟨474489, by rfl⟩ : syracuseStep 5061221 = 948979) (by norm_num)
theorem B3374147 : Blo 2247435 3374147 := bstep (se 1 (by rfl) ⟨2530610, by rfl⟩ : syracuseStep 3374147 = 5061221) B5061221
theorem B2249431 : Blo 2247435 2249431 := bstep (se 1 (by rfl) ⟨1687073, by rfl⟩ : syracuseStep 2249431 = 3374147) B3374147
theorem B5693885 : Blo 2247435 5693885 := bbase (se 3 (by rfl) ⟨1067603, by rfl⟩ : syracuseStep 5693885 = 2135207) (by norm_num)
theorem B3795923 : Blo 2247435 3795923 := bstep (se 1 (by rfl) ⟨2846942, by rfl⟩ : syracuseStep 3795923 = 5693885) B5693885
theorem B2530615 : Blo 2247435 2530615 := bstep (se 1 (by rfl) ⟨1897961, by rfl⟩ : syracuseStep 2530615 = 3795923) B3795923
theorem B3374153 : Blo 2247435 3374153 := bstep (se 2 (by rfl) ⟨1265307, by rfl⟩ : syracuseStep 3374153 = 2530615) B2530615
theorem B2249435 : Blo 2247435 2249435 := bstep (se 1 (by rfl) ⟨1687076, by rfl⟩ : syracuseStep 2249435 = 3374153) B3374153
theorem C0 (j : ℕ) (h1 : 561858 ≤ j) (h2 : j ≤ 562358) : Blo 2247435 (4 * j + 3) := by
  interval_cases j
  · exact B2247435
  · exact B2247439
  · exact B2247443
  · exact B2247447
  · exact B2247451
  · exact B2247455
  · exact B2247459
  · exact B2247463
  · exact B2247467
  · exact B2247471
  · exact B2247475
  · exact B2247479
  · exact B2247483
  · exact B2247487
  · exact B2247491
  · exact B2247495
  · exact B2247499
  · exact B2247503
  · exact B2247507
  · exact B2247511
  · exact B2247515
  · exact B2247519
  · exact B2247523
  · exact B2247527
  · exact B2247531
  · exact B2247535
  · exact B2247539
  · exact B2247543
  · exact B2247547
  · exact B2247551
  · exact B2247555
  · exact B2247559
  · exact B2247563
  · exact B2247567
  · exact B2247571
  · exact B2247575
  · exact B2247579
  · exact B2247583
  · exact B2247587
  · exact B2247591
  · exact B2247595
  · exact B2247599
  · exact B2247603
  · exact B2247607
  · exact B2247611
  · exact B2247615
  · exact B2247619
  · exact B2247623
  · exact B2247627
  · exact B2247631
  · exact B2247635
  · exact B2247639
  · exact B2247643
  · exact B2247647
  · exact B2247651
  · exact B2247655
  · exact B2247659
  · exact B2247663
  · exact B2247667
  · exact B2247671
  · exact B2247675
  · exact B2247679
  · exact B2247683
  · exact B2247687
  · exact B2247691
  · exact B2247695
  · exact B2247699
  · exact B2247703
  · exact B2247707
  · exact B2247711
  · exact B2247715
  · exact B2247719
  · exact B2247723
  · exact B2247727
  · exact B2247731
  · exact B2247735
  · exact B2247739
  · exact B2247743
  · exact B2247747
  · exact B2247751
  · exact B2247755
  · exact B2247759
  · exact B2247763
  · exact B2247767
  · exact B2247771
  · exact B2247775
  · exact B2247779
  · exact B2247783
  · exact B2247787
  · exact B2247791
  · exact B2247795
  · exact B2247799
  · exact B2247803
  · exact B2247807
  · exact B2247811
  · exact B2247815
  · exact B2247819
  · exact B2247823
  · exact B2247827
  · exact B2247831
  · exact B2247835
  · exact B2247839
  · exact B2247843
  · exact B2247847
  · exact B2247851
  · exact B2247855
  · exact B2247859
  · exact B2247863
  · exact B2247867
  · exact B2247871
  · exact B2247875
  · exact B2247879
  · exact B2247883
  · exact B2247887
  · exact B2247891
  · exact B2247895
  · exact B2247899
  · exact B2247903
  · exact B2247907
  · exact B2247911
  · exact B2247915
  · exact B2247919
  · exact B2247923
  · exact B2247927
  · exact B2247931
  · exact B2247935
  · exact B2247939
  · exact B2247943
  · exact B2247947
  · exact B2247951
  · exact B2247955
  · exact B2247959
  · exact B2247963
  · exact B2247967
  · exact B2247971
  · exact B2247975
  · exact B2247979
  · exact B2247983
  · exact B2247987
  · exact B2247991
  · exact B2247995
  · exact B2247999
  · exact B2248003
  · exact B2248007
  · exact B2248011
  · exact B2248015
  · exact B2248019
  · exact B2248023
  · exact B2248027
  · exact B2248031
  · exact B2248035
  · exact B2248039
  · exact B2248043
  · exact B2248047
  · exact B2248051
  · exact B2248055
  · exact B2248059
  · exact B2248063
  · exact B2248067
  · exact B2248071
  · exact B2248075
  · exact B2248079
  · exact B2248083
  · exact B2248087
  · exact B2248091
  · exact B2248095
  · exact B2248099
  · exact B2248103
  · exact B2248107
  · exact B2248111
  · exact B2248115
  · exact B2248119
  · exact B2248123
  · exact B2248127
  · exact B2248131
  · exact B2248135
  · exact B2248139
  · exact B2248143
  · exact B2248147
  · exact B2248151
  · exact B2248155
  · exact B2248159
  · exact B2248163
  · exact B2248167
  · exact B2248171
  · exact B2248175
  · exact B2248179
  · exact B2248183
  · exact B2248187
  · exact B2248191
  · exact B2248195
  · exact B2248199
  · exact B2248203
  · exact B2248207
  · exact B2248211
  · exact B2248215
  · exact B2248219
  · exact B2248223
  · exact B2248227
  · exact B2248231
  · exact B2248235
  · exact B2248239
  · exact B2248243
  · exact B2248247
  · exact B2248251
  · exact B2248255
  · exact B2248259
  · exact B2248263
  · exact B2248267
  · exact B2248271
  · exact B2248275
  · exact B2248279
  · exact B2248283
  · exact B2248287
  · exact B2248291
  · exact B2248295
  · exact B2248299
  · exact B2248303
  · exact B2248307
  · exact B2248311
  · exact B2248315
  · exact B2248319
  · exact B2248323
  · exact B2248327
  · exact B2248331
  · exact B2248335
  · exact B2248339
  · exact B2248343
  · exact B2248347
  · exact B2248351
  · exact B2248355
  · exact B2248359
  · exact B2248363
  · exact B2248367
  · exact B2248371
  · exact B2248375
  · exact B2248379
  · exact B2248383
  · exact B2248387
  · exact B2248391
  · exact B2248395
  · exact B2248399
  · exact B2248403
  · exact B2248407
  · exact B2248411
  · exact B2248415
  · exact B2248419
  · exact B2248423
  · exact B2248427
  · exact B2248431
  · exact B2248435
  · exact B2248439
  · exact B2248443
  · exact B2248447
  · exact B2248451
  · exact B2248455
  · exact B2248459
  · exact B2248463
  · exact B2248467
  · exact B2248471
  · exact B2248475
  · exact B2248479
  · exact B2248483
  · exact B2248487
  · exact B2248491
  · exact B2248495
  · exact B2248499
  · exact B2248503
  · exact B2248507
  · exact B2248511
  · exact B2248515
  · exact B2248519
  · exact B2248523
  · exact B2248527
  · exact B2248531
  · exact B2248535
  · exact B2248539
  · exact B2248543
  · exact B2248547
  · exact B2248551
  · exact B2248555
  · exact B2248559
  · exact B2248563
  · exact B2248567
  · exact B2248571
  · exact B2248575
  · exact B2248579
  · exact B2248583
  · exact B2248587
  · exact B2248591
  · exact B2248595
  · exact B2248599
  · exact B2248603
  · exact B2248607
  · exact B2248611
  · exact B2248615
  · exact B2248619
  · exact B2248623
  · exact B2248627
  · exact B2248631
  · exact B2248635
  · exact B2248639
  · exact B2248643
  · exact B2248647
  · exact B2248651
  · exact B2248655
  · exact B2248659
  · exact B2248663
  · exact B2248667
  · exact B2248671
  · exact B2248675
  · exact B2248679
  · exact B2248683
  · exact B2248687
  · exact B2248691
  · exact B2248695
  · exact B2248699
  · exact B2248703
  · exact B2248707
  · exact B2248711
  · exact B2248715
  · exact B2248719
  · exact B2248723
  · exact B2248727
  · exact B2248731
  · exact B2248735
  · exact B2248739
  · exact B2248743
  · exact B2248747
  · exact B2248751
  · exact B2248755
  · exact B2248759
  · exact B2248763
  · exact B2248767
  · exact B2248771
  · exact B2248775
  · exact B2248779
  · exact B2248783
  · exact B2248787
  · exact B2248791
  · exact B2248795
  · exact B2248799
  · exact B2248803
  · exact B2248807
  · exact B2248811
  · exact B2248815
  · exact B2248819
  · exact B2248823
  · exact B2248827
  · exact B2248831
  · exact B2248835
  · exact B2248839
  · exact B2248843
  · exact B2248847
  · exact B2248851
  · exact B2248855
  · exact B2248859
  · exact B2248863
  · exact B2248867
  · exact B2248871
  · exact B2248875
  · exact B2248879
  · exact B2248883
  · exact B2248887
  · exact B2248891
  · exact B2248895
  · exact B2248899
  · exact B2248903
  · exact B2248907
  · exact B2248911
  · exact B2248915
  · exact B2248919
  · exact B2248923
  · exact B2248927
  · exact B2248931
  · exact B2248935
  · exact B2248939
  · exact B2248943
  · exact B2248947
  · exact B2248951
  · exact B2248955
  · exact B2248959
  · exact B2248963
  · exact B2248967
  · exact B2248971
  · exact B2248975
  · exact B2248979
  · exact B2248983
  · exact B2248987
  · exact B2248991
  · exact B2248995
  · exact B2248999
  · exact B2249003
  · exact B2249007
  · exact B2249011
  · exact B2249015
  · exact B2249019
  · exact B2249023
  · exact B2249027
  · exact B2249031
  · exact B2249035
  · exact B2249039
  · exact B2249043
  · exact B2249047
  · exact B2249051
  · exact B2249055
  · exact B2249059
  · exact B2249063
  · exact B2249067
  · exact B2249071
  · exact B2249075
  · exact B2249079
  · exact B2249083
  · exact B2249087
  · exact B2249091
  · exact B2249095
  · exact B2249099
  · exact B2249103
  · exact B2249107
  · exact B2249111
  · exact B2249115
  · exact B2249119
  · exact B2249123
  · exact B2249127
  · exact B2249131
  · exact B2249135
  · exact B2249139
  · exact B2249143
  · exact B2249147
  · exact B2249151
  · exact B2249155
  · exact B2249159
  · exact B2249163
  · exact B2249167
  · exact B2249171
  · exact B2249175
  · exact B2249179
  · exact B2249183
  · exact B2249187
  · exact B2249191
  · exact B2249195
  · exact B2249199
  · exact B2249203
  · exact B2249207
  · exact B2249211
  · exact B2249215
  · exact B2249219
  · exact B2249223
  · exact B2249227
  · exact B2249231
  · exact B2249235
  · exact B2249239
  · exact B2249243
  · exact B2249247
  · exact B2249251
  · exact B2249255
  · exact B2249259
  · exact B2249263
  · exact B2249267
  · exact B2249271
  · exact B2249275
  · exact B2249279
  · exact B2249283
  · exact B2249287
  · exact B2249291
  · exact B2249295
  · exact B2249299
  · exact B2249303
  · exact B2249307
  · exact B2249311
  · exact B2249315
  · exact B2249319
  · exact B2249323
  · exact B2249327
  · exact B2249331
  · exact B2249335
  · exact B2249339
  · exact B2249343
  · exact B2249347
  · exact B2249351
  · exact B2249355
  · exact B2249359
  · exact B2249363
  · exact B2249367
  · exact B2249371
  · exact B2249375
  · exact B2249379
  · exact B2249383
  · exact B2249387
  · exact B2249391
  · exact B2249395
  · exact B2249399
  · exact B2249403
  · exact B2249407
  · exact B2249411
  · exact B2249415
  · exact B2249419
  · exact B2249423
  · exact B2249427
  · exact B2249431
  · exact B2249435
theorem solution (m : ℕ) (hlo : 2247435 ≤ m) (hhi : m ≤ 2249435) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 561858 ≤ j := by omega
    have hj2 : j ≤ 562358 := by omega
    have hb : Blo 2247435 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
